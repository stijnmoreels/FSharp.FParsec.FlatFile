module Header

open System
open System.Text.RegularExpressions
open FsCheck
open FsCheck.Xunit
open FParsec

//////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
//// Infrastructure
//////////////////////////////////////////////////////////////////////////////////////////////////////////////////////

let apply (fp : Parser<('a -> 'b), 'u>) (xp: Parser<'a,'u>) : Parser<'b, 'u> =
    pipe2 fp xp (fun f x -> f x)

let traverse f list =
    let (<*>) = apply
    let retn = preturn
    let cons head tail = head :: tail
     
    let init = retn []
    let folder head tail =
        retn cons <*> (f head) <*> tail

    List.foldBack folder list init

let sequence x = traverse id x

let count n p =
    match n with
    | _ when n <= 0 -> preturn []
    | _ -> sequence <| List.replicate n p

//////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
//// HEADER
//////////////////////////////////////////////////////////////////////////////////////////////////////////////////////

let string' (cs : char list) : string = System.String.Join("",  cs |> List.toArray)
let string_int = string' >> int
let datetime y m d = new DateTime (y, m, d)

let PO = pstring "PO"
let dash = pstring "-"

let year = count 4 digit |>> string_int
let year_dash = year .>> dash

let month = count 2 digit |>> string_int
let month_dash = month .>> dash

let day = count 2 digit |>> string_int

let pheader : Parser<DateTime, unit> = PO >>. pipe3 year_dash month_dash day datetime

let exercise p x =
    match run p x with
    | Success _ -> true
    | Failure (errors, _, _) -> false

let headerRE = "PO[0-9]{4}-[0-9]{2}-[0-9]{2}"
let matchRegex pattrn input = Regex.IsMatch (input, pattrn)

[<Property>]
let ``Header gets parsed when it contains a valid date`` () =
    let expected = matchRegex headerRE
    let actual = exercise pheader

    Arb.generate<DateTime>
    |> Gen.map (fun d -> "PO" + d.ToString ("yyyy-MM-dd"))
    |> Gen.filter expected
    |> Arb.fromGen
    |> Prop.forAll <| actual

[<Property>]
let ``Header don't gets parsed when it doesn't contain a valid date`` () =
    let expected = matchRegex headerRE
    let actual = exercise pheader

    Arb.generate<string>
    |> Gen.three
    |> Gen.map (fun (s1, s2, s3) -> sprintf "PO%s-%s-%s" s1 s2 s3)
    |> Gen.filter (not << expected)
    |> Arb.fromGen
    |> Prop.forAll <| (not << actual)

[<Property>]
let ``Header gets parsed as the regular expression`` (NonNull x) =
    let expected = matchRegex headerRE x
    let actual = exercise pheader x
    
    expected = actual

//////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
//// BODY
//////////////////////////////////////////////////////////////////////////////////////////////////////////////////////

let (|NotMatch|_|) pattern s = 
    if Regex.IsMatch (s, pattern) then None
    else Some NotMatch

type Cap2 = private Cap2 of string
let cap2 = function
    | NotMatch "^[A-Z]{2}$" -> None
    | s -> Some <| Cap2 s

type StringAZ = private StringAZ of string
let stringAZ = function
    | NotMatch "[A-Za-z ]+" -> None
    | s -> Some <| StringAZ s

type StringAZ123 = private StringAZ123 of string
let stringAZ123 = function
    | NotMatch "[A-Za-z0-9 ]+" -> None
    | s -> Some <| StringAZ123 s

type PostInt5 = PostalCode of int
let int5 = function
    | i when string i |> String.length <> 5 || i <= 0 -> None
    | i -> Some <| PostalCode i

type Customer =
    { Country : Cap2
      FullName : StringAZ
      Street : StringAZ123
      City : StringAZ
      State : Cap2
      PostalCode : PostInt5 }

let customer country name street city state postal = 
    { Country = country
      FullName = name
      Street = street
      State = state
      City = city
      PostalCode = postal }

let pipe6 p1 p2 p3 p4 p5 p6 f = 
    pipe5 p1 p2 p3 p4 (tuple2 p5 p6)
          (fun x1 x2 x3 x4 (x5, x6) -> f x1 x2 x3 x4 x5 x6)

let applyOpt fOpt xOpt =
    match fOpt, xOpt with
    | Some f, Some x -> f x |> Some
    | _, _ -> None    

let optCustomer country name street city state postal =
    let (<!>) = Option.map
    let (<*>) = applyOpt

    customer <!> country <*> name <*> street <*> city <*> state <*> postal

let AZ = ['A'..'Z']
let az = ['a'..'z']
let num = [for i in 0..9 -> i |> string |> char]
let singleSpace = ' '

let caps : Parser<_, unit> = anyOf AZ
let space = pchar singleSpace

let trim (s : string) = s.Trim ()
let countString n p = count n p |>> (string' >> trim)

let country = countString 10 (caps <|> space) |>> cap2
let fullname = countString 20 (letter <|> space) |>> stringAZ
let street = countString 20 (letter <|> space <|> digit) |>> stringAZ123
let city = countString 15 (letter <|> space) |>> stringAZ
let state = countString 3 (caps <|> space) |>> cap2
let postal = countString 5 (caps <|> digit <|> space) |>> (int >> int5)

let pcustomer = pipe6 country fullname street city state postal optCustomer
let pcustomers = sepBy1 pcustomer newline |>> List.tryHead

let customerRE = "[A-Z]{2}\s+[A-Za-z ]+[0-9A-Za-z ]+[A-Za-z ]+[A-Z]{2}\s[0-9 ]{5}"

let genString xs l =
    Gen.elements xs
    |> Gen.map string
    |> Gen.listOfLength l
    |> Gen.map (List.reduce (+))
    |> Gen.filter (String.length >> (>=) l)

let genNum l = genString num 5
let genWord l = 
    AZ @ az @ [' '] 
    |> genString <| l

let genAll l = 
    AZ @ az @ num @ [' '] 
    |> genString <| l

let paddingR i s = String.Format (sprintf "{0,-%i}" i, [|box s|])

let genCustString = gen {
    let! country = genString AZ 2
    let! name = genWord 20
    let! street = genAll 20
    let! city = genWord 15
    let! state = genString AZ 2
    let! code = genNum 5

    return [ (10, country); (20, name); (20, street); (15, city); (3, state); (5, code) ]
           |> List.map (fun (x, y) -> paddingR x y)
           |> List.reduce (+) }

[<Property>]
let ``Customer gets parsed with a valid input`` () =
    let expected = matchRegex customerRE
    let actual = exercise pcustomer
    
    genCustString
    |> Arb.fromGen
    |> Prop.forAll <| fun x ->
        expected x = actual x

[<Property>]
let ``Customer doesn't gets parsed with invalid input`` () =
    let expected = matchRegex customerRE
    let actual = exercise pcustomer

    Arb.generate<NonNull<String>>
    |> Gen.map (fun (NonNull x) -> x)
    |> Gen.filter (not << expected)
    |> Arb.fromGen
    |> Prop.forAll <| (not << actual)

[<Property>]
let ``Customer gets parsed as the regular expression`` (NonNull x) =
    let expected = matchRegex customerRE
    let actual = exercise pcustomers
    
    expected x = actual x

///////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
//// TRAILER
//////////////////////////////////////////////////////////////////////////////////////////////////////////////////////

let itemRE = "ITEM[0-9]{3}-[A-Z]{2}\|[A-Za-z]+\|[0-9]\|([0-9]+\.[0-9]+|[0-9])\|[A-Za-z ]+"

type ItemId = Id of string
let itemId = function
    | NotMatch itemRE -> None
    | s -> Some <| Id s

type PosInt = PosInt of int
let posInt i =
    if i >= 0 then Some <| PosInt i
    else None

type PosFloat = PosFloat of float
let posFloat i =
    if i >= 0. then Some <| PosFloat i
    else None

type Item = 
    { Id : ItemId
      Description : StringAZ
      Quantity : PosInt
      UnitPrice : PosFloat
      Notes : StringAZ }

let item i d q u n = { Id = i; Description = d; Quantity = q; UnitPrice = u; Notes = n }

let itemOpt iOpt dOpt qOpt uOpt nOpt =
    let (<*>) = applyOpt
    let (<!>) = Option.map

    item <!> iOpt <*> dOpt <*> qOpt <*> uOpt <*> nOpt

let pipe = skipChar '|'
let comma = pchar ','

let add4 a b c d = a + b + c + d

let pid = pipe4 (pstring "ITEM") (countString 3 digit) (pstring "-") (countString 2 caps) add4 |>> itemId
let pid_pipe : Parser<_, unit> = pid .>> pipe

let sentence = manyChars (letter <|> space) |>> stringAZ
let pdes_pipe = sentence .>> pipe

let pquantity_pipe = (pint32 |>> posInt) .>> pipe
let punitPrice_pipe = (pfloat |>> posFloat) .>> pipe
let pnotes = sentence

let pitem = pipe5 pid_pipe pdes_pipe pquantity_pipe punitPrice_pipe pnotes itemOpt
let pitems = (skipString "ITEMS,") >>. (sepBy pitem comma)

let genId = gen {
    let! itemId1 = genString num 3
    let! itemId2 = genString AZ 2
    return sprintf "ITEM%s-%s" itemId1 itemId2 }

let genQty = 
    Arb.generate<byte> 
    |> Gen.map string

let genUnit = 
    Arb.generate<NormalFloat> 
    |> Gen.map (fun (NormalFloat x) -> string x)

let genItem = gen {
    let! itemId = genId
    let! description = genString (AZ @ az) 10
    let! quantity = genQty
    let! price = genUnit
    let! notes = genString (AZ @ az @ [singleSpace]) 10

    return [ itemId; description; quantity; price; notes ]
           |> List.reduce (sprintf "%s|%s") }

[<Property>]
let ``Item gets parsed when it gets a valid input`` () =
    genItem
    |> Gen.filter (matchRegex itemRE)
    |> Arb.fromGen
    |> Prop.forAll <| exercise pitem

[<Property>]
let ``Item don't gets parsed when it gets an invalid input`` () =
    Arb.generate<NonNull<String>>
    |> Gen.map (fun (NonNull x) -> x)
    |> Gen.filter (not << matchRegex itemRE)
    |> Arb.fromGen
    |> Prop.forAll <| (not << exercise pitem)

[<Property>]
let ``Item gets parsed the same as the regex variant`` (NonNull x) =
    let expected = exercise pitem
    let actual = matchRegex itemRE

    expected x = actual x

type Order =
    { Date : DateTime
      From : Customer
      Item : Item }
