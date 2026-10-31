-- Prove2me | Definitions.Def_Tatamibari_NPC_Encoding
-- name    : Tatamibari_NPC_Encoding
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-30T15:33:01.73034+00:00
-- url     : https://prove2.me/theorems/bb4887ce-810b-4d83-8ac6-f868a5e2770e
-- title:
--   Binary and unary dense-board languages
-- statement:
--   Every cell, including an empty one, is encoded by two bits in row-major order. The ordinary encoding puts the height and width first, each as its canonical little-endian binary digits prefixed by the unary length of that digit string. A unary numeral is a run of true bits terminated by false. The strong-hardness encoding uses unary height and width followed by the same dense cell list. Decoding rejects zero dimensions, noncanonical binary numerals, truncated fields, and any list whose length is not exactly the declared area. The two languages consist of the valid codes whose boards admit seven-rule solutions.
--
--   The certificate is a list of rectangle endpoints written as self-delimiting unary naturals, without proof fields. Its expected number of rectangles is the number of clues. The verifier parses the certificate and runs the full solution test. Malformed board or certificate strings are rejected. All dimensions and coordinate magnitudes of an accepted certificate are bounded by the explicitly represented board dimensions.
-- source:
--   Adler et al., Tatamibari Is NP-Complete, DOI:10.4230/LIPIcs.FUN.2021.1; supplied PDF identified as arXiv:2003.08331v2 (7 May 2020), p. 2, Sections 1–3 (definitions and figures)

import Definitions.Def_Tatamibari_NPC_Puzzle
import Mathlib.Data.Nat.Bits

set_option autoImplicit false

namespace Tatamibari.NPC

def unary (n : Nat) : List Bool := List.replicate n true ++ [false]
def binary (n : Nat) : List Bool := unary n.bits.length ++ n.bits

def readUnary : List Bool → Option (Nat × List Bool)
  | [] => none
  | false :: xs => some (0, xs)
  | true :: xs => do
    let (n, rest) ← readUnary xs
    return (n + 1, rest)

def readBinary (xs : List Bool) : Option (Nat × List Bool) := do
  let (n, rest) ← readUnary xs
  if n ≤ rest.length then
    let v := (rest.take n).foldr (fun b a => b.toNat + 2 * a) 0
    if v.bits == rest.take n then some (v, rest.drop n) else none
  else none

def clueBits : Clue → List Bool
  | .empty => [false, false]
  | .square => [false, true]
  | .horizontal => [true, false]
  | .vertical => [true, true]

def readClues : List Bool → Option (List Clue)
  | [] => some []
  | false :: false :: xs => (.empty :: ·) <$> readClues xs
  | false :: true :: xs => (.square :: ·) <$> readClues xs
  | true :: false :: xs => (.horizontal :: ·) <$> readClues xs
  | true :: true :: xs => (.vertical :: ·) <$> readClues xs
  | [_] => none

def encodeBoard (unaryDimensions : Bool) (b : Board) : List Bool :=
  let enc := if unaryDimensions then unary else binary
  enc b.height ++ enc b.width ++ b.entries.flatMap clueBits

def decodeBoard (unaryDimensions : Bool) (xs : List Bool) : Option Board := do
  let dec := if unaryDimensions then readUnary else readBinary
  let (h, rest) ← dec xs
  let (w, rest) ← dec rest
  let cs ← readClues rest
  let b : Board := ⟨w, h, cs⟩
  if b.valid then some b else none

def language (xs : List Bool) : Prop :=
  ∃ b, decodeBoard false xs = some b ∧ b.solvable

def unaryLanguage (xs : List Bool) : Prop :=
  ∃ b, decodeBoard true xs = some b ∧ b.solvable

/-- Certificate coordinates are self-delimiting unary naturals, without proof fields. -/
def encodeRectangle (r : Rectangle) : List Bool :=
  unary r.left ++ unary r.top ++ unary r.right ++ unary r.bottom

def readRectangles : Nat → List Bool → Option (List Rectangle)
  | 0, [] => some []
  | 0, _ :: _ => none
  | n + 1, xs => do
    let (l, xs) ← readUnary xs
    let (t, xs) ← readUnary xs
    let (r, xs) ← readUnary xs
    let (b, xs) ← readUnary xs
    let rs ← readRectangles n xs
    return ⟨l, t, r, b⟩ :: rs

def verifier (xs ws : List Bool) : Bool :=
  match decodeBoard false xs with
  | none => false
  | some b =>
    match readRectangles b.clues.length ws with
    | none => false
    | some rs => b.isSolution rs

end Tatamibari.NPC


