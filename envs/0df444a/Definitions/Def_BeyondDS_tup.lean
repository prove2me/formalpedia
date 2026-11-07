-- Prove2me | Definitions.Def_BeyondDS_tup
-- name    : BeyondDS_tup
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T16:06:10.320192+00:00
-- url     : https://prove2.me/theorems/911f5663-3103-46cc-8022-da3850e88d5a
-- title:
--   Self-delimiting codes of lists of bit strings
-- statement:
--   Every machine input and output of this mission is a bit string built from a list of bit strings $w_1,\dots,w_k$ by an unambiguous code. Each $w_j$ is written with every bit doubled and followed by the separator $01$; the code of the list is the concatenation
--
--   $$\mathrm{tup}(w_1,\dots,w_k)=\mathrm{sd}(w_1)\cdots\mathrm{sd}(w_k),\qquad \mathrm{sd}(w)=w_1w_1w_2w_2\cdots w_mw_m\,01 .$$
--
--   The module also gives the parser $\mathrm{untup}$ (which reads any bit string, ignoring malformed pairs), the value $\mathrm{decNat}$ of a unary field (its number of leading ones, inverting the published unary code $\mathrm{encNat}$), and one-bit codes of a bit and of an optional bit.
--
--   Unambiguous codes are what make the polynomial-time and length clauses of the goal meaningful: a machine reading $\mathrm{tup}$ of the parameters, the state and the model's answer sees each field separately.
--
--   **Formalization Note** Bit strings are `List Bool` (`QAlgorithms.Complexity.Str`). Natural numbers in machine inputs are unary (`encNat`, terminated by a zero), so a polynomial in the input length is a polynomial in the parameters.
-- source:
--   Rambaud, Beyond Dolev–Strong: Adaptive Byzantine Broadcast with Õ(n^{3/2}) Messages at a Tight Honest Majority, STOC 2027 submission (manuscript sha256 c84cf9c9…), §4.2, p.12 (PDF p.13) and §5.2, p.15 (PDF p.16) ("Signatures have a specified efficiently verifiable encoding"; "Recipients reject malformed encodings")

import Mathlib
import Definitions.Def_QAlgorithms_ClassicalStringComputability

set_option autoImplicit false

open QAlgorithms.Complexity

namespace BeyondDS

/-- A self-delimiting code of one bit string: each bit doubled, then the separator `01`. -/
def selfDelim (w : Str) : Str :=
  w.flatMap (fun b => [b, b]) ++ [false, true]

/-- An unambiguous code of a list of bit strings, used for all machine inputs and outputs of this
mission. -/
def tup (ws : List Str) : Str :=
  ws.flatMap selfDelim

/-- The parser of `tup`, with the bits of the current field held reversed in `cur`. A pair `10` and a
trailing odd bit are ignored, so every string parses. -/
def untupAux : Str → Str → List Str
  | cur, b :: c :: rest =>
    if b = c then untupAux (b :: cur) rest
    else if c = true then cur.reverse :: untupAux [] rest
    else untupAux cur rest
  | _, _ => []

/-- The parser of `tup`. -/
def untup (w : Str) : List Str :=
  untupAux [] w

/-- The value of a unary field: its number of leading `true` bits. It inverts `encNat`. -/
def decNat (w : Str) : ℕ :=
  (w.takeWhile id).length

/-- A code of a bit. -/
def encBool (b : Bool) : Str := [b]

/-- A code of `Option Bool`. -/
def encOptBool : Option Bool → Str
  | none => []
  | some b => [b]

end BeyondDS


