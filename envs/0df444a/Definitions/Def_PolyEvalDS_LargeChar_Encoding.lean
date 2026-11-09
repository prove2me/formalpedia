-- Prove2me | Definitions.Def_PolyEvalDS_LargeChar_Encoding
-- name    : PolyEvalDS_LargeChar_Encoding
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T10:49:37.275993+00:00
-- url     : https://prove2.me/theorems/5d2b07b1-fe55-4835-a894-5abee16b073d
-- title:
--   Bit encodings of natural numbers, lists, points and formulas
-- statement:
--   Fixed binary words for the data a machine reads and writes.
--
--   1. A natural number $m$ with bits $b_0,\dots,b_{k-1}$, least significant first, is coded as $1\,b_0\,1\,b_1\cdots1\,b_{k-1}\,0$. So $0$ is the word $0$, and the code is self-delimiting.
--   2. A list is coded as the code of its length followed by the codes of its entries.
--   3. A point $x\in\mathbb N^n$ is coded as the list of its coordinates.
--   4. A formula is coded by a prefix tree code: two tag bits ($00$ variable, $01$ constant, $10$ sum, $11$ product), then the code of the variable or constant, or the codes of the two subformulas.
--
--   These words only serialize data. They do not carry any computed result, and the length of each word is linear in the bit length of what it writes.
--
--   **Formalization Note** The paper fixes no encoding; any standard encoding gives the same polynomial-time notion.
-- source:
--   Hiroki Okada, Rachel Player, Simon Pohmann, An Algebraic Polynomial Evaluation Datastructure for Fields of Large Characteristic, STOC 2027 submission #463 (October 2026), source.pdf SHA-256 33e2ace7597795eb2f5be3a68d2beb3fd8c69139336faf4559faf1452360646b, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/463.pdf, Definition 2.2, p. 5 (serialization of the algorithm's input and output)

import Mathlib
import Definitions.Def_PolyEvalDS_LargeChar_Formula

namespace PolyEvalDS.LargeChar

/-- Self-delimiting code of a natural number: each bit `b` of `Nat.bits m` (least significant
first) is written as the pair `true, b`, and the code ends with `false`. -/
def encNat (m : ℕ) : List Bool :=
  (Nat.bits m).flatMap (fun b => [true, b]) ++ [false]

/-- Code of a list: its length, then the codes of its entries in order. -/
def encList {α : Type} (enc : α → List Bool) (l : List α) : List Bool :=
  encNat l.length ++ l.flatMap enc

/-- Code of a point `x ∈ ℕ^n`: the list of its `n` coordinates. -/
def encPoint {n : ℕ} (x : Fin n → ℕ) : List Bool :=
  encList encNat (List.ofFn x)

/-- Prefix tree code of a formula: two tag bits for the node kind, then the node's data or the
codes of its two subformulas. -/
def encAF : AF ℕ → List Bool
  | .var j => [false, false] ++ encNat j
  | .const c => [false, true] ++ encNat c
  | .add a b => [true, false] ++ encAF a ++ encAF b
  | .mul a b => [true, true] ++ encAF a ++ encAF b

end PolyEvalDS.LargeChar


