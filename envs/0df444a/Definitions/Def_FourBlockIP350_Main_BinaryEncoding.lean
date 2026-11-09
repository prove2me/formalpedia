-- Prove2me | Definitions.Def_FourBlockIP350_Main_BinaryEncoding
-- name    : FourBlockIP350_Main_BinaryEncoding
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T10:34:57.959532+00:00
-- url     : https://prove2.me/theorems/6e3b7a19-4539-41af-881d-54a1ca35250c
-- title:
--   Delimited binary encodings and charged machine computations
-- statement:
--   Natural numbers use self-delimiting binary words: the bit-length is written in unary, followed by a zero and that many magnitude bits. Signed integers add a sign bit; finite endpoints add a presence tag. Lists have length prefixes, and vectors and matrices use fixed coordinate order. Both dimensions are included. Inputs encode the full matrix, costs, right-hand sides and tagged endpoints. Solver output encodes its outcome tag and, for an optimum, the integer vector and cost.
--   $$\operatorname{ComputesWithin}(P,u,v,T)\iff \exists t\le T:\ P(u\#)\text{ halts with entire output }v.$$
--   The machine is the referenced deterministic finite-alphabet multitape Turing machine. Each transition reads and writes only one cell per tape and moves each head by at most one. Computability of a parameter function is separately witnessed by one such machine halting on all natural argument pairs.
--
--   **Formalization Note** The dense matrix encoding has polynomial overhead over the source's block-list encoding. Time includes output production. No runtime or correctness field is stored in a program.
--   An explicit output decoder rejects malformed tags, truncated vectors and trailing data, and reconstructs a point in the same coordinate order.
-- source:
--   Klaus Jansen, Felix Ohnesorge, Corinna Wambsganz, A Fixed-Parameter Algorithm for 4-Block Integer Programming, STOC 2027 submission #350 (October 2026), p. 3, Theorem 1.1; p. 7 Lemma 3.2

import Mathlib
import Definitions.Def_IntMul_MultitapeModel
import Definitions.Def_FourBlockIP350_Main_BlockData

namespace FourBlockIP350.Main

/-- Self-delimiting binary natural: unary bit-length, zero separator, then that many bits.
The unary part encodes only the bit-length, never the magnitude. -/
def encNat (a : ℕ) : List Bool :=
  let w := a.size
  List.replicate w true ++ [false] ++ IntMul.bin w a

def encInt (a : ℤ) : List Bool := decide (a < 0) :: encNat a.natAbs

def encEndpoint : Option ℤ → List Bool
  | none => [false]
  | some a => true :: encInt a

def encList {α : Type} (enc : α → List Bool) (xs : List α) : List Bool :=
  encNat xs.length ++ xs.flatMap enc

def blockOrder (k n : ℕ) : List (BlockRow k n) :=
  (List.finRange k).map (none, ·) ++
  (List.finRange n).flatMap (fun i => (List.finRange k).map (some i, ·))

def localOrder (k n : ℕ) : List (LocalCol k n) :=
  (List.finRange n).flatMap (fun i => (List.finRange k).map (i, ·))

def encVector {V : Type} (order : List V) (z : V → ℤ) : List Bool :=
  encList encInt (order.map z)

def encFourBlock {k n : ℕ} (I : FourBlock k n) : List Bool :=
  encNat k ++ encNat n ++
  encList encInt ((blockOrder k n).flatMap fun r =>
    (blockOrder k n).map fun j => I.program.matrix r j) ++
  encVector (blockOrder k n) I.b ++ encVector (blockOrder k n) I.c ++
  encList encEndpoint ((blockOrder k n).map I.lower) ++
  encList encEndpoint ((blockOrder k n).map I.upper)

/-- Dense binary encoding; it has polynomial length relative to the block-list encoding,
including arbitrary global-column coefficients. -/
def encNFold {k n : ℕ} (I : BoundedNFold k n) : List Bool :=
  encNat k ++ encNat n ++
  encList encInt ((blockOrder k n).flatMap fun r =>
    (localOrder k n).map fun j => I.blocks.matrix r j) ++
  encVector (blockOrder k n) I.b ++ encVector (localOrder k n) I.c ++
  encVector (localOrder k n) I.lower ++ encVector (localOrder k n) I.upper

def encAnswer {V : Type} (order : List V) : Answer V → List Bool
  | .infeasible => [false,false]
  | .unbounded => [false,true]
  | .optimum z v => [true] ++ encVector order z ++ encInt v

/-- Parsing the self-delimiting natural word; malformed/truncated words fail. -/
def decodeNat (input : List Bool) : Option (ℕ × List Bool) := do
  let w := (input.takeWhile id).length
  let rest ← match input.drop w with
    | false :: xs => some xs
    | _ => none
  if w ≤ rest.length then
    let value := IntMul.val (rest.take w)
    if value.size = w then some (value, rest.drop w) else none
  else none

def decodeInt (input : List Bool) : Option (ℤ × List Bool) := do
  let (sign, rest) ← match input with
    | s :: xs => some (s, xs)
    | _ => none
  let (value, tail) ← decodeNat rest
  if sign then
    if value = 0 then none else some (-(value : ℤ), tail)
  else some ((value : ℤ), tail)

def parseMany {α : Type} (parser : List Bool → Option (α × List Bool)) :
    ℕ → List Bool → Option (List α × List Bool)
  | 0, input => some ([], input)
  | n+1, input => do
      let (a, tail) ← parser input
      let (as, rest) ← parseMany parser n tail
      some (a :: as, rest)

def decodeList {α : Type} (parser : List Bool → Option (α × List Bool))
    (input : List Bool) : Option (List α × List Bool) := do
  let (n, tail) ← decodeNat input
  parseMany parser n tail

/-- Output decoding rejects wrong tags, truncated vectors, and trailing data.
The coordinate order is the same complete order used by the corresponding encoder. -/
def decodeAnswer {V : Type} [DecidableEq V] (order : List V)
    (input : List Bool) : Option (Answer V) :=
  match input with
  | [false, false] => some .infeasible
  | [false, true] => some .unbounded
  | true :: tail => do
      let (zs, tail) ← decodeList decodeInt tail
      if zs.length = order.length then
        let (v, rest) ← decodeInt tail
        if rest = [] then
          some (.optimum (fun j => zs.getD (order.idxOf j) 0) v)
        else none
      else none
  | _ => none

/-- One halting computation on the fixed binary multitape model, with empty second word.
`HaltsWithOutput` checks the complete output tape, not a chosen prefix. -/
def ComputesWithin (P : IntMul.MultitapeTM) (input output : List Bool) (T : ℕ) : Prop :=
  ∃ t ≤ T, P.HaltsWithOutput input [] t output

/-- Total computability, witnessed by one actual bit-machine. No time bound is assumed. -/
def ComputablePairFunction (f : ℕ → ℕ → ℕ) : Prop :=
  ∃ P : IntMul.MultitapeTM, ∀ a b, ∃ t,
    P.HaltsWithOutput (encNat a ++ encNat b) [] t (encNat (f a b))

end FourBlockIP350.Main


