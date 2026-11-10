-- Prove2me | Definitions.Def_GoldsteinMCSP_Hardness_Problems
-- name    : GoldsteinMCSP_Hardness_Problems
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-09T17:13:03.846192+00:00
-- url     : https://prove2.me/theorems/b2ecfb90-49af-41a6-b094-baffb30236f3
-- title:
--   The encoded unsigned and signed two-copy partition optimization problems
-- statement:
--   An input is exactly two self-delimiting natural-number lists with no trailing bits. In the unsigned problem these are the two words; in the signed problem a label n encodes underlying symbol n/2 and sign n mod 2. Valid inputs have matching underlying multiplicities and at most two copies of each underlying symbol in each word. Malformed codes are invalid.
--
--   A solution contains four natural-number lists: positive left block lengths, positive right block lengths, a permutation of block indices, and orientation choices. Lengths sum to the corresponding input length; the two sides have the same block count. The index list must be a permutation of the entire block-index range. Unsigned orientations are all zero and paired blocks must be equal. Signed orientations are 0 or 1 and paired blocks must be equal or equal after reversal and sign flipping, as selected. Every component of a solution code is consumed. The objective is the number of left blocks, and both problems minimize. Invalid input/solution combinations are infeasible, so the zero value assigned to malformed objective codes is never a feasible optimum. Empty input words have the empty, zero-cost solution. This model imposes no alphabet-size bound and does not include an optimum or a source graph in the input.
-- source:
--   Goldstein, Kolman and Zheng (2005), Minimum Common String Partition Problem: Hardness and Approximations, EJC 12, R50, DOI 10.37236/1947, Section 1, printed/PDF p. 2; Theorem 2.1, printed/PDF p. 6

import Definitions.Def_GoldsteinMCSP_Hardness_Strings
import Definitions.Def_GoldsteinMCSP_Hardness_Optimization

namespace GoldsteinMCSP.Hardness

/-- Two self-delimiting binary lists of labels; trailing bits are rejected. -/
def parseInstance (w : Bits) : Option (Word × Word) := do
  let (a, rest) ← parseList w
  let (b, tail) ← parseList rest
  if tail == [] then pure (a,b) else none

/-- Positive block lengths encode cuts; π lists the matched block indices;
θ lists orientation bits (all zero for the unsigned problem). -/
structure PartitionCode where
  leftLengths : List ℕ
  rightLengths : List ℕ
  permutation : List ℕ
  orientations : List ℕ
  deriving DecidableEq

def parsePartition (w : Bits) : Option PartitionCode := do
  let (p, w) ← parseList w
  let (q, w) ← parseList w
  let (π, w) ← parseList w
  let (θ, w) ← parseList w
  if w == [] then pure ⟨p,q,π,θ⟩ else none

def blocksByLengths {α : Type} : List ℕ → List α → List (List α)
  | [], _ => []
  | n :: ns, w => w.take n :: blocksByLengths ns (w.drop n)

def lengthsValid (ns : List ℕ) (n : ℕ) : Bool :=
  ns.all (0 < ·) && ns.sum == n

def decodeSigned (w : Word) : SignedWord := w.map fun n => (n / 2, n % 2 == 1)

def instanceValid (signed : Bool) (w : Bits) : Bool :=
  match parseInstance w with
  | none => false
  | some (a,b) =>
      let a' := if signed then a.map (· / 2) else a
      let b' := if signed then b.map (· / 2) else b
      decide (a'.Perm b') && twoCopies a' && twoCopies b'

def codeFeasible (signed : Bool) (a b : Word) (c : PartitionCode) : Bool :=
  let m := c.leftLengths.length
  let p := blocksByLengths c.leftLengths a
  let q := blocksByLengths c.rightLengths b
  lengthsValid c.leftLengths a.length && lengthsValid c.rightLengths b.length &&
  c.rightLengths.length == m && decide (c.permutation.Perm (List.range m)) &&
  c.orientations.length == m &&
  (List.range m).all fun i =>
    let j := c.permutation.getD i m
    let θ := c.orientations.getD i 2
    if signed then
      θ ≤ 1 && (decodeSigned (p.getD i []) ==
        (if θ == 0 then decodeSigned (q.getD j [])
          else reverseSigned (decodeSigned (q.getD j []))))
    else θ == 0 && p.getD i [] == q.getD j []

def partitionProblem (signed : Bool) : OptimizationProblem where
  valid := instanceValid signed
  feasible x y := instanceValid signed x &&
    match parseInstance x, parsePartition y with
    | some (a,b), some c => codeFeasible signed a b c
    | _, _ => false
  value _ y := match parsePartition y with
    | some c => c.leftLengths.length
    | none => 0
  maximize := false

end GoldsteinMCSP.Hardness


