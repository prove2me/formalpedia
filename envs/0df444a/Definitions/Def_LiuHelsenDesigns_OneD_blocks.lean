-- Prove2me | Definitions.Def_LiuHelsenDesigns_OneD_blocks
-- name    : LiuHelsenDesigns_OneD_blocks
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-10T11:11:03.075825+00:00
-- url     : https://prove2.me/theorems/58173909-2367-4199-b03f-0ad634918edb
-- title:
--   Independent local products and two-layer open-chain blocks
-- statement:
--   Block embedding places a matrix on a contiguous interval and identity on its complement. Independent local laws are combined using product measures, and all compositions use matrix multiplication.
--
--   $$U=(\bigotimes_i V_i^2)C(\bigotimes_i V_i^1).$$
--
--   Here C is exactly uniform over the finite full Clifford group, including its central phases. Two block-brickwork layers act on alternating adjacent patch pairs. Exact divisibility describes this intermediate construction only; it is absent from the headline theorem, whose sampling algorithm must also handle remainders and the whole-chain branch.
-- source:
--   Guoding Liu, Jonas Helsen, STOC 2027 submission #221 (October 2026), pp.3–5, Fig.1, Lemma 1; p.16, Eq.(54). https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/221.pdf

import Definitions.Def_LiuHelsenDesigns_OneD_localLaws

noncomputable section
open MeasureTheory
open scoped Matrix Matrix.Norms.Elementwise

namespace LiuHelsenDesigns.OneD
attribute [local instance] Classical.decEq Classical.propDecidable

def embedBlock (n a w : ℕ) (A : Mat w) : Mat n := fun x y =>
  if ∀ i : Fin n, (i.val < a ∨ a+w ≤ i.val) → x i = y i then
    A (fun j => readWire x (a+j.val)) (fun j => readWire y (a+j.val)) else 0

def blockProductLaw (n ℓ m : ℕ) (ν : Fin m → Measure (Mat ℓ)) : Measure (Mat n) :=
  (Measure.pi ν).map fun Us =>
    (List.finRange m).foldl (fun U i => embedBlock n (i.val*ℓ) ℓ (Us i) * U) 1

/-- Exact uniform counting measure on the full finite H,S,CNOT group, including phases. -/
def uniformCliffordLaw (n : ℕ) : Measure (Mat n) :=
  let S : Set (Mat n) := {A | ∃ U : Cl n, ((U.val : Unitary n) : Mat n) = A}
  ((Measure.count S)⁻¹) • Measure.count.restrict S

def magicLaw (n ℓ m : ℕ) (ν₁ ν₂ : Fin m → Measure (Mat ℓ)) : Measure (Mat n) :=
  multiplyLaws (blockProductLaw n ℓ m ν₂)
    (multiplyLaws (uniformCliffordLaw n) (blockProductLaw n ℓ m ν₁))

def brickLayerLaw (n ξ m parity : ℕ) (ν : Fin (m-1) → Measure (Mat (2*ξ))) : Measure (Mat n) :=
  (Measure.pi ν).map fun Us =>
    ((List.finRange (m-1)).filter fun j => j.val%2 == parity).foldl
      (fun U j => embedBlock n (j.val*ξ) (2*ξ) (Us j) * U) 1
def brickworkLaw (n ξ m : ℕ) (ν : Fin (m-1) → Measure (Mat (2*ξ))) : Measure (Mat n) :=
  multiplyLaws (brickLayerLaw n ξ m 1 ν) (brickLayerLaw n ξ m 0 ν)

end LiuHelsenDesigns.OneD


