-- Prove2me | Definitions.Def_Submission_ThreeSum_TernaryPairedContraction
-- name    : Submission_ThreeSum_TernaryPairedContraction
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T07:59:52.222705+00:00
-- url     : https://prove2.me/theorems/8d4bc11b-813c-439f-b3dc-0a49bb751eae
-- title:
--   Ternary Paired Contraction
-- statement:
--   Definitions and structural lemmas for Ternary Paired Contraction, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryPairedContraction.lean

import Definitions.Def_Submission_ThreeSum_TernaryPairedPotential
set_option autoImplicit false
noncomputable section
namespace ThreeSum.TernaryPairedContraction
open Finset TernaryJointType TernaryCoverLocal TernaryCoverOutputCap
open TernaryOriginalRowMenu TernaryPairedPotential
open scoped BigOperators
attribute [local instance] Classical.propDecidable
abbrev Child (L m F : ℕ) (α π : DigitType) :=
  Fin F × (Σ q : vertices L π, Fin m → outputFiber α π q.val)
variable {p : ℕ} [Fact p.Prime]
def childTarget {L m F : ℕ} {α π : DigitType}
    (maps : Fin F → TernaryCoverHashes.Coordinate (Fin L) → ZMod p)
    (c : Child L m F α π) : Fin (m+m) → ZMod p :=
  fun i => Sum.elim
    (fun j => leftHash (maps c.1) (c.2.2 j).val)
    (fun j => rightHash (maps c.1) (c.2.2 j).val) (finSumFinEquiv.symm i)
variable {E P : Type*} [Field E] [Algebra (ZMod p) E]
  [Fintype E] [DecidableEq E] [Fintype P]
def potential {d Λ : ℕ} (A : P → Matrix (Fin d) (Fin Λ) ℤ) : ℕ :=
  ∑ a, minorWeight (A a)
def nextPotential {Λ L m F : ℕ} {α π : DigitType} (ℓ : E →ₗ[ZMod p] ZMod p)
    (A : P → Matrix (Fin (m+m)) (Fin Λ) ℤ)
    (maps : Fin F → TernaryCoverHashes.Coordinate (Fin L) → ZMod p) (seed : E × E) : ℕ :=
  ∑ a : P, ∑ c : Child L m F α π,
    if seed ∈ menuEvent ℓ (fun i j => (A a i j : ZMod p)) (childTarget maps c)
    then minorWeight (A a) else 0
end ThreeSum.TernaryPairedContraction


