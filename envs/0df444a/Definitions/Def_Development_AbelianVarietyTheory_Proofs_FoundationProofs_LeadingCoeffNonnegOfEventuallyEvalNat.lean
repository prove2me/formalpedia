-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_LeadingCoeffNonnegOfEventuallyEvalNat
-- name    : Development_AbelianVarietyTheory_Proofs_FoundationProofs_LeadingCoeffNonnegOfEventuallyEvalNat
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T11:02:11.451807+00:00
-- url     : https://prove2.me/theorems/ee3bd040-0e27-4cb3-b2c9-181ebd9833f7
-- title:
--   Leading Coeff Nonneg Of Eventually Eval Nat
-- statement:
--   Definitions and structural lemmas for Leading Coeff Nonneg Of Eventually Eval Nat, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/LeadingCoeffNonnegOfEventuallyEvalNat.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_XSmulMemWeightedHomogeneousSubmodule
import Theorems.Thm_GlobalTheory_X_smul_mem_weightedHomogeneousSubmodule

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial Filter Module
namespace GlobalTheory
attribute [local instance] MvPolynomial.gradedAlgebra
section Poly
end Poly
open MvPolynomial DirectSum
variable {ι k : Type*} [Field k]
noncomputable def quotPiece (I : Ideal (MvPolynomial ι k)) (n : ℤ) :
    Submodule k (MvPolynomial ι k ⧸ I) :=
  (weightedHomogeneousSubmodule k (fun _ : ι => (1 : ℤ)) n).map
    (Ideal.Quotient.mkₐ k I).toLinearMap
theorem weightedHomogeneousSubmodule_one_natCast (n : ℕ) :
    weightedHomogeneousSubmodule k (fun _ : ι => (1 : ℤ)) (n : ℤ) =
      homogeneousSubmodule ι k n := by
  ext p
  have : ∀ s : ι →₀ ℕ, Finsupp.weight (fun _ : ι => (1 : ℤ)) s =
      ((Finsupp.weight (1 : ι → ℕ) s : ℕ) : ℤ) := by
    intro s
    simp [Finsupp.weight_apply, Finsupp.sum]
  simp only [mem_weightedHomogeneousSubmodule, mem_homogeneousSubmodule, IsHomogeneous,
    IsWeightedHomogeneous, this, Nat.cast_inj]
instance finite_homogeneousSubmodule' [Finite ι] (n : ℕ) :
    Module.Finite k (homogeneousSubmodule ι k n) := by
  letI := weightedDecomposition k (fun _ : ι => (1 : ℤ))
  rw [← weightedHomogeneousSubmodule_one_natCast]
  exact GradedHilbert.finite_piece _ (X_smul_mem_weightedHomogeneousSubmodule ι k) _
open Classical in

noncomputable def idealHilbertPoly (I : Ideal (MvPolynomial ι k)) : ℚ[X] :=
  if h : ∃ P, IsHilbertPoly (quotPiece I) P then h.choose else 0
noncomputable def hilbertDegree (I : Ideal (MvPolynomial ι k)) : ℕ :=
  ⌊((idealHilbertPoly I).natDegree.factorial : ℚ) * (idealHilbertPoly I).leadingCoeff⌋₊
def projComponents (I : Ideal (MvPolynomial ι k)) : Set (Ideal (MvPolynomial ι k)) :=
  {P | P ∈ I.minimalPrimes ∧ ∃ i, (X i : MvPolynomial ι k) ∉ P}
theorem finite_projComponents [Finite ι] (I : Ideal (MvPolynomial ι k)) :
    (projComponents I).Finite :=
  I.finite_minimalPrimes_of_isNoetherianRing.subset fun _ h => h.1
noncomputable def projSetDegree [Finite ι] (I : Ideal (MvPolynomial ι k)) : ℕ :=
  ∑ P ∈ (finite_projComponents I).toFinset, hilbertDegree P
def IsProjPureDim (I : Ideal (MvPolynomial ι k)) (e : ℕ) : Prop :=
  ∀ P ∈ projComponents I, ringKrullDim (MvPolynomial ι k ⧸ P) = (e + 1 : ℕ)
def projPoints (I : Ideal (MvPolynomial ι k)) : Set (Projectivization k (ι → k)) :=
  {y | ∀ g ∈ I, MvPolynomial.eval y.rep g = 0}
end GlobalTheory


