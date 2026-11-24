-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_MultihomogeneousIdeals_CurvePt
-- name    : ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_MultihomogeneousIdeals_CurvePt
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T00:06:59.271807+00:00
-- url     : https://prove2.me/theorems/c1d4cf8c-422f-45d0-8bd3-efde3a435b84
-- title:
--   Curve Pt
-- statement:
--   Definitions and structural lemmas for Curve Pt, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArithmeticIntersection/MultihomogeneousIdeals/CurvePt.lean

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_MultihomogeneousIdeals_MemDivSuppOfDivCycleNeZero
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_MultihomogeneousIdeals_ExistsMonomialNotMem
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace ReciprocityTheory.ChartRestriction.G.AI.I1
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo
variable {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)] {F : Type*} [Field F]
section Weight
variable [DecidableEq K]
attribute [local instance] MvPolynomial.weightedGradedAlgebra
def mw : (Σ k, ι k) → (K → ℕ) := fun p => Pi.single p.1 1
theorem weight_mw (m : (Σ k, ι k) →₀ ℕ) :
    Finsupp.weight (mw (ι := ι)) m = fun k => ∑ i, m ⟨k, i⟩ := by
  funext k
  rw [Finsupp.weight_apply, Finsupp.sum_fintype _ _ (fun _ => by simp), Finset.sum_apply]
  simp only [Pi.smul_apply, mw, smul_eq_mul]
  rw [Fintype.sum_sigma, Finset.sum_eq_single k]
  · simp
  · intro b _ hb
    simp [Pi.single_apply, Ne.symm hb]
  · simp
end Weight
section Rho
variable {W : Ideal (MRingOver F ι)} [hWp : W.IsPrime]
def chartTheta (W : Ideal (MRingOver F ι)) [W.IsPrime] :
    MRingOver F ι →ₐ[F] FractionRing (MRingOver F ι ⧸ W) :=
  (IsScalarTower.toAlgHom F (MRingOver F ι ⧸ W) (FractionRing (MRingOver F ι ⧸ W))).comp
    (Ideal.Quotient.mkₐ F W)
def chartC (W : Ideal (MRingOver F ι)) [W.IsPrime] (j : ∀ k, ι k) (k : K) :
    FractionRing (MRingOver F ι ⧸ W) :=
  (chartTheta W (X ⟨k, j k⟩))⁻¹
def chartRho (W : Ideal (MRingOver F ι)) [W.IsPrime] (j : ∀ k, ι k) :
    MRingOver F ι →ₐ[F] FractionRing (MRingOver F ι ⧸ W) :=
  aeval fun p => chartC W j p.1 * chartTheta W (X p)
end Rho
section Point
variable {W : Ideal (MRingOver F ι)}
instance finiteDimensional_weighted [DecidableEq K] (e : K → ℕ) :
    FiniteDimensional F (weightedHomogeneousSubmodule F (mw (ι := ι)) e) := by
  classical
  rw [weightedHomogeneousSubmodule_eq_finsupp_supported, AddMonoidAlgebra.supported_eq_span_single]
  apply FiniteDimensional.span_of_finite
  have hfin : {m : (Σ k, ι k) →₀ ℕ | Finsupp.weight (mw (ι := ι)) m = e}.Finite := by
    apply (Set.finite_Iic (Finsupp.equivFunOnFinite.symm fun p : Σ k, ι k => e p.1)).subset
    intro m hm
    rw [Set.mem_setOf_eq, weight_mw] at hm
    rw [Set.mem_Iic, Finsupp.le_def]
    intro p
    simp only [Finsupp.equivFunOnFinite_symm_apply_apply]
    rw [← hm]
    exact Finset.single_le_sum (f := fun i => m ⟨p.1, i⟩) (fun _ _ => Nat.zero_le _)
      (Finset.mem_univ p.2)
  exact hfin.image _
end Point
end ReciprocityTheory.ChartRestriction.G.AI.I1


