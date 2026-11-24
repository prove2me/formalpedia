-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_MultihomogeneousIdeals_CycDim
-- name    : ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_MultihomogeneousIdeals_CycDim
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T23:30:22.060562+00:00
-- url     : https://prove2.me/theorems/f622bfe7-6d0b-44b2-b36e-443ab46cf9b4
-- title:
--   Cyc Dim
-- statement:
--   Definitions and structural lemmas for Cyc Dim, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArithmeticIntersection/MultihomogeneousIdeals/CycDim.lean

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_MultihomogeneousIdeals_IsFieldIntersection
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterDivSuppAC
import Definitions.Def_Lemmata_GeneralBFactBis_Imports
import Definitions.Def_Lemmata_FirstBlockLemmaB_Imports
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
section CycBlocks
variable {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)] {R : Type*} [CommRing R]
def cycBlockWt [DecidableEq K] (k : K) : (Σ k, ι k) → ℕ := fun p => if p.1 = k then 1 else 0
attribute [local instance] MvPolynomial.weightedGradedAlgebra
end CycBlocks
section CycDim
variable {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)] {F : Type*} [Field F]
end CycDim
section CycChart
variable {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)] {F : Type*} [Field F]
theorem aeval_blockScale {A : Type*} [CommRing A] [Algebra F A] {g : MRingOver F ι} {a : K → ℕ}
    (hg : IsMultiHomog g a) (c : K → A) (z : (Σ k, ι k) → A) :
    aeval (fun p => c p.1 * z p) g = (∏ k, c k ^ a k) * aeval z g := by
  simp only [aeval_def, eval₂_eq', Finset.mul_sum]
  refine Finset.sum_congr rfl fun d hd => ?_
  have h1 : ∏ p, (c p.1 * z p) ^ d p = (∏ p, c p.1 ^ d p) * ∏ p, z p ^ d p := by
    rw [← Finset.prod_mul_distrib]
    simp_rw [mul_pow]
  have h2 : ∏ p : (Σ k, ι k), c p.1 ^ d p = ∏ k, c k ^ a k := by
    rw [Fintype.prod_sigma]
    refine Finset.prod_congr rfl fun k _ => ?_
    show ∏ y, c k ^ d ⟨k, y⟩ = _
    rw [Finset.prod_pow_eq_pow_sum, hg d hd k]
  rw [h1, h2]
  ring
theorem aeval_blockScale_eq_zero {A : Type*} [CommRing A] [Algebra F A] {V : Ideal (MRingOver F ι)}
    (hV : IsMultiHomogIdeal V) (c : K → A) (θ : MRingOver F ι →ₐ[F] A) (hθ : ∀ g ∈ V, θ g = 0)
    {g : MRingOver F ι} (hg : g ∈ V) : aeval (fun p => c p.1 * θ (X p)) g = 0 := by
  have e : (aeval fun p => θ (X p) : MRingOver F ι →ₐ[F] A) = θ :=
    MvPolynomial.algHom_ext fun p => aeval_X _ _
  obtain ⟨S, hS, rfl⟩ := hV
  have h : Ideal.span S ≤ RingHom.ker (aeval (fun p => c p.1 * θ (X p)) : MRingOver F ι →ₐ[F] A) := by
    refine Ideal.span_le.mpr fun f hfS => ?_
    obtain ⟨a, ha⟩ := hS f hfS
    rw [SetLike.mem_coe, RingHom.mem_ker, aeval_blockScale ha, DFunLike.congr_fun e f,
      hθ f (Ideal.subset_span hfS), mul_zero]
  exact RingHom.mem_ker.mp (h hg)
def chartSwap {V : Ideal (MRingOver F ι)} (hV : IsMultiHomogIdeal V) (i j : ∀ k, ι k)
    (hu : ∀ k, IsUnit (Ideal.Quotient.mkₐ F (chartIdeal V j) (X ⟨k, i k⟩))) :
    (MRingOver F ι ⧸ chartIdeal V i) →ₐ[F] (MRingOver F ι ⧸ chartIdeal V j) :=
  Ideal.Quotient.liftₐ (chartIdeal V i)
    (aeval fun p => ↑(hu p.1).unit⁻¹ * Ideal.Quotient.mkₐ F (chartIdeal V j) (X p)) (by
      intro a ha
      have h : chartIdeal V i ≤ RingHom.ker
          (aeval fun p => ↑(hu p.1).unit⁻¹ * Ideal.Quotient.mkₐ F (chartIdeal V j) (X p) :
            MRingOver F ι →ₐ[F] _) := by
        refine sup_le (fun g hg => RingHom.mem_ker.mpr (aeval_blockScale_eq_zero
          (A := MRingOver F ι ⧸ chartIdeal V j) hV (fun k => ↑(hu k).unit⁻¹)
          (Ideal.Quotient.mkₐ F (chartIdeal V j)) (fun g hg => ?_) hg)) (Ideal.span_le.mpr ?_)
        · rw [Ideal.Quotient.mkₐ_eq_mk]
          exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_sup_left hg)
        · rintro _ ⟨k, rfl⟩
          rw [SetLike.mem_coe, RingHom.mem_ker, map_sub, map_one, aeval_X, IsUnit.val_inv_mul,
            sub_self]
      exact RingHom.mem_ker.mp (h ha))
end CycChart
end ReciprocityTheory.ChartRestriction.G.AI.I1


