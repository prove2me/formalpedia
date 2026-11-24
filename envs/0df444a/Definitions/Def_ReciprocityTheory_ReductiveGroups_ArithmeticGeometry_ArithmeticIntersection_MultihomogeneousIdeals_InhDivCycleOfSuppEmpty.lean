-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_MultihomogeneousIdeals_InhDivCycleOfSuppEmpty
-- name    : ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_MultihomogeneousIdeals_InhDivCycleOfSuppEmpty
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T23:31:19.621451+00:00
-- url     : https://prove2.me/theorems/48ac7bce-2ef4-4c69-80a0-702f17eaf07d
-- title:
--   Inh Div Cycle Of Supp Empty
-- statement:
--   Definitions and structural lemmas for Inh Div Cycle Of Supp Empty, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArithmeticIntersection/MultihomogeneousIdeals/InhDivCycleOfSuppEmpty.lean

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_MultihomogeneousIdeals_ExistsUniqueStatement
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
section Len
variable {R : Type*} [CommRing R]
variable {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)]
end Len
section Div
variable {R : Type*} [CommRing R]
variable {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)] {F : Type*} [Field F]
end Div
section Kill
variable {σ : Type*} (F : Type*) [Field F] [DecidableEq σ] (S : Finset σ)
def inhKill : MvPolynomial σ F →ₐ[F] MvPolynomial {s // s ∉ S} F :=
  aeval fun s => if h : s ∈ S then 0 else X ⟨s, h⟩
theorem inhKill_X_mem {s : σ} (h : s ∈ S) : inhKill F S (X s) = 0 := by
  simp [inhKill, h]
theorem inhKill_X_nmem {s : σ} (h : s ∉ S) : inhKill F S (X s) = X ⟨s, h⟩ := by
  simp [inhKill, h]
abbrev inhV : Ideal (MvPolynomial σ F) := Ideal.span ((fun s => (X s : MvPolynomial σ F)) '' (S : Set σ))
theorem inhV_kill {f : MvPolynomial σ F} (hf : f ∈ inhV F S) : inhKill F S f = 0 := by
  refine Submodule.span_induction (p := fun f _ => inhKill F S f = 0) ?_ ?_ ?_ ?_ hf
  · rintro _ ⟨s, hs, rfl⟩; exact inhKill_X_mem F S hs
  · simp
  · intro a b _ _ ha hb; simp [ha, hb]
  · intro a b _ hb; simp [smul_eq_mul, hb]
def inhQuotEquiv : (MvPolynomial σ F ⧸ inhV F S) ≃ₐ[F] MvPolynomial {s // s ∉ S} F :=
  AlgEquiv.ofAlgHom (Ideal.Quotient.liftₐ (inhV F S) (inhKill F S) fun _ ha => inhV_kill F S ha)
    ((Ideal.Quotient.mkₐ F (inhV F S)).comp (rename Subtype.val))
    (by
      apply MvPolynomial.algHom_ext
      intro s
      show inhKill F S (rename Subtype.val (X s)) = X s
      rw [rename_X, inhKill_X_nmem F S s.2])
    (by
      apply Ideal.Quotient.algHom_ext
      apply MvPolynomial.algHom_ext
      intro s
      show Ideal.Quotient.mk _ (rename Subtype.val (inhKill F S (X s))) = Ideal.Quotient.mk _ (X s)
      by_cases h : s ∈ S
      · rw [inhKill_X_mem F S h, map_zero, map_zero]
        exact (Ideal.Quotient.eq_zero_iff_mem.mpr
          (Ideal.subset_span (Set.mem_image_of_mem _ (Finset.mem_coe.mpr h)))).symm
      · rw [inhKill_X_nmem F S h, rename_X])
instance inhV_isPrime : (inhV F S).IsPrime := by
  rw [← Ideal.Quotient.isDomain_iff_prime]
  exact (inhQuotEquiv F S).toRingEquiv.toMulEquiv.isDomain
end Kill
section Homog
variable {K : Type*} [Fintype K] [DecidableEq K] {ι : K → Type*} [∀ k, Fintype (ι k)] {F : Type*}
  [Field F]
variable [DecidableEq (Σ k, ι k)]
end Homog
section Fin1
variable {σ : Type*} {F : Type*} [Field F]
end Fin1
end ReciprocityTheory.ChartRestriction.G.AI.I1


