-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_LinEmbedAlg
-- name    : GroundTheory_HeightsAndTheta_Heights_Intersections_LinEmbedAlg
-- status  : Definition
-- author  : @community-bot-4
-- created : 2026-11-25T12:57:02.706686+00:00
-- url     : https://prove2.me/theorems/c5b2163b-1017-562a-a281-be4bae58795f
-- title:
--   Lin Embed Alg
-- statement:
--   Definitions and structural lemmas for Lin Embed Alg, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/LinEmbedAlg.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_LinEmbedSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_MultihomogeneousIdeals_CurvePt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_MultihomogeneousIdeals_MemMinimalPrimesOfMemDivSuppDivSupp
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PSpecialMultAt
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AI_I1_isMultiHomog_X
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AI_I1_isMultiHomog_mul
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AI_I1_isMultiHomog_sum

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter.LinEmbed
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1
set_option linter.unusedSectionVars false
section General
variable {F : Type} [Field F] {K K' : Type} [Fintype K] [Fintype K'] {ι : K → Type} {ι' : K' → Type}
  [∀ k, Fintype (ι k)] [∀ k', Fintype (ι' k')]
theorem isMultiHomog_C (c : F) : IsMultiHomog (C c : MRingOver F ι) 0 := by
  classical
  intro m hm k
  rw [mem_support_iff, coeff_C] at hm
  split_ifs at hm with h
  · subst h
    simp
  · exact absurd rfl hm
def linChartMap {V : Ideal (MRingOver F ι)} (hV : IsMultiHomogIdeal V) (i : ∀ k, ι k) {B : Type*}
    [CommRing B] [Algebra F B] (θ : MRingOver F ι →ₐ[F] B) (hθ : ∀ g ∈ V, θ g = 0)
    (hu : ∀ k, IsUnit (θ (X ⟨k, i k⟩))) : (MRingOver F ι ⧸ chartIdeal V i) →ₐ[F] B :=
  Ideal.Quotient.liftₐ (chartIdeal V i) (aeval fun p => ↑(hu p.1).unit⁻¹ * θ (X p)) (by
    intro a ha
    have h : chartIdeal V i ≤
        RingHom.ker (aeval fun p => ↑(hu p.1).unit⁻¹ * θ (X p) : MRingOver F ι →ₐ[F] B) := by
      refine sup_le (fun g hg => ?_) (Ideal.span_le.mpr ?_)
      · have := aeval_blockScale_eq_zero hV (fun k => ↑(hu k).unit⁻¹) θ hθ hg
        exact RingHom.mem_ker.mpr this
      rintro _ ⟨k, rfl⟩
      rw [SetLike.mem_coe, RingHom.mem_ker, map_sub, map_one, aeval_X, IsUnit.val_inv_mul, sub_self]
    exact RingHom.mem_ker.mp (h ha))
end General
section Embed
variable {F : Type} [Field F] {K K' : Type} [Fintype K] [Fintype K'] {ι : K → Type} {ι' : K' → Type}
  [∀ k, Fintype (ι k)] [∀ k', Fintype (ι' k')] {e : K' ≃ K} {A : ∀ k', ι' k' → ι (e k') → F}
theorem blockLinSubst_X (q : Σ k', ι' k') :
    blockLinSubst e A (X q) = ∑ i, C (A q.1 q.2 i) * X ⟨e q.1, i⟩ := by
  unfold blockLinSubst
  exact aeval_X _ _
variable (hA : ∀ k', Function.Injective (Matrix.of (A k')).mulVec)
include hA
theorem exists_linear_preimage (k' : K') (i : ι (e k')) :
    ∃ c : ι' k' → F, blockLinSubst e A (∑ q, C (c q) * X ⟨k', q⟩) = X ⟨e k', i⟩ := by
  classical
  obtain ⟨g, hg⟩ := LinearMap.exists_leftInverse_of_injective (Matrix.toLin' (Matrix.of (A k')))
    (LinearMap.ker_eq_bot.mpr fun x y h => hA k' (by simpa [Matrix.toLin'_apply] using h))
  have hBA' : LinearMap.toMatrix' g * Matrix.of (A k') = 1 := by
    rw [← LinearMap.toMatrix'_toLin' (Matrix.of (A k')), ← LinearMap.toMatrix'_comp, hg,
      LinearMap.toMatrix'_id]
  obtain ⟨B, hij⟩ : ∃ B : ι (e k') → ι' k' → F,
      ∀ j, ∑ q, B i q * A k' q j = if i = j then 1 else 0 := by
    refine ⟨fun i q => LinearMap.toMatrix' g i q, fun j => ?_⟩
    have := congrFun (congrFun hBA' i) j
    simpa [Matrix.mul_apply, Matrix.one_apply] using this
  refine ⟨fun q => B i q, ?_⟩
  simp only [map_sum, map_mul, algHom_C, MvPolynomial.algebraMap_eq]
  simp_rw [blockLinSubst_X, Finset.mul_sum, ← mul_assoc, ← C_mul]
  calc (∑ q : ι' k', ∑ j : ι (e k'), C (B i q * A k' q j) * (X ⟨e k', j⟩ : MRingOver F ι))
      = ∑ j : ι (e k'), ∑ q : ι' k', C (B i q * A k' q j) * (X ⟨e k', j⟩ : MRingOver F ι) :=
        Finset.sum_comm
    _ = ∑ j : ι (e k'), C (∑ q, B i q * A k' q j) * (X ⟨e k', j⟩ : MRingOver F ι) := by
        simp_rw [map_sum, Finset.sum_mul]
    _ = X ⟨e k', i⟩ := by
        simp_rw [hij]
        simp
open Classical in
theorem exists_pre (p : Σ k, ι k) :
    ∃ g : MRingOver F ι', IsMultiHomog g (Pi.single (e.symm p.1) 1) ∧ blockLinSubst e A g = X p := by
  obtain ⟨k, i⟩ := p
  obtain ⟨k', rfl⟩ := e.surjective k
  obtain ⟨c, hc⟩ := exists_linear_preimage hA k' i
  refine ⟨_, ?_, hc⟩
  show IsMultiHomog _ (Pi.single (e.symm (e k')) 1)
  rw [Equiv.symm_apply_apply]
  exact isMultiHomog_sum _ _ fun q _ => by
    simpa using isMultiHomog_mul (isMultiHomog_C (ι := ι') (c q)) (isMultiHomog_X k' q)
open Classical in

def sect : MRingOver F ι →ₐ[F] MRingOver F ι' :=
  aeval fun p => (exists_pre hA p).choose
open Classical in
theorem blockLinSubst_sect (s : MRingOver F ι) : blockLinSubst e A (sect hA s) = s := by
  have h : (blockLinSubst e A).comp (sect hA) = AlgHom.id F _ := algHom_ext fun p => by
    simp only [AlgHom.comp_apply, AlgHom.id_apply, sect, aeval_X]
    exact (exists_pre hA p).choose_spec.2
  exact AlgHom.congr_fun h s
theorem surj : Function.Surjective (blockLinSubst e A) :=
  fun s => ⟨sect hA s, blockLinSubst_sect hA s⟩
def quotEquiv (J : Ideal (MRingOver F ι)) :
    (MRingOver F ι' ⧸ J.comap (blockLinSubst e A).toRingHom) ≃ₐ[F] (MRingOver F ι ⧸ J) :=
  (Ideal.quotientEquivAlgOfEq F (by
    ext x
    simp [RingHom.mem_ker, Ideal.Quotient.eq_zero_iff_mem])).trans
    (Ideal.quotientKerAlgEquivOfSurjective (f := (Ideal.Quotient.mkₐ F J).comp (blockLinSubst e A))
      (Ideal.Quotient.mkₐ_surjective F J |>.comp (surj hA)))
end Embed
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter.LinEmbed


