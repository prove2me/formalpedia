-- Prove2me | solution 1 for AlgebraicCurve.exists_finiteDimensional_isSeparable_adjoin_of_constantFieldExtension_of_isAlgClosed
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.4153+00:00
-- url     : https://prove2.me/submissions/f712fcd4-03e1-57d7-b600-a62920b8a436

import Mathlib
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Theorems.Thm_AlgebraicCurve_exists_separating_transcendental_of_perfectField
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_exists_finiteDimensional_isSeparable_adjoin_of_constantFieldExtension_of_isAlgClosed

set_option autoImplicit false
set_option maxHeartbeats 4000000

open IntermediateField

theorem solution
    (K F K' F' : Type*)
    [Field K] [Field F] [Field K'] [Field F'] [Algebra K F] [Algebra K' F']
    [Algebra K K'] [Algebra F F'] [Algebra K F'] [IsScalarTower K K' F'] [IsScalarTower K F F']
    [IsAlgClosed K]
    (hfg : ∃ x : F, Transcendental K x ∧
      FiniteDimensional (IntermediateField.adjoin K ({x} : Set F)) F)
    (hfg' : ∃ x : F', Transcendental K' x ∧
      FiniteDimensional (IntermediateField.adjoin K' ({x} : Set F')) F')
    (hgen : IntermediateField.adjoin K' (Set.range (algebraMap F F')) = ⊤) :
    ∃ t' : F', FiniteDimensional (IntermediateField.adjoin K' ({t'} : Set F')) F' ∧
      Algebra.IsSeparable (IntermediateField.adjoin K' ({t'} : Set F')) F' := by
  classical
  obtain ⟨x, hx, hxfin⟩ := hfg
  obtain ⟨t, _ht_trans, ht_fin, ht_sep⟩ :=
    AlgebraicCurve.exists_separating_transcendental_of_perfectField hx hxfin
  haveI := ht_fin; haveI := ht_sep
  refine ⟨algebraMap F F' t, ?_, ?_⟩
  all_goals
    set Kt := IntermediateField.adjoin K ({t} : Set F) with hKt
    set t' := algebraMap F F' t with ht'
    set Kt' := IntermediateField.adjoin K' ({t'} : Set F') with hKt'

    have hmem : ∀ a : Kt, algebraMap F F' (a : F) ∈ Kt' := by
      intro a
      have hle : Kt.toSubfield ≤ Kt'.toSubfield.comap (algebraMap F F') := by
        rw [hKt, adjoin_toSubfield]
        refine Subfield.closure_le.mpr ?_
        rintro y (⟨c, rfl⟩ | ⟨rfl : y = t⟩)
        · simp only [SetLike.mem_coe, Subfield.mem_comap]
          rw [← IsScalarTower.algebraMap_apply K F F', IsScalarTower.algebraMap_apply K K' F']
          exact IntermediateField.algebraMap_mem Kt' _
        · exact mem_adjoin_simple_self K' t'
      exact hle a.2

    let σ : Kt →+* Kt' :=
      ((algebraMap F F').comp (algebraMap Kt F)).codRestrict Kt'.toSubring hmem
    have hσF' : (algebraMap Kt' F').comp σ = (algebraMap F F').comp (algebraMap Kt F) :=
      RingHom.ext fun _ => rfl

    set Bt := Module.finBasis Kt F with hBt
    set S : Set F' := Set.range fun i => algebraMap F F' (Bt i : F) with hS
    haveI : Finite S := (Set.finite_range _).to_subtype

    have key : ∀ i,
        Polynomial.aeval (R := Kt') (algebraMap F F' (Bt i : F))
          ((minpoly Kt (Bt i : F)).map σ) = 0 := by
      intro i
      rw [Polynomial.aeval_def, Polynomial.eval₂_map, hσF',
        ← Polynomial.hom_eval₂, ← Polynomial.aeval_def, minpoly.aeval, map_zero]
    have hint : ∀ y ∈ S, IsIntegral Kt' y := by
      rintro _ ⟨i, rfl⟩
      exact ⟨(minpoly Kt (Bt i : F)).map σ,
        ((minpoly.monic (Algebra.IsIntegral.isIntegral (R := Kt) (Bt i : F))).map σ), key i⟩
    have hsepS : ∀ y ∈ S, IsSeparable Kt' y := by
      rintro _ ⟨i, rfl⟩
      have hp : ((minpoly Kt (Bt i : F)).map σ).Separable :=
        Polynomial.Separable.map (Algebra.IsSeparable.isSeparable Kt (Bt i : F))
      exact Polynomial.Separable.of_dvd hp (minpoly.dvd _ _ (key i))

    have hadj_top : IntermediateField.adjoin Kt' S = ⊤ := by
      rw [← IntermediateField.restrictScalars_eq_top_iff (K := K'), eq_top_iff, ← hgen]
      refine IntermediateField.adjoin_le_iff.mpr ?_
      rintro _ ⟨f, rfl⟩
      show algebraMap F F' f ∈ (adjoin Kt' S).restrictScalars K'
      have hrepr : algebraMap F F' f =
          ∑ i, algebraMap Kt' F' (σ (Bt.repr f i)) * algebraMap F F' (Bt i : F) := by
        conv_lhs => rw [← Bt.sum_repr f, map_sum]
        simp only [Algebra.smul_def, map_mul]
        rfl
      rw [hrepr]
      exact sum_mem fun i _ => mul_mem
        (IntermediateField.algebraMap_mem (adjoin Kt' S) (σ (Bt.repr f i)))
        (subset_adjoin Kt' S ⟨i, rfl⟩)

  · have hfd : FiniteDimensional Kt' (adjoin Kt' S) :=
      IntermediateField.finiteDimensional_adjoin fun y hy => hint y hy
    rw [hadj_top] at hfd
    exact IntermediateField.topEquiv.toLinearEquiv.finiteDimensional

  · rw [← separableClosure.eq_top_iff, eq_top_iff, ← hadj_top]
    exact adjoin_le_iff.mpr fun y hy => mem_separableClosure_iff.mpr (hsepS y hy)

end S_AlgebraicCurve_exists_finiteDimensional_isSeparable_adjoin_of_constantFieldExtension_of_isAlgClosed
end P2MW
export P2MW.S_AlgebraicCurve_exists_finiteDimensional_isSeparable_adjoin_of_constantFieldExtension_of_isAlgClosed (solution)
