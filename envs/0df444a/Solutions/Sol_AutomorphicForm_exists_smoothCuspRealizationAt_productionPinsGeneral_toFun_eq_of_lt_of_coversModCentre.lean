-- Prove2me | solution 1 for AutomorphicForm.exists_smoothCuspRealizationAt_productionPinsGeneral_toFun_eq_of_lt_of_coversModCentre
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.961684+00:00
-- url     : https://prove2.me/submissions/9e99a650-1a70-54f2-a53a-606c2227953b

import Mathlib
import Definitions.Def_AutomorphicForm_HeckeEigensystem
import Definitions.Def_AutomorphicForm_ViaCompactCuspNotion
import Definitions.Def_AutomorphicForm_ProductionPinsGeneral
import Definitions.Def_AutomorphicForm_ArithCuspRealization
import Definitions.Def_AutomorphicForm_AutomorphicFnAt
import Definitions.Def_AutomorphicForm_CentreCutSiegelSet
import Definitions.Def_NumberField_AdelicVolume
import Theorems.Thm_AutomorphicForm_not_isArithGenuineCuspRealizable_of_nonpos_of_lt_of_coversModCentre
import Theorems.Thm_AutomorphicForm_coversModCentre_iUnion_centreCutSiegelSet_of_detWindow
import Theorems.Thm_AutomorphicForm_exists_smoothCuspRealizationAt_productionPinsGeneral_toFun_eq_of_coversModCentre
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_exists_smoothCuspRealizationAt_productionPinsGeneral_toFun_eq_of_lt_of_coversModCentre
p2m_attr_erase "instance" "instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions instCountableOfNumberField_definitions"
p2m_attr_erase "simp" "AutomorphicForm.CuspidalSpectrum.fdPins_μ AutomorphicForm.CuspidalSpectrum.fdPins_nS AutomorphicForm.CuspidalSpectrum.fdPins_ν AutomorphicForm.CuspidalSpectrum.fdPins_gen AutomorphicForm.CuspidalSpectrum.fdPins_U AutomorphicForm.CuspidalSpectrum.fdPins_D AutomorphicForm.CuspidalSpectrum.fdPins_Z AutomorphicForm.CuspidalSpectrum.mem_detNormSlab AutomorphicForm.CuspidalSpectrum.fdPins_eq AutomorphicForm.CuspidalSpectrum.fdPins_mS AutomorphicForm.CuspidalConstituent.rightRegular_apply AutomorphicForm.IsStableLinearOn.coe_toEnd_apply AutomorphicForm.ArchRepAt.mk.sizeOf_spec AutomorphicForm.IsIsotypicCuspFormAt.toRealization_toFun AutomorphicForm.ArchTypeFamily.mk.sizeOf_spec AutomorphicForm.charRep_apply AutomorphicForm.ArchRepAt.mk.injEq AutomorphicForm.ArchTypeFamily.mk.injEq M4aHerbrand.IdeleGaloisDescent.mk.sizeOf_spec M4aHerbrand.IdeleGaloisDescent.mk.injEq AutomorphicForm.whittakerCoefficient_zero NumberField.StandardAddChar.ratArchLine_apply NumberField.StandardAddChar.AdelicTraceData.mk.sizeOf_spec NumberField.StandardAddChar.AdelicTraceData.mk.injEq NumberField.AdelicTrace.traceDiag_apply NumberField.AdelicTrace.diag_apply"

set_option autoImplicit false

open NumberField NumberField.AdelicLevel NumberField.AdelicBox AutomorphicForm AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering IsDedekindDomain

private def restrictRealization (D₁ D₂ : Set (AdelicGL2 (𝓞 ℚ) ℚ)) (hsub : D₂ ⊆ D₁)
    (U : Ideal (𝓞 ℚ) → Subgroup (AdelicGL2 (𝓞 ℚ) ℚ)) (gen : HeightOneSpectrum (𝓞 ℚ) → AdelicGL2 (𝓞 ℚ) ℚ)
    (B : Set (AdeleRing (𝓞 ℚ) ℚ)) (Φ : HeckeEigensystem ℚ ℂ)
    (R : SmoothCuspRealizationAt ℚ (productionPinsOf ℚ D₁ U gen B) Φ) :
    SmoothCuspRealizationAt ℚ (productionPinsOf ℚ D₂ U gen B) Φ where
  toFun := R.toFun
  exists_ne_zero := R.exists_ne_zero
  centralChar := R.centralChar
  smoothCusp := by
    refine ⟨⟨?_, R.smoothCusp.1.2⟩, R.smoothCusp.2⟩
    letI := (productionPinsOf ℚ D₁ U gen B).mS
    have hL := (AutomorphicForm.lsXiMemberAt_iff (𝓞 ℚ) ℚ (productionPinsOf ℚ D₁ U gen B).μ
      (productionPinsOf ℚ D₁ U gen B).Z R.centralChar (productionPinsOf ℚ D₁ U gen B).D R.toFun).mp
      R.smoothCusp.1.1
    exact (AutomorphicForm.lsXiMemberAt_iff (𝓞 ℚ) ℚ (productionPinsOf ℚ D₂ U gen B).μ
      (productionPinsOf ℚ D₂ U gen B).Z R.centralChar (productionPinsOf ℚ D₂ U gen B).D R.toFun).mpr
      ⟨hL.1, hL.2.mono_measure (MeasureTheory.Measure.restrict_mono hsub le_rfl)⟩
  level_invariant := R.level_invariant
  exceptionalSet := R.exceptionalSet
  hecke_eigen := R.hecke_eigen
  central_eigen := R.central_eigen

private theorem restrictRealization_genuine (D₁ D₂ : Set (AdelicGL2 (𝓞 ℚ) ℚ)) (hsub : D₂ ⊆ D₁)
    (U : Ideal (𝓞 ℚ) → Subgroup (AdelicGL2 (𝓞 ℚ) ℚ)) (gen : HeightOneSpectrum (𝓞 ℚ) → AdelicGL2 (𝓞 ℚ) ℚ)
    (B : Set (AdeleRing (𝓞 ℚ) ℚ)) (Φ : HeckeEigensystem ℚ ℂ)
    (R : SmoothCuspRealizationAt ℚ (productionPinsOf ℚ D₁ U gen B) Φ)
    (hR : IsGenuineCuspRealizationAt ℚ (productionPinsOf ℚ D₁ U gen B) Φ R) :
    IsGenuineCuspRealizationAt ℚ (productionPinsOf ℚ D₂ U gen B) Φ (restrictRealization D₁ D₂ hsub U gen B Φ R) :=
  hR

theorem solution
    (c u d₁ d₂ : ℝ) (T : Finset (AdelicGL2 (𝓞 ℚ) ℚ)) (hd : d₁ < d₂)
    (hcov : CoversModCentre ℚ (⋃ x ∈ T, (· * x) '' centreCutSiegelSet ℚ c u d₁ d₂))
    (Φ : HeckeEigensystem ℚ ℂ)
    (R : SmoothCuspRealizationAt ℚ
      (productionPinsOf ℚ (⋃ x ∈ T, (· * x) '' centreCutSiegelSet ℚ c u d₁ d₂)
        (fun N => levelOne (𝓞 ℚ) ℚ N ⊓ finiteAdelicGL2Subgroup ℚ) (fun v => heckeGen (𝓞 ℚ) ℚ v)
        (adelicBox ℚ)) Φ)
    (hR : IsGenuineCuspRealizationAt ℚ
      (productionPinsOf ℚ (⋃ x ∈ T, (· * x) '' centreCutSiegelSet ℚ c u d₁ d₂)
        (fun N => levelOne (𝓞 ℚ) ℚ N ⊓ finiteAdelicGL2Subgroup ℚ) (fun v => heckeGen (𝓞 ℚ) ℚ v)
        (adelicBox ℚ)) Φ R) :
    ∃ R' : SmoothCuspRealizationAt ℚ (productionPinsGeneral ℚ) Φ, R'.toFun = R.toFun := by
  rcases le_or_gt c 0 with hc | hc
  · exfalso
    have h := AutomorphicForm.not_isArithGenuineCuspRealizable_of_nonpos_of_lt_of_coversModCentre ℚ c u d₁ d₂ T
      hc hd hcov (AutomorphicForm.HeckeEigensystem.ofRawCentral Φ)
    rw [AutomorphicForm.IsArithGenuineCuspRealizable,
      AutomorphicForm.HeckeEigensystem.toRawCentral_ofRawCentral] at h
    exact h ⟨R, hR⟩
  rcases lt_or_ge 0 d₁ with hd₁ | hd₁
  · exact AutomorphicForm.exists_smoothCuspRealizationAt_productionPinsGeneral_toFun_eq_of_coversModCentre
      c u d₁ d₂ T hc hd₁ hd hcov Φ R hR
  rcases le_or_gt d₂ 0 with hd₂ | hd₂
  · exfalso
    obtain ⟨γ, z, hmem⟩ := hcov 1
    rw [Set.mem_iUnion₂] at hmem
    obtain ⟨x, -, s, hs, -⟩ := hmem
    have hwin := (AutomorphicForm.WindowedSiegel.mem_centreCutSiegelSet_iff.1 hs).2.2.2
      (Classical.arbitrary (InfinitePlace ℚ))
    exact absurd (hwin.2.trans hd₂)
      (not_le.2 (NumberField.AdelicVolume.archDetNorm_pos (Classical.arbitrary (InfinitePlace ℚ)) s))
  · have hcov' := AutomorphicForm.coversModCentre_iUnion_centreCutSiegelSet_of_detWindow ℚ c u d₁ d₂ (d₂ / 2) d₂ T
      (by positivity) (by linarith) hcov
    have hwin : centreCutSiegelSet ℚ c u (d₂ / 2) d₂ ⊆ centreCutSiegelSet ℚ c u d₁ d₂ := by
      intro g hg
      rw [AutomorphicForm.WindowedSiegel.mem_centreCutSiegelSet_iff] at hg ⊢
      exact ⟨hg.1, hg.2.1, hg.2.2.1, fun w => Set.Icc_subset_Icc (by linarith) le_rfl (hg.2.2.2 w)⟩
    have hsub : (⋃ x ∈ T, (· * x) '' centreCutSiegelSet ℚ c u (d₂ / 2) d₂)
        ⊆ ⋃ x ∈ T, (· * x) '' centreCutSiegelSet ℚ c u d₁ d₂ :=
      Set.iUnion₂_mono fun x _ => Set.image_mono hwin
    obtain ⟨R', hR'⟩ :=
      AutomorphicForm.exists_smoothCuspRealizationAt_productionPinsGeneral_toFun_eq_of_coversModCentre
        c u (d₂ / 2) d₂ T hc (by positivity) (by linarith) hcov' Φ (restrictRealization _ _ hsub _ _ _ Φ R)
        (restrictRealization_genuine _ _ hsub _ _ _ Φ R hR)
    exact ⟨R', hR'⟩

end S_AutomorphicForm_exists_smoothCuspRealizationAt_productionPinsGeneral_toFun_eq_of_lt_of_coversModCentre
end P2MW
export P2MW.S_AutomorphicForm_exists_smoothCuspRealizationAt_productionPinsGeneral_toFun_eq_of_lt_of_coversModCentre (solution)
