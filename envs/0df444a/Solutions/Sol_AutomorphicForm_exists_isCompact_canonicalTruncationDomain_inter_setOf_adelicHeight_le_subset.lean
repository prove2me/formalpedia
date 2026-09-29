-- Prove2me | solution 1 for AutomorphicForm.exists_isCompact_canonicalTruncationDomain_inter_setOf_adelicHeight_le_subset
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.961684+00:00
-- url     : https://prove2.me/submissions/d4539c1b-eedd-55ac-8d3a-2e0950ccd693

import Theorems.Thm_AutomorphicForm_canonicalTruncationData_isTruncationDatum
import Theorems.Thm_NumberField_AdelicHeight_exists_forall_mul_adelicHeight_le_adelicHeight_mul_of_isCompact
import Theorems.Thm_AutomorphicForm_exists_isCompact_forall_mem_centreCutSiegelSet_archHeight_le_mem
import Theorems.Thm_NumberField_TateGlobal_ideleNorm_det_eq_prod_archDetNorm_pow_mult
import Theorems.Thm_NumberField_TateGlobal_continuous_ideleNorm_det
import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_AutomorphicForm_CanonicalTruncationDomain
import Definitions.Def_NumberField_AdelicHeight
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_exists_isCompact_canonicalTruncationDomain_inter_setOf_adelicHeight_le_subset
p2m_attr_erase "instance" "instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions instCountableOfNumberField_definitions"
p2m_attr_erase "simp" "AutomorphicForm.mem_inducedSectionSubmodule_iff AutomorphicForm.mem_borelSubgroup_iff AutomorphicForm.borelDiagFst_apply_val AutomorphicForm.borelDiagSnd_apply_val M4aHerbrand.IdeleGaloisDescent.mk.sizeOf_spec M4aHerbrand.IdeleGaloisDescent.mk.injEq"

set_option autoImplicit false

open NumberField

open AutomorphicForm AutomorphicForm.WindowedSiegel NumberField.AdelicHeight NumberField.AdelicVolume NumberField.TateGlobal NumberField.AdelicLevel

open scoped Pointwise

theorem solution
    (F : Type) [Field F] [NumberField F]
    (d₁ d₂ : ℝ) (_hd₁ : 0 < d₁) (_hd : d₁ < d₂) (T : ℝ) :
    ∃ C : Set (AdelicGL2 (𝓞 F) F), IsCompact C ∧
      AutomorphicForm.canonicalTruncationDomain F d₁ d₂ ∩
          {g | NumberField.AdelicHeight.adelicHeight F g ≤ T} ⊆ C := by
  classical
  obtain ⟨hc0, hTc, hΦS, hslab, -⟩ := AutomorphicForm.canonicalTruncationData_isTruncationDatum F d₁ d₂ _hd₁ _hd
  set Φ₀ := AutomorphicForm.canonicalTruncationDomain F d₁ d₂ with hΦ₀
  set c₀ := AutomorphicForm.canonicalTruncationFloor F d₁ d₂ with hc₀
  set u₀ := AutomorphicForm.canonicalTruncationWindow F d₁ d₂ with hu₀
  set D₁ := AutomorphicForm.canonicalTruncationLowerCut F d₁ d₂ with hD₁
  set D₂ := AutomorphicForm.canonicalTruncationUpperCut F d₁ d₂ with hD₂
  set Tc := AutomorphicForm.canonicalTruncationTranslates F d₁ d₂ with hTcdef

  obtain ⟨κ, Kup, hκ, hκK⟩ := NumberField.AdelicHeight.exists_forall_mul_adelicHeight_le_adelicHeight_mul_of_isCompact F Tc hTc

  obtain ⟨My0, hMy0⟩ := hTc.exists_bound_of_continuousOn
    (f := fun y : AdelicGL2 (𝓞 F) F => ideleNorm F (Matrix.GeneralLinearGroup.det y))
    (NumberField.TateGlobal.continuous_ideleNorm_det F).continuousOn
  set My : ℝ := max My0 1 with hMy
  have hMypos : 0 < My := one_pos.trans_le (le_max_right _ _)

  set P : ℝ := ∏ w : InfinitePlace F, (max D₂ 1) ^ w.mult with hP
  have hP1 : 1 ≤ P := by
    rw [hP]
    calc (1 : ℝ) = ∏ w : InfinitePlace F, (1 : ℝ) := by simp
      _ ≤ ∏ w : InfinitePlace F, (max D₂ 1) ^ w.mult :=
          Finset.prod_le_prod (fun _ _ => zero_le_one) fun w _ => one_le_pow₀ (le_max_right _ _)
  have hPpos : 0 < P := one_pos.trans_le hP1
  set e : ℝ := d₁ / (My * P) with he
  have hepos : 0 < e := div_pos _hd₁ (mul_pos hMypos hPpos)
  set D₁' : ℝ := min e 1 with hD₁'
  have hD₁'pos : 0 < D₁' := lt_min hepos one_pos

  have hfloor : ∀ s ∈ centreCutSiegelSet F c₀ u₀ D₁ D₂, ∀ y ∈ Tc, s * y ∈ Φ₀ →
      ∀ w : InfinitePlace F, D₁' ≤ archDetNorm w s := by
    intro s hs y hy hsy w₀
    obtain ⟨hint, -, -, hdet⟩ := mem_centreCutSiegelSet_iff.mp hs

    have hslab' := hslab hsy
    simp only [Set.mem_setOf_eq, Set.mem_Icc, map_mul, ideleNorm_mul] at hslab'
    have hy' : ideleNorm F (Matrix.GeneralLinearGroup.det y) ≤ My :=
      ((le_abs_self _).trans ((Real.norm_eq_abs _).symm.le.trans (hMy0 y hy))).trans (le_max_left _ _)
    have hypos : 0 < ideleNorm F (Matrix.GeneralLinearGroup.det y) := ideleNorm_pos _
    have hNs : d₁ / My ≤ ideleNorm F (Matrix.GeneralLinearGroup.det s) := by
      rw [div_le_iff₀ hMypos]
      exact hslab'.1.trans (mul_le_mul le_rfl hy' hypos.le (ideleNorm_pos _).le)

    rw [NumberField.TateGlobal.ideleNorm_det_eq_prod_archDetNorm_pow_mult F s hint] at hNs
    have hapos : ∀ w, 0 < archDetNorm w s := fun w => archDetNorm_pos w s
    have hale : ∀ w, archDetNorm w s ^ w.mult ≤ (max D₂ 1) ^ w.mult := fun w =>
      pow_le_pow_left₀ (hapos w).le ((hdet w).2.trans (le_max_left _ _)) _
    rw [← Finset.mul_prod_erase Finset.univ (fun w => archDetNorm w s ^ w.mult) (Finset.mem_univ w₀)] at hNs
    set Q : ℝ := ∏ w ∈ Finset.univ.erase w₀, archDetNorm w s ^ w.mult with hQ
    have hQpos : 0 < Q := Finset.prod_pos fun w _ => pow_pos (hapos w) _
    have hQP : Q ≤ P := by
      calc Q ≤ ∏ w ∈ Finset.univ.erase w₀, (max D₂ 1) ^ w.mult :=
            Finset.prod_le_prod (fun w _ => (pow_pos (hapos w) _).le) fun w _ => hale w
        _ ≤ P := by
            rw [hP, ← Finset.mul_prod_erase Finset.univ (fun w : InfinitePlace F => (max D₂ 1) ^ w.mult) (Finset.mem_univ w₀)]
            exact le_mul_of_one_le_left
              (Finset.prod_nonneg fun w _ => (pow_pos (one_pos.trans_le (le_max_right D₂ 1)) _).le)
              (one_le_pow₀ (le_max_right _ _))

    have hpow : e ≤ archDetNorm w₀ s ^ w₀.mult := by
      have h1 : d₁ / My ≤ archDetNorm w₀ s ^ w₀.mult * P :=
        hNs.trans (mul_le_mul le_rfl hQP hQpos.le (pow_pos (hapos w₀) _).le)
      rw [he, div_le_iff₀ (mul_pos hMypos hPpos)]
      rw [div_le_iff₀ hMypos] at h1
      nlinarith [h1, hPpos, hMypos]

    by_cases ha1 : 1 ≤ archDetNorm w₀ s
    · exact (min_le_right _ _).trans ha1
    · push Not at ha1
      have hm : 1 ≤ w₀.mult := NumberField.InfinitePlace.mult_pos
      have : archDetNorm w₀ s ^ w₀.mult ≤ archDetNorm w₀ s := by
        calc archDetNorm w₀ s ^ w₀.mult ≤ archDetNorm w₀ s ^ 1 :=
              pow_le_pow_of_le_one (hapos w₀).le ha1.le hm
          _ = archDetNorm w₀ s := pow_one _
      exact (min_le_left _ _).trans (hpow.trans this)

  obtain ⟨K₀, hK₀, hK₀mem⟩ := AutomorphicForm.exists_isCompact_forall_mem_centreCutSiegelSet_archHeight_le_mem F
    (c := c₀) (u := u₀) (d₁ := D₁') (d₂ := D₂) hc0 hD₁'pos (T / κ)
  refine ⟨K₀ * Tc, hK₀.mul hTc, ?_⟩
  rintro g ⟨hg, hgT⟩
  obtain ⟨y, hy, s, hs, rfl⟩ : ∃ y ∈ Tc, ∃ s ∈ centreCutSiegelSet F c₀ u₀ D₁ D₂, s * y = g := by
    have := hΦS hg
    simp only [Set.mem_iUnion, Set.mem_image, exists_prop] at this
    obtain ⟨y, hy, s, hs, hsg⟩ := this
    exact ⟨y, hy, s, hs, hsg⟩
  refine Set.mul_mem_mul (hK₀mem s ?_ ?_) hy
  ·
    obtain ⟨hint, hh, hx, hdet⟩ := mem_centreCutSiegelSet_iff.mp hs
    exact mem_centreCutSiegelSet_iff.mpr ⟨hint, hh, hx, fun w => ⟨hfloor s hs y hy hg w, (hdet w).2⟩⟩
  ·
    obtain ⟨hint, -, -, -⟩ := mem_centreCutSiegelSet_iff.mp hs
    rw [← adelicHeight_eq_archHeight_of_mem hint, le_div_iff₀ hκ, mul_comm]
    exact (hκK s y hy).1.trans hgT

end S_AutomorphicForm_exists_isCompact_canonicalTruncationDomain_inter_setOf_adelicHeight_le_subset
end P2MW
export P2MW.S_AutomorphicForm_exists_isCompact_canonicalTruncationDomain_inter_setOf_adelicHeight_le_subset (solution)
