-- Prove2me | solution 1 for AutomorphicForm.exists_forall_eLpNorm_foldr_archDeriv_le_mul_rpow_mul_eLpNorm_of_mem_archCutSubmodule_of_archCasimir_eq_smul
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.961684+00:00
-- url     : https://prove2.me/submissions/64087897-36ce-54d0-9fe7-fe806eaddc47

import Definitions.Def_AutomorphicForm_CuspidalConstituent
import Definitions.Def_AutomorphicForm_CanonicalTruncationDomain
import Definitions.Def_AutomorphicForm_ArchDerivCasimirComplex
import Definitions.Def_NumberField_PrincipalLevel
import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_NumberField_AdelicHaar
import Theorems.Thm_AutomorphicForm_exists_forall_eLpNorm_archDerivAt_foldr_le_mul_sqrt_mul_eLpNorm_of_mem_archCutSubmodule_of_archCasimir_eq_smul
import Theorems.Thm_AutomorphicForm_exists_forall_eLpNorm_archDerivAtComplex_foldr_le_mul_sqrt_mul_eLpNorm_of_mem_archCutSubmodule_of_archCasimir_eq_smul
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_exists_forall_eLpNorm_foldr_archDeriv_le_mul_rpow_mul_eLpNorm_of_mem_archCutSubmodule_of_archCasimir_eq_smul
p2m_attr_erase "instance" "AutomorphicForm.compactSpace_maximalCompactAway AutomorphicForm.compactSpace_adelicMaximalCompact AutomorphicForm.isProbabilityMeasure_maximalCompactHaar AutomorphicForm.isHaarMeasure_maximalCompactHaar AutomorphicForm.compactSpace_maximalCompactAt AutomorphicForm.isProbabilityMeasure_maximalCompactAwayHaar AutomorphicForm.isHaarMeasure_maximalCompactAwayHaar AutomorphicForm.isProbabilityMeasure_maximalCompactAtHaar AutomorphicForm.isHaarMeasure_maximalCompactAtHaar instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions instCountableOfNumberField_definitions"
p2m_attr_erase "simp" "AutomorphicForm.CuspidalSpectrum.fdPins_μ AutomorphicForm.CuspidalSpectrum.fdPins_nS AutomorphicForm.CuspidalSpectrum.fdPins_ν AutomorphicForm.CuspidalSpectrum.fdPins_gen AutomorphicForm.CuspidalSpectrum.fdPins_U AutomorphicForm.CuspidalSpectrum.fdPins_D AutomorphicForm.CuspidalSpectrum.fdPins_Z AutomorphicForm.CuspidalSpectrum.mem_detNormSlab AutomorphicForm.CuspidalSpectrum.fdPins_eq AutomorphicForm.CuspidalSpectrum.fdPins_mS AutomorphicForm.mem_inducedSectionSubmodule_iff AutomorphicForm.mem_borelSubgroup_iff AutomorphicForm.borelDiagFst_apply_val AutomorphicForm.borelDiagSnd_apply_val AutomorphicForm.iotaZsqrtdNegTwo_apply LanglandsTunnell.Converse.ArchDatumC.mk.injEq LanglandsTunnell.Converse.ArchDatumC.mk.sizeOf_spec LanglandsTunnell.Converse.FinWhittakerDatum.mk.sizeOf_spec LanglandsTunnell.Converse.ArchDatumR.mk.sizeOf_spec LanglandsTunnell.Converse.ArchDatumR.mk.injEq LanglandsTunnell.Converse.FinWhittakerDatum.mk.injEq LanglandsTunnell.Converse.SOrderReps.mk.sizeOf_spec LanglandsTunnell.Converse.JLData.mk.injEq LanglandsTunnell.Converse.SOrderReps.mk.injEq LanglandsTunnell.Converse.JLData.mk.sizeOf_spec NumberField.StandardAddChar.ratArchLine_apply NumberField.StandardAddChar.AdelicTraceData.mk.sizeOf_spec NumberField.StandardAddChar.AdelicTraceData.mk.injEq AutomorphicForm.whittakerCoefficient_zero NumberField.AdelicTrace.traceDiag_apply NumberField.AdelicTrace.diag_apply LanglandsTunnell.TateLocal.conductorExponentAt_one LanglandsTunnell.TateLocal.charExt_coe_units LanglandsTunnell.TateLocal.modulus_one LanglandsTunnell.TateLocal.modulus_zero LanglandsTunnell.TateLocal.modulus_coe_units LanglandsTunnell.TateLocal.charExt_zero LanglandsTunnell.signEpsilon_one LanglandsTunnell.RealArchParam.epsilonFactor_principal LanglandsTunnell.RealArchParam.epsilonFactor_discrete"
p2m_attr_erase "simp" "LanglandsTunnell.signEpsilon_zero LanglandsTunnell.LDatum.mk.sizeOf_spec LanglandsTunnell.LDatum.badFactor_zero LanglandsTunnell.LDatum.mk.injEq AutomorphicForm.rightTranslationEmbed_smul_apply AdelicDock.coe_finEmbed AdelicDock.splice_apply_self AdelicDock.coe_localEmbed"

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicLevel NumberField.AdelicBox NumberField.AdelicHaar
open AutomorphicForm AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering AutomorphicForm.CuspidalConstituent
open IsDedekindDomain
open scoped ENNReal

attribute [local instance] NumberField.AdelicHaar.glBorel

noncomputable section

namespace SN3Reduce

variable {K : Type} [Field K] [NumberField K]

abbrev Dir (K : Type) [Field K] [NumberField K] : Type :=
  (Σ' w : InfinitePlace K, Σ' _ : w.IsReal, ArchDir) ⊕ (Σ' w : InfinitePlace K, Σ' _ : w.IsComplex, ArchDirComplex)

abbrev Wd (l : List (Dir K)) (b : AdelicGL2 (𝓞 K) K → ℂ) : AdelicGL2 (𝓞 K) K → ℂ :=
  l.foldr (fun d φ => Sum.elim (fun d => archDerivAt d.2.1 d.2.2 φ) (fun d => archDerivAtComplex d.2.1 d.2.2 φ) d) b

theorem sqrt_mul_rpow (Λ : ℝ) (hΛ : 0 ≤ Λ) (k : ℕ) :
    Real.sqrt Λ * Λ ^ ((k : ℝ) / 2) = Λ ^ (((k + 1 : ℕ) : ℝ) / 2) := by
  rw [Real.sqrt_eq_rpow, ← Real.rpow_add' hΛ]
  · congr 1; push_cast; ring
  · push_cast; positivity

end SN3Reduce

open SN3Reduce in
theorem solution
    (K : Type) [Field K] [NumberField K]
    (α β : ℝ) (hα : 0 < α) (hαβ : α < β)
    (tys : ArchTypeFamily K) (m : ℕ) :
    let W : List ((Σ' w : InfinitePlace K, Σ' _ : w.IsReal, ArchDir) ⊕
          (Σ' w : InfinitePlace K, Σ' _ : w.IsComplex, ArchDirComplex)) →
        (AdelicGL2 (𝓞 K) K → ℂ) → (AdelicGL2 (𝓞 K) K → ℂ) :=
      fun l b => l.foldr (fun d φ => Sum.elim (fun d => archDerivAt d.2.1 d.2.2 φ)
        (fun d => archDerivAtComplex d.2.1 d.2.2 φ) d) b
    ∃ c : ℝ, 0 ≤ c ∧
      ∀ (Λ : ℝ), 1 ≤ Λ →
      ∀ b : AdelicGL2 (𝓞 K) K → ℂ,
        (∀ (γ : GL (Fin 2) K) (g : AdelicGL2 (𝓞 K) K), b (globalPoints (𝓞 K) K γ * g) = b g) →
        b ∈ archCutSubmodule K tys →

        (∀ l, l.length ≤ m + 2 →
          Continuous (W l b) ∧
          (∀ (w : InfinitePlace K) (hw : w.IsReal), IsArchSmoothAt hw (W l b)) ∧
          (∀ (w : InfinitePlace K) (hw : w.IsComplex), IsArchSmoothAtComplex hw (W l b)) ∧
          ∃ B : ℝ, ∀ g : AdelicGL2 (𝓞 K) K,
            NumberField.TateGlobal.ideleNorm K (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β → ‖W l b g‖ ≤ B) →

        (∀ (w : InfinitePlace K) (hw : w.IsReal), ∃ lam : ℂ, ‖lam‖ ≤ Λ ∧ archCasimirAt hw b = lam • b) →
        (∀ (w : InfinitePlace K) (hw : w.IsComplex), ∃ lam lam' : ℂ, ‖lam‖ ≤ Λ ∧ ‖lam'‖ ≤ Λ ∧
          archCasimirAtComplex hw b = lam • b ∧ archCasimirBarAtComplex hw b = lam' • b) →
        ∀ l, l.length ≤ m →
          eLpNorm (W l b) 2
              ((adelicGLHaar (Fin 2) (𝓞 K) K).restrict (AutomorphicForm.canonicalTruncationDomain K α β)) ≤
            ENNReal.ofReal (c * Λ ^ ((l.length : ℝ) / 2)) *
              eLpNorm b 2 ((adelicGLHaar (Fin 2) (𝓞 K) K).restrict (AutomorphicForm.canonicalTruncationDomain K α β)) := by
  intro W
  obtain ⟨cR, hcR, HR⟩ :=
    AutomorphicForm.exists_forall_eLpNorm_archDerivAt_foldr_le_mul_sqrt_mul_eLpNorm_of_mem_archCutSubmodule_of_archCasimir_eq_smul
      K α β hα hαβ tys m
  obtain ⟨cC, hcC, HC⟩ :=
    AutomorphicForm.exists_forall_eLpNorm_archDerivAtComplex_foldr_le_mul_sqrt_mul_eLpNorm_of_mem_archCutSubmodule_of_archCasimir_eq_smul
      K α β hα hαβ tys m
  set c₀ : ℝ := max 1 (max cR cC) with hc₀
  have hc₀1 : 1 ≤ c₀ := le_max_left _ _
  have hcR' : cR ≤ c₀ := (le_max_left _ _).trans (le_max_right _ _)
  have hcC' : cC ≤ c₀ := (le_max_right _ _).trans (le_max_right _ _)
  refine ⟨c₀ ^ m, by positivity, ?_⟩
  intro Λ hΛ b hinv hT hreg hcasR hcasC
  have hΛ0 : 0 ≤ Λ := zero_le_one.trans hΛ
  set μ₀ := (adelicGLHaar (Fin 2) (𝓞 K) K).restrict (AutomorphicForm.canonicalTruncationDomain K α β) with hμ₀

  have key : ∀ l : List (Dir K), l.length ≤ m →
      eLpNorm (Wd l b) 2 μ₀ ≤ ENNReal.ofReal (c₀ ^ l.length * Λ ^ ((l.length : ℝ) / 2)) * eLpNorm b 2 μ₀ := by
    intro l
    induction l with
    | nil =>
      intro _
      simp only [List.length_nil, pow_zero, Nat.cast_zero, zero_div, Real.rpow_zero, mul_one, ENNReal.ofReal_one, one_mul]
      exact le_rfl
    | cons d l ih =>
      intro hl
      rw [List.length_cons] at hl
      have hl' : l.length ≤ m := by omega
      have hl1 : l.length + 1 ≤ m := hl
      have ih' := ih hl'
      have step : eLpNorm (Wd (d :: l) b) 2 μ₀ ≤ ENNReal.ofReal (c₀ * Real.sqrt Λ) * eLpNorm (Wd l b) 2 μ₀ := by
        rcases d with ⟨w, hw, d⟩ | ⟨w, hw, d⟩
        · have h := HR Λ hΛ b hinv hT hreg w hw (hcasR w hw) d l hl1
          refine h.trans ?_
          gcongr
        · have h := HC Λ hΛ b hinv hT hreg w hw (hcasC w hw) d l hl1
          refine h.trans ?_
          gcongr
      calc eLpNorm (Wd (d :: l) b) 2 μ₀ ≤ ENNReal.ofReal (c₀ * Real.sqrt Λ) * eLpNorm (Wd l b) 2 μ₀ := step
        _ ≤ ENNReal.ofReal (c₀ * Real.sqrt Λ) * (ENNReal.ofReal (c₀ ^ l.length * Λ ^ ((l.length : ℝ) / 2)) * eLpNorm b 2 μ₀) := by
            gcongr
        _ = ENNReal.ofReal (c₀ ^ (d :: l).length * Λ ^ (((d :: l).length : ℝ) / 2)) * eLpNorm b 2 μ₀ := by
            rw [← mul_assoc, ← ENNReal.ofReal_mul (by positivity), List.length_cons]
            congr 2
            rw [pow_succ, ← sqrt_mul_rpow Λ hΛ0 l.length]
            ring
  intro l hl
  refine (key l hl).trans ?_
  have hpow : c₀ ^ l.length ≤ c₀ ^ m := pow_le_pow_right₀ hc₀1 hl
  gcongr

end

end S_AutomorphicForm_exists_forall_eLpNorm_foldr_archDeriv_le_mul_rpow_mul_eLpNorm_of_mem_archCutSubmodule_of_archCasimir_eq_smul
end P2MW
export P2MW.S_AutomorphicForm_exists_forall_eLpNorm_foldr_archDeriv_le_mul_rpow_mul_eLpNorm_of_mem_archCutSubmodule_of_archCasimir_eq_smul (solution)
