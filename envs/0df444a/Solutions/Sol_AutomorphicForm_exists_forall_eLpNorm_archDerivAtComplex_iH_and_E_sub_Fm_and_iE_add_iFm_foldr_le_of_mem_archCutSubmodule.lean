-- Prove2me | solution 1 for AutomorphicForm.exists_forall_eLpNorm_archDerivAtComplex_iH_and_E_sub_Fm_and_iE_add_iFm_foldr_le_of_mem_archCutSubmodule
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.961684+00:00
-- url     : https://prove2.me/submissions/bd28a24a-0318-57f5-a6d9-7a15d3679d0e

import Definitions.Def_AutomorphicForm_CuspidalConstituent
import Definitions.Def_AutomorphicForm_CanonicalTruncationDomain
import Definitions.Def_AutomorphicForm_ArchDerivCasimirComplex
import Definitions.Def_NumberField_PrincipalLevel
import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_NumberField_AdelicHaar
import Definitions.Def_AutomorphicForm_ArchDerivCasimirComplexAPI
import Theorems.Thm_AutomorphicForm_setIntegral_comp_mul_eq_setIntegral_of_isFundamentalDomain_of_ideleNorm_det_eq_one
import Theorems.Thm_AutomorphicForm_archDerivAtComplex_iH_eq_smul_of_hasCircleWeightAt_of_isArchSmoothAtComplex
import Theorems.Thm_AutomorphicForm_exists_archDerivAtComplex_Fm_sub_E_and_iE_add_iFm_eq_rightTranslate_iH_rightTranslate
import Theorems.Thm_AutomorphicForm_hasCircleWeightAt_archDelAt_archDelBarAt_archDerivAtComplex_of_hasCircleWeightAt_of_isArchSmoothAtComplex
import Theorems.Thm_AutomorphicForm_exists_forall_eq_sum_hasCircleWeightAt_mem_span_rightTranslate_of_mem_archCutSubmodule_of_isArchSmoothAtComplex
import Theorems.Thm_AutomorphicForm_eLpNorm_sum_weight_smul_le_mul_eLpNorm_sum_of_hasCircleWeightAt
import Theorems.Thm_AutomorphicForm_forall_continuous_isArchSmoothAt_bounded_foldr_archDeriv_rightTranslate_rowIsometryInclAt_of_isComplex
import Theorems.Thm_AutomorphicForm_rightTranslate_foldr_archDeriv_mem_span_foldr_archDeriv_rightTranslate_of_isComplex
import Theorems.Thm_AutomorphicForm_isArchSmoothAtComplex_archDerivAtComplex_and_add_and_smul_and_comm
import Theorems.Thm_AutomorphicForm_canonicalTruncationData_isTruncationDatum
import Theorems.Thm_AutomorphicForm_adelicGLHaar_inter_setOf_ideleNorm_det_mem_Icc_lt_top_of_isFundamentalDomain
import Theorems.Thm_AutomorphicForm_ideleNorm_det_globalPoints
import Theorems.Thm_NumberField_TateGlobal_measurableSet_setOf_ideleNorm_det_mem_Icc
import Theorems.Thm_NumberField_TateGlobal_ideleNorm_det_eq_prod_archDetNorm_pow_mult
import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_exists_forall_eLpNorm_archDerivAtComplex_iH_and_E_sub_Fm_and_iE_add_iFm_foldr_le_of_mem_archCutSubmodule
p2m_attr_erase "instance" "instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions instCountableOfNumberField_definitions AutomorphicForm.compactSpace_maximalCompactAway AutomorphicForm.compactSpace_adelicMaximalCompact AutomorphicForm.isProbabilityMeasure_maximalCompactHaar AutomorphicForm.isHaarMeasure_maximalCompactHaar AutomorphicForm.compactSpace_maximalCompactAt AutomorphicForm.isProbabilityMeasure_maximalCompactAwayHaar AutomorphicForm.isHaarMeasure_maximalCompactAwayHaar AutomorphicForm.isProbabilityMeasure_maximalCompactAtHaar AutomorphicForm.isHaarMeasure_maximalCompactAtHaar"
p2m_attr_erase "simp" "AutomorphicForm.CuspidalSpectrum.fdPins_μ AutomorphicForm.CuspidalSpectrum.fdPins_nS AutomorphicForm.CuspidalSpectrum.fdPins_ν AutomorphicForm.CuspidalSpectrum.fdPins_gen AutomorphicForm.CuspidalSpectrum.fdPins_U AutomorphicForm.CuspidalSpectrum.fdPins_D AutomorphicForm.CuspidalSpectrum.fdPins_Z AutomorphicForm.CuspidalSpectrum.mem_detNormSlab AutomorphicForm.CuspidalSpectrum.fdPins_eq AutomorphicForm.CuspidalSpectrum.fdPins_mS AutomorphicForm.mem_inducedSectionSubmodule_iff AutomorphicForm.mem_borelSubgroup_iff AutomorphicForm.borelDiagFst_apply_val AutomorphicForm.borelDiagSnd_apply_val"

set_option autoImplicit false
set_option maxHeartbeats 1600000

open MeasureTheory NumberField NumberField.AdelicLevel NumberField.AdelicBox NumberField.AdelicHaar
open AutomorphicForm AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering AutomorphicForm.CuspidalConstituent
open IsDedekindDomain
open scoped ComplexConjugate ENNReal

attribute [local instance] NumberField.AdelicHaar.glBorel

noncomputable section

namespace KtypeCfd

variable {K : Type} [Field K] [NumberField K]

section Slab

open scoped Pointwise

attribute [local instance] NumberField.AdelicHaar.borelSpace_glBorel NumberField.AdelicHaar.isHaarMeasure_adelicGLHaar

abbrev slab (K : Type) [Field K] [NumberField K] (a b : ℝ) : Set (AdelicGL2 (𝓞 K) K) :=
  {g | NumberField.TateGlobal.ideleNorm K (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc a b}

abbrev Γp (K : Type) [Field K] [NumberField K] : Subgroup (AdelicGL2 (𝓞 K) K) :=
  (globalPoints (𝓞 K) K).range

scoped instance instCountableK : Countable K :=
  (Module.finBasis ℚ K).equivFun.toEquiv.injective.countable

scoped instance instCountableΓ : Countable ↥(Γp K) := by
  haveI : Countable (Matrix (Fin 2) (Fin 2) K) := inferInstanceAs (Countable (Fin 2 → Fin 2 → K))
  haveI : Countable (GL (Fin 2) K) := Units.val_injective.countable
  exact (MonoidHom.rangeRestrict_surjective (globalPoints (𝓞 K) K)).countable

theorem measurableSet_slab (a b : ℝ) : MeasurableSet (slab K a b) :=
  NumberField.TateGlobal.measurableSet_setOf_ideleNorm_det_mem_Icc K a b

theorem preimage_subtype_mul_slab (γ : ↥(Γp K)) (a b : ℝ) :
    (fun g : AdelicGL2 (𝓞 K) K => (γ : AdelicGL2 (𝓞 K) K) * g) ⁻¹' slab K a b = slab K a b := by
  obtain ⟨_, γ', rfl⟩ := γ
  ext g
  simp only [Set.mem_preimage, Set.mem_setOf_eq, MonoidHom.coe_rangeRestrict, map_mul,
    NumberField.TateGlobal.ideleNorm_mul, AutomorphicForm.ideleNorm_det_globalPoints, one_mul]

theorem smulInvariantMeasure_slab (a b : ℝ) :
    SMulInvariantMeasure ↥(Γp K) (AdelicGL2 (𝓞 K) K) ((adelicGLHaar (Fin 2) (𝓞 K) K).restrict (slab K a b)) := by
  refine ⟨fun γ A hA => ?_⟩
  rw [Measure.restrict_apply (hA.preimage (measurable_const_smul _)), Measure.restrict_apply hA]
  conv_lhs => rw [← preimage_subtype_mul_slab γ a b]
  rw [show (fun x : AdelicGL2 (𝓞 K) K => γ • x) = fun g => (γ : AdelicGL2 (𝓞 K) K) * g from rfl, ← Set.preimage_inter]
  exact SMulInvariantMeasure.measure_preimage_smul γ (hA.inter (measurableSet_slab a b))

theorem exists_measurable_fd (α β : ℝ) (hα : 0 < α) (hαβ : α < β) :
    ∃ 𝓕 : Set (AdelicGL2 (𝓞 K) K), MeasurableSet 𝓕 ∧ 𝓕 ⊆ slab K α β ∧
      IsFundamentalDomain (↥(Γp K)) 𝓕 ((adelicGLHaar (Fin 2) (𝓞 K) K).restrict (slab K α β)) ∧
      (adelicGLHaar (Fin 2) (𝓞 K) K).restrict 𝓕 =
        (adelicGLHaar (Fin 2) (𝓞 K) K).restrict (AutomorphicForm.canonicalTruncationDomain K α β) ∧
      adelicGLHaar (Fin 2) (𝓞 K) K 𝓕 < ⊤ := by
  obtain ⟨-, -, -, hΦs, hΦ⟩ := AutomorphicForm.canonicalTruncationData_isTruncationDatum K α β hα hαβ
  set Φ₀ := AutomorphicForm.canonicalTruncationDomain K α β with hΦ₀
  set μ := adelicGLHaar (Fin 2) (𝓞 K) K with hμ
  set ν := μ.restrict (slab K α β) with hν
  haveI := smulInvariantMeasure_slab (K := K) α β
  obtain ⟨t, ht_sub, ht_m, ht_eq⟩ := hΦ.nullMeasurableSet.exists_measurable_subset_ae_eq
  have hdiff : ν (Φ₀ \ t) = 0 := (ae_eq_set.1 ht_eq).2
  refine ⟨t, ht_m, ht_sub.trans hΦs, ?_, ?_, ?_⟩
  · refine ⟨ht_m.nullMeasurableSet, ?_, fun a b hab => (hΦ.aedisjoint hab).mono
      (Set.smul_set_mono ht_sub) (Set.smul_set_mono ht_sub)⟩
    have hnull : ∀ γ : ↥(Γp K), ∀ᵐ x ∂ν, γ • x ∉ Φ₀ \ t := by
      intro γ
      have h0 : ν ((fun x => γ • x) ⁻¹' (Φ₀ \ t)) = 0 := by
        rw [Set.preimage_smul]
        exact measure_smul_null hdiff γ⁻¹
      exact (measure_eq_zero_iff_ae_notMem.1 h0)
    have hall : ∀ᵐ x ∂ν, ∀ γ : ↥(Γp K), γ • x ∉ Φ₀ \ t := ae_all_iff.2 hnull
    filter_upwards [hΦ.ae_covers, hall] with x hx h2
    obtain ⟨γ, hγ⟩ := hx
    exact ⟨γ, by_contra fun h => h2 γ ⟨hγ, h⟩⟩
  · have h1 : μ (Φ₀ \ t) = 0 := by
      have h := hdiff
      rw [hν, Measure.restrict_apply' (measurableSet_slab α β),
        Set.inter_eq_self_of_subset_left (Set.diff_subset.trans hΦs)] at h
      exact h
    exact Measure.restrict_congr_set (ae_eq_set.2 ⟨by rw [Set.diff_eq_empty.2 ht_sub, measure_empty], h1⟩)
  · exact (measure_mono (Set.subset_inter ht_sub (ht_sub.trans hΦs))).trans_lt
      (AutomorphicForm.adelicGLHaar_inter_setOf_ideleNorm_det_mem_Icc_lt_top_of_isFundamentalDomain K α β hα hαβ Φ₀ hΦ)

end Slab

end KtypeCfd
p2m_reactivate "P2MW.S_AutomorphicForm_exists_forall_eLpNorm_archDerivAtComplex_iH_and_E_sub_Fm_and_iE_add_iFm_foldr_le_of_mem_archCutSubmodule.KtypeCfd"

namespace KtypeC

variable {K : Type} [Field K] [NumberField K]

abbrev Dir (K : Type) [Field K] [NumberField K] : Type :=
  (Σ' w : InfinitePlace K, Σ' _ : w.IsReal, ArchDir) ⊕ (Σ' w : InfinitePlace K, Σ' _ : w.IsComplex, ArchDirComplex)

abbrev D1 (d : Dir K) (φ : AdelicGL2 (𝓞 K) K → ℂ) : AdelicGL2 (𝓞 K) K → ℂ :=
  Sum.elim (fun d => archDerivAt d.2.1 d.2.2 φ) (fun d => archDerivAtComplex d.2.1 d.2.2 φ) d

abbrev Wd (l : List (Dir K)) (b : AdelicGL2 (𝓞 K) K → ℂ) : AdelicGL2 (𝓞 K) K → ℂ :=
  l.foldr (fun d φ => Sum.elim (fun d => archDerivAt d.2.1 d.2.2 φ) (fun d => archDerivAtComplex d.2.1 d.2.2 φ) d) b

abbrev R {w : InfinitePlace K} (hw : w.IsReal) (x : ArchDir) : Dir K := Sum.inl ⟨w, hw, x⟩

abbrev place (d : Dir K) : InfinitePlace K := Sum.elim (fun e => e.1) (fun e => e.1) d

abbrev slab (K : Type) [Field K] [NumberField K] (a b : ℝ) : Set (AdelicGL2 (𝓞 K) K) :=
  {g | NumberField.TateGlobal.ideleNorm K (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc a b}

theorem Wd_nil (b : AdelicGL2 (𝓞 K) K → ℂ) : Wd [] b = b := rfl

theorem Wd_cons (d : Dir K) (l : List (Dir K)) (b : AdelicGL2 (𝓞 K) K → ℂ) : Wd (d :: l) b = D1 d (Wd l b) := rfl

theorem Wd_append (l l' : List (Dir K)) (b : AdelicGL2 (𝓞 K) K → ℂ) : Wd (l ++ l') b = Wd l (Wd l' b) :=
  List.foldr_append

theorem archDerivAtComplex_comp_mul_left {w : InfinitePlace K} (hw : w.IsComplex) (d : ArchDirComplex)
    (φ : AdelicGL2 (𝓞 K) K → ℂ) (h : AdelicGL2 (𝓞 K) K) :
    archDerivAtComplex hw d (fun g => φ (h * g)) = fun g => archDerivAtComplex hw d φ (h * g) := by
  funext g
  show deriv (fun t : ℝ => φ (h * (g * archFlowAtComplex hw d t))) 0 =
    deriv (fun t : ℝ => φ (h * g * archFlowAtComplex hw d t)) 0
  simp only [mul_assoc]

theorem D1_comp_mul_left (d : Dir K) (φ : AdelicGL2 (𝓞 K) K → ℂ) (h : AdelicGL2 (𝓞 K) K) :
    D1 d (fun g => φ (h * g)) = fun g => D1 d φ (h * g) := by
  rcases d with ⟨w, hw, d⟩ | ⟨w, hw, d⟩
  · exact archDerivAt_comp_mul_left hw d φ h
  · exact archDerivAtComplex_comp_mul_left hw d φ h

theorem IsArchSmoothAtComplex.add' {w : InfinitePlace K} {hw : w.IsComplex} {φ ψ : AdelicGL2 (𝓞 K) K → ℂ}
    (hφ : IsArchSmoothAtComplex hw φ) (hψ : IsArchSmoothAtComplex hw ψ) : IsArchSmoothAtComplex hw (φ + ψ) := by
  intro g
  show ContDiffOn ℝ (⊤ : ℕ∞) (fun e => φ (g * archComplexLiftAt hw e) + ψ (g * archComplexLiftAt hw e)) _
  exact (hφ g).add (hψ g)

def SmoothFor (d : Dir K) (φ : AdelicGL2 (𝓞 K) K → ℂ) : Prop :=
  Sum.elim (fun e => IsArchSmoothAt e.2.1 φ) (fun e => IsArchSmoothAtComplex e.2.1 φ) d

theorem D1_add (d : Dir K) {φ ψ : AdelicGL2 (𝓞 K) K → ℂ} (hφ : SmoothFor d φ) (hψ : SmoothFor d ψ) :
    D1 d (φ + ψ) = D1 d φ + D1 d ψ := by
  rcases d with ⟨w, hw, x⟩ | ⟨w, hw, x⟩
  · exact archDerivAt_add hφ hψ x
  · exact (AutomorphicForm.isArchSmoothAtComplex_archDerivAtComplex_and_add_and_smul_and_comm K w hw).2.1 φ ψ hφ hψ x

theorem D1_smul (d : Dir K) (c : ℂ) (φ : AdelicGL2 (𝓞 K) K → ℂ) : D1 d (c • φ) = c • D1 d φ := by
  rcases d with ⟨w, hw, x⟩ | ⟨w, hw, x⟩
  · exact archDerivAt_smul hw x c φ
  · exact (AutomorphicForm.isArchSmoothAtComplex_archDerivAtComplex_and_add_and_smul_and_comm K w hw).2.2.1 c φ x

theorem D1_zero (d : Dir K) : D1 d (0 : AdelicGL2 (𝓞 K) K → ℂ) = 0 := by
  rcases d with ⟨w, hw, x⟩ | ⟨w, hw, x⟩
  · exact archDerivAt_const hw x 0
  · exact archDerivAtComplex_const hw x 0

theorem Wd_smul (l : List (Dir K)) (c : ℂ) (φ : AdelicGL2 (𝓞 K) K → ℂ) : Wd l (c • φ) = c • Wd l φ := by
  induction l with
  | nil => rfl
  | cons d l ih => rw [Wd_cons, Wd_cons, ih, D1_smul]

theorem Wd_zero (l : List (Dir K)) : Wd l (0 : AdelicGL2 (𝓞 K) K → ℂ) = 0 := by
  induction l with
  | nil => rfl
  | cons d l ih => rw [Wd_cons, ih, D1_zero]

def RegL (α β : ℝ) (j : ℕ) (ψ : AdelicGL2 (𝓞 K) K → ℂ) : Prop :=
  (∀ (γ : GL (Fin 2) K) (g : AdelicGL2 (𝓞 K) K), ψ (globalPoints (𝓞 K) K γ * g) = ψ g) ∧
  ∀ l : List (Dir K), l.length ≤ j →
    Continuous (Wd l ψ) ∧
    (∀ (v : InfinitePlace K) (hv : v.IsReal), IsArchSmoothAt hv (Wd l ψ)) ∧
    (∀ (v : InfinitePlace K) (hv : v.IsComplex), IsArchSmoothAtComplex hv (Wd l ψ)) ∧
    ∃ B : ℝ, ∀ g : AdelicGL2 (𝓞 K) K, g ∈ slab K α β → ‖Wd l ψ g‖ ≤ B

variable {α β : ℝ}

theorem RegL.smoothFor {j : ℕ} {ψ : AdelicGL2 (𝓞 K) K → ℂ} (h : RegL α β j ψ) (d : Dir K)
    (l : List (Dir K)) (hl : l.length ≤ j) : SmoothFor d (Wd l ψ) := by
  rcases d with ⟨w, hw, x⟩ | ⟨w, hw, x⟩
  · exact (h.2 l hl).2.1 w hw
  · exact (h.2 l hl).2.2.1 w hw

theorem RegL.smoothFor0 {j : ℕ} {ψ : AdelicGL2 (𝓞 K) K → ℂ} (h : RegL α β j ψ) (d : Dir K) :
    SmoothFor d ψ :=
  h.smoothFor d [] (Nat.zero_le _)

theorem RegL.mono {j j' : ℕ} {ψ : AdelicGL2 (𝓞 K) K → ℂ} (h : RegL α β j ψ) (hj : j' ≤ j) : RegL α β j' ψ :=
  ⟨h.1, fun l hl => h.2 l (hl.trans hj)⟩

theorem RegL.zero (j : ℕ) : RegL α β j (0 : AdelicGL2 (𝓞 K) K → ℂ) := by
  refine ⟨fun _ _ => rfl, fun l _ => ?_⟩
  rw [Wd_zero]
  exact ⟨continuous_const, fun v hv => isArchSmoothAt_const hv 0, fun v hv => isArchSmoothAtComplex_const hv 0,
    ⟨0, fun g _ => by simp⟩⟩

theorem RegL.smul {j : ℕ} {ψ : AdelicGL2 (𝓞 K) K → ℂ} (h : RegL α β j ψ) (c : ℂ) : RegL α β j (c • ψ) := by
  refine ⟨fun γ g => by simp only [Pi.smul_apply, h.1 γ g], fun l hl => ?_⟩
  obtain ⟨hc, hsR, hsC, B, hB⟩ := h.2 l hl
  rw [Wd_smul]
  refine ⟨hc.const_smul c, fun v hv => (hsR v hv).smul c, fun v hv => ?_, ⟨‖c‖ * B, fun g hg => ?_⟩⟩
  · intro g
    show ContDiffOn ℝ (⊤ : ℕ∞) (fun e => c * Wd l ψ (g * archComplexLiftAt hv e)) _
    exact contDiffOn_const.mul (hsC v hv g)
  · rw [Pi.smul_apply, norm_smul]
    exact mul_le_mul_of_nonneg_left (hB g hg) (norm_nonneg _)

theorem Wd_add_of_regL {j : ℕ} {φ ψ : AdelicGL2 (𝓞 K) K → ℂ} (hφ : RegL α β j φ) (hψ : RegL α β j ψ) :
    ∀ l : List (Dir K), l.length ≤ j + 1 → Wd l (φ + ψ) = Wd l φ + Wd l ψ
  | [], _ => rfl
  | d :: l, hl => by
    rw [List.length_cons] at hl
    rw [Wd_cons, Wd_cons, Wd_cons, Wd_add_of_regL hφ hψ l (by omega),
      D1_add d (hφ.smoothFor d l (by omega)) (hψ.smoothFor d l (by omega))]

theorem RegL.add {j : ℕ} {φ ψ : AdelicGL2 (𝓞 K) K → ℂ} (hφ : RegL α β j φ) (hψ : RegL α β j ψ) :
    RegL α β j (φ + ψ) := by
  refine ⟨fun γ g => by simp only [Pi.add_apply, hφ.1 γ g, hψ.1 γ g], fun l hl => ?_⟩
  obtain ⟨hc, hsR, hsC, B, hB⟩ := hφ.2 l hl
  obtain ⟨hc', hsR', hsC', B', hB'⟩ := hψ.2 l hl
  rw [Wd_add_of_regL hφ hψ l (by omega)]
  exact ⟨hc.add hc', fun v hv => (hsR v hv).add (hsR' v hv), fun v hv => IsArchSmoothAtComplex.add' (hsC v hv) (hsC' v hv),
    ⟨B + B', fun g hg => (norm_add_le _ _).trans (add_le_add (hB g hg) (hB' g hg))⟩⟩

theorem RegL.sum {j : ℕ} {ι : Type} (s : Finset ι) {p : ι → AdelicGL2 (𝓞 K) K → ℂ}
    (h : ∀ i ∈ s, RegL α β j (p i)) : RegL α β j (∑ i ∈ s, p i) := by
  classical
  induction s using Finset.induction_on with
  | empty => rw [Finset.sum_empty]; exact RegL.zero j
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact (h a (Finset.mem_insert_self a s)).add (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

theorem D1_sum_of_regL {j : ℕ} {ι : Type} (s : Finset ι) {p : ι → AdelicGL2 (𝓞 K) K → ℂ}
    (h : ∀ i ∈ s, RegL α β j (p i)) (d : Dir K) : D1 d (∑ i ∈ s, p i) = ∑ i ∈ s, D1 d (p i) := by
  classical
  induction s using Finset.induction_on with
  | empty => rw [Finset.sum_empty, Finset.sum_empty, D1_zero]
  | insert a s ha ih =>
    have h' : ∀ i ∈ s, RegL α β j (p i) := fun i hi => h i (Finset.mem_insert_of_mem hi)
    rw [Finset.sum_insert ha, Finset.sum_insert ha,
      D1_add d ((h a (Finset.mem_insert_self a s)).smoothFor0 d) ((RegL.sum s h').smoothFor0 d), ih h']

theorem RegL.letter {j : ℕ} {ψ : AdelicGL2 (𝓞 K) K → ℂ} (h : RegL α β (j + 1) ψ) (d : Dir K) :
    RegL α β j (D1 d ψ) := by
  refine ⟨fun γ g => ?_, fun l hl => ?_⟩
  · have e := D1_comp_mul_left d ψ (globalPoints (𝓞 K) K γ)
    have hψ' : (fun g => ψ (globalPoints (𝓞 K) K γ * g)) = ψ := funext fun g => h.1 γ g
    rw [hψ'] at e
    exact (congrFun e g).symm
  · have e : Wd l (D1 d ψ) = Wd (l ++ [d]) ψ := by rw [Wd_append]; rfl
    rw [e]
    exact h.2 (l ++ [d]) (by rw [List.length_append, List.length_singleton]; omega)

theorem RegL.of_mem_span {j : ℕ} {ι : Type} {f : ι → AdelicGL2 (𝓞 K) K → ℂ} (hf : ∀ i, RegL α β j (f i))
    {c : AdelicGL2 (𝓞 K) K → ℂ} (hc : c ∈ Submodule.span ℂ (Set.range f)) : RegL α β j c := by
  refine Submodule.span_induction (p := fun c _ => RegL α β j c) ?_ (RegL.zero j) (fun _ _ _ _ h₁ h₂ => h₁.add h₂)
    (fun a _ _ h₁ => h₁.smul a) hc
  rintro _ ⟨i, rfl⟩
  exact hf i

section Weights

variable {w : InfinitePlace K} (hw : w.IsComplex)

abbrev Wt (hw : w.IsComplex) (n : ℤ) (ψ : AdelicGL2 (𝓞 K) K → ℂ) : Prop := HasCircleWeightAt hw n ψ

abbrev Cx (hw : w.IsComplex) (X : ArchDirComplex) : Dir K := Sum.inr ⟨w, hw, X⟩

theorem Wt.zero (n : ℤ) : Wt hw n (0 : AdelicGL2 (𝓞 K) K → ℂ) := fun ζ _ g => by simp

theorem Wt.add {n : ℤ} {φ ψ : AdelicGL2 (𝓞 K) K → ℂ} (hφ : Wt hw n φ) (hψ : Wt hw n ψ) : Wt hw n (φ + ψ) :=
  fun ζ hζ g => by rw [Pi.add_apply, Pi.add_apply, hφ ζ hζ g, hψ ζ hζ g, mul_add]

theorem Wt.smul {n : ℤ} {φ : AdelicGL2 (𝓞 K) K → ℂ} (hφ : Wt hw n φ) (c : ℂ) : Wt hw n (c • φ) :=
  fun ζ hζ g => by rw [Pi.smul_apply, Pi.smul_apply, hφ ζ hζ g, smul_eq_mul, smul_eq_mul]; ring

theorem Wt.sum {n : ℤ} {ι : Type} (s : Finset ι) {p : ι → AdelicGL2 (𝓞 K) K → ℂ}
    (h : ∀ i ∈ s, Wt hw n (p i)) : Wt hw n (∑ i ∈ s, p i) := by
  classical
  induction s using Finset.induction_on with
  | empty => rw [Finset.sum_empty]; exact Wt.zero hw n
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact Wt.add hw (h a (Finset.mem_insert_self a s)) (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

theorem wt_letter_of_ne {n : ℤ} {ψ : AdelicGL2 (𝓞 K) K → ℂ} (hψ : Wt hw n ψ) (d : Dir K) (hd : place d ≠ w) :
    Wt hw n (D1 d ψ) := by
  intro ζ hζ g
  rcases d with ⟨w', hw', x⟩ | ⟨w', hw', x⟩
  · change w' ≠ w at hd
    show deriv (fun t : ℝ => ψ (g * archCircleAt hw ζ * archFlowAt hw' x t)) 0 =
      (ζ : ℂ) ^ n * deriv (fun t : ℝ => ψ (g * archFlowAt hw' x t)) 0
    have hc : ∀ t : ℝ, g * archCircleAt hw ζ * archFlowAt hw' x t = g * archFlowAt hw' x t * archCircleAt hw ζ := fun t => by
      rw [mul_assoc, mul_assoc]
      congr 1
      exact (commute_adelicArchGLInclAt_of_ne K hd.symm _ _).eq
    simp_rw [hc, hψ ζ hζ]
    exact deriv_const_mul_field _
  · change w' ≠ w at hd
    show deriv (fun t : ℝ => ψ (g * archCircleAt hw ζ * archFlowAtComplex hw' x t)) 0 =
      (ζ : ℂ) ^ n * deriv (fun t : ℝ => ψ (g * archFlowAtComplex hw' x t)) 0
    have hc : ∀ t : ℝ, g * archCircleAt hw ζ * archFlowAtComplex hw' x t =
        g * archFlowAtComplex hw' x t * archCircleAt hw ζ := fun t => by
      rw [mul_assoc, mul_assoc]
      congr 1
      exact (commute_adelicArchGLInclAt_of_ne K hd.symm _ _).eq
    simp_rw [hc, hψ ζ hζ]
    exact deriv_const_mul_field _

def piece (X : ArchDirComplex) (ψ : AdelicGL2 (𝓞 K) K → ℂ) : Fin 2 → AdelicGL2 (𝓞 K) K → ℂ :=
  match X with
  | .H => ![archDerivAtComplex hw .H ψ, 0]
  | .iH => ![archDerivAtComplex hw .iH ψ, 0]
  | .E => ![archDelAt hw .E ψ, archDelBarAt hw .E ψ]
  | .Fm => ![archDelAt hw .Fm ψ, archDelBarAt hw .Fm ψ]
  | .iE => ![Complex.I • archDelAt hw .E ψ, (-Complex.I) • archDelBarAt hw .E ψ]
  | .iFm => ![Complex.I • archDelAt hw .Fm ψ, (-Complex.I) • archDelBarAt hw .Fm ψ]

def shift : ArchDirComplex → Fin 2 → ℤ
  | .H => ![0, 0]
  | .iH => ![0, 0]
  | .E => ![2, -2]
  | .Fm => ![-2, 2]
  | .iE => ![2, -2]
  | .iFm => ![-2, 2]

theorem D_toComplex_eq (e : ArchDir) (v : AdelicGL2 (𝓞 K) K → ℂ) :
    archDerivAtComplex hw e.toComplex v = archDelAt hw e v + archDelBarAt hw e v := by
  funext g; simp only [archDelAt, archDelBarAt, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]; ring

theorem D_toComplexI_eq (e : ArchDir) (v : AdelicGL2 (𝓞 K) K → ℂ) :
    archDerivAtComplex hw e.toComplexI v = Complex.I • archDelAt hw e v + (-Complex.I) • archDelBarAt hw e v := by
  funext g
  simp only [archDelAt, archDelBarAt, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  ring_nf
  simp only [Complex.I_sq]
  ring

theorem archDerivAtComplex_eq_sum_piece (X : ArchDirComplex) (ψ : AdelicGL2 (𝓞 K) K → ℂ) :
    archDerivAtComplex hw X ψ = ∑ r : Fin 2, piece hw X ψ r := by
  rw [Fin.sum_univ_two]
  cases X with
  | H => simp [piece]
  | iH => simp [piece]
  | E => exact (by first | simpa [piece] using D_toComplex_eq hw .E ψ | (simpa [piece] using (D_toComplex_eq hw .E ψ :)) | (simpa [Function.comp_def] using D_toComplex_eq hw .E ψ) | exact D_toComplex_eq hw .E ψ | (have h__ := D_toComplex_eq hw .E ψ; (try simp [piece] at h__); (try simp [piece]); exact h__))
  | Fm => exact (by first | simpa [piece] using D_toComplex_eq hw .Fm ψ | (simpa [piece] using (D_toComplex_eq hw .Fm ψ :)) | (simpa [Function.comp_def] using D_toComplex_eq hw .Fm ψ) | exact D_toComplex_eq hw .Fm ψ | (have h__ := D_toComplex_eq hw .Fm ψ; (try simp [piece] at h__); (try simp [piece]); exact h__))
  | iE => exact (by first | simpa [piece] using D_toComplexI_eq hw .E ψ | (simpa [piece] using (D_toComplexI_eq hw .E ψ :)) | (simpa [Function.comp_def] using D_toComplexI_eq hw .E ψ) | exact D_toComplexI_eq hw .E ψ | (have h__ := D_toComplexI_eq hw .E ψ; (try simp [piece] at h__); (try simp [piece]); exact h__))
  | iFm => exact (by first | simpa [piece] using D_toComplexI_eq hw .Fm ψ | (simpa [piece] using (D_toComplexI_eq hw .Fm ψ :)) | (simpa [Function.comp_def] using D_toComplexI_eq hw .Fm ψ) | exact D_toComplexI_eq hw .Fm ψ | (have h__ := D_toComplexI_eq hw .Fm ψ; (try simp [piece] at h__); (try simp [piece]); exact h__))

theorem wt_piece {n : ℤ} {ψ : AdelicGL2 (𝓞 K) K → ℂ} (hs : IsArchSmoothAtComplex hw ψ) (hψ : Wt hw n ψ)
    (X : ArchDirComplex) (r : Fin 2) : Wt hw (n + shift X r) (piece hw X ψ r) := by
  obtain ⟨hE1, hE2, hF1, hF2, hH, hI⟩ :=
    AutomorphicForm.hasCircleWeightAt_archDelAt_archDelBarAt_archDerivAtComplex_of_hasCircleWeightAt_of_isArchSmoothAtComplex
      K w hw n ψ hs hψ
  cases X <;> fin_cases r
  · simpa [piece, shift] using hH
  · simpa [piece, shift] using Wt.zero hw (n + 0)
  · simpa [piece, shift] using hE1
  · show Wt hw (n + -2) (archDelBarAt hw .E ψ); rw [← sub_eq_add_neg]; exact hE2
  · show Wt hw (n + -2) (archDelAt hw .Fm ψ); rw [← sub_eq_add_neg]; exact hF1
  · simpa [piece, shift] using hF2
  · simpa [piece, shift] using hI
  · simpa [piece, shift] using Wt.zero hw (n + 0)
  · simpa [piece, shift] using Wt.smul hw hE1 Complex.I
  · show Wt hw (n + -2) ((-Complex.I) • archDelBarAt hw .E ψ); rw [← sub_eq_add_neg]; exact Wt.smul hw hE2 _
  · show Wt hw (n + -2) (Complex.I • archDelAt hw .Fm ψ); rw [← sub_eq_add_neg]; exact Wt.smul hw hF1 _
  · simpa [piece, shift] using Wt.smul hw hF2 (-Complex.I)

theorem abs_shift_le (X : ArchDirComplex) (r : Fin 2) : |shift X r| ≤ 2 := by
  cases X <;> fin_cases r <;> simp [shift]

end Weights
p2m_reactivate "P2MW.S_AutomorphicForm_exists_forall_eLpNorm_archDerivAtComplex_iH_and_E_sub_Fm_and_iE_add_iFm_foldr_le_of_mem_archCutSubmodule.KtypeCfd"

theorem del_eq_lin2 {w : InfinitePlace K} (hw : w.IsComplex) (e : ArchDir) (v : AdelicGL2 (𝓞 K) K → ℂ) :
    archDelAt hw e v = (1 / 2 : ℂ) • archDerivAtComplex hw e.toComplex v +
      (-(Complex.I / 2)) • archDerivAtComplex hw e.toComplexI v := by
  funext g
  simp only [archDelAt, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  ring

theorem delbar_eq_lin2 {w : InfinitePlace K} (hw : w.IsComplex) (e : ArchDir) (v : AdelicGL2 (𝓞 K) K → ℂ) :
    archDelBarAt hw e v = (1 / 2 : ℂ) • archDerivAtComplex hw e.toComplex v +
      (Complex.I / 2) • archDerivAtComplex hw e.toComplexI v := by
  funext g
  simp only [archDelBarAt, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  ring

theorem regL_del {α β : ℝ} {w : InfinitePlace K} (hw : w.IsComplex) {j : ℕ} {ψ : AdelicGL2 (𝓞 K) K → ℂ}
    (h : RegL α β (j + 1) ψ) (e : ArchDir) : RegL α β j (archDelAt hw e ψ) ∧ RegL α β j (archDelBarAt hw e ψ) := by
  have h1 : RegL α β j (archDerivAtComplex hw e.toComplex ψ) := h.letter (Cx hw e.toComplex)
  have h2 : RegL α β j (archDerivAtComplex hw e.toComplexI ψ) := h.letter (Cx hw e.toComplexI)
  constructor
  · rw [del_eq_lin2]; exact (h1.smul _).add (h2.smul _)
  · rw [delbar_eq_lin2]; exact (h1.smul _).add (h2.smul _)

theorem regL_piece {α β : ℝ} {w : InfinitePlace K} (hw : w.IsComplex) {j : ℕ} {ψ : AdelicGL2 (𝓞 K) K → ℂ}
    (h : RegL α β (j + 1) ψ) (X : ArchDirComplex) (r : Fin 2) : RegL α β j (piece hw X ψ r) := by
  cases X <;> fin_cases r
  · simpa [piece] using h.letter (Cx hw .H)
  · simpa [piece] using RegL.zero (α := α) (β := β) j
  · simpa [piece] using (regL_del hw h .E).1
  · simpa [piece] using (regL_del hw h .E).2
  · simpa [piece] using (regL_del hw h .Fm).1
  · simpa [piece] using (regL_del hw h .Fm).2
  · simpa [piece] using h.letter (Cx hw .iH)
  · simpa [piece] using RegL.zero (α := α) (β := β) j
  · simpa [piece] using (regL_del hw h .E).1.smul Complex.I
  · simpa [piece] using (regL_del hw h .E).2.smul (-Complex.I)
  · simpa [piece] using (regL_del hw h .Fm).1.smul Complex.I
  · simpa [piece] using (regL_del hw h .Fm).2.smul (-Complex.I)

end KtypeC
p2m_reactivate "P2MW.S_AutomorphicForm_exists_forall_eLpNorm_archDerivAtComplex_iH_and_E_sub_Fm_and_iE_add_iFm_foldr_le_of_mem_archCutSubmodule.KtypeCfd"

namespace KtypeC

variable {K : Type} [Field K] [NumberField K]

section Main

variable {α β : ℝ} {w : InfinitePlace K} (hw : w.IsComplex)

def Inv (α β : ℝ) (hw : w.IsComplex) (j : ℕ) (N : ℤ) (φ : AdelicGL2 (𝓞 K) K → ℂ) : Prop :=
  ∃ (ι : Type) (_ : Fintype ι) (p : ι → AdelicGL2 (𝓞 K) K → ℂ) (wt : ι → ℤ),
    (∀ i, Wt hw (wt i) (p i)) ∧ (∀ i, RegL α β j (p i)) ∧ (∀ i, |wt i| ≤ N) ∧ φ = ∑ i, p i

theorem Inv.mono_N {j : ℕ} {N N' : ℤ} {φ : AdelicGL2 (𝓞 K) K → ℂ} (h : Inv α β hw j N φ) (hN : N ≤ N') :
    Inv α β hw j N' φ := by
  obtain ⟨ι, _, p, wt, h1, h2, h3, h4⟩ := h
  exact ⟨ι, inferInstance, p, wt, h1, h2, fun i => (h3 i).trans hN, h4⟩

theorem Inv.letter_ne {j : ℕ} {N : ℤ} {φ : AdelicGL2 (𝓞 K) K → ℂ} (h : Inv α β hw (j + 1) N φ) (d : Dir K)
    (hd : place d ≠ w) : Inv α β hw j N (D1 d φ) := by
  obtain ⟨ι, _, p, wt, h1, h2, h3, h4⟩ := h
  refine ⟨ι, inferInstance, fun i => D1 d (p i), wt, fun i => wt_letter_of_ne hw (h1 i) d hd,
    fun i => (h2 i).letter d, h3, ?_⟩
  rw [h4]
  exact D1_sum_of_regL Finset.univ (fun i _ => h2 i) d

theorem Inv.letter_same {j : ℕ} {N : ℤ} {φ : AdelicGL2 (𝓞 K) K → ℂ} (h : Inv α β hw (j + 1) N φ) (x : ArchDirComplex) :
    Inv α β hw j (N + 2) (archDerivAtComplex hw x φ) := by
  obtain ⟨ι, _, p, wt, h1, h2, h3, h4⟩ := h
  refine ⟨ι × Fin 2, inferInstance, fun ir => piece hw x (p ir.1) ir.2, fun ir => wt ir.1 + shift x ir.2,
    fun ir => wt_piece hw ((h2 ir.1).smoothFor (Cx hw x) [] (Nat.zero_le _)) (h1 ir.1) x ir.2,
    fun ir => regL_piece hw (h2 ir.1) x ir.2,
    fun ir => (abs_add_le _ _).trans (add_le_add (h3 ir.1) (abs_shift_le x ir.2)), ?_⟩
  rw [h4]
  have e : archDerivAtComplex hw x (∑ i, p i) = D1 (Cx hw x) (∑ i, p i) := rfl
  rw [e, D1_sum_of_regL Finset.univ (fun i _ => h2 i) (Cx hw x), Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun i _ => ?_
  exact archDerivAtComplex_eq_sum_piece hw x (p i)

theorem Inv.letter {j : ℕ} {N : ℤ} {φ : AdelicGL2 (𝓞 K) K → ℂ} (h : Inv α β hw (j + 1) N φ) (d : Dir K) :
    Inv α β hw j (N + 2) (D1 d φ) := by
  by_cases hd : place d = w
  · rcases d with ⟨w', hw', x⟩ | ⟨w', hw', x⟩
    · change w' = w at hd
      subst hd
      exact absurd hw' (NumberField.InfinitePlace.not_isReal_iff_isComplex.2 hw)
    · change w' = w at hd
      subst hd
      exact h.letter_same hw x
  · exact (h.letter_ne hw d hd).mono_N hw (by linarith)

theorem inv_words {m : ℕ} {n₀ : ℤ} {b : AdelicGL2 (𝓞 K) K → ℂ} (hb : Inv α β hw (m + 2) n₀ b) :
    ∀ l : List (Dir K), l.length ≤ m + 2 → Inv α β hw (m + 2 - l.length) (n₀ + 2 * l.length) (Wd l b)
  | [], _ => by simpa using hb
  | d :: l, hl => by
    rw [List.length_cons] at hl
    have ih := inv_words hb l (by omega)
    have e : m + 2 - l.length = (m + 2 - (l.length + 1)) + 1 := by omega
    rw [e] at ih
    have h := ih.letter hw d
    show Inv α β hw (m + 2 - (l.length + 1)) (n₀ + 2 * ((l.length + 1 : ℕ) : ℤ)) (D1 d (Wd l b))
    have e2 : (n₀ + 2 * ((l.length + 1 : ℕ) : ℤ)) = n₀ + 2 * (l.length : ℤ) + 2 := by push_cast; ring
    rw [e2]
    exact h

theorem bound_of_inv (hα : 0 < α) (hαβ : α < β) {j : ℕ} {N : ℕ} {φ : AdelicGL2 (𝓞 K) K → ℂ}
    (h : Inv α β hw (j + 1) N φ) :
    eLpNorm (archDerivAtComplex hw .iH φ) 2
        ((adelicGLHaar (Fin 2) (𝓞 K) K).restrict (AutomorphicForm.canonicalTruncationDomain K α β)) ≤
      (N : ENNReal) * eLpNorm φ 2
        ((adelicGLHaar (Fin 2) (𝓞 K) K).restrict (AutomorphicForm.canonicalTruncationDomain K α β)) := by
  classical
  obtain ⟨ι, _, p, wt, h1, h2, h3, h4⟩ := h

  set ψ : ℤ → AdelicGL2 (𝓞 K) K → ℂ := fun n => ∑ i ∈ Finset.univ.filter (fun i => wt i = n), p i with hψ
  have hmaps : ∀ i ∈ (Finset.univ : Finset ι), wt i ∈ Finset.Icc (-(N : ℤ)) N := fun i _ => by
    rw [Finset.mem_Icc]; exact abs_le.1 (h3 i)
  have hreg : ∀ n, RegL α β (j + 1) (ψ n) := fun n => RegL.sum _ fun i _ => h2 i
  have hψinv : ∀ (n : ℤ) (γ : GL (Fin 2) K) (g : AdelicGL2 (𝓞 K) K), ψ n (globalPoints (𝓞 K) K γ * g) = ψ n g :=
    fun n => (hreg n).1
  have hψcont : ∀ n : ℤ, Continuous (ψ n) := fun n => ((hreg n).2 [] (Nat.zero_le _)).1
  have hψwt : ∀ n : ℤ, HasCircleWeightAt hw n (ψ n) := fun n =>
    Wt.sum hw _ fun i hi => by
      rw [Finset.mem_filter] at hi
      rw [← hi.2]
      exact h1 i

  have hbd : ∀ i, ∃ B : ℝ, 0 ≤ B ∧ ∀ g, g ∈ slab K α β → ‖p i g‖ ≤ B := fun i => by
    obtain ⟨B, hB⟩ := ((h2 i).2 [] (Nat.zero_le _)).2.2.2
    exact ⟨max B 0, le_max_right _ _, fun g hg => (hB g hg).trans (le_max_left _ _)⟩
  choose B hB0 hB using hbd
  have hψbdd : ∃ B' : ℝ, ∀ (n : ℤ) (g : AdelicGL2 (𝓞 K) K),
      NumberField.TateGlobal.ideleNorm K (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β → ‖ψ n g‖ ≤ B' := by
    refine ⟨∑ i, B i, fun n g hg => ?_⟩
    show ‖(∑ i ∈ Finset.univ.filter (fun i => wt i = n), p i) g‖ ≤ ∑ i, B i
    rw [Finset.sum_apply]
    refine (norm_sum_le _ _).trans ((Finset.sum_le_sum fun i _ => hB i g hg).trans ?_)
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) fun i _ _ => hB0 i
  have K3 := AutomorphicForm.eLpNorm_sum_weight_smul_le_mul_eLpNorm_sum_of_hasCircleWeightAt K α β hα hαβ w hw N ψ
    hψinv hψcont hψwt hψbdd

  have hsumψ : ∑ n ∈ Finset.Icc (-(N : ℤ)) N, ψ n = φ := by
    rw [h4]
    exact Finset.sum_fiberwise_of_maps_to hmaps p
  have hsumE : ∑ n ∈ Finset.Icc (-(N : ℤ)) N, (Complex.I * (n : ℂ)) • ψ n =
      archDerivAtComplex hw .iH φ := by
    have e1 : ∀ n ∈ Finset.Icc (-(N : ℤ)) N, (Complex.I * (n : ℂ)) • ψ n =
        ∑ i ∈ Finset.univ.filter (fun i => wt i = n), archDerivAtComplex hw .iH (p i) := by
      intro n _
      show (Complex.I * (n : ℂ)) • (∑ i ∈ Finset.univ.filter (fun i => wt i = n), p i) = _
      rw [Finset.smul_sum]
      refine Finset.sum_congr rfl fun i hi => ?_
      rw [Finset.mem_filter] at hi
      rw [AutomorphicForm.archDerivAtComplex_iH_eq_smul_of_hasCircleWeightAt_of_isArchSmoothAtComplex K w hw (wt i) (p i)
        (((h2 i).2 [] (Nat.zero_le _)).2.2.1 w hw) (h1 i), hi.2]
    rw [Finset.sum_congr rfl e1, Finset.sum_fiberwise_of_maps_to hmaps, h4]
    exact (D1_sum_of_regL Finset.univ (fun i _ => h2 i) (Cx hw .iH)).symm
  rw [hsumψ, hsumE] at K3
  exact K3

end Main
p2m_reactivate "P2MW.S_AutomorphicForm_exists_forall_eLpNorm_archDerivAtComplex_iH_and_E_sub_Fm_and_iE_add_iFm_foldr_le_of_mem_archCutSubmodule.KtypeCfd"

end KtypeC
p2m_reactivate "P2MW.S_AutomorphicForm_exists_forall_eLpNorm_archDerivAtComplex_iH_and_E_sub_Fm_and_iE_add_iFm_foldr_le_of_mem_archCutSubmodule.KtypeCfd"

namespace KtypeC

variable {K : Type} [Field K] [NumberField K]

section Transport

variable {α β : ℝ} {w : InfinitePlace K} (hw : w.IsComplex)

theorem Inv.zero (j : ℕ) (N : ℤ) (hN : 0 ≤ N) : Inv α β hw j N (0 : AdelicGL2 (𝓞 K) K → ℂ) := by
  refine ⟨Empty, inferInstance, (fun _ => 0 : Empty → AdelicGL2 (𝓞 K) K → ℂ), (fun _ => 0 : Empty → ℤ),
    fun i => i.elim, fun i => i.elim, fun i => i.elim, ?_⟩
  simp

theorem Inv.add {j : ℕ} {N : ℤ} {φ ψ : AdelicGL2 (𝓞 K) K → ℂ} (hφ : Inv α β hw j N φ) (hψ : Inv α β hw j N ψ) :
    Inv α β hw j N (φ + ψ) := by
  obtain ⟨ι, _, p, wt, h1, h2, h3, h4⟩ := hφ
  obtain ⟨ι', _, p', wt', h1', h2', h3', h4'⟩ := hψ
  refine ⟨ι ⊕ ι', inferInstance, fun i => Sum.elim p p' i, fun i => Sum.elim wt wt' i,
    fun i => by cases i <;> simp [h1, h1'], fun i => by cases i <;> simp [h2, h2'],
    fun i => by cases i <;> simp [h3, h3'], ?_⟩
  rw [h4, h4', Fintype.sum_sum_type]
  rfl

theorem Inv.smul {j : ℕ} {N : ℤ} {φ : AdelicGL2 (𝓞 K) K → ℂ} (hφ : Inv α β hw j N φ) (c : ℂ) :
    Inv α β hw j N (c • φ) := by
  obtain ⟨ι, _, p, wt, h1, h2, h3, h4⟩ := hφ
  refine ⟨ι, inferInstance, fun i => c • p i, wt, fun i => Wt.smul hw (h1 i) c, fun i => (h2 i).smul c, h3, ?_⟩
  rw [h4, Finset.smul_sum]

theorem Inv.of_mem_span {j : ℕ} {N : ℤ} (hN : 0 ≤ N) {ι : Type} {f : ι → AdelicGL2 (𝓞 K) K → ℂ}
    (hf : ∀ i, Inv α β hw j N (f i)) {c : AdelicGL2 (𝓞 K) K → ℂ} (hc : c ∈ Submodule.span ℂ (Set.range f)) :
    Inv α β hw j N c := by
  refine Submodule.span_induction (p := fun c _ => Inv α β hw j N c) ?_ (Inv.zero hw j N hN)
    (fun _ _ _ _ h₁ h₂ => h₁.add hw h₂) (fun a _ _ h₁ => h₁.smul hw a) hc
  rintro _ ⟨i, rfl⟩
  exact hf i

theorem Inv.regL {j : ℕ} {N : ℤ} {φ : AdelicGL2 (𝓞 K) K → ℂ} (h : Inv α β hw j N φ) : RegL α β j φ := by
  obtain ⟨ι, _, p, wt, h1, h2, h3, h4⟩ := h
  rw [h4]
  exact RegL.sum _ fun i _ => h2 i

theorem Inv.mono_j {j j' : ℕ} {N : ℤ} {φ : AdelicGL2 (𝓞 K) K → ℂ} (h : Inv α β hw j N φ) (hj : j' ≤ j) :
    Inv α β hw j' N φ := by
  obtain ⟨ι, _, p, wt, h1, h2, h3, h4⟩ := h
  exact ⟨ι, inferInstance, p, wt, h1, fun i => (h2 i).mono hj, h3, h4⟩

theorem ideleNorm_det_incl (k : rowIsometrySubgroup₀ w.Completion) :
    NumberField.TateGlobal.ideleNorm K (Matrix.GeneralLinearGroup.det (rowIsometryInclAt₀ K w k)) = 1 := by
  rw [rowIsometryInclAt₀_apply]
  have hfin : glFin (𝓞 K) K (adelicArchGLInclAt K w (k : GL (Fin 2) w.Completion)) ∈ finiteIntegralGL2 (𝓞 K) K := by
    have : glFin (𝓞 K) K (adelicArchGLInclAt K w (k : GL (Fin 2) w.Completion)) = 1 := glFin_adelicArchGLIncl K _
    rw [this]
    exact Subgroup.one_mem _
  rw [NumberField.TateGlobal.ideleNorm_det_eq_prod_archDetNorm_pow_mult K (adelicArchGLInclAt K w (k : GL (Fin 2) w.Completion)) hfin]
  refine Finset.prod_eq_one fun v _ => ?_
  have hglArch : glArch (𝓞 K) K (adelicArchGLInclAt K w (k : GL (Fin 2) w.Completion)) = archGLIncl K w (k : GL (Fin 2) w.Completion) :=
    glArch_adelicArchGLIncl K _
  have h1 : NumberField.AdelicVolume.archDetNorm v (adelicArchGLInclAt K w (k : GL (Fin 2) w.Completion)) = 1 := by
    unfold NumberField.AdelicVolume.archDetNorm
    rw [hglArch]
    by_cases hv : v = w
    · subst hv
      rw [archComponent_archGLIncl_self]
      obtain ⟨hd, -⟩ := (mem_rowIsometrySubgroup₀_iff _).1 k.2
      rw [hd, norm_one]
    · rw [archComponent_archGLIncl_of_ne K hv, Units.val_one, Matrix.det_one, norm_one]
  rw [h1, one_pow]

theorem mem_slab_mul_incl (k : rowIsometrySubgroup₀ w.Completion) {g : AdelicGL2 (𝓞 K) K} (hg : g ∈ slab K α β) :
    g * rowIsometryInclAt₀ K w k ∈ slab K α β := by
  simp only [Set.mem_setOf_eq] at hg ⊢
  rwa [map_mul, NumberField.TateGlobal.ideleNorm_mul, ideleNorm_det_incl, mul_one]

attribute [local instance] NumberField.AdelicHaar.borelSpace_glBorel

theorem eLpNorm_two_eq_sqrt {𝓕 : Set (AdelicGL2 (𝓞 K) K)} (h𝓕m : MeasurableSet 𝓕)
    (hfin : adelicGLHaar (Fin 2) (𝓞 K) K 𝓕 < ⊤) {f : AdelicGL2 (𝓞 K) K → ℂ} (hf : Continuous f) {B : ℝ}
    (hb : ∀ g, g ∈ 𝓕 → ‖f g‖ ≤ B) :
    eLpNorm f 2 ((adelicGLHaar (Fin 2) (𝓞 K) K).restrict 𝓕) =
      ENNReal.ofReal (Real.sqrt (∫ g in 𝓕, ‖f g‖ ^ 2 ∂(adelicGLHaar (Fin 2) (𝓞 K) K))) := by
  haveI : IsFiniteMeasure ((adelicGLHaar (Fin 2) (𝓞 K) K).restrict 𝓕) := isFiniteMeasure_restrict.2 hfin.ne
  have hmem : MemLp f 2 ((adelicGLHaar (Fin 2) (𝓞 K) K).restrict 𝓕) :=
    MemLp.of_bound hf.aestronglyMeasurable B ((ae_restrict_iff' h𝓕m).2 (ae_of_all _ hb))
  rw [hmem.eLpNorm_eq_integral_rpow_norm two_ne_zero ENNReal.ofNat_ne_top, Real.sqrt_eq_rpow, one_div]
  simp only [ENNReal.toReal_ofNat, Real.rpow_two]

theorem eLpNorm_rightTranslate_incl (hα : 0 < α) (hαβ : α < β) (k : rowIsometrySubgroup₀ w.Completion)
    {u : AdelicGL2 (𝓞 K) K → ℂ} (hu : RegL α β 0 u) :
    eLpNorm (rightTranslate K (rowIsometryInclAt₀ K w k) u) 2
        ((adelicGLHaar (Fin 2) (𝓞 K) K).restrict (AutomorphicForm.canonicalTruncationDomain K α β)) =
      eLpNorm u 2 ((adelicGLHaar (Fin 2) (𝓞 K) K).restrict (AutomorphicForm.canonicalTruncationDomain K α β)) := by
  obtain ⟨𝓕, h𝓕m, h𝓕s, h𝓕, hres, hfin⟩ := KtypeCfd.exists_measurable_fd (K := K) α β hα hαβ
  obtain ⟨hc, -, -, B, hB⟩ := hu.2 [] (Nat.zero_le _)
  have hc0 : Continuous u := hc
  have hB0 : ∀ g, g ∈ slab K α β → ‖u g‖ ≤ B := hB
  have hc' : Continuous (rightTranslate K (rowIsometryInclAt₀ K w k) u) := hc0.comp (continuous_mul_right _)
  rw [← hres, eLpNorm_two_eq_sqrt h𝓕m hfin hc' (fun g hg => hB0 _ (mem_slab_mul_incl k (h𝓕s hg))),
    eLpNorm_two_eq_sqrt h𝓕m hfin hc0 (fun g hg => hB0 _ (h𝓕s hg))]
  congr 2
  have hT := AutomorphicForm.setIntegral_comp_mul_eq_setIntegral_of_isFundamentalDomain_of_ideleNorm_det_eq_one K α β 𝓕 h𝓕s h𝓕
    (rowIsometryInclAt₀ K w k) (ideleNorm_det_incl k) (fun g => ((‖u g‖ ^ 2 : ℝ) : ℂ)) (fun γ g => by simp only [hu.1 γ g])
  rw [integral_complex_ofReal, integral_complex_ofReal] at hT
  exact_mod_cast hT

end Transport
p2m_reactivate "P2MW.S_AutomorphicForm_exists_forall_eLpNorm_archDerivAtComplex_iH_and_E_sub_Fm_and_iE_add_iFm_foldr_le_of_mem_archCutSubmodule.KtypeCfd"

end KtypeC
p2m_reactivate "P2MW.S_AutomorphicForm_exists_forall_eLpNorm_archDerivAtComplex_iH_and_E_sub_Fm_and_iE_add_iFm_foldr_le_of_mem_archCutSubmodule.KtypeCfd"

open KtypeC in
theorem solution
    (K : Type) [Field K] [NumberField K]
    (α β : ℝ) (hα : 0 < α) (hαβ : α < β)
    (tys : ArchTypeFamily K) (m : ℕ) :
    let W : List ((Σ' w : InfinitePlace K, Σ' _ : w.IsReal, ArchDir) ⊕
          (Σ' w : InfinitePlace K, Σ' _ : w.IsComplex, ArchDirComplex)) →
        (AdelicGL2 (𝓞 K) K → ℂ) → (AdelicGL2 (𝓞 K) K → ℂ) :=
      fun l b => l.foldr (fun d φ => Sum.elim (fun d => archDerivAt d.2.1 d.2.2 φ)
        (fun d => archDerivAtComplex d.2.1 d.2.2 φ) d) b
    ∃ n₀ : ℕ,
      ∀ b : AdelicGL2 (𝓞 K) K → ℂ,
        (∀ (γ : GL (Fin 2) K) (g : AdelicGL2 (𝓞 K) K), b (globalPoints (𝓞 K) K γ * g) = b g) →
        b ∈ archCutSubmodule K tys →
        (∀ l, l.length ≤ m + 2 →
          Continuous (W l b) ∧
          (∀ (w : InfinitePlace K) (hw : w.IsReal), IsArchSmoothAt hw (W l b)) ∧
          (∀ (w : InfinitePlace K) (hw : w.IsComplex), IsArchSmoothAtComplex hw (W l b)) ∧
          ∃ B : ℝ, ∀ g : AdelicGL2 (𝓞 K) K,
            NumberField.TateGlobal.ideleNorm K (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β → ‖W l b g‖ ≤ B) →
        ∀ (w : InfinitePlace K) (hw : w.IsComplex) (l : List ((Σ' w : InfinitePlace K, Σ' _ : w.IsReal, ArchDir) ⊕
              (Σ' w : InfinitePlace K, Σ' _ : w.IsComplex, ArchDirComplex))), l.length ≤ m →
          eLpNorm (archDerivAtComplex hw .iH (W l b)) 2
              ((adelicGLHaar (Fin 2) (𝓞 K) K).restrict (AutomorphicForm.canonicalTruncationDomain K α β)) ≤
            ((n₀ + 2 * l.length : ℕ) : ENNReal) *
              eLpNorm (W l b) 2 ((adelicGLHaar (Fin 2) (𝓞 K) K).restrict (AutomorphicForm.canonicalTruncationDomain K α β)) ∧
          eLpNorm (archDerivAtComplex hw .E (W l b) - archDerivAtComplex hw .Fm (W l b)) 2
              ((adelicGLHaar (Fin 2) (𝓞 K) K).restrict (AutomorphicForm.canonicalTruncationDomain K α β)) ≤
            ((n₀ + 2 * l.length : ℕ) : ENNReal) *
              eLpNorm (W l b) 2 ((adelicGLHaar (Fin 2) (𝓞 K) K).restrict (AutomorphicForm.canonicalTruncationDomain K α β)) ∧
          eLpNorm (archDerivAtComplex hw .iE (W l b) + archDerivAtComplex hw .iFm (W l b)) 2
              ((adelicGLHaar (Fin 2) (𝓞 K) K).restrict (AutomorphicForm.canonicalTruncationDomain K α β)) ≤
            ((n₀ + 2 * l.length : ℕ) : ENNReal) *
              eLpNorm (W l b) 2 ((adelicGLHaar (Fin 2) (𝓞 K) K).restrict (AutomorphicForm.canonicalTruncationDomain K α β)) := by
  intro W
  obtain ⟨n₀, HK1⟩ := AutomorphicForm.exists_forall_eq_sum_hasCircleWeightAt_mem_span_rightTranslate_of_mem_archCutSubmodule_of_isArchSmoothAtComplex K tys
  refine ⟨n₀, ?_⟩
  intro b hinv hT hreg w hw l hl
  have hreg' : RegL α β (m + 2) b := ⟨hinv, hreg⟩

  have hRk : ∀ k : rowIsometrySubgroup₀ w.Completion, RegL α β (m + 2) (rightTranslate K (rowIsometryInclAt₀ K w k) b) :=
    fun k => AutomorphicForm.forall_continuous_isArchSmoothAt_bounded_foldr_archDeriv_rightTranslate_rowIsometryInclAt_of_isComplex K α β (m + 2) b hinv hreg w hw k
  have hcutk : ∀ k : rowIsometrySubgroup₀ w.Completion, rightTranslate K (rowIsometryInclAt₀ K w k) b ∈ archCutSubmodule K tys :=
    fun k => comp_mul_rowIsometryInclAt₀_mem_archCutSubmodule K hT w k
  have hInvk : ∀ k : rowIsometrySubgroup₀ w.Completion,
      Inv α β hw (m + 2) (n₀ : ℤ) (rightTranslate K (rowIsometryInclAt₀ K w k) b) := by
    intro k
    obtain ⟨c, hcw, hcs, hcz, hcsum⟩ := HK1 (rightTranslate K (rowIsometryInclAt₀ K w k) b)
      ((hRk k).2 [] (Nat.zero_le _)).1 (hcutk k) w hw (((hRk k).2 [] (Nat.zero_le _)).2.2.1 w hw)
    have hRk' : ∀ k' : rowIsometrySubgroup₀ w.Completion,
        RegL α β (m + 2) (rightTranslate K (rowIsometryInclAt₀ K w k') (rightTranslate K (rowIsometryInclAt₀ K w k) b)) := by
      intro k'
      have e : rightTranslate K (rowIsometryInclAt₀ K w k') (rightTranslate K (rowIsometryInclAt₀ K w k) b) =
          rightTranslate K (rowIsometryInclAt₀ K w (k' * k)) b := by
        funext x; simp only [rightTranslate, map_mul, mul_assoc]
      rw [e]; exact hRk (k' * k)
    have hcreg : ∀ n, RegL α β (m + 2) (c n) := fun n => RegL.of_mem_span hRk' (hcs n)
    refine ⟨↥(Finset.Icc (-(n₀ : ℤ)) n₀), inferInstance, fun i => c i, fun i => i, fun i => hcw i, fun i => hcreg i,
      fun i => abs_le.2 (Finset.mem_Icc.1 i.2), ?_⟩
    rw [Finset.sum_coe_sort]
    exact hcsum
  have hb : Inv α β hw (m + 2) (n₀ : ℤ) b := by
    have e : rightTranslate K (rowIsometryInclAt₀ K w 1) b = b := by
      funext x; simp only [rightTranslate, map_one, mul_one]
    rw [← e]; exact hInvk 1
  have hφ := inv_words hw hb l (by omega)
  have e : m + 2 - l.length = (m + 1 - l.length) + 1 := by omega

  have B1 : eLpNorm (archDerivAtComplex hw .iH (Wd l b)) 2 ((adelicGLHaar (Fin 2) (𝓞 K) K).restrict (AutomorphicForm.canonicalTruncationDomain K α β)) ≤
      ((n₀ + 2 * l.length : ℕ) : ENNReal) * eLpNorm (Wd l b) 2 ((adelicGLHaar (Fin 2) (𝓞 K) K).restrict (AutomorphicForm.canonicalTruncationDomain K α β)) := by
    have hφ' := hφ
    rw [e] at hφ'
    exact bound_of_inv hw hα hαβ (N := n₀ + 2 * l.length) (by exact_mod_cast hφ')

  obtain ⟨k₁, k₂, hK5⟩ := AutomorphicForm.exists_archDerivAtComplex_Fm_sub_E_and_iE_add_iFm_eq_rightTranslate_iH_rightTranslate K w hw
  have hsm : IsArchSmoothAtComplex hw (Wd l b) := (hreg l (by omega)).2.2.1 w hw
  obtain ⟨e5a, e5b⟩ := hK5 (Wd l b) hsm
  have conj_bound : ∀ k : rowIsometrySubgroup₀ w.Completion,
      eLpNorm (rightTranslate K (rowIsometryInclAt₀ K w k)
        (archDerivAtComplex hw .iH (rightTranslate K (rowIsometryInclAt₀ K w k⁻¹) (Wd l b)))) 2 ((adelicGLHaar (Fin 2) (𝓞 K) K).restrict (AutomorphicForm.canonicalTruncationDomain K α β)) ≤
      ((n₀ + 2 * l.length : ℕ) : ENNReal) * eLpNorm (Wd l b) 2 ((adelicGLHaar (Fin 2) (𝓞 K) K).restrict (AutomorphicForm.canonicalTruncationDomain K α β)) := by
    intro k
    have hψ' : Inv α β hw (m + 2 - l.length) ((n₀ : ℤ) + 2 * (l.length : ℤ))
        (rightTranslate K (rowIsometryInclAt₀ K w k⁻¹) (Wd l b)) := by
      have hmem := AutomorphicForm.rightTranslate_foldr_archDeriv_mem_span_foldr_archDeriv_rightTranslate_of_isComplex K α β (m + 2) b hinv hreg w hw k⁻¹ l (by omega)
      refine Inv.of_mem_span hw (by positivity) (fun l' => ?_) hmem
      have h' := inv_words hw (hInvk k⁻¹) l'.1 (by rw [l'.2]; omega)
      rw [l'.2] at h'
      exact h'
    rw [e] at hψ'
    have hb' := bound_of_inv hw hα hαβ (N := n₀ + 2 * l.length) (by exact_mod_cast hψ')
    have hu : RegL α β 0 (archDerivAtComplex hw .iH (rightTranslate K (rowIsometryInclAt₀ K w k⁻¹) (Wd l b))) :=
      ((hψ'.regL hw).letter (Cx hw .iH)).mono (Nat.zero_le _)
    rw [eLpNorm_rightTranslate_incl hα hαβ k hu]
    refine hb'.trans ?_
    have hφ0 : RegL α β 0 (Wd l b) := (hφ.regL hw).mono (Nat.zero_le _)
    rw [eLpNorm_rightTranslate_incl hα hαβ k⁻¹ hφ0]
  refine ⟨B1, ?_, ?_⟩
  · have eneg : archDerivAtComplex hw .E (Wd l b) - archDerivAtComplex hw .Fm (Wd l b) =
        -(archDerivAtComplex hw .Fm (Wd l b) - archDerivAtComplex hw .E (Wd l b)) := (neg_sub _ _).symm
    show eLpNorm (archDerivAtComplex hw .E (Wd l b) - archDerivAtComplex hw .Fm (Wd l b)) 2 ((adelicGLHaar (Fin 2) (𝓞 K) K).restrict (AutomorphicForm.canonicalTruncationDomain K α β)) ≤
      ((n₀ + 2 * l.length : ℕ) : ENNReal) * eLpNorm (Wd l b) 2 ((adelicGLHaar (Fin 2) (𝓞 K) K).restrict (AutomorphicForm.canonicalTruncationDomain K α β))
    rw [eneg, eLpNorm_neg, e5a]
    exact conj_bound k₁
  · show eLpNorm (archDerivAtComplex hw .iE (Wd l b) + archDerivAtComplex hw .iFm (Wd l b)) 2 ((adelicGLHaar (Fin 2) (𝓞 K) K).restrict (AutomorphicForm.canonicalTruncationDomain K α β)) ≤
      ((n₀ + 2 * l.length : ℕ) : ENNReal) * eLpNorm (Wd l b) 2 ((adelicGLHaar (Fin 2) (𝓞 K) K).restrict (AutomorphicForm.canonicalTruncationDomain K α β))
    rw [e5b]
    exact conj_bound k₂

end
p2m_reactivate "P2MW.S_AutomorphicForm_exists_forall_eLpNorm_archDerivAtComplex_iH_and_E_sub_Fm_and_iE_add_iFm_foldr_le_of_mem_archCutSubmodule.KtypeCfd"

end S_AutomorphicForm_exists_forall_eLpNorm_archDerivAtComplex_iH_and_E_sub_Fm_and_iE_add_iFm_foldr_le_of_mem_archCutSubmodule
end P2MW
export P2MW.S_AutomorphicForm_exists_forall_eLpNorm_archDerivAtComplex_iH_and_E_sub_Fm_and_iE_add_iFm_foldr_le_of_mem_archCutSubmodule (solution)
