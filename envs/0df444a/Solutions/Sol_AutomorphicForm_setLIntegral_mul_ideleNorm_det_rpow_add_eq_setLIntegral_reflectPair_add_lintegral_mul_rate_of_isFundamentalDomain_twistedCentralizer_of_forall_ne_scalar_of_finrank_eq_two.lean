-- Prove2me | solution 1 for AutomorphicForm.setLIntegral_mul_ideleNorm_det_rpow_add_eq_setLIntegral_reflectPair_add_lintegral_mul_rate_of_isFundamentalDomain_twistedCentralizer_of_forall_ne_scalar_of_finrank_eq_two
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.340288+00:00
-- url     : https://prove2.me/submissions/3fee0aae-b959-5e39-9253-62fc99dab56b

import Definitions.Def_AutomorphicForm_BaseChangePlaces
import Definitions.Def_AutomorphicForm_AdelicLsXi
import Definitions.Def_AutomorphicForm_GodementSection
import Definitions.Def_AutomorphicForm_WhittakerCoefficient
import Definitions.Def_NumberField_AdelicBox
import Definitions.Def_NumberField_AdelicHaar
import Definitions.Def_NumberField_TateGlobalZeta
import Theorems.Thm_AutomorphicForm_tsum_sigmaCentralizer_apply_mulVec_add_eq_inv_ideleNorm_det_mul_tsum_reflectPair_of_forall_ne_scalar_of_finrank_eq_two
import Theorems.Thm_AutomorphicForm_map_genuineRingEquiv_sigmaGL_and_toTensorGL_and_includeLeft
import Theorems.Thm_MeasureTheory_Measure_map_eq_self_of_involutive_of_isHaarMeasure
import Theorems.Thm_NumberField_TateGlobal_continuous_ideleNorm
import Theorems.Thm_NumberField_AdeleRing_distribHaarChar_algebraMap
import Theorems.Thm_NumberField_AdeleRing_secondCountableTopology_generalLinearGroup_finTwo
import Theorems.Thm_NumberField_AdelicFourier_continuous_integrable_comp_vecMul_mem_and_bottomRowVec_mem_schwartzBruhat_of_mem_schwartzBruhat2
import Theorems.Thm_NumberField_AdelicFourier_fourierTransform2_mem_schwartzBruhat2_and_reflectPair_mem_schwartzBruhat2
import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_setLIntegral_mul_ideleNorm_det_rpow_add_eq_setLIntegral_reflectPair_add_lintegral_mul_rate_of_isFundamentalDomain_twistedCentralizer_of_forall_ne_scalar_of_finrank_eq_two
p2m_attr_erase "instance" "instCountableOfNumberField_definitions RestrictedProduct.SecondCountableTopology_of_principal instCountableElemSetSetsCofinite_definitions instMeasurableSpaceRestrictedProduct_definitions instBorelSpaceRestrictedProduct_definitions MeasureTheory.instMeasurableNegSubtypeMemAddSubgroup_definitions MeasureTheory.instMeasurableMulSubtypeMemSubgroup_definitions MeasureTheory.instMeasurableMul₂SubtypeMemSubgroup_definitions MeasureTheory.instMeasurableMul₂SubtypeMemAddSubgroup_definitions MeasureTheory.instMeasurableAddSubtypeMemAddSubgroup_definitions MeasureTheory.instMeasurableInvSubtypeMemSubgroup_definitions instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions"
p2m_attr_erase "simp" "ContinuousAddEquiv.restrictedProductPi_apply RestrictedProduct.flatten_homeomorph_apply RestrictedProduct.flatten_homeomorph'_symm_apply ContinuousMulEquiv.restrictedProductPi_symm_apply RestrictedProduct.flatten_homeomorph'_apply RestrictedProduct.flatten_homeomorph_symm_apply ContinuousMulEquiv.restrictedProductPi_apply ContinuousAddEquiv.restrictedProductPi_symm_apply ContinuousAddEquiv.preimage_mulLeft_smul"

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

open MeasureTheory Set NumberField
open scoped ENNReal Pointwise

noncomputable section

namespace AutomorphicForm
p2m_export "AutomorphicForm" "baseChangeGLEquiv isTopologicalRing_tensor t2Space_tensor locallyCompactSpace_tensor isTopologicalGroup_tensorGL t2Space_tensorGL centralizerBorel sigmaTensor sigmaGL twistedCentralizer twistedCentralizerBorel globalPoints sigmaCentralizer mem_sigmaCentralizer_iff IsGlobalAddChar tsum_sigmaCentralizer_apply_mulVec_add_eq_inv_ideleNorm_det_mul_tsum_reflectPair_of_forall_ne_scalar_of_finrank_eq_two map_genuineRingEquiv_sigmaGL_and_toTensorGL_and_includeLeft"
namespace QuatZeta
p2m_open "AutomorphicForm"

theorem measurable_tsum_ennreal {α ι : Type*} [MeasurableSpace α] [Countable ι] {f : ι → α → ℝ≥0∞}
    (h : ∀ i, Measurable (f i)) : Measurable fun x => ∑' i, f i x := by
  simp_rw [ENNReal.tsum_eq_iSup_sum]
  exact Measurable.iSup fun s => s.measurable_fun_sum fun i _ => h i

section LogSlab

variable {X : Type*} [MeasurableSpace X]

theorem setLIntegral_comp_eq_mul_lintegral_Ioi (ν : Measure X) (Ω : Set X) (hΩ : MeasurableSet Ω)
    (N : X → ℝ) (hN : Measurable N) (hNpos : ∀ x ∈ Ω, 0 < N x)
    (C : ℝ≥0∞) (hC : C ≠ ⊤)
    (h : ∀ a b : ℝ, 0 < a → a ≤ b →
      ν (Ω ∩ {x | N x ∈ Set.Icc a b}) = C * ENNReal.ofReal (Real.log (b / a)))
    (H : ℝ → ℝ≥0∞) (hH : Measurable H) :
    ∫⁻ x in Ω, H (N x) ∂ν = C * ∫⁻ r in Set.Ioi (0 : ℝ), H r * ENNReal.ofReal r⁻¹ := by

  have hmeas : Measurable fun x => Real.log (N x) := Real.measurable_log.comp hN
  set m : Measure ℝ := Measure.map (fun x => Real.log (N x)) (ν.restrict Ω) with hm
  have hm_Icc : ∀ s t : ℝ, s ≤ t → m (Icc s t) = C * ENNReal.ofReal (t - s) := by
    intro s t hst
    rw [hm, Measure.map_apply hmeas measurableSet_Icc,
      Measure.restrict_apply (hmeas measurableSet_Icc)]
    have hpre : (fun x => Real.log (N x)) ⁻¹' Icc s t ∩ Ω =
        Ω ∩ {x | N x ∈ Icc (Real.exp s) (Real.exp t)} := by
      ext x
      simp only [mem_inter_iff, mem_preimage, mem_Icc, mem_setOf_eq]
      constructor
      · rintro ⟨⟨h1, h2⟩, hx⟩
        have hp := hNpos x hx
        exact ⟨hx, (Real.le_log_iff_exp_le hp).1 h1, (Real.log_le_iff_le_exp hp).1 h2⟩
      · rintro ⟨hx, h1, h2⟩
        have hp := hNpos x hx
        exact ⟨⟨(Real.le_log_iff_exp_le hp).2 h1, (Real.log_le_iff_le_exp hp).2 h2⟩, hx⟩
    rw [hpre, h (Real.exp s) (Real.exp t) (Real.exp_pos s) (Real.exp_le_exp.2 hst),
      Real.log_div (Real.exp_pos t).ne' (Real.exp_pos s).ne', Real.log_exp, Real.log_exp]
  have hm_pt : ∀ s : ℝ, m {s} = 0 := by
    intro s
    rw [← Icc_self, hm_Icc s s le_rfl, sub_self, ENNReal.ofReal_zero, mul_zero]
  have hm_Ioc : ∀ s t : ℝ, s < t → m (Ioc s t) = C * ENNReal.ofReal (t - s) := by
    intro s t hst
    rw [← Icc_diff_left, measure_diff (singleton_subset_iff.2 (left_mem_Icc.2 hst.le))
      (measurableSet_singleton s).nullMeasurableSet (by rw [hm_pt]; exact ENNReal.zero_ne_top),
      hm_pt, tsub_zero, hm_Icc s t hst.le]
  have hm_eq : m = C • (volume : Measure ℝ) := by
    refine Measure.ext_of_Ioc' m (C • volume) (fun a b hab => ?_) (fun a b hab => ?_)
    · rw [hm_Ioc a b hab]; exact ENNReal.mul_ne_top hC ENNReal.ofReal_ne_top
    · rw [hm_Ioc a b hab, Measure.smul_apply, Real.volume_Ioc, smul_eq_mul]

  have hL : ∫⁻ x in Ω, H (N x) ∂ν = ∫⁻ y, H (Real.exp y) ∂m := by
    rw [hm, lintegral_map (show Measurable fun y => H (Real.exp y) from hH.comp Real.measurable_exp)
      hmeas]
    refine setLIntegral_congr_fun hΩ fun x hx => ?_
    simp only [Real.exp_log (hNpos x hx)]
  rw [hL, hm_eq, lintegral_smul_measure, smul_eq_mul]
  congr 1

  have hcv := lintegral_image_eq_lintegral_abs_deriv_mul (f := Real.exp) (f' := Real.exp)
    (s := Set.univ) MeasurableSet.univ (fun x _ => (Real.hasDerivAt_exp x).hasDerivWithinAt)
    Real.exp_injective.injOn (fun r => H r * ENNReal.ofReal r⁻¹)
  rw [image_univ, Real.range_exp, Measure.restrict_univ] at hcv
  rw [hcv]
  refine lintegral_congr fun y => ?_
  rw [abs_of_pos (Real.exp_pos y), mul_left_comm, ← ENNReal.ofReal_mul (Real.exp_pos y).le,
    mul_inv_cancel₀ (Real.exp_pos y).ne', ENNReal.ofReal_one, mul_one]

def wLow (s : ℝ) (r : ℝ) : ℝ≥0∞ := (Set.Iic (1 : ℝ)).indicator (fun r => ENNReal.ofReal (r ^ s)) r

theorem measurable_wLow (s : ℝ) : Measurable (wLow s) :=
  (ENNReal.measurable_ofReal.comp (Measurable.pow_const measurable_id s)).indicator measurableSet_Iic

theorem wLow_of_le {s r : ℝ} (hr : r ≤ 1) : wLow s r = ENNReal.ofReal (r ^ s) := by
  unfold wLow; rw [Set.indicator_of_mem (show r ∈ Set.Iic (1 : ℝ) from hr)]

theorem wLow_of_gt {s r : ℝ} (hr : 1 < r) : wLow s r = 0 := by
  unfold wLow; rw [Set.indicator_of_notMem (show r ∉ Set.Iic (1 : ℝ) from not_le.2 hr)]

theorem lintegral_Ioc_rpow {e : ℝ} (he : -1 < e) :
    ∫⁻ r in Set.Ioc (0 : ℝ) 1, ENNReal.ofReal (r ^ e) = ENNReal.ofReal (1 / (e + 1)) := by
  have hint : IntervalIntegrable (fun r : ℝ => r ^ e) volume 0 1 :=
    intervalIntegral.intervalIntegrable_rpow' he
  have hI : IntegrableOn (fun r : ℝ => r ^ e) (Set.Ioc 0 1) volume :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one).1 hint
  rw [← ofReal_integral_eq_lintegral_ofReal hI]
  · congr 1
    rw [← intervalIntegral.integral_of_le zero_le_one, integral_rpow (Or.inl he), Real.one_rpow,
      Real.zero_rpow (by linarith), sub_zero]
  · refine (ae_restrict_iff' measurableSet_Ioc).2 (Filter.Eventually.of_forall fun r hr => ?_)
    exact Real.rpow_nonneg hr.1.le e

theorem lintegral_wLow_mul_inv {s : ℝ} (hs : 0 < s) :
    ∫⁻ r in Set.Ioi (0 : ℝ), wLow s r * ENNReal.ofReal r⁻¹ = ENNReal.ofReal (1 / s) := by
  have hsplit : ∫⁻ r in Set.Ioi (0 : ℝ), wLow s r * ENNReal.ofReal r⁻¹ =
      ∫⁻ r in Set.Ioc (0 : ℝ) 1, ENNReal.ofReal (r ^ (s - 1)) := by
    rw [← Set.Ioc_union_Ioi_eq_Ioi zero_le_one, lintegral_union measurableSet_Ioi
      (Set.Ioc_disjoint_Ioi_same)]
    have h2 : ∫⁻ r in Set.Ioi (1 : ℝ), wLow s r * ENNReal.ofReal r⁻¹ = 0 := by
      refine (setLIntegral_congr_fun measurableSet_Ioi fun r hr => ?_).trans (lintegral_zero)
      rw [wLow_of_gt hr, zero_mul]
    rw [h2, add_zero]
    refine setLIntegral_congr_fun measurableSet_Ioc fun r hr => ?_
    rw [wLow_of_le hr.2, ← ENNReal.ofReal_mul (Real.rpow_nonneg hr.1.le s), Real.rpow_sub_one hr.1.ne',
      div_eq_mul_inv]
  rw [hsplit, lintegral_Ioc_rpow (by linarith), sub_add_cancel]

theorem lintegral_wLow_mul_inv_mul_inv {s : ℝ} (hs : 1 < s) :
    ∫⁻ r in Set.Ioi (0 : ℝ), (wLow s r * ENNReal.ofReal r⁻¹) * ENNReal.ofReal r⁻¹ =
      ENNReal.ofReal (1 / (s - 1)) := by
  have hsplit : ∫⁻ r in Set.Ioi (0 : ℝ), (wLow s r * ENNReal.ofReal r⁻¹) * ENNReal.ofReal r⁻¹ =
      ∫⁻ r in Set.Ioc (0 : ℝ) 1, ENNReal.ofReal (r ^ (s - 2)) := by
    rw [← Set.Ioc_union_Ioi_eq_Ioi zero_le_one, lintegral_union measurableSet_Ioi
      (Set.Ioc_disjoint_Ioi_same)]
    have h2 : ∫⁻ r in Set.Ioi (1 : ℝ), (wLow s r * ENNReal.ofReal r⁻¹) * ENNReal.ofReal r⁻¹ = 0 := by
      refine (setLIntegral_congr_fun measurableSet_Ioi fun r hr => ?_).trans (lintegral_zero)
      rw [wLow_of_gt hr, zero_mul, zero_mul]
    rw [h2, add_zero]
    refine setLIntegral_congr_fun measurableSet_Ioc fun r hr => ?_
    have hrr : r ^ s * r⁻¹ * r⁻¹ = r ^ (s - 2) := by
      rw [Real.rpow_sub hr.1, Real.rpow_two]; field_simp
    rw [wLow_of_le hr.2, ← ENNReal.ofReal_mul (Real.rpow_nonneg hr.1.le s),
      ← ENNReal.ofReal_mul (mul_nonneg (Real.rpow_nonneg hr.1.le s) (inv_nonneg.2 hr.1.le)), hrr]
  rw [hsplit, lintegral_Ioc_rpow (by linarith)]
  congr 1; ring

end LogSlab

section Unfold

variable {G : Type*} [Group G] [MeasurableSpace G] [MeasurableMul G]

theorem lintegral_eq_setLIntegral_tsum_mul_right
    (τ : Measure G) [SFinite τ] [τ.IsMulRightInvariant]
    (Γ : Subgroup G) [Countable Γ] (D : Set G) (hD : IsFundamentalDomain Γ.op D τ)
    (F : G → ℝ≥0∞) (hF : Measurable F) :
    ∫⁻ x, F x ∂τ = ∫⁻ x in D, ∑' γ : Γ, F (x * γ) ∂τ := by
  haveI : Countable Γ.op := Subgroup.instCountableSubtypeMulOppositeMemOp Γ
  rw [hD.lintegral_eq_tsum F]
  have hterm : ∀ g : Γ.op, ∫⁻ x in g • D, F x ∂τ =
      ∫⁻ x in D, F (x * MulOpposite.unop (g : Gᵐᵒᵖ)) ∂τ := by
    intro g
    set c : G := MulOpposite.unop (g : Gᵐᵒᵖ) with hc
    have hgD : (g • D : Set G) = (fun x => x * c) '' D := by
      ext y
      simp only [Set.mem_image]
      constructor
      · rintro ⟨d, hd, rfl⟩
        exact ⟨d, hd, by simp only [Subgroup.smul_def, MulOpposite.smul_eq_mul_unop, hc]⟩
      · rintro ⟨d, hd, rfl⟩
        exact ⟨d, hd, by simp only [Subgroup.smul_def, MulOpposite.smul_eq_mul_unop, hc]⟩
    have hpre : (fun x => x * c) ⁻¹' (g • D) = D := by
      rw [hgD, (mul_left_injective c).preimage_image]
    have h1 := (measurePreserving_mul_right τ c).setLIntegral_comp_preimage_emb
      (MeasurableEquiv.mulRight c).measurableEmbedding F (g • D)
    rw [← h1, hpre]
  simp_rw [hterm]
  rw [← lintegral_tsum fun g : Γ.op => (show Measurable fun x : G =>
    F (x * MulOpposite.unop (g : Gᵐᵒᵖ)) from hF.comp (measurable_mul_const _)).aemeasurable]
  refine lintegral_congr fun x => ?_
  exact (Equiv.tsum_eq (Subgroup.equivOp Γ) fun g : Γ.op => F (x * MulOpposite.unop (g : Gᵐᵒᵖ))).symm

theorem setLIntegral_mul_tsum_eq_lintegral_mul
    (τ : Measure G) [SFinite τ] [τ.IsMulRightInvariant]
    (Γ : Subgroup G) [Countable Γ] (D : Set G) (hD : IsFundamentalDomain Γ.op D τ)
    (w : G → ℝ≥0∞) (hw : Measurable w) (hwΓ : ∀ (x : G) (γ : Γ), w (x * γ) = w x)
    (f : G → ℝ≥0∞) (hf : Measurable f) :
    ∫⁻ x in D, w x * ∑' γ : Γ, f (x * γ) ∂τ = ∫⁻ x, w x * f x ∂τ := by
  rw [lintegral_eq_setLIntegral_tsum_mul_right τ Γ D hD (fun x => w x * f x) (hw.mul hf)]
  refine lintegral_congr fun x => ?_
  rw [← ENNReal.tsum_mul_left]
  exact tsum_congr fun γ => by rw [hwΓ]

end Unfold

section Main

variable {G : Type*} [Group G] [MeasurableSpace G] [MeasurableMul G]

theorem zeta_decomposition
    (τ : Measure G) [SFinite τ] [τ.IsMulRightInvariant]
    (Γ : Subgroup G) [Countable Γ]
    (D : Set G) (hDm : MeasurableSet D) (hD : IsFundamentalDomain Γ.op D τ)
    (ι : G → G) (hιm : Measurable ι) (hιι : ∀ x, ι (ι x) = x) (hιτ : Measure.map ι τ = τ)
    (hDι : IsFundamentalDomain Γ.op (ι ⁻¹' D) τ)
    (N : G → ℝ) (hN : Measurable N) (hNpos : ∀ x, 0 < N x) (hNΓ : ∀ (x : G) (γ : Γ), N (x * γ) = N x)
    (hNι : ∀ x, N (ι x) = (N x)⁻¹)
    (R : ℝ≥0∞) (hR : R ≠ ⊤)
    (hrate : ∀ a b : ℝ, 0 < a → a ≤ b →
      τ (D ∩ {x | N x ∈ Set.Icc a b}) = R * ENNReal.ofReal (Real.log (b / a)))
    (a p m : G → ℝ≥0∞) (ha : Measurable a) (hp : Measurable p) (hm : Measurable m)
    (φ0 φ0' : ℝ≥0∞)
    (hθ : ∀ x, (∑' γ : Γ, a (x * γ)) + φ0 + ENNReal.ofReal (N x)⁻¹ * ∑' γ : Γ, m (ι x * γ) =
      ENNReal.ofReal (N x)⁻¹ * (∑' γ : Γ, p (ι x * γ)) + ENNReal.ofReal (N x)⁻¹ * φ0')
    (s : ℝ) (hs : 1 < s) :
    ∫⁻ x in {x | N x ≤ 1}, a x * ENNReal.ofReal (N x ^ s) ∂τ + φ0 * R * ENNReal.ofReal (1 / s) +
        ∫⁻ x in {x | 1 ≤ N x}, m x * ENNReal.ofReal (N x ^ (1 - s)) ∂τ =
      ∫⁻ x in {x | 1 ≤ N x}, p x * ENNReal.ofReal (N x ^ (1 - s)) ∂τ +
        φ0' * R * ENNReal.ofReal (1 / (s - 1)) := by

  set w : G → ℝ≥0∞ := fun x => wLow s (N x) with hw_def
  set w' : G → ℝ≥0∞ := fun x => ({x | 1 ≤ N x} : Set G).indicator (fun x => ENNReal.ofReal (N x ^ (1 - s))) x
    with hw'_def
  have hw : Measurable w := (measurable_wLow s).comp hN
  have hS1 : MeasurableSet ({x | 1 ≤ N x} : Set G) := hN measurableSet_Ici
  have hS0 : MeasurableSet ({x | N x ≤ 1} : Set G) := hN measurableSet_Iic
  have hw' : Measurable w' := (ENNReal.measurable_ofReal.comp (hN.pow_const _)).indicator hS1
  have hwΓ : ∀ (x : G) (γ : Γ), w (x * γ) = w x := fun x γ => by simp only [hw_def, hNΓ]
  have hw'Γ : ∀ (x : G) (γ : Γ), w' (x * γ) = w' x := fun x γ => by
    simp only [hw'_def, Set.indicator, Set.mem_setOf_eq, hNΓ]
  have hn : Measurable fun x => ENNReal.ofReal (N x)⁻¹ := ENNReal.measurable_ofReal.comp hN.inv

  have hww' : ∀ x, w x * ENNReal.ofReal (N x)⁻¹ = w' (ι x) := by
    intro x
    have hNx := hNpos x
    by_cases hx : N x ≤ 1
    · have h1 : (1 : ℝ) ≤ N (ι x) := by rw [hNι]; exact (one_le_inv₀ hNx).2 hx
      rw [hw_def]; dsimp only
      rw [wLow_of_le hx, hw'_def]; dsimp only
      rw [Set.indicator_of_mem (show ι x ∈ {x | 1 ≤ N x} from h1), hNι,
        Real.inv_rpow hNx.le, ← Real.rpow_neg hNx.le, neg_sub, ← ENNReal.ofReal_mul (Real.rpow_nonneg hNx.le _),
        Real.rpow_sub_one hNx.ne', div_eq_mul_inv]
    · have hx' : 1 < N x := not_le.1 hx
      have h1 : ¬ (1 : ℝ) ≤ N (ι x) := by
        rw [hNι, not_le]; exact inv_lt_one_of_one_lt₀ hx'
      rw [hw_def]; dsimp only
      rw [wLow_of_gt hx', zero_mul, hw'_def]; dsimp only
      rw [Set.indicator_of_notMem (show ι x ∉ {x | 1 ≤ N x} from h1)]

  have mA : Measurable fun x => ∑' γ : Γ, a (x * γ) :=
    measurable_tsum_ennreal fun γ => ha.comp (measurable_mul_const _)
  have mPι : Measurable fun x => ∑' γ : Γ, p (ι x * γ) :=
    measurable_tsum_ennreal fun γ => (hp.comp (measurable_mul_const _)).comp hιm
  have mMι : Measurable fun x => ∑' γ : Γ, m (ι x * γ) :=
    measurable_tsum_ennreal fun γ => (hm.comp (measurable_mul_const _)).comp hιm

  have hT1 : ∫⁻ x in D, w x * ∑' γ : Γ, a (x * γ) ∂τ =
      ∫⁻ x in {x | N x ≤ 1}, a x * ENNReal.ofReal (N x ^ s) ∂τ := by
    rw [setLIntegral_mul_tsum_eq_lintegral_mul τ Γ D hD w hw hwΓ a ha, ← lintegral_indicator hS0]
    refine lintegral_congr fun x => ?_
    by_cases hx : N x ≤ 1
    · rw [Set.indicator_of_mem (show x ∈ {x | N x ≤ 1} from hx), hw_def]; dsimp only
      rw [wLow_of_le hx, mul_comm]
    · rw [Set.indicator_of_notMem (show x ∉ {x | N x ≤ 1} from hx), hw_def]; dsimp only
      rw [wLow_of_gt (not_le.1 hx), zero_mul]

  have hT2 : ∫⁻ x in D, w x * φ0 ∂τ = φ0 * R * ENNReal.ofReal (1 / s) := by
    rw [lintegral_mul_const _ hw, setLIntegral_comp_eq_mul_lintegral_Ioi τ D hDm N hN (fun x _ => hNpos x)
      R hR hrate (wLow s) (measurable_wLow s), lintegral_wLow_mul_inv (zero_lt_one.trans hs)]
    ring

  have hT34 : ∀ (f : G → ℝ≥0∞), Measurable f →
      ∫⁻ x in D, w x * (ENNReal.ofReal (N x)⁻¹ * ∑' γ : Γ, f (ι x * γ)) ∂τ =
        ∫⁻ x in {x | 1 ≤ N x}, f x * ENNReal.ofReal (N x ^ (1 - s)) ∂τ := by
    intro f hf
    have mg : Measurable fun u => w' u * ∑' γ : Γ, f (u * γ) :=
      hw'.mul (measurable_tsum_ennreal fun γ => hf.comp (measurable_mul_const _))
    have hDιm : MeasurableSet (ι ⁻¹' D) := hDm.preimage hιm
    calc ∫⁻ x in D, w x * (ENNReal.ofReal (N x)⁻¹ * ∑' γ : Γ, f (ι x * γ)) ∂τ
        = ∫⁻ x in D, (fun u => w' u * ∑' γ : Γ, f (u * γ)) (ι x) ∂τ := by
          refine lintegral_congr fun x => ?_
          rw [← mul_assoc, hww']
      _ = ∫⁻ x, (ι ⁻¹' D).indicator (fun u => w' u * ∑' γ : Γ, f (u * γ)) (ι x) ∂τ := by
          rw [← lintegral_indicator hDm]
          refine lintegral_congr fun x => ?_
          have : x ∈ D ↔ ι x ∈ ι ⁻¹' D := by rw [Set.mem_preimage, hιι]
          by_cases hx : x ∈ D
          · rw [Set.indicator_of_mem hx, Set.indicator_of_mem (this.1 hx)]
          · rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem (fun h => hx (this.2 h))]
      _ = ∫⁻ u, (ι ⁻¹' D).indicator (fun u => w' u * ∑' γ : Γ, f (u * γ)) u ∂(Measure.map ι τ) :=
          (lintegral_map (mg.indicator hDιm) hιm).symm
      _ = ∫⁻ u in ι ⁻¹' D, w' u * ∑' γ : Γ, f (u * γ) ∂τ := by rw [hιτ, lintegral_indicator hDιm]
      _ = ∫⁻ u, w' u * f u ∂τ := setLIntegral_mul_tsum_eq_lintegral_mul τ Γ (ι ⁻¹' D) hDι w' hw' hw'Γ f hf
      _ = ∫⁻ x in {x | 1 ≤ N x}, f x * ENNReal.ofReal (N x ^ (1 - s)) ∂τ := by
          rw [← lintegral_indicator hS1]
          refine lintegral_congr fun x => ?_
          by_cases hx : 1 ≤ N x
          · rw [Set.indicator_of_mem (show x ∈ {x | 1 ≤ N x} from hx), hw'_def]; dsimp only
            rw [Set.indicator_of_mem (show x ∈ {x | 1 ≤ N x} from hx), mul_comm]
          · rw [Set.indicator_of_notMem (show x ∉ {x | 1 ≤ N x} from hx), hw'_def]; dsimp only
            rw [Set.indicator_of_notMem (show x ∉ {x | 1 ≤ N x} from hx), zero_mul]

  have hT5 : ∫⁻ x in D, w x * (ENNReal.ofReal (N x)⁻¹ * φ0') ∂τ = φ0' * R * ENNReal.ofReal (1 / (s - 1)) := by
    simp_rw [← mul_assoc]
    rw [lintegral_mul_const _ (hw.fun_mul hn)]
    have h := setLIntegral_comp_eq_mul_lintegral_Ioi τ D hDm N hN (fun x _ => hNpos x) R hR hrate
      (fun r => wLow s r * ENNReal.ofReal r⁻¹) ((measurable_wLow s).mul (ENNReal.measurable_ofReal.comp
        measurable_inv))
    rw [show (fun x => w x * ENNReal.ofReal (N x)⁻¹) = fun x => wLow s (N x) * ENNReal.ofReal (N x)⁻¹ from rfl,
      h, lintegral_wLow_mul_inv_mul_inv hs]
    ring

  have hI : ∫⁻ x in D, w x * ((∑' γ : Γ, a (x * γ)) + φ0 + ENNReal.ofReal (N x)⁻¹ * ∑' γ : Γ, m (ι x * γ)) ∂τ =
      ∫⁻ x in D, w x * (ENNReal.ofReal (N x)⁻¹ * (∑' γ : Γ, p (ι x * γ)) + ENNReal.ofReal (N x)⁻¹ * φ0') ∂τ :=
    lintegral_congr fun x => by rw [hθ x]
  simp_rw [mul_add] at hI
  rw [lintegral_add_left ((hw.fun_mul mA).fun_add (hw.fun_mul measurable_const)),
    lintegral_add_left (hw.fun_mul mA),
    lintegral_add_left (hw.fun_mul (hn.fun_mul mPι)), hT1, hT2, hT34 m hm, hT34 p hp, hT5] at hI
  exact hI

end Main

section Iota

variable {R : Type*} [CommRing R]

def iotaFun (g : GL (Fin 2) R) : GL (Fin 2) R :=
  Matrix.GeneralLinearGroup.scalar (Fin 2) (Matrix.GeneralLinearGroup.det g)⁻¹ * g

theorem coe_scalar (u : Rˣ) :
    ((Matrix.GeneralLinearGroup.scalar (Fin 2) u : GL (Fin 2) R) : Matrix (Fin 2) (Fin 2) R) =
      Matrix.diagonal fun _ => (u : R) := by
  show ((Units.map (Matrix.scalar (Fin 2) : R →+* Matrix (Fin 2) (Fin 2) R).toMonoidHom) u : Matrix (Fin 2) (Fin 2) R)
    = _
  rw [Units.coe_map]
  exact Matrix.scalar_apply (u : R)

theorem scalar_mul_comm (u : Rˣ) (g : GL (Fin 2) R) :
    Matrix.GeneralLinearGroup.scalar (Fin 2) u * g = g * Matrix.GeneralLinearGroup.scalar (Fin 2) u := by
  refine Units.ext ?_
  rw [Units.val_mul, Units.val_mul, coe_scalar, ← Matrix.scalar_apply]
  exact (Matrix.scalar_commute (u : R) (fun r' => Commute.all _ _) _).eq

theorem det_scalar_two (u : Rˣ) :
    Matrix.GeneralLinearGroup.det (Matrix.GeneralLinearGroup.scalar (Fin 2) u) = u ^ 2 := by
  rw [Matrix.GeneralLinearGroup.det_scalar, Fintype.card_fin]

theorem det_iotaFun (g : GL (Fin 2) R) :
    Matrix.GeneralLinearGroup.det (iotaFun g) = (Matrix.GeneralLinearGroup.det g)⁻¹ := by
  rw [iotaFun, map_mul, det_scalar_two, sq, inv_mul_cancel_right]

theorem iotaFun_iotaFun (g : GL (Fin 2) R) : iotaFun (iotaFun g) = g := by
  rw [iotaFun, det_iotaFun, inv_inv, iotaFun, ← mul_assoc, ← map_mul, mul_inv_cancel, map_one, one_mul]

theorem coe_iotaFun (g : GL (Fin 2) R) :
    ((iotaFun g : GL (Fin 2) R) : Matrix (Fin 2) (Fin 2) R) =
      (((Matrix.GeneralLinearGroup.det g)⁻¹ : Rˣ) : R) • (g : Matrix (Fin 2) (Fin 2) R) := by
  rw [iotaFun, Matrix.GeneralLinearGroup.coe_mul, coe_scalar, ← Matrix.smul_eq_diagonal_mul]

theorem iotaFun_mul (g h : GL (Fin 2) R) : iotaFun (g * h) = iotaFun g * iotaFun h := by
  refine Units.ext ?_
  rw [Matrix.GeneralLinearGroup.coe_mul, coe_iotaFun, coe_iotaFun, coe_iotaFun, Matrix.GeneralLinearGroup.coe_mul,
    map_mul, mul_inv, Matrix.smul_mul, Matrix.mul_smul, smul_smul, Units.val_mul, mul_comm]

def iota : GL (Fin 2) R ≃* GL (Fin 2) R where
  toFun := iotaFun
  invFun := iotaFun
  left_inv := iotaFun_iotaFun
  right_inv := iotaFun_iotaFun
  map_mul' := iotaFun_mul

theorem iota_apply (g : GL (Fin 2) R) :
    iota g = Matrix.GeneralLinearGroup.scalar (Fin 2) (Matrix.GeneralLinearGroup.det g)⁻¹ * g := rfl

theorem iota_iota (g : GL (Fin 2) R) : iota (iota g) = g := iotaFun_iotaFun g

theorem det_iota (g : GL (Fin 2) R) :
    Matrix.GeneralLinearGroup.det (iota g) = (Matrix.GeneralLinearGroup.det g)⁻¹ := det_iotaFun g

theorem coe_iota (g : GL (Fin 2) R) :
    ((iota g : GL (Fin 2) R) : Matrix (Fin 2) (Fin 2) R) =
      (((Matrix.GeneralLinearGroup.det g)⁻¹ : Rˣ) : R) • (g : Matrix (Fin 2) (Fin 2) R) :=
  coe_iotaFun g

private theorem _root_.AutomorphicForm.QuatZeta.coe_map {S : Type*} [CommRing S] (f : R →+* S) (γ : GL (Fin 2) R) :
    ((Matrix.GeneralLinearGroup.map f γ : GL (Fin 2) S) : Matrix (Fin 2) (Fin 2) S) =
      (γ : Matrix (Fin 2) (Fin 2) R).map f := by
  ext i j; exact Matrix.GeneralLinearGroup.map_apply f i j γ

p2m_export "AutomorphicForm.QuatZeta" "coe_map"
theorem det_map {S : Type*} [CommRing S] (f : R →+* S) (γ : GL (Fin 2) R) :
    Matrix.GeneralLinearGroup.det (Matrix.GeneralLinearGroup.map f γ) =
      Units.map (f : R →* S) (Matrix.GeneralLinearGroup.det γ) := by
  refine Units.ext ?_
  rw [Matrix.GeneralLinearGroup.val_det_apply, Units.coe_map, MonoidHom.coe_coe, Matrix.GeneralLinearGroup.val_det_apply,
    coe_map, RingHom.map_det, RingHom.mapMatrix_apply]

theorem iota_map {S : Type*} [CommRing S] (f : R →+* S) (γ : GL (Fin 2) R) :
    iota (Matrix.GeneralLinearGroup.map f γ) = Matrix.GeneralLinearGroup.map f (iota γ) := by
  refine Units.ext ?_
  rw [coe_iota]
  ext i j
  rw [Matrix.smul_apply, Matrix.GeneralLinearGroup.map_apply, Matrix.GeneralLinearGroup.map_apply, coe_iota,
    Matrix.smul_apply, smul_eq_mul, smul_eq_mul, map_mul, det_map, ← map_inv, Units.coe_map, MonoidHom.coe_coe]

theorem map_scalar {S : Type*} [CommRing S] (f : R →+* S) (u : Rˣ) :
    Matrix.GeneralLinearGroup.map f (Matrix.GeneralLinearGroup.scalar (Fin 2) u) =
      Matrix.GeneralLinearGroup.scalar (Fin 2) (Units.map (f : R →* S) u) := by
  refine Units.ext (Matrix.ext fun i j => ?_)
  rw [Matrix.GeneralLinearGroup.map_apply, coe_scalar, coe_scalar, Matrix.diagonal_apply, Matrix.diagonal_apply]
  split_ifs
  · rfl
  · exact map_zero f

theorem map_det_eq_of_mem_sigmaCentralizer (φ : R →+* R) (δ t : GL (Fin 2) R)
    (ht : t ∈ sigmaCentralizer (Matrix.GeneralLinearGroup.map φ) δ) :
    Units.map (φ : R →* R) (Matrix.GeneralLinearGroup.det t) = Matrix.GeneralLinearGroup.det t := by
  rw [mem_sigmaCentralizer_iff] at ht
  have h := congrArg Matrix.GeneralLinearGroup.det ht
  rw [map_mul, map_mul, map_inv, det_map] at h
  have h' := mul_inv_eq_iff_eq_mul.1 h
  rw [mul_comm (Matrix.GeneralLinearGroup.det δ)] at h'
  exact (mul_right_cancel h').symm

theorem scalar_mem_sigmaCentralizer (φ : R →+* R) (δ : GL (Fin 2) R) (u : Rˣ)
    (hu : Units.map (φ : R →* R) u = u) :
    Matrix.GeneralLinearGroup.scalar (Fin 2) u ∈ sigmaCentralizer (Matrix.GeneralLinearGroup.map φ) δ := by
  rw [mem_sigmaCentralizer_iff, map_scalar, hu, scalar_mul_comm, mul_inv_cancel_right]

theorem iota_mem_sigmaCentralizer (φ : R →+* R) (δ t : GL (Fin 2) R)
    (ht : t ∈ sigmaCentralizer (Matrix.GeneralLinearGroup.map φ) δ) :
    iota t ∈ sigmaCentralizer (Matrix.GeneralLinearGroup.map φ) δ := by
  rw [iota_apply, map_inv]
  exact Subgroup.mul_mem _ (Subgroup.inv_mem _
    (scalar_mem_sigmaCentralizer φ δ _ (map_det_eq_of_mem_sigmaCentralizer φ δ t ht))) ht

end Iota

section Setting

p2m_open "AutomorphicForm P2MW.S_AutomorphicForm_setLIntegral_mul_ideleNorm_det_rpow_add_eq_setLIntegral_reflectPair_add_lintegral_mul_rate_of_isFundamentalDomain_twistedCentralizer_of_forall_ne_scalar_of_finrank_eq_two.AutomorphicForm"
open scoped TensorProduct TensorProduct.RightActions

variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]

attribute [local instance] NumberField.AdelicHaar.glBorel AutomorphicForm.twistedCentralizerBorel

abbrev inclA : L →+* L ⊗[K] AdeleRing (𝓞 K) K := Algebra.TensorProduct.includeLeftRingHom

abbrev Emap : L ⊗[K] AdeleRing (𝓞 K) K →+* AdeleRing (𝓞 L) L :=
  ((Algebra.TensorProduct.comm K L (AdeleRing (𝓞 K) K)).toRingEquiv.trans
    (M4aHerbrand.Bridge.genuineRingEquiv K L)).toRingHom

abbrev δA (δ₀ : GL (Fin 2) L) (c : (L ⊗[K] AdeleRing (𝓞 K) K)ˣ) :
    GL (Fin 2) (L ⊗[K] AdeleRing (𝓞 K) K) :=
  Matrix.GeneralLinearGroup.map (inclA K L) δ₀ * Matrix.GeneralLinearGroup.scalar (Fin 2) c

abbrev Tw (σ : L ≃ₐ[K] L) (δ₀ : GL (Fin 2) L) (c : (L ⊗[K] AdeleRing (𝓞 K) K)ˣ) :
    Subgroup (GL (Fin 2) (L ⊗[K] AdeleRing (𝓞 K) K)) :=
  AutomorphicForm.twistedCentralizer K L (AdeleRing (𝓞 K) K) σ (δA K L δ₀ c)

abbrev Γrat (σ : L ≃ₐ[K] L) (δ₀ : GL (Fin 2) L) : Subgroup (GL (Fin 2) L) :=
  AutomorphicForm.sigmaCentralizer (Matrix.GeneralLinearGroup.map (σ : L →+* L)) δ₀

abbrev ΓTw (σ : L ≃ₐ[K] L) (δ₀ : GL (Fin 2) L) (c : (L ⊗[K] AdeleRing (𝓞 K) K)ˣ) :
    Subgroup (Tw K L σ δ₀ c) :=
  ((Γrat K L σ δ₀).map (Matrix.GeneralLinearGroup.map (inclA K L))).subgroupOf (Tw K L σ δ₀ c)

variable (σ : L ≃ₐ[K] L) (δ₀ : GL (Fin 2) L) (c : (L ⊗[K] AdeleRing (𝓞 K) K)ˣ)

def normDet (t : Tw K L σ δ₀ c) : ℝ :=
  NumberField.TateGlobal.ideleNorm L (Matrix.GeneralLinearGroup.det (Matrix.GeneralLinearGroup.map (Emap K L)
    (t : GL (Fin 2) (L ⊗[K] AdeleRing (𝓞 K) K))))

theorem normDet_pos (t : Tw K L σ δ₀ c) : 0 < normDet K L σ δ₀ c t := NumberField.TateGlobal.ideleNorm_pos _

theorem normDet_mul (s t : Tw K L σ δ₀ c) :
    normDet K L σ δ₀ c (s * t) = normDet K L σ δ₀ c s * normDet K L σ δ₀ c t := by
  simp only [normDet, Subgroup.coe_mul, map_mul, NumberField.TateGlobal.ideleNorm]
  push_cast
  ring

theorem continuous_normDet : Continuous (normDet K L σ δ₀ c) := by
  haveI := isTopologicalRing_tensor K L (AdeleRing (𝓞 K) K)
  have hE : Continuous fun g : GL (Fin 2) (L ⊗[K] AdeleRing (𝓞 K) K) =>
      Matrix.GeneralLinearGroup.map (n := Fin 2) (Emap K L) g :=
    (baseChangeGLEquiv K L).continuous.congr fun g => rfl
  exact (NumberField.TateGlobal.continuous_ideleNorm L).comp
    (Matrix.GeneralLinearGroup.continuous_det.comp (hE.comp continuous_subtype_val))

theorem measurable_normDet : Measurable (normDet K L σ δ₀ c) := by
  haveI : BorelSpace (Tw K L σ δ₀ c) := ⟨rfl⟩
  exact (continuous_normDet K L σ δ₀ c).measurable

theorem ideleNorm_principal (a : Lˣ) :
    NumberField.TateGlobal.ideleNorm L (Units.map (algebraMap L (AdeleRing (𝓞 L) L) : L →* AdeleRing (𝓞 L) L) a) = 1 := by
  letI : MeasurableSpace (AdeleRing (𝓞 L) L) := borel _
  haveI : BorelSpace (AdeleRing (𝓞 L) L) := ⟨rfl⟩
  have h := NumberField.AdeleRing.distribHaarChar_algebraMap L a
  simp only [NumberField.TateGlobal.ideleNorm]
  rw [RingHom.toMonoidHom_eq_coe] at h
  rw [h]
  rfl

theorem map_Emap_map_inclA (g : GL (Fin 2) L) :
    Matrix.GeneralLinearGroup.map (Emap K L) (Matrix.GeneralLinearGroup.map (inclA K L) g) =
      globalPoints (𝓞 L) L g :=
  (AutomorphicForm.map_genuineRingEquiv_sigmaGL_and_toTensorGL_and_includeLeft K L
    (M4aHerbrand.GenuineDescent.genuineDescentDatum K L)).2.2 g

theorem normDet_of_mem (γ : Tw K L σ δ₀ c) (hγ : γ ∈ ΓTw K L σ δ₀ c) : normDet K L σ δ₀ c γ = 1 := by
  rw [Subgroup.mem_subgroupOf, Subgroup.mem_map] at hγ
  obtain ⟨g, -, hg⟩ := hγ
  simp only [normDet]
  rw [← hg, map_Emap_map_inclA]
  have hdet : Matrix.GeneralLinearGroup.det (globalPoints (𝓞 L) L g) =
      Units.map (algebraMap L (AdeleRing (𝓞 L) L) : L →* AdeleRing (𝓞 L) L)
        (Matrix.GeneralLinearGroup.det g) := det_map _ g
  rw [hdet, ideleNorm_principal L]

theorem normDet_mul_coe (t : Tw K L σ δ₀ c) (γ : ΓTw K L σ δ₀ c) :
    normDet K L σ δ₀ c (t * γ) = normDet K L σ δ₀ c t := by
  rw [normDet_mul, normDet_of_mem K L σ δ₀ c _ γ.2, mul_one]

theorem sigmaTensor_inclA (l : L) :
    sigmaTensor K L (AdeleRing (𝓞 K) K) σ (inclA K L l) = inclA K L (σ l) := by
  simp [sigmaTensor, Algebra.TensorProduct.map_tmul, Algebra.TensorProduct.includeLeftRingHom_apply]

theorem sigmaGL_map_inclA (g : GL (Fin 2) L) :
    sigmaGL K L (AdeleRing (𝓞 K) K) σ (Matrix.GeneralLinearGroup.map (inclA K L) g) =
      Matrix.GeneralLinearGroup.map (inclA K L) (Matrix.GeneralLinearGroup.map (σ : L →+* L) g) := by
  refine Units.ext (Matrix.ext fun i j => ?_)
  exact sigmaTensor_inclA K L σ (g i j)

theorem map_mem_Tw (g : GL (Fin 2) L) (hg : g ∈ Γrat K L σ δ₀) :
    Matrix.GeneralLinearGroup.map (inclA K L) g ∈ Tw K L σ δ₀ c := by
  rw [mem_sigmaCentralizer_iff] at hg ⊢
  show _ * _ * (sigmaGL K L (AdeleRing (𝓞 K) K) σ _)⁻¹ = _
  rw [sigmaGL_map_inclA, ← map_inv, mul_assoc, mul_assoc, scalar_mul_comm c, ← mul_assoc,
    ← mul_assoc, ← map_mul, ← map_mul, hg]

theorem inclA_injective : Function.Injective (inclA K L) := by
  intro a b hab
  have h := congrArg (Emap K L) hab
  have hE : ∀ l : L, Emap K L (inclA K L l) = algebraMap L (AdeleRing (𝓞 L) L) l := fun l => by
    show M4aHerbrand.Bridge.genuineRingEquiv K L ((Algebra.TensorProduct.comm K L (AdeleRing (𝓞 K) K))
      (l ⊗ₜ[K] (1 : AdeleRing (𝓞 K) K))) = _
    rw [Algebra.TensorProduct.comm_tmul]
    exact M4aHerbrand.Bridge.genuineRingEquiv_one_tmul K L l
  rw [hE, hE] at h
  haveI : Nontrivial (AdeleRing (𝓞 L) L) := inferInstanceAs (Nontrivial (InfiniteAdeleRing L × IsDedekindDomain.FiniteAdeleRing (𝓞 L) L))
  exact (algebraMap L (AdeleRing (𝓞 L) L)).injective h

theorem map_inclA_injective :
    Function.Injective (Matrix.GeneralLinearGroup.map (n := Fin 2) (inclA K L)) := by
  intro g h hgh
  refine Units.ext (Matrix.ext fun i j => inclA_injective K L ?_)
  have h1 : ((g : Matrix (Fin 2) (Fin 2) L).map (inclA K L)) = (h : Matrix (Fin 2) (Fin 2) L).map (inclA K L) := by
    rw [← coe_map, ← coe_map, hgh]
  have h2 := congrFun (congrFun h1 i) j
  simpa only [Matrix.map_apply] using h2

def ratPt (g : Γrat K L σ δ₀) : ΓTw K L σ δ₀ c :=
  ⟨⟨Matrix.GeneralLinearGroup.map (inclA K L) g, map_mem_Tw K L σ δ₀ c g g.2⟩, by
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_map]
    exact ⟨g, g.2, rfl⟩⟩

theorem coe_coe_ratPt (g : Γrat K L σ δ₀) :
    (((ratPt K L σ δ₀ c g : ΓTw K L σ δ₀ c) : Tw K L σ δ₀ c) : GL (Fin 2) (L ⊗[K] AdeleRing (𝓞 K) K)) =
      Matrix.GeneralLinearGroup.map (inclA K L) g := rfl

theorem ratPt_bijective : Function.Bijective (ratPt K L σ δ₀ c) := by
  refine ⟨fun g h hgh => ?_, fun γ => ?_⟩
  · have h1 := congrArg (fun x : ΓTw K L σ δ₀ c => ((x : Tw K L σ δ₀ c) : GL (Fin 2) (L ⊗[K] AdeleRing (𝓞 K) K))) hgh
    simp only [coe_coe_ratPt] at h1
    exact Subtype.ext (map_inclA_injective K L h1)
  · have hγ := γ.2
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_map] at hγ
    obtain ⟨g, hg, hgγ⟩ := hγ
    exact ⟨⟨g, hg⟩, Subtype.ext (Subtype.ext hgγ)⟩

def eqΓ : Γrat K L σ δ₀ ≃ ΓTw K L σ δ₀ c := Equiv.ofBijective _ (ratPt_bijective K L σ δ₀ c)

theorem coe_coe_eqΓ (g : Γrat K L σ δ₀) :
    (((eqΓ K L σ δ₀ c g : ΓTw K L σ δ₀ c) : Tw K L σ δ₀ c) : GL (Fin 2) (L ⊗[K] AdeleRing (𝓞 K) K)) =
      Matrix.GeneralLinearGroup.map (inclA K L) g := rfl

scoped instance countable_ΓTw : Countable (ΓTw K L σ δ₀ c) := by
  haveI : Countable L := (Module.Free.chooseBasis ℚ L).equivFun.toEquiv.countable_iff.2 inferInstance
  haveI : Countable (Matrix (Fin 2) (Fin 2) L) := inferInstanceAs (Countable (Fin 2 → Fin 2 → L))
  haveI : Countable (GL (Fin 2) L) :=
    Function.Injective.countable (f := fun g : GL (Fin 2) L => (g : Matrix (Fin 2) (Fin 2) L))
      fun g h hgh => Units.ext hgh
  exact (ratPt_bijective K L σ δ₀ c).2.countable

theorem iota_mem_Tw (t : Tw K L σ δ₀ c) :
    iota (t : GL (Fin 2) (L ⊗[K] AdeleRing (𝓞 K) K)) ∈ Tw K L σ δ₀ c :=
  iota_mem_sigmaCentralizer (sigmaTensor K L (AdeleRing (𝓞 K) K) σ) (δA K L δ₀ c) _ t.2

theorem iota_mem_Γrat (g : Γrat K L σ δ₀) : iota (g : GL (Fin 2) L) ∈ Γrat K L σ δ₀ :=
  iota_mem_sigmaCentralizer (σ : L →+* L) δ₀ _ g.2

def iotaT : Tw K L σ δ₀ c ≃* Tw K L σ δ₀ c where
  toFun t := ⟨iota (t : GL (Fin 2) (L ⊗[K] AdeleRing (𝓞 K) K)), iota_mem_Tw K L σ δ₀ c t⟩
  invFun t := ⟨iota (t : GL (Fin 2) (L ⊗[K] AdeleRing (𝓞 K) K)), iota_mem_Tw K L σ δ₀ c t⟩
  left_inv t := Subtype.ext (iota_iota _)
  right_inv t := Subtype.ext (iota_iota _)
  map_mul' s t := Subtype.ext (map_mul iota _ _)

theorem coe_iotaT (t : Tw K L σ δ₀ c) :
    ((iotaT K L σ δ₀ c t : Tw K L σ δ₀ c) : GL (Fin 2) (L ⊗[K] AdeleRing (𝓞 K) K)) =
      iota (t : GL (Fin 2) (L ⊗[K] AdeleRing (𝓞 K) K)) := rfl

theorem iotaT_iotaT (t : Tw K L σ δ₀ c) : iotaT K L σ δ₀ c (iotaT K L σ δ₀ c t) = t :=
  Subtype.ext (iota_iota _)

theorem continuous_iotaT : Continuous (iotaT K L σ δ₀ c) := by
  haveI := isTopologicalRing_tensor K L (AdeleRing (𝓞 K) K)
  haveI := isTopologicalGroup_tensorGL K L (AdeleRing (𝓞 K) K)
  refine Continuous.subtype_mk ?_ _
  have hsc : Continuous (Matrix.GeneralLinearGroup.scalar (Fin 2) :
      (L ⊗[K] AdeleRing (𝓞 K) K)ˣ → GL (Fin 2) (L ⊗[K] AdeleRing (𝓞 K) K)) := by
    refine Units.continuous_iff.2 ⟨?_, ?_⟩
    · have h1 : Continuous fun z : (L ⊗[K] AdeleRing (𝓞 K) K)ˣ => fun _ : Fin 2 => (z : L ⊗[K] AdeleRing (𝓞 K) K) :=
        continuous_pi fun _ => Units.continuous_val
      exact h1.matrix_diagonal.congr fun z => (coe_scalar z).symm
    · have h1 : Continuous fun z : (L ⊗[K] AdeleRing (𝓞 K) K)ˣ => fun _ : Fin 2 =>
          ((z⁻¹ : (L ⊗[K] AdeleRing (𝓞 K) K)ˣ) : L ⊗[K] AdeleRing (𝓞 K) K) :=
        continuous_pi fun _ => Units.continuous_coe_inv
      refine h1.matrix_diagonal.congr fun z => ?_
      rw [← map_inv]; exact (coe_scalar z⁻¹).symm
  show Continuous fun t : Tw K L σ δ₀ c =>
    Matrix.GeneralLinearGroup.scalar (Fin 2) (Matrix.GeneralLinearGroup.det
      (t : GL (Fin 2) (L ⊗[K] AdeleRing (𝓞 K) K)))⁻¹ * (t : GL (Fin 2) (L ⊗[K] AdeleRing (𝓞 K) K))
  exact (hsc.comp ((Matrix.GeneralLinearGroup.continuous_det.comp continuous_subtype_val).inv)).mul
    continuous_subtype_val

theorem measurable_iotaT : Measurable (iotaT K L σ δ₀ c) := by
  haveI : BorelSpace (Tw K L σ δ₀ c) := ⟨rfl⟩
  exact (continuous_iotaT K L σ δ₀ c).measurable

theorem ideleNorm_inv (x : (AdeleRing (𝓞 L) L)ˣ) :
    NumberField.TateGlobal.ideleNorm L x⁻¹ = (NumberField.TateGlobal.ideleNorm L x)⁻¹ := by
  unfold NumberField.TateGlobal.ideleNorm
  rw [map_inv, NNReal.coe_inv]

theorem normDet_iotaT (t : Tw K L σ δ₀ c) :
    normDet K L σ δ₀ c (iotaT K L σ δ₀ c t) = (normDet K L σ δ₀ c t)⁻¹ := by
  simp only [normDet, coe_iotaT]
  rw [← iota_map, det_iota, ideleNorm_inv]

theorem iotaT_mem_ΓTw (γ : Tw K L σ δ₀ c) (hγ : γ ∈ ΓTw K L σ δ₀ c) :
    iotaT K L σ δ₀ c γ ∈ ΓTw K L σ δ₀ c := by
  rw [Subgroup.mem_subgroupOf, Subgroup.mem_map] at hγ ⊢
  obtain ⟨g, hg, hgγ⟩ := hγ
  refine ⟨iota g, iota_mem_Γrat K L σ δ₀ ⟨g, hg⟩, ?_⟩
  rw [coe_iotaT, ← hgγ, iota_map]

theorem isFundamentalDomain_preimage_iotaT (τ' : Measure (Tw K L σ δ₀ c))
    (hpres : MeasurePreserving (iotaT K L σ δ₀ c) τ' τ') {D : Set (Tw K L σ δ₀ c)}
    (hD : IsFundamentalDomain (ΓTw K L σ δ₀ c).op D τ') :
    IsFundamentalDomain (ΓTw K L σ δ₀ c).op ((iotaT K L σ δ₀ c) ⁻¹' D) τ' := by
  have hmem : ∀ x : ↥(ΓTw K L σ δ₀ c).op,
      MulOpposite.op (iotaT K L σ δ₀ c (MulOpposite.unop x.1)) ∈ (ΓTw K L σ δ₀ c).op := fun x =>
    Subgroup.mem_op.2 (iotaT_mem_ΓTw K L σ δ₀ c _ (Subgroup.mem_op.1 x.2))
  let e : ↥(ΓTw K L σ δ₀ c).op → ↥(ΓTw K L σ δ₀ c).op := fun x =>
    ⟨MulOpposite.op (iotaT K L σ δ₀ c (MulOpposite.unop x.1)), hmem x⟩
  have he_inv : Function.Involutive e := fun x => Subtype.ext (by
    show MulOpposite.op (iotaT K L σ δ₀ c (MulOpposite.unop (MulOpposite.op
      (iotaT K L σ δ₀ c (MulOpposite.unop x.1))))) = x.1
    rw [MulOpposite.unop_op, iotaT_iotaT, MulOpposite.op_unop])
  refine hD.preimage_of_equiv hpres.quasiMeasurePreserving he_inv.bijective fun x g => ?_
  show iotaT K L σ δ₀ c (g * MulOpposite.unop (e x).1) = iotaT K L σ δ₀ c g * MulOpposite.unop x.1
  show iotaT K L σ δ₀ c (g * iotaT K L σ δ₀ c (MulOpposite.unop x.1)) = iotaT K L σ δ₀ c g * MulOpposite.unop x.1
  rw [map_mul, iotaT_iotaT]

def colv (v : Fin 2 → L) (t : Tw K L σ δ₀ c) : Fin 2 → AdeleRing (𝓞 L) L :=
  ((Matrix.GeneralLinearGroup.map (Emap K L) (t : GL (Fin 2) (L ⊗[K] AdeleRing (𝓞 K) K)) :
      GL (Fin 2) (AdeleRing (𝓞 L) L)) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 L) L)).mulVec
    fun i => algebraMap L (AdeleRing (𝓞 L) L) (v i)

theorem continuous_colv (v : Fin 2 → L) : Continuous (colv K L σ δ₀ c v) := by
  haveI := isTopologicalRing_tensor K L (AdeleRing (𝓞 K) K)
  have hE : Continuous fun g : GL (Fin 2) (L ⊗[K] AdeleRing (𝓞 K) K) =>
      Matrix.GeneralLinearGroup.map (n := Fin 2) (Emap K L) g :=
    (baseChangeGLEquiv K L).continuous.congr fun g => rfl
  exact (Units.continuous_val.comp (hE.comp continuous_subtype_val)).matrix_mulVec continuous_const

theorem globalPoints_mulVec (g : GL (Fin 2) L) (v : Fin 2 → L) :
    ((globalPoints (𝓞 L) L g : GL (Fin 2) (AdeleRing (𝓞 L) L)) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 L) L)).mulVec
        (fun i => algebraMap L (AdeleRing (𝓞 L) L) (v i)) =
      fun i => algebraMap L (AdeleRing (𝓞 L) L) (((g : Matrix (Fin 2) (Fin 2) L).mulVec v) i) := by
  funext i
  rw [RingHom.map_mulVec]
  rfl

theorem colv_mul_eqΓ (v : Fin 2 → L) (t : Tw K L σ δ₀ c) (g : Γrat K L σ δ₀) :
    colv K L σ δ₀ c v (t * (eqΓ K L σ δ₀ c g : Tw K L σ δ₀ c)) =
      ((Matrix.GeneralLinearGroup.map (Emap K L) (t : GL (Fin 2) (L ⊗[K] AdeleRing (𝓞 K) K)) :
          GL (Fin 2) (AdeleRing (𝓞 L) L)) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 L) L)).mulVec
        fun i => algebraMap L (AdeleRing (𝓞 L) L) ((((g : GL (Fin 2) L) : Matrix (Fin 2) (Fin 2) L).mulVec v) i) := by
  unfold colv
  rw [Subgroup.coe_mul, coe_coe_eqΓ, map_mul, map_Emap_map_inclA, Matrix.GeneralLinearGroup.coe_mul,
    ← Matrix.mulVec_mulVec, globalPoints_mulVec]

theorem colv_iotaT_mul_eqΓ (v : Fin 2 → L) (t : Tw K L σ δ₀ c) (g : Γrat K L σ δ₀) :
    colv K L σ δ₀ c v (iotaT K L σ δ₀ c t * (eqΓ K L σ δ₀ c g : Tw K L σ δ₀ c)) =
      (((Matrix.GeneralLinearGroup.det (Matrix.GeneralLinearGroup.map (Emap K L)
          (t : GL (Fin 2) (L ⊗[K] AdeleRing (𝓞 K) K))))⁻¹ : (AdeleRing (𝓞 L) L)ˣ) : AdeleRing (𝓞 L) L) •
      ((Matrix.GeneralLinearGroup.map (Emap K L) (t : GL (Fin 2) (L ⊗[K] AdeleRing (𝓞 K) K)) :
          GL (Fin 2) (AdeleRing (𝓞 L) L)) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 L) L)).mulVec
        fun i => algebraMap L (AdeleRing (𝓞 L) L) ((((g : GL (Fin 2) L) : Matrix (Fin 2) (Fin 2) L).mulVec v) i) := by
  unfold colv
  rw [Subgroup.coe_mul, coe_coe_eqΓ, map_mul, map_Emap_map_inclA, Matrix.GeneralLinearGroup.coe_mul,
    ← Matrix.mulVec_mulVec, globalPoints_mulVec, coe_iotaT, ← iota_map, coe_iota, Matrix.smul_mulVec]

end Setting

section Theta

p2m_open "AutomorphicForm P2MW.S_AutomorphicForm_setLIntegral_mul_ideleNorm_det_rpow_add_eq_setLIntegral_reflectPair_add_lintegral_mul_rate_of_isFundamentalDomain_twistedCentralizer_of_forall_ne_scalar_of_finrank_eq_two.AutomorphicForm NumberField.AdelicFourier NumberField.AdelicBox NumberField.TateGlobal"
open scoped TensorProduct TensorProduct.RightActions

variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]

attribute [local instance] NumberField.AdelicHaar.glBorel AutomorphicForm.twistedCentralizerBorel

variable (σ : L ≃ₐ[K] L) (δ₀ : GL (Fin 2) L) (c : (L ⊗[K] AdeleRing (𝓞 K) K)ˣ)

theorem ofReal_eq_ofReal_max (r : ℝ) : ENNReal.ofReal r = ENNReal.ofReal (max r 0) := by
  rcases le_total 0 r with h | h
  · rw [max_eq_left h]
  · rw [max_eq_right h, ENNReal.ofReal_of_nonpos h, ENNReal.ofReal_zero]

theorem summable_parts {ι : Type*} {f : ι → ℂ} (hf : Summable f) :
    Summable (fun i => (f i).re) ∧ Summable (fun i => max (f i).re 0) ∧ Summable (fun i => max (-(f i).re) 0) := by
  have hn : Summable fun i => ‖f i‖ := summable_norm_iff.2 hf
  refine ⟨((Complex.hasSum_iff _ _).1 hf.hasSum).1.summable, ?_, ?_⟩
  · exact Summable.of_nonneg_of_le (fun i => le_max_right _ _)
      (fun i => max_le ((le_abs_self _).trans (Complex.abs_re_le_norm _)) (norm_nonneg _)) hn
  · exact Summable.of_nonneg_of_le (fun i => le_max_right _ _)
      (fun i => max_le ((neg_le_abs _).trans (Complex.abs_re_le_norm _)) (norm_nonneg _)) hn

theorem theta_identity
    (h2 : Module.finrank K L = 2) (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ)
    (hN₀ : ∃ z : Lˣ, δ₀ * Matrix.GeneralLinearGroup.map (σ : L →+* L) δ₀ =
      Matrix.GeneralLinearGroup.scalar (Fin 2) z)
    (hns : ∀ (x : GL (Fin 2) L) (z : Lˣ),
      x⁻¹ * δ₀ * Matrix.GeneralLinearGroup.map (σ : L →+* L) x ≠
        Matrix.GeneralLinearGroup.scalar (Fin 2) z)
    (v : Fin 2 → L) (hv : v ≠ 0)
    [MeasurableSpace (AdeleRing (𝓞 L) L)] [BorelSpace (AdeleRing (𝓞 L) L)]
    (μ₁ : Measure (AdeleRing (𝓞 L) L)) [μ₁.IsAddHaarMeasure] (hμ₁ : μ₁ (adelicBox L) = 1)
    {ψ : AddChar (AdeleRing (𝓞 L) L) ℂ} (hψ : IsGlobalAddChar L ψ)
    {Φ : (Fin 2 → AdeleRing (𝓞 L) L) → ℂ} (hΦ : Φ ∈ schwartzBruhat2 L)
    (hΦnn : ∀ x, 0 ≤ (Φ x).re) (hΦ'0 : 0 ≤ (reflectPair ψ μ₁ Φ 0).re)
    (t : Tw K L σ δ₀ c) :
    (∑' γ : ΓTw K L σ δ₀ c, ENNReal.ofReal (Φ (colv K L σ δ₀ c v (t * γ))).re) +
        ENNReal.ofReal (Φ 0).re +
        ENNReal.ofReal (normDet K L σ δ₀ c t)⁻¹ *
          ∑' γ : ΓTw K L σ δ₀ c, ENNReal.ofReal (-(reflectPair ψ μ₁ Φ (colv K L σ δ₀ c v (iotaT K L σ δ₀ c t * γ))).re) =
      ENNReal.ofReal (normDet K L σ δ₀ c t)⁻¹ *
          (∑' γ : ΓTw K L σ δ₀ c, ENNReal.ofReal (reflectPair ψ μ₁ Φ (colv K L σ δ₀ c v (iotaT K L σ δ₀ c t * γ))).re) +
        ENNReal.ofReal (normDet K L σ δ₀ c t)⁻¹ * ENNReal.ofReal (reflectPair ψ μ₁ Φ 0).re := by

  set G : GL (Fin 2) (AdeleRing (𝓞 L) L) :=
    Matrix.GeneralLinearGroup.map (Emap K L) (t : GL (Fin 2) (L ⊗[K] AdeleRing (𝓞 K) K)) with hG
  obtain ⟨hs1, hs2, hid⟩ :=
    AutomorphicForm.tsum_sigmaCentralizer_apply_mulVec_add_eq_inv_ideleNorm_det_mul_tsum_reflectPair_of_forall_ne_scalar_of_finrank_eq_two
      K L h2 σ hgen δ₀ hN₀ hns v hv μ₁ hμ₁ hψ hΦ G

  set F1 : Γrat K L σ δ₀ → ℂ := fun γ =>
    Φ ((G : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 L) L)).mulVec fun i =>
      algebraMap L (AdeleRing (𝓞 L) L) ((((γ : GL (Fin 2) L) : Matrix (Fin 2) (Fin 2) L).mulVec v) i)) with hF1
  set F2 : Γrat K L σ δ₀ → ℂ := fun γ =>
    reflectPair ψ μ₁ Φ ((((Matrix.GeneralLinearGroup.det G)⁻¹ : (AdeleRing (𝓞 L) L)ˣ) : AdeleRing (𝓞 L) L) •
      (G : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 L) L)).mulVec fun i =>
        algebraMap L (AdeleRing (𝓞 L) L) ((((γ : GL (Fin 2) L) : Matrix (Fin 2) (Fin 2) L).mulVec v) i)) with hF2
  change Summable F1 at hs1
  change Summable F2 at hs2
  change (∑' γ, F1 γ) + Φ 0 = (((ideleNorm L (Matrix.GeneralLinearGroup.det G))⁻¹ : ℝ) : ℂ) *
    ((∑' γ, F2 γ) + reflectPair ψ μ₁ Φ 0) at hid

  set e := eqΓ K L σ δ₀ c with he
  have hA : (∑' γ : ΓTw K L σ δ₀ c, ENNReal.ofReal (Φ (colv K L σ δ₀ c v (t * γ))).re) =
      ∑' γ : Γrat K L σ δ₀, ENNReal.ofReal (F1 γ).re := by
    rw [← Equiv.tsum_eq e]
    exact tsum_congr fun γ => by rw [he, colv_mul_eqΓ]
  have hP : (∑' γ : ΓTw K L σ δ₀ c, ENNReal.ofReal (reflectPair ψ μ₁ Φ (colv K L σ δ₀ c v (iotaT K L σ δ₀ c t * γ))).re) =
      ∑' γ : Γrat K L σ δ₀, ENNReal.ofReal (max (F2 γ).re 0) := by
    rw [← Equiv.tsum_eq e]
    exact tsum_congr fun γ => by rw [he, colv_iotaT_mul_eqΓ, ofReal_eq_ofReal_max]
  have hM : (∑' γ : ΓTw K L σ δ₀ c, ENNReal.ofReal (-(reflectPair ψ μ₁ Φ (colv K L σ δ₀ c v (iotaT K L σ δ₀ c t * γ))).re)) =
      ∑' γ : Γrat K L σ δ₀, ENNReal.ofReal (max (-(F2 γ).re) 0) := by
    rw [← Equiv.tsum_eq e]
    exact tsum_congr fun γ => by rw [he, colv_iotaT_mul_eqΓ, ofReal_eq_ofReal_max]
  rw [hA, hP, hM]

  obtain ⟨hs1re, -, -⟩ := summable_parts hs1
  obtain ⟨hs2re, hs2p, hs2m⟩ := summable_parts hs2
  have hs1re' : Summable fun γ => (F1 γ).re := hs1re

  have hre := congrArg Complex.re hid
  rw [Complex.add_re, Complex.re_ofReal_mul, Complex.add_re, Complex.re_tsum hs1, Complex.re_tsum hs2] at hre
  have hpm : (fun γ => (F2 γ).re) = fun γ => max (F2 γ).re 0 - max (-(F2 γ).re) 0 := by
    funext γ
    rcases le_total 0 (F2 γ).re with h | h
    · rw [max_eq_left h, max_eq_right (neg_nonpos.2 h), sub_zero]
    · rw [max_eq_right h, max_eq_left (neg_nonneg.2 h), zero_sub, neg_neg]
  rw [show (fun γ => (F2 γ).re) = fun γ => max (F2 γ).re 0 - max (-(F2 γ).re) 0 from hpm, hs2p.tsum_sub hs2m] at hre
  set A := ∑' γ, (F1 γ).re with hAdef
  set Up := ∑' γ, max (F2 γ).re 0 with hUp
  set Um := ∑' γ, max (-(F2 γ).re) 0 with hUm
  set Nn := ideleNorm L (Matrix.GeneralLinearGroup.det G) with hNn
  have hNt : normDet K L σ δ₀ c t = Nn := rfl
  have key : A + (Φ 0).re + Nn⁻¹ * Um = Nn⁻¹ * Up + Nn⁻¹ * (reflectPair ψ μ₁ Φ 0).re := by linear_combination hre
  have hA0 : 0 ≤ A := tsum_nonneg fun γ => hΦnn _
  have hUp0 : 0 ≤ Up := tsum_nonneg fun γ => le_max_right _ _
  have hUm0 : 0 ≤ Um := tsum_nonneg fun γ => le_max_right _ _
  have hN0 : 0 ≤ Nn⁻¹ := inv_nonneg.2 (ideleNorm_pos _).le

  have tA : (∑' γ : Γrat K L σ δ₀, ENNReal.ofReal (F1 γ).re) = ENNReal.ofReal A := by
    rw [hAdef, ENNReal.ofReal_tsum_of_nonneg (fun γ => hΦnn _) hs1re']
  have tp : (∑' γ : Γrat K L σ δ₀, ENNReal.ofReal (max (F2 γ).re 0)) = ENNReal.ofReal Up := by
    rw [hUp, ENNReal.ofReal_tsum_of_nonneg (fun γ => le_max_right _ _) hs2p]
  have tm : (∑' γ : Γrat K L σ δ₀, ENNReal.ofReal (max (-(F2 γ).re) 0)) = ENNReal.ofReal Um := by
    rw [hUm, ENNReal.ofReal_tsum_of_nonneg (fun γ => le_max_right _ _) hs2m]
  rw [tA, tp, tm, hNt]
  calc ENNReal.ofReal A + ENNReal.ofReal (Φ 0).re + ENNReal.ofReal Nn⁻¹ * ENNReal.ofReal Um
      = ENNReal.ofReal (A + (Φ 0).re + Nn⁻¹ * Um) := by
        rw [← ENNReal.ofReal_mul hN0, ← ENNReal.ofReal_add hA0 (hΦnn 0),
          ← ENNReal.ofReal_add (add_nonneg hA0 (hΦnn 0)) (mul_nonneg hN0 hUm0)]
    _ = ENNReal.ofReal (Nn⁻¹ * Up + Nn⁻¹ * (reflectPair ψ μ₁ Φ 0).re) := by rw [key]
    _ = ENNReal.ofReal Nn⁻¹ * ENNReal.ofReal Up + ENNReal.ofReal Nn⁻¹ * ENNReal.ofReal (reflectPair ψ μ₁ Φ 0).re := by
        rw [ENNReal.ofReal_add (mul_nonneg hN0 hUp0) (mul_nonneg hN0 hΦ'0), ENNReal.ofReal_mul hN0,
          ENNReal.ofReal_mul hN0]

theorem reflectPair_zero
    [MeasurableSpace (AdeleRing (𝓞 L) L)]
    (μ₁ : Measure (AdeleRing (𝓞 L) L)) (ψ : AddChar (AdeleRing (𝓞 L) L) ℂ)
    (Φ : (Fin 2 → AdeleRing (𝓞 L) L) → ℂ) :
    reflectPair ψ μ₁ Φ 0 = ∫ x, Φ x ∂(pairHaar μ₁) := by
  have h0 : (![(0 : Fin 2 → AdeleRing (𝓞 L) L) 1, -(0 : Fin 2 → AdeleRing (𝓞 L) L) 0] :
      Fin 2 → AdeleRing (𝓞 L) L) = 0 := by
    funext i; fin_cases i <;> simp
  show fourierTransform2 ψ μ₁ Φ ![(0 : Fin 2 → AdeleRing (𝓞 L) L) 1, -(0 : Fin 2 → AdeleRing (𝓞 L) L) 0] = _
  rw [h0, fourierTransform2, fourierIntegral_def]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  show pairChar ψ (-(x * 0)) * Φ x = Φ x
  rw [mul_zero, neg_zero, AddChar.map_zero_eq_one, one_mul]

theorem ofReal_re_reflectPair_zero
    [MeasurableSpace (AdeleRing (𝓞 L) L)] [BorelSpace (AdeleRing (𝓞 L) L)]
    (μ₁ : Measure (AdeleRing (𝓞 L) L)) [μ₁.IsAddHaarMeasure] (ψ : AddChar (AdeleRing (𝓞 L) L) ℂ)
    {Φ : (Fin 2 → AdeleRing (𝓞 L) L) → ℂ} (hΦ : Φ ∈ schwartzBruhat2 L) (hΦnn : ∀ x, 0 ≤ (Φ x).re) :
    0 ≤ (reflectPair ψ μ₁ Φ 0).re ∧
      ENNReal.ofReal (reflectPair ψ μ₁ Φ 0).re = ∫⁻ x, ENNReal.ofReal (Φ x).re ∂(pairHaar μ₁) := by
  have hint : Integrable Φ (pairHaar μ₁) :=
    (NumberField.AdelicFourier.continuous_integrable_comp_vecMul_mem_and_bottomRowVec_mem_schwartzBruhat_of_mem_schwartzBruhat2
      L Φ hΦ).2.2.2.1 μ₁
  have hre : (reflectPair ψ μ₁ Φ 0).re = ∫ x, (Φ x).re ∂(pairHaar μ₁) := by
    rw [reflectPair_zero]
    exact (integral_re hint).symm
  have hnn : 0 ≤ ∫ x, (Φ x).re ∂(pairHaar μ₁) := integral_nonneg fun x => hΦnn x
  refine ⟨hre ▸ hnn, ?_⟩
  have hint' : Integrable (fun x => (Φ x).re) (pairHaar μ₁) := hint.re
  rw [hre, ofReal_integral_eq_lintegral_ofReal hint' (Filter.Eventually.of_forall fun x => hΦnn x)]

end Theta

section Assembly

p2m_open "AutomorphicForm P2MW.S_AutomorphicForm_setLIntegral_mul_ideleNorm_det_rpow_add_eq_setLIntegral_reflectPair_add_lintegral_mul_rate_of_isFundamentalDomain_twistedCentralizer_of_forall_ne_scalar_of_finrank_eq_two.AutomorphicForm NumberField.AdelicFourier NumberField.AdelicBox NumberField.TateGlobal"
open scoped TensorProduct TensorProduct.RightActions

variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]

attribute [local instance] NumberField.AdelicHaar.glBorel AutomorphicForm.twistedCentralizerBorel

theorem t2Space_GL (A : Type) [CommRing A] [TopologicalSpace A] [IsTopologicalRing A] [T2Space A] :
    T2Space (GL (Fin 2) A) := by
  haveI : T2Space (Matrix (Fin 2) (Fin 2) A) := inferInstanceAs (T2Space (Fin 2 → Fin 2 → A))
  exact Units.isEmbedding_embedProduct.t2Space

theorem locallyCompactSpace_GL (A : Type) [CommRing A] [TopologicalSpace A] [IsTopologicalRing A] [T2Space A]
    [LocallyCompactSpace A] : LocallyCompactSpace (GL (Fin 2) A) := by
  haveI : T2Space (Matrix (Fin 2) (Fin 2) A) := inferInstanceAs (T2Space (Fin 2 → Fin 2 → A))
  haveI : LocallyCompactSpace (Matrix (Fin 2) (Fin 2) A) :=
    inferInstanceAs (LocallyCompactSpace (Fin 2 → Fin 2 → A))
  exact Units.isClosedEmbedding_embedProduct.locallyCompactSpace

theorem continuous_sigmaGL (A : Type) [CommRing A] [Algebra K A] [TopologicalSpace A] [IsTopologicalRing A]
    (σ : L ≃ₐ[K] L) : Continuous (AutomorphicForm.sigmaGL K L A σ) := by
  haveI := AutomorphicForm.isTopologicalRing_tensor K L A
  refine Continuous.units_map _ ?_
  have hc : Continuous (AutomorphicForm.sigmaTensor K L A σ) :=
    IsModuleTopology.continuous_of_linearMap
      (TensorProduct.RightActions.AlgebraMap.baseChange K L L A σ.toAlgHom).toLinearMap
  exact continuous_id.matrix_map hc

theorem isClosed_twistedCentralizer (A : Type) [CommRing A] [Algebra K A] [TopologicalSpace A]
    [IsTopologicalRing A] [T2Space A] (σ : L ≃ₐ[K] L) (δ : GL (Fin 2) (L ⊗[K] A)) :
    IsClosed ((AutomorphicForm.twistedCentralizer K L A σ δ : Subgroup (GL (Fin 2) (L ⊗[K] A))) :
      Set (GL (Fin 2) (L ⊗[K] A))) := by
  haveI := AutomorphicForm.isTopologicalGroup_tensorGL K L A
  haveI := AutomorphicForm.t2Space_tensorGL K L A
  have hc : Continuous fun t : GL (Fin 2) (L ⊗[K] A) =>
      t * δ * (AutomorphicForm.sigmaGL K L A σ t)⁻¹ :=
    (continuous_id.mul continuous_const).mul (continuous_sigmaGL K L A σ).inv
  have : ((AutomorphicForm.twistedCentralizer K L A σ δ : Subgroup (GL (Fin 2) (L ⊗[K] A))) :
      Set (GL (Fin 2) (L ⊗[K] A))) =
      (fun t : GL (Fin 2) (L ⊗[K] A) => t * δ * (AutomorphicForm.sigmaGL K L A σ t)⁻¹) ⁻¹' {δ} := by
    ext t
    exact AutomorphicForm.mem_sigmaCentralizer_iff
  rw [this]
  exact (isClosed_singleton).preimage hc

theorem main
    (h2 : Module.finrank K L = 2) (σ : L ≃ₐ[K] L) (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ)
    (δ₀ : GL (Fin 2) L) (c : (L ⊗[K] AdeleRing (𝓞 K) K)ˣ)
    (hN₀ : ∃ z : Lˣ, δ₀ * Matrix.GeneralLinearGroup.map (σ : L →+* L) δ₀ =
      Matrix.GeneralLinearGroup.scalar (Fin 2) z)
    (hns : ∀ (x : GL (Fin 2) L) (z : Lˣ),
      x⁻¹ * δ₀ * Matrix.GeneralLinearGroup.map (σ : L →+* L) x ≠
        Matrix.GeneralLinearGroup.scalar (Fin 2) z)
    (v : Fin 2 → L) (hv : v ≠ 0)
    [MeasurableSpace (AdeleRing (𝓞 L) L)] [BorelSpace (AdeleRing (𝓞 L) L)]
    (μ₁ : Measure (AdeleRing (𝓞 L) L)) [μ₁.IsAddHaarMeasure] (hμ₁ : μ₁ (adelicBox L) = 1)
    {ψ : AddChar (AdeleRing (𝓞 L) L) ℂ} (hψ : IsGlobalAddChar L ψ)
    {Φ : (Fin 2 → AdeleRing (𝓞 L) L) → ℂ} (hΦ : Φ ∈ schwartzBruhat2 L)
    (hΦnn : ∀ x, 0 ≤ (Φ x).re)
    (τ' : Measure (Tw K L σ δ₀ c)) [τ'.IsHaarMeasure] [τ'.IsMulRightInvariant]
    (R' : ENNReal) (hR' : R' ≠ ⊤)
    (D₀ : Set (Tw K L σ δ₀ c)) (hD₀m : MeasurableSet D₀)
    (hD₀ : IsFundamentalDomain (ΓTw K L σ δ₀ c).op D₀ τ')
    (hrate : ∀ a b : ℝ, 0 < a → a ≤ b →
      τ' (D₀ ∩ {t | normDet K L σ δ₀ c t ∈ Set.Icc a b}) = R' * ENNReal.ofReal (Real.log (b / a)))
    (s : ℝ) (hs : 1 < s) :
    ∫⁻ t in {t | normDet K L σ δ₀ c t ≤ 1},
        ENNReal.ofReal (Φ (colv K L σ δ₀ c v t)).re * ENNReal.ofReal (normDet K L σ δ₀ c t ^ s) ∂τ' +
        ENNReal.ofReal (Φ 0).re * R' * ENNReal.ofReal (1 / s) +
      ∫⁻ t in {t | 1 ≤ normDet K L σ δ₀ c t},
        ENNReal.ofReal (-(reflectPair ψ μ₁ Φ (colv K L σ δ₀ c v t)).re) *
          ENNReal.ofReal (normDet K L σ δ₀ c t ^ (1 - s)) ∂τ' =
    ∫⁻ t in {t | 1 ≤ normDet K L σ δ₀ c t},
        ENNReal.ofReal (reflectPair ψ μ₁ Φ (colv K L σ δ₀ c v t)).re *
          ENNReal.ofReal (normDet K L σ δ₀ c t ^ (1 - s)) ∂τ' +
      (∫⁻ x, ENNReal.ofReal (Φ x).re ∂(pairHaar μ₁)) * R' * ENNReal.ofReal (1 / (s - 1)) := by

  haveI := isTopologicalRing_tensor K L (AdeleRing (𝓞 K) K)
  haveI := t2Space_tensor K L (AdeleRing (𝓞 K) K)
  haveI := locallyCompactSpace_tensor K L (AdeleRing (𝓞 K) K)
  haveI := isTopologicalGroup_tensorGL K L (AdeleRing (𝓞 K) K)
  haveI := t2Space_GL (L ⊗[K] AdeleRing (𝓞 K) K)
  haveI := locallyCompactSpace_GL (L ⊗[K] AdeleRing (𝓞 K) K)
  haveI : SecondCountableTopology (GL (Fin 2) (L ⊗[K] AdeleRing (𝓞 K) K)) := by
    haveI := NumberField.AdeleRing.secondCountableTopology_generalLinearGroup_finTwo L
    exact (baseChangeGLEquiv K L).toHomeomorph.secondCountableTopology
  haveI : BorelSpace (Tw K L σ δ₀ c) := ⟨rfl⟩
  have hclosed := isClosed_twistedCentralizer K L (AdeleRing (𝓞 K) K) σ (δA K L δ₀ c)
  haveI : LocallyCompactSpace (Tw K L σ δ₀ c) := hclosed.isClosedEmbedding_subtypeVal.locallyCompactSpace
  haveI : SecondCountableTopology (Tw K L σ δ₀ c) := Topology.IsInducing.subtypeVal.secondCountableTopology
  haveI : SigmaFinite τ' := Measure.IsHaarMeasure.sigmaFinite τ'

  have hιτ : Measure.map (iotaT K L σ δ₀ c) τ' = τ' :=
    MeasureTheory.Measure.map_eq_self_of_involutive_of_isHaarMeasure τ' (iotaT K L σ δ₀ c)
      (continuous_iotaT K L σ δ₀ c) (iotaT_iotaT K L σ δ₀ c)
  have hpres : MeasurePreserving (iotaT K L σ δ₀ c) τ' τ' := ⟨measurable_iotaT K L σ δ₀ c, hιτ⟩
  have hDι := isFundamentalDomain_preimage_iotaT K L σ δ₀ c τ' hpres hD₀

  have hΦc : Continuous Φ :=
    (NumberField.AdelicFourier.continuous_integrable_comp_vecMul_mem_and_bottomRowVec_mem_schwartzBruhat_of_mem_schwartzBruhat2
      L Φ hΦ).1
  have hΦ'mem : reflectPair ψ μ₁ Φ ∈ schwartzBruhat2 L :=
    (NumberField.AdelicFourier.fourierTransform2_mem_schwartzBruhat2_and_reflectPair_mem_schwartzBruhat2 L μ₁ hψ hΦ).2
  have hΦ'c : Continuous (reflectPair ψ μ₁ Φ) :=
    (NumberField.AdelicFourier.continuous_integrable_comp_vecMul_mem_and_bottomRowVec_mem_schwartzBruhat_of_mem_schwartzBruhat2
      L _ hΦ'mem).1
  have hcol := continuous_colv K L σ δ₀ c v
  have ma : Measurable fun t : Tw K L σ δ₀ c => ENNReal.ofReal (Φ (colv K L σ δ₀ c v t)).re :=
    (ENNReal.continuous_ofReal.comp (Complex.continuous_re.comp (hΦc.comp hcol))).measurable
  have mp : Measurable fun t : Tw K L σ δ₀ c => ENNReal.ofReal (reflectPair ψ μ₁ Φ (colv K L σ δ₀ c v t)).re :=
    (ENNReal.continuous_ofReal.comp (Complex.continuous_re.comp (hΦ'c.comp hcol))).measurable
  have mm : Measurable fun t : Tw K L σ δ₀ c => ENNReal.ofReal (-(reflectPair ψ μ₁ Φ (colv K L σ δ₀ c v t)).re) :=
    (ENNReal.continuous_ofReal.comp (Complex.continuous_re.comp (hΦ'c.comp hcol)).neg).measurable

  obtain ⟨hΦ'0, hΦ'0eq⟩ := ofReal_re_reflectPair_zero L μ₁ ψ hΦ hΦnn
  rw [← hΦ'0eq]

  exact zeta_decomposition τ' (ΓTw K L σ δ₀ c) D₀ hD₀m hD₀ (iotaT K L σ δ₀ c) (measurable_iotaT K L σ δ₀ c)
    (iotaT_iotaT K L σ δ₀ c) hιτ hDι (normDet K L σ δ₀ c) (measurable_normDet K L σ δ₀ c)
    (normDet_pos K L σ δ₀ c) (normDet_mul_coe K L σ δ₀ c) (normDet_iotaT K L σ δ₀ c) R' hR' hrate
    _ _ _ ma mp mm (ENNReal.ofReal (Φ 0).re) (ENNReal.ofReal (reflectPair ψ μ₁ Φ 0).re)
    (theta_identity K L σ δ₀ c h2 hgen hN₀ hns v hv μ₁ hμ₁ hψ hΦ hΦnn hΦ'0) s hs

end Assembly

end AutomorphicForm.QuatZeta
p2m_reactivate "P2MW.S_AutomorphicForm_setLIntegral_mul_ideleNorm_det_rpow_add_eq_setLIntegral_reflectPair_add_lintegral_mul_rate_of_isFundamentalDomain_twistedCentralizer_of_forall_ne_scalar_of_finrank_eq_two.AutomorphicForm P2MW.S_AutomorphicForm_setLIntegral_mul_ideleNorm_det_rpow_add_eq_setLIntegral_reflectPair_add_lintegral_mul_rate_of_isFundamentalDomain_twistedCentralizer_of_forall_ne_scalar_of_finrank_eq_two.AutomorphicForm.QuatZeta"
p2m_reactivate "P2MW.S_AutomorphicForm_setLIntegral_mul_ideleNorm_det_rpow_add_eq_setLIntegral_reflectPair_add_lintegral_mul_rate_of_isFundamentalDomain_twistedCentralizer_of_forall_ne_scalar_of_finrank_eq_two.AutomorphicForm"

end
p2m_reactivate "P2MW.S_AutomorphicForm_setLIntegral_mul_ideleNorm_det_rpow_add_eq_setLIntegral_reflectPair_add_lintegral_mul_rate_of_isFundamentalDomain_twistedCentralizer_of_forall_ne_scalar_of_finrank_eq_two.AutomorphicForm P2MW.S_AutomorphicForm_setLIntegral_mul_ideleNorm_det_rpow_add_eq_setLIntegral_reflectPair_add_lintegral_mul_rate_of_isFundamentalDomain_twistedCentralizer_of_forall_ne_scalar_of_finrank_eq_two.AutomorphicForm.QuatZeta"

p2m_open "MeasureTheory Filter NumberField NumberField.AdelicHaar NumberField.AdelicFourier NumberField.AdelicBox NumberField.TateGlobal IsDedekindDomain AutomorphicForm P2MW.S_AutomorphicForm_setLIntegral_mul_ideleNorm_det_rpow_add_eq_setLIntegral_reflectPair_add_lintegral_mul_rate_of_isFundamentalDomain_twistedCentralizer_of_forall_ne_scalar_of_finrank_eq_two.AutomorphicForm"

open scoped TensorProduct TensorProduct.RightActions Topology ENNReal

attribute [local instance] NumberField.AdelicHaar.glBorel AutomorphicForm.centralizerBorel
  AutomorphicForm.twistedCentralizerBorel

theorem solution
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (h2 : Module.finrank K L = 2) (σ : L ≃ₐ[K] L) (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ)
    (δ₀ : GL (Fin 2) L) (c : (L ⊗[K] AdeleRing (𝓞 K) K)ˣ)
    (hN₀ : ∃ z : Lˣ, δ₀ * Matrix.GeneralLinearGroup.map (σ : L →+* L) δ₀ =
      Matrix.GeneralLinearGroup.scalar (Fin 2) z)
    (hns : ∀ (x : GL (Fin 2) L) (z : Lˣ),
      x⁻¹ * δ₀ * Matrix.GeneralLinearGroup.map (σ : L →+* L) x ≠
        Matrix.GeneralLinearGroup.scalar (Fin 2) z)
    (v : Fin 2 → L) (hv : v ≠ 0)
    [MeasurableSpace (AdeleRing (𝓞 L) L)] [BorelSpace (AdeleRing (𝓞 L) L)]
    (μ₁ : Measure (AdeleRing (𝓞 L) L)) [μ₁.IsAddHaarMeasure] (hμ₁ : μ₁ (adelicBox L) = 1)
    {ψ : AddChar (AdeleRing (𝓞 L) L) ℂ} (hψ : IsGlobalAddChar L ψ)
    {Φ : (Fin 2 → AdeleRing (𝓞 L) L) → ℂ} (hΦ : Φ ∈ schwartzBruhat2 L)
    (hΦnn : ∀ x, 0 ≤ (Φ x).re)
    (τ' : Measure (AutomorphicForm.twistedCentralizer K L (AdeleRing (𝓞 K) K) σ (Matrix.GeneralLinearGroup.map
            (Algebra.TensorProduct.includeLeftRingHom : L →+* L ⊗[K] AdeleRing (𝓞 K) K) δ₀ *
          Matrix.GeneralLinearGroup.scalar (Fin 2) c)))
    (hτ' : τ'.IsHaarMeasure) (hτ'r : τ'.IsMulRightInvariant)
    (R' : ENNReal) (hR' : R' ≠ ⊤)
    (hD' : ∀ D' : Set (AutomorphicForm.twistedCentralizer K L (AdeleRing (𝓞 K) K) σ (Matrix.GeneralLinearGroup.map
            (Algebra.TensorProduct.includeLeftRingHom : L →+* L ⊗[K] AdeleRing (𝓞 K) K) δ₀ *
          Matrix.GeneralLinearGroup.scalar (Fin 2) c)),
      IsFundamentalDomain
        (((AutomorphicForm.sigmaCentralizer
            (Matrix.GeneralLinearGroup.map (σ : L →+* L)) δ₀).map
            (Matrix.GeneralLinearGroup.map
              (Algebra.TensorProduct.includeLeftRingHom : L →+* L ⊗[K] AdeleRing (𝓞 K) K))).subgroupOf
          (AutomorphicForm.twistedCentralizer K L (AdeleRing (𝓞 K) K) σ (Matrix.GeneralLinearGroup.map
            (Algebra.TensorProduct.includeLeftRingHom : L →+* L ⊗[K] AdeleRing (𝓞 K) K) δ₀ *
          Matrix.GeneralLinearGroup.scalar (Fin 2) c))).op D' τ' →
      ∀ a b : ℝ, 0 < a → a ≤ b →
        τ' (D' ∩ {t | NumberField.TateGlobal.ideleNorm L
          (Matrix.GeneralLinearGroup.det
            (Matrix.GeneralLinearGroup.map
              (((Algebra.TensorProduct.comm K L (AdeleRing (𝓞 K) K)).toRingEquiv.trans
                (M4aHerbrand.Bridge.genuineRingEquiv K L)).toRingHom)
              (t : GL (Fin 2) (L ⊗[K] AdeleRing (𝓞 K) K)))) ∈ Set.Icc a b}) =
          R' * ENNReal.ofReal (Real.log (b / a)))
    (D₀ : Set (AutomorphicForm.twistedCentralizer K L (AdeleRing (𝓞 K) K) σ (Matrix.GeneralLinearGroup.map
            (Algebra.TensorProduct.includeLeftRingHom : L →+* L ⊗[K] AdeleRing (𝓞 K) K) δ₀ *
          Matrix.GeneralLinearGroup.scalar (Fin 2) c)))
    (hD₀m : MeasurableSet D₀)
    (hD₀ : IsFundamentalDomain
        (((AutomorphicForm.sigmaCentralizer
            (Matrix.GeneralLinearGroup.map (σ : L →+* L)) δ₀).map
            (Matrix.GeneralLinearGroup.map
              (Algebra.TensorProduct.includeLeftRingHom : L →+* L ⊗[K] AdeleRing (𝓞 K) K))).subgroupOf
          (AutomorphicForm.twistedCentralizer K L (AdeleRing (𝓞 K) K) σ (Matrix.GeneralLinearGroup.map
            (Algebra.TensorProduct.includeLeftRingHom : L →+* L ⊗[K] AdeleRing (𝓞 K) K) δ₀ *
          Matrix.GeneralLinearGroup.scalar (Fin 2) c))).op D₀ τ')
    (s : ℝ) (hs : 1 < s) :
    ∫⁻ t in {t | NumberField.TateGlobal.ideleNorm L
          (Matrix.GeneralLinearGroup.det
            (Matrix.GeneralLinearGroup.map
              (((Algebra.TensorProduct.comm K L (AdeleRing (𝓞 K) K)).toRingEquiv.trans
                (M4aHerbrand.Bridge.genuineRingEquiv K L)).toRingHom)
              (t : GL (Fin 2) (L ⊗[K] AdeleRing (𝓞 K) K)))) ≤ 1},
        ENNReal.ofReal (Φ ((Matrix.GeneralLinearGroup.map
              (((Algebra.TensorProduct.comm K L (AdeleRing (𝓞 K) K)).toRingEquiv.trans
                (M4aHerbrand.Bridge.genuineRingEquiv K L)).toRingHom)
              (t : GL (Fin 2) (L ⊗[K] AdeleRing (𝓞 K) K)) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 L) L)).mulVec
            fun i => algebraMap L (AdeleRing (𝓞 L) L) (v i))).re *
          ENNReal.ofReal (NumberField.TateGlobal.ideleNorm L
            (Matrix.GeneralLinearGroup.det
              (Matrix.GeneralLinearGroup.map
                (((Algebra.TensorProduct.comm K L (AdeleRing (𝓞 K) K)).toRingEquiv.trans
                  (M4aHerbrand.Bridge.genuineRingEquiv K L)).toRingHom)
                (t : GL (Fin 2) (L ⊗[K] AdeleRing (𝓞 K) K)))) ^ s) ∂τ' +
        ENNReal.ofReal (Φ 0).re * R' * ENNReal.ofReal (1 / s) +
      ∫⁻ t in {t | 1 ≤ NumberField.TateGlobal.ideleNorm L
          (Matrix.GeneralLinearGroup.det
            (Matrix.GeneralLinearGroup.map
              (((Algebra.TensorProduct.comm K L (AdeleRing (𝓞 K) K)).toRingEquiv.trans
                (M4aHerbrand.Bridge.genuineRingEquiv K L)).toRingHom)
              (t : GL (Fin 2) (L ⊗[K] AdeleRing (𝓞 K) K))))},
        ENNReal.ofReal (-(reflectPair ψ μ₁ Φ ((Matrix.GeneralLinearGroup.map
              (((Algebra.TensorProduct.comm K L (AdeleRing (𝓞 K) K)).toRingEquiv.trans
                (M4aHerbrand.Bridge.genuineRingEquiv K L)).toRingHom)
              (t : GL (Fin 2) (L ⊗[K] AdeleRing (𝓞 K) K)) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 L) L)).mulVec
            fun i => algebraMap L (AdeleRing (𝓞 L) L) (v i))).re) *
          ENNReal.ofReal (NumberField.TateGlobal.ideleNorm L
            (Matrix.GeneralLinearGroup.det
              (Matrix.GeneralLinearGroup.map
                (((Algebra.TensorProduct.comm K L (AdeleRing (𝓞 K) K)).toRingEquiv.trans
                  (M4aHerbrand.Bridge.genuineRingEquiv K L)).toRingHom)
                (t : GL (Fin 2) (L ⊗[K] AdeleRing (𝓞 K) K)))) ^ (1 - s)) ∂τ' =
    ∫⁻ t in {t | 1 ≤ NumberField.TateGlobal.ideleNorm L
          (Matrix.GeneralLinearGroup.det
            (Matrix.GeneralLinearGroup.map
              (((Algebra.TensorProduct.comm K L (AdeleRing (𝓞 K) K)).toRingEquiv.trans
                (M4aHerbrand.Bridge.genuineRingEquiv K L)).toRingHom)
              (t : GL (Fin 2) (L ⊗[K] AdeleRing (𝓞 K) K))))},
        ENNReal.ofReal (reflectPair ψ μ₁ Φ ((Matrix.GeneralLinearGroup.map
              (((Algebra.TensorProduct.comm K L (AdeleRing (𝓞 K) K)).toRingEquiv.trans
                (M4aHerbrand.Bridge.genuineRingEquiv K L)).toRingHom)
              (t : GL (Fin 2) (L ⊗[K] AdeleRing (𝓞 K) K)) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 L) L)).mulVec
            fun i => algebraMap L (AdeleRing (𝓞 L) L) (v i))).re *
          ENNReal.ofReal (NumberField.TateGlobal.ideleNorm L
            (Matrix.GeneralLinearGroup.det
              (Matrix.GeneralLinearGroup.map
                (((Algebra.TensorProduct.comm K L (AdeleRing (𝓞 K) K)).toRingEquiv.trans
                  (M4aHerbrand.Bridge.genuineRingEquiv K L)).toRingHom)
                (t : GL (Fin 2) (L ⊗[K] AdeleRing (𝓞 K) K)))) ^ (1 - s)) ∂τ' +
      (∫⁻ x, ENNReal.ofReal (Φ x).re ∂(pairHaar μ₁)) * R' * ENNReal.ofReal (1 / (s - 1)) := by
  haveI := hτ'
  haveI := hτ'r
  exact AutomorphicForm.QuatZeta.main K L h2 σ hgen δ₀ c hN₀ hns v hv μ₁ hμ₁ hψ hΦ hΦnn τ' R' hR' D₀ hD₀m hD₀
    (hD' D₀ hD₀) s hs

end S_AutomorphicForm_setLIntegral_mul_ideleNorm_det_rpow_add_eq_setLIntegral_reflectPair_add_lintegral_mul_rate_of_isFundamentalDomain_twistedCentralizer_of_forall_ne_scalar_of_finrank_eq_two
end P2MW
export P2MW.S_AutomorphicForm_setLIntegral_mul_ideleNorm_det_rpow_add_eq_setLIntegral_reflectPair_add_lintegral_mul_rate_of_isFundamentalDomain_twistedCentralizer_of_forall_ne_scalar_of_finrank_eq_two (solution)
