-- Prove2me | solution 1 for AutomorphicForm.integrable_and_differentiableAt_and_continuous_godementSection_of_mem_schwartzBruhat2
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.340288+00:00
-- url     : https://prove2.me/submissions/63a54fb9-58d4-5995-99cd-868ec59c9745

import Definitions.Def_AutomorphicForm_GodementSection
import Theorems.Thm_NumberField_TateGlobal_integrable_zetaIntegrand
import Theorems.Thm_NumberField_TateGlobal_continuous_ideleNorm
import Theorems.Thm_NumberField_TateGlobal_continuous_ideleNorm_det
import Theorems.Thm_NumberField_AdeleRing_secondCountableTopology
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_integrable_and_differentiableAt_and_continuous_godementSection_of_mem_schwartzBruhat2
p2m_attr_erase "instance" "instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions instCountableOfNumberField_definitions RestrictedProduct.SecondCountableTopology_of_principal instCountableElemSetSetsCofinite_definitions"
p2m_attr_erase "simp" "LanglandsTunnell.TateLocal.charExt_coe_units LanglandsTunnell.TateLocal.modulus_one LanglandsTunnell.TateLocal.modulus_zero LanglandsTunnell.TateLocal.modulus_coe_units LanglandsTunnell.TateLocal.charExt_zero ContinuousAddEquiv.restrictedProductPi_apply RestrictedProduct.flatten_homeomorph_apply RestrictedProduct.flatten_homeomorph'_symm_apply ContinuousMulEquiv.restrictedProductPi_symm_apply RestrictedProduct.flatten_homeomorph'_apply RestrictedProduct.flatten_homeomorph_symm_apply ContinuousMulEquiv.restrictedProductPi_apply ContinuousAddEquiv.restrictedProductPi_symm_apply RingEquiv.restrictedProductCongr_symm_apply RingEquiv.restrictedProductCongrRight_apply MulEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductProd_symm_apply_coe Equiv.restrictedProductCongrRight_apply AddEquiv.restrictedProductCongr_apply Equiv.restrictedProductCongrLeft'_symm_apply_apply Equiv.restrictedProductCongr_apply_apply Equiv.restrictedProductCongrLeft_apply_apply RestrictedProduct.flatten_equiv'_apply AddEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductCongr_symm_apply Equiv.restrictedProductCongrRight_symm_apply RestrictedProduct.flatten_equiv'_symm_apply AddEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductCongrLeft'_apply RestrictedProduct.flatten_apply RingEquiv.restrictedProductCongr_apply_apply RingEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductProd_apply RestrictedProduct.flatten_equiv_apply RestrictedProduct.flatten_equiv_symm_apply LinearEquiv.restrictedProductCongrLeft'_apply RestrictedProduct.not_mem_support RestrictedProduct.mem_structureSubring_iff RestrictedProduct.not_mem_mulSupport RestrictedProduct.support_neg"
p2m_attr_erase "simp" "RestrictedProduct.mem_indexSupport_iff RestrictedProduct.mulSupport_inv RestrictedProduct.mapAlongLinearMap_apply"

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

open MeasureTheory Filter Topology NumberField NumberField.AdelicFourier NumberField.TateGlobal
p2m_open "AutomorphicForm P2MW.S_AutomorphicForm_integrable_and_differentiableAt_and_continuous_godementSection_of_mem_schwartzBruhat2.AutomorphicForm IsDedekindDomain"
open scoped SchwartzMap ENNReal

noncomputable section

namespace AutomorphicForm
p2m_export "AutomorphicForm" "bottomRowVec godementSection AdelicGL2 IsUnitaryChar"
namespace GodementK0b
p2m_open "AutomorphicForm"

theorem rpow_le_rpow_add_rpow {x lo e hi : ℝ} (hx : 0 < x) (hlo : lo ≤ e) (hhi : e ≤ hi) :
    x ^ e ≤ x ^ lo + x ^ hi := by
  rcases le_or_gt 1 x with h1 | h1
  · have : x ^ e ≤ x ^ hi := Real.rpow_le_rpow_of_exponent_le h1 hhi
    linarith [Real.rpow_nonneg hx.le lo]
  · have : x ^ e ≤ x ^ lo := Real.rpow_le_rpow_of_exponent_ge hx h1.le hlo
    linarith [Real.rpow_nonneg hx.le hi]

theorem abs_log_le_rpow_add_rpow_div {x δ : ℝ} (hx : 0 < x) (hδ : 0 < δ) :
    |Real.log x| ≤ (x ^ δ + x ^ (-δ)) / δ := by
  have h1 : Real.log x ≤ x ^ δ / δ := by
    have h := Real.log_le_sub_one_of_pos (Real.rpow_pos_of_pos hx δ)
    rw [Real.log_rpow hx] at h
    rw [le_div_iff₀ hδ]
    linarith
  have h2 : -Real.log x ≤ x ^ (-δ) / δ := by
    have h := Real.log_le_sub_one_of_pos (Real.rpow_pos_of_pos hx (-δ))
    rw [Real.log_rpow hx] at h
    rw [le_div_iff₀ hδ]
    linarith
  rw [abs_le]
  constructor
  · rw [add_div]
    linarith [div_nonneg (Real.rpow_nonneg hx.le δ) hδ.le]
  · rw [add_div]
    linarith [div_nonneg (Real.rpow_nonneg hx.le (-δ)) hδ.le]

section Mellin

variable {X : Type*} [MeasurableSpace X] (m : Measure X)
variable {P : Type*} [TopologicalSpace P]

theorem norm_mul_cpow_ofReal {N : X → ℝ} (hNpos : ∀ x, 0 < N x) (h : X → ℂ) (w : ℂ) (x : X) :
    ‖h x * ((N x : ℝ) : ℂ) ^ w‖ = ‖h x‖ * N x ^ w.re := by
  rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos (hNpos x)]

theorem measurable_cpow_ofReal {N : X → ℝ} (hN : Measurable N) (w : ℂ) :
    Measurable fun x => ((N x : ℝ) : ℂ) ^ w :=
  (Complex.measurable_ofReal.comp hN).pow_const w

theorem aestronglyMeasurable_mul_cpow {N : X → ℝ} (hN : Measurable N) {h : X → ℂ}
    (hh : AEStronglyMeasurable h m) (w : ℂ) :
    AEStronglyMeasurable (fun x => h x * ((N x : ℝ) : ℂ) ^ w) m :=
  hh.mul (measurable_cpow_ofReal hN w).aestronglyMeasurable

theorem integrable_mul_cpow_of_dom {N : X → ℝ} (hN : Measurable N) (hNpos : ∀ x, 0 < N x)
    {h : X → ℂ} (hh : AEStronglyMeasurable h m) {a b : ℝ} {bound : X → ℝ}
    (hbound : Integrable bound m) (hdom : ∀ x, ‖h x‖ * (N x ^ a + N x ^ b) ≤ bound x)
    {w : ℂ} (haw : a ≤ w.re) (hwb : w.re ≤ b) :
    Integrable (fun x => h x * ((N x : ℝ) : ℂ) ^ w) m := by
  refine hbound.mono' (aestronglyMeasurable_mul_cpow m hN hh w) (Eventually.of_forall fun x => ?_)
  rw [norm_mul_cpow_ofReal hNpos]
  refine le_trans ?_ (hdom x)
  exact mul_le_mul_of_nonneg_left (rpow_le_rpow_add_rpow (hNpos x) haw hwb) (norm_nonneg _)

theorem differentiableAt_integral_mul_cpow {N : X → ℝ} (hN : Measurable N) (hNpos : ∀ x, 0 < N x)
    {h : X → ℂ} (hh : AEStronglyMeasurable h m) (c : ℝ)
    (hdom : ∀ a b : ℝ, c < a → a ≤ b → ∃ bound : X → ℝ, Integrable bound m ∧
      ∀ x, ‖h x‖ * (N x ^ a + N x ^ b) ≤ bound x)
    {w₀ : ℂ} (hw₀ : c < w₀.re) :
    DifferentiableAt ℂ (fun w : ℂ => ∫ x, h x * ((N x : ℝ) : ℂ) ^ w ∂m) w₀ := by
  set ε : ℝ := (w₀.re - c) / 4 with hε
  have hεpos : 0 < ε := by rw [hε]; linarith
  set lo : ℝ := w₀.re - 2 * ε with hlo
  set hi : ℝ := w₀.re + 2 * ε with hhi
  have hclo : c < lo := by rw [hlo, hε]; linarith
  have hlohi : lo ≤ hi := by rw [hlo, hhi]; linarith
  obtain ⟨bound, hbound, hdomb⟩ := hdom lo hi hclo hlohi
  set F' : ℂ → X → ℂ := fun w x => h x * (((N x : ℝ) : ℂ) ^ w * Complex.log ((N x : ℝ) : ℂ)) with hF'
  have hderiv : ∀ x, ∀ w : ℂ, HasDerivAt (fun w => h x * ((N x : ℝ) : ℂ) ^ w) (F' w x) w := by
    intro x w
    have hne : ((N x : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (hNpos x).ne'
    have h1 : HasDerivAt (fun w : ℂ => ((N x : ℝ) : ℂ) ^ w)
        (((N x : ℝ) : ℂ) ^ w * Complex.log ((N x : ℝ) : ℂ) * 1) w :=
      (hasDerivAt_id w).const_cpow (Or.inl hne)
    rw [mul_one] at h1
    exact h1.const_mul (h x)
  have hlog : ∀ x, ‖Complex.log ((N x : ℝ) : ℂ)‖ = |Real.log (N x)| := by
    intro x
    rw [← Complex.ofReal_log (hNpos x).le, Complex.norm_real, Real.norm_eq_abs]
  have hF'bound : ∀ x, ∀ w ∈ Metric.ball w₀ ε, ‖F' w x‖ ≤ (4 / ε) * bound x := by
    intro x w hw
    have hNx := hNpos x
    have hre : |w.re - w₀.re| < ε := by
      have h1 : |w.re - w₀.re| ≤ ‖w - w₀‖ := by
        simpa [Complex.sub_re] using Complex.abs_re_le_norm (w - w₀)
      exact lt_of_le_of_lt h1 (mem_ball_iff_norm.mp hw)
    rw [abs_lt] at hre
    have hnorm : ‖F' w x‖ = ‖h x‖ * (N x ^ w.re * |Real.log (N x)|) := by
      rw [hF']
      simp only
      rw [norm_mul, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hNx, hlog]
    rw [hnorm]
    have hl := abs_log_le_rpow_add_rpow_div hNx hεpos
    have hpow : N x ^ w.re * |Real.log (N x)| ≤ (N x ^ (w.re + ε) + N x ^ (w.re - ε)) / ε := by
      calc N x ^ w.re * |Real.log (N x)|
          ≤ N x ^ w.re * ((N x ^ ε + N x ^ (-ε)) / ε) :=
            mul_le_mul_of_nonneg_left hl (Real.rpow_nonneg hNx.le _)
        _ = (N x ^ (w.re + ε) + N x ^ (w.re - ε)) / ε := by
            rw [Real.rpow_add hNx, Real.rpow_sub hNx, Real.rpow_neg hNx.le]
            field_simp
    have h2 : N x ^ (w.re + ε) ≤ N x ^ lo + N x ^ hi :=
      rpow_le_rpow_add_rpow hNx (by rw [hlo]; linarith) (by rw [hhi]; linarith)
    have h3 : N x ^ (w.re - ε) ≤ N x ^ lo + N x ^ hi :=
      rpow_le_rpow_add_rpow hNx (by rw [hlo]; linarith) (by rw [hhi]; linarith)
    have h4 : N x ^ w.re * |Real.log (N x)| ≤ (2 / ε) * (N x ^ lo + N x ^ hi) := by
      refine hpow.trans ?_
      rw [div_le_iff₀ hεpos]
      have : (2 / ε) * (N x ^ lo + N x ^ hi) * ε = 2 * (N x ^ lo + N x ^ hi) := by
        field_simp
      rw [this]
      linarith
    calc ‖h x‖ * (N x ^ w.re * |Real.log (N x)|)
        ≤ ‖h x‖ * ((2 / ε) * (N x ^ lo + N x ^ hi)) :=
          mul_le_mul_of_nonneg_left h4 (norm_nonneg _)
      _ = (2 / ε) * (‖h x‖ * (N x ^ lo + N x ^ hi)) := by ring
      _ ≤ (2 / ε) * bound x :=
          mul_le_mul_of_nonneg_left (hdomb x) (div_nonneg (by norm_num) hεpos.le)
      _ ≤ (4 / ε) * bound x := by
          have hb0 : 0 ≤ bound x := le_trans (by positivity) (hdomb x)
          have : (2 / ε) ≤ 4 / ε := div_le_div_of_nonneg_right (by norm_num) hεpos.le
          exact mul_le_mul_of_nonneg_right this hb0
  have hlogm : Measurable fun x => Complex.log ((N x : ℝ) : ℂ) :=
    Complex.measurable_log.comp (Complex.measurable_ofReal.comp hN)
  have hF'meas : ∀ w, AEStronglyMeasurable (F' w) m := fun w =>
    hh.mul (((measurable_cpow_ofReal hN w).mul hlogm).aestronglyMeasurable)
  have hint : Integrable (fun x => h x * ((N x : ℝ) : ℂ) ^ w₀) m :=
    integrable_mul_cpow_of_dom m hN hNpos hh hbound hdomb (by rw [hlo]; linarith) (by rw [hhi]; linarith)
  have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := m) (F' := F') (x₀ := w₀)
    (bound := fun x => (4 / ε) * bound x) (Metric.ball_mem_nhds w₀ hεpos)
    (Eventually.of_forall fun w => aestronglyMeasurable_mul_cpow m hN hh w) hint (hF'meas w₀)
    (Eventually.of_forall fun x => hF'bound x) (hbound.const_mul _)
    (Eventually.of_forall fun x w _ => hderiv x w)
  exact key.2.differentiableAt

theorem continuousOn_integral_mul_cpow [FirstCountableTopology P] {N : X → ℝ} (hN : Measurable N)
    (hNpos : ∀ x, 0 < N x) (h : P → X → ℂ) (hh : ∀ p, AEStronglyMeasurable (h p) m)
    (hcont : ∀ x, Continuous fun p => h p x) (c : ℝ)
    (hdom : ∀ (p₀ : P) (a b : ℝ), c < a → a ≤ b → ∃ bound : X → ℝ, Integrable bound m ∧
      ∀ᶠ p in 𝓝 p₀, ∀ x, ‖h p x‖ * (N x ^ a + N x ^ b) ≤ bound x) :
    ContinuousOn (fun q : ℂ × P => ∫ x, h q.2 x * ((N x : ℝ) : ℂ) ^ q.1 ∂m) {q | c < q.1.re} := by
  intro q₀ hq₀
  apply ContinuousAt.continuousWithinAt
  have hq₀' : c < q₀.1.re := hq₀
  set ε : ℝ := (q₀.1.re - c) / 2 with hε
  have hεpos : 0 < ε := by rw [hε]; linarith
  set lo : ℝ := q₀.1.re - ε with hlo
  set hi : ℝ := q₀.1.re + ε with hhi
  have hclo : c < lo := by rw [hlo, hε]; linarith
  obtain ⟨bound, hbound, hdomb⟩ := hdom q₀.2 lo hi hclo (by rw [hlo, hhi]; linarith)
  have hev1 : ∀ᶠ w in 𝓝 q₀.1, lo < w.re ∧ w.re < hi := by
    have hc : ContinuousAt (fun w : ℂ => w.re) q₀.1 := Complex.continuous_re.continuousAt
    have h1 : ∀ᶠ w in 𝓝 q₀.1, lo < w.re :=
      hc.eventually (Ioi_mem_nhds (by rw [hlo]; linarith))
    have h2 : ∀ᶠ w in 𝓝 q₀.1, w.re < hi :=
      hc.eventually (Iio_mem_nhds (by rw [hhi]; linarith))
    exact h1.and h2
  have hev : ∀ᶠ q in 𝓝 q₀, (lo < q.1.re ∧ q.1.re < hi) ∧
      ∀ x, ‖h q.2 x‖ * (N x ^ lo + N x ^ hi) ≤ bound x := by
    have := hev1.prod_mk hdomb
    rw [← nhds_prod_eq] at this
    exact this
  refine continuousAt_of_dominated (bound := bound) ?_ ?_ hbound ?_
  · exact Eventually.of_forall fun q => aestronglyMeasurable_mul_cpow m hN (hh q.2) q.1
  · refine hev.mono fun q hq => Eventually.of_forall fun x => ?_
    rw [norm_mul_cpow_ofReal hNpos]
    refine le_trans ?_ (hq.2 x)
    exact mul_le_mul_of_nonneg_left (rpow_le_rpow_add_rpow (hNpos x) hq.1.1.le hq.1.2.le)
      (norm_nonneg _)
  · refine Eventually.of_forall fun x => ?_
    have hne : ((N x : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (hNpos x).ne'
    have h1 : ContinuousAt (fun q : ℂ × P => h q.2 x) q₀ :=
      ((hcont x).comp continuous_snd).continuousAt
    have h2 : ContinuousAt (fun q : ℂ × P => ((N x : ℝ) : ℂ) ^ q.1) q₀ :=
      (continuousAt_const_cpow hne).comp continuous_fst.continuousAt
    exact h1.mul h2

end Mellin

section Adelic

open scoped Classical

variable {F : Type} [Field F] [NumberField F]

theorem firstCountableTopology_units (M : Type*) [Monoid M] [TopologicalSpace M] [FirstCountableTopology M] :
    FirstCountableTopology Mˣ := by
  haveI : FirstCountableTopology Mᵐᵒᵖ :=
    (MulOpposite.opHomeomorph (M := M)).symm.isInducing.firstCountableTopology
  exact Units.isInducing_embedProduct.firstCountableTopology

theorem firstCountableTopology_adelicGL2 : FirstCountableTopology (AdelicGL2 (𝓞 F) F) := by
  haveI : SecondCountableTopology (AdeleRing (𝓞 F) F) := NumberField.AdeleRing.secondCountableTopology F
  haveI : FirstCountableTopology (Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) :=
    inferInstanceAs (FirstCountableTopology (Fin 2 → Fin 2 → AdeleRing (𝓞 F) F))
  exact firstCountableTopology_units _

theorem continuous_ringEquiv_mixedSpace :
    Continuous (InfiniteAdeleRing.ringEquiv_mixedSpace F) := by
  refine continuous_prodMk.2 ⟨continuous_pi fun v => ?_, continuous_pi fun v => ?_⟩
  · exact (InfinitePlace.Completion.isometry_extensionEmbeddingOfIsReal v.2).continuous.comp
      (continuous_apply _)
  · exact (InfinitePlace.Completion.isometry_extensionEmbedding v.1).continuous.comp
      (continuous_apply _)

variable (F) in

def archHom : AdeleRing (𝓞 F) F →+* mixedEmbedding.mixedSpace F :=
  (InfiniteAdeleRing.ringEquiv_mixedSpace F).toRingHom.comp
    (RingHom.fst (InfiniteAdeleRing F) (FiniteAdeleRing (𝓞 F) F))

theorem archHom_apply (x : AdeleRing (𝓞 F) F) :
    archHom F x = InfiniteAdeleRing.ringEquiv_mixedSpace F x.1 := rfl

theorem continuous_archHom : Continuous (archHom F) :=
  continuous_ringEquiv_mixedSpace.comp continuous_fst

variable (F) in

def finHom : AdeleRing (𝓞 F) F →+* FiniteAdeleRing (𝓞 F) F :=
  RingHom.snd (InfiniteAdeleRing F) (FiniteAdeleRing (𝓞 F) F)

theorem finHom_apply (x : AdeleRing (𝓞 F) F) : finHom F x = x.2 := rfl

def archRow (g : AdelicGL2 (𝓞 F) F) (a : mixedEmbedding.mixedSpace F) : Fin 2 → mixedEmbedding.mixedSpace F :=
  fun j => a * archHom F ((g : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) 1 j)

def finRow (g : AdelicGL2 (𝓞 F) F) (z : FiniteAdeleRing (𝓞 F) F) : Fin 2 → FiniteAdeleRing (𝓞 F) F :=
  fun j => z * ((g : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) 1 j).2

theorem adele_fst_mul (x y : AdeleRing (𝓞 F) F) : (x * y).1 = x.1 * y.1 := rfl

theorem adele_snd_mul (x y : AdeleRing (𝓞 F) F) : (x * y).2 = x.2 * y.2 := rfl

theorem archProj_bottomRowVec (g : AdelicGL2 (𝓞 F) F) (t : AdeleRing (𝓞 F) F) :
    (fun i => InfiniteAdeleRing.ringEquiv_mixedSpace F ((bottomRowVec F g t) i).1)
      = archRow g (archHom F t) := by
  funext i
  show InfiniteAdeleRing.ringEquiv_mixedSpace F
      (t * (g : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) 1 i).1 = _
  rw [adele_fst_mul, map_mul]
  rfl

theorem finProj_bottomRowVec (g : AdelicGL2 (𝓞 F) F) (t : AdeleRing (𝓞 F) F) :
    (fun i => ((bottomRowVec F g t) i).2) = finRow g t.2 := by
  funext i
  show (t * (g : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) 1 i).2 = _
  rw [adele_snd_mul]
  rfl

theorem archRow_recover (g : AdelicGL2 (𝓞 F) F) (a : mixedEmbedding.mixedSpace F) :
    a = archRow g a 0 * archHom F (((g⁻¹ : AdelicGL2 (𝓞 F) F) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) 0 1)
      + archRow g a 1 * archHom F (((g⁻¹ : AdelicGL2 (𝓞 F) F) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) 1 1) := by
  have hmul : ((g : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F))
      * ((g⁻¹ : AdelicGL2 (𝓞 F) F) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F))) 1 1 = 1 := by
    rw [Units.mul_inv, Matrix.one_apply_eq]
  rw [Matrix.mul_apply, Fin.sum_univ_two] at hmul
  have h2 := congrArg (archHom F) hmul
  rw [map_add, map_mul, map_mul, map_one] at h2
  simp only [archRow]
  calc a = a * 1 := (mul_one a).symm
    _ = a * (archHom F ((g : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) 1 0)
          * archHom F (((g⁻¹ : AdelicGL2 (𝓞 F) F) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) 0 1)
        + archHom F ((g : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) 1 1)
          * archHom F (((g⁻¹ : AdelicGL2 (𝓞 F) F) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) 1 1)) := by
          rw [h2]
    _ = _ := by ring

theorem finRow_recover (g : AdelicGL2 (𝓞 F) F) (z : FiniteAdeleRing (𝓞 F) F) :
    z = finRow g z 0 * (((g⁻¹ : AdelicGL2 (𝓞 F) F) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) 0 1).2
      + finRow g z 1 * (((g⁻¹ : AdelicGL2 (𝓞 F) F) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) 1 1).2 := by
  have hmul : ((g : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F))
      * ((g⁻¹ : AdelicGL2 (𝓞 F) F) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F))) 1 1 = 1 := by
    rw [Units.mul_inv, Matrix.one_apply_eq]
  rw [Matrix.mul_apply, Fin.sum_univ_two] at hmul
  have h2 := congrArg (finHom F) hmul
  rw [map_add, map_mul, map_mul, map_one] at h2
  simp only [finRow, finHom_apply] at h2 ⊢
  calc z = z * 1 := (mul_one z).symm
    _ = z * (((g : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) 1 0).2
          * (((g⁻¹ : AdelicGL2 (𝓞 F) F) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) 0 1).2
        + ((g : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) 1 1).2
          * (((g⁻¹ : AdelicGL2 (𝓞 F) F) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) 1 1).2) := by
          rw [h2]
    _ = _ := by ring

def colSize (g : AdelicGL2 (𝓞 F) F) : ℝ :=
  ‖archHom F (((g⁻¹ : AdelicGL2 (𝓞 F) F) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) 0 1)‖
    + ‖archHom F (((g⁻¹ : AdelicGL2 (𝓞 F) F) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) 1 1)‖

theorem colSize_nonneg (g : AdelicGL2 (𝓞 F) F) : 0 ≤ colSize g := by
  unfold colSize; positivity

theorem continuous_entry (i j : Fin 2) :
    Continuous fun g : AdelicGL2 (𝓞 F) F => (g : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) i j :=
  (Continuous.matrix_elem Units.continuous_val i j)

theorem continuous_colSize : Continuous (colSize (F := F)) := by
  unfold colSize
  refine Continuous.add ?_ ?_
  · exact (continuous_archHom.comp ((continuous_entry 0 1).comp continuous_inv)).norm
  · exact (continuous_archHom.comp ((continuous_entry 1 1).comp continuous_inv)).norm

theorem norm_le_colSize_mul_norm_archRow (g : AdelicGL2 (𝓞 F) F) (a : mixedEmbedding.mixedSpace F) :
    ‖a‖ ≤ colSize g * ‖archRow g a‖ := by
  have h := archRow_recover g a
  have h0 : ‖archRow g a 0‖ ≤ ‖archRow g a‖ := norm_le_pi_norm _ 0
  have h1 : ‖archRow g a 1‖ ≤ ‖archRow g a‖ := norm_le_pi_norm _ 1
  calc ‖a‖ = ‖archRow g a 0 * archHom F (((g⁻¹ : AdelicGL2 (𝓞 F) F) :
              Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) 0 1)
            + archRow g a 1 * archHom F (((g⁻¹ : AdelicGL2 (𝓞 F) F) :
              Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) 1 1)‖ := by rw [← h]
    _ ≤ ‖archRow g a 0‖ * ‖archHom F (((g⁻¹ : AdelicGL2 (𝓞 F) F) :
              Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) 0 1)‖
            + ‖archRow g a 1‖ * ‖archHom F (((g⁻¹ : AdelicGL2 (𝓞 F) F) :
              Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) 1 1)‖ :=
          (norm_add_le _ _).trans (add_le_add (norm_mul_le _ _) (norm_mul_le _ _))
    _ ≤ ‖archRow g a‖ * ‖archHom F (((g⁻¹ : AdelicGL2 (𝓞 F) F) :
              Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) 0 1)‖
            + ‖archRow g a‖ * ‖archHom F (((g⁻¹ : AdelicGL2 (𝓞 F) F) :
              Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) 1 1)‖ :=
          add_le_add (mul_le_mul_of_nonneg_right h0 (norm_nonneg _))
            (mul_le_mul_of_nonneg_right h1 (norm_nonneg _))
    _ = colSize g * ‖archRow g a‖ := by unfold colSize; ring

theorem schwartz_decay (G : 𝓢((Fin 2 → mixedEmbedding.mixedSpace F), ℂ)) (N : ℕ) :
    ∃ S : ℝ, 0 ≤ S ∧ ∀ y, ‖G y‖ * (1 + ‖y‖) ^ N ≤ S := by
  refine ⟨2 ^ N * (Finset.Iic (N, 0)).sup (fun m => SchwartzMap.seminorm ℂ m.1 m.2) G, by positivity,
    fun y => ?_⟩
  have h := SchwartzMap.one_add_le_sup_seminorm_apply (𝕜 := ℂ) (m := (N, 0)) (k := N) (n := 0)
    le_rfl le_rfl G y
  rw [norm_iteratedFDeriv_zero] at h
  rw [mul_comm]
  exact h

theorem norm_apply_archRow_le (G : 𝓢((Fin 2 → mixedEmbedding.mixedSpace F), ℂ)) (N : ℕ) {S : ℝ}
    (hS0 : 0 ≤ S) (hS : ∀ y, ‖G y‖ * (1 + ‖y‖) ^ N ≤ S) {L : ℝ} (hL : 1 ≤ L)
    (g : AdelicGL2 (𝓞 F) F) (hg : colSize g ≤ L) (a : mixedEmbedding.mixedSpace F) :
    ‖G (archRow g a)‖ ≤ L ^ N * S * ((1 + ‖a‖) ^ N)⁻¹ := by
  set y := archRow g a with hy
  have h1 : ‖a‖ ≤ L * ‖y‖ :=
    (norm_le_colSize_mul_norm_archRow g a).trans (mul_le_mul_of_nonneg_right hg (norm_nonneg _))
  have h2 : 1 + ‖a‖ ≤ L * (1 + ‖y‖) := by
    calc 1 + ‖a‖ ≤ L + L * ‖y‖ := add_le_add hL h1
      _ = L * (1 + ‖y‖) := by ring
  have h3 : (1 + ‖a‖) ^ N ≤ L ^ N * (1 + ‖y‖) ^ N := by
    rw [← mul_pow]; exact pow_le_pow_left₀ (by positivity) h2 N
  have hpos : 0 < (1 + ‖a‖) ^ N := by positivity
  rw [le_mul_inv_iff₀ hpos]
  calc ‖G y‖ * (1 + ‖a‖) ^ N ≤ ‖G y‖ * (L ^ N * (1 + ‖y‖) ^ N) :=
        mul_le_mul_of_nonneg_left h3 (norm_nonneg _)
    _ = L ^ N * (‖G y‖ * (1 + ‖y‖) ^ N) := by ring
    _ ≤ L ^ N * S := mul_le_mul_of_nonneg_left (hS y) (by positivity)

theorem exists_nhds_forall_vecMul_eq {R : Type*} [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]
    {H : (Fin 2 → R) → ℂ} (hlc : IsLocallyConstant H) (hcs : HasCompactSupport H) :
    ∃ V ∈ 𝓝 (1 : GL (Fin 2) R), ∀ u ∈ V, ∀ w : Fin 2 → R,
      H (Matrix.vecMul w (u : Matrix (Fin 2) (Fin 2) R)) = H w := by

  have hact : Continuous fun p : (Fin 2 → R) × GL (Fin 2) R =>
      Matrix.vecMul p.1 (p.2 : Matrix (Fin 2) (Fin 2) R) :=
    Continuous.matrix_vecMul continuous_fst (Units.continuous_val.comp continuous_snd)

  set Z : Set ((Fin 2 → R) × GL (Fin 2) R) :=
    {p | H (Matrix.vecMul p.1 (p.2 : Matrix (Fin 2) (Fin 2) R)) = H p.1} with hZ
  have hZopen : IsOpen Z := by
    have h1 : IsLocallyConstant fun p : (Fin 2 → R) × GL (Fin 2) R =>
        (H (Matrix.vecMul p.1 (p.2 : Matrix (Fin 2) (Fin 2) R)), H p.1) :=
      (hlc.comp_continuous hact).prodMk (hlc.comp_continuous continuous_fst)
    have : Z = (fun p : (Fin 2 → R) × GL (Fin 2) R =>
        (H (Matrix.vecMul p.1 (p.2 : Matrix (Fin 2) (Fin 2) R)), H p.1)) ⁻¹' {q | q.1 = q.2} := by
      ext p; simp [hZ]
    rw [this]
    exact h1 _

  set K : Set (Fin 2 → R) := tsupport H with hK
  have hKc : IsCompact K := hcs
  have hsub : K ×ˢ ({1} : Set (GL (Fin 2) R)) ⊆ Z := by
    rintro ⟨w, u⟩ ⟨_, hu⟩
    have hu1 : u = 1 := hu
    subst hu1
    show H (Matrix.vecMul w ((1 : GL (Fin 2) R) : Matrix (Fin 2) (Fin 2) R)) = H w
    rw [Units.val_one, Matrix.vecMul_one]
  obtain ⟨U, V, hU, hV, hKU, h1V, hUV⟩ := generalized_tube_lemma hKc isCompact_singleton hZopen hsub
  have h1V' : (1 : GL (Fin 2) R) ∈ V := h1V (Set.mem_singleton 1)

  refine ⟨V ∩ (fun u => u⁻¹) ⁻¹' V, ?_, ?_⟩
  · refine Filter.inter_mem (hV.mem_nhds h1V') ?_
    exact continuous_inv.continuousAt.preimage_mem_nhds (by rw [inv_one]; exact hV.mem_nhds h1V')
  · rintro u ⟨huV, huV'⟩ w
    by_cases hw : w ∈ K
    · exact hUV (Set.mk_mem_prod (hKU hw) huV)
    · have hw0 : H w = 0 := image_eq_zero_of_notMem_tsupport hw
      rw [hw0]
      by_contra hne
      have hmem : Matrix.vecMul w (u : Matrix (Fin 2) (Fin 2) R) ∈ K :=
        subset_tsupport H (Function.mem_support.mpr hne)
      have hz : (Matrix.vecMul w (u : Matrix (Fin 2) (Fin 2) R), u⁻¹) ∈ Z :=
        hUV (Set.mk_mem_prod (hKU hmem) huV')
      have hz' : H (Matrix.vecMul (Matrix.vecMul w (u : Matrix (Fin 2) (Fin 2) R))
          ((u⁻¹ : GL (Fin 2) R) : Matrix (Fin 2) (Fin 2) R))
          = H (Matrix.vecMul w (u : Matrix (Fin 2) (Fin 2) R)) := hz
      rw [Matrix.vecMul_vecMul, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.vecMul_one] at hz'
      exact hne (hz'.symm.trans hw0)

variable (F) in

def mapFin : AdelicGL2 (𝓞 F) F →* GL (Fin 2) (FiniteAdeleRing (𝓞 F) F) :=
  Matrix.GeneralLinearGroup.map (finHom F)

theorem mapFin_apply (g : AdelicGL2 (𝓞 F) F) (i j : Fin 2) :
    ((mapFin F g : GL (Fin 2) (FiniteAdeleRing (𝓞 F) F)) : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 F) F)) i j
      = ((g : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) i j).2 :=
  Matrix.GeneralLinearGroup.map_apply (finHom F) i j g

theorem continuous_mapFin : Continuous (mapFin F) := by
  refine Units.continuous_iff.2 ⟨?_, ?_⟩
  · have : (Units.val ∘ (mapFin F)) = fun g : AdelicGL2 (𝓞 F) F =>
        (g : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)).map (finHom F) := by
      funext g; exact Matrix.ext fun i j => mapFin_apply g i j
    rw [this]
    exact Units.continuous_val.matrix_map continuous_snd
  · have : (fun g : AdelicGL2 (𝓞 F) F => ((mapFin F g)⁻¹ : GL (Fin 2) (FiniteAdeleRing (𝓞 F) F)).val)
        = fun g : AdelicGL2 (𝓞 F) F =>
          ((g⁻¹ : AdelicGL2 (𝓞 F) F) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)).map (finHom F) := by
      funext g
      rw [← map_inv]
      exact Matrix.ext fun i j => mapFin_apply g⁻¹ i j
    rw [this]
    exact (Units.continuous_val.comp continuous_inv).matrix_map continuous_snd

theorem finRow_eq_vecMul (g : AdelicGL2 (𝓞 F) F) (z : FiniteAdeleRing (𝓞 F) F) :
    finRow g z = Matrix.vecMul (Pi.single 1 z)
      ((mapFin F g : GL (Fin 2) (FiniteAdeleRing (𝓞 F) F)) : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 F) F)) := by
  rw [Matrix.single_vecMul]
  funext j
  simp [finRow, Matrix.row_apply, mapFin_apply]

theorem eventually_finRow_eq {H : (Fin 2 → FiniteAdeleRing (𝓞 F) F) → ℂ}
    (hlc : IsLocallyConstant H) (hcs : HasCompactSupport H) (g₀ : AdelicGL2 (𝓞 F) F) :
    ∀ᶠ g in 𝓝 g₀, ∀ z : FiniteAdeleRing (𝓞 F) F, H (finRow g z) = H (finRow g₀ z) := by
  obtain ⟨V, hV, hinv⟩ := exists_nhds_forall_vecMul_eq hlc hcs
  have hc : Continuous fun g : AdelicGL2 (𝓞 F) F => (mapFin F g₀)⁻¹ * mapFin F g :=
    continuous_const.mul continuous_mapFin
  have hmem : {g : AdelicGL2 (𝓞 F) F | (mapFin F g₀)⁻¹ * mapFin F g ∈ V} ∈ 𝓝 g₀ := by
    refine hc.continuousAt.preimage_mem_nhds ?_
    rw [inv_mul_cancel]
    exact hV
  refine Filter.mem_of_superset hmem fun g hg z => ?_
  have h := hinv _ hg (finRow g₀ z)
  rw [finRow_eq_vecMul g₀, Matrix.vecMul_vecMul, ← Units.val_mul, mul_inv_cancel_left] at h
  rw [finRow_eq_vecMul g, finRow_eq_vecMul g₀]
  exact h

theorem finRow_locallyConstant_compactSupport {H : (Fin 2 → FiniteAdeleRing (𝓞 F) F) → ℂ}
    (hlc : IsLocallyConstant H) (hcs : HasCompactSupport H) (g₀ : AdelicGL2 (𝓞 F) F) :
    IsLocallyConstant (fun z => H (finRow g₀ z)) ∧ HasCompactSupport (fun z => H (finRow g₀ z)) := by
  have hcont : Continuous (finRow (F := F) g₀) :=
    continuous_pi fun j => continuous_id.mul continuous_const
  refine ⟨hlc.comp_continuous hcont, ?_⟩
  set p := (((g₀⁻¹ : AdelicGL2 (𝓞 F) F) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) 0 1).2 with hp
  set q := (((g₀⁻¹ : AdelicGL2 (𝓞 F) F) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) 1 1).2 with hq
  set ψ : (Fin 2 → FiniteAdeleRing (𝓞 F) F) → FiniteAdeleRing (𝓞 F) F := fun w => w 0 * p + w 1 * q with hψ
  have hψc : Continuous ψ :=
    ((continuous_apply 0).mul continuous_const).add ((continuous_apply 1).mul continuous_const)
  refine HasCompactSupport.intro (hcs.image hψc) fun z hz => ?_
  by_contra hne
  have hmem : finRow g₀ z ∈ tsupport H := subset_tsupport H (Function.mem_support.mpr hne)
  refine hz ⟨finRow g₀ z, hmem, ?_⟩
  rw [hψ]
  exact (finRow_recover g₀ z).symm

variable (F) in

def archBumpData : ContDiffBump (0 : mixedEmbedding.mixedSpace F) := ⟨2, 3, by norm_num, by norm_num⟩

variable (F) in
def archBump : 𝓢(mixedEmbedding.mixedSpace F, ℂ) :=
  HasCompactSupport.toSchwartzMap
    (f := fun y => (((archBumpData F) y : ℝ) : ℂ))
    ((archBumpData F).hasCompactSupport.comp_left Complex.ofReal_zero)
    (Complex.ofRealCLM.contDiff.comp (archBumpData F).contDiff)

theorem archBump_apply (y : mixedEmbedding.mixedSpace F) : archBump F y = (((archBumpData F) y : ℝ) : ℂ) := rfl

theorem norm_archBump_le_one (y : mixedEmbedding.mixedSpace F) : ‖archBump F y‖ ≤ 1 := by
  rw [archBump_apply, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (archBumpData F).nonneg]
  exact (archBumpData F).le_one

theorem norm_archBump_eq_one {y : mixedEmbedding.mixedSpace F} (hy : ‖y‖ ≤ 2) : ‖archBump F y‖ = 1 := by
  rw [archBump_apply, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (archBumpData F).nonneg]
  apply (archBumpData F).one_of_mem_closedBall
  simp at hy ⊢
  exact hy

variable (F) in

def archScalar (r : ℝ) (hr : r ≠ 0) : (AdeleRing (𝓞 F) F)ˣ where
  val := ((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm (r • (1 : mixedEmbedding.mixedSpace F)), 1)
  inv := ((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm (r⁻¹ • (1 : mixedEmbedding.mixedSpace F)), 1)
  val_inv := by
    refine Prod.ext ?_ (one_mul 1)
    show (InfiniteAdeleRing.ringEquiv_mixedSpace F).symm (r • 1)
        * (InfiniteAdeleRing.ringEquiv_mixedSpace F).symm (r⁻¹ • 1) = 1
    rw [← map_mul, smul_one_mul, smul_smul, mul_inv_cancel₀ hr, one_smul, map_one]
  inv_val := by
    refine Prod.ext ?_ (one_mul 1)
    show (InfiniteAdeleRing.ringEquiv_mixedSpace F).symm (r⁻¹ • 1)
        * (InfiniteAdeleRing.ringEquiv_mixedSpace F).symm (r • 1) = 1
    rw [← map_mul, smul_one_mul, smul_smul, inv_mul_cancel₀ hr, one_smul, map_one]

theorem archHom_archScalar (r : ℝ) (hr : r ≠ 0) :
    archHom F (archScalar F r hr : AdeleRing (𝓞 F) F) = r • (1 : mixedEmbedding.mixedSpace F) := by
  show InfiniteAdeleRing.ringEquiv_mixedSpace F
      ((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm (r • 1)) = r • 1
  exact (InfiniteAdeleRing.ringEquiv_mixedSpace F).apply_symm_apply _

theorem archScalar_snd (r : ℝ) (hr : r ≠ 0) : ((archScalar F r hr : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F).2 = 1 :=
  rfl

theorem archHom_archScalar_pow_mul (r : ℝ) (hr : r ≠ 0) (k : ℕ) (t : (AdeleRing (𝓞 F) F)ˣ) :
    archHom F (((archScalar F r hr) ^ k * t : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F)
      = r ^ k • archHom F (t : AdeleRing (𝓞 F) F) := by
  rw [Units.val_mul, Units.val_pow_eq_pow_val, map_mul, map_pow, archHom_archScalar, smul_pow, one_pow,
    smul_one_mul]

theorem snd_archScalar_pow_mul (r : ℝ) (hr : r ≠ 0) (k : ℕ) (t : (AdeleRing (𝓞 F) F)ˣ) :
    (((archScalar F r hr) ^ k * t : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F).2 = (t : AdeleRing (𝓞 F) F).2 := by
  show finHom F (((archScalar F r hr) ^ k * t : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F) = finHom F t
  rw [Units.val_mul, Units.val_pow_eq_pow_val, map_mul, map_pow]
  have : finHom F (archScalar F r hr : AdeleRing (𝓞 F) F) = 1 := rfl
  rw [this, one_pow, one_mul]

theorem ideleNorm_pow (x : (AdeleRing (𝓞 F) F)ˣ) (k : ℕ) : ideleNorm F (x ^ k) = ideleNorm F x ^ k := by
  induction k with
  | zero => simp [ideleNorm]
  | succ k ih => rw [pow_succ, ideleNorm_mul, ih, pow_succ]

def majorant (N : ℕ) (h₁ : FiniteAdeleRing (𝓞 F) F → ℂ) (σ : ℝ) (t : (AdeleRing (𝓞 F) F)ˣ) : ℝ :=
  ((1 + ‖archHom F (t : AdeleRing (𝓞 F) F)‖) ^ N)⁻¹ * ‖h₁ (t : AdeleRing (𝓞 F) F).2‖ * ideleNorm F t ^ σ

theorem majorant_nonneg (N : ℕ) (h₁ : FiniteAdeleRing (𝓞 F) F → ℂ) (σ : ℝ) (t : (AdeleRing (𝓞 F) F)ˣ) :
    0 ≤ majorant N h₁ σ t := by
  unfold majorant
  have := ideleNorm_pos (F := F) t
  positivity

theorem continuous_archHom_units : Continuous fun t : (AdeleRing (𝓞 F) F)ˣ => archHom F (t : AdeleRing (𝓞 F) F) :=
  continuous_archHom.comp Units.continuous_val

theorem continuous_snd_units : Continuous fun t : (AdeleRing (𝓞 F) F)ˣ => (t : AdeleRing (𝓞 F) F).2 :=
  continuous_snd.comp Units.continuous_val

theorem continuous_ideleNorm_rpow (σ : ℝ) : Continuous fun t : (AdeleRing (𝓞 F) F)ˣ => ideleNorm F t ^ σ :=
  (NumberField.TateGlobal.continuous_ideleNorm F).rpow_const fun t => Or.inl (ideleNorm_pos t).ne'

theorem continuous_majorant (N : ℕ) {h₁ : FiniteAdeleRing (𝓞 F) F → ℂ} (hh₁ : Continuous h₁) (σ : ℝ) :
    Continuous (majorant (F := F) N h₁ σ) := by
  unfold majorant
  refine Continuous.mul (Continuous.mul ?_ ?_) (continuous_ideleNorm_rpow σ)
  · refine Continuous.inv₀ ((continuous_const.add continuous_archHom_units.norm).pow N) fun t => ?_
    positivity
  · exact (hh₁.comp continuous_snd_units).norm

theorem exists_integrable_majorant [MeasurableSpace (AdeleRing (𝓞 F) F)ˣ] [BorelSpace (AdeleRing (𝓞 F) F)ˣ]
    (ν₀ : Measure (AdeleRing (𝓞 F) F)ˣ) [ν₀.IsHaarMeasure]
    {h₁ : FiniteAdeleRing (𝓞 F) F → ℂ} (hlc : IsLocallyConstant h₁) (hcs : HasCompactSupport h₁)
    {σ : ℝ} (hσ : 1 < σ) :
    ∃ N : ℕ, Integrable (majorant N h₁ σ) ν₀ := by

  set f₀ : AdeleRing (𝓞 F) F → ℂ := fun x =>
    archBump F (InfiniteAdeleRing.ringEquiv_mixedSpace F x.1) * h₁ x.2 with hf₀
  have hf₀v : ∀ x, f₀ x = archBump F (archHom F x) * h₁ x.2 := fun x => rfl
  have hf₀mem : f₀ ∈ schwartzBruhat F :=
    mem_schwartzBruhat_of_mem_pureTensorSet (tensor_mem_pureTensorSet (archBump F) h₁ hlc hcs)
  have hf₀c : Continuous f₀ :=
    ((archBump F).continuous.comp continuous_archHom).mul (hlc.continuous.comp continuous_snd)
  have hχ1 : Continuous (1 : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ) := continuous_const
  have hχ1u : IsUnitaryChar (𝓞 F) F (1 : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ) := fun x => by simp
  have hs : 1 < ((σ : ℝ) : ℂ).re := by simpa using hσ
  have hI := NumberField.TateGlobal.integrable_zetaIntegrand F ν₀ hf₀mem hχ1 hχ1u hs

  set g₀ : (AdeleRing (𝓞 F) F)ˣ → ℝ := fun t => ‖f₀ (t : AdeleRing (𝓞 F) F)‖ * ideleNorm F t ^ σ with hg₀
  have hg₀v : ∀ t, g₀ t = ‖f₀ (t : AdeleRing (𝓞 F) F)‖ * ideleNorm F t ^ σ := fun t => rfl
  have hg₀eq : ∀ t : (AdeleRing (𝓞 F) F)ˣ, ‖f₀ (t : AdeleRing (𝓞 F) F)
      * (((1 : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ) t : ℂˣ) : ℂ) * ((ideleNorm F t : ℝ) : ℂ) ^ ((σ : ℝ) : ℂ)‖ = g₀ t := by
    intro t
    rw [norm_mul, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos (ideleNorm_pos t), Complex.ofReal_re,
      MonoidHom.one_apply, Units.val_one, norm_one, mul_one]
  have hg₀c : Continuous g₀ :=
    (hf₀c.comp Units.continuous_val).norm.mul (continuous_ideleNorm_rpow σ)
  have hg₀m : Measurable g₀ := hg₀c.measurable
  have hL₀ : ∫⁻ t, ENNReal.ofReal (g₀ t) ∂ν₀ < ∞ := by
    have h := hI.hasFiniteIntegral
    rw [hasFiniteIntegral_iff_norm] at h
    simpa only [hg₀eq] using h

  obtain ⟨c, hcarch, hcsnd⟩ : ∃ c : (AdeleRing (𝓞 F) F)ˣ,
      (∀ (k : ℕ) (t : (AdeleRing (𝓞 F) F)ˣ),
        archHom F ((c ^ k * t : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F)
          = (1 / 2 : ℝ) ^ k • archHom F (t : AdeleRing (𝓞 F) F)) ∧
      (∀ (k : ℕ) (t : (AdeleRing (𝓞 F) F)ˣ),
        ((c ^ k * t : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F).2 = (t : AdeleRing (𝓞 F) F).2) :=
    ⟨archScalar F (1 / 2) (by norm_num), archHom_archScalar_pow_mul _ _, snd_archScalar_pow_mul _ _⟩
  set ρ : ℝ := ideleNorm F c with hρ
  have hρpos : 0 < ρ := ideleNorm_pos c
  have hρσ : 0 < ρ ^ σ := Real.rpow_pos_of_pos hρpos σ

  obtain ⟨N, hN⟩ := pow_unbounded_of_one_lt (ρ ^ σ)⁻¹ (one_lt_two (α := ℝ))
  set a : ℝ := (ρ ^ σ)⁻¹ / 2 ^ N with ha
  have ha0 : 0 ≤ a := by rw [ha]; positivity
  have ha1 : a < 1 := by rw [ha]; exact (div_lt_one (by positivity)).2 hN
  have haρ : a * ρ ^ σ = (2 ^ N)⁻¹ := by
    rw [ha]; field_simp
  refine ⟨N, ?_⟩

  have hpt : ∀ t, ∃ k : ℕ, majorant N h₁ σ t ≤ a ^ k * g₀ (c ^ k * t) := by
    intro t
    set r : ℝ := ‖archHom F (t : AdeleRing (𝓞 F) F)‖ with hr
    have hr0 : 0 ≤ r := norm_nonneg _
    obtain ⟨k, hk1, hk2⟩ := exists_nat_pow_near (x := 1 + r) (y := (2 : ℝ)) (by linarith) one_lt_two
    refine ⟨k, ?_⟩

    have hnorm : ‖archHom F ((c ^ k * t : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F)‖ ≤ 2 := by
      rw [hcarch, norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity : (0 : ℝ) ≤ (1 / 2) ^ k), ← hr]
      have h2k : (0 : ℝ) < 2 ^ k := by positivity
      have : (1 / 2 : ℝ) ^ k * r = r / 2 ^ k := by rw [one_div, inv_pow]; ring
      rw [this, div_le_iff₀ h2k]
      calc r ≤ 1 + r := by linarith
        _ ≤ 2 ^ (k + 1) := hk2.le
        _ = 2 * 2 ^ k := by ring
    have hbump : ‖archBump F (archHom F ((c ^ k * t : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F))‖ = 1 :=
      norm_archBump_eq_one hnorm
    have hρk : (ρ ^ k) ^ σ = (ρ ^ σ) ^ k := by
      rw [← Real.rpow_natCast ρ k, ← Real.rpow_mul hρpos.le, mul_comm, Real.rpow_mul hρpos.le,
        Real.rpow_natCast]
    have hg₀val : g₀ (c ^ k * t) = ‖h₁ (t : AdeleRing (𝓞 F) F).2‖ * ((ρ ^ σ) ^ k * ideleNorm F t ^ σ) := by
      rw [hg₀v, hf₀v, norm_mul, hbump, one_mul, hcsnd, ideleNorm_mul, ideleNorm_pow,
        Real.mul_rpow (by positivity) (ideleNorm_pos t).le, hρk]
    rw [hg₀val]
    unfold majorant
    rw [← hr]

    have hkey : ((1 + r) ^ N)⁻¹ ≤ a ^ k * (ρ ^ σ) ^ k := by
      have h2 : a ^ k * (ρ ^ σ) ^ k = ((2 ^ k) ^ N)⁻¹ := by
        rw [← mul_pow, haρ, inv_pow, ← pow_mul, ← pow_mul, mul_comm]
      rw [h2]
      exact inv_anti₀ (by positivity) (pow_le_pow_left₀ (by positivity) hk1 N)
    have hrest : 0 ≤ ‖h₁ (t : AdeleRing (𝓞 F) F).2‖ * ideleNorm F t ^ σ := by
      have := ideleNorm_pos (F := F) t; positivity
    calc ((1 + r) ^ N)⁻¹ * ‖h₁ (t : AdeleRing (𝓞 F) F).2‖ * ideleNorm F t ^ σ
        = ((1 + r) ^ N)⁻¹ * (‖h₁ (t : AdeleRing (𝓞 F) F).2‖ * ideleNorm F t ^ σ) := by ring
      _ ≤ (a ^ k * (ρ ^ σ) ^ k) * (‖h₁ (t : AdeleRing (𝓞 F) F).2‖ * ideleNorm F t ^ σ) :=
          mul_le_mul_of_nonneg_right hkey hrest
      _ = a ^ k * (‖h₁ (t : AdeleRing (𝓞 F) F).2‖ * ((ρ ^ σ) ^ k * ideleNorm F t ^ σ)) := by ring

  have hmeas : ∀ j : ℕ, Measurable fun t => ENNReal.ofReal (a ^ j * g₀ (c ^ j * t)) := fun j =>
    ((measurable_const.mul (hg₀m.comp (measurable_const_mul _)))).ennreal_ofReal
  have hseries : ∫⁻ t, ∑' j : ℕ, ENNReal.ofReal (a ^ j * g₀ (c ^ j * t)) ∂ν₀ < ∞ := by
    rw [lintegral_tsum fun j => (hmeas j).aemeasurable]
    have hterm : ∀ j : ℕ, ∫⁻ t, ENNReal.ofReal (a ^ j * g₀ (c ^ j * t)) ∂ν₀
        = ENNReal.ofReal a ^ j * ∫⁻ t, ENNReal.ofReal (g₀ t) ∂ν₀ := by
      intro j
      have h1 : (fun t => ENNReal.ofReal (a ^ j * g₀ (c ^ j * t)))
          = fun t => ENNReal.ofReal (a ^ j) * ENNReal.ofReal (g₀ (c ^ j * t)) := by
        funext t; rw [ENNReal.ofReal_mul (pow_nonneg ha0 j)]
      have hm : Measurable fun t : (AdeleRing (𝓞 F) F)ˣ => ENNReal.ofReal (g₀ (c ^ j * t)) :=
        (hg₀m.comp (measurable_const_mul (c ^ j))).ennreal_ofReal
      rw [h1, lintegral_const_mul _ hm, ENNReal.ofReal_pow ha0]
      congr 1
      exact lintegral_mul_left_eq_self (fun t => ENNReal.ofReal (g₀ t)) (c ^ j)
    simp_rw [hterm]
    rw [ENNReal.tsum_mul_right, ENNReal.tsum_geometric]
    refine ENNReal.mul_lt_top ?_ hL₀
    refine ENNReal.inv_lt_top.2 (tsub_pos_of_lt ?_)
    rw [← ENNReal.ofReal_one]
    exact (ENNReal.ofReal_lt_ofReal_iff one_pos).2 ha1
  refine ⟨(continuous_majorant N hlc.continuous σ).aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_iff_norm]
  refine lt_of_le_of_lt (lintegral_mono fun t => ?_) hseries
  rw [Real.norm_eq_abs, abs_of_nonneg (majorant_nonneg N h₁ σ t)]
  obtain ⟨k, hk⟩ := hpt t
  exact (ENNReal.ofReal_le_ofReal hk).trans (ENNReal.le_tsum k)

section Domination

variable [MeasurableSpace (AdeleRing (𝓞 F) F)ˣ] [BorelSpace (AdeleRing (𝓞 F) F)ˣ]
  (ν₀ : Measure (AdeleRing (𝓞 F) F)ˣ) [ν₀.IsHaarMeasure]

def DomProp (Φ : (Fin 2 → AdeleRing (𝓞 F) F) → ℂ) : Prop :=
  ∀ (g₀ : AdelicGL2 (𝓞 F) F) (σ : ℝ), 1 < σ → ∃ B : (AdeleRing (𝓞 F) F)ˣ → ℝ, Integrable B ν₀ ∧
    ∀ᶠ g in 𝓝 g₀, ∀ t : (AdeleRing (𝓞 F) F)ˣ,
      ‖Φ (bottomRowVec F g (t : AdeleRing (𝓞 F) F))‖ * ideleNorm F t ^ σ ≤ B t

theorem domProp_of_mem_pureTensorSet2 {Φ : (Fin 2 → AdeleRing (𝓞 F) F) → ℂ} (hΦ : Φ ∈ pureTensorSet2 F) :
    DomProp ν₀ Φ := by
  obtain ⟨G, H, hlc, hcs, rfl⟩ := hΦ
  intro g₀ σ hσ

  obtain ⟨hlc₁, hcs₁⟩ := finRow_locallyConstant_compactSupport hlc hcs g₀
  obtain ⟨N, hmaj⟩ := exists_integrable_majorant ν₀ hlc₁ hcs₁ hσ
  obtain ⟨S, hS0, hS⟩ := schwartz_decay G N
  set L : ℝ := colSize g₀ + 1 with hL
  have hL1 : 1 ≤ L := by rw [hL]; linarith [colSize_nonneg g₀]
  refine ⟨fun t => (L ^ N * S) * majorant N (fun z => H (finRow g₀ z)) σ t, hmaj.const_mul _, ?_⟩
  have hev1 : ∀ᶠ g in 𝓝 g₀, colSize g < L :=
    continuous_colSize.continuousAt.eventually (Iio_mem_nhds (by rw [hL]; linarith))
  have hev2 := eventually_finRow_eq hlc hcs g₀
  filter_upwards [hev1, hev2] with g hg1 hg2 t
  rw [archProj_bottomRowVec, finProj_bottomRowVec, hg2, norm_mul]
  have hG := norm_apply_archRow_le G N hS0 hS hL1 g hg1.le (archHom F (t : AdeleRing (𝓞 F) F))
  unfold majorant
  beta_reduce
  have hpos := ideleNorm_pos (F := F) t
  have h1 : 0 ≤ ‖H (finRow g₀ (t : AdeleRing (𝓞 F) F).2)‖ * ideleNorm F t ^ σ := by positivity
  calc ‖G (archRow g (archHom F (t : AdeleRing (𝓞 F) F)))‖ * ‖H (finRow g₀ (t : AdeleRing (𝓞 F) F).2)‖
        * ideleNorm F t ^ σ
      = ‖G (archRow g (archHom F (t : AdeleRing (𝓞 F) F)))‖
          * (‖H (finRow g₀ (t : AdeleRing (𝓞 F) F).2)‖ * ideleNorm F t ^ σ) := by ring
    _ ≤ (L ^ N * S * ((1 + ‖archHom F (t : AdeleRing (𝓞 F) F)‖) ^ N)⁻¹)
          * (‖H (finRow g₀ (t : AdeleRing (𝓞 F) F).2)‖ * ideleNorm F t ^ σ) :=
        mul_le_mul_of_nonneg_right hG h1
    _ = _ := by ring

theorem domProp_zero : DomProp ν₀ (0 : (Fin 2 → AdeleRing (𝓞 F) F) → ℂ) := by
  intro g₀ σ hσ
  exact ⟨0, integrable_zero _ _ _, Eventually.of_forall fun g t => by simp⟩

theorem DomProp.add {Φ Ψ : (Fin 2 → AdeleRing (𝓞 F) F) → ℂ} (hΦ : DomProp ν₀ Φ) (hΨ : DomProp ν₀ Ψ) :
    DomProp ν₀ (Φ + Ψ) := by
  intro g₀ σ hσ
  obtain ⟨B₁, hB₁, h₁⟩ := hΦ g₀ σ hσ
  obtain ⟨B₂, hB₂, h₂⟩ := hΨ g₀ σ hσ
  refine ⟨B₁ + B₂, hB₁.add hB₂, ?_⟩
  filter_upwards [h₁, h₂] with g hg₁ hg₂ t
  have hw : 0 ≤ ideleNorm F t ^ σ := Real.rpow_nonneg (ideleNorm_pos t).le _
  calc ‖(Φ + Ψ) (bottomRowVec F g (t : AdeleRing (𝓞 F) F))‖ * ideleNorm F t ^ σ
      ≤ (‖Φ (bottomRowVec F g (t : AdeleRing (𝓞 F) F))‖ + ‖Ψ (bottomRowVec F g (t : AdeleRing (𝓞 F) F))‖)
          * ideleNorm F t ^ σ := mul_le_mul_of_nonneg_right (norm_add_le _ _) hw
    _ = ‖Φ (bottomRowVec F g (t : AdeleRing (𝓞 F) F))‖ * ideleNorm F t ^ σ
          + ‖Ψ (bottomRowVec F g (t : AdeleRing (𝓞 F) F))‖ * ideleNorm F t ^ σ := by ring
    _ ≤ B₁ t + B₂ t := add_le_add (hg₁ t) (hg₂ t)
    _ = (B₁ + B₂) t := rfl

theorem DomProp.smul {Φ : (Fin 2 → AdeleRing (𝓞 F) F) → ℂ} (hΦ : DomProp ν₀ Φ) (a : ℂ) :
    DomProp ν₀ (a • Φ) := by
  intro g₀ σ hσ
  obtain ⟨B, hB, h⟩ := hΦ g₀ σ hσ
  refine ⟨fun t => ‖a‖ * B t, hB.const_mul _, ?_⟩
  filter_upwards [h] with g hg t
  rw [Pi.smul_apply, norm_smul, mul_assoc]
  exact mul_le_mul_of_nonneg_left (hg t) (norm_nonneg a)

theorem domProp_of_mem_schwartzBruhat2 {Φ : (Fin 2 → AdeleRing (𝓞 F) F) → ℂ} (hΦ : Φ ∈ schwartzBruhat2 F) :
    DomProp ν₀ Φ := by
  induction hΦ using schwartzBruhat2_induction with
  | tensor Φ hΦ => exact domProp_of_mem_pureTensorSet2 ν₀ hΦ
  | zero => exact domProp_zero ν₀
  | add Φ Ψ _ _ ihΦ ihΨ => exact ihΦ.add ν₀ ihΨ
  | smul a Φ _ ih => exact ih.smul ν₀ a

end Domination

theorem continuous_of_mem_schwartzBruhat2 {Φ : (Fin 2 → AdeleRing (𝓞 F) F) → ℂ}
    (hΦ : Φ ∈ schwartzBruhat2 F) : Continuous Φ := by
  induction hΦ using schwartzBruhat2_induction with
  | tensor Φ hΦ =>
      obtain ⟨G, H, hlc, hcs, rfl⟩ := hΦ
      refine Continuous.mul (G.continuous.comp ?_) (hlc.continuous.comp ?_)
      · exact continuous_pi fun i => continuous_archHom.comp (continuous_apply i)
      · exact continuous_pi fun i => continuous_snd.comp (continuous_apply i)
  | zero => exact continuous_const
  | add Φ Ψ _ _ ihΦ ihΨ => exact ihΦ.add ihΨ
  | smul a Φ _ ih => exact ih.const_smul a

theorem continuous_bottomRowVec_left (t : AdeleRing (𝓞 F) F) :
    Continuous fun g : AdelicGL2 (𝓞 F) F => bottomRowVec F g t :=
  continuous_pi fun j => continuous_const.mul (continuous_entry 1 j)

theorem continuous_bottomRowVec_right (g : AdelicGL2 (𝓞 F) F) :
    Continuous fun t : (AdeleRing (𝓞 F) F)ˣ => bottomRowVec F g (t : AdeleRing (𝓞 F) F) :=
  continuous_pi fun j => Units.continuous_val.mul continuous_const

variable (F) in

def hFun (Φ : (Fin 2 → AdeleRing (𝓞 F) F) → ℂ) (χ : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ)
    (g : AdelicGL2 (𝓞 F) F) (t : (AdeleRing (𝓞 F) F)ˣ) : ℂ :=
  Φ (bottomRowVec F g (t : AdeleRing (𝓞 F) F)) * ((χ t : ℂˣ) : ℂ)

theorem godementSection_eq {mI : MeasurableSpace (AdeleRing (𝓞 F) F)ˣ} (ν₀ : Measure (AdeleRing (𝓞 F) F)ˣ)
    (μ ν : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ) (α : (AdeleRing (𝓞 F) F)ˣ →* ℝˣ) (hα : ∀ x, 0 < ((α x : ℝˣ) : ℝ))
    (Φ : (Fin 2 → AdeleRing (𝓞 F) F) → ℂ) (s : ℂ) (g : AdelicGL2 (𝓞 F) F) :
    godementSection F ν₀ μ ν α hα Φ s g
      = ((μ (Matrix.GeneralLinearGroup.det g) : ℂˣ) : ℂ)
        * ((((α (Matrix.GeneralLinearGroup.det g) : ℝˣ) : ℝ) : ℂ)) ^ (s + 1 / 2)
        * ∫ t, hFun F Φ (μ * ν⁻¹) g t * ((ideleNorm F t : ℝ) : ℂ) ^ (2 * s + 1) ∂ν₀ :=
  rfl

theorem norm_coe_mul_inv (μ ν : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ)
    (hμ : IsUnitaryChar (𝓞 F) F μ) (hν : IsUnitaryChar (𝓞 F) F ν) (t : (AdeleRing (𝓞 F) F)ˣ) :
    ‖(((μ * ν⁻¹) t : ℂˣ) : ℂ)‖ = 1 := by
  rw [MonoidHom.mul_apply, MonoidHom.inv_apply, Units.val_mul, Units.val_inv_eq_inv_val, norm_mul, norm_inv,
    hμ t, hν t]
  norm_num

theorem continuous_coe_mul_inv (μ ν : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ)
    (hμc : Continuous fun x : (AdeleRing (𝓞 F) F)ˣ => ((μ x : ℂˣ) : ℂ))
    (hνc : Continuous fun x : (AdeleRing (𝓞 F) F)ˣ => ((ν x : ℂˣ) : ℂ)) :
    Continuous fun t : (AdeleRing (𝓞 F) F)ˣ => (((μ * ν⁻¹) t : ℂˣ) : ℂ) := by
  have h : (fun t : (AdeleRing (𝓞 F) F)ˣ => (((μ * ν⁻¹) t : ℂˣ) : ℂ))
      = fun t => ((μ t : ℂˣ) : ℂ) * (((ν t : ℂˣ) : ℂ))⁻¹ := by
    funext t
    rw [MonoidHom.mul_apply, MonoidHom.inv_apply, Units.val_mul, Units.val_inv_eq_inv_val]
  rw [h]
  exact hμc.mul (hνc.inv₀ fun t => Units.ne_zero _)

section Main

variable [MeasurableSpace (AdeleRing (𝓞 F) F)ˣ] [BorelSpace (AdeleRing (𝓞 F) F)ˣ]
  (ν₀ : Measure (AdeleRing (𝓞 F) F)ˣ) [ν₀.IsHaarMeasure]
  (μ ν : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ)
  (hμ : IsUnitaryChar (𝓞 F) F μ) (hν : IsUnitaryChar (𝓞 F) F ν)
  (hμc : Continuous fun x : (AdeleRing (𝓞 F) F)ˣ => ((μ x : ℂˣ) : ℂ))
  (hνc : Continuous fun x : (AdeleRing (𝓞 F) F)ˣ => ((ν x : ℂˣ) : ℂ))
  {Φ : (Fin 2 → AdeleRing (𝓞 F) F) → ℂ} (hΦ : Φ ∈ schwartzBruhat2 F)

include hμc hνc hΦ in
theorem aestronglyMeasurable_hFun (g : AdelicGL2 (𝓞 F) F) : AEStronglyMeasurable (hFun F Φ (μ * ν⁻¹) g) ν₀ :=
  (((continuous_of_mem_schwartzBruhat2 hΦ).comp (continuous_bottomRowVec_right g)).mul
    (continuous_coe_mul_inv μ ν hμc hνc)).aestronglyMeasurable

include hΦ in
theorem continuous_hFun (t : (AdeleRing (𝓞 F) F)ˣ) : Continuous fun g => hFun F Φ (μ * ν⁻¹) g t :=
  ((continuous_of_mem_schwartzBruhat2 hΦ).comp (continuous_bottomRowVec_left (t : AdeleRing (𝓞 F) F))).mul
    continuous_const

include hμ hν hΦ in

theorem hFun_dom (g₀ : AdelicGL2 (𝓞 F) F) (a b : ℝ) (ha : 1 < a) (hab : a ≤ b) :
    ∃ bound : (AdeleRing (𝓞 F) F)ˣ → ℝ, Integrable bound ν₀ ∧
      ∀ᶠ g in 𝓝 g₀, ∀ t, ‖hFun F Φ (μ * ν⁻¹) g t‖ * (ideleNorm F t ^ a + ideleNorm F t ^ b) ≤ bound t := by
  have hD := domProp_of_mem_schwartzBruhat2 ν₀ hΦ
  obtain ⟨Ba, hBa, hea⟩ := hD g₀ a ha
  obtain ⟨Bb, hBb, heb⟩ := hD g₀ b (lt_of_lt_of_le ha hab)
  refine ⟨Ba + Bb, hBa.add hBb, ?_⟩
  filter_upwards [hea, heb] with g hga hgb t
  have hn : ‖hFun F Φ (μ * ν⁻¹) g t‖ = ‖Φ (bottomRowVec F g (t : AdeleRing (𝓞 F) F))‖ := by
    rw [hFun, norm_mul, norm_coe_mul_inv μ ν hμ hν, mul_one]
  rw [hn, mul_add]
  exact add_le_add (hga t) (hgb t)

include hμ hν hΦ in
theorem hFun_dom' (g : AdelicGL2 (𝓞 F) F) (a b : ℝ) (ha : 1 < a) (hab : a ≤ b) :
    ∃ bound : (AdeleRing (𝓞 F) F)ˣ → ℝ, Integrable bound ν₀ ∧
      ∀ t, ‖hFun F Φ (μ * ν⁻¹) g t‖ * (ideleNorm F t ^ a + ideleNorm F t ^ b) ≤ bound t := by
  obtain ⟨bound, hb, he⟩ := hFun_dom ν₀ μ ν hμ hν hΦ g a b ha hab
  exact ⟨bound, hb, he.self_of_nhds⟩

theorem re_two_mul_add_one (s : ℂ) : (2 * s + 1).re = 2 * s.re + 1 := by simp

include hμ hν hμc hνc hΦ in

theorem integrable_godementIntegrand (g : AdelicGL2 (𝓞 F) F) (s : ℂ) (hs : 0 < s.re) :
    Integrable (fun t : (AdeleRing (𝓞 F) F)ˣ =>
      Φ (bottomRowVec F g (t : AdeleRing (𝓞 F) F)) * (((μ * ν⁻¹) t : ℂˣ) : ℂ)
        * ((ideleNorm F t : ℝ) : ℂ) ^ (2 * s + 1)) ν₀ := by
  have hw : 1 < (2 * s + 1).re := by rw [re_two_mul_add_one]; linarith
  obtain ⟨bound, hb, he⟩ := hFun_dom' ν₀ μ ν hμ hν hΦ g (2 * s + 1).re (2 * s + 1).re hw le_rfl
  exact integrable_mul_cpow_of_dom ν₀ (NumberField.TateGlobal.continuous_ideleNorm F).measurable
    ideleNorm_pos (aestronglyMeasurable_hFun ν₀ μ ν hμc hνc hΦ g) hb he le_rfl le_rfl

include hμ hν hμc hνc hΦ in

theorem differentiableAt_godementSection (α : (AdeleRing (𝓞 F) F)ˣ →* ℝˣ) (hα : ∀ x, 0 < ((α x : ℝˣ) : ℝ))
    (g : AdelicGL2 (𝓞 F) F) (s : ℂ) (hs : 0 < s.re) :
    DifferentiableAt ℂ (fun s : ℂ => godementSection F ν₀ μ ν α hα Φ s g) s := by
  have hw : 1 < (2 * s + 1).re := by rw [re_two_mul_add_one]; linarith
  have hM : DifferentiableAt ℂ
      (fun w : ℂ => ∫ t, hFun F Φ (μ * ν⁻¹) g t * ((ideleNorm F t : ℝ) : ℂ) ^ w ∂ν₀) (2 * s + 1) :=
    differentiableAt_integral_mul_cpow ν₀ (NumberField.TateGlobal.continuous_ideleNorm F).measurable
      ideleNorm_pos (aestronglyMeasurable_hFun ν₀ μ ν hμc hνc hΦ g) 1 (hFun_dom' ν₀ μ ν hμ hν hΦ g) hw
  have haff : DifferentiableAt ℂ (fun s : ℂ => 2 * s + 1) s := by fun_prop
  have hcomp := hM.comp s haff
  have hne : ((((α (Matrix.GeneralLinearGroup.det g) : ℝˣ) : ℝ) : ℂ)) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (hα _).ne'
  have hcpow : DifferentiableAt ℂ
      (fun s : ℂ => ((((α (Matrix.GeneralLinearGroup.det g) : ℝˣ) : ℝ) : ℂ)) ^ (s + 1 / 2)) s :=
    (differentiableAt_id.add_const _).const_cpow (Or.inl hne)
  simp only [godementSection_eq]
  exact ((differentiableAt_const _).mul hcpow).mul hcomp

include hμ hν hμc hνc hΦ in

theorem continuousOn_godementSection (α : (AdeleRing (𝓞 F) F)ˣ →* ℝˣ) (hα : ∀ x, 0 < ((α x : ℝˣ) : ℝ))
    (hαN : ∀ x, ((α x : ℝˣ) : ℝ) = ideleNorm F x) :
    ContinuousOn (fun p : ℂ × AdelicGL2 (𝓞 F) F => godementSection F ν₀ μ ν α hα Φ p.1 p.2)
      {p | 0 < p.1.re} := by
  haveI : FirstCountableTopology (AdelicGL2 (𝓞 F) F) := firstCountableTopology_adelicGL2
  have hM := continuousOn_integral_mul_cpow ν₀ (NumberField.TateGlobal.continuous_ideleNorm F).measurable
    ideleNorm_pos (hFun F Φ (μ * ν⁻¹)) (aestronglyMeasurable_hFun ν₀ μ ν hμc hνc hΦ)
    (continuous_hFun μ ν hΦ) 1 (hFun_dom ν₀ μ ν hμ hν hΦ)
  have haff : Continuous fun p : ℂ × AdelicGL2 (𝓞 F) F => ((2 * p.1 + 1, p.2) : ℂ × AdelicGL2 (𝓞 F) F) := by
    fun_prop
  have hmaps : Set.MapsTo (fun p : ℂ × AdelicGL2 (𝓞 F) F => ((2 * p.1 + 1, p.2) : ℂ × AdelicGL2 (𝓞 F) F))
      {p | 0 < p.1.re} {q | 1 < q.1.re} := by
    intro p hp
    have hp' : 0 < p.1.re := hp
    show 1 < (2 * p.1 + 1).re
    rw [re_two_mul_add_one]; linarith
  have hcomp := hM.comp haff.continuousOn hmaps
  have hdet : Continuous fun p : ℂ × AdelicGL2 (𝓞 F) F => Matrix.GeneralLinearGroup.det p.2 :=
    Matrix.GeneralLinearGroup.continuous_det.comp continuous_snd
  have hcμ : Continuous fun p : ℂ × AdelicGL2 (𝓞 F) F =>
      ((μ (Matrix.GeneralLinearGroup.det p.2) : ℂˣ) : ℂ) := hμc.comp hdet
  have hbase : Continuous fun p : ℂ × AdelicGL2 (𝓞 F) F =>
      ((((α (Matrix.GeneralLinearGroup.det p.2) : ℝˣ) : ℝ) : ℂ)) := by
    have : (fun p : ℂ × AdelicGL2 (𝓞 F) F => ((((α (Matrix.GeneralLinearGroup.det p.2) : ℝˣ) : ℝ) : ℂ)))
        = fun p => ((ideleNorm F (Matrix.GeneralLinearGroup.det p.2) : ℝ) : ℂ) := by
      funext p; rw [hαN]
    rw [this]
    exact Complex.continuous_ofReal.comp ((NumberField.TateGlobal.continuous_ideleNorm F).comp hdet)
  have hcpow : Continuous fun p : ℂ × AdelicGL2 (𝓞 F) F =>
      ((((α (Matrix.GeneralLinearGroup.det p.2) : ℝˣ) : ℝ) : ℂ)) ^ (p.1 + 1 / 2) := by
    refine hbase.cpow (by fun_prop) fun p => ?_
    exact Complex.ofReal_mem_slitPlane.2 (hα _)
  simp only [godementSection_eq]
  exact (hcμ.continuousOn.mul hcpow.continuousOn).mul hcomp

include hμ hν hμc hνc hΦ in

theorem continuous_godementSection (α : (AdeleRing (𝓞 F) F)ˣ →* ℝˣ) (hα : ∀ x, 0 < ((α x : ℝˣ) : ℝ))
    (hαN : ∀ x, ((α x : ℝˣ) : ℝ) = ideleNorm F x) (s : ℂ) (hs : 0 < s.re) :
    Continuous fun g : AdelicGL2 (𝓞 F) F => godementSection F ν₀ μ ν α hα Φ s g := by
  haveI : FirstCountableTopology (AdelicGL2 (𝓞 F) F) := firstCountableTopology_adelicGL2
  have hM := continuousOn_integral_mul_cpow ν₀ (NumberField.TateGlobal.continuous_ideleNorm F).measurable
    ideleNorm_pos (hFun F Φ (μ * ν⁻¹)) (aestronglyMeasurable_hFun ν₀ μ ν hμc hνc hΦ)
    (continuous_hFun μ ν hΦ) 1 (hFun_dom ν₀ μ ν hμ hν hΦ)
  have hemb : Continuous fun g : AdelicGL2 (𝓞 F) F => ((2 * s + 1, g) : ℂ × AdelicGL2 (𝓞 F) F) := by
    fun_prop
  have hw : 1 < (2 * s + 1).re := by rw [re_two_mul_add_one]; linarith
  have hcomp : Continuous fun g : AdelicGL2 (𝓞 F) F =>
      ∫ t, hFun F Φ (μ * ν⁻¹) g t * ((ideleNorm F t : ℝ) : ℂ) ^ (2 * s + 1) ∂ν₀ :=
    (hM.comp_continuous hemb fun g => hw).congr fun g => rfl
  have hdet : Continuous fun g : AdelicGL2 (𝓞 F) F => Matrix.GeneralLinearGroup.det g :=
    Matrix.GeneralLinearGroup.continuous_det
  have hcμ : Continuous fun g : AdelicGL2 (𝓞 F) F =>
      ((μ (Matrix.GeneralLinearGroup.det g) : ℂˣ) : ℂ) := hμc.comp hdet
  have hbase : Continuous fun g : AdelicGL2 (𝓞 F) F =>
      ((((α (Matrix.GeneralLinearGroup.det g) : ℝˣ) : ℝ) : ℂ)) := by
    have : (fun g : AdelicGL2 (𝓞 F) F => ((((α (Matrix.GeneralLinearGroup.det g) : ℝˣ) : ℝ) : ℂ)))
        = fun g => ((ideleNorm F (Matrix.GeneralLinearGroup.det g) : ℝ) : ℂ) := by
      funext g; rw [hαN]
    rw [this]
    exact Complex.continuous_ofReal.comp ((NumberField.TateGlobal.continuous_ideleNorm F).comp hdet)
  have hcpow : Continuous fun g : AdelicGL2 (𝓞 F) F =>
      ((((α (Matrix.GeneralLinearGroup.det g) : ℝˣ) : ℝ) : ℂ)) ^ (s + 1 / 2) := by
    refine hbase.cpow continuous_const fun g => ?_
    exact Complex.ofReal_mem_slitPlane.2 (hα _)
  simp only [godementSection_eq]
  exact (hcμ.mul hcpow).mul hcomp

end Main

end Adelic

end AutomorphicForm.GodementK0b

end

p2m_open "MeasureTheory NumberField NumberField.AdelicFourier NumberField.TateGlobal AutomorphicForm P2MW.S_AutomorphicForm_integrable_and_differentiableAt_and_continuous_godementSection_of_mem_schwartzBruhat2.AutomorphicForm"

theorem solution
    (F : Type) [Field F] [NumberField F]
    [MeasurableSpace (AdeleRing (𝓞 F) F)ˣ] [BorelSpace (AdeleRing (𝓞 F) F)ˣ]
    (ν₀ : Measure (AdeleRing (𝓞 F) F)ˣ) [ν₀.IsHaarMeasure]
    (μ ν : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ)
    (_hμ : IsUnitaryChar (𝓞 F) F μ) (_hν : IsUnitaryChar (𝓞 F) F ν)
    (_hμc : Continuous fun x : (AdeleRing (𝓞 F) F)ˣ => ((μ x : ℂˣ) : ℂ))
    (_hνc : Continuous fun x : (AdeleRing (𝓞 F) F)ˣ => ((ν x : ℂˣ) : ℂ))
    (α : (AdeleRing (𝓞 F) F)ˣ →* ℝˣ) (hα : ∀ x, 0 < ((α x : ℝˣ) : ℝ))
    (_hαN : ∀ x, ((α x : ℝˣ) : ℝ) = ideleNorm F x)
    (Φ : (Fin 2 → AdeleRing (𝓞 F) F) → ℂ) (_hΦ : Φ ∈ schwartzBruhat2 F) :
    (∀ (g : AdelicGL2 (𝓞 F) F) (s : ℂ), 0 < s.re →
      Integrable (fun t : (AdeleRing (𝓞 F) F)ˣ =>
        Φ (bottomRowVec F g (t : AdeleRing (𝓞 F) F)) * (((μ * ν⁻¹) t : ℂˣ) : ℂ)
          * ((ideleNorm F t : ℝ) : ℂ) ^ (2 * s + 1)) ν₀) ∧
    (∀ (g : AdelicGL2 (𝓞 F) F) (s : ℂ), 0 < s.re →
      DifferentiableAt ℂ (fun s : ℂ => godementSection F ν₀ μ ν α hα Φ s g) s) ∧
    ContinuousOn (fun p : ℂ × AdelicGL2 (𝓞 F) F => godementSection F ν₀ μ ν α hα Φ p.1 p.2)
      {p | 0 < p.1.re} ∧
    (∀ s : ℂ, 0 < s.re →
      Continuous fun g : AdelicGL2 (𝓞 F) F => godementSection F ν₀ μ ν α hα Φ s g) :=
  ⟨AutomorphicForm.GodementK0b.integrable_godementIntegrand ν₀ μ ν _hμ _hν _hμc _hνc _hΦ,
    AutomorphicForm.GodementK0b.differentiableAt_godementSection ν₀ μ ν _hμ _hν _hμc _hνc _hΦ α hα,
    AutomorphicForm.GodementK0b.continuousOn_godementSection ν₀ μ ν _hμ _hν _hμc _hνc _hΦ α hα _hαN,
    AutomorphicForm.GodementK0b.continuous_godementSection ν₀ μ ν _hμ _hν _hμc _hνc _hΦ α hα _hαN⟩

end S_AutomorphicForm_integrable_and_differentiableAt_and_continuous_godementSection_of_mem_schwartzBruhat2
end P2MW
export P2MW.S_AutomorphicForm_integrable_and_differentiableAt_and_continuous_godementSection_of_mem_schwartzBruhat2 (solution)
