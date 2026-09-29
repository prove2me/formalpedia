-- Prove2me | solution 1 for AutomorphicForm.exists_forall_sq_mul_eq_norm_mul_and_forall_integral_affineChart_eq_add_mul_apply_one_of_not_isSquare
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.961684+00:00
-- url     : https://prove2.me/submissions/c6c444df-6d00-5a62-bf1a-18df8edd7e47

import Definitions.Def_AutomorphicForm_LocalOrbitalBase
import Theorems.Thm_AutomorphicForm_exists_forall_integral_affineChart_eq_add_mul_apply_one_of_not_isSquare
import Theorems.Thm_LanglandsTunnell_TateLocal_modulus_adicCompletion_eq_nnnorm
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_exists_forall_sq_mul_eq_norm_mul_and_forall_integral_affineChart_eq_add_mul_apply_one_of_not_isSquare
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
p2m_attr_erase "instance" "instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions instCountableOfNumberField_definitions"
p2m_attr_erase "simp" "NumberField.StandardAddChar.ratArchLine_apply NumberField.StandardAddChar.AdelicTraceData.mk.sizeOf_spec NumberField.StandardAddChar.AdelicTraceData.mk.injEq AutomorphicForm.whittakerCoefficient_zero AutomorphicForm.CarrierPins.mk.injEq AutomorphicForm.CarrierPins.mk.sizeOf_spec AutomorphicForm.unipotentGL2_zero AutomorphicForm.constantTerm_const AutomorphicForm.constantTerm_zero AutomorphicForm.unipotentGL2_coe NumberField.AdelicTrace.traceDiag_apply NumberField.AdelicTrace.diag_apply"

set_option autoImplicit false

open MeasureTheory Filter Topology NumberField IsDedekindDomain
open scoped NNReal ENNReal Pointwise

noncomputable section

namespace P2mIdentityGermHomog

section General

variable {F : Type*} [Field F]

def chartArg (s : F) (q : Fˣ × F) : Matrix (Fin 2) (Fin 2) F :=
  1 + !![q.2, ((q.1 : Fˣ) : F); (s - q.2 ^ 2) / ((q.1 : Fˣ) : F), -q.2]

def dil (s : F) (Φ : Matrix (Fin 2) (Fin 2) F → ℂ) : Matrix (Fin 2) (Fin 2) F → ℂ :=
  fun M => Φ (1 + s • (M - 1))

theorem dil_one (s : F) (Φ : Matrix (Fin 2) (Fin 2) F → ℂ) : dil s Φ 1 = Φ 1 := by
  simp [dil]

theorem chartArg_dilate (s t : F) (hs : s ≠ 0) (q : Fˣ × F) :
    chartArg (s ^ 2 * t) (Units.mk0 s hs * q.1, s * q.2) = 1 + s • (chartArg t q - 1) := by
  obtain ⟨b, a⟩ := q
  have hb : ((b : Fˣ) : F) ≠ 0 := b.ne_zero
  simp only [chartArg, Units.val_mul, Units.val_mk0, add_sub_cancel_left]
  congr 1
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.smul_apply] <;> field_simp

end General

section Local

variable (K : Type) [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))

theorem exists_norm_pos_lt_one : ∃ π : v.adicCompletion K, π ≠ 0 ∧ ‖π‖ < 1 := by
  obtain ⟨x, hxv, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot v.ne_bot
  refine ⟨((algebraMap (𝓞 K) K x : K) : v.adicCompletion K), ?_, ?_⟩
  · intro h
    apply hx0
    have h' : (algebraMap K (v.adicCompletion K)) (algebraMap (𝓞 K) K x) = 0 := h
    rw [map_eq_zero] at h'
    exact (map_eq_zero_iff _ (FaithfulSMul.algebraMap_injective (𝓞 K) K)).1 h'
  · exact (NumberField.FinitePlace.norm_lt_one_iff_mem K v x).2 hxv

theorem secondCountableTopology_units : SecondCountableTopology (v.adicCompletion K)ˣ :=
  Units.isEmbedding_val₀.secondCountableTopology

attribute [local instance] secondCountableTopology_units

variable [MeasurableSpace (v.adicCompletion K)] [BorelSpace (v.adicCompletion K)]

theorem measure_smul_eq (μ : Measure (v.adicCompletion K)) [μ.IsAddHaarMeasure] {s : v.adicCompletion K}
    (hs : s ≠ 0) (E : Set (v.adicCompletion K)) : μ (s • E) = (‖s‖₊ : ℝ≥0∞) * μ E := by
  have h1 : (Units.mk0 s hs : (v.adicCompletion K)ˣ) • E = s • E := by
    ext x
    simp only [Set.mem_smul_set, Units.smul_mk0]
  rw [← h1, ← distribHaarChar_mul μ (Units.mk0 s hs) E]
  congr 2
  have := LanglandsTunnell.TateLocal.modulus_adicCompletion_eq_nnnorm K v s
  rwa [LanglandsTunnell.TateLocal.modulus_of_ne_zero hs] at this

theorem map_mul_left_eq_smul (μ : Measure (v.adicCompletion K)) [μ.IsAddHaarMeasure] {s : v.adicCompletion K}
    (hs : s ≠ 0) : Measure.map (fun y => s * y) μ = ((‖s‖₊ : ℝ≥0∞)⁻¹) • μ := by
  refine Measure.ext fun E hE => ?_
  rw [Measure.map_apply (measurable_const_mul s) hE, Measure.smul_apply, smul_eq_mul]
  have hpre : (fun y => s * y) ⁻¹' E = s⁻¹ • E := by
    have : (fun y : v.adicCompletion K => s * y) = fun y => s • y := rfl
    rw [this, Set.preimage_smul₀ hs]
  rw [hpre, measure_smul_eq K v μ (inv_ne_zero hs), nnnorm_inv, ENNReal.coe_inv (nnnorm_ne_zero_iff.2 hs)]

variable [MeasurableSpace (v.adicCompletion K)ˣ] [BorelSpace (v.adicCompletion K)ˣ]
  (μ : Measure (v.adicCompletion K)) [μ.IsAddHaarMeasure]
  (ν : Measure (v.adicCompletion K)ˣ) [ν.IsHaarMeasure]

def Jc (Φ : Matrix (Fin 2) (Fin 2) (v.adicCompletion K) → ℂ) (s : v.adicCompletion K) : ℂ :=
  ∫ q : (v.adicCompletion K)ˣ × v.adicCompletion K,
    Φ (1 + !![q.2, ((q.1 : (v.adicCompletion K)ˣ) : v.adicCompletion K);
      (s - q.2 ^ 2) / ((q.1 : (v.adicCompletion K)ˣ) : v.adicCompletion K), -q.2]) ∂(ν.prod μ)

theorem Jc_eq (Φ : Matrix (Fin 2) (Fin 2) (v.adicCompletion K) → ℂ) (s : v.adicCompletion K) :
    Jc K v μ ν Φ s = ∫ q, Φ (chartArg s q) ∂(ν.prod μ) := rfl

theorem Jc_sq_mul (Φ : Matrix (Fin 2) (Fin 2) (v.adicCompletion K) → ℂ) {s : v.adicCompletion K} (hs : s ≠ 0)
    (t : v.adicCompletion K) : Jc K v μ ν Φ (s ^ 2 * t) = (‖s‖ : ℂ) * Jc K v μ ν (dil s Φ) t := by

  set e : (v.adicCompletion K)ˣ × v.adicCompletion K ≃ₜ (v.adicCompletion K)ˣ × v.adicCompletion K :=
    (Homeomorph.mulLeft (Units.mk0 s hs)).prodCongr (Homeomorph.mulLeft₀ s hs) with he
  have he' : ∀ q, e q = (Units.mk0 s hs * q.1, s * q.2) := fun q => rfl
  have hmap : Measure.map e (ν.prod μ) = ((‖s‖₊ : ℝ≥0∞)⁻¹) • (ν.prod μ) := by
    have h1 : (e : (v.adicCompletion K)ˣ × v.adicCompletion K → (v.adicCompletion K)ˣ × v.adicCompletion K) =
        Prod.map (fun b => Units.mk0 s hs * b) (fun a => s * a) := by
      funext q; rfl
    rw [h1, ← Measure.map_prod_map _ _ (measurable_const_mul _) (measurable_const_mul _), map_mul_left_eq_self,
      map_mul_left_eq_smul K v μ hs, Measure.prod_smul_right]
  have hint : ∫ q, Φ (chartArg (s ^ 2 * t) q) ∂(ν.prod μ) =
      (∫ q, Φ (chartArg (s ^ 2 * t) (e q)) ∂(ν.prod μ)) * (‖s‖ : ℂ) := by
    have h2 : ∫ q, Φ (chartArg (s ^ 2 * t) (e q)) ∂(ν.prod μ) =
        ∫ q, Φ (chartArg (s ^ 2 * t) q) ∂(Measure.map e (ν.prod μ)) := by
      rw [← Homeomorph.toMeasurableEquiv_coe, integral_map_equiv]
    rw [h2, hmap, integral_smul_measure, ENNReal.toReal_inv, ENNReal.coe_toReal, coe_nnnorm, Complex.real_smul,
      Complex.ofReal_inv]
    have hn : (‖s‖ : ℂ) ≠ 0 := by exact_mod_cast norm_ne_zero_iff.2 hs
    field_simp
  rw [Jc_eq, Jc_eq, hint, mul_comm]
  congr 1
  refine integral_congr_ae (ae_of_all _ fun q => ?_)
  simp only [he', chartArg_dilate s t hs q, dil]

def chi : Matrix (Fin 2) (Fin 2) (v.adicCompletion K) → ℂ :=
  {M | ∀ i j, ‖(M - 1) i j‖ ≤ 1}.indicator fun _ => 1

theorem chi_one : chi K v 1 = 1 := by
  simp [chi]

theorem chi_of_mem {M : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)} (h : ∀ i j, ‖(M - 1) i j‖ ≤ 1) :
    chi K v M = 1 := Set.indicator_of_mem (by exact h) _

theorem chi_of_not_mem {M : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)} (h : ¬ ∀ i j, ‖(M - 1) i j‖ ≤ 1) :
    chi K v M = 0 := Set.indicator_of_notMem (by exact h) _

theorem dil_chi_add {s : v.adicCompletion K} (hs1 : ‖s‖ ≤ 1) (M E : Matrix (Fin 2) (Fin 2) (v.adicCompletion K))
    (hE : ∀ i j, ‖E i j‖ ≤ 1) : dil s (chi K v) (M + E) = dil s (chi K v) M := by
  simp only [dil]
  have key : (∀ i j, ‖((1 : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) + s • (M + E - 1) - 1) i j‖ ≤ 1) ↔
      ∀ i j, ‖((1 : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) + s • (M - 1) - 1) i j‖ ≤ 1 := by
    have hsE : ∀ i j, ‖(s • E) i j‖ ≤ 1 := fun i j => by
      rw [Matrix.smul_apply, smul_eq_mul, norm_mul]
      exact mul_le_one₀ hs1 (norm_nonneg _) (hE i j)
    have e1 : (1 : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) + s • (M + E - 1) - 1 = s • (M - 1) + s • E := by
      rw [add_sub_cancel_left, show M + E - 1 = (M - 1) + E by abel, smul_add]
    have e2 : (1 : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) + s • (M - 1) - 1 = s • (M - 1) := by
      rw [add_sub_cancel_left]
    rw [e1, e2]
    constructor
    · intro h i j
      have : (s • (M - 1)) i j = (s • (M - 1) + s • E) i j - (s • E) i j := by simp
      rw [this, sub_eq_add_neg]
      exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le (h i j) (by rw [norm_neg]; exact hsE i j))
    · intro h i j
      rw [Matrix.add_apply]
      exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le (h i j) (hsE i j))
  by_cases h : ∀ i j, ‖((1 : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) + s • (M - 1) - 1) i j‖ ≤ 1
  · rw [chi_of_mem K v h, chi_of_mem K v (key.2 h)]
  · rw [chi_of_not_mem K v h, chi_of_not_mem K v (fun h' => h (key.1 h'))]

theorem dil_chi_support {s : v.adicCompletion K} (hs : s ≠ 0) (hs1 : ‖s‖ ≤ 1)
    (M : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) (h : dil s (chi K v) M ≠ 0) (i j : Fin 2) :
    ‖M i j‖ ≤ ‖s‖⁻¹ := by
  simp only [dil] at h
  have hmem : ∀ i j, ‖((1 : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) + s • (M - 1) - 1) i j‖ ≤ 1 := by
    by_contra hn
    exact h (chi_of_not_mem K v hn)
  have h1 := hmem i j
  rw [add_sub_cancel_left, Matrix.smul_apply, smul_eq_mul, norm_mul] at h1
  have hs' : 0 < ‖s‖ := norm_pos_iff.2 hs
  have h2 : ‖(M - 1) i j‖ ≤ ‖s‖⁻¹ :=
    calc ‖(M - 1) i j‖ = ‖s‖⁻¹ * (‖s‖ * ‖(M - 1) i j‖) := by field_simp
      _ ≤ ‖s‖⁻¹ * 1 := by gcongr
      _ = ‖s‖⁻¹ := mul_one _
  have h3 : M i j = (M - 1) i j + (1 : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) i j := by simp
  rw [h3]
  refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le h2 ?_)
  have h1le : ‖(1 : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) i j‖ ≤ 1 := by
    fin_cases i <;> fin_cases j <;> simp
  exact h1le.trans (one_le_inv₀ hs' |>.2 hs1)

def Inv (δ : ℝ) (Φ : Matrix (Fin 2) (Fin 2) (v.adicCompletion K) → ℂ) : Prop :=
  ∀ M E : Matrix (Fin 2) (Fin 2) (v.adicCompletion K), (∀ i j, ‖E i j‖ ≤ δ) → Φ (M + E) = Φ M

def Supp (B : ℝ) (Φ : Matrix (Fin 2) (Fin 2) (v.adicCompletion K) → ℂ) : Prop :=
  ∀ M : Matrix (Fin 2) (Fin 2) (v.adicCompletion K), Φ M ≠ 0 → ∀ i j, ‖M i j‖ ≤ B

variable {K v} in
theorem Inv.mono {δ δ' : ℝ} {Φ : Matrix (Fin 2) (Fin 2) (v.adicCompletion K) → ℂ} (h : Inv K v δ Φ)
    (hδ : δ' ≤ δ) : Inv K v δ' Φ :=
  fun M E hE => h M E fun i j => (hE i j).trans hδ

variable {K v} in
theorem Supp.mono {B B' : ℝ} {Φ : Matrix (Fin 2) (Fin 2) (v.adicCompletion K) → ℂ} (h : Supp K v B Φ)
    (hB : B ≤ B') : Supp K v B' Φ :=
  fun M hM i j => (h M hM i j).trans hB

theorem dil_one_eq (Φ : Matrix (Fin 2) (Fin 2) (v.adicCompletion K) → ℂ) : dil 1 Φ = Φ := by
  funext M; simp [dil]

theorem inv_dil_chi {s : v.adicCompletion K} (hs1 : ‖s‖ ≤ 1) {δ : ℝ} (hδ1 : δ ≤ 1) :
    Inv K v δ (dil s (chi K v)) :=
  fun M E hE => dil_chi_add K v hs1 M E fun i j => (hE i j).trans hδ1

theorem inv_chi {δ : ℝ} (hδ1 : δ ≤ 1) : Inv K v δ (chi K v) := by
  have := inv_dil_chi K v (s := 1) (by rw [norm_one]) hδ1
  rwa [dil_one_eq] at this

theorem supp_dil_chi {s : v.adicCompletion K} (hs : s ≠ 0) (hs1 : ‖s‖ ≤ 1) :
    Supp K v ‖s‖⁻¹ (dil s (chi K v)) :=
  fun M hM i j => dil_chi_support K v hs hs1 M hM i j

theorem supp_chi : Supp K v 1 (chi K v) := by
  have := supp_dil_chi K v (s := 1) one_ne_zero (by rw [norm_one])
  rwa [dil_one_eq, norm_one, inv_one] at this

def alpha (t : v.adicCompletion K) : ℂ := Jc K v μ ν (chi K v) t - Jc K v μ ν (chi K v) 0

theorem expansion_at {δ' B' : ℝ} (hδ' : 0 < δ') (hδ'1 : δ' ≤ 1) (hB' : 1 ≤ B') :
    ∃ ε : ℝ, 0 < ε ∧ ∀ t : v.adicCompletion K, ‖t‖ < ε → ¬ IsSquare t →
      alpha K v μ ν t ≠ 0 ∧
      ∀ Φ : Matrix (Fin 2) (Fin 2) (v.adicCompletion K) → ℂ, Inv K v δ' Φ → Supp K v B' Φ →
        Jc K v μ ν Φ t = Jc K v μ ν Φ 0 + alpha K v μ ν t * Φ 1 := by
  obtain ⟨ε, hε, h⟩ :=
    AutomorphicForm.exists_forall_integral_affineChart_eq_add_mul_apply_one_of_not_isSquare K v μ ν δ' B' hδ'
  refine ⟨ε, hε, fun t ht hts => ?_⟩
  obtain ⟨α', hα'0, hexp⟩ := h t ht hts
  have hχ := hexp (chi K v) (inv_chi K v hδ'1) ((supp_chi K v).mono hB') (Jc K v μ ν (chi K v)) fun s => rfl
  rw [chi_one, mul_one] at hχ
  have hα : alpha K v μ ν t = α' := by
    unfold alpha; rw [hχ]; ring
  refine ⟨hα ▸ hα'0, fun Φ hΦi hΦs => ?_⟩
  rw [hα]
  exact hexp Φ hΦi hΦs (Jc K v μ ν Φ) fun s => rfl

theorem not_isSquare_sq_mul {t u : v.adicCompletion K} (ht : ¬ IsSquare t) (hu : u ≠ 0) :
    ¬ IsSquare (u ^ 2 * t) := by
  rintro ⟨r, hr⟩
  apply ht
  refine ⟨r / u, ?_⟩
  field_simp
  linear_combination hr

theorem alpha_sq_mul_step {π : v.adicCompletion K} (hπ0 : π ≠ 0) (hπ1 : ‖π‖ < 1) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ t s : v.adicCompletion K, ‖t‖ < ε₀ → ¬ IsSquare t → s ≠ 0 → ‖π‖ ≤ ‖s‖ → ‖s‖ ≤ 1 →
      alpha K v μ ν (s ^ 2 * t) = (‖s‖ : ℂ) * alpha K v μ ν t := by
  have hπpos : 0 < ‖π‖ := norm_pos_iff.2 hπ0
  obtain ⟨ε₀, hε₀, h⟩ := expansion_at K v μ ν (δ' := 1) (B' := ‖π‖⁻¹) one_pos le_rfl (one_le_inv₀ hπpos |>.2 hπ1.le)
  refine ⟨ε₀, hε₀, fun t s ht hts hs hπs hs1 => ?_⟩
  obtain ⟨-, hexp⟩ := h t ht hts
  have hsupp : Supp K v ‖π‖⁻¹ (dil s (chi K v)) :=
    (supp_dil_chi K v hs hs1).mono ((inv_le_inv₀ (norm_pos_iff.2 hs) hπpos).2 hπs)
  have h1 := hexp (dil s (chi K v)) (inv_dil_chi K v hs1 le_rfl) hsupp
  rw [dil_one, chi_one, mul_one] at h1
  have h2 : Jc K v μ ν (chi K v) 0 = (‖s‖ : ℂ) * Jc K v μ ν (dil s (chi K v)) 0 := by
    have := Jc_sq_mul K v μ ν (chi K v) hs 0
    rwa [mul_zero] at this
  have eL : alpha K v μ ν (s ^ 2 * t) = Jc K v μ ν (chi K v) (s ^ 2 * t) - Jc K v μ ν (chi K v) 0 := rfl
  have eR : alpha K v μ ν t = Jc K v μ ν (chi K v) t - Jc K v μ ν (chi K v) 0 := rfl
  rw [eL, Jc_sq_mul K v μ ν (chi K v) hs t, h1, h2, eR, h2]
  ring

theorem alpha_sq_mul :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ t s : v.adicCompletion K, ‖t‖ < ε₀ → ¬ IsSquare t → s ≠ 0 → ‖s‖ ≤ 1 →
      alpha K v μ ν (s ^ 2 * t) = (‖s‖ : ℂ) * alpha K v μ ν t := by
  obtain ⟨π, hπ0, hπ1⟩ := exists_norm_pos_lt_one K v
  have hπpos : 0 < ‖π‖ := norm_pos_iff.2 hπ0
  obtain ⟨ε₀, hε₀, hstep⟩ := alpha_sq_mul_step K v μ ν hπ0 hπ1
  refine ⟨ε₀, hε₀, ?_⟩

  have hiter : ∀ n : ℕ, ∀ t : v.adicCompletion K, ‖t‖ < ε₀ → ¬ IsSquare t →
      ∀ w : v.adicCompletion K, w ≠ 0 → ‖π‖ ≤ ‖w‖ → ‖w‖ ≤ 1 →
        alpha K v μ ν ((π ^ n * w) ^ 2 * t) = (‖π ^ n * w‖ : ℂ) * alpha K v μ ν t := by
    intro n
    induction n with
    | zero =>
      intro t ht hts w hw0 hw hw1
      rw [pow_zero, one_mul]
      exact hstep t w ht hts hw0 hw hw1
    | succ n ih =>
      intro t ht hts w hw0 hw hw1
      have hu : π ^ n * w ≠ 0 := mul_ne_zero (pow_ne_zero _ hπ0) hw0
      have hnorm : ‖π ^ n * w‖ ≤ 1 := by
        rw [norm_mul, norm_pow]
        exact mul_le_one₀ (pow_le_one₀ (norm_nonneg _) hπ1.le) (norm_nonneg _) hw1
      have ht' : ‖(π ^ n * w) ^ 2 * t‖ < ε₀ := by
        rw [norm_mul, norm_pow]
        calc ‖π ^ n * w‖ ^ 2 * ‖t‖ ≤ 1 * ‖t‖ := by
              gcongr; exact pow_le_one₀ (norm_nonneg _) hnorm
          _ = ‖t‖ := one_mul _
          _ < ε₀ := ht
      have e : (π ^ (n + 1) * w) ^ 2 * t = π ^ 2 * ((π ^ n * w) ^ 2 * t) := by ring
      rw [e, hstep _ π ht' (not_isSquare_sq_mul K v hts hu) hπ0 le_rfl hπ1.le, ih t ht hts w hw0 hw hw1,
        ← mul_assoc, ← Complex.ofReal_mul, ← norm_mul]
      congr 2; ring
  intro t s ht hts hs hs1

  have hspos : 0 < ‖s‖ := norm_pos_iff.2 hs
  have hex : ∃ n : ℕ, ‖π‖ ^ (n + 1) < ‖s‖ := by
    have hlim : Tendsto (fun n : ℕ => ‖π‖ ^ (n + 1)) atTop (𝓝 0) :=
      (tendsto_pow_atTop_nhds_zero_of_lt_one (norm_nonneg _) hπ1).comp (tendsto_add_atTop_nat 1)
    exact ((hlim.eventually (gt_mem_nhds hspos)).exists)
  classical
  obtain ⟨n, hn1, hn2⟩ : ∃ n : ℕ, ‖π‖ ^ (n + 1) < ‖s‖ ∧ ‖s‖ ≤ ‖π‖ ^ n := by
    refine ⟨Nat.find hex, Nat.find_spec hex, ?_⟩
    rcases Nat.eq_zero_or_pos (Nat.find hex) with h0 | hpos
    · rw [h0, pow_zero]; exact hs1
    · have hm := Nat.find_min hex (m := Nat.find hex - 1) (by omega)
      have e : Nat.find hex - 1 + 1 = Nat.find hex := by omega
      rw [e] at hm
      exact not_lt.1 hm
  set w := s * (π ^ n)⁻¹ with hw
  have hπn : π ^ n ≠ 0 := pow_ne_zero _ hπ0
  have hsw : s = π ^ n * w := by rw [hw]; field_simp
  have hw0 : w ≠ 0 := by rw [hw]; exact mul_ne_zero hs (inv_ne_zero hπn)
  have hπnpos : 0 < ‖π‖ ^ n := pow_pos hπpos n
  have hwn : ‖w‖ = ‖s‖ / ‖π‖ ^ n := by rw [hw, norm_mul, norm_inv, norm_pow, div_eq_mul_inv]
  have hw1 : ‖w‖ ≤ 1 := by rw [hwn, div_le_one hπnpos]; exact hn2
  have hwπ : ‖π‖ ≤ ‖w‖ := by
    rw [hwn, le_div_iff₀ hπnpos, ← pow_succ']
    exact hn1.le
  rw [hsw]
  exact hiter n t ht hts w hw0 hwπ hw1

theorem main :
    ∃ α : v.adicCompletion K → ℂ,
      (∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ t s : v.adicCompletion K, ‖t‖ < ε₀ → ¬ IsSquare t → s ≠ 0 → ‖s‖ ≤ 1 →
          α (s ^ 2 * t) = (‖s‖ : ℂ) * α t) ∧
      ∀ δ B : ℝ, 0 < δ →
        ∃ ε : ℝ, 0 < ε ∧ ∀ t : v.adicCompletion K, ‖t‖ < ε → ¬ IsSquare t →
          α t ≠ 0 ∧
          ∀ Φ : Matrix (Fin 2) (Fin 2) (v.adicCompletion K) → ℂ,
            (∀ M E : Matrix (Fin 2) (Fin 2) (v.adicCompletion K), (∀ i j, ‖E i j‖ ≤ δ) → Φ (M + E) = Φ M) →
            (∀ M : Matrix (Fin 2) (Fin 2) (v.adicCompletion K), Φ M ≠ 0 → ∀ i j, ‖M i j‖ ≤ B) →
            ∀ J : v.adicCompletion K → ℂ,
              (∀ s : v.adicCompletion K, J s = ∫ q : (v.adicCompletion K)ˣ × v.adicCompletion K,
                Φ (1 + !![q.2, ((q.1 : (v.adicCompletion K)ˣ) : v.adicCompletion K);
                  (s - q.2 ^ 2) / ((q.1 : (v.adicCompletion K)ˣ) : v.adicCompletion K), -q.2]) ∂(ν.prod μ)) →
              J t = J 0 + α t * Φ 1 := by
  refine ⟨alpha K v μ ν, alpha_sq_mul K v μ ν, fun δ B hδ => ?_⟩
  obtain ⟨ε, hε, h⟩ := expansion_at K v μ ν (δ' := min δ 1) (B' := max B 1) (lt_min hδ one_pos)
    (min_le_right _ _) (le_max_right _ _)
  refine ⟨ε, hε, fun t ht hts => ?_⟩
  obtain ⟨hα0, hexp⟩ := h t ht hts
  refine ⟨hα0, fun Φ hΦi hΦs J hJ => ?_⟩
  have hi : Inv K v (min δ 1) Φ := Inv.mono (fun M E hE => hΦi M E hE) (min_le_left _ _)
  have hs : Supp K v (max B 1) Φ := Supp.mono (fun M hM i j => hΦs M hM i j) (le_max_left _ _)
  have := hexp Φ hi hs
  rw [hJ t, hJ 0]
  exact this

end Local

end P2mIdentityGermHomog

end

open MeasureTheory NumberField
open IsDedekindDomain

theorem solution
    (K : Type) [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))
    [MeasurableSpace (v.adicCompletion K)] [BorelSpace (v.adicCompletion K)]
    (μ : Measure (v.adicCompletion K)) [μ.IsAddHaarMeasure]
    [MeasurableSpace (v.adicCompletion K)ˣ] [BorelSpace (v.adicCompletion K)ˣ]
    (ν : Measure (v.adicCompletion K)ˣ) [ν.IsHaarMeasure] :
    ∃ α : v.adicCompletion K → ℂ,
      (∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ t s : v.adicCompletion K, ‖t‖ < ε₀ → ¬ IsSquare t → s ≠ 0 → ‖s‖ ≤ 1 →
          α (s ^ 2 * t) = (‖s‖ : ℂ) * α t) ∧
      ∀ δ B : ℝ, 0 < δ →
        ∃ ε : ℝ, 0 < ε ∧ ∀ t : v.adicCompletion K, ‖t‖ < ε → ¬ IsSquare t →
          α t ≠ 0 ∧
          ∀ Φ : Matrix (Fin 2) (Fin 2) (v.adicCompletion K) → ℂ,
            (∀ M E : Matrix (Fin 2) (Fin 2) (v.adicCompletion K), (∀ i j, ‖E i j‖ ≤ δ) → Φ (M + E) = Φ M) →
            (∀ M : Matrix (Fin 2) (Fin 2) (v.adicCompletion K), Φ M ≠ 0 → ∀ i j, ‖M i j‖ ≤ B) →
            ∀ J : v.adicCompletion K → ℂ,
              (∀ s : v.adicCompletion K, J s = ∫ q : (v.adicCompletion K)ˣ × v.adicCompletion K,
                Φ (1 + !![q.2, ((q.1 : (v.adicCompletion K)ˣ) : v.adicCompletion K);
                  (s - q.2 ^ 2) / ((q.1 : (v.adicCompletion K)ˣ) : v.adicCompletion K), -q.2]) ∂(ν.prod μ)) →
              J t = J 0 + α t * Φ 1 :=
  P2mIdentityGermHomog.main K v μ ν

end S_AutomorphicForm_exists_forall_sq_mul_eq_norm_mul_and_forall_integral_affineChart_eq_add_mul_apply_one_of_not_isSquare
end P2MW
export P2MW.S_AutomorphicForm_exists_forall_sq_mul_eq_norm_mul_and_forall_integral_affineChart_eq_add_mul_apply_one_of_not_isSquare (solution)
