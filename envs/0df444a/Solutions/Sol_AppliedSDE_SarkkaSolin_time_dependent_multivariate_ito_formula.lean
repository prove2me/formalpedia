-- Prove2me | solution 1 for AppliedSDE.SarkkaSolin.time_dependent_multivariate_ito_formula
-- status  : ACCEPTED   (prove)
-- author  : @Xeroth
-- created : 2026-11-23T01:51:47.990864+00:00
-- url     : https://prove2.me/submissions/8b549f01-2d88-4b22-8479-57efa5e3ac55

import Definitions.Def_KLSModular_LevyStochCalc_Brownian_VectorItoFormula
import Definitions.Def_KLSModular_LevyStochCalc_Brownian_ItoL2CompletionApi
import Theorems.Thm_LevyStochCalc_Brownian_Ito_IsVectorItoVersion_itoFormula_readable
import Theorems.Thm_LevyStochCalc_Brownian_Ito_stochasticIntegralBrownian_indicator_Ioc_readable
import Theorems.Thm_LevyStochCalc_Brownian_Ito_exists_stochasticIntegralBrownian_finsetSum_readable
import Theorems.Thm_ItoLemma_continuous_adapted_composition_progressive
open MeasureTheory ProbabilityTheory LevyStochCalc.Brownian.Ito
open scoped NNReal ENNReal Topology BigOperators
open LevyStochCalc

theorem grid_sum_eval {T : ℝ} (hT : 0 < T) (m : ℕ) {s : ℝ} (hs : s ∈ Set.Ioc 0 T) :
    ∃ j, j < m + 1 ∧ |unifGrid T (m+1) j - s| ≤ T / ((m:ℝ) + 1) ∧ ∀ w : ℕ → ℝ,
      ∑ i ∈ Finset.range (m+1),
        (Set.Ioc (unifGrid T (m+1) i) (unifGrid T (m+1) (i+1))).indicator (fun _ => (1:ℝ)) s
          * w i = w j := by
  have hN : (0:ℝ) < (m:ℝ) + 1 := by positivity
  obtain ⟨hs0, hsT⟩ := hs
  set u := s * ((m:ℝ) + 1) / T with hu
  have hu0 : 0 < u := by positivity
  have huN : u ≤ (m:ℝ) + 1 := by
    rw [hu, div_le_iff₀ hT]; nlinarith
  have key : ∀ i : ℕ, s ∈ Set.Ioc (unifGrid T (m+1) i) (unifGrid T (m+1) (i+1)) ↔
      ⌈u⌉₊ = i + 1 := by
    intro i
    rw [Nat.ceil_eq_iff (by omega)]
    simp only [unifGrid, Set.mem_Ioc, Nat.add_sub_cancel]
    push_cast
    rw [div_lt_iff₀ hN, le_div_iff₀ hN, hu, lt_div_iff₀ hT, div_le_iff₀ hT]
  have hc1 : 1 ≤ ⌈u⌉₊ := Nat.one_le_iff_ne_zero.mpr (Nat.pos_iff_ne_zero.mp (Nat.ceil_pos.mpr hu0))
  have hcN : ⌈u⌉₊ ≤ m + 1 := by
    have := Nat.ceil_le.mpr (show u ≤ ((m + 1 : ℕ) : ℝ) by push_cast; exact huN)
    exact this
  refine ⟨⌈u⌉₊ - 1, by omega, ?_, ?_⟩
  · have hj := (key (⌈u⌉₊ - 1)).mpr (by omega)
    obtain ⟨h1, h2⟩ := hj
    have hd : unifGrid T (m+1) (⌈u⌉₊ - 1 + 1) - unifGrid T (m+1) (⌈u⌉₊ - 1) = T / ((m:ℝ)+1) := by
      simp only [unifGrid]; push_cast; field_simp; ring
    rw [abs_sub_comm, abs_of_pos (by linarith)]
    linarith
  · intro w
    rw [Finset.sum_eq_single (⌈u⌉₊ - 1)]
    · rw [Set.indicator_of_mem ((key _).mpr (by omega)), one_mul]
    · intro i _ hi
      rw [Set.indicator_of_notMem, zero_mul]
      intro hm
      have := (key i).mp hm
      omega
    · intro h
      exact absurd (Finset.mem_range.mpr (by omega)) h

theorem grid_sum_abs_le {T : ℝ} (hT : 0 < T) (m : ℕ) (s : ℝ) (w : ℕ → ℝ) {M : ℝ} (hM0 : 0 ≤ M)
    (hw : ∀ i, |w i| ≤ M) :
    |∑ i ∈ Finset.range (m+1),
        (Set.Ioc (unifGrid T (m+1) i) (unifGrid T (m+1) (i+1))).indicator (fun _ => (1:ℝ)) s
          * w i| ≤ M := by
  by_cases hs : s ∈ Set.Ioc 0 T
  · obtain ⟨j, -, -, hj⟩ := grid_sum_eval hT m hs
    rw [hj w]; exact hw j
  · rw [Finset.sum_eq_zero]
    · simpa using hM0
    · intro i hi
      rw [Set.indicator_of_notMem, zero_mul]
      intro hm
      apply hs
      have hi' : i + 1 ≤ m + 1 := by simpa [Finset.mem_range] using hi
      have hN : (0:ℝ) < ((m+1 : ℕ) : ℝ) := by positivity
      refine ⟨lt_of_le_of_lt ?_ hm.1, le_trans hm.2 ?_⟩
      · simp only [unifGrid]; positivity
      · simp only [unifGrid]
        rw [div_le_iff₀ hN]
        have : ((i+1 : ℕ) : ℝ) ≤ ((m+1 : ℕ) : ℝ) := by exact_mod_cast hi'
        nlinarith

theorem grid_tendsto {T : ℝ} (hT : 0 < T) {s : ℝ} (hs : s ∈ Set.Ioc 0 T) (v : ℝ → ℝ) {L : ℝ}
    (hv : Filter.Tendsto v (𝓝 s) (𝓝 L)) :
    Filter.Tendsto (fun m : ℕ => ∑ i ∈ Finset.range (m+1),
        (Set.Ioc (unifGrid T (m+1) i) (unifGrid T (m+1) (i+1))).indicator (fun _ => (1:ℝ)) s
          * v (unifGrid T (m+1) i)) Filter.atTop (𝓝 L) := by
  choose j _ hj2 hj3 using fun m => grid_sum_eval hT m hs
  have hz : Filter.Tendsto (fun m : ℕ => T / ((m:ℝ) + 1)) Filter.atTop (𝓝 0) := by
    have := (tendsto_one_div_add_atTop_nhds_zero_nat).const_mul T
    simpa [div_eq_mul_inv] using this
  have hg : Filter.Tendsto (fun m => unifGrid T (m+1) (j m)) Filter.atTop (𝓝 s) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    refine squeeze_zero (fun _ => norm_nonneg _) (fun m => ?_) hz
    rw [Real.norm_eq_abs]; exact hj2 m
  exact (hv.comp hg).congr (fun m => (hj3 m (fun i => v (unifGrid T (m+1) i))).symm)

theorem bdd_integrableOn {g : ℝ → ℝ} (hg : Measurable g) {M : ℝ} (hM : ∀ s, |g s| ≤ M) (a b : ℝ) :
    MeasureTheory.IntegrableOn g (Set.Ioc a b) volume := by
  haveI : IsFiniteMeasure (volume.restrict (Set.Ioc a b)) :=
    ⟨by rw [Measure.restrict_apply_univ, Real.volume_Ioc]; exact ENNReal.ofReal_lt_top⟩
  exact (integrable_const M).mono' hg.aestronglyMeasurable
    (ae_of_all _ fun s => by rw [Real.norm_eq_abs]; exact hM s)

theorem det_window {T : ℝ} (hT : 0 < T) (v : ℝ → ℝ → ℝ) {M : ℝ} (hM0 : 0 ≤ M)
    (hM : ∀ c s, |v c s| ≤ M) (hmeas : ∀ c, Measurable (v c))
    (hconv : ∀ s, Filter.Tendsto (fun c => v c s) (𝓝 s) (𝓝 (v s s))) :
    Filter.Tendsto (fun m : ℕ => ∑ i ∈ Finset.range (m+1),
        ((∫ s in Set.Ioc (0:ℝ) (unifGrid T (m+1) (i+1)), v (unifGrid T (m+1) i) s ∂volume)
          - ∫ s in Set.Ioc (0:ℝ) (unifGrid T (m+1) i), v (unifGrid T (m+1) i) s ∂volume))
      Filter.atTop (𝓝 (∫ s in Set.Ioc (0:ℝ) T, v s s ∂volume)) := by
  set F : ℕ → ℝ → ℝ := fun m s => ∑ i ∈ Finset.range (m+1),
        (Set.Ioc (unifGrid T (m+1) i) (unifGrid T (m+1) (i+1))).indicator (fun _ => (1:ℝ)) s
          * v (unifGrid T (m+1) i) s with hF
  have hind : ∀ a b : ℝ, Measurable ((Set.Ioc a b).indicator (fun _ => (1:ℝ))) :=
    fun a b => measurable_const.indicator measurableSet_Ioc
  have hFm : ∀ m, Measurable (F m) := fun m =>
    Finset.measurable_sum _ (fun i _ => (hind _ _).mul (hmeas _))
  have hlim : Filter.Tendsto (fun m => ∫ s in Set.Ioc (0:ℝ) T, F m s ∂volume) Filter.atTop
      (𝓝 (∫ s in Set.Ioc (0:ℝ) T, v s s ∂volume)) := by
    haveI : IsFiniteMeasure (volume.restrict (Set.Ioc (0:ℝ) T)) :=
      ⟨by rw [Measure.restrict_apply_univ, Real.volume_Ioc]; exact ENNReal.ofReal_lt_top⟩
    refine tendsto_integral_of_dominated_convergence (fun _ => M)
      (fun m => (hFm m).aestronglyMeasurable) (integrable_const M) (fun m => ?_) ?_
    · exact ae_of_all _ fun s => by
        rw [Real.norm_eq_abs]
        exact grid_sum_abs_le hT m s _ hM0 (fun i => hM _ _)
    · filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
      exact grid_tendsto hT hs (fun c => v c s) (hconv s)
  refine hlim.congr (fun m => ?_)
  rw [hF]
  simp only
  rw [integral_finset_sum]
  · refine Finset.sum_congr rfl (fun i hi => ?_)
    have hi' : i + 1 ≤ m + 1 := by simpa [Finset.mem_range] using hi
    have hN : (0:ℝ) < ((m+1 : ℕ) : ℝ) := by positivity
    have ha : 0 ≤ unifGrid T (m+1) i := by simp only [unifGrid]; positivity
    have hab : unifGrid T (m+1) i ≤ unifGrid T (m+1) (i+1) := by
      simp only [unifGrid]; gcongr; push_cast; linarith
    have hbT : unifGrid T (m+1) (i+1) ≤ T := by
      simp only [unifGrid]
      rw [div_le_iff₀ hN]
      have : ((i+1 : ℕ) : ℝ) ≤ ((m+1 : ℕ) : ℝ) := by exact_mod_cast hi'
      nlinarith
    have e1 : ∀ s, (Set.Ioc (unifGrid T (m+1) i) (unifGrid T (m+1) (i+1))).indicator
        (fun _ => (1:ℝ)) s * v (unifGrid T (m+1) i) s
        = (Set.Ioc (unifGrid T (m+1) i) (unifGrid T (m+1) (i+1))).indicator
          (v (unifGrid T (m+1) i)) s := by
      intro s
      by_cases h : s ∈ Set.Ioc (unifGrid T (m+1) i) (unifGrid T (m+1) (i+1))
      · simp [Set.indicator_of_mem h]
      · simp [Set.indicator_of_notMem h]
    simp_rw [e1]
    rw [setIntegral_indicator measurableSet_Ioc,
      Set.inter_eq_right.mpr (Set.Ioc_subset_Ioc ha hbT),
      ← intervalIntegral.integral_of_le (ha.trans hab), ← intervalIntegral.integral_of_le ha,
      ← intervalIntegral.integral_of_le hab]
    rw [intervalIntegral.integral_interval_sub_left]
    · exact (intervalIntegrable_iff_integrableOn_Ioc_of_le (ha.trans hab)).mpr
        (bdd_integrableOn (hmeas _) (hM _) _ _)
    · exact (intervalIntegrable_iff_integrableOn_Ioc_of_le ha).mpr
        (bdd_integrableOn (hmeas _) (hM _) _ _)
  · intro i _
    exact bdd_integrableOn (g := fun s => (Set.Ioc (unifGrid T (m+1) i)
        (unifGrid T (m+1) (i+1))).indicator (fun _ => (1:ℝ)) s * v (unifGrid T (m+1) i) s)
      ((hind _ _).mul (hmeas _))
      (fun s => by
        rw [abs_mul]
        by_cases h : s ∈ Set.Ioc (unifGrid T (m+1) i) (unifGrid T (m+1) (i+1))
        · simp only [Set.indicator_of_mem h, abs_one, one_mul]; exact hM _ _
        · simp only [Set.indicator_of_notMem h, abs_zero, zero_mul]; exact hM0) _ _

theorem pm_det {Ω : Type*} [MeasurableSpace Ω] (ℱ : Filtration ℝ ‹MeasurableSpace Ω›)
    {g : ℝ → ℝ} (hg : Measurable g) :
    Probability.ProgressivelyMeasurable ℱ (fun (_ : Ω) (s : ℝ) => g s) := by
  intro t
  exact ((hg.indicator measurableSet_Iic).comp measurable_snd).stronglyMeasurable

theorem hq_of_bdd {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    (G : Ω → ℝ → ℝ) {M : ℝ} (hG : ∀ ω s, |G ω s| ≤ M) :
    ∀ T, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
      (‖G ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤ := by
  intro T _
  calc ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, (‖G ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P
      ≤ ∫⁻ _ω, ∫⁻ _s in Set.Icc (0 : ℝ) T, (ENNReal.ofReal M) ^ 2 ∂volume ∂P := by
        refine lintegral_mono fun ω => lintegral_mono fun s => ?_
        refine pow_le_pow_left₀ (zero_le) ?_ 2
        rw [← ENNReal.ofReal_coe_nnreal, coe_nnnorm]
        exact ENNReal.ofReal_le_ofReal (by rw [Real.norm_eq_abs]; exact hG ω s)
    _ < ⊤ := by
        simp only [lintegral_const, measure_univ, mul_one, Measure.restrict_apply_univ,
          Real.volume_Icc]
        exact ENNReal.mul_lt_top (ENNReal.pow_lt_top ENNReal.ofReal_lt_top) ENNReal.ofReal_lt_top

theorem tim_of_L2 {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    (Y U : ℕ → Ω → ℝ) (Z : Ω → ℝ) (hYU : ∀ m, Y m =ᵐ[P] U m) (hU : ∀ m, AEMeasurable (U m) P)
    (hZ : AEMeasurable Z P)
    (h : Filter.Tendsto (fun m => ∫⁻ ω, (‖U m ω - Z ω‖₊ : ℝ≥0∞) ^ 2 ∂P) Filter.atTop (𝓝 0)) :
    TendstoInMeasure P Y Filter.atTop Z := by
  refine TendstoInMeasure.congr' (f := U) (g := Z)
    (Filter.Eventually.of_forall fun m => (hYU m).symm) Filter.EventuallyEq.rfl ?_
  rw [tendstoInMeasure_iff_norm]
  intro ε hε
  have hε2 : ENNReal.ofReal (ε ^ 2) ≠ 0 := by
    rw [ne_eq, ENNReal.ofReal_eq_zero, not_le]; positivity
  have hlim := ENNReal.Tendsto.div_const h (Or.inr hε2)
  rw [ENNReal.zero_div] at hlim
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlim
    (fun _ => zero_le) (fun m => ?_)
  have hmeas : AEMeasurable (fun ω => (‖U m ω - Z ω‖₊ : ℝ≥0∞) ^ 2) P :=
    (((hU m).sub hZ).nnnorm.coe_nnreal_ennreal).pow_const 2
  refine le_trans (measure_mono ?_) (meas_ge_le_lintegral_div hmeas hε2 ENNReal.ofReal_ne_top)
  intro ω hω
  simp only [Set.mem_ofPred_eq] at hω ⊢
  rw [← ENNReal.ofReal_coe_nnreal, coe_nnnorm, ← ENNReal.ofReal_pow (norm_nonneg _)]
  exact ENNReal.ofReal_le_ofReal (pow_le_pow_left₀ hε.le hω 2)

noncomputable def winInt {Ω : Type*} (T : ℝ) (Φ : ℝ → Ω → ℝ → ℝ) (m i : ℕ) (ω : Ω) (s : ℝ) : ℝ :=
  (Set.Ioc (unifGrid T (m+1) i) (unifGrid T (m+1) (i+1))).indicator (fun _ => (1:ℝ)) s
    * Φ (unifGrid T (m+1) i) ω s

noncomputable def winSq {Ω : Type*} (T : ℝ) (Φ : ℝ → Ω → ℝ → ℝ) (Φi : Ω → ℝ → ℝ) (m : ℕ)
    (ω : Ω) (s : ℝ) : ℝ≥0∞ :=
  (‖(∑ i ∈ Finset.range (m+1), winInt T Φ m i ω s) - Φi ω s‖₊ : ℝ≥0∞) ^ 2

theorem stoch_window {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    (W : LevyStochCalc.Brownian.BrownianMotion P) (ℱ : Filtration ℝ ‹MeasurableSpace Ω›)
    (hℱ : LevyStochCalc.Brownian.IsBrownianFiltration W ℱ)
    (Φ : ℝ → Ω → ℝ → ℝ) (Φi : Ω → ℝ → ℝ)
    (hm : ∀ c, Measurable (Function.uncurry (Φ c)))
    (hp : ∀ c, Probability.ProgressivelyMeasurable ℱ (Φ c))
    (hq : ∀ c, ∀ T', 0 < T' → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T',
      (‖Φ c ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    (hmi : Measurable (Function.uncurry Φi))
    (hpi : Probability.ProgressivelyMeasurable ℱ Φi)
    (hqi : ∀ T', 0 < T' → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T',
      (‖Φi ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    {M : ℝ} (hM0 : 0 ≤ M) (hM : ∀ c ω s, |Φ c ω s| ≤ M) (hMi : ∀ ω s, |Φi ω s| ≤ M)
    (hconv : ∀ ω s, Filter.Tendsto (fun c => Φ c ω s) (𝓝 s) (𝓝 (Φi ω s)))
    {T : ℝ} (hT : 0 < T) :
    TendstoInMeasure P (fun (m : ℕ) (ω : Ω) => ∑ i ∈ Finset.range (m+1),
        (stochasticIntegralBrownian W ℱ hℱ (Φ (unifGrid T (m+1) i)) (hm _) (hp _) (hq _)
            (unifGrid T (m+1) (i+1)) ω
          - stochasticIntegralBrownian W ℱ hℱ (Φ (unifGrid T (m+1) i)) (hm _) (hp _) (hq _)
            (unifGrid T (m+1) i) ω))
      Filter.atTop (stochasticIntegralBrownian W ℱ hℱ Φi hmi hpi hqi T) := by
  have hind : ∀ a b : ℝ, Measurable ((Set.Ioc a b).indicator (fun _ => (1:ℝ))) :=
    fun a b => measurable_const.indicator measurableSet_Ioc
  have hindb : ∀ (a b s : ℝ) (x : ℝ), |x| ≤ M →
      |(Set.Ioc a b).indicator (fun _ => (1:ℝ)) s * x| ≤ M := by
    intro a b s x hx
    rw [abs_mul]
    by_cases h : s ∈ Set.Ioc a b
    · simp only [Set.indicator_of_mem h, abs_one, one_mul]; exact hx
    · simp only [Set.indicator_of_notMem h, abs_zero, zero_mul]; exact hM0
  have hψm : ∀ m i, Measurable (Function.uncurry (winInt T Φ m i)) := fun m i =>
    ((hind _ _).comp measurable_snd).mul (hm _)
  have hψp : ∀ m i, Probability.ProgressivelyMeasurable ℱ (winInt T Φ m i) := fun m i =>
    Probability.ProgressivelyMeasurable.mul
      (A := fun (_ : Ω) (s : ℝ) => (Set.Ioc (unifGrid T (m+1) i)
        (unifGrid T (m+1) (i+1))).indicator (fun _ => (1:ℝ)) s)
      (pm_det ℱ (hind _ _)) (hp _)
  have hψq : ∀ m i, ∀ T', 0 < T' → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T',
      (‖winInt T Φ m i ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤ := fun m i =>
    hq_of_bdd (winInt T Φ m i) (fun ω s => hindb _ _ _ _ (hM _ ω s))
  have hgrid : ∀ m i, i ∈ Finset.range (m+1) →
      0 ≤ unifGrid T (m+1) i ∧ unifGrid T (m+1) i < unifGrid T (m+1) (i+1) ∧
        unifGrid T (m+1) (i+1) ≤ T := by
    intro m i hi
    have hi' : i + 1 ≤ m + 1 := by simpa [Finset.mem_range] using hi
    have hN : (0:ℝ) < ((m+1 : ℕ) : ℝ) := by positivity
    refine ⟨by simp only [unifGrid]; positivity, ?_, ?_⟩
    · simp only [unifGrid]; gcongr; push_cast; linarith
    · simp only [unifGrid]
      rw [div_le_iff₀ hN]
      have : ((i+1 : ℕ) : ℝ) ≤ ((m+1 : ℕ) : ℝ) := by exact_mod_cast hi'
      nlinarith
  have hex : ∀ m, ∃ (hms : Measurable (Function.uncurry fun ω u => ∑ i ∈ Finset.range (m+1), winInt T Φ m i ω u))
      (hps : Probability.ProgressivelyMeasurable ℱ fun ω u => ∑ i ∈ Finset.range (m+1), winInt T Φ m i ω u)
      (hqs : ∀ T', 0 < T' → ∫⁻ ω, ∫⁻ u in Set.Icc (0 : ℝ) T',
        (‖∑ i ∈ Finset.range (m+1), winInt T Φ m i ω u‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤),
      stochasticIntegralBrownian W ℱ hℱ (fun ω u => ∑ i ∈ Finset.range (m+1), winInt T Φ m i ω u) hms hps hqs T
        =ᵐ[P] fun ω => ∑ i ∈ Finset.range (m+1),
          stochasticIntegralBrownian W ℱ hℱ (winInt T Φ m i) (hψm m i) (hψp m i) (hψq m i) T ω :=
    fun m => exists_stochasticIntegralBrownian_finsetSum_readable W ℱ hℱ (winInt T Φ m) (hψm m) (hψp m)
      (hψq m) (Finset.range (m+1)) hT
  choose hms hps hqs hsum using hex
  refine tim_of_L2 _ (fun m => stochasticIntegralBrownian W ℱ hℱ
      (fun ω u => ∑ i ∈ Finset.range (m+1), winInt T Φ m i ω u) (hms m) (hps m) (hqs m) T) _
    (fun m => ?_) (fun m => (stochasticIntegralBrownian_memLp W ℱ hℱ _ _ _ _ T).1.aemeasurable)
    (stochasticIntegralBrownian_memLp W ℱ hℱ _ _ _ _ T).1.aemeasurable ?_
  · -- window identity
    have hw : ∀ᵐ ω ∂P, ∀ i ∈ Finset.range (m+1),
        stochasticIntegralBrownian W ℱ hℱ (Φ (unifGrid T (m+1) i)) (hm _) (hp _) (hq _)
            (unifGrid T (m+1) (i+1)) ω
          - stochasticIntegralBrownian W ℱ hℱ (Φ (unifGrid T (m+1) i)) (hm _) (hp _) (hq _)
            (unifGrid T (m+1) i) ω
        = stochasticIntegralBrownian W ℱ hℱ (winInt T Φ m i) (hψm m i) (hψp m i) (hψq m i) T ω := by
      rw [Filter.eventually_all_finset]
      intro i hi
      obtain ⟨h0, hlt, hle⟩ := hgrid m i hi
      have := stochasticIntegralBrownian_indicator_Ioc_readable W ℱ hℱ
        (Φ (unifGrid T (m+1) i)) (hm _) (hp _) (hq _) h0 hlt (hψm m i) (hψp m i) (hψq m i) hT
      filter_upwards [this] with ω hω
      refine Eq.trans ?_ hω.symm
      rw [min_eq_left hle, min_eq_left (hlt.le.trans hle)]
    filter_upwards [hw, hsum m] with ω hω hs
    rw [hs]
    exact Finset.sum_congr rfl hω
  · -- L² convergence
    have hiso : ∀ m, ∫⁻ ω, (‖stochasticIntegralBrownian W ℱ hℱ
        (fun ω u => ∑ i ∈ Finset.range (m+1), winInt T Φ m i ω u) (hms m) (hps m) (hqs m) T ω
          - stochasticIntegralBrownian W ℱ hℱ Φi hmi hpi hqi T ω‖₊ : ℝ≥0∞) ^ 2 ∂P
        = ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, winSq T Φ Φi m ω s ∂volume ∂P :=
      fun m => isometry_diff_stochasticIntegralBrownian W ℱ hℱ _ _ (hms m) hmi (hps m) hpi
        (hqs m) hqi hT
    simp_rw [hiso]
    have hbd : ∀ m ω s, winSq T Φ Φi m ω s ≤ ENNReal.ofReal ((2 * M) ^ 2) := by
      intro m ω s
      have h1 : |∑ i ∈ Finset.range (m+1), winInt T Φ m i ω s| ≤ M :=
        grid_sum_abs_le hT m s (fun i => Φ (unifGrid T (m+1) i) ω s) hM0 (fun i => hM _ ω s)
      have hr : ‖(∑ i ∈ Finset.range (m+1), winInt T Φ m i ω s) - Φi ω s‖ ≤ 2 * M := by
        rw [Real.norm_eq_abs]
        linarith [abs_sub (∑ i ∈ Finset.range (m+1), winInt T Φ m i ω s) (Φi ω s), hMi ω s]
      show (‖(∑ i ∈ Finset.range (m+1), winInt T Φ m i ω s) - Φi ω s‖₊ : ℝ≥0∞) ^ 2 ≤ _
      rw [← ENNReal.ofReal_coe_nnreal, coe_nnnorm, ← ENNReal.ofReal_pow (norm_nonneg _)]
      exact ENNReal.ofReal_le_ofReal (pow_le_pow_left₀ (norm_nonneg _) hr 2)
    have hmeasF : ∀ m, Measurable (Function.uncurry (winSq T Φ Φi m)) := fun m =>
      (((hms m).sub hmi).nnnorm.coe_nnreal_ennreal).pow_const 2
    have hmeasS : ∀ m ω, Measurable (winSq T Φ Φi m ω) := fun m ω =>
      (hmeasF m).of_uncurry_left
    have hmeasO : ∀ m, Measurable (fun ω => ∫⁻ s in Set.Icc (0 : ℝ) T, winSq T Φ Φi m ω s ∂volume) :=
      fun m => (hmeasF m).lintegral_prod_right'
    haveI : IsFiniteMeasure (volume.restrict (Set.Icc (0:ℝ) T)) :=
      ⟨by rw [Measure.restrict_apply_univ, Real.volume_Icc]; exact ENNReal.ofReal_lt_top⟩
    have hinner : ∀ ω, Filter.Tendsto (fun m => ∫⁻ s in Set.Icc (0 : ℝ) T, winSq T Φ Φi m ω s ∂volume)
        Filter.atTop (𝓝 0) := by
      intro ω
      have hae : ∀ᵐ s ∂(volume.restrict (Set.Icc (0:ℝ) T)), s ∈ Set.Ioc 0 T := by
        rw [← Measure.restrict_congr_set Ioc_ae_eq_Icc]
        exact ae_restrict_mem measurableSet_Ioc
      have key := tendsto_lintegral_of_dominated_convergence (μ := volume.restrict (Set.Icc (0:ℝ) T))
        (F := fun m => winSq T Φ Φi m ω) (f := fun _ => (0:ℝ≥0∞))
        (fun _ => ENNReal.ofReal ((2 * M) ^ 2))
        (fun m => hmeasS m ω) (fun m => ae_of_all _ (hbd m ω))
        (by simpa using ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top) (by
          filter_upwards [hae] with s hs
          have hl := grid_tendsto hT hs (fun c => Φ c ω s) (hconv ω s)
          have hc : Continuous fun x : ℝ => ((‖x - Φi ω s‖₊ : ℝ≥0∞)) ^ 2 := by fun_prop
          have := (hc.tendsto (Φi ω s)).comp hl
          simp only [sub_self, nnnorm_zero, ENNReal.coe_zero, ne_eq, OfNat.ofNat_ne_zero,
            not_false_eq_true, zero_pow] at this
          exact this)
      rw [lintegral_zero] at key
      exact key
    have key := tendsto_lintegral_of_dominated_convergence (μ := P)
      (F := fun m ω => ∫⁻ s in Set.Icc (0 : ℝ) T, winSq T Φ Φi m ω s ∂volume)
      (f := fun _ => (0:ℝ≥0∞))
      (fun _ => ENNReal.ofReal ((2 * M) ^ 2) * volume (Set.Icc (0:ℝ) T))
      hmeasO (fun m => ae_of_all _ fun ω => ?_)
      (by simpa [Real.volume_Icc] using ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top)
      (ae_of_all _ hinner)
    · rw [lintegral_zero] at key
      exact key
    · calc ∫⁻ s in Set.Icc (0 : ℝ) T, winSq T Φ Φi m ω s ∂volume
          ≤ ∫⁻ _s in Set.Icc (0 : ℝ) T, ENNReal.ofReal ((2 * M) ^ 2) ∂volume :=
            lintegral_mono (hbd m ω)
        _ = _ := by simp [lintegral_const]

section Aux
variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}

theorem tim_add {f₁ f₂ : ℕ → Ω → ℝ} {g₁ g₂ : Ω → ℝ}
    (h₁ : TendstoInMeasure P f₁ Filter.atTop g₁) (h₂ : TendstoInMeasure P f₂ Filter.atTop g₂) :
    TendstoInMeasure P (fun m ω => f₁ m ω + f₂ m ω) Filter.atTop (fun ω => g₁ ω + g₂ ω) := by
  rw [tendstoInMeasure_iff_norm] at *
  intro ε hε
  have a := h₁ (ε / 2) (by positivity)
  have b := h₂ (ε / 2) (by positivity)
  have c := tendsto_add (a := (0 : ENNReal)) (b := 0) |>.comp (a.prodMk_nhds b)
  simp only [add_zero] at c
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds c (fun _ => zero_le) ?_
  intro m
  refine le_trans (measure_mono ?_) (measure_union_le _ _)
  intro ω hω
  simp only [Set.mem_ofPred_eq, Set.mem_union] at hω ⊢
  by_contra hcon
  push Not at hcon
  have := norm_add_le (f₁ m ω - g₁ ω) (f₂ m ω - g₂ ω)
  have e : f₁ m ω + f₂ m ω - (g₁ ω + g₂ ω) = (f₁ m ω - g₁ ω) + (f₂ m ω - g₂ ω) := by ring
  rw [e] at hω
  linarith [hcon.1, hcon.2]

theorem tim_const_mul {f₁ : ℕ → Ω → ℝ} {g₁ : Ω → ℝ} (c : ℝ)
    (h₁ : TendstoInMeasure P f₁ Filter.atTop g₁) :
    TendstoInMeasure P (fun m ω => c * f₁ m ω) Filter.atTop (fun ω => c * g₁ ω) := by
  rw [tendstoInMeasure_iff_norm] at *
  intro ε hε
  have a := h₁ (ε / (|c| + 1)) (by positivity)
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds a (fun _ => zero_le) ?_
  intro m
  refine measure_mono ?_
  intro ω hω
  simp only [Set.mem_ofPred_eq] at hω ⊢
  rw [← mul_sub, norm_mul, Real.norm_eq_abs] at hω
  by_contra hcon
  push Not at hcon
  have hn : 0 ≤ ‖f₁ m ω - g₁ ω‖ := norm_nonneg _
  have h1 : ‖f₁ m ω - g₁ ω‖ * (|c| + 1) < ε := by
    rwa [lt_div_iff₀ (by positivity)] at hcon
  nlinarith [abs_nonneg c]

theorem tim_sum {ι : Type*} (s : Finset ι) {f₁ : ι → ℕ → Ω → ℝ} {g₁ : ι → Ω → ℝ}
    (h₁ : ∀ i ∈ s, TendstoInMeasure P (f₁ i) Filter.atTop (g₁ i)) :
    TendstoInMeasure P (fun m ω => ∑ i ∈ s, f₁ i m ω) Filter.atTop (fun ω => ∑ i ∈ s, g₁ i ω) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    rw [tendstoInMeasure_iff_norm]
    intro ε hε
    simp [not_le.mpr hε]
  | insert a s ha ih =>
    simp only [Finset.sum_insert ha]
    exact tim_add (h₁ a (Finset.mem_insert_self _ _))
      (ih (fun i hi => h₁ i (Finset.mem_insert_of_mem hi)))

theorem telescope (u a b c r : ℕ → ℝ) (N : ℕ)
    (hu : ∀ i, u (i+1) - u i = a i + (b i + (1/2 : ℝ) * c i + r i)) :
    u N - u 0 = ∑ i ∈ Finset.range N, a i
      + (∑ i ∈ Finset.range N, b i + (1/2 : ℝ) * ∑ i ∈ Finset.range N, c i
        + ∑ i ∈ Finset.range N, r i) := by
  rw [← Finset.sum_range_sub u N]
  simp_rw [hu, Finset.sum_add_distrib, ← Finset.mul_sum]

end Aux

theorem time_riemann {E : Type*} [NormedAddCommGroup E] (f ft : ℝ → E → ℝ)
    (ht : ∀ s z, HasDerivAt (fun r => f r z) (ft s z) s)
    (hftc : Continuous (Function.uncurry ft)) (x : ℝ → E) (hx : Continuous x)
    (T : ℝ) (hT : 0 < T) :
    Filter.Tendsto (fun m : ℕ => ∑ i ∈ Finset.range (m+1),
      (f (unifGrid T (m+1) (i+1)) (x (unifGrid T (m+1) (i+1)))
        - f (unifGrid T (m+1) i) (x (unifGrid T (m+1) (i+1)))))
      Filter.atTop (nhds (∫ s in Set.Ioc (0 : ℝ) T, ft s (x s) ∂volume)) := by
  have hFc : Continuous fun s => ft s (x s) :=
    hftc.comp (continuous_id.prodMk hx)
  have hcomp : IsCompact (Set.Icc (0:ℝ) T ×ˢ Set.Icc (0:ℝ) T) := isCompact_Icc.prod isCompact_Icc
  have hG : Continuous fun p : ℝ × ℝ => ft p.1 (x p.2) :=
    hftc.comp (continuous_fst.prodMk (hx.comp continuous_snd))
  have huc := hcomp.uniformContinuousOn_of_continuous hG.continuousOn
  rw [Metric.tendsto_atTop]
  intro ε hε
  have hε' : 0 < ε / (T + 1) := by positivity
  obtain ⟨δ, hδ, hδ'⟩ := Metric.uniformContinuousOn_iff.mp huc (ε / (T+1)) hε'
  obtain ⟨M, hM⟩ := exists_nat_gt (T / δ)
  refine ⟨M, fun m hm => ?_⟩
  have hm0 : (0:ℝ) < (m+1 : ℕ) := by positivity
  set N : ℕ := m + 1 with hN
  have hstep : T / (N:ℝ) < δ := by
    rw [div_lt_iff₀ hm0]
    have : T / δ < (N : ℝ) := by
      have : (M : ℝ) ≤ m := by exact_mod_cast hm
      have : (m : ℝ) ≤ N := by simp [hN]
      linarith
    rw [div_lt_iff₀ hδ] at this
    linarith
  have hgmono : ∀ i, unifGrid T N i ≤ unifGrid T N (i+1) := fun i => (unifGrid_lt_succ hT (Nat.succ_ne_zero m) i).le
  have hgnonneg : ∀ i, 0 ≤ unifGrid T N i := fun i => by unfold unifGrid; positivity
  have hgle : ∀ i, i ≤ N → unifGrid T N i ≤ T := by
    intro i hi
    unfold unifGrid
    rw [div_le_iff₀ hm0]
    have : (i:ℝ) ≤ N := by exact_mod_cast hi
    nlinarith
  have hint : ∀ a b : ℝ, IntervalIntegrable (fun s => ft s (x s)) volume a b := fun a b => hFc.intervalIntegrable a b
  have htot : ∫ s in Set.Ioc (0 : ℝ) T, ft s (x s) ∂volume
      = ∑ i ∈ Finset.range N, ∫ s in unifGrid T N i..unifGrid T N (i+1), ft s (x s) := by
    rw [← intervalIntegral.integral_of_le hT.le]
    have := intervalIntegral.sum_integral_adjacent_intervals (a := unifGrid T N) (μ := volume)
      (f := fun s => ft s (x s)) (n := N) (fun k _ => hint _ _)
    rw [this, unifGrid_self (Nat.succ_ne_zero m), unifGrid_zero]
  have hcell : ∀ i ∈ Finset.range N,
      f (unifGrid T N (i+1)) (x (unifGrid T N (i+1))) - f (unifGrid T N i) (x (unifGrid T N (i+1)))
        - ∫ s in unifGrid T N i..unifGrid T N (i+1), ft s (x s)
      = ∫ s in unifGrid T N i..unifGrid T N (i+1), (ft s (x (unifGrid T N (i+1))) - ft s (x s)) := by
    intro i _
    have h1 : ∫ s in unifGrid T N i..unifGrid T N (i+1), ft s (x (unifGrid T N (i+1)))
        = f (unifGrid T N (i+1)) (x (unifGrid T N (i+1))) - f (unifGrid T N i) (x (unifGrid T N (i+1))) := by
      apply intervalIntegral.integral_eq_sub_of_hasDerivAt (f := fun r => f r (x (unifGrid T N (i+1))))
      · intro s _; exact ht s _
      · exact (hftc.comp (continuous_id.prodMk continuous_const)).intervalIntegrable _ _
    have hi2 : IntervalIntegrable (fun s => ft s (x (unifGrid T N (i+1)))) volume (unifGrid T N i) (unifGrid T N (i+1)) :=
      (hftc.comp (continuous_id.prodMk continuous_const)).intervalIntegrable _ _
    rw [intervalIntegral.integral_sub hi2 (hint _ _), h1]
  have hbound : ∀ i ∈ Finset.range N,
      ‖∫ s in unifGrid T N i..unifGrid T N (i+1), (ft s (x (unifGrid T N (i+1))) - ft s (x s))‖
        ≤ ε / (T+1) * (T / N) := by
    intro i hi
    have hiN : i + 1 ≤ N := Finset.mem_range.mp hi
    have hlen : unifGrid T N (i+1) - unifGrid T N i = T / N := unifGrid_succ_sub (Nat.succ_ne_zero m) i
    have := intervalIntegral.norm_integral_le_of_norm_le_const (a := unifGrid T N i) (b := unifGrid T N (i+1))
      (C := ε / (T+1)) (f := fun s => ft s (x (unifGrid T N (i+1))) - ft s (x s)) ?_
    · rw [abs_of_nonneg (by linarith [hgmono i])] at this
      rw [hlen] at this
      exact this.trans (le_of_eq (by ring))
    · intro s hs
      rw [Set.uIoc_of_le (hgmono i)] at hs
      have hs0 : 0 ≤ s := le_trans (hgnonneg i) hs.1.le
      have hsT : s ≤ T := le_trans hs.2 (hgle _ hiN)
      have hd := hδ' (s, unifGrid T N (i+1)) ⟨⟨hs0, hsT⟩, ⟨hgnonneg _, hgle _ hiN⟩⟩ (s, s) ⟨⟨hs0, hsT⟩, ⟨hs0, hsT⟩⟩ ?_
      · simpa [Real.dist_eq, norm_sub_rev, dist_eq_norm] using hd.le
      · rw [Prod.dist_eq]
        simp only [dist_self, Real.dist_eq]
        rw [max_lt_iff]
        refine ⟨hδ, ?_⟩
        rw [abs_of_nonneg (by linarith [hs.2])]
        linarith [hs.1, hlen]
  rw [Real.dist_eq, htot, ← Finset.sum_sub_distrib]
  have hsub : ∑ i ∈ Finset.range N, (f (unifGrid T N (i+1)) (x (unifGrid T N (i+1))) - f (unifGrid T N i) (x (unifGrid T N (i+1))) - ∫ s in unifGrid T N i..unifGrid T N (i+1), ft s (x s))
      = ∑ i ∈ Finset.range N, ∫ s in unifGrid T N i..unifGrid T N (i+1), (ft s (x (unifGrid T N (i+1))) - ft s (x s)) :=
    Finset.sum_congr rfl hcell
  rw [hsub]
  calc |∑ i ∈ Finset.range N, ∫ s in unifGrid T N i..unifGrid T N (i+1), (ft s (x (unifGrid T N (i+1))) - ft s (x s))|
      ≤ ∑ i ∈ Finset.range N, ‖∫ s in unifGrid T N i..unifGrid T N (i+1), (ft s (x (unifGrid T N (i+1))) - ft s (x s))‖ := by
        rw [← Real.norm_eq_abs]; exact norm_sum_le _ _
    _ ≤ ∑ i ∈ Finset.range N, ε / (T+1) * (T / N) := Finset.sum_le_sum hbound
    _ = ε / (T+1) * T := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; field_simp
    _ < ε := by
        rw [div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]; nlinarith


theorem swap_sub {ι : Type*} (s : Finset ι) (N : ℕ) (a b : ℕ → ι → ℝ) :
    ∑ i ∈ Finset.range N, (∑ p ∈ s, a i p - ∑ p ∈ s, b i p)
      = ∑ p ∈ s, ∑ i ∈ Finset.range N, (a i p - b i p) := by
  simp_rw [← Finset.sum_sub_distrib]
  exact Finset.sum_comm

theorem swap_sub2 {ι κ : Type*} (s : Finset ι) (t : Finset κ) (N : ℕ) (a b : ℕ → ι → κ → ℝ) :
    ∑ i ∈ Finset.range N, (∑ p ∈ s, ∑ k ∈ t, a i p k - ∑ p ∈ s, ∑ k ∈ t, b i p k)
      = ∑ p ∈ s, ∑ k ∈ t, ∑ i ∈ Finset.range N, (a i p k - b i p k) := by
  rw [swap_sub]
  exact Finset.sum_congr rfl fun p _ => swap_sub _ _ _ _

noncomputable def Dpart {Ω : Type*} {n : ℕ} (fx : ℝ → (Fin n → ℝ) → (Fin n → ℝ) →L[ℝ] ℝ)
    (X : ℝ → Ω → Fin n → ℝ) (bdrift : Fin n → Ω → ℝ → ℝ) (c t : ℝ) (ω : Ω) : ℝ :=
  ∑ p : Fin n, ∫ s in Set.Ioc (0:ℝ) t, coordDeriv (fx c) p (X s ω) * bdrift p ω s ∂volume

noncomputable def Qpart {Ω : Type*} {n d : ℕ}
    (fxx : ℝ → (Fin n → ℝ) → (Fin n → ℝ) →L[ℝ] (Fin n → ℝ) →L[ℝ] ℝ)
    (X : ℝ → Ω → Fin n → ℝ) (H : Fin n → Fin d → Ω → ℝ → ℝ) (c t : ℝ) (ω : Ω) : ℝ :=
  1 / 2 * ∑ p : Fin n, ∑ q : Fin n, ∫ s in Set.Ioc (0:ℝ) t,
    coordDeriv₂ (fxx c) p q (X s ω) * ∑ k : Fin d, H p k ω s * H q k ω s ∂volume

theorem solution
    {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P]
    {n d : ℕ}
    {W : LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion P d}
    {ℱ : Filtration ℝ ‹MeasurableSpace Ω›}
    {hcoord : ∀ k : Fin d,
      LevyStochCalc.Brownian.IsBrownianFiltration (W.W k) ℱ}
    {H : Fin n → Fin d → Ω → ℝ → ℝ}
    {hHm : ∀ p k, Measurable (Function.uncurry (H p k))}
    {hHp : ∀ p k, LevyStochCalc.Probability.ProgressivelyMeasurable ℱ (H p k)}
    {hHs : ∀ (p : Fin n) (k : Fin d) (T' : ℝ), 0 < T' →
      ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T',
        (‖H p k ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤}
    {X₀ : Ω → Fin n → ℝ}
    {bdrift : Fin n → Ω → ℝ → ℝ}
    {X : ℝ → Ω → Fin n → ℝ}
    {C : ℝ} (hC0 : 0 ≤ C)
    (hCH : ∀ (p : Fin n) (k : Fin d) (ω : Ω) (s : ℝ),
      |H p k ω s| ≤ C)
    (h : IsVectorItoVersion W ℱ hcoord H hHm hHp hHs X₀ bdrift X)
    (hX₀ : ∀ p : Fin n, Measurable fun ω => X₀ ω p)
    (hbm : ∀ p, Measurable (Function.uncurry (bdrift p)))
    {B : ℝ} (hB0 : 0 ≤ B)
    (hB : ∀ (p : Fin n) (ω : Ω) (s : ℝ), |bdrift p ω s| ≤ B)
    (hma : ∀ (p q : Fin n) (k : Fin d),
      Measurable (Function.uncurry fun ω s => H p k ω s + H q k ω s))
    (hpa : ∀ (p q : Fin n) (k : Fin d),
      Probability.ProgressivelyMeasurable ℱ fun ω s => H p k ω s + H q k ω s)
    (hqa : ∀ (p q : Fin n) (k : Fin d) (T' : ℝ), 0 < T' →
      ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T',
        (‖H p k ω s + H q k ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    {f : ℝ → (Fin n → ℝ) → ℝ}
    {ft : ℝ → (Fin n → ℝ) → ℝ}
    {fx : ℝ → (Fin n → ℝ) → (Fin n → ℝ) →L[ℝ] ℝ}
    {fxx : ℝ → (Fin n → ℝ) →
       (Fin n → ℝ) →L[ℝ] (Fin n → ℝ) →L[ℝ] ℝ}
    (ht : ∀ s z, HasDerivAt (fun r => f r z) (ft s z) s)
    (hx : ∀ s z, HasFDerivAt (f s) (fx s z) z)
    (hxx : ∀ s z, HasFDerivAt (fx s) (fxx s z) z)
    (hftc : Continuous (Function.uncurry ft))
    (hfxc : Continuous (Function.uncurry fx))
    (hfxxc : Continuous (Function.uncurry fxx))
    (hfxxunif : ∀ (s : ℝ) (ε : ℝ), 0 < ε →
      ∃ δ : ℝ, 0 < δ ∧ ∀ z w : Fin n → ℝ,
        ‖z - w‖ < δ → ‖fxx s z - fxx s w‖ ≤ ε)
    {K : ℝ} (hK0 : 0 ≤ K)
    (hfbd : ∀ (s : ℝ) (z : Fin n → ℝ),
      |ft s z| ≤ K ∧ ‖fx s z‖ ≤ K ∧ ‖fxx s z‖ ≤ K)
    (hmg : ∀ (p : Fin n) (k : Fin d),
      Measurable (Function.uncurry fun ω s =>
        coordDeriv (fx s) p (X s ω) * H p k ω s))
    (hpg : ∀ (p : Fin n) (k : Fin d),
      Probability.ProgressivelyMeasurable ℱ fun ω s =>
        coordDeriv (fx s) p (X s ω) * H p k ω s)
    (hqg : ∀ (p : Fin n) (k : Fin d) (T' : ℝ), 0 < T' →
      ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T',
        (‖coordDeriv (fx s) p (X s ω) * H p k ω s‖₊ : ℝ≥0∞) ^ 2
          ∂volume ∂P < ⊤)
    {T : ℝ} (hT : 0 < T) :
    (fun ω : Ω => f T (X T ω) - f 0 (X 0 ω)) =ᵐ[P]
      fun ω : Ω =>
        (∫ s in Set.Ioc (0 : ℝ) T, ft s (X s ω) ∂volume)
          + (∑ p : Fin n, ∫ s in Set.Ioc (0 : ℝ) T,
              coordDeriv (fx s) p (X s ω) * bdrift p ω s ∂volume)
          + (∑ p : Fin n, ∑ k : Fin d,
              stochasticIntegralBrownian (W.W k) ℱ (hcoord k)
                (fun ω s =>
                  coordDeriv (fx s) p (X s ω) * H p k ω s)
                (hmg p k) (hpg p k) (hqg p k) T ω)
          + (1 / 2 : ℝ) * ∑ p : Fin n, ∑ q : Fin n,
              ∫ s in Set.Ioc (0 : ℝ) T,
                coordDeriv₂ (fxx s) p q (X s ω) *
                  (∑ k : Fin d, H p k ω s * H q k ω s) ∂volume := by
  classical
  have hXm : ∀ s, Measurable (X s) := fun s => ((h.adapted s).mono (ℱ.le s)).measurable
  have hfxc_c : ∀ c, Continuous (fx c) := fun c =>
    hfxc.comp (continuous_const.prodMk continuous_id)
  have hfxxc_c : ∀ c, Continuous (fxx c) := fun c =>
    hfxxc.comp (continuous_const.prodMk continuous_id)
  have hcd : ∀ c p, Continuous fun z => coordDeriv (fx c) p z := fun c p =>
    (hfxc_c c).clm_apply continuous_const
  have hcd2 : ∀ c p q, Continuous fun z => coordDeriv₂ (fxx c) p q z := fun c p q =>
    ((hfxxc_c c).clm_apply continuous_const).clm_apply continuous_const
  have hcdb : ∀ c p z, |coordDeriv (fx c) p z| ≤ K := by
    intro c p z
    have h1 := (fx c z).le_opNorm (Pi.single p (1 : ℝ))
    simp only [Pi.norm_single, norm_one, mul_one] at h1
    rw [← Real.norm_eq_abs]
    exact h1.trans (hfbd c z).2.1
  have hcd2b : ∀ c p q z, |coordDeriv₂ (fxx c) p q z| ≤ K := by
    intro c p q z
    have h1 := (fxx c z).le_opNorm₂ (Pi.single p (1 : ℝ)) (Pi.single q (1 : ℝ))
    simp only [Pi.norm_single, norm_one, mul_one] at h1
    rw [← Real.norm_eq_abs]
    exact h1.trans (hfbd c z).2.2
  have hcdt : ∀ p z s, Filter.Tendsto (fun c => coordDeriv (fx c) p z) (𝓝 s)
      (𝓝 (coordDeriv (fx s) p z)) := fun p z s =>
    (((hfxc.comp (continuous_id.prodMk continuous_const)).clm_apply
      continuous_const).tendsto s)
  have hcd2t : ∀ p q z s, Filter.Tendsto (fun c => coordDeriv₂ (fxx c) p q z) (𝓝 s)
      (𝓝 (coordDeriv₂ (fxx s) p q z)) := fun p q z s =>
    ((((hfxxc.comp (continuous_id.prodMk continuous_const)).clm_apply
      continuous_const).clm_apply continuous_const).tendsto s)
  have hmcomp : ∀ g : (Fin n → ℝ) → ℝ, Continuous g →
      Measurable (Function.uncurry fun ω s => g (X s ω)) := fun g hg =>
    (measurable_uncurry_of_continuous_of_measurable (u := fun s ω => g (X s ω))
      (fun ω => hg.comp (h.continuous_path ω)) (fun s => hg.measurable.comp (hXm s))).comp
      measurable_swap
  have hpcomp : ∀ g : (Fin n → ℝ) → ℝ, Continuous g →
      Probability.ProgressivelyMeasurable ℱ (fun ω s => g (X s ω)) := fun g hg =>
    ItoLemma.continuous_adapted_composition_progressive
      (Y := fun s ω => fun _ : Fin 2 => g (X s ω))
      (fun ω => continuous_pi fun _ => hg.comp (h.continuous_path ω))
      (fun t => by
        have hm : Measurable[ℱ t] (fun ω => g (X t ω)) := hg.measurable.comp (h.adapted t).measurable
        letI : MeasurableSpace Ω := ℱ t
        exact measurable_pi_lambda _ (fun _ => hm))
      (φ := fun y => y 0) (continuous_apply 0)
  have hφm : ∀ p k c, Measurable (Function.uncurry fun ω s =>
      coordDeriv (fx c) p (X s ω) * H p k ω s) := fun p k c =>
    (hmcomp _ (hcd c p)).mul (hHm p k)
  have hφp : ∀ p k c, Probability.ProgressivelyMeasurable ℱ (fun ω s =>
      coordDeriv (fx c) p (X s ω) * H p k ω s) := fun p k c =>
    (hpcomp _ (hcd c p)).mul (hHp p k)
  have hφb : ∀ p k c (ω : Ω) s, |coordDeriv (fx c) p (X s ω) * H p k ω s| ≤ K * C := by
    intro p k c ω s
    rw [abs_mul]
    exact mul_le_mul (hcdb c p _) (hCH p k ω s) (abs_nonneg _) hK0
  have hφq : ∀ p k c, ∀ T', 0 < T' → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T',
      (‖coordDeriv (fx c) p (X s ω) * H p k ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤ := fun p k c =>
    hq_of_bdd _ (hφb p k c)
  -- Itô's formula for the frozen-time function `f c` up to time `t`
  have hwin : ∀ c t, 0 ≤ t → (fun ω => f c (X t ω) - f c (X 0 ω)) =ᵐ[P] fun ω =>
      Dpart fx X bdrift c t ω
        + (∑ p : Fin n, ∑ k : Fin d, stochasticIntegralBrownian (W.W k) ℱ (hcoord k)
            (fun ω s => coordDeriv (fx c) p (X s ω) * H p k ω s)
            (hφm p k c) (hφp p k c) (hφq p k c) t ω)
        + Qpart fxx X H c t ω := by
    intro c t ht
    rcases ht.lt_or_eq with ht | ht
    · exact h.itoFormula_readable hC0 hCH hX₀ hbm hB0 hB hma hpa hqa (hx c) (hxx c)
        (fun z => (hfbd c z).2.1) hK0 (fun z => (hfbd c z).2.2) (hfxxc_c c) (hfxxunif c)
        (fun p k => hφm p k c) (fun p k => hφp p k c) (fun p k => hφq p k c) ht
    · subst ht
      have h0 : ∀ᵐ ω ∂P, ∀ p : Fin n, ∀ k : Fin d, stochasticIntegralBrownian (W.W k) ℱ (hcoord k)
          (fun ω s => coordDeriv (fx c) p (X s ω) * H p k ω s)
          (hφm p k c) (hφp p k c) (hφq p k c) 0 ω = 0 := by
        rw [ae_all_iff]; intro p; rw [ae_all_iff]; intro k
        exact stochasticIntegralBrownian_ae_zero_of_nonpos _ _ _ _ _ _ _ le_rfl
      filter_upwards [h0] with ω hω
      simp [Dpart, Qpart, hω]
  -- all grid windows simultaneously
  have hall : ∀ᵐ ω ∂P, ∀ m i : ℕ,
      f (unifGrid T (m+1) i) (X (unifGrid T (m+1) (i+1)) ω)
          - f (unifGrid T (m+1) i) (X (unifGrid T (m+1) i) ω)
        = (Dpart fx X bdrift (unifGrid T (m+1) i) (unifGrid T (m+1) (i+1)) ω
            - Dpart fx X bdrift (unifGrid T (m+1) i) (unifGrid T (m+1) i) ω)
          + ((∑ p : Fin n, ∑ k : Fin d, stochasticIntegralBrownian (W.W k) ℱ (hcoord k)
              (fun ω s => coordDeriv (fx (unifGrid T (m+1) i)) p (X s ω) * H p k ω s)
              (hφm p k _) (hφp p k _) (hφq p k _) (unifGrid T (m+1) (i+1)) ω)
            - (∑ p : Fin n, ∑ k : Fin d, stochasticIntegralBrownian (W.W k) ℱ (hcoord k)
              (fun ω s => coordDeriv (fx (unifGrid T (m+1) i)) p (X s ω) * H p k ω s)
              (hφm p k _) (hφp p k _) (hφq p k _) (unifGrid T (m+1) i) ω))
          + (Qpart fxx X H (unifGrid T (m+1) i) (unifGrid T (m+1) (i+1)) ω
            - Qpart fxx X H (unifGrid T (m+1) i) (unifGrid T (m+1) i) ω) := by
    rw [ae_all_iff]; intro m; rw [ae_all_iff]; intro i
    have hg : ∀ j, 0 ≤ unifGrid T (m+1) j := fun j => by simp only [unifGrid]; positivity
    filter_upwards [hwin (unifGrid T (m+1) i) _ (hg (i+1)),
      hwin (unifGrid T (m+1) i) _ (hg i)] with ω h1 h2
    linarith
  -- the stochastic Riemann sums converge in measure
  have hS : TendstoInMeasure P (fun (m : ℕ) (ω : Ω) => ∑ p : Fin n, ∑ k : Fin d,
      ∑ i ∈ Finset.range (m+1),
        (stochasticIntegralBrownian (W.W k) ℱ (hcoord k)
            (fun ω s => coordDeriv (fx (unifGrid T (m+1) i)) p (X s ω) * H p k ω s)
            (hφm p k _) (hφp p k _) (hφq p k _) (unifGrid T (m+1) (i+1)) ω
          - stochasticIntegralBrownian (W.W k) ℱ (hcoord k)
            (fun ω s => coordDeriv (fx (unifGrid T (m+1) i)) p (X s ω) * H p k ω s)
            (hφm p k _) (hφp p k _) (hφq p k _) (unifGrid T (m+1) i) ω))
      Filter.atTop (fun ω => ∑ p : Fin n, ∑ k : Fin d,
        stochasticIntegralBrownian (W.W k) ℱ (hcoord k)
          (fun ω s => coordDeriv (fx s) p (X s ω) * H p k ω s)
          (hmg p k) (hpg p k) (hqg p k) T ω) := by
    refine tim_sum _ (fun p _ => tim_sum _ (fun k _ => ?_))
    exact stoch_window (W.W k) ℱ (hcoord k)
      (fun c ω s => coordDeriv (fx c) p (X s ω) * H p k ω s)
      (fun ω s => coordDeriv (fx s) p (X s ω) * H p k ω s)
      (hφm p k) (hφp p k) (hφq p k) (hmg p k) (hpg p k) (hqg p k)
      (mul_nonneg hK0 hC0) (hφb p k) (fun ω s => hφb p k s ω s)
      (fun ω s => (hcdt p (X s ω) s).mul_const _) hT
  obtain ⟨ns, hns, hae⟩ := hS.exists_seq_tendsto_ae
  filter_upwards [hall, hae] with ω hω hSω
  have hid : ∀ m : ℕ, f T (X T ω) - f 0 (X 0 ω) =
      (∑ i ∈ Finset.range (m+1), (f (unifGrid T (m+1) (i+1)) (X (unifGrid T (m+1) (i+1)) ω)
          - f (unifGrid T (m+1) i) (X (unifGrid T (m+1) (i+1)) ω)))
      + (∑ p : Fin n, ∑ i ∈ Finset.range (m+1),
          ((∫ s in Set.Ioc (0:ℝ) (unifGrid T (m+1) (i+1)),
              coordDeriv (fx (unifGrid T (m+1) i)) p (X s ω) * bdrift p ω s ∂volume)
            - ∫ s in Set.Ioc (0:ℝ) (unifGrid T (m+1) i),
              coordDeriv (fx (unifGrid T (m+1) i)) p (X s ω) * bdrift p ω s ∂volume))
      + (∑ p : Fin n, ∑ k : Fin d,
        ∑ i ∈ Finset.range (m+1),
          (stochasticIntegralBrownian (W.W k) ℱ (hcoord k)
              (fun ω s => coordDeriv (fx (unifGrid T (m+1) i)) p (X s ω) * H p k ω s)
              (hφm p k _) (hφp p k _) (hφq p k _) (unifGrid T (m+1) (i+1)) ω
            - stochasticIntegralBrownian (W.W k) ℱ (hcoord k)
              (fun ω s => coordDeriv (fx (unifGrid T (m+1) i)) p (X s ω) * H p k ω s)
              (hφm p k _) (hφp p k _) (hφq p k _) (unifGrid T (m+1) i) ω))
      + (1 / 2 : ℝ) * ∑ p : Fin n, ∑ q : Fin n, ∑ i ∈ Finset.range (m+1),
          ((∫ s in Set.Ioc (0:ℝ) (unifGrid T (m+1) (i+1)),
              coordDeriv₂ (fxx (unifGrid T (m+1) i)) p q (X s ω)
                * ∑ k : Fin d, H p k ω s * H q k ω s ∂volume)
            - ∫ s in Set.Ioc (0:ℝ) (unifGrid T (m+1) i),
              coordDeriv₂ (fxx (unifGrid T (m+1) i)) p q (X s ω)
                * ∑ k : Fin d, H p k ω s * H q k ω s ∂volume) := by
    intro m
    have e1 : f T (X T ω) - f 0 (X 0 ω) = ∑ i ∈ Finset.range (m+1),
        (f (unifGrid T (m+1) (i+1)) (X (unifGrid T (m+1) (i+1)) ω)
          - f (unifGrid T (m+1) i) (X (unifGrid T (m+1) i) ω)) := by
      rw [Finset.sum_range_sub (fun i => f (unifGrid T (m+1) i) (X (unifGrid T (m+1) i) ω)),
        unifGrid_self (Nat.succ_ne_zero m), unifGrid_zero]
    rw [e1]
    rw [Finset.sum_congr rfl (fun i _ => (show
        f (unifGrid T (m+1) (i+1)) (X (unifGrid T (m+1) (i+1)) ω)
          - f (unifGrid T (m+1) i) (X (unifGrid T (m+1) i) ω)
        = (f (unifGrid T (m+1) (i+1)) (X (unifGrid T (m+1) (i+1)) ω)
            - f (unifGrid T (m+1) i) (X (unifGrid T (m+1) (i+1)) ω))
          + (f (unifGrid T (m+1) i) (X (unifGrid T (m+1) (i+1)) ω)
            - f (unifGrid T (m+1) i) (X (unifGrid T (m+1) i) ω)) by ring))]
    simp only [hω, Finset.sum_add_distrib]
    have eD := swap_sub Finset.univ (m+1)
      (fun i p => ∫ s in Set.Ioc (0:ℝ) (unifGrid T (m+1) (i+1)),
          coordDeriv (fx (unifGrid T (m+1) i)) p (X s ω) * bdrift p ω s ∂volume)
      (fun i p => ∫ s in Set.Ioc (0:ℝ) (unifGrid T (m+1) i),
          coordDeriv (fx (unifGrid T (m+1) i)) p (X s ω) * bdrift p ω s ∂volume)
    have eS := swap_sub2 Finset.univ Finset.univ (m+1)
      (fun i p k => stochasticIntegralBrownian (W.W k) ℱ (hcoord k)
              (fun ω s => coordDeriv (fx (unifGrid T (m+1) i)) p (X s ω) * H p k ω s)
              (hφm p k _) (hφp p k _) (hφq p k _) (unifGrid T (m+1) (i+1)) ω)
      (fun i p k => stochasticIntegralBrownian (W.W k) ℱ (hcoord k)
              (fun ω s => coordDeriv (fx (unifGrid T (m+1) i)) p (X s ω) * H p k ω s)
              (hφm p k _) (hφp p k _) (hφq p k _) (unifGrid T (m+1) i) ω)
    have eQ := swap_sub2 Finset.univ Finset.univ (m+1)
      (fun i p q => ∫ s in Set.Ioc (0:ℝ) (unifGrid T (m+1) (i+1)),
              coordDeriv₂ (fxx (unifGrid T (m+1) i)) p q (X s ω)
                * ∑ k : Fin d, H p k ω s * H q k ω s ∂volume)
      (fun i p q => ∫ s in Set.Ioc (0:ℝ) (unifGrid T (m+1) i),
              coordDeriv₂ (fxx (unifGrid T (m+1) i)) p q (X s ω)
                * ∑ k : Fin d, H p k ω s * H q k ω s ∂volume)
    have eQ' : ∑ i ∈ Finset.range (m+1),
        (Qpart fxx X H (unifGrid T (m+1) i) (unifGrid T (m+1) (i+1)) ω
          - Qpart fxx X H (unifGrid T (m+1) i) (unifGrid T (m+1) i) ω)
        = (1 / 2 : ℝ) * ∑ p : Fin n, ∑ q : Fin n, ∑ i ∈ Finset.range (m+1),
          ((∫ s in Set.Ioc (0:ℝ) (unifGrid T (m+1) (i+1)),
              coordDeriv₂ (fxx (unifGrid T (m+1) i)) p q (X s ω)
                * ∑ k : Fin d, H p k ω s * H q k ω s ∂volume)
            - ∫ s in Set.Ioc (0:ℝ) (unifGrid T (m+1) i),
              coordDeriv₂ (fxx (unifGrid T (m+1) i)) p q (X s ω)
                * ∑ k : Fin d, H p k ω s * H q k ω s ∂volume) := by
      rw [← eQ, Finset.mul_sum]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      simp only [Qpart]
      ring
    have eD' : ∑ i ∈ Finset.range (m+1),
        (Dpart fx X bdrift (unifGrid T (m+1) i) (unifGrid T (m+1) (i+1)) ω
          - Dpart fx X bdrift (unifGrid T (m+1) i) (unifGrid T (m+1) i) ω)
        = ∑ p : Fin n, ∑ i ∈ Finset.range (m+1),
          ((∫ s in Set.Ioc (0:ℝ) (unifGrid T (m+1) (i+1)),
              coordDeriv (fx (unifGrid T (m+1) i)) p (X s ω) * bdrift p ω s ∂volume)
            - ∫ s in Set.Ioc (0:ℝ) (unifGrid T (m+1) i),
              coordDeriv (fx (unifGrid T (m+1) i)) p (X s ω) * bdrift p ω s ∂volume) := eD
    rw [eD', eS, eQ']
    ring
  -- pathwise limits
  have hTm := time_riemann f ft ht hftc (fun t => X t ω) (h.continuous_path ω) T hT
  have hD : Filter.Tendsto (fun m : ℕ => ∑ p : Fin n, ∑ i ∈ Finset.range (m+1),
          ((∫ s in Set.Ioc (0:ℝ) (unifGrid T (m+1) (i+1)),
              coordDeriv (fx (unifGrid T (m+1) i)) p (X s ω) * bdrift p ω s ∂volume)
            - ∫ s in Set.Ioc (0:ℝ) (unifGrid T (m+1) i),
              coordDeriv (fx (unifGrid T (m+1) i)) p (X s ω) * bdrift p ω s ∂volume))
      Filter.atTop (𝓝 (∑ p : Fin n, ∫ s in Set.Ioc (0 : ℝ) T,
              coordDeriv (fx s) p (X s ω) * bdrift p ω s ∂volume)) := by
    refine tendsto_finsetSum _ (fun p _ => ?_)
    refine det_window hT (fun c s => coordDeriv (fx c) p (X s ω) * bdrift p ω s)
      (mul_nonneg hK0 hB0) (fun c s => ?_) (fun c => ?_) (fun s => (hcdt p (X s ω) s).mul_const _)
    · rw [abs_mul]; exact mul_le_mul (hcdb c p _) (hB p ω s) (abs_nonneg _) hK0
    · exact ((hcd c p).comp (h.continuous_path ω)).measurable.mul (hbm p).of_uncurry_left
  have hHH : ∀ p q s, |∑ k : Fin d, H p k ω s * H q k ω s| ≤ (d : ℝ) * (C * C) := by
    intro p q s
    calc |∑ k : Fin d, H p k ω s * H q k ω s| ≤ ∑ k : Fin d, |H p k ω s * H q k ω s| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _k : Fin d, C * C := Finset.sum_le_sum (fun k _ => by
          rw [abs_mul]; exact mul_le_mul (hCH p k ω s) (hCH q k ω s) (abs_nonneg _) hC0)
      _ = (d : ℝ) * (C * C) := by simp
  have hQ : Filter.Tendsto (fun m : ℕ => (1 / 2 : ℝ) * ∑ p : Fin n, ∑ q : Fin n,
        ∑ i ∈ Finset.range (m+1),
          ((∫ s in Set.Ioc (0:ℝ) (unifGrid T (m+1) (i+1)),
              coordDeriv₂ (fxx (unifGrid T (m+1) i)) p q (X s ω)
                * ∑ k : Fin d, H p k ω s * H q k ω s ∂volume)
            - ∫ s in Set.Ioc (0:ℝ) (unifGrid T (m+1) i),
              coordDeriv₂ (fxx (unifGrid T (m+1) i)) p q (X s ω)
                * ∑ k : Fin d, H p k ω s * H q k ω s ∂volume))
      Filter.atTop (𝓝 ((1 / 2 : ℝ) * ∑ p : Fin n, ∑ q : Fin n,
              ∫ s in Set.Ioc (0 : ℝ) T,
                coordDeriv₂ (fxx s) p q (X s ω) *
                  (∑ k : Fin d, H p k ω s * H q k ω s) ∂volume)) := by
    refine Filter.Tendsto.const_mul _ (tendsto_finsetSum _ (fun p _ =>
      tendsto_finsetSum _ (fun q _ => ?_)))
    refine det_window hT (fun c s => coordDeriv₂ (fxx c) p q (X s ω)
        * ∑ k : Fin d, H p k ω s * H q k ω s)
      (mul_nonneg hK0 (mul_nonneg (Nat.cast_nonneg d) (mul_nonneg hC0 hC0)))
      (fun c s => ?_) (fun c => ?_) (fun s => (hcd2t p q (X s ω) s).mul_const _)
    · rw [abs_mul]; exact mul_le_mul (hcd2b c p q _) (hHH p q s) (abs_nonneg _) hK0
    · exact ((hcd2 c p q).comp (h.continuous_path ω)).measurable.mul
        (Finset.measurable_sum _ fun k _ =>
          ((hHm p k).of_uncurry_left).mul ((hHm q k).of_uncurry_left))
  have hlim := (((hTm.comp hns.tendsto_atTop).add (hD.comp hns.tendsto_atTop)).add hSω).add
    (hQ.comp hns.tendsto_atTop)
  have hlim' : Filter.Tendsto (fun _ : ℕ => f T (X T ω) - f 0 (X 0 ω)) Filter.atTop
      (𝓝 ((∫ s in Set.Ioc (0 : ℝ) T, ft s (X s ω) ∂volume)
          + (∑ p : Fin n, ∫ s in Set.Ioc (0 : ℝ) T,
              coordDeriv (fx s) p (X s ω) * bdrift p ω s ∂volume)
          + (∑ p : Fin n, ∑ k : Fin d,
              stochasticIntegralBrownian (W.W k) ℱ (hcoord k)
                (fun ω s =>
                  coordDeriv (fx s) p (X s ω) * H p k ω s)
                (hmg p k) (hpg p k) (hqg p k) T ω)
          + (1 / 2 : ℝ) * ∑ p : Fin n, ∑ q : Fin n,
              ∫ s in Set.Ioc (0 : ℝ) T,
                coordDeriv₂ (fxx s) p q (X s ω) *
                  (∑ k : Fin d, H p k ω s * H q k ω s) ∂volume)) :=
    hlim.congr (fun j => (hid (ns j)).symm)
  exact tendsto_nhds_unique tendsto_const_nhds hlim'
