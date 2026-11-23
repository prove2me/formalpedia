-- Prove2me | solution 2 for AppliedSDE.SarkkaSolin.girsanov_brownian_shift_terminal_density
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Xeroth
-- created : 2026-11-23T00:51:24.353794+00:00
-- url     : https://prove2.me/submissions/cc4ca6dd-7fd1-4243-8636-74b61cf3fd16
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_KLSModular_LevyStochCalc_Brownian_Filtered
import Definitions.Def_KLSModular_LevyStochCalc_Brownian_ItoL2CompletionMaster
import Theorems.Thm_AppliedSDE_SarkkaSolin_girsanov_shifted_pre_brownian_core
open MeasureTheory ProbabilityTheory Filter LevyStochCalc.Brownian
open scoped ENNReal NNReal Topology

lemma withDensity_exp_isProb {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (Z : Ω → ℝ)
    (hpos : ∀ ω, 0 < Z ω) (hZmean : ∫ ω, Z ω ∂P = 1) :
    IsProbabilityMeasure (P.withDensity (fun ω => ENNReal.ofReal (Z ω))) := by
  have hint : Integrable Z P := by
    by_contra h
    rw [integral_undef h] at hZmean
    exact zero_ne_one hZmean
  constructor
  have hm : AEMeasurable Z P := hint.aemeasurable
  rw [withDensity_apply' _ _, Measure.restrict_univ]
  · rw [← ofReal_integral_eq_lintegral_ofReal hint (Filter.Eventually.of_forall fun ω => (hpos ω).le), hZmean]
    simp


lemma drift_primitive_continuous_ae {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (T : ℝ) (hT : 0 < T) (θ : Ω → ℝ → ℝ)
    (hθmeas : Measurable (Function.uncurry θ))
    (hθq : ∀ (t : ℝ), 0 < t →
      ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) t,
        (‖θ ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    (hθzero : ∀ (ω : Ω) (s : ℝ), T ≤ s → θ ω s = 0) :
    ∀ᵐ ω ∂P, Continuous fun t : ℝ≥0 => ∫ s in (0 : ℝ)..(t : ℝ), θ ω s := by
  have hmeasF : Measurable fun ω => ∫⁻ s in Set.Icc (0 : ℝ) T, (‖θ ω s‖₊ : ℝ≥0∞) ^ 2 := by
    have h : Measurable fun p : Ω × ℝ => (‖θ p.1 p.2‖₊ : ℝ≥0∞) ^ 2 :=
      (hθmeas.nnnorm.coe_nnreal_ennreal).pow_const 2
    exact h.lintegral_prod_right'
  filter_upwards [ae_lt_top hmeasF (hθq T hT).ne] with ω hω
  have hm : Measurable (θ ω) := hθmeas.comp measurable_prodMk_left
  have hL2 : MemLp (θ ω) 2 (volume.restrict (Set.Icc (0 : ℝ) T)) := by
    refine ⟨hm.aestronglyMeasurable, ?_⟩
    rw [eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top (by norm_num) (by norm_num)]
    simpa [enorm_eq_nnnorm] using hω
  have hI : IntegrableOn (θ ω) (Set.Icc (0 : ℝ) T) volume := by
    have : IsFiniteMeasure (volume.restrict (Set.Icc (0 : ℝ) T)) := by
      rw [isFiniteMeasure_restrict]; simp
    exact hL2.integrable (by norm_num)
  set g : ℝ → ℝ := (Set.Icc (0 : ℝ) T).indicator (θ ω) with hg
  have hgi : Integrable g volume := (integrable_indicator_iff measurableSet_Icc).2 hI
  have hcont : Continuous fun t : ℝ => ∫ s in (0 : ℝ)..t, g s :=
    intervalIntegral.continuous_primitive (fun a b => hgi.intervalIntegrable) 0
  have heq : ∀ t : ℝ≥0, ∫ s in (0 : ℝ)..(t : ℝ), θ ω s = ∫ s in (0 : ℝ)..(t : ℝ), g s := by
    intro t
    rw [intervalIntegral.integral_of_le (NNReal.coe_nonneg t), intervalIntegral.integral_of_le (NNReal.coe_nonneg t)]
    refine setIntegral_congr_fun measurableSet_Ioc (fun s hs => ?_)
    by_cases hsT : s ≤ T
    · have hs' : s ∈ Set.Icc (0 : ℝ) T := ⟨hs.1.le, hsT⟩
      simp [hg, Set.indicator_of_mem hs']
    · have hs' : s ∉ Set.Icc (0 : ℝ) T := fun h => hsT h.2
      simp [hg, Set.indicator_of_notMem hs', hθzero ω s (le_of_not_ge hsT)]
  simp_rw [heq]
  exact hcont.comp NNReal.continuous_coe

lemma shifted_cont_ae {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (W : LevyStochCalc.Brownian.BrownianMotion P)
    (T : ℝ) (hT : 0 < T) (θ : Ω → ℝ → ℝ)
    (hθmeas : Measurable (Function.uncurry θ))
    (hθq : ∀ (t : ℝ), 0 < t →
      ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) t,
        (‖θ ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    (hθzero : ∀ (ω : Ω) (s : ℝ), T ≤ s → θ ω s = 0) (Z : Ω → ℝ) :
    ∀ᵐ ω ∂(P.withDensity (fun ω => ENNReal.ofReal (Z ω))),
      Continuous fun t : ℝ≥0 => W.W (t : ℝ) ω - ∫ s in (0 : ℝ)..(t : ℝ), θ ω s := by
  refine withDensity_absolutelyContinuous P _ |>.ae_le ?_
  filter_upwards [W.continuous_paths,
    drift_primitive_continuous_ae P T hT θ hθmeas hθq hθzero] with ω h1 h2
  exact (h1.comp NNReal.continuous_coe).sub h2

theorem solution
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (W : LevyStochCalc.Brownian.BrownianMotion P)
    (ℱ : Filtration ℝ ‹MeasurableSpace Ω›)
    (hW : LevyStochCalc.Brownian.IsBrownianFiltration W ℱ)
    (T : ℝ) (hT : 0 < T)
    (θ : Ω → ℝ → ℝ)
    (hθmeas : Measurable (Function.uncurry θ))
    (hθprog : LevyStochCalc.Probability.ProgressivelyMeasurable ℱ θ)
    (hθq : ∀ (t : ℝ), 0 < t →
      ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) t,
        (‖θ ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    (hθzero : ∀ (ω : Ω) (s : ℝ), T ≤ s → θ ω s = 0)
    (Z : Ω → ℝ)
    (hZ : ∀ ω : Ω,
      Z ω = Real.exp (
        LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hW θ hθmeas hθprog hθq T ω -
        (1 / 2 : ℝ) * ∫ s in (0 : ℝ)..T, θ ω s ^ 2))
    (hZmean : ∫ ω, Z ω ∂P = 1) :
    let Q : Measure Ω := P.withDensity (fun ω => ENNReal.ofReal (Z ω))
    let shifted : ℝ≥0 → Ω → ℝ := fun t ω =>
      W.W (t : ℝ) ω - ∫ s in (0 : ℝ)..(t : ℝ), θ ω s
    IsProbabilityMeasure Q ∧ IsBrownianReal shifted Q := by
  intro Q shifted
  have hQ : IsProbabilityMeasure Q :=
    withDensity_exp_isProb P Z (fun ω => by rw [hZ ω]; exact Real.exp_pos _) hZmean
  refine ⟨hQ, ?_⟩
  exact ⟨AppliedSDE.SarkkaSolin.girsanov_shifted_pre_brownian_core P W ℱ hW T hT θ hθmeas hθprog hθq hθzero Z hZ hZmean,
    shifted_cont_ae P W T hT θ hθmeas hθq hθzero Z⟩
