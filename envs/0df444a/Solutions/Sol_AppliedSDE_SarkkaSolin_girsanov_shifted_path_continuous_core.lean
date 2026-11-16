-- Prove2me | solution 1 for AppliedSDE.SarkkaSolin.girsanov_shifted_path_continuous_core
-- status  : ACCEPTED   (prove)
-- author  : @Himan
-- created : 2026-11-15T22:29:52.378175+00:00
-- url     : https://prove2.me/submissions/5d212d46-6d46-4326-8359-316028a6d263

import Mathlib
import Definitions.Def_KLSModular_LevyStochCalc_Brownian_Filtered
import Definitions.Def_KLSModular_LevyStochCalc_Brownian_ItoL2CompletionMaster
open MeasureTheory ProbabilityTheory Filter LevyStochCalc.Brownian
open scoped ENNReal NNReal Topology

/-- Time-local square integrability of a jointly measurable integrand makes its
primitive `t ↦ ∫₀ᵗ θ ω s ds` continuous on `ℝ≥0` for almost every `ω`. -/
theorem girsanov_drift_primitive_continuous_ae
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (θ : Ω → ℝ → ℝ) (hθmeas : Measurable (Function.uncurry θ))
    (hθq : ∀ (t : ℝ), 0 < t →
      ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) t, (‖θ ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤) :
    ∀ᵐ ω ∂P, Continuous (fun t : ℝ≥0 => ∫ s in (0 : ℝ)..(t : ℝ), θ ω s) := by
  have hae : ∀ᵐ ω ∂P, ∀ N : ℕ,
      ∫⁻ s in Set.Icc (0 : ℝ) ((N : ℝ) + 1), (‖θ ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume < ⊤ := by
    rw [ae_all_iff]
    intro N
    refine ae_lt_top ?_ (hθq ((N : ℝ) + 1) (by positivity)).ne
    exact Measurable.lintegral_prod_right'
      (f := fun p : Ω × ℝ => (‖θ p.1 p.2‖₊ : ℝ≥0∞) ^ 2)
      ((hθmeas.nnnorm.coe_nnreal_ennreal).pow_const 2)
  filter_upwards [hae] with ω hω
  have hm : Measurable (θ ω) := hθmeas.of_uncurry_left
  have hpt : ∀ a : ℝ≥0∞, a ≤ 1 + a ^ 2 := by
    intro a
    rcases le_total a 1 with h | h
    · exact h.trans le_self_add
    · calc a = a * 1 := (mul_one a).symm
        _ ≤ a * a := by gcongr
        _ = a ^ 2 := (sq a).symm
        _ ≤ 1 + a ^ 2 := le_add_self
  have hint : ∀ N : ℕ, IntegrableOn (θ ω) (Set.Icc (0 : ℝ) ((N : ℝ) + 1)) volume := by
    intro N
    refine ⟨hm.aestronglyMeasurable, ?_⟩
    calc ∫⁻ s in Set.Icc (0 : ℝ) ((N : ℝ) + 1), ‖θ ω s‖ₑ ∂volume
        ≤ ∫⁻ s in Set.Icc (0 : ℝ) ((N : ℝ) + 1), (1 + (‖θ ω s‖₊ : ℝ≥0∞) ^ 2) ∂volume :=
          lintegral_mono (fun s => hpt _)
      _ = ∫⁻ s in Set.Icc (0 : ℝ) ((N : ℝ) + 1), (1 : ℝ≥0∞) ∂volume +
            ∫⁻ s in Set.Icc (0 : ℝ) ((N : ℝ) + 1), (‖θ ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume :=
          lintegral_add_left measurable_const _
      _ < ⊤ := by
          refine ENNReal.add_lt_top.mpr ⟨?_, hω N⟩
          simp
  rw [continuous_iff_continuousAt]
  intro t₀
  obtain ⟨N, hN⟩ := exists_nat_gt (t₀ : ℝ)
  set g : ℝ → ℝ := (Set.Icc (0 : ℝ) ((N : ℝ) + 1)).indicator (θ ω) with hg
  have hgint : Integrable g volume := (hint N).integrable_indicator measurableSet_Icc
  have hcont : Continuous (fun t : ℝ≥0 => ∫ s in (0 : ℝ)..(t : ℝ), g s) :=
    (intervalIntegral.continuous_primitive (fun a b => hgint.intervalIntegrable) 0).comp
      NNReal.continuous_coe
  refine hcont.continuousAt.congr ?_
  have hopen : IsOpen {t : ℝ≥0 | (t : ℝ) < (N : ℝ) + 1} :=
    isOpen_lt NNReal.continuous_coe continuous_const
  filter_upwards [hopen.mem_nhds (show (t₀ : ℝ) < (N : ℝ) + 1 by linarith)] with t ht
  apply intervalIntegral.integral_congr
  intro x hx
  rw [Set.uIcc_of_le t.coe_nonneg] at hx
  have hx' : x ∈ Set.Icc (0 : ℝ) ((N : ℝ) + 1) := ⟨hx.1, hx.2.trans (le_of_lt ht)⟩
  simp [hg, Set.indicator_of_mem hx']

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
    (∀ᵐ ω ∂Q, Continuous (fun t : ℝ≥0 => shifted t ω)) := by
  intro Q shifted
  have hQ : Q ≪ P := withDensity_absolutelyContinuous _ _
  have hP : ∀ᵐ ω ∂P, Continuous (fun t : ℝ≥0 => shifted t ω) := by
    filter_upwards [W.continuous_paths,
      girsanov_drift_primitive_continuous_ae P θ hθmeas hθq] with ω h1 h2
    exact (h1.comp NNReal.continuous_coe).sub h2
  exact hQ.ae_le hP
