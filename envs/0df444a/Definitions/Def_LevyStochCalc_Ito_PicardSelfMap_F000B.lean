-- Prove2me | Definitions.Def_LevyStochCalc_Ito_PicardSelfMap_F000B
-- name    : LevyStochCalc_Ito_PicardSelfMap_F000B
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T19:43:12.345389+00:00
-- url     : https://prove2.me/theorems/207ddcb3-c78e-4a84-a127-a302c98bcd79
-- title:
--   LevyStochCalc source module: LevyStochCalc_Ito_PicardSelfMap_F000B
-- statement:
--   Source-preserving second segment of the Picard self-map: the original path-map projection lemma with unchanged binders, statement and proof, isolated for bounded Lean elaboration.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Ito_PicardSelfMap_F000A
open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
namespace LevyStochCalc.Ito.Picard
universe u v
variable {Ω : Type u} [MeasurableSpace Ω]
variable {E : Type v} [MeasurableSpace E]
-- `picardStep`, its two integral components and `bieleckiNorm` unfold to `Finset` sums
-- over `Fin d` / `Fin n` and to the `L²`-limit integrals; the statement below repeats
-- those terms verbatim on both sides, so unfolding them during unification only costs
-- time (296760 `Fin.foldr` reductions before this seal).
attribute [local irreducible] picardStep picardStep_diffusion picardStep_jump bieleckiNorm
attribute [local irreducible]
  LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.stochasticIntegral
attribute [local irreducible] LevyStochCalc.Brownian.Ito.stochasticIntegral
attribute [local irreducible] LevyStochCalc.Poisson.Compensated.stochasticIntegral

set_option maxHeartbeats 400000 in
-- The three output hypotheses restate the whole Picard term, so checking them against
-- `picardStepOnS2`'s binders compares the filtration argument of every progressive-
-- measurability side condition; that alone exceeds the default budget.
-- maxHeartbeats: the `rfl` below unifies the full argument bundle of `ofPicardStep`.
set_option maxHeartbeats 1600000 in
/-- The path map of `picardStepOnS2 W N ℱ … X` is `picardStep` applied to `X.X`, so a
bound on `picardStep` is a bound on the lifted iterate's path map. -/
@[simp]
lemma picardStepOnS2_X
    {P : MeasureTheory.Measure Ω} [MeasureTheory.IsProbabilityMeasure P]
    {ν : MeasureTheory.Measure E} [MeasureTheory.SigmaFinite ν]
    {n d : ℕ}
    (W : LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion P d)
    (N : LevyStochCalc.Poisson.PoissonRandomMeasure P ν)
    (ℱ : MeasureTheory.Filtration ℝ ‹MeasurableSpace Ω›)
    (hℱW : ∀ j : Fin d, LevyStochCalc.Brownian.IsBrownianFiltration (W.W j) ℱ)
    (hℱN : LevyStochCalc.Poisson.IsPoissonFiltration N ℱ)
    (coeffs : LevyStochCalc.Ito.Setting.JumpDiffusionCoeffs n d E)
    (x₀ : Fin n → ℝ) (T : ℝ)
    (X : SBoundedProcess (n := n) P ℱ T)
    (h_σ_meas : ∀ i : Fin n, ∀ j : Fin d,
      Measurable (Function.uncurry (fun ω s => coeffs.σ s (X.X s ω) i j)))
    (h_σ_progMeas : ∀ i : Fin n, ∀ j : Fin d,
        Probability.ProgressivelyMeasurable ℱ
          (fun ω s => coeffs.σ s (X.X s ω) i j))
    (h_σ_sq : ∀ i : Fin n, ∀ j : Fin d, ∀ T' : ℝ, 0 < T' →
      ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T',
        (‖coeffs.σ s (X.X s ω) i j‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    (h_γ_meas : ∀ i : Fin n,
      Measurable (fun (p : Ω × ℝ × E) => coeffs.γ p.2.1 (X.X p.2.1 p.1) p.2.2 i))
    (h_γ_progMeas : ∀ i : Fin n,
        Probability.MarkedProgressivelyMeasurable ℱ
          (fun ω s e => coeffs.γ s (X.X s ω) e i))
    (h_γ_sq : ∀ i : Fin n, ∀ T' : ℝ, 0 < T' →
      ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T', ∫⁻ e,
        (‖coeffs.γ s (X.X s ω) e i‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume ∂P < ⊤)
    (h_out_meas : Measurable (Function.uncurry
      (fun t ω => picardStep (E := E) W N ℱ hℱW hℱN coeffs X.X x₀
        h_σ_meas h_σ_progMeas h_σ_sq h_γ_meas h_γ_progMeas h_γ_sq t ω)))
    (h_out_adapted : ∀ i : Fin n, Probability.ProgressivelyMeasurable ℱ
      (fun ω s => picardStep (E := E) W N ℱ hℱW hℱN coeffs X.X x₀
        h_σ_meas h_σ_progMeas h_σ_sq h_γ_meas h_γ_progMeas h_γ_sq s ω i))
    (h_out_cadlag : ∀ᵐ ω ∂P, ∀ t : ℝ,
      Filter.Tendsto
        (fun s => picardStep (E := E) W N ℱ hℱW hℱN coeffs X.X x₀
          h_σ_meas h_σ_progMeas h_σ_sq h_γ_meas h_γ_progMeas h_γ_sq s ω)
        (nhdsWithin t (Set.Ioi t))
        (nhds (picardStep (E := E) W N ℱ hℱW hℱN coeffs X.X x₀
          h_σ_meas h_σ_progMeas h_σ_sq h_γ_meas h_γ_progMeas h_γ_sq t ω))
        ∧ ∀ i : Fin n, ∃ L : ℝ,
            Filter.Tendsto
              (fun s => picardStep (E := E) W N ℱ hℱW hℱN coeffs X.X x₀
                h_σ_meas h_σ_progMeas h_σ_sq h_γ_meas h_γ_progMeas h_γ_sq s ω i)
              (nhdsWithin t (Set.Iio t)) (nhds L))
    (h_out_sup_L2 : bieleckiNorm (P := P) 0 T
      (fun t ω => picardStep (E := E) W N ℱ hℱW hℱN coeffs X.X x₀
        h_σ_meas h_σ_progMeas h_σ_sq h_γ_meas h_γ_progMeas h_γ_sq t ω) < ⊤) :
    (picardStepOnS2 (E := E) W N ℱ hℱW hℱN coeffs x₀ T X
        h_σ_meas h_σ_progMeas h_σ_sq h_γ_meas h_γ_progMeas h_γ_sq
        h_out_meas h_out_adapted h_out_cadlag h_out_sup_L2).X
      = fun t ω => picardStep (E := E) W N ℱ hℱW hℱN coeffs X.X x₀
          h_σ_meas h_σ_progMeas h_σ_sq h_γ_meas h_γ_progMeas h_γ_sq t ω := by
  rfl
end LevyStochCalc.Ito.Picard


