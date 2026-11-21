-- Prove2me | Definitions.Def_LevyStochCalc_Ito_PicardSelfMap_F000A
-- name    : LevyStochCalc_Ito_PicardSelfMap_F000A
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T19:36:32.466046+00:00
-- url     : https://prove2.me/theorems/9258b5db-c486-494f-badf-30e02f97619e
-- title:
--   LevyStochCalc source module: LevyStochCalc_Ito_PicardSelfMap_F000A
-- statement:
--   Source-preserving first segment of LevyStochCalc.Ito.PicardSelfMap: constructs SBoundedProcess.ofPicardStep and defines picardStepOnS2 with the original measurable, adapted, cadlag and Bielecki-integrability hypotheses and unchanged proof bodies.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Ito_PicardStochasticLipschitz_F000

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# The Picard map as a self-map of the process space, and its difference bounds

The output of a Picard step as an element of `SBoundedProcess`, the induced self-map
`picardStepOnS2` of the process space and the identification of its path map; and the
sub-additivity bounds `(a + b + c)² ≤ 3 (a² + b² + c²)` in real, vector and `ω`-integrated form,
which split the difference of two Picard steps into its drift, diffusion and jump contributions.
-/
open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace LevyStochCalc.Ito.Picard

universe u v

variable {Ω : Type u} [MeasurableSpace Ω]
variable {E : Type v} [MeasurableSpace E]

/-- **Construct an `SBoundedProcess` from the Picard step output and
the three caller-supplied field hypotheses.**

This is the `fromCandidate`-style constructor described in the module
docstring: given the data + hypotheses that make `picardStep` well-typed
(σ-side measurability/progressive-measurability/L²-boundedness +
γ-side analogue), PLUS three explicit hypothesis bundles for the
output's joint measurability, càdlàg paths, and finite Bielecki-norm,
package the result into an `SBoundedProcess`.

The σ/γ hypothesis bundles are the same ones that `picardStep` takes;
they are reproduced here as named arguments so the constructor can be
invoked uniformly across Picard iterates (each iterate produces the
same shape of hypotheses for the next iterate, with σ/γ replaced by
σ/γ along the new candidate).

The three output-field hypotheses
(`h_out_meas`, `h_out_adapted`, `h_out_cadlag`, `h_out_sup_L2`) encode the
"missing-Mathlib-infrastructure" content that a BDG-based analytic
argument would otherwise discharge — see the module docstring. -/
noncomputable def SBoundedProcess.ofPicardStep
    {P : MeasureTheory.Measure Ω} [MeasureTheory.IsProbabilityMeasure P]
    {ν : MeasureTheory.Measure E} [MeasureTheory.SigmaFinite ν]
    {n d : ℕ}
    (W : LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion P d)
    (N : LevyStochCalc.Poisson.PoissonRandomMeasure P ν)
    (ℱ : MeasureTheory.Filtration ℝ ‹MeasurableSpace Ω›)
    (hℱW : ∀ j : Fin d, LevyStochCalc.Brownian.IsBrownianFiltration (W.W j) ℱ)
    (hℱN : LevyStochCalc.Poisson.IsPoissonFiltration N ℱ)
    (coeffs : LevyStochCalc.Ito.Setting.JumpDiffusionCoeffs n d E)
    (X : ℝ → Ω → (Fin n → ℝ))
    (x₀ : Fin n → ℝ)
    -- σ-side hypotheses for the Brownian integral
    (h_σ_meas : ∀ i : Fin n, ∀ j : Fin d,
      Measurable (Function.uncurry (fun ω s => coeffs.σ s (X s ω) i j)))
    (h_σ_progMeas : ∀ i : Fin n, ∀ j : Fin d,
        Probability.ProgressivelyMeasurable ℱ
          (fun ω s => coeffs.σ s (X s ω) i j))
    (h_σ_sq : ∀ i : Fin n, ∀ j : Fin d, ∀ T : ℝ, 0 < T →
      ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
        (‖coeffs.σ s (X s ω) i j‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    -- γ-side hypotheses for the compensated-Poisson integral
    (h_γ_meas : ∀ i : Fin n,
      Measurable (fun (p : Ω × ℝ × E) => coeffs.γ p.2.1 (X p.2.1 p.1) p.2.2 i))
    (h_γ_progMeas : ∀ i : Fin n,
        Probability.MarkedProgressivelyMeasurable ℱ
          (fun ω s e => coeffs.γ s (X s ω) e i))
    (h_γ_sq : ∀ i : Fin n, ∀ T : ℝ, 0 < T →
      ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, ∫⁻ e,
        (‖coeffs.γ s (X s ω) e i‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume ∂P < ⊤)
    (T : ℝ)
    -- Three explicit output-field hypotheses (see module docstring).
    (h_out_meas : Measurable (Function.uncurry
      (fun t ω => picardStep (E := E) W N ℱ hℱW hℱN coeffs X x₀
        h_σ_meas h_σ_progMeas h_σ_sq h_γ_meas h_γ_progMeas h_γ_sq t ω)))
    (h_out_cadlag : ∀ᵐ ω ∂P, ∀ t : ℝ,
      Filter.Tendsto
        (fun s => picardStep (E := E) W N ℱ hℱW hℱN coeffs X x₀
          h_σ_meas h_σ_progMeas h_σ_sq h_γ_meas h_γ_progMeas h_γ_sq s ω)
        (nhdsWithin t (Set.Ioi t))
        (nhds (picardStep (E := E) W N ℱ hℱW hℱN coeffs X x₀
          h_σ_meas h_σ_progMeas h_σ_sq h_γ_meas h_γ_progMeas h_γ_sq t ω))
        ∧ ∀ i : Fin n, ∃ L : ℝ,
            Filter.Tendsto
              (fun s => picardStep (E := E) W N ℱ hℱW hℱN coeffs X x₀
                h_σ_meas h_σ_progMeas h_σ_sq h_γ_meas h_γ_progMeas h_γ_sq s ω i)
              (nhdsWithin t (Set.Iio t)) (nhds L))
    (h_out_adapted : ∀ i : Fin n, Probability.ProgressivelyMeasurable ℱ
      (fun ω s => picardStep (E := E) W N ℱ hℱW hℱN coeffs X x₀
        h_σ_meas h_σ_progMeas h_σ_sq h_γ_meas h_γ_progMeas h_γ_sq s ω i))
    (h_out_sup_L2 : bieleckiNorm (P := P) 0 T
      (fun t ω => picardStep (E := E) W N ℱ hℱW hℱN coeffs X x₀
        h_σ_meas h_σ_progMeas h_σ_sq h_γ_meas h_γ_progMeas h_γ_sq t ω) < ⊤) :
    SBoundedProcess (n := n) P ℱ T where
  X := fun t ω => picardStep (E := E) W N ℱ hℱW hℱN coeffs X x₀
    h_σ_meas h_σ_progMeas h_σ_sq h_γ_meas h_γ_progMeas h_γ_sq t ω
  measurable_path := h_out_meas
  adapted := h_out_adapted
  cadlag_paths := h_out_cadlag
  sup_L2 := h_out_sup_L2
/-- **The Picard self-map on `SBoundedProcess`.**

Given:

* the Brownian motion `W`, the Poisson random measure `N`, the coefficient
  bundle `coeffs`, and the initial condition `x₀`,
* an `SBoundedProcess` candidate `X`,
* σ/γ-side measurability + L²-boundedness bundles for `coeffs` along
  `X.X` (these depend on `X` and must be supplied at call time — they
  are produced uniformly across all Picard iterates by combining the
  shared coeffs measurability with the SBoundedProcess's joint
  measurability via `sigma_along_X_measurable` and
  `gamma_along_X_measurable`),
* the **four output-field hypothesis bundles** for the lifted iterate.

…produces a new `SBoundedProcess` whose underlying path map is
exactly `picardStep` applied to `X.X`.

This is the `Φ : SBoundedProcess → SBoundedProcess` map that the Banach
fixed-point theorem consumes in
`picardFixedPoint_jumpDiffusion_exists_unique`. The contraction
estimate (proved in `Picard.lean`) operates on the
underlying path map and lifts trivially through `picardStepOnS2`. -/
noncomputable def picardStepOnS2
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
    -- σ-side hypotheses along X.X
    (h_σ_meas : ∀ i : Fin n, ∀ j : Fin d,
      Measurable (Function.uncurry (fun ω s => coeffs.σ s (X.X s ω) i j)))
    (h_σ_progMeas : ∀ i : Fin n, ∀ j : Fin d,
        Probability.ProgressivelyMeasurable ℱ
          (fun ω s => coeffs.σ s (X.X s ω) i j))
    (h_σ_sq : ∀ i : Fin n, ∀ j : Fin d, ∀ T' : ℝ, 0 < T' →
      ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T',
        (‖coeffs.σ s (X.X s ω) i j‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    -- γ-side hypotheses along X.X
    (h_γ_meas : ∀ i : Fin n,
      Measurable (fun (p : Ω × ℝ × E) => coeffs.γ p.2.1 (X.X p.2.1 p.1) p.2.2 i))
    (h_γ_progMeas : ∀ i : Fin n,
        Probability.MarkedProgressivelyMeasurable ℱ
          (fun ω s e => coeffs.γ s (X.X s ω) e i))
    (h_γ_sq : ∀ i : Fin n, ∀ T' : ℝ, 0 < T' →
      ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T', ∫⁻ e,
        (‖coeffs.γ s (X.X s ω) e i‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume ∂P < ⊤)
    -- Four output-field hypothesis bundles (see module docstring).
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
    SBoundedProcess (n := n) P ℱ T :=
  SBoundedProcess.ofPicardStep (E := E) W N ℱ hℱW hℱN coeffs X.X x₀
    h_σ_meas h_σ_progMeas h_σ_sq h_γ_meas h_γ_progMeas h_γ_sq T
    h_out_meas h_out_cadlag h_out_adapted h_out_sup_L2
end LevyStochCalc.Ito.Picard


