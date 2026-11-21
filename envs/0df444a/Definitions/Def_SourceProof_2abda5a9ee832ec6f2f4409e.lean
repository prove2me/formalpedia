-- Prove2me | Definitions.Def_SourceProof_2abda5a9ee832ec6f2f4409e
-- name    : SourceProof_2abda5a9ee832ec6f2f4409e
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T19:46:39.883241+00:00
-- url     : https://prove2.me/theorems/97142ab2-4049-489e-8bcf-6b25645a2dcc
-- title:
--   LevyStochCalc source module: SourceProof_2abda5a9ee832ec6f2f4409e
-- statement:
--   The original source theorem `LevyStochCalc.Brownian.Ito.energy_lt_top_of_bounded` comes from the `LevyStochCalc.Brownian.ItoCutoff` module. The staged Lean declaration includes its source proof and dependency references.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Brownian_ItoLocality_F001
import Definitions.Def_LevyStochCalc_Brownian_SmoothCutoff_F000
import Definitions.Def_LevyStochCalc_Brownian_VectorItoFormula_F000
import Definitions.Def_LevyStochCalc_Probability_ExitTime_F001

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Itô's formula for a twice continuously differentiable function

Multiplying `f` by a smooth box cutoff leaves it, together with its first two derivatives,
unchanged on a cube and makes them bounded and uniformly continuous. Along a path stopped before
it leaves that cube the two functions therefore give the same integrands, and the local property
of the Itô integral transfers the stochastic terms.

## Main statements

* `LevyStochCalc.cutoffFun` — the cut-off function.
* `LevyStochCalc.fderiv_cutoffFun` — its first two derivatives agree with `f`'s on the cube.
* `LevyStochCalc.Brownian.Ito.IsVectorItoVersion.itoFormula_of_contDiff` — Itô's formula for a
  twice continuously differentiable function, with no bound on its derivatives.
-/

namespace LevyStochCalc

open scoped Topology

section Cutoff

variable {n : ℕ}

end Cutoff

namespace Brownian.Ito

open MeasureTheory ProbabilityTheory LevyStochCalc.Brownian.Multidim LevyStochCalc.Probability
open scoped NNReal ENNReal

universe u

section Bounded

variable {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]


theorem _root_.Prove2MeSourceProof.h_2abda5a9ee832ec6f2f4409e {K : Ω → ℝ → ℝ} {M : ℝ} (hM : ∀ ω s, |K ω s| ≤ M) :
    ∀ T : ℝ, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
      (‖K ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤ := by
  intro T _hT
  have hpt : ∀ (ω : Ω) (s : ℝ),
      (‖K ω s‖₊ : ℝ≥0∞) ^ 2 ≤ ((Real.toNNReal M : ℝ≥0) : ℝ≥0∞) ^ 2 := by
    intro ω s
    have h0 : (0 : ℝ) ≤ M := le_trans (abs_nonneg _) (hM ω s)
    have h1 : ‖K ω s‖₊ ≤ Real.toNNReal M := by
      rw [← NNReal.coe_le_coe, coe_nnnorm, Real.coe_toNNReal M h0]
      simpa [Real.norm_eq_abs] using hM ω s
    exact pow_le_pow_left' (by exact_mod_cast h1) 2
  calc ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, (‖K ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P
      ≤ ∫⁻ _ω : Ω, ∫⁻ _s in Set.Icc (0 : ℝ) T,
          ((Real.toNNReal M : ℝ≥0) : ℝ≥0∞) ^ 2 ∂volume ∂P :=
        MeasureTheory.lintegral_mono fun ω => MeasureTheory.lintegral_mono fun s => hpt ω s
    _ < ⊤ := by
        simp only [MeasureTheory.lintegral_const, MeasureTheory.Measure.restrict_apply_univ,
          Real.volume_Icc, measure_univ, mul_one]
        exact ENNReal.mul_lt_top (ENNReal.pow_lt_top ENNReal.coe_lt_top) ENNReal.ofReal_lt_top
end Bounded

section Formula

open LevyStochCalc.Brownian.Multidim

variable {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {n d : ℕ} {W : Multidim.MultidimBrownianMotion P d}
  {ℱ : Filtration ℝ ‹MeasurableSpace Ω›}
  {hcoord : ∀ k : Fin d, IsBrownianFiltration (W.W k) ℱ}
  {H : Fin n → Fin d → Ω → ℝ → ℝ}
  {hHm : ∀ p k, Measurable (Function.uncurry (H p k))}
  {hHp : ∀ p k, Probability.ProgressivelyMeasurable ℱ (H p k)}
  {hHs : ∀ (p : Fin n) (k : Fin d) (T : ℝ), 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
    (‖H p k ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤}
  {X₀ : Ω → Fin n → ℝ} {bdrift : Fin n → Ω → ℝ → ℝ} {X : ℝ → Ω → Fin n → ℝ}
  {C : ℝ} (hC0 : 0 ≤ C)
  (hCH : ∀ (p : Fin n) (k : Fin d) (ω : Ω) (s : ℝ), |H p k ω s| ≤ C)

end Formula

end Brownian.Ito

end LevyStochCalc


