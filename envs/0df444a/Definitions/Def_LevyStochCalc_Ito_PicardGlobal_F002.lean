-- Prove2me | Definitions.Def_LevyStochCalc_Ito_PicardGlobal_F002
-- name    : LevyStochCalc_Ito_PicardGlobal_F002
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T23:43:45.094564+00:00
-- url     : https://prove2.me/theorems/afc60223-b5a3-4f53-9ff3-d3fac953b173
-- title:
--   Source declarations: LevyStochCalc.Ito.PicardGlobal
-- statement:
--   Source-preserving extracted declarations from LevyStochCalc.Ito.PicardGlobal. Existing definitions, lemmas, instances, proofs and elaboration context are retained; generated import closure remains under review.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Ito_PicardWindow_F002
import Definitions.Def_SourceProof_217f44132bf28379085aa30a

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# From window solutions to a solution on `[0, ∞)`

The Bielecki contraction produces a solution on each finite window. Uniqueness on the shorter of
two windows makes the family consistent, and right-continuity upgrades that to an almost-sure
agreement of whole paths, so the windows can be glued along `⌈t⌉₊` into a single path map that
restricts to a window solution on every `[0, T]`.
-/

open MeasureTheory ProbabilityTheory LevyStochCalc.Probability
open scoped NNReal ENNReal

namespace LevyStochCalc.Ito.Picard

universe u v

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E]
variable {P : Measure Ω} [IsProbabilityMeasure P] {n d : ℕ}

/-! ### Right-continuity upgrades per-time equality to path equality -/

/-! ### The glued path map -/

/-! ### Consistency of a family of window solutions -/

section Glue

variable {ν : Measure E} [SigmaFinite ν]
variable (W : LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion P d)
variable (N : LevyStochCalc.Poisson.PoissonRandomMeasure P ν)
variable (ℱ : MeasureTheory.Filtration ℝ ‹MeasurableSpace Ω›)
variable (hℱW : ∀ j : Fin d, LevyStochCalc.Brownian.IsBrownianFiltration (W.W j) ℱ)
variable (hℱN : LevyStochCalc.Poisson.IsPoissonFiltration N ℱ)
variable (coeffs : LevyStochCalc.Ito.Setting.JumpDiffusionCoeffs n d E)

/-- A solution on a window starts at the initial datum. -/
theorem ae_eq_initial_of_solvesOn (x₀ : Fin n → ℝ) {X : ℝ → Ω → (Fin n → ℝ)} {T : ℝ}
    (hT : 0 ≤ T) (h : SolvesOn W N ℱ hℱW hℱN coeffs x₀ X T) :
    ∀ᵐ ω ∂P, X 0 ω = x₀ := by
  filter_upwards [h.eqn 0 ⟨le_rfl, hT⟩,
    _root_.Prove2MeSourceProof.h_217f44132bf28379085aa30a W N ℱ hℱW hℱN coeffs X x₀ h.h_σ_meas h.h_σ_progMeas h.h_σ_sq
      h.h_γ_meas h.h_γ_progMeas h.h_γ_sq] with ω h1 h2
  funext i
  rw [h1 i, h2 i]
end Glue

end LevyStochCalc.Ito.Picard


