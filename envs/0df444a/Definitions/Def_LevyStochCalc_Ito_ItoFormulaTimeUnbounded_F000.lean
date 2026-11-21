-- Prove2me | Definitions.Def_LevyStochCalc_Ito_ItoFormulaTimeUnbounded_F000
-- name    : LevyStochCalc_Ito_ItoFormulaTimeUnbounded_F000
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T23:09:55.761646+00:00
-- url     : https://prove2.me/theorems/2b8277d4-f15b-4d29-8901-558dbfed8932
-- title:
--   Source declarations: LevyStochCalc.Ito.ItoFormulaTimeUnbounded
-- statement:
--   Source-preserving extracted declarations from LevyStochCalc.Ito.ItoFormulaTimeUnbounded. Existing definitions, lemmas, instances, proofs and elaboration context are retained; generated import closure remains under review.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Brownian_VectorItoTimeAug_F000
import Definitions.Def_LevyStochCalc_Ito_ItoFormulaUnboundedClamp_F000
import Definitions.Def_LevyStochCalc_Ito_ItoFormulaUnboundedClamp_F001
import Definitions.Def_LevyStochCalc_Ito_ItoFormulaUnboundedClamp_F002
import Definitions.Def_LevyStochCalc_Ito_ItoFormulaUnboundedIntegrands_F000
import Definitions.Def_LevyStochCalc_Ito_ItoFormulaUnboundedIntegrands_F001
import Definitions.Def_LevyStochCalc_Ito_ItoFormulaUnboundedLimit_F000
import Definitions.Def_LevyStochCalc_Ito_ItoFormulaUnboundedLimit_F001

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Itô's formula for a time-dependent function of an Itô process with unbounded coefficients

Applying the state-only formula for unbounded coefficients to the process augmented by its own
time separates the time derivative — paired with the unit drift of the extra coordinate — from
the space derivatives, with no pointwise bound on either the diffusion matrix or the drift. The
extra coordinate carries no diffusion, so it contributes neither a stochastic integral nor a
quadratic-variation term.

## Main statements

* `LevyStochCalc.Brownian.Ito.sq_timeAugDrift` — the drift with a time coordinate prepended has
  finite energy on every bounded window.
* `LevyStochCalc.Brownian.Ito.measurable_timeAugInit` — the initial value with the origin
  prepended is measurable in each coordinate.
* `LevyStochCalc.Brownian.Ito.IsVectorItoVersion.itoFormulaTime_of_unbounded` — Itô's formula for
  a time-dependent function, with no bound on the coefficients.
-/

namespace LevyStochCalc.Brownian.Ito

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

universe u

section AugDrift

variable {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {n : ℕ}

/-- The drift with a time coordinate prepended has finite energy on every bounded window as soon
as the original drift does, the extra row being the constant `1`. -/
theorem sq_timeAugDrift (bdrift : Fin n → Ω → ℝ → ℝ)
    (hbq : ∀ (p : Fin n) (T : ℝ), 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
      (‖bdrift p ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    (p : Fin (n + 1)) (T : ℝ) (hT : 0 < T) :
    ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
      (‖timeAugDrift bdrift p ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤ := by
  induction p using Fin.cases with
  | zero =>
    have hone : ∀ (ω : Ω) (s : ℝ), |timeAugDrift bdrift 0 ω s| ≤ 1 := by
      intro ω s
      simp [timeAugDrift]
    exact _root_.Prove2MeSourceProof.h_2abda5a9ee832ec6f2f4409e hone T hT
  | succ q => simpa [timeAugDrift] using hbq q T hT
end AugDrift

section AugInit

variable {Ω : Type u} {n : ℕ}

/-- The initial value with the origin prepended as a time coordinate is measurable in each
coordinate with respect to any σ-algebra for which the original coordinates are. -/
theorem measurable_timeAugInit {m : MeasurableSpace Ω} {X₀ : Ω → Fin n → ℝ}
    (hX₀ : ∀ p : Fin n, Measurable[m] fun ω => X₀ ω p) (p : Fin (n + 1)) :
    Measurable[m] fun ω => timeAugInit X₀ ω p := by
  induction p using Fin.cases with
  | zero =>
    simp only [timeAugInit, Fin.cons_zero]
    exact measurable_const
  | succ q => simpa [timeAugInit] using hX₀ q
end AugInit

section TimeFormula

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

end TimeFormula

end LevyStochCalc.Brownian.Ito


