-- Prove2me | Definitions.Def_LevyStochCalc_BSDEJ_PicardStep_F001
-- name    : LevyStochCalc_BSDEJ_PicardStep_F001
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T23:02:58.947042+00:00
-- url     : https://prove2.me/theorems/b50d41a4-41aa-4707-bc1f-c0b007aefe1e
-- title:
--   Source declarations: LevyStochCalc.BSDEJ.PicardStep
-- statement:
--   Source-preserving extracted declarations from LevyStochCalc.BSDEJ.PicardStep. Existing definitions, lemmas, instances, proofs and elaboration context are retained; generated import closure remains under review.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_BSDEJ_CadlagLegs_F000
import Definitions.Def_LevyStochCalc_BSDEJ_PicardTerminal_F000

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# One Picard step of a backward equation with jumps

The Picard map of a backward equation with jumps sends a triple `(Y', Z', U')` to the triple
solving the equation whose generator is frozen along the input, that is to the martingale
representation of the terminal datum `ξ + ∫_0^T b_s ds` for `b = f(·, Y', Z', U')`.
`PicardOutput` is the predicate satisfied by the output triple: the fields of `SolvesBSDEJ` with
the drift integral taken along the input triple, together with the terminal value of `Y` and its
finite `S²` seminorm. A fixed point of the map, that is a `PicardOutput` whose input and output
triples agree, solves the backward equation.

The output is built from the martingale representation of the centred terminal datum
(`exists_picard_integrands_of_rightCont`), the everywhere-càdlàg versions of the two stochastic
legs (`exists_cadlag_brownianLeg`, `exists_cadlag_poissonLeg`) and the primitive of the drift
(`driftLeg`), as `Y_t = c + M^W_t + M^N_t − ∫_0^t b_s ds` with `c` the mean of the terminal
datum.

## Main definitions

* `LevyStochCalc.BSDEJ.Solves.PicardOutput` — the output triple of one Picard step.

## Main statements

* `LevyStochCalc.BSDEJ.Solves.PicardOutput.toSolvesBSDEJ` — a fixed point of the Picard step
  solves the backward equation.
* `LevyStochCalc.BSDEJ.Solves.measurable_biSup_sq_of_rightContinuous` — the squared running
  supremum of a right-continuous process with measurable slices is measurable.
* `LevyStochCalc.BSDEJ.Solves.exists_picardOutput` — the Picard step has an output triple.

## References

* Tang–Li, *Necessary conditions for optimal control of stochastic systems with random jumps*,
  SIAM J. Control Optim. 32 (1994), §2.
* Barles–Buckdahn–Pardoux, *BSDEs and integral-partial differential equations*, Stochastics 60
  (1997), §2.
-/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal

namespace LevyStochCalc.BSDEJ.Solves

universe u v w

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E]
  {P : Measure Ω} [IsProbabilityMeasure P] {ν : Measure E} [SigmaFinite ν] {d : ℕ}

/-! ### The output of a Picard step -/

/-! ### Measurability of the running supremum -/

/-- The squared supremum over `[0, T]` of a process with measurable slices and right-continuous
paths is measurable. -/
theorem measurable_biSup_sq_of_rightContinuous {M : ℝ → Ω → ℝ} {T : ℝ} (hT : 0 ≤ T)
    (hm : ∀ t : ℝ, Measurable (M t))
    (hrc : ∀ (ω : Ω) (t : ℝ), Tendsto (fun s => M s ω) (𝓝[>] t) (𝓝 (M t ω))) :
    Measurable fun ω => ⨆ t ∈ Set.Icc (0 : ℝ) T, (‖M t ω‖₊ : ℝ≥0∞) ^ 2 := by
  have heq : (fun ω => ⨆ t ∈ Set.Icc (0 : ℝ) T, (‖M t ω‖₊ : ℝ≥0∞) ^ 2)
      = fun ω => (⨆ n : ℕ, (‖Probability.dyadicRunMax M T n ω‖₊ : ℝ≥0∞)) ^ 2 := by
    funext ω
    rw [SupBound.biSup_sq_eq_iSup_subtype_sq (fun t => (‖M t ω‖₊ : ℝ≥0∞)) T,
      _root_.Prove2MeSourceProof.h_755d31da2fec92eb2a10cfd6 hT (hrc ω)]
  rw [heq]
  exact (Measurable.iSup fun n =>
    Probability.measurable_enorm_dyadicRunMax hm T n).pow_const 2
/-! ### The Picard step -/

end LevyStochCalc.BSDEJ.Solves


