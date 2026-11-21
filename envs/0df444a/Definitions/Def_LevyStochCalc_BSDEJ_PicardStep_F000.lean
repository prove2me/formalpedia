-- Prove2me | Definitions.Def_LevyStochCalc_BSDEJ_PicardStep_F000
-- name    : LevyStochCalc_BSDEJ_PicardStep_F000
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T23:03:44.510325+00:00
-- url     : https://prove2.me/theorems/9740b75c-8a80-4d37-9749-6c24535bf02d
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

/-- `(Y, Z, U)` is the output of the Picard step from the input triple `(Y', Z', U')` for the
backward equation with generator `f`, terminal value `ξ` and horizon `T` driven by `D`: it
satisfies the fields of `SolvesBSDEJ` with the drift integral of the equation taken along
`(Y', Z', U')`, ends at `ξ` and has finite `S²` seminorm on `[0, T]`. -/
structure PicardOutput (D : LevyStochCalc.Driver.LevyDriver.{u, v, w} P d ν)
    (f : ℝ → ℝ → (Fin d → ℝ) → (E → ℝ) → ℝ) (ξ : Ω → ℝ) (T : ℝ)
    (Y' : ℝ → Ω → ℝ) (Z' : ℝ → Ω → (Fin d → ℝ)) (U' : ℝ → Ω → E → ℝ)
    (Y : ℝ → Ω → ℝ) (Z : ℝ → Ω → (Fin d → ℝ)) (U : ℝ → Ω → E → ℝ) : Prop where
  /-- Each coordinate of `Z` is jointly measurable. -/
  Z_meas : ∀ i : Fin d, Measurable (Function.uncurry fun ω s => Z s ω i)
  /-- Each coordinate of `Z` is progressively measurable for the augmented joint filtration. -/
  Z_prog : ∀ i : Fin d,
    LevyStochCalc.Probability.ProgressivelyMeasurable (augJoint D) fun ω s => Z s ω i
  /-- `Z` vanishes off the horizon. -/
  Z_vanish : ∀ ω s, s ∉ Set.Icc (0 : ℝ) T → Z s ω = 0
  /-- Each coordinate of `Z` has finite energy on the horizon. -/
  Z_sq : ∀ i : Fin d, LevyStochCalc.Brownian.Ito.energy P T (fun ω s => Z s ω i) ≠ ⊤
  /-- `U` is jointly measurable in the sample point, the time and the mark. -/
  U_meas : Measurable fun p : Ω × ℝ × E => U p.2.1 p.1 p.2.2
  /-- `U` is marked progressively measurable for the augmented joint filtration. -/
  U_prog : LevyStochCalc.Probability.MarkedProgressivelyMeasurable (augJoint D)
    fun ω s e => U s ω e
  /-- `U` vanishes off the horizon. -/
  U_vanish : ∀ ω s e, s ∉ Set.Icc (0 : ℝ) T → U s ω e = 0
  /-- `U` has finite marked energy on the horizon. -/
  U_sq : LevyStochCalc.Poisson.Compensated.markedEnergy P ν T (fun ω s e => U s ω e) ≠ ⊤
  /-- `Y` is jointly measurable. -/
  Y_meas : Measurable (Function.uncurry Y)
  /-- `Y` is adapted to the right-continuous augmented joint filtration. -/
  Y_adapted : MeasureTheory.Adapted (augJoint D).rightCont Y
  /-- Every path of `Y` is right-continuous with left limits. -/
  Y_cadlag : ∀ ω : Ω, ∀ t : ℝ,
    Filter.Tendsto (fun s => Y s ω) (nhdsWithin t (Set.Ioi t)) (nhds (Y t ω))
      ∧ ∃ L : ℝ, Filter.Tendsto (fun s => Y s ω) (nhdsWithin t (Set.Iio t)) (nhds L)
  /-- The backward equation with the drift frozen along the input triple, almost surely at each
  time of the horizon. -/
  eqn : ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ᵐ ω ∂P,
    Y t ω = ξ ω + (∫ s in Set.Icc t T, f s (Y' s ω) (Z' s ω) (U' s ω))
      - (LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.stochasticIntegral D.W
            (augJoint D) D.isBrownianFiltration_aug Z Z_meas Z_prog
            (sq_int_global_of_vanishing Z_vanish Z_sq) T ω
          - LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.stochasticIntegral D.W
            (augJoint D) D.isBrownianFiltration_aug Z Z_meas Z_prog
            (sq_int_global_of_vanishing Z_vanish Z_sq) t ω)
      - (LevyStochCalc.Poisson.Compensated.stochasticIntegral D.N (augJoint D)
            D.isPoissonFiltration_aug (fun ω' s e => U s ω' e) U_meas U_prog
            (marked_sq_int_global_of_vanishing U_vanish U_sq) T ω
          - LevyStochCalc.Poisson.Compensated.stochasticIntegral D.N (augJoint D)
            D.isPoissonFiltration_aug (fun ω' s e => U s ω' e) U_meas U_prog
            (marked_sq_int_global_of_vanishing U_vanish U_sq) t ω)
  /-- `Y` ends at the terminal value. -/
  Y_terminal : Y T =ᵐ[P] ξ
  /-- `Y` has finite `S²` seminorm on the horizon. -/
  Y_sup : ∫⁻ ω, (⨆ t ∈ Set.Icc (0 : ℝ) T, (‖Y t ω‖₊ : ℝ≥0∞) ^ 2) ∂P < ⊤
/-! ### Measurability of the running supremum -/

/-! ### The Picard step -/

end LevyStochCalc.BSDEJ.Solves


