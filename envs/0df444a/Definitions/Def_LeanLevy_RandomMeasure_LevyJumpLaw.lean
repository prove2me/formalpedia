-- Prove2me | Definitions.Def_LeanLevy_RandomMeasure_LevyJumpLaw
-- name    : LeanLevy_RandomMeasure_LevyJumpLaw
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-31T10:25:33.346129+00:00
-- url     : https://prove2.me/theorems/796a9313-f9fe-4fbb-92b2-057ac371b30b
-- title:
--   LeanLevy source module: RandomMeasure.LevyJumpLaw
-- statement:
--   Pinned source definition and helper bundle. The original generated Lean module passed the earlier local build. This draft awaits Prove2Me remote compilation.
-- source:
--   https://github.com/slink/LeanLevy/blob/7e73fd9b23ad52956ec2756a815889a783131ce4/LeanLevy/RandomMeasure/LevyJumpLaw.lean

/-
Copyright (c) 2026 LeanLevy Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: LeanLevy Contributors
-/
import Definitions.Def_LeanLevy_RandomMeasure_PoissonMartingale
import Definitions.Def_LeanLevy_Levy_LevyKhintchineUniqueness

/-!
# The assembled jump law

This file combines the two jump components of a Lévy process — the compound-Poisson large-jump
sum and the compensated small-jump integral — with a constant drift, and identifies the
characteristic function of their sum at a fixed time `t`.

The large-jump sum and the compensated small jumps are supported on the disjoint mark bands
`{|x| ≥ 1}` and `(-1, 1)`, so they are independent; their characteristic functions multiply.
Each factor is a compound-Poisson / compensated exponential of a band integral against the Lévy
measure `ν`, and the two band integrals reassemble the Lévy–Khintchine jump integral at split
radius `1`. Adding the deterministic drift `b · t` supplies the linear term, giving the
characteristic function `exp (t · ψ(ξ))` where `ψ` is the Lévy–Khintchine exponent of the triple
`(b, 0, ν)` — a triple with **zero Gaussian variance**, as befits a pure-jump process.

## Main results

* `ProbabilityTheory.charFun_map_levyJumpSum_eq_exponent` — **the assembled jump law**: for
  `0 ≤ t`, the fixed-time marginal law of `b · t + (large-jump sum) + (compensated small jumps)`
  has characteristic function `exp (t · (b, 0, ν).exponent ξ)`.
* `ProbabilityTheory.isInfinitelyDivisible_map_levyJumpSum` — for `0 ≤ t`, that same fixed-time
  marginal law is **infinitely divisible**: it is the Lévy–Khintchine law of the `t`-scaled triple
  `(t · b, 0, ENNReal.ofReal t • ν)`.
* `ProbabilityTheory.levyJumpProcess` — the **jump process** indexed by `ℝ≥0`: drift plus large-jump
  sum plus compensated small jumps. Only its law-level Lévy structure is established; no path
  regularity is claimed.
* `ProbabilityTheory.hasIndependentIncrements_levyJumpProcess` — **the jump process has independent
  increments** over any monotone time grid.
* `ProbabilityTheory.charFun_map_levyJumpProcess_sub` — **the increment law**: the increment over
  `(s, t]` has characteristic function `exp ((t − s) · (b, 0, ν).exponent ξ)`.
* `ProbabilityTheory.hasStationaryIncrements_levyJumpProcess` — **stationary increments**: the law
  of an increment depends only on its length.
* `ProbabilityTheory.exists_levyJumpProcess` — **the realization theorem** (headline): every
  pure-jump Lévy triple `(b, 0, ν)` is realized in law by a process with independent stationary
  increments, a.e. zero start, and marginal characteristic functions `exp (t · ψ_{(b,0,ν)})`. NO
  path regularity is claimed.
-/

open MeasureTheory Complex
open scoped ENNReal NNReal

namespace ProbabilityTheory

variable {Ω : Type} [MeasurableSpace Ω] {K : ℕ → Ω → ℕ} {X : ℕ → ℕ → Ω → ℝ × ℝ}
  {ν : Measure ℝ} [SigmaFinite ν] {μ : Measure Ω}







/-! ### The jump process and its independent increments

The three jump ingredients — a constant drift, the compound-Poisson large-jump sum, and the
compensated small-jump integral — are assembled into a single process indexed by `ℝ≥0`. Over a time
step `(s, t]` each ingredient reads only the marks of the Poisson random measure inside the band
`(s, t] × ℝ`, and consecutive bands over a monotone grid are pairwise disjoint. Since the evaluation
sigma-algebras of disjoint regions are mutually independent (`iIndep_prmEvalSigma`), the increments
over such a grid are mutually independent. -/

/-- The **jump process** of a Lévy measure: drift plus large-jump sum plus compensated
small jumps, indexed by `ℝ≥0`. Its law-level Lévy structure (independent and stationary
increments, increment charFun `exp((t−s)·ψ)`) is proved below; NO path regularity is claimed. -/
noncomputable def levyJumpProcess [IsProbabilityMeasure μ]
    (hd : IsPoissonPointFamily K X ((volume : Measure ℝ).prod ν) μ) (hν : IsLevyMeasure ν)
    (b : ℝ) (t : ℝ≥0) (ω : Ω) : ℝ :=
  b * (t : ℝ) + levyLargeJumpSum K X (t : ℝ) ω + levyCompensatedSmallJump hd hν (t : ℝ) ω













end ProbabilityTheory


