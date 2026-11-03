-- Prove2me | Definitions.Def_LeanLevy_Processes_PiecewisePath
-- name    : LeanLevy_Processes_PiecewisePath
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-30T22:00:40.78022+00:00
-- url     : https://prove2.me/theorems/c1ad424f-794b-4c62-a29d-42903a083048
-- title:
--   LeanLevy source module: Processes.PiecewisePath
-- statement:
--   Source-faithful definition and structural-lemma bundle for `LeanLevy.Processes.PiecewisePath`. It preserves the original Lean declarations, namespaces, assumptions and imported definitions. The upstream source is credited below. This is a draft pending Prove2Me compilation.
-- source:
--   https://github.com/slink/LeanLevy/blob/7e73fd9b23ad52956ec2756a815889a783131ce4/LeanLevy/Processes/PiecewisePath.lean

/-
Copyright (c) 2026 LeanLevy Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: LeanLevy Contributors
-/
import Definitions.Def_LeanLevy_Processes_Cadlag
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Order.Lattice.Nat
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.Calculus.Deriv.Mul

/-!
# Piecewise-affine jump paths

A **piecewise-affine jump path** is a deterministic real path that moves with constant
drift `b` between a discrete set of jump times `T 0 < T 1 < …` and jumps by `Y n` at time
`T n`. Such paths are the deterministic skeleton of a compound-Poisson-with-drift process:
once the arrival times and marks are fixed, the sample path is exactly one of these.

The number of jumps that have occurred strictly before (or at) time `t` is tracked by
`jumpCount T t`, the smallest index `n` with `t < T n`. The path value is then

`piecewisePath x₀ b T Y t = x₀ + b * t + ∑ n < jumpCount T t, Y n`.

## Main definitions

* `ProbabilityTheory.jumpCount` — the number of arrival times that have passed by time `t`.
* `ProbabilityTheory.piecewisePath` — the value of the drift-plus-jumps path at time `t`.

## Main results

* `ProbabilityTheory.lt_jumpCount_iff` — the defining characterization `n < jumpCount T t ↔ T n ≤ t`.
* `ProbabilityTheory.jumpCount_mono` — the jump count is monotone in time.
* `ProbabilityTheory.jumpCount_arrival_self` — `jumpCount T (T n) = n + 1`.
* `ProbabilityTheory.piecewisePath_eqOn_affine` — the path is affine on any interval on which
  the jump count is constant.
* `ProbabilityTheory.tendsto_piecewisePath_leftLim` — the left limit at `T n` is smaller than the
  value there by exactly the jump size `Y n`.
* `ProbabilityTheory.isCadlag_piecewisePath` — a piecewise-affine jump path is càdlàg.
* `ProbabilityTheory.piecewisePath_ito` — the deterministic Itô formula: for `f` with continuous
  derivative `f'`, the increment `f (path t) − f (path 0)` splits into the drift integral
  `∫₀ᵗ f' (path s)·b ds` plus the sum of jump increments `f (path (T n)) − f (path (T n) − Y n)`.
-/

open Filter Set Topology

namespace ProbabilityTheory

section JumpCount

variable {T : ℕ → ℝ}

/-- `jumpCount T t` is the number of arrival times among `T 0, T 1, …` that have occurred by
time `t`; equivalently the least index `n` with `t < T n`. -/
noncomputable def jumpCount (T : ℕ → ℝ) (t : ℝ) : ℕ := sInf {n | t < T n}









end JumpCount

section PiecewisePath

variable {x₀ b : ℝ} {T Y : ℕ → ℝ}

/-- `piecewisePath x₀ b T Y t` is the value at time `t` of the path that starts at `x₀`, drifts
at rate `b`, and jumps by `Y n` at each arrival time `T n`. -/
noncomputable def piecewisePath (x₀ b : ℝ) (T Y : ℕ → ℝ) (t : ℝ) : ℝ :=
  x₀ + b * t + ∑ n ∈ Finset.range (jumpCount T t), Y n













end PiecewisePath

section Ito

open MeasureTheory
open scoped Interval

variable {x₀ b : ℝ} {T Y : ℕ → ℝ} {f f' : ℝ → ℝ}









end Ito

end ProbabilityTheory


