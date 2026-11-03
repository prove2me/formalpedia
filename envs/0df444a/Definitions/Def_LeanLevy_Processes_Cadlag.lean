-- Prove2me | Definitions.Def_LeanLevy_Processes_Cadlag
-- name    : LeanLevy_Processes_Cadlag
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-30T21:59:58.364133+00:00
-- url     : https://prove2.me/theorems/a4a3e9aa-542c-47de-bb48-f02f13caa2c1
-- title:
--   LeanLevy source module: Processes.Cadlag
-- statement:
--   Source-faithful definition and structural-lemma bundle for `LeanLevy.Processes.Cadlag`. It preserves the original Lean declarations, namespaces, assumptions and imported definitions. The upstream source is credited below. This is a draft pending Prove2Me compilation.
-- source:
--   https://github.com/slink/LeanLevy/blob/7e73fd9b23ad52956ec2756a815889a783131ce4/LeanLevy/Processes/Cadlag.lean

/-
Copyright (c) 2026 LeanLevy Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: LeanLevy Contributors
-/
import Mathlib.Topology.Order.Basic
import Mathlib.Topology.Order.OrderClosed
import Mathlib.Topology.Order.DenselyOrdered
import Mathlib.Topology.Instances.NNReal.Lemmas
import Mathlib.Order.Preorder.Finite
import Mathlib.Topology.MetricSpace.Cauchy
import Mathlib.Topology.Algebra.Monoid

/-!
# Càdlàg Functions

A function is **càdlàg** (continue à droite, limite à gauche) if it is right-continuous
and has left limits at every point. This is the standard regularity condition for sample
paths of Lévy processes and many other stochastic processes.

## Main definitions

* `ProbabilityTheory.IsCadlagAt f t` — `f` is right-continuous at `t` and has a left limit at `t`.
* `ProbabilityTheory.IsCadlag f` — `f` is càdlàg everywhere.

## Main results

* `ProbabilityTheory.isCadlag_const` — constant functions are càdlàg.
* `Monotone.leftLim_exists_nat` — a monotone function `f : ℝ≥0 → ℕ` has left limits.
* `Monotone.isCadlag_of_rightContinuous_nat` — a monotone, right-continuous, ℕ-valued function
  is càdlàg.
-/

open Filter Set Topology
open scoped NNReal

namespace ProbabilityTheory

variable {α : Type*} {β : Type*} [TopologicalSpace α] [TopologicalSpace β] [Preorder α]

/-- A function `f` is **càdlàg at** `t` if it is right-continuous at `t` (i.e., continuous
within `[t, ∞)`) and has a left limit at `t` (i.e., `f` converges along the filter of
points strictly less than `t`). -/
def IsCadlagAt (f : α → β) (t : α) : Prop :=
  ContinuousWithinAt f (Ici t) t ∧ ∃ l, Tendsto f (𝓝[Iio t] t) (𝓝 l)

/-- A function `f` is **càdlàg** if it is càdlàg at every point. -/
def IsCadlag (f : α → β) : Prop :=
  ∀ t, IsCadlagAt f t







end ProbabilityTheory

/-! ### Monotone ℕ-valued functions on ℝ≥0

A monotone function `f : ℝ≥0 → ℕ` has left limits at every point. The key observation is
that the image of `Iio t` under `f` is a bounded (by `f t`) subset of `ℕ`, hence finite.
A finite nonempty subset of `ℕ` has a maximum, and by monotonicity `f` is eventually
constant near `t` from the left. -/





/-! ### Closure properties of càdlàg functions

The càdlàg condition is preserved under equality along `𝓝 t`, continuous functions are
càdlàg, and pointwise finite sums of càdlàg functions are càdlàg. The final result of this
section, `ProbabilityTheory.isCadlag_of_tendstoUniformlyOn`, shows that a uniform-on-`Iic T`
limit of càdlàg functions `ℝ → ℝ` is again càdlàg. -/

namespace ProbabilityTheory

variable {α : Type*} {β : Type*} [TopologicalSpace α] [TopologicalSpace β] [Preorder α]













end ProbabilityTheory

variable {α : Type*} {β : Type*} [TopologicalSpace α] [TopologicalSpace β] [Preorder α]


