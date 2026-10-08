-- Prove2me | Definitions.Def_WhittFLT_Composition_SkorohodD
-- name    : WhittFLT_Composition_SkorohodD
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T15:56:22.169974+00:00
-- url     : https://prove2.me/theorems/3a8e91aa-6be8-4c94-84c5-48b3e7e4195a
-- title:
--   Càdlàg paths, time changes, and $J_1$ convergence on intervals
-- statement:
--   Let $T$ be an interval of real times and $S$ a metric space. A path $x:T\to S$ belongs to $D(T,S)$ when it is right continuous and has a limit from the left at each time where a left approach is possible. A time change of a compact interval $[a,b]$ is a continuous, strictly increasing bijection from $[a,b]$ onto itself. Write $\rho_{[a,b]}$ for uniform distance. Whitt's compact $J_1$ distance is
--
--   $$
--   d_{[a,b]}(x,y)=\inf_{\lambda\in\Lambda_{[a,b]}}
--     \max\{\rho_{[a,b]}(\lambda,e),\rho_{[a,b]}(x,y\circ\lambda)\}.
--   $$
--
--   On an arbitrary interval $T$, $J_1$ convergence means convergence on every compact subinterval whose endpoints are continuity points of the limit or endpoints of $T$. The file also names uniform convergence on compact subintervals and the discontinuity set of a path. These notions provide the path-space interface reused by the paper's continuity theorems.
--
--   **Formalization Note** Paths are total functions on $\mathbb R$; only their values on $T$ count. The compact distances take values in $[0,\infty]$, avoiding a default real supremum on an unbounded set. Each time change is represented by a total function whose restriction to $[a,b]$ is continuous, strictly increasing, and onto. Convergence explicitly includes membership of every path in $D(T,S)$. Continuity at a time is relative to $T$.
-- source:
--   Whitt, Some Useful Functions for Functional Limit Theorems, Math. Oper. Res. 5(1) (1980), §2 and equation (2.1), p. 70; §4, p. 79; §6, p. 80; https://doi.org/10.1287/moor.5.1.67

import Mathlib

namespace WhittFLT.Composition

open Set Filter Topology
open scoped ENNReal

variable {S : Type*} [MetricSpace S]

/-- §2, p. 70: `x ∈ D(T, S)` — `x` is right-continuous on `T` and has limits from the left in `T`
(at the left endpoint of `T` the left-limit clause is vacuous: the filter is `⊥`). -/
def IsCadlagOn (T : Set ℝ) (x : ℝ → S) : Prop :=
  ∀ t ∈ T, ContinuousWithinAt x (T ∩ Ici t) t ∧ ∃ l : S, Tendsto x (𝓝[T ∩ Iio t] t) (𝓝 l)

/-- §2, p. 70: `λ ∈ Λ` for `T = [a, b]` — an increasing homeomorphism of `[a, b]`. -/
def IsTimeChange (a b : ℝ) (l : ℝ → ℝ) : Prop :=
  StrictMonoOn l (Icc a b) ∧ ContinuousOn l (Icc a b) ∧ l '' Icc a b = Icc a b

/-- §2, p. 70: `ρ(x, y) = sup_{a ≤ t ≤ b} m(x(t), y(t))`, the uniform metric on `[a, b]`, valued in
`ℝ≥0∞` (a real `sSup` would read an unbounded set as `0`). -/
noncomputable def supDist {E : Type*} [PseudoEMetricSpace E] (a b : ℝ) (x y : ℝ → E) : ℝ≥0∞ :=
  ⨆ t ∈ Icc a b, edist (x t) (y t)

/-- (2.1), p. 70: `d(x, y) = inf_{λ ∈ Λ} {ρ(λ, e) ∨ ρ(x, y ∘ λ)}` on `D([a, b], S)`. -/
noncomputable def j1Dist (a b : ℝ) (x y : ℝ → S) : ℝ≥0∞ :=
  ⨅ (l : ℝ → ℝ) (_ : IsTimeChange a b l), max (supDist a b l id) (supDist a b x (y ∘ l))

/-- `xₙ → x` in `D([a, b], S)`: `d(xₙ, x) → 0` for the metric (2.1). -/
def J1TendstoOn (a b : ℝ) (xs : ℕ → ℝ → S) (x : ℝ → S) : Prop :=
  Tendsto (fun n => j1Dist a b (xs n) x) atTop (𝓝 0)

/-- `t` is an endpoint of `T` belonging to `T`. -/
def IsEndpoint (T : Set ℝ) (t : ℝ) : Prop := IsLeast T t ∨ IsGreatest T t

/-- §2, p. 70: `xₙ → x` in `D(T, S)` (J₁, extended to noncompact `T`): every path lies in
`D(T, S)`, and the restrictions converge in `D([a, b])` for each compact `[a, b] ⊆ T` whose endpoints
are continuity points of `x` or endpoints of `T`. -/
def J1Tendsto (T : Set ℝ) (xs : ℕ → ℝ → S) (x : ℝ → S) : Prop :=
  (∀ n, IsCadlagOn T (xs n)) ∧ IsCadlagOn T x ∧
    ∀ a b : ℝ, a ≤ b → Icc a b ⊆ T →
      (ContinuousWithinAt x T a ∨ IsEndpoint T a) →
      (ContinuousWithinAt x T b ∨ IsEndpoint T b) → J1TendstoOn a b xs x

/-- §6, p. 80: `xₙ → x(U)`, uniform convergence on compact subintervals of `T`. -/
def UTendsto (T : Set ℝ) (xs : ℕ → ℝ → S) (x : ℝ → S) : Prop :=
  ∀ a b : ℝ, Icc a b ⊆ T → Tendsto (fun n => supDist a b (xs n) x) atTop (𝓝 0)

/-- §4, p. 79: `Disc(x)`, the discontinuity points of `x` in `T`. -/
def disc (T : Set ℝ) (x : ℝ → S) : Set ℝ := {t | t ∈ T ∧ ¬ ContinuousWithinAt x T t}

end WhittFLT.Composition


