-- Prove2me | Definitions.Def_BellmanDP_Allocation_Model
-- name    : BellmanDP_Allocation_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-02T04:19:27.658458+00:00
-- url     : https://prove2.me/theorems/e36ffbfd-58ed-4011-b36b-ec62b109356e
-- title:
--   The multi-stage allocation equation $f(x)=\max_{0\le y\le x}[g(y)+h(x-y)+f(ay+b(x-y))]$ and its hypotheses
-- statement:
--   This file sets up Bellman's infinite-stage allocation process. A quantity $x \ge 0$ is split into $y$, allocated to a first activity with return $g(y)$, and $x-y$, allocated to a second activity with return $h(x-y)$; after the stage the first allocation shrinks to $ay$ and the second to $b(x-y)$, and the process continues with $ay + b(x-y)$.
--
--   1. The one-stage operator (Bellman, Eq. (9.3)): for a function $f$ and $0 \le y \le x$,
--   $$T(f,y) = g(y) + h(x-y) + f\big(ay + b(x-y)\big).$$
--   2. The majorant of hypothesis (1b) of Theorem 1: $m(x) = \max_{0 \le y \le x} \max(|g(y)|, |h(y)|)$.
--   3. The hypotheses (1a)–(1c) of Chapter I, Theorem 1, bundled as `AllocationHyp g h a b`: $g$ and $h$ are continuous on $[0,\infty)$ with $g(0)=h(0)=0$; with $c = \max(a,b)$, $\sum_{n=0}^{\infty} m(c^n x) < \infty$ for every $x \ge 0$; and $0 \le a < 1$, $0 \le b < 1$.
--   4. The equation (8.1): $f$ is a solution when, for every $x \ge 0$, the maximum
--   $$f(x) = \max_{0 \le y \le x} T(f,y)$$
--   is attained and equals $f(x)$.
--   5. The successive approximations (9.4)/(10.2) from an initial function $f_0$: $f_{N+1}(x) = \max_{0 \le y \le x} T(f_N, y)$.
--
--   These objects are shared by every statement of the mission.
--
--   **Formalization Note** Functions are `ℝ → ℝ`; only their values on $x \ge 0$ matter. The maximum in $m$ and in $f_{N+1}$ is written as a real supremum (`sSup`) of the image of $[0,x]$; for continuous data this set is compact and nonempty, so the supremum is the book's maximum. In the solution predicate the maximum is required to be attained (`IsGreatest`).
-- source:
--   Bellman, Dynamic Programming, Princeton University Press (1957; Princeton Landmarks ed. 2010), DOI 10.2307/j.ctv1nxcw0f, Chapter I, § 8, Eq. (8.1), p. 11; § 9, Theorem 1 hypotheses (1a)-(1c) and Eqs. (9.3)-(9.4), p. 12; § 10, Eq. (10.2), p. 16

import Mathlib

namespace BellmanDP.Allocation

/-- Bellman, *Dynamic Programming*, Ch. I, § 9, Eq. (9.3), p. 12: the one-stage return
`T(f, y) = g(y) + h(x − y) + f(ay + b(x − y))` of allocating `y` of the quantity `x` to the
first activity and `x − y` to the second, followed by the total return `f` of what is left. -/
def allocT (g h : ℝ → ℝ) (a b : ℝ) (f : ℝ → ℝ) (x y : ℝ) : ℝ :=
  g y + h (x - y) + f (a * y + b * (x - y))

/-- Ch. I, Theorem 1, hypothesis (1b), p. 12: `m(x) = Max_{0 ≤ y ≤ x} Max(|g(y)|, |h(y)|)`.
For `g, h` continuous on `[0, ∞)` and `x ≥ 0` the supremum is over a compact interval and is
attained, so it is the book's maximum. -/
noncomputable def allocM (g h : ℝ → ℝ) (x : ℝ) : ℝ :=
  sSup ((fun y => max |g y| |h y|) '' Set.Icc 0 x)

/-- Ch. I, Theorem 1, hypotheses (1a)–(1c), p. 12. -/
structure AllocationHyp (g h : ℝ → ℝ) (a b : ℝ) : Prop where
  /-- (1a) `g` is continuous for `x ≥ 0`. -/
  cont_g : ContinuousOn g (Set.Ici 0)
  /-- (1a) `h` is continuous for `x ≥ 0`. -/
  cont_h : ContinuousOn h (Set.Ici 0)
  /-- (1a) `g(0) = 0`. -/
  g_zero : g 0 = 0
  /-- (1a) `h(0) = 0`. -/
  h_zero : h 0 = 0
  /-- (1b) with `c = Max(a, b)`: `Σ_{n=0}^∞ m(cⁿ x) < ∞` for all `x ≥ 0`. -/
  summable_m : ∀ x : ℝ, 0 ≤ x → Summable (fun n : ℕ => allocM g h (max a b ^ n * x))
  /-- (1c) `0 ≤ a`. -/
  a_nonneg : 0 ≤ a
  /-- (1c) `a < 1`. -/
  a_lt_one : a < 1
  /-- (1c) `0 ≤ b`. -/
  b_nonneg : 0 ≤ b
  /-- (1c) `b < 1`. -/
  b_lt_one : b < 1

/-- Ch. I, § 8, Eq. (8.1), p. 11: `f` solves `f(x) = Max_{0 ≤ y ≤ x} T(f, y)` for every
`x ≥ 0`, the maximum being attained (`IsGreatest`). -/
def IsAllocationSolution (g h : ℝ → ℝ) (a b : ℝ) (f : ℝ → ℝ) : Prop :=
  ∀ x : ℝ, 0 ≤ x → IsGreatest ((fun y => allocT g h a b f x y) '' Set.Icc 0 x) (f x)

/-- Ch. I, § 9, Eq. (9.4), p. 12, and § 10, Eq. (10.2), p. 16: the successive approximations
`f_{N+1}(x) = Max_{0 ≤ y ≤ x} T(f_N, y)` started from `f₀`. -/
noncomputable def allocIter (g h : ℝ → ℝ) (a b : ℝ) (f₀ : ℝ → ℝ) : ℕ → ℝ → ℝ
  | 0 => f₀
  | N + 1 => fun x => sSup ((fun y => allocT g h a b (allocIter g h a b f₀ N) x y) '' Set.Icc 0 x)

end BellmanDP.Allocation


