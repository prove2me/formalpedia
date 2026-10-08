-- Prove2me | Definitions.Def_FZEchelon_Discounted_Programs
-- name    : FZEchelon_Discounted_Programs
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-05T11:24:22.958956+00:00
-- url     : https://prove2.me/theorems/88c54009-c2cc-4841-8cf8-e199eeea6398
-- title:
--   The finite-horizon programs (1), (2), (3), (5): $\hat g_n$, $g_n^r$, $\hat g_n^d$, $g_n^d$, and the induced penalties $\hat P_n$
-- statement:
--   This file defines the finite-horizon dynamic programs of Federgruen and Zipkin (1984), §1, indexed by the number $n$ of periods remaining. Write $u$ for a demand with law $\nu$ and $E$ for expectation over it.
--
--   1. **The outlet program (2)** (p. 823): $g_0^r = 0$ and, for $n \ge 1$,
--   $$
--   g_n^r(x^r) = \min_{z \ge 0}\big\{c^r z + R(x^r + z) + \alpha E g^r_{n-1}(x^r + z - u)\big\}.
--   $$
--   2. **Critical numbers** (p. 823). $x_n^{r*}$, the critical number for period $n \ge 1$, is a global minimizer of $w \mapsto c^r w + R(w) + \alpha E g^r_{n-1}(w - u)$.
--   3. **The induced penalty costs** (p. 823), $n \ge 1$:
--   $$
--   \hat P_n(x) = \begin{cases} 0, & x \ge x_n^{r*},\\ c^r(x - x_n^{r*}) + [R(x) - R(x_n^{r*})] + \alpha E[g^r_{n-1}(x-u) - g^r_{n-1}(x_n^{r*} - u)], & x < x_n^{r*}.\end{cases}
--   $$
--   4. **The depot program (3)** (p. 823): $\hat g_0^d = 0$ and, for $n \ge 1$,
--   $$
--   \hat g_n^d(\hat y, v^d) = \min_{y \ge 0}\big\{c^d(y) + D(v^d + y^L) + \hat P_n(v^d + y^L) + \alpha E \hat g^d_{n-1}[(y, y^1, \dots, y^{L-1}), v^d + y^L - u]\big\}.
--   $$
--   5. **The depot program (5)** (p. 825): $g_n^d$ is defined like $\hat g_n^d$, with the stationary penalty $P$ in place of $\hat P_n$.
--   6. **The system program (1)** (p. 822): $\hat g_0 = 0$ and, for $n \ge 1$,
--   $$
--   \hat g_n(\hat y, v^d, x^r) = \min_{y, z}\big\{c^d(y) + D(v^d + y^L) + c^r z + R(x^r + z) + \alpha E \hat g_{n-1}[(y, y^1, \dots, y^{L-1}), v^d + y^L - u, x^r + z - u]\big\},
--   $$
--   the minimum over $y \ge 0$, $z \ge 0$, $x^r + z \le v^d + y^L$.
--
--   The decomposition of program (1) into (2) and (3), and the comparison of (3) with (5), are the finite-horizon tools from which the paper obtains the infinite-horizon result.
--
--   **Formalization Note.** Each "min" is a real infimum over the feasible actions. On the physical states (outstanding orders $\ge 0$, $x^r \le v^d$) the feasible set is nonempty and the objective is bounded below, so the infimum is the paper's value. $\hat P_0$ is set to $0$; the paper defines $\hat P_n$ only for $n \ge 1$, and program (3) uses only those. The critical numbers are not defined here: theorems take a sequence `xn` with the hypothesis `IsCriticalNumberSeq`, which says that `xn (n+1)` minimizes the period-$(n+1)$ objective.
-- source:
--   Federgruen and Zipkin, Computational Issues in an Infinite-Horizon, Multiechelon Inventory Model, Oper. Res. 32(4), 1984, p. 822 eq. (1); p. 823 eqs. (2), (3) and the definition of P̂_n; p. 825 eq. (5)

import Mathlib
import Definitions.Def_FZEchelon_Discounted_Model

open MeasureTheory

namespace FZEchelon.Discounted

namespace Model

variable (M : Model)

/-- The outlet program (2), p. 823, indexed by the number `n` of periods remaining:
`g_0^r = 0`, `g_{n+1}^r(x) = min_{z ≥ 0} {c^r z + R(x + z) + α E g_n^r(x + z − u)}`. -/
noncomputable def gr : ℕ → ℝ → ℝ
  | 0 => fun _ => 0
  | n + 1 => fun x =>
      ⨅ z : {z : ℝ // 0 ≤ z}, M.cr * z + M.R (x + z) + M.α * ∫ t, gr n (x + z - t) ∂M.ν

/-- The outlet objective of period `n + 1` as a function of the post-shipment position `w`:
`c^r w + R(w) + α E g_n^r(w − u)` (so `g_{n+1}^r(x) = min_{w ≥ x} outletObj n w − c^r x`). -/
noncomputable def outletObj (n : ℕ) (w : ℝ) : ℝ :=
  M.cr * w + M.R w + M.α * ∫ t, M.gr n (w - t) ∂M.ν

/-- `xn (n + 1)` is a critical number `x_{n+1}^{r*}` of program (2) for period `n + 1`: a global
minimizer of `outletObj n` (p. 823). `xn 0` is not used. -/
def IsCriticalNumberSeq (xn : ℕ → ℝ) : Prop :=
  ∀ (n : ℕ) (w : ℝ), M.outletObj n (xn (n + 1)) ≤ M.outletObj n w

/-- The induced penalty cost functions `P̂_n`, `n ≥ 1` (p. 823): `P̂_n(x) = 0` for
`x ≥ x_n^{r*}`, and for `x < x_n^{r*}`
`P̂_n(x) = c^r (x − x_n^{r*}) + [R(x) − R(x_n^{r*})] + α E[g_{n−1}^r(x − u) − g_{n−1}^r(x_n^{r*} − u)]`.
The value at `n = 0` is set to `0`; the paper defines `P̂_n` only for `n ≥ 1`. -/
noncomputable def Phat (xn : ℕ → ℝ) : ℕ → ℝ → ℝ
  | 0 => fun _ => 0
  | n + 1 => fun x =>
      if xn (n + 1) ≤ x then 0
      else M.cr * (x - xn (n + 1)) + (M.R x - M.R (xn (n + 1)))
        + M.α * ∫ t, (M.gr n (x - t) - M.gr n (xn (n + 1) - t)) ∂M.ν

/-- The depot program (3), p. 823: `ĝ_0^d = 0` and
`ĝ_{n+1}^d(ŷ, v^d) = min_{y ≥ 0} {c^d(y) + D(v^d + y^L) + P̂_{n+1}(v^d + y^L)
  + α E ĝ_n^d[(y, y^1, …, y^{L−1}), v^d + y^L − u]}`. -/
noncomputable def ghatd (xn : ℕ → ℝ) : ℕ → M.DepotState → ℝ
  | 0 => fun _ => 0
  | n + 1 => fun p =>
      ⨅ y : {y : ℝ // 0 ≤ y}, M.orderCost y + M.D (p.2 + M.arrival p.1 y)
        + M.Phat xn (n + 1) (p.2 + M.arrival p.1 y)
        + M.α * ∫ t, ghatd xn n (M.shift p.1 y, p.2 + M.arrival p.1 y - t) ∂M.ν

/-- The depot program (5), p. 825: as (3) with the stationary penalty `P` in place of `P̂_n`. -/
noncomputable def gd (xstar : ℝ) : ℕ → M.DepotState → ℝ
  | 0 => fun _ => 0
  | n + 1 => fun p =>
      ⨅ y : {y : ℝ // 0 ≤ y}, M.orderCost y + M.D (p.2 + M.arrival p.1 y)
        + M.P xstar (p.2 + M.arrival p.1 y)
        + M.α * ∫ t, gd xstar n (M.shift p.1 y, p.2 + M.arrival p.1 y - t) ∂M.ν

/-- The finite-horizon system program (1), p. 822: `ĝ_0 = 0` and
`ĝ_{n+1}(ŷ, v^d, x^r) = min_{y, z} {c^d(y) + D(v^d + y^L) + c^r z + R(x^r + z)
  + α E ĝ_n[(y, y^1, …, y^{L−1}), v^d + y^L − u, x^r + z − u] : y ≥ 0, z ≥ 0,
  x^r + z ≤ v^d + y^L}`. -/
noncomputable def ghat : ℕ → M.State → ℝ
  | 0 => fun _ => 0
  | n + 1 => fun s =>
      ⨅ a : {a : ℝ × ℝ // M.system.feasible s a},
        M.system.cost s a + M.α * ∫ t, ghat n (M.system.next s a t) ∂M.ν

end Model

end FZEchelon.Discounted


