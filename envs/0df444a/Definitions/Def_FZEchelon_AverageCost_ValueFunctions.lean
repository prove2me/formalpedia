-- Prove2me | Definitions.Def_FZEchelon_AverageCost_ValueFunctions
-- name    : FZEchelon_AverageCost_ValueFunctions
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-05T11:23:23.658488+00:00
-- url     : https://prove2.me/theorems/d0adfe6d-6e01-42e4-9f05-fed3b565d159
-- title:
--   The finite-horizon programs (1), (2), (3), (5), the induced penalties P̂_n and the function (6)
-- statement:
--   This file defines the finite-horizon dynamic programs of Federgruen and Zipkin (1984), §1, with $n$ the number of periods remaining and every value function equal to $0$ at $n = 0$. Below, $y^L$ is the order arriving now and $E$ is over the one-period demand $u$.
--
--   1. The **system program** (1): $\hat g_n(\tilde y, v^d, x^r)$ is the minimum over $y \ge 0$, $z \ge 0$, $x^r + z \le v^d + y^L$ of
--   $$c^d(y) + D(v^d + y^L) + c^r z + R(x^r + z) + \alpha E\hat g_{n-1}[(y, y^1, \dots, y^{L-1}), v^d + y^L - u, x^r + z - u].$$
--   2. The **outlet program** (2): $g^r_n(x^r) = \min_{z \ge 0}\{c^r z + R(x^r + z) + \alpha E g^r_{n-1}(x^r + z - u)\}$. A **critical number** $x^{r*}_n$ for period $n \ge 1$ is a global minimizer of $G_n(w) = c^r w + R(w) + \alpha E g^r_{n-1}(w - u)$.
--   3. The **induced penalties**: for critical numbers $x^{r*}_n$, $\hat P_n(x) = 0$ for $x \ge x^{r*}_n$ and
--   $$\hat P_n(x) = c^r(x - x^{r*}_n) + [R(x) - R(x^{r*}_n)] + \alpha E[g^r_{n-1}(x - u) - g^r_{n-1}(x^{r*}_n - u)],\quad x < x^{r*}_n.$$
--   4. The **depot program** (3): $\hat g^d_n(\tilde y, v^d) = \min_{y \ge 0}\{c^d(y) + D(v^d + y^L) + \hat P_n(v^d + y^L) + \alpha E\hat g^d_{n-1}[(y, y^1, \dots, y^{L-1}), v^d + y^L - u]\}$.
--   5. The **program (5)**: $g^d_n$ is defined like $\hat g^d_n$ with the stationary penalty $P$ (critical number $x^{r*}$) in place of $\hat P_n$.
--   6. The **function (6)**: $g_n(\tilde y, v^d, x^r) = g^d_n(\tilde y, v^d) + g^r_n(x^r)$.
--
--   These are the objects whose relations (eq. (4), the §3 claims) the mission states.
--
--   **Formalization Note.** Each "min" is a real infimum over the constraint set, and each $E$ a Bochner integral against the demand law $\nu$; the statements that use them carry the hypotheses under which these are genuine (nonempty constraint sets on the physical states, objectives bounded below, integrands integrable). $\hat P_n$ and $\hat g^d_n$ take the sequence of critical numbers as a parameter. Only $n \ge 1$ matters for $G_n$ and $\hat P_n$.
-- source:
--   Federgruen and Zipkin, Computational Issues in an Infinite-Horizon, Multiechelon Inventory Model, Oper. Res. 32(4), 1984, pp. 822-825: program (1) (p. 822), program (2), the critical numbers x_n^{r*} and the penalties P̂_n, program (3) (p. 823), program (5) and the function (6) (p. 825)

import Mathlib
import Definitions.Def_FZEchelon_AverageCost_Model

namespace FZEchelon.AverageCost

open MeasureTheory

namespace Model

variable (m : Model)

/-- The outlet program (2) (p. 823), with `n` periods remaining:
`g^r_0 = 0`, `g^r_n(x) = min_{z ≥ 0} {c^r z + R(x + z) + α E g^r_{n−1}(x + z − u)}`, `n ≥ 1`.
The minimum is a real infimum over `z ≥ 0`. -/
noncomputable def gr : ℕ → ℝ → ℝ
  | 0 => fun _ => 0
  | n + 1 => fun x =>
      ⨅ z : {z : ℝ // 0 ≤ z}, m.cr * z.1 + m.R (x + z.1) + m.α * ∫ t, gr n (x + z.1 - t) ∂m.ν

/-- The function minimized by the critical number of period `n ≥ 1` (p. 823): with
`w = x^r + z`, `G_n(w) = c^r w + R(w) + α E g^r_{n−1}(w − u)`. A critical number `x_n^{r*}` for
period `n` is a global minimizer of `G_n`. -/
noncomputable def Gcrit (n : ℕ) (w : ℝ) : ℝ :=
  m.cr * w + m.R w + m.α * ∫ t, m.gr (n - 1) (w - t) ∂m.ν

/-- The induced penalty cost functions (p. 823), for a sequence `xn` of critical numbers
(`xn n` = `x_n^{r*}`): `P̂_n(x) = 0` for `x ≥ x_n^{r*}`, and for `x < x_n^{r*}`
`P̂_n(x) = c^r (x − x_n^{r*}) + [R(x) − R(x_n^{r*})] + α E[g^r_{n−1}(x − u) − g^r_{n−1}(x_n^{r*} − u)]`. -/
noncomputable def Phat (xn : ℕ → ℝ) (n : ℕ) (x : ℝ) : ℝ :=
  if xn n ≤ x then 0
  else m.cr * (x - xn n) + (m.R x - m.R (xn n))
    + m.α * ∫ t, (m.gr (n - 1) (x - t) - m.gr (n - 1) (xn n - t)) ∂m.ν

/-- The depot program (3) (p. 823): `ĝ^d_0 = 0`,
`ĝ^d_n(ŷ, v^d) = min_{y ≥ 0} {c^d(y) + D(v^d + y^L) + P̂_n(v^d + y^L) + α E ĝ^d_{n−1}[(y, y^1, …, y^{L−1}), v^d + y^L − u]}`.
The minimum is a real infimum over `y ≥ 0`. -/
noncomputable def ghatd (xn : ℕ → ℝ) : ℕ → DepotState m.L → ℝ
  | 0 => fun _ => 0
  | n + 1 => fun p =>
      ⨅ y : {y : ℝ // 0 ≤ y},
        m.orderCost y.1 + m.D (p.2 + arrival p.1 y.1) + m.Phat xn (n + 1) (p.2 + arrival p.1 y.1)
          + m.α * ∫ t, ghatd xn n (m.depotNext p y.1 t) ∂m.ν

/-- The program (5) (p. 825), with the stationary penalty `P` (critical number `xstar`) in place of
`P̂_n`: `g^d_0 = 0`,
`g^d_n(ŷ, v^d) = min_{y ≥ 0} {c^d(y) + D(v^d + y^L) + P(v^d + y^L) + α E g^d_{n−1}[(y, y^1, …, y^{L−1}), v^d + y^L − u]}`. -/
noncomputable def gd (xstar : ℝ) : ℕ → DepotState m.L → ℝ
  | 0 => fun _ => 0
  | n + 1 => fun p =>
      ⨅ y : {y : ℝ // 0 ≤ y},
        m.orderCost y.1 + m.D (p.2 + arrival p.1 y.1) + m.P xstar (p.2 + arrival p.1 y.1)
          + m.α * ∫ t, gd xstar n (m.depotNext p y.1 t) ∂m.ν

/-- The system program (1) (p. 822): `ĝ_0 = 0`,
`ĝ_n(ŷ, v^d, x^r) = min_{y,z} {c^d(y) + D(v^d + y^L) + c^r z + R(x^r + z) + α E ĝ_{n−1}[(y, y^1, …, y^{L−1}), v^d + y^L − u, x^r + z − u] : y ≥ 0, z ≥ 0, x^r + z ≤ v^d + y^L}`.
The minimum is a real infimum over the feasible actions. -/
noncomputable def ghat : ℕ → SysState m.L → ℝ
  | 0 => fun _ => 0
  | n + 1 => fun s =>
      ⨅ a : {a : ℝ × ℝ // m.SysFeasible s a},
        m.sysCost s a.1 + m.α * ∫ t, ghat n (m.sysNext s a.1 t) ∂m.ν

/-- The function (6) (p. 825): `g_n(ŷ, v^d, x^r) = g^d_n(ŷ, v^d) + g^r_n(x^r)`. -/
noncomputable def gsys (xstar : ℝ) (n : ℕ) (s : SysState m.L) : ℝ :=
  m.gd xstar n (s.1, s.2.1) + m.gr n s.2.2

end Model

end FZEchelon.AverageCost


