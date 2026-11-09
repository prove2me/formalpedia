-- Prove2me | Definitions.Def_CEPolytopeHard_pm
-- name    : CEPolytopeHard_pm
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T17:15:25.728527+00:00
-- url     : https://prove2.me/theorems/146ec260-94eb-4352-af93-c32beabef58f
-- title:
--   Tent map $T$, interpolant $p_m$ and the polytope (13)
-- statement:
--   The **tent map** is $T(x) = \min\{2x, 2(1-x)\}$ on $[0,1]$ and, with $T^{(j)}$ its $j$-th iterate,
--   $$
--   p_m(x) = x - \sum_{j=1}^m 4^{-j} T^{(j)}(x).
--   $$
--   The **polytope (13)** in the variables $(x, t, w_1, \dots, w_m)$ is
--   $$
--   0 \le x, t, w_1, \dots, w_m \le 1,\quad w_0 = x,\quad w_j \le 2w_{j-1},\quad w_j \le 2(1 - w_{j-1})\ (j \in [m]),\quad t \ge x - \sum_{j=1}^m 4^{-j} w_j .
--   $$
--   Minimizing $t$ over it recovers $p_m(x)$ (Claim 4.3), which approximates $x^2$; this replaces the quadratic imitation cost by a linear one.
--
--   **Formalization Note** $w$ lists $w_0, w_1, \dots, w_m$, and $w_0 = x$ is one of the constraints.
-- source:
--   Anagnostides–Daskalakis–Farina–Golowich–Sandholm–Zhang, The Complexity of Correlated Equilibria Beyond Normal-Form Games, arXiv:2605.17665 (held version of November 2, 2026, sha256 6aec500a…7820), p.21 (T, p_m, polytope (13))

import Mathlib

set_option autoImplicit false

namespace CEPolytopeHard

/-- the tent map `T(x) = min{2x, 2(1 − x)}` (Anagnostides–Daskalakis–Farina–Golowich–Sandholm–Zhang, *The Complexity of Correlated Equilibria Beyond Normal-Form Games*, arXiv:2605.17665, held version of November 2, 2026, sha256 6aec500a…7820, p.21) -/
noncomputable def tent (x : ℝ) : ℝ := min (2 * x) (2 * (1 - x))

/-- The **piecewise-linear interpolant `p_m`** (Anagnostides–Daskalakis–Farina–Golowich–Sandholm–Zhang, *The Complexity of Correlated Equilibria Beyond Normal-Form Games*, arXiv:2605.17665, held version of November 2, 2026, sha256 6aec500a…7820, p.21: "p_m(x) = x − ∑_{j=1}^m 4^{−j}T^{(j)}(x),
where T^{(j)} denotes the jth composition of T with itself"). -/
noncomputable def pm (m : ℕ) (x : ℝ) : ℝ :=
  x - ∑ j ∈ Finset.Icc 1 m, (4 : ℝ) ^ (-(j : ℤ)) * tent^[j] x

/-- **Membership in the polytope (13)** (p.21: "0 ≤ x, t, w_1, . . . , w_m ≤ 1, w_0 = x,
w_j ≤ 2w_{j−1}, w_j ≤ 2(1 − w_{j−1}) for j ∈ [m], t ≥ x − ∑_{j=1}^m 4^{−j}w_j").

**Formalization Note** `w : Fin (m + 1) → ℝ` lists `w_0, w_1, …, w_m`, with the defining equation
`w_0 = x` as a constraint, so the coordinates are those of the page. -/
def InPoly13 (m : ℕ) (x t : ℝ) (w : Fin (m + 1) → ℝ) : Prop :=
  0 ≤ x ∧ x ≤ 1 ∧ 0 ≤ t ∧ t ≤ 1 ∧ w 0 = x ∧
  (∀ j : Fin m, 0 ≤ w j.succ ∧ w j.succ ≤ 1) ∧
  (∀ j : Fin m, w j.succ ≤ 2 * w j.castSucc ∧ w j.succ ≤ 2 * (1 - w j.castSucc)) ∧
  x - ∑ j : Fin m, (4 : ℝ) ^ (-((j.val : ℤ) + 1)) * w j.succ ≤ t

end CEPolytopeHard


