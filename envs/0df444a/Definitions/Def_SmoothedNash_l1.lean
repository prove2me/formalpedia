-- Prove2me | Definitions.Def_SmoothedNash_l1
-- name    : SmoothedNash_l1
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T16:46:42.188269+00:00
-- url     : https://prove2.me/theorems/163cc6cc-b056-453c-a029-8b0cecdbcdd7
-- title:
--   Product $\ell_1$ metric $\|x - y\|_1$
-- statement:
--   For two profiles $x = (x_1, \dots, x_m)$ and $y = (y_1, \dots, y_m)$ of vectors in $\mathbb R^n$, the **product $\ell_1$ metric** is
--   $$
--   \|x - y\|_1 := \sum_{i=1}^m \|x_i - y_i\|_1 = \sum_{i=1}^m \sum_{a \in [n]} |x_i(a) - y_i(a)| .
--   $$
--   The balls $B_A(c, r) := \{x \in K_A : \|x - c\|_1 \le r\}$ of the paper are written with this metric and membership in $K_A$.
-- source:
--   Attias–Dagan–Daskalakis–Yao–Zampetakis, Nash Equilibria, Variational Inequalities, and Fixed Points: Beating Brute Force via Smoothed Analysis, STOC 2027 submission (manuscript sha256 3f9ea37d…77a1ea53), §2.1.1, pp.13–14

import Mathlib

namespace SmoothedNash

/-- The product `ℓ_1` metric `‖x − y‖_1 := Σ_{i=1}^m ‖x_i − y_i‖_1` (Attias–Dagan–Daskalakis–Yao–Zampetakis, *Nash Equilibria, Variational Inequalities, and Fixed Points: Beating Brute Force via Smoothed Analysis*, STOC 2027 submission manuscript (sha256 3f9ea37d…77a1ea53), §2.1.1, p.13). The ball
`B_A(c, r) := {x ∈ K_A : ‖x − c‖_1 ≤ r}` (p.14) is written with `InK` and `l1`. -/
noncomputable def l1 {m n : ℕ} (x y : Fin m → Fin n → ℝ) : ℝ :=
  ∑ i, ∑ a, |x i a - y i a|

end SmoothedNash


