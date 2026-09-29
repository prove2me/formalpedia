-- Prove2me | Definitions.Def_CalibratedCE_Convergence_EmpDist
-- name    : CalibratedCE_Convergence_EmpDist
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-27T13:27:37.843654+00:00
-- url     : https://prove2.me/theorems/a7271ef9-f715-425a-9d20-288f3d8497ad
-- title:
--   Empirical joint distribution $D_t(x, y)$ (Section 3, p. 44)
-- statement:
--   Let $x(s) \in S(1)$ and $y(s) \in S(2)$ be the plays of the two players in round $s$. The **empirical joint distribution** after $t$ rounds is
--   $$D_t(a, b) = \frac{|\{ s < t : x(s) = a,\ y(s) = b \}|}{t},$$
--   in the paper's words (p. 44), "$D_t(x, y)$, the fraction of times up to time $t$ that player 1 plays $x$ and player 2 plays $y$. This is the empirical joint distribution."
--
--   Theorem 1 is a statement about the limit behaviour of $D_t$.
--
--   **Formalization Note** Rounds are indexed $0, \dots, t-1$. At $t = 0$ the value is $0$ (Lean's $x / 0 = 0$), which is not a distribution; every statement takes $t \ge 1$ or a limit $t \to \infty$.
-- source:
--   Foster and Vohra, Calibrated learning and correlated equilibrium, Games Econ. Behav. 21 (1997), p. 44, Section 3 (empirical joint distribution)

import Mathlib

namespace CalibratedCE.Convergence

/-- `D_t(x, y)`: the fraction of the first `t` rounds (rounds `0, …, t-1`) in which player 1
played `a` and player 2 played `b`. At `t = 0` it is `0` (division by zero). -/
noncomputable def empDist {m n : ℕ} (x : ℕ → Fin m) (y : ℕ → Fin n) (t : ℕ) (a : Fin m)
    (b : Fin n) : ℝ :=
  (((Finset.range t).filter (fun s => x s = a ∧ y s = b)).card : ℝ) / (t : ℝ)

end CalibratedCE.Convergence


