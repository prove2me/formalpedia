-- Prove2me | Definitions.Def_TRSHolderKL_S0
-- name    : TRSHolderKL_S0
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T04:50:54.663599+00:00
-- url     : https://prove2.me/theorems/f8077c36-3895-4787-9f70-16f0e523ad10
-- title:
--   The optimal solution set $S_0$ of the TRS
-- statement:
--   $S_0$ is the set of optimal solutions of (P$_0$): the points $x$ with $\|x\|\le1$ such that $f(x)\le f(y)$ for every $y$ with $\|y\|\le 1$. It is nonempty, and $f=f^*$ on $S_0$.
-- source:
--   Jiang and Li, Hölderian error bounds and Kurdyka-Łojasiewicz inequality for the trust region subproblem, arXiv:1911.11955v2, p.1

import Mathlib
import Definitions.Def_RBMSensitivity_E
import Definitions.Def_TRSHolderKL_f
open RBMSensitivity (E)

namespace TRSHolderKL

/-- `S₀`, the optimal solution set of (P₀): the minimizers of `f` over the unit ball,
Jiang and Li, arXiv:1911.11955v2, p.1. -/
def S0 {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (b : E n) : Set (E n) :=
  {x | ‖x‖ ≤ 1 ∧ ∀ y : E n, ‖y‖ ≤ 1 → f A b x ≤ f A b y}

end TRSHolderKL


