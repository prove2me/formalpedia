-- Prove2me | Definitions.Def_NondualOpt_lpBall
-- name    : NondualOpt_lpBall
-- status  : Definition
-- author  : @iris
-- created : 2026-11-05T23:57:49.862422+00:00
-- url     : https://prove2.me/theorems/402c687c-0aed-4ed4-bbf0-641c09c895cc
-- title:
--   The unit ball $B_r^d$
-- statement:
--   For $r\in[1,\infty]$ the **unit $\ell_r$ ball** is
--   $$
--   B_r^d=\{x\in\mathbb R^d:\|x\|_r\le 1\}.
--   $$
--   The feasible set of Corollary 7 is $B_p^d$, and the oracle's subgradients lie in $B_{q^*}^d$.
--
--   **Formalization Note** $\mathbb R^d$ is `Fin d → ℝ` and $\|x\|_r$ is the published $\ell_r$ norm `RegimeDRCVaR.normM r x` (Mathlib's `PiLp r` norm of the vector, with $r\in[1,\infty]$ an extended nonnegative real).
-- source:
--   Bullins–Guzmán–Martínez-Rubio–Molina, The First-Order Oracle Complexity of Lipschitz Convex Optimization in Nondual Settings, arXiv:2609.20687, §2, p.6

import Mathlib
import Definitions.Def_RegimeDRCVaR_normM

open scoped ENNReal

namespace NondualOpt

/-- The closed unit `ℓr` ball `B_r^d = {x ∈ ℝ^d : ‖x‖_r ≤ 1}`.
Bullins–Guzmán–Martínez-Rubio–Molina, arXiv:2609.20687, §2, p.6.

**Formalization Note.** `ℝ^d` is `Fin d → ℝ`, and `‖x‖_r` is the published `ℓr` norm
`RegimeDRCVaR.normM r x` (the `PiLp r` norm of the vector). -/
def lpBall (r : ℝ≥0∞) (d : ℕ) : Set (Fin d → ℝ) :=
  {x | RegimeDRCVaR.normM r x ≤ 1}

end NondualOpt


