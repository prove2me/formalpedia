-- Prove2me | Definitions.Def_DissolveCDF_MXc
-- name    : DissolveCDF_MXc
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T21:32:56.056004+00:00
-- url     : https://prove2.me/theorems/30b1636b-95cd-4d2a-b9c7-565d8cb0a5df
-- title:
--   §2.3 — $M_{x,c}=\sup_{y\in\Theta_x}\|J_c(y)\|$
-- statement:
--   For $x\in\mathcal M$,
--
--   $$
--   M_{x,c}:=\sup_{y\in\Theta_x}\|J_c(y)\|,
--   $$
--
--   with $\|\cdot\|$ the $\ell_2$ operator norm.
--
--   Here $\Theta_x=\{y:\|y-x\|\le\rho_x\}$. Under Assumptions 1.1 and 1.2 the supremum is finite (a continuous function on a compact ball).
--
--   **Formalization Note** The supremum is Lean's `sSup`, which agrees with the true supremum because the set is nonempty and bounded; boundedness follows from the assumptions and is not added as a hypothesis.
-- source:
--   Xiao, Liu & Toh, Dissolving Constraints for Riemannian Optimization, arXiv:2203.10319v3, §2.3, p.7

import Mathlib
import Definitions.Def_DissolveCDF_transJac
import Definitions.Def_DissolveCDF_rhoX

namespace DissolveCDF

/-- Xiao, Liu & Toh, *Dissolving Constraints for Riemannian Optimization*, arXiv:2203.10319v3, §2.3 (p.7): `M_{x,c} := sup_{y∈Θ_x} ‖J_c(y)‖` (operator norm).

**Formalization Note** `Θ_x = {y : ‖y − x‖ ≤ ρ_x}` is `Metric.closedBall x (rhoX c x)`. The
supremum is Lean's `sSup`, which is the true supremum because the set is nonempty and bounded
under Assumptions 1.1 and 1.2 (a continuous function on a compact ball); this boundedness is a
consequence of the assumptions, not an extra hypothesis. -/
noncomputable def MXc {n p : ℕ} (c : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin p))
    (x : EuclideanSpace ℝ (Fin n)) : ℝ :=
  sSup ((fun y => ‖transJac c y‖) '' Metric.closedBall x (rhoX c x))

end DissolveCDF


