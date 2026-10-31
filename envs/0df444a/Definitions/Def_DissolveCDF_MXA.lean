-- Prove2me | Definitions.Def_DissolveCDF_MXA
-- name    : DissolveCDF_MXA
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T21:33:05.350688+00:00
-- url     : https://prove2.me/theorems/ba7cac83-a169-4918-8b5f-a0109e0035b4
-- title:
--   §2.3 — $M_{x,A}=\sup_{y\in\Theta_x}\|J_{\mathcal A}(y)\|$
-- statement:
--   For $x\in\mathcal M$,
--
--   $$
--   M_{x,A}:=\sup_{y\in\Theta_x}\|J_{\mathcal A}(y)\|,
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

/-- Xiao, Liu & Toh, *Dissolving Constraints for Riemannian Optimization*, arXiv:2203.10319v3, §2.3 (p.7): `M_{x,A} := sup_{y∈Θ_x} ‖J_A(y)‖` (operator norm).

**Formalization Note** `Θ_x = {y : ‖y − x‖ ≤ ρ_x}` is `Metric.closedBall x (rhoX c x)`. The
supremum is Lean's `sSup`, which is the true supremum because the set is nonempty and bounded
under Assumptions 1.1 and 1.2 (a continuous function on a compact ball); this boundedness is a
consequence of the assumptions, not an extra hypothesis. -/
noncomputable def MXA {n p : ℕ} (c : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin p))
    (A : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) (x : EuclideanSpace ℝ (Fin n)) : ℝ :=
  sSup ((fun y => ‖transJac A y‖) '' Metric.closedBall x (rhoX c x))

end DissolveCDF


