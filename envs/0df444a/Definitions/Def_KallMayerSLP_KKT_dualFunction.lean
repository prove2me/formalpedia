-- Prove2me | Definitions.Def_KallMayerSLP_KKT_dualFunction
-- name    : KallMayerSLP_KKT_dualFunction
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T22:09:34.477767+00:00
-- url     : https://prove2.me/theorems/2dd75e7f-6a29-4d14-95b7-054f78aa9d30
-- title:
--   Dual function $u\mapsto\inf_x L(x,u)$
-- statement:
--   For $u\in\mathbb R^m$ let
--   $$
--   \theta(u):=\inf_{x\in\mathbb R^n}L(x,u)\in[-\infty,\infty),
--   $$
--   the inner infimum on the left-hand side of (3.7), $\max_{u\ge0}\inf_{x\in\mathbb R^n}L(x,u)$, whose outer maximization is the dual problem.
--
--   **Formalization Note** The infimum may be $-\infty$, so it is taken in `EReal`.
-- source:
--   Kall & Mayer, Stochastic Linear Programming: Models, Theory, and Computation (Kluwer/Springer 2005), Chapter 1, §3.1, eq. (3.7), p.66 (PDF 77)

import Mathlib
import Definitions.Def_KallMayerSLP_KKT_lagrangian

namespace KallMayerSLP.KKT

/-- **The dual function `u ↦ inf_{x ∈ ℝⁿ} L(x, u)` of (3.7).**
Kall & Mayer, *Stochastic Linear Programming* (2005), Chapter 1, §3.1, eq. (3.7), p.66 (PDF 77):
the inner infimum of the left-hand side `max_{u≥0} inf_{x∈ℝⁿ} L(x, u)`.

**Formalization Note.** The infimum may be `−∞`, so it is taken in `EReal`
(`⨅` over the nonempty set `ℝⁿ` of the real values coerced to `EReal`). -/
noncomputable def dualFunction {n m : ℕ} (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (g : Fin m → EuclideanSpace ℝ (Fin n) → ℝ) (u : Fin m → ℝ) : EReal :=
  ⨅ x : EuclideanSpace ℝ (Fin n), ((lagrangian f g x u : ℝ) : EReal)

end KallMayerSLP.KKT


