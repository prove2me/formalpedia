-- Prove2me | Definitions.Def_KallMayerSLP_KKT_primalFunction
-- name    : KallMayerSLP_KKT_primalFunction
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T22:09:29.502396+00:00
-- url     : https://prove2.me/theorems/ad848be0-7d77-4aea-975b-01aaff782615
-- title:
--   Primal function $x\mapsto\sup_{u\ge0}L(x,u)$
-- statement:
--   For $x\in\mathbb R^n$ let
--   $$
--   \phi(x):=\sup_{u\ge 0}L(x,u)\in(-\infty,+\infty],
--   $$
--   the inner supremum on the right-hand side of (3.7), $\min_{x\in\mathbb R^n}\sup_{u\ge0}L(x,u)$, whose outer minimization is the primal problem.
--
--   **Formalization Note** The supremum may be $+\infty$, so it is taken in `EReal`, over the vectors $u\in\mathbb R^m$ with $u\ge0$ componentwise.
-- source:
--   Kall & Mayer, Stochastic Linear Programming: Models, Theory, and Computation (Kluwer/Springer 2005), Chapter 1, §3.1, eq. (3.7), p.66 (PDF 77)

import Mathlib
import Definitions.Def_KallMayerSLP_KKT_lagrangian

namespace KallMayerSLP.KKT

/-- **The primal function `x ↦ sup_{u ≥ 0} L(x, u)` of (3.7).**
Kall & Mayer, *Stochastic Linear Programming* (2005), Chapter 1, §3.1, eq. (3.7), p.66 (PDF 77):
the inner supremum of the right-hand side `min_{x∈ℝⁿ} sup_{u≥0} L(x, u)`.

**Formalization Note.** The supremum may be `+∞`, so it is taken in `EReal`, over the nonempty
set `{u : Fin m → ℝ | 0 ≤ u}` (componentwise order). -/
noncomputable def primalFunction {n m : ℕ} (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (g : Fin m → EuclideanSpace ℝ (Fin n) → ℝ) (x : EuclideanSpace ℝ (Fin n)) : EReal :=
  ⨆ (u : Fin m → ℝ) (_ : 0 ≤ u), ((lagrangian f g x u : ℝ) : EReal)

end KallMayerSLP.KKT


