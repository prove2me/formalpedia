-- Prove2me | Definitions.Def_BnBPEP_WeakCvx_moreauEnv
-- name    : BnBPEP_WeakCvx_moreauEnv
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-08T06:45:55.632816+00:00
-- url     : https://prove2.me/theorems/29e6501c-8897-4416-9fd6-0a593b22e14d
-- title:
--   Moreau envelope $f_{(1/\hat\rho)}$
-- statement:
--   Let $f:\mathbb R^d\to\mathbb R$ and $\hat\rho\in\mathbb R$. The **Moreau envelope** of $f$ with parameter $1/\hat\rho$ is the function
--   $$f_{(1/\hat\rho)}(x)\;=\;\inf_{y\in\mathbb R^d}\Big\{f(y)+\frac{\hat\rho}{2}\|y-x\|^2\Big\},\qquad x\in\mathbb R^d.$$
--
--   In §6.3.1 of Das Gupta, Van Parys and Ryu the envelope is used with a $1$-weakly convex $f$ and $\hat\rho>1$; then $y\mapsto f(y)+\frac{\hat\rho}{2}\|y-x\|^2$ is strongly convex, the infimum is finite and attained at the proximal point $\mathrm{prox}_{(1/\hat\rho)f}(x)$, and the infimum is the paper's minimum. The squared norm of its gradient, $\|\nabla f_{(1/2)}(x)\|^2$, is the paper's measure of approximate stationarity for nonsmooth nonconvex $f$.
--
--   **Formalization Note** The envelope is a real-valued infimum (`⨅`). When the set of values is unbounded below, which does not happen in the regime above, Lean's real infimum returns the default value $0$; that the infimum equals the attained minimum in the paper's regime is the first conclusion of the mission's milestone on the Moreau envelope (§6.3.1).
-- source:
--   Das Gupta, Van Parys, Ryu, Branch-and-bound performance estimation programming, Math. Program. 204 (2024), §6.3.1, p. 614 (definition of f_{(1/ρ̂)})

import Mathlib

namespace BnBPEP.WeakCvx

/-- The Moreau envelope `f_{(1/ρ̂)}(x) = min_y { f(y) + (ρ̂/2)‖y - x‖² }`
(Das Gupta–Van Parys–Ryu, Math. Program. 204 (2024), §6.3.1, p. 614), written as a real
infimum. For a `1`-weakly convex `f` and `ρ̂ > 1` the function `y ↦ f y + (ρ̂/2)‖y - x‖²` is
strongly convex, so the infimum is finite and attained at the proximal point (the paper's `min`).
Outside that regime (an unbounded-below set) Lean's real `⨅` returns the junk value `0`. -/
noncomputable def moreauEnv {d : ℕ} (ρhat : ℝ) (f : EuclideanSpace ℝ (Fin d) → ℝ)
    (x : EuclideanSpace ℝ (Fin d)) : ℝ :=
  ⨅ y : EuclideanSpace ℝ (Fin d), f y + ρhat / 2 * ‖y - x‖ ^ 2

end BnBPEP.WeakCvx


