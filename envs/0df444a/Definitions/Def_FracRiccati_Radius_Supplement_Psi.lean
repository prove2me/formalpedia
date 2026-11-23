-- Prove2me | Definitions.Def_FracRiccati_Radius_Supplement_Psi
-- name    : FracRiccati_Radius_Supplement_Psi
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-23T20:52:15.204225+00:00
-- url     : https://prove2.me/theorems/9a93f407-15d7-464a-b830-484fd9d614dc
-- title:
--   (3.17) — fractional power-series function
-- statement:
--   Let $\alpha$ be the fractional order and $\lambda,\mu,\nu\in\mathbb C$. Using exactly the published coefficients $a_k$ of (3.19), set
--   $$\psi_{\lambda,\mu,\nu}(t)=\sum_{k\ge0}a_k t^{\alpha k}.$$
--   For real parameters, $\psi^{\mathbb R}_{\lambda,\mu,\nu}$ is its real part. In the theorem's domain the coefficients are real, so this is the real-valued series itself. This definition adds the function that the radius mission did not need.
--
--   **Formalization Note** The total sum uses Mathlib's `tsum`; it is meaningful as a series sum only where the series converges. All function assertions below are restricted to the interior of the radius. No new coefficient recursion or radius is defined.
-- source:
--   Callegaro, Grasselli, Pagès, Fast Hybrid Schemes for Fractional Riccati Equations (Rough is not so Tough), arXiv:1805.12587v4, p. 8, (3.17)–(3.21)

import Mathlib
import Definitions.Def_FracRiccati_Radius_Coeff

namespace FracRiccati.Radius.Supplement

/-- Equation (3.17), with the already published coefficients. -/
noncomputable def psi (α : ℝ) (lam mu nu : ℂ) (t : ℝ) : ℂ :=
  ∑' k : ℕ, coeff α lam mu nu k * (t ^ (α * (k : ℝ)) : ℝ)

/-- The real-valued series used in the real-parameter clauses. -/
noncomputable def psiReal (α l m n t : ℝ) : ℝ := (psi α l m n t).re

end FracRiccati.Radius.Supplement


