-- Prove2me | Definitions.Def_FracRiccati_Radius_Supplement_RLIntegral
-- name    : FracRiccati_Radius_Supplement_RLIntegral
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-23T20:52:36.971555+00:00
-- url     : https://prove2.me/theorems/2552590d-14fb-4889-9448-b90180b23e03
-- title:
--   (2.5) — complex Riemann–Liouville integral based at zero
-- statement:
--   For positive order $\alpha$ and a complex-valued function $f$ whose weighted kernel is integrable, the Riemann–Liouville integral based at zero is
--   $$I^\alpha f(t)=\frac1{\Gamma(\alpha)}\int_{(0,t)}(t-s)^{\alpha-1}f(s)\,ds.$$
--   It supplies the operator in the complex Riccati integral equation. The published real-valued operator does not accept this paper's complex functions.
--
--   **Formalization Note** This is a Bochner integral on the open interval. On empty intervals or for nonintegrable kernels it takes Lean's default value zero; solution predicates explicitly rule out the latter situation. No order-zero convention is used by the results.
-- source:
--   Callegaro, Grasselli, Pagès, Fast Hybrid Schemes for Fractional Riccati Equations (Rough is not so Tough), arXiv:1805.12587v4, p. 5, (2.5); p. 6, (2.12)–(2.13)

import Mathlib

namespace FracRiccati.Radius.Supplement

/-- Complex-valued Riemann–Liouville integral (2.5), based at zero. -/
noncomputable def rlIntegral (α : ℝ) (f : ℝ → ℂ) (t : ℝ) : ℂ :=
  (Real.Gamma α : ℂ)⁻¹ * ∫ s in Set.Ioo 0 t, ((t - s) ^ (α - 1) : ℝ) * f s

end FracRiccati.Radius.Supplement


