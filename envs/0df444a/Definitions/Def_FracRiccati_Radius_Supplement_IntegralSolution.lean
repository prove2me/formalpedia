-- Prove2me | Definitions.Def_FracRiccati_Radius_Supplement_IntegralSolution
-- name    : FracRiccati_Radius_Supplement_IntegralSolution
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-23T20:53:14.543806+00:00
-- url     : https://prove2.me/theorems/80932acc-f485-4523-a213-617bc4830dec
-- title:
--   (2.12)–(2.13) — integrable complex Riccati integral solution
-- statement:
--   Let $\lambda,\mu,\nu,u,v\in\mathbb C$ and $R>0$. A function $f:\mathbb R\to\mathbb C$ solves the integral equation on $(0,R)$ when the weighted Riccati kernel is integrable on $(0,t)$ for every $t\in(0,R)$ and
--   $$f(t)=\frac{u}{\Gamma(\alpha)}t^{\alpha-1}+\frac{v}{\Gamma(\alpha-1)}t^{\alpha-2}+I^\alpha(\lambda f^2+\mu f+\nu)(t).$$
--   Case (a) uses $v=0$ and hence (2.12). Case (b) uses (2.13). Integrability is part of the solution concept, rather than a premise about an unknown future solution. This representation follows the integral form explicitly chosen by Section 6 and does not claim a formalized Riemann–Liouville derivative equivalence.
-- source:
--   Callegaro, Grasselli, Pagès, Fast Hybrid Schemes for Fractional Riccati Equations (Rough is not so Tough), arXiv:1805.12587v4, p. 6, (2.12)–(2.13); p. 24, §6

import Mathlib
import Definitions.Def_FracRiccati_Radius_Supplement_RLIntegral

namespace FracRiccati.Radius.Supplement

/-- The integral equation (2.12), or (2.13) with its second datum `v`.
The kernel must be integrable; the Bochner default value is not a solution criterion. -/
def IsIntegralSolution (α : ℝ) (lam mu nu u v : ℂ) (R : ℝ) (f : ℝ → ℂ) : Prop :=
  ∀ t ∈ Set.Ioo 0 R,
    MeasureTheory.IntegrableOn
      (fun s => ((t - s) ^ (α - 1) : ℝ) * (lam * f s ^ 2 + mu * f s + nu))
      (Set.Ioo 0 t) ∧
    f t = u / (Real.Gamma α : ℂ) * (t ^ (α - 1) : ℝ) +
      v / (Real.Gamma (α - 1) : ℂ) * (t ^ (α - 2) : ℝ) +
      rlIntegral α (fun s => lam * f s ^ 2 + mu * f s + nu) t

end FracRiccati.Radius.Supplement


