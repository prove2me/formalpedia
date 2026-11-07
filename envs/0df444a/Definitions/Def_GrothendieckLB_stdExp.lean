-- Prove2me | Definitions.Def_GrothendieckLB_stdExp
-- name    : GrothendieckLB_stdExp
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T06:46:25.638988+00:00
-- url     : https://prove2.me/theorems/49f6a89a-a349-439d-8131-a967c4e4c380
-- title:
--   One-dimensional Gaussian expectation $\mathbb E[\varphi(Z)]$
-- statement:
--   For $\psi:\mathbb R\to\mathbb R$, this is $\mathbb E[\psi(Z)]=\int_{\mathbb R}\psi(z)\,\varphi(z)\,dz$ for a standard Gaussian $Z\sim N(0,1)$ with density $\varphi$. It is used for the one-dimensional objects of Section 8: the rearrangement problem, the moments $V(u)$ and the budget $\beta(u)$.
--
--   **Formalization Note** Every use takes $\psi$ measurable with polynomial growth, so the integrand is integrable.
-- source:
--   Saha et al., New Lower and Upper Bounds for the Grothendieck Constant, arXiv:2608.11158 (held version, sha256 e7eb5d65…), Section 8.3, p.34; Section 8.4, p.36

import Mathlib
open MeasureTheory ProbabilityTheory

namespace GrothendieckLB

/-- One-dimensional Gaussian expectation `E[φ(Z)]` for `Z ∼ N(0, 1)` (Saha et al., *New Lower and Upper Bounds for the Grothendieck Constant*, arXiv:2608.11158 (held version, sha256 e7eb5d65…), Section 8, pp.34, 36).

**Formalization Note** The integral against `gaussianPDFReal 0 1`. Every use takes `φ` measurable
and of polynomial growth, so the integrand is integrable. -/
noncomputable def stdExp (φ : ℝ → ℝ) : ℝ :=
  ∫ z, φ z * gaussianPDFReal 0 1 z

end GrothendieckLB


