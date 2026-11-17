-- Prove2me | Definitions.Def_GrothendieckLB_Supplement_cqA
-- name    : GrothendieckLB_Supplement_cqA
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T14:40:48.147979+00:00
-- url     : https://prove2.me/theorems/42f4ab6c-b793-49a8-a72d-5ae59fc2ae22
-- title:
--   Hermite coefficients $A_{a,b}$ of the cubic–quintic partition
-- statement:
--   For $a,b\ge0$ and independent standard Gaussians $W,X$,
--   $$
--   A_{a,b}=\mathbb E\bigl[f(W,X)\,\mathrm{He}_a(W)\,\mathrm{He}_b(X)\bigr],
--   $$
--   where $f$ is the cubic–quintic partition (12) and $\mathrm{He}_n$ are the orthonormal Hermite polynomials. These are the coefficients of $f$ in the orthonormal Hermite basis of $L^2$ of the standard Gaussian measure on $\mathbb R^2$.
--
--   **Formalization Note** The expectation is the iterated integral against the product of two standard Gaussian densities. $\mathrm{He}_n(x)=h_n(x)/\sqrt{n!}$, with $h_n$ the monic probabilists' Hermite polynomial, is the published `QuadSDE.hermiteN` (same normalization; for $n\le3$ it agrees with the base mission's `GrothendieckLB.he`).
-- source:
--   Saha et al., New Lower and Upper Bounds for the Grothendieck Constant, arXiv:2608.11158 (held version, sha256 e7eb5d65…), (14), p.25

import Mathlib
import Definitions.Def_QuadSDE_GaussHermite
import Definitions.Def_GrothendieckLB_Supplement_cqF
open MeasureTheory ProbabilityTheory

namespace GrothendieckLB

namespace Supplement

/-- The Hermite coefficients of the cubic–quintic partition `f` (Saha et al., *New Lower and Upper Bounds for the Grothendieck Constant*, arXiv:2608.11158 (held version, sha256 e7eb5d65…), (14), p.25):
`A_{a,b} = E[f(W, X) He_a(W) He_b(X)]` for `W, X` independent standard Gaussians and `He_n` the
orthonormal Hermite polynomials
`He_n(x) = He^{mon}_n(x)/√(n!)`.

**Formalization Note** The expectation is the iterated integral against the product of two
standard Gaussian densities `gaussianPDFReal 0 1`; `He_n` is the published
`QuadSDE.hermiteN n` (Mathlib's monic `Polynomial.hermite n` divided by `√(n!)`); the integrand is a bounded function times a
polynomial, hence integrable. The parameters are free reals; the paper's are (10). -/
noncomputable def cqA (η s₃ s₅ : ℝ) (a b : ℕ) : ℝ :=
  ∫ w, ∫ x, cqF η s₃ s₅ w x * QuadSDE.hermiteN a w * QuadSDE.hermiteN b x *
    (gaussianPDFReal 0 1 w * gaussianPDFReal 0 1 x)

end Supplement

end GrothendieckLB


