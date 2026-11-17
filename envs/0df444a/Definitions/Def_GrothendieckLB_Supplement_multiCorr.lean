-- Prove2me | Definitions.Def_GrothendieckLB_Supplement_multiCorr
-- name    : GrothendieckLB_Supplement_multiCorr
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T14:37:00.72186+00:00
-- url     : https://prove2.me/theorems/3f10d92b-d326-4847-ac14-a9a1789a7a05
-- title:
--   Correlation $\frac\pi2\mathbb E[f(X)g(Y)]$ under coordinate correlations $r_i$
-- statement:
--   For $f,g:\mathbb R^k\to\mathbb R$ and correlations $r=(r_1,\dots,r_k)$ with $|r_i|<1$, let $X,Y$ be standard Gaussian vectors in $\mathbb R^k$ with
--   $$
--   \mathbb E[X_iX_j]=\mathbb E[Y_iY_j]=\delta_{ij},\qquad \mathbb E[X_iY_j]=\delta_{ij}\,r_i ,
--   $$
--   and set
--   $$
--   \Phi_{f,g}(r)=\frac\pi2\,\mathbb E[f(X)\,g(Y)] .
--   $$
--   This is the common formula behind the correlation function of a limiting Krivine scheme ($r_i=\rho_i(t)$) and of the cubic–quintic scheme ($r=(\rho(t),t)$).
--
--   **Formalization Note** The joint law is the product over coordinates of bivariate standard Gaussian densities with correlation $r_i$, each the published `gaussianPairDensity` in dimension $1$. With $r_i=t$ for all $i$ it is the published `correlationFunction`.
-- source:
--   Saha et al., New Lower and Upper Bounds for the Grothendieck Constant, arXiv:2608.11158 (held version, sha256 e7eb5d65…), Definition 3.6, p.18; (13), p.24

import Mathlib
import Definitions.Def_KrivineSchemeDefs
open MeasureTheory

namespace GrothendieckLB

namespace Supplement

/-- The arcsine-normalized correlation of a pair `f, g : ℝ^k → ℝ` under coordinatewise
correlations `r = (r₁, …, r_k)`: `(π/2) E[f(X) g(Y)]`, where `X, Y` are standard Gaussian
vectors in `ℝ^k` with `E[X_i X_j] = E[Y_i Y_j] = δ_ij` and `E[X_i Y_j] = δ_ij r_i`
(Saha et al., *New Lower and Upper Bounds for the Grothendieck Constant*, arXiv:2608.11158 (held version, sha256 e7eb5d65…), Definition 3.6, p.18; (13), p.24).

**Formalization Note** The joint law of `(X, Y)` is the product over `i` of the bivariate
standard Gaussian densities with correlation `r_i`, each written with the published
`GrothendieckConstant.gaussianPairDensity` in dimension `1`. The density is meaningful for
`|r_i| < 1`, which holds in every use (`|ρ_i(t)| ≤ |t| < 1` for an allowable `ρ_i`). With
`r_i = t` for all `i` this is the published `GrothendieckConstant.correlationFunction`. -/
noncomputable def multiCorr {k : ℕ} (f g : (Fin k → ℝ) → ℝ) (r : Fin k → ℝ) : ℝ :=
  (Real.pi / 2) * ∫ x : Fin k → ℝ, ∫ y : Fin k → ℝ,
    f x * g y * ∏ i : Fin k,
      GrothendieckConstant.gaussianPairDensity 1 (r i) (fun _ => x i) (fun _ => y i)

end Supplement

end GrothendieckLB


