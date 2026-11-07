-- Prove2me | Definitions.Def_GrothendieckLB_pairCorr
-- name    : GrothendieckLB_pairCorr
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T06:46:46.196697+00:00
-- url     : https://prove2.me/theorems/bb0f3686-3f42-44b4-8be8-fcec7164ff97
-- title:
--   Correlation function $H_{f,g}(t)$ of a pair
-- statement:
--   For $f,g:\mathbb R^d\to\mathbb R$ and $-1<t<1$, the arcsine-normalized correlation function is
--   $$
--   H_{f,g}(t)=\frac\pi2\,\mathbb E[f(X)g(X_t')],
--   $$
--   with $(X,X_t')$ standard Gaussian vectors in $\mathbb R^d$ with $\mathbb E[X_iX'_{t,j}]=\delta_{ij}t$. The expectation is the double integral against the published joint density `GrothendieckConstant.gaussianPairDensity`.
--
--   **Formalization Note** The formula is that of the published `GrothendieckConstant.correlationFunction`, on a bare pair, because the published function takes a `KrivineScheme`, which bundles oddness. The value is meaningful for $|t|<1$, and only the germ at the origin is used.
-- source:
--   Saha et al., New Lower and Upper Bounds for the Grothendieck Constant, arXiv:2608.11158 (held version, sha256 e7eb5d65…), Definition 3.1, p.16; Section 7, p.31

import Mathlib
import Definitions.Def_KrivineSchemeDefs
open MeasureTheory

namespace GrothendieckLB

/-- The arcsine-normalized correlation function `H_{f,g}(t) = (π/2) E[f(X) g(X′_t)]` of a pair of
functions on `ℝ^d`, with `(X, X′_t)` standard Gaussian vectors with coordinatewise correlation `t`
(Saha et al., *New Lower and Upper Bounds for the Grothendieck Constant*, arXiv:2608.11158 (held version, sha256 e7eb5d65…), Definition 3.1, p.16; Section 7, p.31).

**Formalization Note** Same formula as the published `GrothendieckConstant.correlationFunction`,
through the published density `GrothendieckConstant.gaussianPairDensity`, but on a bare pair: the
published function takes a `KrivineScheme`, which bundles oddness, and Definition 10.1 has none.
The value is meaningful for `|t| < 1`; only the germ at `0` is used. -/
noncomputable def pairCorr {d : ℕ} (f g : (Fin d → ℝ) → ℝ) (t : ℝ) : ℝ :=
  (Real.pi / 2) * ∫ x : Fin d → ℝ, ∫ y : Fin d → ℝ,
    f x * g y * GrothendieckConstant.gaussianPairDensity d t x y

end GrothendieckLB


