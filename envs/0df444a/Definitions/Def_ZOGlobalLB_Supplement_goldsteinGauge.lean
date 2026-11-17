-- Prove2me | Definitions.Def_ZOGlobalLB_Supplement_goldsteinGauge
-- name    : ZOGlobalLB_Supplement_goldsteinGauge
-- status  : Definition
-- author  : @iris
-- created : 2026-11-17T01:47:52.312205+00:00
-- url     : https://prove2.me/theorems/e152b58e-93b2-4096-b2b6-381edabe087b
-- title:
--   Goldstein stationarity gauge $g_\delta(x)$
-- statement:
--   For a locally Lipschitz function $f:\mathbb R^d\to\mathbb R$, let $\partial^G_\delta f(x)$ be the closed convex hull of all Clarke subgradients at points in the closed $\delta$-ball around $x$. The **Goldstein stationarity gauge** is
--
--   $$
--   g_\delta(x)=\inf\{\lVert v\rVert:v\in\partial^G_\delta f(x)\}.
--   $$
--
--   A point is Goldstein $(\delta,\varepsilon)$-stationary exactly when $g_\delta(x)\le\varepsilon$.
--
--   **Formalization Note** The published `GradSampling.Conv.epsSubdiff` supplies the closed Goldstein hull, and `Metric.infDist 0` supplies its least norm.
-- source:
--   Xia, Yuan, On Global Joint Lower Bounds in Zeroth-Order Nonconvex Optimization, arXiv:2610.19652, Eq. (6), p.4

import Mathlib
import Definitions.Def_GradSampling_Conv_Setting
import Definitions.Def_ZOGlobalLB_Admissible

namespace ZOGlobalLB

namespace Supplement

/-- The Goldstein stationarity gauge
`g_δ(x) = inf {‖v‖ : v ∈ ∂ᴳ_δ f(x)}` from Xia--Yuan,
*On Global Joint Lower Bounds in Zeroth-Order Nonconvex Optimization*,
arXiv:2610.19652, display (6), p.4.

**Formalization Note.** `GradSampling.Conv.epsSubdiff` is the published closed convex hull of
Clarke subgradients over the closed `δ`-ball. `Metric.infDist 0` is exactly the infimum of
the Euclidean norms of its elements. For the globally Lipschitz functions used in Theorem 2.2
this set is nonempty. -/
noncomputable def goldsteinGauge {d : ℕ} (f : E d → ℝ) (δ : ℝ) (x : E d) : ℝ :=
  Metric.infDist 0 (GradSampling.Conv.epsSubdiff f δ x)

end Supplement

end ZOGlobalLB


