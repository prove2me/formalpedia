-- Prove2me | Definitions.Def_ExactModKL_dist0
-- name    : ExactModKL_dist0
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T07:55:17.715687+00:00
-- url     : https://prove2.me/theorems/c3f5a292-de06-43a5-8ddf-5b26beb5ab82
-- title:
--   $\operatorname{dist}(0,\partial f(x))\in[0,\infty]$
-- statement:
--   For $f:\mathbb R^n\to(-\infty,\infty]$ and $x\in\mathbb R^n$,
--   $$
--   \operatorname{dist}\big(0,\partial f(x)\big)=\inf\{\|v\|:v\in\partial f(x)\}\in[0,\infty],
--   $$
--   the distance from the origin to the limiting subdifferential, with $\operatorname{dist}(0,\emptyset)=\infty$. Its reciprocal is the quantity whose supremum defines the exact modulus.
--
--   **Formalization Note** The extended distance (`Metric.infEDist`) is used, which is $\infty$ on the empty set; the real-valued distance would be $0$ there.
-- source:
--   Wang–Wang, arXiv:2008.13257v5, §1 notation, p.2; Definition 3.6, p.11

import Mathlib
import Definitions.Def_NonconvexSplitting_Shared_LimitingSubdiff

open scoped ENNReal

namespace ExactModKL

open NonconvexSplitting.Shared

/-- `dist(0, ∂f(x)) ∈ [0, ∞]`, the distance from the origin to the limiting subdifferential of
`f` at `x` (Wang–Wang, arXiv:2008.13257v5 (preprint), p.2: "dist(·, K) : Rⁿ → [0, ∞]", so
`dist(0, ∅) = inf ∅ = ∞`).

**Formalization Note.** `Metric.infEDist 0 (∂f x) : ℝ≥0∞`, which is `⊤` on the empty set
(`Metric.infDist` would be `0` there). -/
noncomputable def dist0 {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → EReal)
    (x : EuclideanSpace ℝ (Fin n)) : ℝ≥0∞ :=
  Metric.infEDist 0 (LimitingSubdiff f x)

end ExactModKL


