-- Prove2me | Definitions.Def_AdaDiscRL_IsAdmissibleMetric
-- name    : AdaDiscRL_IsAdmissibleMetric
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T04:25:57.541989+00:00
-- url     : https://prove2.me/theorems/ce17ff99-32a1-47e7-8c59-fd7d95fd46e3
-- title:
--   Metric $\mathcal D$ on $\mathcal S\times\mathcal A$ with $\mathcal D\le\mathcal D_{\mathcal S}+\mathcal D_{\mathcal A}$
-- statement:
--   The state and action spaces carry metrics $\mathcal D_{\mathcal S}$ and $\mathcal D_{\mathcal A}$. The algorithms work with a metric $\mathcal D$ on $\mathcal S\times\mathcal A$ given "via the product metric, or any sub-additive metric" with
--   $$
--   \mathcal D((x,a),(x',a'))\le\mathcal D_{\mathcal S}(x,x')+\mathcal D_{\mathcal A}(a,a').
--   $$
--   `IsAdmissibleMetric D` states that $\mathcal D$ is a metric (zero exactly on the diagonal, symmetric, triangle inequality) satisfying this bound.
--
--   **Formalization Note** $\mathcal D_{\mathcal S}$ and $\mathcal D_{\mathcal A}$ are the `dist` of the metric-space instances on `S` and `A`.
-- source:
--   Sinclair, Banerjee & Yu, Adaptive Discretization in Online Reinforcement Learning, arXiv:2110.15843v3, §2.3, p.10

import Mathlib

namespace AdaDiscRL

/-- **The metric `D` on `S × A`** (arXiv:2110.15843v3, §2.3, p.10): "These metrics imposes a metric
structure `D` on `S × A` via the product metric, or any sub-additive metric such that
`D((x, a), (x′, a′)) ≤ D_S(x, x′) + D_A(a, a′)`."

`D` is a metric on `S × A` (zero exactly on the diagonal, symmetric, triangle inequality) bounded
by the sum of the metrics `D_S = dist` on `S` and `D_A = dist` on `A`. The max (product) metric of
Mathlib's `Prod` instance is one example. -/
def IsAdmissibleMetric {S A : Type*} [MetricSpace S] [MetricSpace A]
    (D : S × A → S × A → ℝ) : Prop :=
  (∀ p q, D p q = 0 ↔ p = q) ∧ (∀ p q, D p q = D q p) ∧
  (∀ p q w, D p w ≤ D p q + D q w) ∧
  (∀ p q, D p q ≤ dist p.1 q.1 + dist p.2 q.2)

end AdaDiscRL


