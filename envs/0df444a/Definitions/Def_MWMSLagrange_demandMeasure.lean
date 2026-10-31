-- Prove2me | Definitions.Def_MWMSLagrange_demandMeasure
-- name    : MWMSLagrange_demandMeasure
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T19:00:41.103036+00:00
-- url     : https://prove2.me/theorems/9cdeb3ae-b11e-4dbf-931b-2c45f4a52e27
-- title:
--   Joint law of independent demands $D_{i,t}$
-- statement:
--   Store $i$ faces demand $D_{i,t}$ in period $t$. Demands are independent across stores and periods and may have different distributions $\mu_{i,t}$. A demand sample path is $\omega\in\mathbb R^{[N]\times[T]}$ with $D_{i,t}(\omega)=\omega(i,t)$, and its law is the product measure
--
--   $$\mathbb P=\bigotimes_{(i,t)\in[N]\times[T]}\mu_{i,t}.$$
--
--   All expectations of the mission are taken under $\mathbb P$.
--
--   **Formalization Note** Independence is encoded by `Measure.pi`. The theorems assume each $\mu_{i,t}$ is a probability measure with $\mu_{i,t}([0,\bar D])=1$. Periods are `Fin T` (0-based).
-- source:
--   Miao, Jasin, Chao, Asymptotically Optimal Lagrangian Policies for Multi-Warehouse, Multi-Store Systems with Lost Sales, SSRN 3552995 (manuscript, sha256 1146a7f8…), §2, p.6 (independent, non-stationary demands bounded by D̄)

import Mathlib

open MeasureTheory

namespace MWMSLagrange

/-- Miao, Jasin, Chao, SSRN 3552995 (manuscript, sha256 1146a7f8…), §2, p.6: "demands are
independent and potentially non-stationary over time and across the stores (i.e., for
different i, t, D_{i,t} are independent and their distributions can be different)".

The sample space is `Ω = ℝ^{[N] × [T]}`, a sample path `ω` has demand `D_{i,t}(ω) = ω (i, t)`,
and the law of the whole demand path is the product `⊗_{i,t} μ_{i,t}` of the per-store,
per-period laws `μ_{i,t}`.

**Formalization Note.** Independence with possibly different marginals is encoded by the
product measure `Measure.pi`. The theorems assume each `μ_{i,t}` is a probability measure
concentrated on `[0, D̄]` (p.6: `D_{i,t} ≤ D̄`; nonnegativity of demand is implicit). Periods
are `Fin T`, so period `t ∈ [T]` of the paper is index `t - 1`. -/
noncomputable def demandMeasure {N T : ℕ} (μ : Fin N → Fin T → Measure ℝ) :
    Measure (Fin N × Fin T → ℝ) :=
  Measure.pi fun p : Fin N × Fin T => μ p.1 p.2

end MWMSLagrange


