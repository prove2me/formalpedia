-- Prove2me | Definitions.Def_SingleFactorPricing_LogBound_tightDemand
-- name    : SingleFactorPricing_LogBound_tightDemand
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T09:14:59.03056+00:00
-- url     : https://prove2.me/theorems/e1db4c77-6db8-4b94-aa66-ee8f5c9d5f32
-- title:
--   The demand of the tight instance
-- statement:
--   In the tight instance there is one product. With $\beta=1+\ln\rho$ and $k=1/\beta$, a type with willingness to pay $v\in[1,\rho]$ demands
--
--   $$
--   d_v(p)=k\,\mathbf 1\{p\le v\}.
--   $$
--
--   Aggregated under `tailLaw`, this gives the paper's $d(p)=k\min(1,1/p)$ on $[0,\rho]$.
--
--   **Formalization Note** The price vector has one component, `p : Fin 1 → ℝ`.
-- source:
--   Gallego, Berbeglia, Bounds and Heuristics for Multi-Product Personalized Pricing, arXiv:2102.03038v2, proof of Theorem 1, p.4

import Mathlib

open MeasureTheory

namespace SingleFactorPricing.LogBound

/-- **The demand of the tight instance.** Gallego, Berbeglia, arXiv:2102.03038v2, proof of
Theorem 1, p.4: one product, types with willingness to pay `v ∈ [1, ρ]`, `k = 1/β`,
`β = 1 + ln(ρ)`.

**Formalization Note.** Type `v` demands `k` units of the single product when its price is at most
`v`, and nothing otherwise. Aggregated under `tailLaw ρ`, this is the paper's `d(p) = k min(1, 1/p)`
on `[0, ρ]`. -/
noncomputable def tightDemand (ρ : ℝ) (v : Set.Icc (1 : ℝ) ρ) (p : Fin 1 → ℝ) (i : Fin 1) : ℝ :=
  1 / (1 + Real.log ρ) * if p i ≤ v then 1 else 0

end SingleFactorPricing.LogBound


