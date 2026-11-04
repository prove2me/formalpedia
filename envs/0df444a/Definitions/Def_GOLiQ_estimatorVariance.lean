-- Prove2me | Definitions.Def_GOLiQ_estimatorVariance
-- name    : GOLiQ_estimatorVariance
-- status  : Definition
-- author  : @iris
-- created : 2026-11-03T05:51:11.175551+00:00
-- url     : https://prove2.me/theorems/3f4e730e-7fab-4da1-b7bc-ae2032e50196
-- title:
--   Second moment $\mathcal V_k=\mathbb E[\|H_k\|^2]$ of a gradient estimator
-- statement:
--   The **variability** of the estimator in iteration $k$ is
--   $$\mathcal V_k=\mathbb E[\|H_k\|^2].\tag{4}$$
--
--   **Formalization Note** The expectation is a lower Lebesgue integral in $[0,\infty]$, so a finite bound on $\mathcal V_k$ asserts that $H_k$ is square integrable.
-- source:
--   Chen, Liu, Hong, An Online Learning Approach to Dynamic Pricing and Capacity Sizing in Service Systems, arXiv:2009.02911v3, (4), p.13

import Mathlib
import Definitions.Def_GOLiQ_Model
import Definitions.Def_GOLiQ_Primitives

open MeasureTheory

namespace GOLiQ

/-- **The variance `𝒱ₖ = E[‖Hₖ‖²]` of a gradient estimator** ((4), p.13), as a lower Lebesgue
integral in `[0, ∞]`. -/
noncomputable def estimatorVariance {Ω : Type*} [MeasurableSpace Ω] (Pr : Primitives Ω)
    (H : ℕ → Ω → Point) (k : ℕ) : ENNReal :=
  ∫⁻ ω, ‖H k ω‖ₑ ^ 2 ∂Pr.P

end GOLiQ


