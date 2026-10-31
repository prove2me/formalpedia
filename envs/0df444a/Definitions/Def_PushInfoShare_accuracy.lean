-- Prove2me | Definitions.Def_PushInfoShare_accuracy
-- name    : PushInfoShare_accuracy
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T19:46:27.384923+00:00
-- url     : https://prove2.me/theorems/ea3940d3-e754-48cc-bb48-7e56bc308eb3
-- title:
--   Accuracy $s_i=t_i/(\sigma^{-1}+t_i)$
-- statement:
--   The accuracy of manufacturer $i$'s information is
--   $$s_i=\frac{t_i}{\sigma^{-1}+t_i}.$$
--   It is the fraction of the demand variance removed by learning $Y_i$, and it is the parameter of Proposition 5.
-- source:
--   Jain, Sharing Demand Information with Retailer under Upstream Competition, SSRN:3388957 (PDF of 2021-04-25), §3, p.8

import Mathlib
import Definitions.Def_PushInfoShare_precision

open MeasureTheory

namespace PushInfoShare

/-- The accuracy `sᵢ = tᵢ / (σ⁻¹ + tᵢ)` of manufacturer `i`'s information, Jain, SSRN:3388957
(PDF of 2021-04-25), §3, p.8. -/
noncomputable def accuracy {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (θ : Ω → ℝ)
    (Y : Fin 2 → Ω → ℝ) (σ : ℝ) (i : Fin 2) : ℝ :=
  precision μ θ Y i / (σ⁻¹ + precision μ θ Y i)

end PushInfoShare


