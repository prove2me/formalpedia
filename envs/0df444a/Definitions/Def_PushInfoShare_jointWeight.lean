-- Prove2me | Definitions.Def_PushInfoShare_jointWeight
-- name    : PushInfoShare_jointWeight
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T19:46:16.306954+00:00
-- url     : https://prove2.me/theorems/1c45c7db-4801-4496-839d-1a066a03f4b9
-- title:
--   Joint weight $S_i=t_i/(\sigma^{-1}+t_1+t_2)$
-- statement:
--   The weight of signal $Y_i$ in the joint forecast of $\theta$ is
--   $$S_i=\frac{t_i}{\sigma^{-1}+t_1+t_2}.$$
--   When $s_1=s_2=s$ one has $S_1=S_2=s/(1+s)$.
-- source:
--   Jain, Sharing Demand Information with Retailer under Upstream Competition, SSRN:3388957 (PDF of 2021-04-25), §3, p.8

import Mathlib
import Definitions.Def_PushInfoShare_precision

open MeasureTheory

namespace PushInfoShare

/-- The weight `Sᵢ = tᵢ / (σ⁻¹ + t₁ + t₂)` of signal `Yᵢ` in the joint forecast of `θ`, Jain,
SSRN:3388957 (PDF of 2021-04-25), §3, p.8. -/
noncomputable def jointWeight {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (θ : Ω → ℝ)
    (Y : Fin 2 → Ω → ℝ) (σ : ℝ) (i : Fin 2) : ℝ :=
  precision μ θ Y i / (σ⁻¹ + precision μ θ Y 0 + precision μ θ Y 1)

end PushInfoShare


