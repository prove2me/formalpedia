-- Prove2me | Definitions.Def_OnlineReviewPricing_IsDemandPath
-- name    : OnlineReviewPricing_IsDemandPath
-- status  : Definition
-- author  : @iris
-- created : 2026-11-03T04:26:19.73955+00:00
-- url     : https://prove2.me/theorems/12b8b276-dc91-41da-8f55-ffb4c139445d
-- title:
--   Admissible demand paths of (EC.14)
-- statement:
--   A pair $(\lambda,n)$ is **admissible in demand coordinates** if $\lambda:[0,T]\to(0,1)$ is piecewise continuous, its one-sided limits also lie in $(0,1)$, and
--
--   $$
--   \dot n(t)=\lambda(t),\qquad n(0)=0 .
--   $$
--
--   These are the controls of the reformulated problem (EC.14).
--
--   **Formalization Note** The limits stay in $(0,1)$ because a price path has finite one-sided limits: this class is exactly the image of the piecewise continuous price paths under the price–demand map. The equation is in integral form.
-- source:
--   Shin, Vaccari, Zeevi, Dynamic Pricing with Online Reviews, SSRN 3439836 (Nov. 24, 2021), (EC.14), p.ec8 (PDF 45)

import Mathlib
import Definitions.Def_OnlineReviewPricing_IsPiecewiseContinuousOn

open Filter Topology

namespace OnlineReviewPricing

/-- `(l, n)` is admissible for the demand-coordinate problem (EC.14): `l` is a piecewise continuous
path in `(0, 1)` whose one-sided limits are also in `(0, 1)`, and `ṅ(t) = l(t)`, `n(0) = 0`
(Shin, Vaccari, Zeevi, Dynamic Pricing with Online Reviews, SSRN 3439836 (Nov. 24, 2021), (EC.14), p.ec8).

**Formalization Note.** The one-sided limits stay in `(0, 1)` exactly because the corresponding
price has finite one-sided limits. This is the image of the class `Ψ` under the price–demand map.
The equation `ṅ = l` is in integral form, as in `IsFluidPath`. -/
def IsDemandPath (T : ℝ) (l n : ℝ → ℝ) : Prop :=
  IsPiecewiseContinuousOn T l ∧ (∀ t ∈ Set.Icc 0 T, l t ∈ Set.Ioo 0 1) ∧
    (∀ t ∈ Set.Ico 0 T, ∃ a ∈ Set.Ioo (0 : ℝ) 1, Tendsto l (𝓝[>] t) (𝓝 a)) ∧
    (∀ t ∈ Set.Ioc 0 T, ∃ a ∈ Set.Ioo (0 : ℝ) 1, Tendsto l (𝓝[<] t) (𝓝 a)) ∧
    ContinuousOn n (Set.Icc 0 T) ∧ n 0 = 0 ∧
    ∀ t ∈ Set.Icc 0 T, n t = ∫ s in (0 : ℝ)..t, l s

end OnlineReviewPricing


