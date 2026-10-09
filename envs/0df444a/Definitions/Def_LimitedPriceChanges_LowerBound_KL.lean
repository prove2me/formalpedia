-- Prove2me | Definitions.Def_LimitedPriceChanges_LowerBound_KL
-- name    : LimitedPriceChanges_LowerBound_KL
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-08T16:03:16.20298+00:00
-- url     : https://prove2.me/theorems/7140a03f-72cd-4e3b-a641-0244d8e6f7b6
-- title:
--   Binary relative entropy for the Bernoulli instance
-- statement:
--   For Bernoulli success probabilities $a,c$ in the open unit interval, the relative entropy is
--   $$D_{\mathrm{KL}}(\operatorname{Ber}(a)\|\operatorname{Ber}(c))=a\log(a/c)+(1-a)\log((1-a)/(1-c)).$$
--   It measures the information in one demand observation under two parameters.
--
--   **Formalization Note** The formula is a total Lean function, but the corrected KL milestone requires interior probabilities, so the logarithms and divisions there have their ordinary mathematical meaning.
-- source:
--   Chen, Chao and Wang, Data-Based Dynamic Pricing and Inventory Control with Censored Demand and Limited Price Changes, SSRN 2700747 (revision of 2020-02-10), p. 36, Lemma 2 and proof

import Mathlib
import Definitions.Def_LimitedPriceChanges_LowerBound_Model

namespace LimitedPriceChanges.LowerBound

/-- Binary relative entropy on its interior domain. -/
noncomputable def klBer (a c : ℝ) : ℝ :=
  a * Real.log (a / c) + (1 - a) * Real.log ((1 - a) / (1 - c))

end LimitedPriceChanges.LowerBound


