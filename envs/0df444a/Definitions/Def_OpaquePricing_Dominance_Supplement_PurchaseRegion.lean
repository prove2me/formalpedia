-- Prove2me | Definitions.Def_OpaquePricing_Dominance_Supplement_PurchaseRegion
-- name    : OpaquePricing_Dominance_Supplement_PurchaseRegion
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-23T23:32:41.664411+00:00
-- url     : https://prove2.me/theorems/5573d155-dc81-469c-93f5-c60a7ad9a4ff
-- title:
--   The risk-neutral half-open purchase region E₂
-- statement:
--   For $N\ge2$, common item price $p$, and opaque price $r$ with $0\le r<p/N$, the region from Case 2 is
--   $$E_2(p,r)=\left\{v:p\le\max_i v_i<\frac{N}{N-1}(p-r)\right\}.$$
--   Its lower endpoint is included and its upper endpoint excluded. Lemma 9 uses this region to characterize customers who strictly prefer the full opaque product. The definition itself imposes no conclusion about their choice.
-- source:
--   Elmachtoub & Hamilton, The Power of Opaque Products in Pricing, author's manuscript (2021; Manag. Sci. doi:10.1287/mnsc.2020.3750), Appendix I.7, p. 51, Case 2; Appendix J, p. 54

import Mathlib
import Definitions.Def_OpaquePricing_Dominance_Setting
import Definitions.Def_OpaquePricing_Dominance_Supplement_SinglePricing

open MeasureTheory

namespace OpaquePricing.Dominance.Supplement

def E2 {N : ℕ} (p r : ℝ) : Set (Fin N → ℝ) :=
  {v | p ≤ maxValue v ∧ maxValue v < (N : ℝ) / ((N : ℝ) - 1) * (p - r)}

end OpaquePricing.Dominance.Supplement


