-- Prove2me | Definitions.Def_SingleFactorPricing_LogBound_tightPrice
-- name    : SingleFactorPricing_LogBound_tightPrice
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T09:15:02.602525+00:00
-- url     : https://prove2.me/theorems/7a334554-c93f-4ae1-bb6c-d6aac5f72f11
-- title:
--   The optimal prices of the tight instance
-- statement:
--   In the tight instance, the type with willingness to pay $v$ is charged $\bar p_v=v$, so personalized pricing earns $kv$ from it.
-- source:
--   Gallego, Berbeglia, Bounds and Heuristics for Multi-Product Personalized Pricing, arXiv:2102.03038v2, proof of Theorem 1, p.4

import Mathlib

open MeasureTheory

namespace SingleFactorPricing.LogBound

/-- **The optimal prices of the tight instance.** Gallego, Berbeglia, arXiv:2102.03038v2, proof of
Theorem 1, p.4: type `v` is charged its willingness to pay, so personalized pricing earns `kv` from
it. -/
def tightPrice (ρ : ℝ) (v : Set.Icc (1 : ℝ) ρ) (_ : Fin 1) : ℝ :=
  v

end SingleFactorPricing.LogBound


