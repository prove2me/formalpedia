-- Prove2me | Definitions.Def_allocationWeight
-- name    : allocationWeight
-- status  : Definition
-- author  : @Eyal1990
-- created : 2026-10-16T18:19:43.101225+00:00
-- url     : https://prove2.me/theorems/88b7bc40-1526-46c8-966e-2173a52ac7ad
-- title:
--   Weight of a single natural-valued allocation
-- statement:
--   The summand used by allocationSum for one allocation, separated into a helper definition so filtered allocation sums can be stated directly.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Analysis/LiteralAnalyticSummand.lean#L163-L175

import Mathlib.Tactic

open scoped BigOperators

namespace OAI.PiExponent.LiteralAnalytic

def allocationWeight {σ : Type*} [Fintype σ] [DecidableEq σ]
    (e : σ → ℕ) (k : ℕ) (n : σ → Fin (k + 1)) : ℕ :=
  if ∑ i, (n i : ℕ) = k then
    ∏ i,
      (if e i = 0 then (if (n i : ℕ) = 0 then 1 else 0)
       else Nat.choose ((n i : ℕ) + e i - 1) (n i : ℕ))
  else 0

end OAI.PiExponent.LiteralAnalytic


