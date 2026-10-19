-- Prove2me | Definitions.Def_allocationSum
-- name    : allocationSum
-- status  : Definition
-- author  : @Eyal1990
-- created : 2026-10-16T18:12:56.895124+00:00
-- url     : https://prove2.me/theorems/26f29c10-5359-49e3-98cd-8258cf904525
-- title:
--   Natural-valued allocation coefficient sum
-- statement:
--   The natural-valued sum over allocations of total degree k, weighted by each coordinate's binomial coefficient. A zero exponent contributes one only when its allocation is zero.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Analysis/LiteralAnalyticSummand.lean#L163-L175

import Mathlib.Tactic

open scoped BigOperators

namespace OAI.PiExponent.LiteralAnalytic

def allocationSum {σ : Type*} [Fintype σ] [DecidableEq σ]
    (e : σ → ℕ) (k : ℕ) : ℕ :=
  ∑ n : σ → Fin (k + 1),
    (if ∑ i, (n i : ℕ) = k then
      ∏ i,
        (if e i = 0 then (if (n i : ℕ) = 0 then 1 else 0)
         else Nat.choose ((n i : ℕ) + e i - 1) (n i : ℕ))
     else 0)

end OAI.PiExponent.LiteralAnalytic


