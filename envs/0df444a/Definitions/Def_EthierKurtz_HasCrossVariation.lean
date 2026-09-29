-- Prove2me | Definitions.Def_EthierKurtz_HasCrossVariation
-- name    : EthierKurtz_HasCrossVariation
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-21T05:43:58.322798+00:00
-- url     : https://prove2.me/theorems/ee1c2e25-5fa3-4c27-94f9-ae41b221bf5a
-- title:
--   Cross variation by dyadic increments
-- statement:
--   Convergence in probability of the dyadic products of two processes’ increments to the specified cross-variation process.
-- source:
--   Stewart N. Ethier and Thomas G. Kurtz, Markov Processes: Characterization and Convergence, Wiley, 1986. Chapter 2, equation (6.4), printed p. 79 (PDF p. 88); Chapter 5, Theorem 2.9, printed p. 287 (PDF p. 296).

import Mathlib

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal Topology BigOperators

namespace EthierKurtz

/-- Cross variation as the probability limit of dyadic increment products,
Chapter 2 (6.4). A concrete relation, not a postulated bracket operator. -/
def HasCrossVariation {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X Y A : ℝ≥0 → Ω → ℝ) : Prop :=
  ∀ t : ℝ≥0, TendstoInMeasure P
    (fun m ω => ∑ k ∈ Finset.range (2 ^ m),
      (X (((k : ℝ≥0) + 1) * t / 2 ^ m) ω - X ((k : ℝ≥0) * t / 2 ^ m) ω) *
      (Y (((k : ℝ≥0) + 1) * t / 2 ^ m) ω - Y ((k : ℝ≥0) * t / 2 ^ m) ω))
    atTop (A t)

end EthierKurtz


