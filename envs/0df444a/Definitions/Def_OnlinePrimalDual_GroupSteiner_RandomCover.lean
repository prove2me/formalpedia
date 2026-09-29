-- Prove2me | Definitions.Def_OnlinePrimalDual_GroupSteiner_RandomCover
-- name    : OnlinePrimalDual_GroupSteiner_RandomCover
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-21T05:55:05.082694+00:00
-- url     : https://prove2.me/theorems/4bffb9bd-d106-4bc0-bca6-84f4fdb8dc3c
-- title:
--   A finite probability distribution over random edge covers
-- statement:
--   `RandomCover E` bundles a probability mass function `p : Finset E → ℝ` over subsets of a
--   finite edge type `E`, representing the random edge-cover `C` produced by the online
--   randomized rounding scheme at a given point in its execution: `p C` is the probability that
--   the random cover equals exactly `C`, non-negative and summing to `1`.
-- source:
--   Buchbinder & Naor, The Design of Competitive Online Algorithms via a Primal-Dual Approach, FnT TCS 2009, p. 229-230, Section 11.2

import Mathlib

namespace OnlinePrimalDual.GroupSteiner

/-- A finite probability distribution over subsets of a finite edge type `E`, representing the
random edge-cover `C` produced by the online randomized rounding scheme of Buchbinder & Naor,
*The Design of Competitive Online Algorithms via a Primal-Dual Approach*, FnT TCS 2009, Section
11.2 (p. 229-230, PDF p. 140-141), at a given point in its execution. `p C` is the probability
that the algorithm's random cover equals exactly the edge set `C`. -/
structure RandomCover (E : Type*) [Fintype E] [DecidableEq E] where
  /-- `p C` is the probability that the random cover equals exactly `C`. -/
  p : Finset E → ℝ
  hp_nonneg : ∀ C, 0 ≤ p C
  hp_sum : ∑ C, p C = 1

end OnlinePrimalDual.GroupSteiner


