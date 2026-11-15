-- Prove2me | Definitions.Def_TimeSpaceMA_RRVNearFull
-- name    : TimeSpaceMA_RRVNearFull
-- status  : Definition
-- author  : @bersubs
-- created : 2026-11-14T20:34:43.678456+00:00
-- url     : https://prove2.me/theorems/9cdb8bab-ac31-4e9f-bf0e-e9d196bfd708
-- title:
--   Strong extraction leaving a polylogarithmic amount of entropy
-- statement:
--   The predicate fixes the interface for a first strong extractor with a cubically polylogarithmic seed and output length given by the entropy threshold minus that seed length, rounded down at zero. The guarantee concerns the joint distribution of the seed and output against every finite event and requires a uniform polynomial-time evaluator.

import Definitions.Def_TimeSpaceMA_TUZExtractorComponents

open scoped BigOperators

namespace TimeSpaceMA.RRV
open Turing.MultiTapeTM

/-- A first strong extractor may leave a polylogarithmic amount of entropy to recover. -/
def HasNearFullStrongExtractor (ε : ℝ) : Prop :=
  ∃ (B : ℕ) (eval : ExtractorInput → ℕ), 0 < B ∧
    ComputableInPolyTime eval encExtractorInput encNat ∧
    ∀ w K : ℕ, 1 ≤ w → K ≤ w →
      ∀ p : Fin (2^w) → ℝ, (∑ x, p x = 1) →
        (∀ x, 0 ≤ p x ∧ p x ≤ 1/(2:ℝ)^K) →
        let d := B*w.size^3
        WeightedExtractorEvents (fun x s => (s,fixedOutput eval w K d (K-d) x s)) p ε

end TimeSpaceMA.RRV


