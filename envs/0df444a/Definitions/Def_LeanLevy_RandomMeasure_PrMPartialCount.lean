-- Prove2me | Definitions.Def_LeanLevy_RandomMeasure_PrMPartialCount
-- name    : LeanLevy_RandomMeasure_PrMPartialCount
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-01T18:03:53.67073+00:00
-- url     : https://prove2.me/theorems/e5855484-0070-40bc-832b-1be5fcd4a0f9
-- title:
--   LeanLevy partial superposition count for a Poisson random measure
-- statement:
--   Source-exact promotion of the original private partial-count definition: the number of sample points in the mark set A among the first n+1 Poisson point-family pieces, represented as a finite sum of thinned counts. Needed to decompose the original finite-dimensional independence proof into verifier-sized public support theorems.

import Definitions.Def_LeanLevy_RandomMeasure_PoissonRandomMeasure
import Definitions.Def_LeanLevy_RandomMeasure_PoissonPointFamily
open MeasureTheory ProbabilityTheory
namespace ProbabilityTheory
variable {Ω E : Type} [MeasurableSpace E] [MeasurableSpace Ω]
noncomputable def prmPartialCount (K : ℕ → Ω → ℕ) (X : ℕ → ℕ → Ω → E) (A : Set E) (n : ℕ)
    (ω : Ω) : ℕ :=
  ∑ k ∈ Finset.range (n + 1), thinnedCount K X A k ω
end ProbabilityTheory


