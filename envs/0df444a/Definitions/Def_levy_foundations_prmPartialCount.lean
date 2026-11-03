-- Prove2me | Definitions.Def_levy_foundations_prmPartialCount
-- name    : levy_foundations_prmPartialCount
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-26T23:00:56.525535+00:00
-- url     : https://prove2.me/theorems/cf201141-d46a-4d8b-952c-bb37958c6a72
-- title:
--   Finite superposition of independent thinned Poisson pieces
-- statement:
--   Sum the thinned counts in pieces numbered 0 through n, producing a finite natural-number approximation to the Poisson random-measure count.
-- source:
--   Inspired by Shmuel Link, LeanLevy (MIT), frozen source commit 7e73fd9b23ad52956ec2756a815889a783131ce4, LeanLevy/RandomMeasure/PoissonRandomMeasure.lean, prmPartialCount at line 189.

import Definitions.Def_levy_foundations_thinnedCount

namespace LevyFoundations
noncomputable def prmPartialCount {Ω E : Type*}
    (K : ℕ → Ω → ℕ) (X : ℕ → ℕ → Ω → E)
    (A : Set E) (n : ℕ) (ω : Ω) : ℕ :=
  ∑ k ∈ Finset.range (n + 1), thinnedCount K X A k ω
end LevyFoundations


