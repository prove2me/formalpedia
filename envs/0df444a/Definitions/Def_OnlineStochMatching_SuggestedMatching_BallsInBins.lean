-- Prove2me | Definitions.Def_OnlineStochMatching_SuggestedMatching_BallsInBins
-- name    : OnlineStochMatching_SuggestedMatching_BallsInBins
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-05T21:32:57.190814+00:00
-- url     : https://prove2.me/theorems/388efcaf-d174-4256-8461-416d7267c795
-- title:
--   Uniform occupancy probability and expectation
-- statement:
--   Place $n$ balls independently and uniformly into $n$ labelled bins. For a set $B$ of bins, let $S_B$ count the bins in $B$ that receive at least one ball:
--
--   $$S_B(\omega)=|\{b\in B:\exists t,\ \omega(t)=b\}|.$$
--
--   Probabilities and expectations on any finite sample space use normalized counting measure. This general occupancy model is reused for Fact 1 and for the suggested matching run.
-- source:
--   Feldman, Mehta, Mirrokni, Muthukrishnan, Online Stochastic Matching: Beating 1-1/e, arXiv:0905.4100v1, p. 4, §2.1, Fact 1

import Mathlib

namespace OnlineStochMatching.SuggestedMatching

/-- The number of bins in `B` hit by `n` independent placements into `Fin n`. -/
noncomputable def occupiedIn (n : ℕ) (B : Finset (Fin n)) (ω : Fin n → Fin n) : ℕ := by
  classical
  exact (B.filter fun b => ∃ t, ω t = b).card

/-- Uniform counting probability on a finite sample space. -/
noncomputable def uniformProbability {Ω : Type} [Fintype Ω] (P : Ω → Prop) : ℝ := by
  classical
  exact ((Finset.univ.filter P).card : ℝ) / (Fintype.card Ω : ℝ)

/-- Uniform counting expectation of a real-valued statistic. -/
noncomputable def uniformExpectation {Ω : Type} [Fintype Ω] (X : Ω → ℝ) : ℝ :=
  (∑ ω, X ω) / (Fintype.card Ω : ℝ)

end OnlineStochMatching.SuggestedMatching


