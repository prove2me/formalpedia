-- Prove2me | Definitions.Def_levy_foundations_compensatedPoissonSum
-- name    : levy_foundations_compensatedPoissonSum
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-30T10:31:52.02519+00:00
-- url     : https://prove2.me/theorems/a418e45a-22de-441a-ac70-74df62fdcf77
-- title:
--   Countable pathwise compensated Poisson series
-- statement:
--   The pathwise compensated Poisson integral is a countable series of centred piece sums. Almost-sure convergence requires separate hypotheses.
-- source:
--   Inspired by Shmuel Link, LeanLevy (MIT), https://github.com/slink/LeanLevy/blob/7e73fd9b23ad52956ec2756a815889a783131ce4/LeanLevy/RandomMeasure/PoissonCompensated.lean#L77-L80. Independently authored Prove2Me draft, awaiting remote compilation.

import Definitions.Def_levy_foundations_compensatedPieceSum
import Mathlib.Topology.Algebra.InfiniteSum.Basic

open MeasureTheory
namespace LevyFoundations
/-- Sum the centred Poisson piece contributions over every partition piece. -/
noncomputable def compensatedPoissonSum {Ω E : Type}
    [MeasurableSpace E] (m : Measure E) [SigmaFinite m]
    (K : ℕ → Ω → ℕ) (X : ℕ → ℕ → Ω → E)
    (f : E → ℝ) (ω : Ω) : ℝ :=
  ∑' k, compensatedPieceSum m K X f k ω
end LevyFoundations


