-- Prove2me | Definitions.Def_levy_foundations_poissonTimeCount
-- name    : levy_foundations_poissonTimeCount
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-30T12:15:37.983792+00:00
-- url     : https://prove2.me/theorems/0fb7529c-d75b-4bec-8a58-131cc80e6233
-- title:
--   Running count of time-space Poisson points
-- statement:
--   Evaluate the Poisson random counting measure on the space-time strip (0,t] × A.
-- source:
--   Inspired by Shmuel Link, LeanLevy (MIT), https://github.com/slink/LeanLevy/blob/7e73fd9b23ad52956ec2756a815889a783131ce4/LeanLevy/RandomMeasure/TimeSpacePoisson.lean#L104-L108. Independently authored Prove2Me draft, awaiting remote compilation.

import Definitions.Def_levy_foundations_poissonRandomMeasure
import Mathlib.MeasureTheory.Integral.Prod

namespace LevyFoundations
/-- Count marks in the half-open time window (0,t] and mark set A. -/
noncomputable def poissonTimeCount {Ω E : Type}
    [MeasurableSpace E] (K : ℕ → Ω → ℕ)
    (X : ℕ → ℕ → Ω → ℝ × E) (A : Set E)
    (t : ℝ) (ω : Ω) : ENNReal :=
  poissonRandomMeasure K X ω (Set.Ioc (0 : ℝ) t ×ˢ A)
end LevyFoundations


