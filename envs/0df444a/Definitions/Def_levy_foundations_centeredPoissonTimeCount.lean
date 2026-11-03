-- Prove2me | Definitions.Def_levy_foundations_centeredPoissonTimeCount
-- name    : levy_foundations_centeredPoissonTimeCount
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-30T12:23:54.646303+00:00
-- url     : https://prove2.me/theorems/cc00fac6-2be7-46e8-b6b7-265e5bb0c543
-- title:
--   Centred running count of a time-space Poisson random measure
-- statement:
--   Take the real-valued count in (0,t]×A and subtract its deterministic mean t·m(A) for finite-intensity measurable A.
-- source:
--   Inspired by Shmuel Link, LeanLevy (MIT), commit 7e73fd9b23ad52956ec2756a815889a783131ce4. Independently formulated Prove2Me draft; remote elaboration and proof pending. PoissonMartingale.lean lines 120–126.

import Definitions.Def_levy_foundations_poissonTimeCount
import Mathlib.MeasureTheory.Integral.Prod
open scoped NNReal

open MeasureTheory
namespace LevyFoundations
noncomputable def centeredPoissonTimeCount
    {Ω E : Type} [MeasurableSpace E]
    (K : ℕ → Ω → ℕ) (X : ℕ → ℕ → Ω → ℝ × E)
    (m : Measure E) (A : Set E)
    (t : ℝ≥0) (ω : Ω) : ℝ :=
  (@LevyFoundations.poissonTimeCount Ω E _ K X A (t : ℝ) ω).toReal -
    (t : ℝ) * (m A).toReal
end LevyFoundations


