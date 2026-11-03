-- Prove2me | Definitions.Def_levy_foundations_finiteDimMap
-- name    : levy_foundations_finiteDimMap
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-30T21:14:59.697108+00:00
-- url     : https://prove2.me/theorems/d2e9f011-2b27-4837-b185-30c7dd280c90
-- title:
--   Finite-dimensional sampling map for a stochastic process
-- statement:
--   Finite-dimensional sampling map for a stochastic process.
-- source:
--   https://github.com/slink/LeanLevy/blob/7e73fd9b23ad52956ec2756a815889a783131ce4/LeanLevy/Processes/FiniteDimensional.lean#L45

import Mathlib.MeasureTheory.Constructions.Projective

open scoped NNReal

namespace LevyFoundations
/-- Sample a stochastic process at the times of a finite index set. -/
def finiteDimMap {Ω E : Type*} (X : ℝ≥0 → Ω → E)
    (I : Finset ℝ≥0) : Ω → ((i : I) → E) :=
  fun ω (i : I) => X i ω
end LevyFoundations


