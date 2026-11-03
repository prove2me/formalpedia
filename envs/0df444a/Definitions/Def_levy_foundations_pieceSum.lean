-- Prove2me | Definitions.Def_levy_foundations_pieceSum
-- name    : levy_foundations_pieceSum
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-26T23:07:15.725489+00:00
-- url     : https://prove2.me/theorems/c3f79f4e-2da3-475c-8569-6591ec5ab38d
-- title:
--   Finite sum over the Poisson marks in a partition piece
-- statement:
--   Each partition piece contributes the finite sum of the test function over its realised Poisson points.
-- source:
--   Inspired by Shmuel Link, LeanLevy (MIT), https://github.com/slink/LeanLevy/blob/7e73fd9b23ad52956ec2756a815889a783131ce4/LeanLevy/RandomMeasure/PoissonPointFamily.lean#L425-L433. Independently authored Prove2Me draft, awaiting remote compilation.

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Real.Basic

namespace LevyFoundations
/-- Sum a test function over the marks of one Poisson partition piece. -/
noncomputable def pieceSum {Ω E : Type} (K : ℕ → Ω → ℕ)
    (X : ℕ → ℕ → Ω → E) (f : E → ℝ) (k : ℕ) (ω : Ω) : ℝ :=
  ∑ n ∈ Finset.range (K k ω), f (X k n ω)
end LevyFoundations


