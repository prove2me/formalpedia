-- Prove2me | Definitions.Def_levy_foundations_thinnedCount
-- name    : levy_foundations_thinnedCount
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-26T22:52:21.147196+00:00
-- url     : https://prove2.me/theorems/09d923e7-c682-4470-af0b-e3b8598d0392
-- title:
--   Number of marked points in a single finite-intensity piece
-- statement:
--   Count those marks in a single point-family piece k, among indices below K(k,ω), that lie in A.
-- source:
--   Inspired by Shmuel Link, LeanLevy (MIT), frozen source commit 7e73fd9b23ad52956ec2756a815889a783131ce4, LeanLevy/RandomMeasure/PoissonPointFamily.lean, thinnedCount at line 933.

import Mathlib.MeasureTheory.Integral.DominatedConvergence

namespace LevyFoundations
noncomputable def thinnedCount {Ω E : Type*}
    (K : ℕ → Ω → ℕ) (X : ℕ → ℕ → Ω → E)
    (A : Set E) (k : ℕ) (ω : Ω) : ℕ :=
  by
    classical
    exact ((Finset.range (K k ω)).filter fun n => X k n ω ∈ A).card
end LevyFoundations


