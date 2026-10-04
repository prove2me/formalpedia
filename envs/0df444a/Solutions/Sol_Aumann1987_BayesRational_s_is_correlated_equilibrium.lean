-- Prove2me | solution 1 for Aumann1987.BayesRational.s_is_correlated_equilibrium
-- status  : ACCEPTED   (prove)
-- author  : @moona3k
-- created : 2026-10-04T07:32:46.190339+00:00
-- url     : https://prove2.me/submissions/93690983-e9f5-4c97-9158-939f63a99d80

import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Finite.Prod
import Mathlib.Data.Real.Basic
import Definitions.Def_agt_games
import Definitions.Def_Aumann1987_BayesRational_CorrelatedEquilibrium
import Definitions.Def_Aumann1987_BayesRational_InformationSystem
import Theorems.Thm_Aumann1987_BayesRational_sum_over_partition

open Finset

open Aumann1987.BayesRational in
theorem solution {ι : Type*} [Fintype ι] [DecidableEq ι] {S : ι → Type*}
    {Ω : Type*} [Fintype Ω] (h : ι → (∀ i, S i) → ℝ) (I : InformationSystem Ω S)
    (hrat : ∀ i ω, IsBayesRationalAt h I.p I.P I.s i ω) :
    IsCorrelatedEquilibrium h I.p I.s := by
  intro i φ
  -- the recoding `φ ∘ sⁱ` is constant on each cell, because `sⁱ` itself is
  refine sum_over_partition h I i (hrat i) (fun ω => φ (I.s ω i)) ?_
  intro ω ω' hr
  exact congrArg φ (I.measurable i ω ω' hr)
