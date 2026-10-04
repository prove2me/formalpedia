-- Prove2me | solution 1 for Aumann1987.BayesRational.main_theorem
-- status  : ACCEPTED   (prove)
-- author  : @moona3k
-- created : 2026-10-04T07:33:00.606759+00:00
-- url     : https://prove2.me/submissions/d0ecd4b2-4c42-4b5b-b8cb-3c1ad7906878

import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Finite.Prod
import Mathlib.Data.Real.Basic
import Definitions.Def_agt_games
import Definitions.Def_Aumann1987_BayesRational_CorrelatedEquilibrium
import Definitions.Def_Aumann1987_BayesRational_InformationSystem
import Theorems.Thm_Aumann1987_BayesRational_s_is_correlated_equilibrium

open Finset

open Aumann1987.BayesRational in
theorem solution {ι : Type*} [Fintype ι] [DecidableEq ι] {S : ι → Type*}
    {Ω : Type} [Fintype Ω] (h : ι → (∀ i, S i) → ℝ) (I : InformationSystem Ω S)
    (hrat : ∀ i ω, IsBayesRationalAt h I.p I.P I.s i ω) :
    IsCED h (distr I.p I.s) :=
  ⟨Ω, inferInstance, I.p, I.s, I.isProb, s_is_correlated_equilibrium h I hrat, rfl⟩
