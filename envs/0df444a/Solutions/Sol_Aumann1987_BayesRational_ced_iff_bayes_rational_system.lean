-- Prove2me | solution 1 for Aumann1987.BayesRational.ced_iff_bayes_rational_system
-- status  : ACCEPTED   (prove)
-- author  : @moona3k
-- created : 2026-10-04T07:33:36.580349+00:00
-- url     : https://prove2.me/submissions/1eed87e9-0288-4bfa-9906-f45b030e7293

import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Finite.Prod
import Mathlib.Data.Real.Basic
import Definitions.Def_agt_games
import Definitions.Def_Aumann1987_BayesRational_CorrelatedEquilibrium
import Definitions.Def_Aumann1987_BayesRational_InformationSystem
import Theorems.Thm_Aumann1987_BayesRational_main_theorem
import Theorems.Thm_Aumann1987_BayesRational_converse

open Finset

open Aumann1987.BayesRational in
theorem solution {ι : Type*} [Fintype ι] [DecidableEq ι] {S : ι → Type*}
    (h : ι → (∀ i, S i) → ℝ) (Q : (∀ i, S i) → ℝ) :
    IsCED h Q ↔
      ∃ (Ω : Type) (_ : Fintype Ω) (I : InformationSystem Ω S),
        (∀ i ω, IsBayesRationalAt h I.p I.P I.s i ω) ∧ distr I.p I.s = Q := by
  constructor
  · rintro ⟨Γ, instΓ, q, f, hq, hce, hQ⟩
    obtain ⟨Ω, instΩ, I, hrat, hdistr⟩ := converse h q hq f hce
    exact ⟨Ω, instΩ, I, hrat, hdistr.trans hQ⟩
  · rintro ⟨Ω, instΩ, I, hrat, hQ⟩
    have := main_theorem h I hrat
    rwa [hQ] at this
