-- Prove2me | solution 1 for Aumann1987.BayesRational.converse
-- status  : ACCEPTED   (prove)
-- author  : @moona3k
-- created : 2026-10-04T07:33:35.951977+00:00
-- url     : https://prove2.me/submissions/05778d8e-c130-471b-972d-c5e82d282e8c

import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Finite.Prod
import Mathlib.Data.Real.Basic
import Definitions.Def_agt_games
import Definitions.Def_Aumann1987_BayesRational_CorrelatedEquilibrium
import Definitions.Def_Aumann1987_BayesRational_InformationSystem
import Theorems.Thm_Aumann1987_BayesRational_bayes_rational_iff_ce

open Finset

open Aumann1987.BayesRational in
theorem solution {ι : Type*} [Fintype ι] [DecidableEq ι] {S : ι → Type*}
    {Γ : Type} [Fintype Γ] (h : ι → (∀ i, S i) → ℝ) (q : Γ → ℝ) (hq : AGT.IsLottery q)
    (f : Γ → ∀ i, S i) (hf : IsCorrelatedEquilibrium h q f) :
    ∃ (Ω : Type) (_ : Fintype Ω) (I : InformationSystem Ω S),
      (∀ i ω, IsBayesRationalAt h I.p I.P I.s i ω) ∧ distr I.p I.s = distr q f := by
  exact ⟨Γ, inferInstance,
    InformationSystem.mk q hq (fun j => Setoid.ker (fun γ' => f γ' j)) f
      (fun _ _ _ hr => hr),
    (bayes_rational_iff_ce h q hq f).mpr hf, rfl⟩
