-- Prove2me | solution 1 for AJOnline.ofStrategy_randCompetitive
-- status  : ACCEPTED   (prove)
-- author  : @martelus trismortuus
-- created : 2026-11-18T16:12:49.790892+00:00
-- url     : https://prove2.me/submissions/97daaf4b-a835-435f-8cb0-bcd3bb3e2761

import Mathlib
import Definitions.Def_AJOnline_CostedGame

open AJGames AJOnline
open scoped ENNReal NNReal

universe u

/-- Every outcome of a play-out is a position of the game. -/
theorem playOut_support_pos {A : Game.{u}} (β : BehStrategy A) :
    ∀ (rs s : List A.M), s ∈ A.pos → ∀ p ∈ (playOut β s rs).support, p ∈ A.pos := by
  intro rs
  induction rs with
  | nil => intro s hs p hp; simp [playOut] at hp; rw [hp]; exact hs
  | cons r rs ih =>
    intro s hs p hp
    simp only [playOut] at hp
    split_ifs at hp with h
    · rw [PMF.mem_support_bind_iff] at hp
      obtain ⟨o, ho, hpo⟩ := hp
      cases o with
      | none => simp at hpo; rw [hpo]; exact h.2
      | some a =>
        have hleg := β.legal _ a ((PMF.mem_support_iff _ _).1 ho)
        exact ih _ (hleg.2.2 h.2) p hpo
    · simp at hp; rw [hp]; exact hs

/-- Against any script, a deterministic strategy's play-out is a single play of `σ`. -/
theorem playOut_ofStrategy {A : Game.{u}} (σ : Strategy A) :
    ∀ (rs s : List A.M), s ∈ σ.carrier → ∃ p ∈ σ.carrier, playOut (ofStrategy σ) s rs = PMF.pure p := by
  classical
  intro rs
  induction rs with
  | nil => intro s hs; exact ⟨s, hs, by simp [playOut]⟩
  | cons r rs ih =>
    intro s hs
    simp only [playOut]
    split_ifs with h
    · have hsr : s ++ [r] ∈ σ.carrier := σ.receptive s r hs h.1 h.2
      simp only [ofStrategy]
      by_cases hb : ∃ b, s ++ [r] ++ [b] ∈ σ.carrier ∧ A.lab b = Pl.P
      · rw [dif_pos hb, PMF.pure_bind]
        exact ih _ hb.choose_spec.1
      · rw [dif_neg hb, PMF.pure_bind]
        exact ⟨_, hsr, rfl⟩
    · exact ⟨s, hs, rfl⟩

theorem solution (C : CostedGame.{u}) (σ : Strategy C.G) (ρ b : ℝ≥0)
    (h : Competitive C σ ρ b) : RandCompetitive C (ofStrategy σ) ρ b := by
  intro rs
  obtain ⟨p, hp, hout⟩ := playOut_ofStrategy σ rs [] σ.nil_mem
  have key : ∀ f : List C.G.M → ℝ≥0∞, ∑' s, playOut (ofStrategy σ) [] rs s * f s = f p := by
    intro f
    rw [hout, tsum_eq_single p]
    · simp
    · intro s hs; simp [PMF.pure_apply, hs]
  unfold expAlg expOpt
  rw [key C.alg, key C.opt]
  exact h p hp
