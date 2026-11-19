-- Prove2me | solution 1 for AJGames.playOut_support_pos
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-18T15:40:55.789606+00:00
-- url     : https://prove2.me/submissions/ec4f92c8-fd27-45ca-a72c-e466a9579ce8

import Mathlib
import Definitions.Def_AJGames_Behaviour

set_option autoImplicit false
universe u

open AJGames in
theorem solution {A : Game.{u}} (β : BehStrategy A) :
    ∀ (rs s : List A.M), s ∈ A.pos → ∀ p ∈ (playOut β s rs).support, p ∈ A.pos := by
  intro rs
  induction rs with
  | nil =>
    intro s hs p hp
    simp only [playOut, PMF.support_pure, Set.mem_singleton_iff] at hp
    subst hp; exact hs
  | cons r rs ih =>
    intro s hs p hp
    simp only [playOut] at hp
    split_ifs at hp with hc
    · rw [PMF.mem_support_bind_iff] at hp
      obtain ⟨o, ho, hp⟩ := hp
      cases o with
      | none =>
        simp only [Option.elim, PMF.support_pure, Set.mem_singleton_iff] at hp
        subst hp; exact hc.2
      | some a =>
        simp only [Option.elim] at hp
        have hleg := β.legal (s ++ [r]) a ((PMF.mem_support_iff _ _).1 ho)
        exact ih _ (hleg.2.2 hc.2) p hp
    · simp only [PMF.support_pure, Set.mem_singleton_iff] at hp
      subst hp; exact hs
