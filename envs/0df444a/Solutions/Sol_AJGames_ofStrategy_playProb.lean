-- Prove2me | solution 1 for AJGames.ofStrategy_playProb
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-18T15:40:58.475034+00:00
-- url     : https://prove2.me/submissions/eb11f4a0-97ae-445b-b0bb-7722bd2f285d

import Mathlib
import Definitions.Def_AJGames_Behaviour

set_option autoImplicit false
universe u

namespace OSAux
open AJGames
open scoped ENNReal


lemma step {A : Game.{u}} (β : BehStrategy A) (r : List A.M) (a : A.M) :
    playProb β (r ++ [a]) =
      playProb β r * (if A.lab a = Pl.P then β.next r (some a) else 1) := by
  simp [playProb, playProbRev, List.reverse_append]

end OSAux

open AJGames in
open scoped ENNReal in
open Classical in
theorem solution {A : Game.{u}} (σ : Strategy A) (s : List A.M) (hs : s ∈ A.pos) :
    playProb (ofStrategy σ) s = if s ∈ σ.carrier then 1 else 0 := by
  induction s using List.reverseRecOn with
  | nil =>
    simp [playProb, playProbRev, σ.nil_mem]
  | append_singleton r a ih =>
    have hr : r ∈ A.pos := A.prefix_closed r (r ++ [a]) (List.prefix_append r [a]) hs
    rw [OSAux.step, ih hr]
    by_cases hlab : A.lab a = Pl.P
    · rw [if_pos hlab]
      by_cases hrσ : r ∈ σ.carrier
      · rw [if_pos hrσ, one_mul]
        by_cases haσ : r ++ [a] ∈ σ.carrier
        · rw [if_pos haσ]
          have hex : ∃ b, r ++ [b] ∈ σ.carrier ∧ A.lab b = Pl.P := ⟨a, haσ, hlab⟩
          have hch : hex.choose = a :=
            σ.deterministic r _ a hex.choose_spec.1 haσ hex.choose_spec.2 hlab
          simp only [ofStrategy, dif_pos hex, PMF.pure_apply, hch, if_true]
        · rw [if_neg haσ]
          simp only [ofStrategy]
          split_ifs with hex
          · rw [PMF.pure_apply, if_neg]
            intro heq
            have : hex.choose = a := (Option.some_inj.1 heq).symm
            exact haσ (this ▸ hex.choose_spec.1)
          · rw [PMF.pure_apply, if_neg (by simp)]
      · rw [if_neg hrσ, zero_mul, if_neg]
        intro h
        exact hrσ (σ.prefix_closed r _ (List.prefix_append r [a]) h)
    · rw [if_neg hlab, mul_one]
      have hO : A.lab a = Pl.O := by
        cases h : A.lab a
        · exact absurd h hlab
        · rfl
      by_cases hrσ : r ∈ σ.carrier
      · rw [if_pos hrσ, if_pos (σ.receptive r a hrσ hO hs)]
      · rw [if_neg hrσ, if_neg]
        intro h
        exact hrσ (σ.prefix_closed r _ (List.prefix_append r [a]) h)
