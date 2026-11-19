-- Prove2me | Definitions.Def_AJGames_Behaviour
-- name    : AJGames_Behaviour
-- status  : Definition
-- author  : @martelus trismortuus
-- created : 2026-11-18T15:27:41.021218+00:00
-- url     : https://prove2.me/theorems/720f7737-3c93-442c-86ab-509c29f25f41
-- title:
--   Behaviour strategies, play probability and play-out against a script
-- statement:
--   A **behaviour strategy** $\beta$ for Player in $A$ assigns to every finite sequence $s$ a probability distribution $\beta(s)$ on $M_A\cup\{\mathrm{none}\}$. A move $a$ may have positive probability only if three conditions hold:
--
--   1. Player is to move at $s$, meaning the last move of $s$ is an Opponent move;
--   2. $a$ is a Player move;
--   3. $sa$ is a position whenever $s$ is.
--
--   The file defines the following derived notions.
--
--   1. The **probability of a play** $s$ is the product, over the Player moves $a$ of $s$, of the probability $\beta$ gave $a$ after the prefix preceding it.
--   2. $\beta$ **depends on** a function $f$ of histories when $f(s)=f(t)$ implies $\beta(s)=\beta(t)$; **history-free** is the case where $f$ returns the last move.
--   3. A deterministic strategy $\sigma$ is read as a behaviour strategy by putting all mass on $\sigma$'s Player move when it has one, and on $\mathrm{none}$ otherwise.
--   4. The **play-out** of $\beta$ from a position $s$ against a script $r_1,\dots,r_n$ of moves is a distribution on finite plays. If $r_1$ is an Opponent move and $s\,r_1$ is a position, play it and draw from $\beta(s\,r_1)$. A move continues the play with $r_2,\dots,r_n$; $\mathrm{none}$ stops it, and $s\,r_1$ is the outcome. Otherwise, and when the script is exhausted, the outcome is $s$.
--
--   The play-out is the semantics of a randomised online algorithm against an oblivious adversary.
--
--   **Formalization Note** Opponent's moves are not randomised; an oblivious adversary fixes them in advance. Distributions are Mathlib `PMF`s.
-- source:
--   H. W. Kuhn, Extensive games and the problem of information, Contributions to the Theory of Games II, Annals of Mathematics Studies 28 (1953) 193-216 (behaviour strategies), placed on the games of S. Abramsky, R. Jagadeesan, Games and full completeness for multiplicative linear logic, J. Symbolic Logic 59(2) (1994) 543-574, https://arxiv.org/abs/1311.6057

import Mathlib
import Definitions.Def_AJGames_Strategy

/-!
# Behaviour strategies in Abramsky–Jagadeesan games

A *behaviour strategy* for Player gives, at every position, a probability distribution over Player's
next move, or `none` (no move). This is Kuhn's notion of behaviour strategy (H. W. Kuhn,
*Extensive games and the problem of information*, Contributions to the Theory of Games II, 1953)
placed on AJ games (Abramsky and Jagadeesan, J. Symbolic Logic 59(2), 1994, Definition 2). It is the
form in which randomised online algorithms, such as memoryless policies, appear as strategies.

**Formalization Note.** Finite-play (safety) fragment. Opponent moves are not randomised: an
oblivious adversary fixes them. `playProb β s` is the probability that Player, following `β`, makes
every Player move of `s` when Opponent plays the Opponent moves of `s`. A deterministic strategy
`σ` is read as the behaviour strategy `ofStrategy σ`, which puts all its mass on `σ`'s move when
`σ` has one and on `none` otherwise.
-/

namespace AJGames

universe u

open scoped ENNReal

variable {A : Game.{u}}

/-- Player is to move at `s`: the last move of `s` was an Opponent move. Opponent opens, so
Player is not to move at `[]`. -/
def PlayerToMove (A : Game.{u}) (s : List A.M) : Prop :=
  ∃ m, s.getLast? = some m ∧ A.lab m = Pl.O

/-- A behaviour strategy for Player in `A`: a distribution over Player's next move (or `none`) at
every position. Moves in the support are legal Player moves, offered only when Player is to move. -/
structure BehStrategy (A : Game.{u}) where
  next : List A.M → PMF (Option A.M)
  legal : ∀ s a, next s (some a) ≠ 0 →
    PlayerToMove A s ∧ A.lab a = Pl.P ∧ (s ∈ A.pos → s ++ [a] ∈ A.pos)

/-- Probability of a play, computed on the reversed play (last move first). -/
noncomputable def playProbRev (β : BehStrategy A) : List A.M → ℝ≥0∞
  | [] => 1
  | a :: r => playProbRev β r * (if A.lab a = Pl.P then β.next r.reverse (some a) else 1)

/-- The probability that Player, following `β`, makes every Player move of `s` when Opponent
plays the Opponent moves of `s`: the product of `β`'s probabilities of its own moves. -/
noncomputable def playProb (β : BehStrategy A) (s : List A.M) : ℝ≥0∞ :=
  playProbRev β s.reverse

/-- `β` is history-free: its next-move distribution depends only on the last move. -/
def BehStrategy.HistoryFree (β : BehStrategy A) : Prop :=
  ∀ s t : List A.M, s.getLast? = t.getLast? → β.next s = β.next t

/-- `β` depends on the history only through `f`. `HistoryFree` is the case `f = List.getLast?`;
a memoryless online policy depends on (current configuration, last request). -/
def BehStrategy.DependsOn {S : Type*} (β : BehStrategy A) (f : List A.M → S) : Prop :=
  ∀ s t : List A.M, f s = f t → β.next s = β.next t

/-- If `σ` has a Player move at `s`, then Player is to move at `s`. -/
theorem Strategy.playerToMove_of_move (σ : Strategy A) {s : List A.M} {b : A.M}
    (hb : s ++ [b] ∈ σ.carrier) (hP : A.lab b = Pl.P) : PlayerToMove A s := by
  cases hl : s.getLast? with
  | none =>
    have : s = [] := List.getLast?_eq_none_iff.1 hl
    subst this
    have := σ.first_O b [] (by simpa using hb)
    rw [hP] at this; cases this
  | some m =>
    refine ⟨m, hl, ?_⟩
    have halt := A.alt _ (σ.subset_pos hb)
    have hne : A.lab m ≠ A.lab b := (List.isChain_append.1 halt).2.2 m hl b (by simp)
    rw [hP] at hne
    cases h : A.lab m
    · exact absurd h hne
    · rfl

open Classical in
/-- A deterministic strategy read as a behaviour strategy: all mass on `σ`'s move when it has one,
otherwise on `none`. -/
noncomputable def ofStrategy (σ : Strategy A) : BehStrategy A where
  next s := if h : ∃ b, s ++ [b] ∈ σ.carrier ∧ A.lab b = Pl.P then PMF.pure (some h.choose)
    else PMF.pure none
  legal := by
    intro s a ha
    by_cases h : ∃ b, s ++ [b] ∈ σ.carrier ∧ A.lab b = Pl.P
    · rw [dif_pos h, PMF.pure_apply] at ha
      have hab : some a = some h.choose := by
        by_contra hne; exact ha (if_neg hne)
      cases hab
      obtain ⟨hmem, hP⟩ := h.choose_spec
      exact ⟨σ.playerToMove_of_move hmem hP, hP, fun _ => σ.subset_pos hmem⟩
    · rw [dif_neg h, PMF.pure_apply] at ha
      exact absurd (if_neg (by simp)) ha

open Classical in
/-- **Play-out against an oblivious adversary** (stop-counts semantics). From position `s`, the
adversary's remaining script is `rs`. The next request `r` is played if it is a legal Opponent move;
Player then draws from `β.next`. A move `a` continues the play; `none` stops it, and the play so far
is an outcome with that probability. The play also stops when the script runs out or the next
request is not a legal Opponent move. -/
noncomputable def playOut (β : BehStrategy A) : List A.M → List A.M → PMF (List A.M)
  | s, [] => PMF.pure s
  | s, r :: rs =>
    if A.lab r = Pl.O ∧ s ++ [r] ∈ A.pos then
      (β.next (s ++ [r])).bind fun o =>
        o.elim (PMF.pure (s ++ [r])) fun a => playOut β (s ++ [r] ++ [a]) rs
    else PMF.pure s

end AJGames


