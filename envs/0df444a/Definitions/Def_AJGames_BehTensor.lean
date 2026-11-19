-- Prove2me | Definitions.Def_AJGames_BehTensor
-- name    : AJGames_BehTensor
-- status  : Definition
-- author  : @martelus trismortuus
-- created : 2026-11-18T15:28:29.5234+00:00
-- url     : https://prove2.me/theorems/f649d414-a576-4f7f-a9b1-be84abae4f9e
-- title:
--   Tensor of behaviour strategies; never-stopping strategies; open games
-- statement:
--   For behaviour strategies $\beta_A$ on $A$ and $\beta_B$ on $B$, the behaviour strategy $\beta_A\otimes\beta_B$ on $A\otimes B$ answers in the component of the last move.
--
--   - If the last move is in $A$, it draws from $\beta_A(s{\restriction}A)$ and embeds the result in the left component.
--   - If the last move is in $B$, it does the same with $\beta_B(s{\restriction}B)$ in the right component.
--   - At the empty play it chooses $\mathrm{none}$.
--
--   The file proves that this satisfies the legality conditions of a behaviour strategy.
--
--   The file also defines two conditions:
--
--   1. $\beta$ is **never-stopping** if, at every position where Player is to move, $\mathrm{none}$ has probability $0$;
--   2. a game is **open to Opponent** if, at every position where Player is not to move, every Opponent move extends it to a position.
--
--   These are the hypotheses of the randomised tensor milestone.
-- source:
--   S. Abramsky, R. Jagadeesan, Games and full completeness for multiplicative linear logic, J. Symbolic Logic 59(2) (1994) 543-574, https://arxiv.org/abs/1311.6057, §3.3 (tensor of strategies), here for behaviour strategies in the sense of H. W. Kuhn, Extensive games and the problem of information, Contributions to the Theory of Games II, Annals of Mathematics Studies 28 (1953) 193-216

import Mathlib
import Definitions.Def_AJGames_Behaviour

/-!
# Tensor of behaviour strategies

Two behaviour strategies played side by side in `A ⊗ B` (Abramsky and Jagadeesan,
J. Symbolic Logic 59(2), 1994, §3.3, tensor of strategies, here for Kuhn behaviour strategies). In
`A ⊗ B` only Opponent switches component, so Player always answers in the component of the last
move, using that component's strategy on the restriction of the play to it.

Also: `NonStop` (the strategy never chooses `none` when Player is to move at a position) and
`OpenToOpponent` (Opponent may always play any of its moves when it is Opponent's turn).
-/

namespace AJGames

universe u

open scoped ENNReal

variable {A B : Game.{u}}

/-- `β` never stops: at every position where Player is to move, `none` has probability `0`. -/
def BehStrategy.NonStop (β : BehStrategy A) : Prop :=
  ∀ s ∈ A.pos, PlayerToMove A s → β.next s none = 0

/-- Opponent may always play any of its moves when it is Opponent's turn. -/
def OpenToOpponent (A : Game.{u}) : Prop :=
  ∀ s ∈ A.pos, ¬ PlayerToMove A s → ∀ m, A.lab m = Pl.O → s ++ [m] ∈ A.pos

/-- Next-move distribution of `βA ⊗ βB`: answer in the component of the last move. -/
noncomputable def tensorBNext (βA : BehStrategy A) (βB : BehStrategy B) (s : List (A.M ⊕ B.M)) :
    PMF (Option (A.M ⊕ B.M)) :=
  match s.getLast? with
  | some (Sum.inl _) => (βA.next (projL s)).map (Option.map Sum.inl)
  | some (Sum.inr _) => (βB.next (projR s)).map (Option.map Sum.inr)
  | none => PMF.pure none

theorem getLast_projL_of_inl {s : List (A.M ⊕ B.M)} {m : A.M} (h : s.getLast? = some (Sum.inl m)) :
    (projL s).getLast? = some m := by
  obtain ⟨t, rfl⟩ : ∃ t, s = t ++ [Sum.inl m] := List.getLast?_eq_some_iff.1 h
  simp [projL_snoc_inl]

theorem getLast_projR_of_inr {s : List (A.M ⊕ B.M)} {m : B.M} (h : s.getLast? = some (Sum.inr m)) :
    (projR s).getLast? = some m := by
  obtain ⟨t, rfl⟩ : ∃ t, s = t ++ [Sum.inr m] := List.getLast?_eq_some_iff.1 h
  simp [projR_snoc_inr]

theorem tensorBNext_legal (βA : BehStrategy A) (βB : BehStrategy B) (s : List (A.M ⊕ B.M))
    (a : A.M ⊕ B.M) (ha : tensorBNext βA βB s (some a) ≠ 0) :
    PlayerToMove (Game.tensor A B) s ∧ (Game.tensor A B).lab a = Pl.P ∧
      (s ∈ (Game.tensor A B).pos → s ++ [a] ∈ (Game.tensor A B).pos) := by
  unfold tensorBNext at ha
  cases hl : s.getLast? with
  | none => simp [hl] at ha
  | some m =>
    cases m with
    | inl m =>
      rw [hl] at ha
      obtain ⟨o, ho, hoa⟩ := (PMF.mem_support_map_iff _ _ _).1 ((PMF.mem_support_iff _ _).2 ha)
      obtain ⟨x, rfl⟩ : ∃ x, o = some x := by
        cases o with
        | none => simp at hoa
        | some x => exact ⟨x, rfl⟩
      simp only [Option.map_some, Option.some.injEq] at hoa
      subst hoa
      obtain ⟨⟨m', hm', hO⟩, hP, hext⟩ := βA.legal _ x ((PMF.mem_support_iff _ _).1 ho)
      rw [getLast_projL_of_inl hl] at hm'
      cases hm'
      refine ⟨⟨Sum.inl m, hl, hO⟩, hP, fun hs => ⟨?_, ?_, ?_⟩⟩
      · show List.IsChain _ (s ++ [Sum.inl x])
        rw [List.isChain_append]
        refine ⟨hs.1, List.isChain_singleton _, ?_⟩
        intro y hy z hz
        rw [hl] at hy
        simp at hy hz
        subst hy; subst hz
        refine ⟨?_, Or.inl rfl⟩
        show A.lab m ≠ A.lab x
        rw [hO, hP]; decide
      · rw [projL_snoc_inl]; exact hext hs.2.1
      · rw [projR_snoc_inl]; exact hs.2.2
    | inr m =>
      rw [hl] at ha
      obtain ⟨o, ho, hoa⟩ := (PMF.mem_support_map_iff _ _ _).1 ((PMF.mem_support_iff _ _).2 ha)
      obtain ⟨x, rfl⟩ : ∃ x, o = some x := by
        cases o with
        | none => simp at hoa
        | some x => exact ⟨x, rfl⟩
      simp only [Option.map_some, Option.some.injEq] at hoa
      subst hoa
      obtain ⟨⟨m', hm', hO⟩, hP, hext⟩ := βB.legal _ x ((PMF.mem_support_iff _ _).1 ho)
      rw [getLast_projR_of_inr hl] at hm'
      cases hm'
      refine ⟨⟨Sum.inr m, hl, hO⟩, hP, fun hs => ⟨?_, ?_, ?_⟩⟩
      · show List.IsChain _ (s ++ [Sum.inr x])
        rw [List.isChain_append]
        refine ⟨hs.1, List.isChain_singleton _, ?_⟩
        intro y hy z hz
        rw [hl] at hy
        simp at hy hz
        subst hy; subst hz
        refine ⟨?_, Or.inl rfl⟩
        show B.lab m ≠ B.lab x
        rw [hO, hP]; decide
      · rw [projL_snoc_inr]; exact hs.2.1
      · rw [projR_snoc_inr]; exact hext hs.2.2

/-- The tensor `βA ⊗ βB` of behaviour strategies. -/
noncomputable def tensorB (βA : BehStrategy A) (βB : BehStrategy B) :
    BehStrategy (Game.tensor A B) where
  next := tensorBNext βA βB
  legal := tensorBNext_legal βA βB

end AJGames


