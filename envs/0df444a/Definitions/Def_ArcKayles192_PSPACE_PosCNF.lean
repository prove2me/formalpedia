-- Prove2me | Definitions.Def_ArcKayles192_PSPACE_PosCNF
-- name    : ArcKayles192_PSPACE_PosCNF
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T08:58:23.310294+00:00
-- url     : https://prove2.me/theorems/8a674834-8610-4610-844c-6ad04d4f3711
-- title:
--   The Pos CNF game, its variant with passes and free truth values, and the encoding of Pos CNF instances
-- statement:
--   A **Pos CNF** instance is a formula $\varphi=C_1\wedge\cdots\wedge C_m$ over variables $x_1,\dots,x_n$ in which every clause $C_j$ is a set of positive literals, i.e. a set of variables. Empty and repeated clauses are allowed.
--
--   1. **Positions.** A position is a pair $(T,F)$ of sets of variables, those set to true and those set to false, together with the player to move. The unclaimed variables are those outside $T\cup F$. The play ends when every variable is claimed, and True wins iff every clause $C_j$ contains a variable of $T$.
--   2. **The Pos CNF game.** True and False alternate, and each move claims one unclaimed variable: True puts it into $T$, False into $F$. $\mathrm{TrueWins}(\varphi,T,F,\text{mover})$ is defined by backward induction on the number of unclaimed variables. True to move wins iff some claim leads to a position True wins; False to move loses iff every claim leads to a position True wins.
--   3. **The variant with pass budget $p$.** The player to move may pass, if $p>0$, which lowers $p$ by one and hands the move over. Or the player may claim any unclaimed variable and give it either truth value (put it into $T$ or into $F$). The play still ends as soon as every variable is claimed, and the final rule is the same. $\mathrm{TrueWinsVar}(\varphi,T,F,\text{mover},p)$ is defined by backward induction on the number of unclaimed variables plus $p$.
--   4. **The decision problem.** POS CNF asks whether $\mathrm{TrueWins}(\varphi,\emptyset,\emptyset,\text{True to move})$ holds, i.e. whether True, moving first, has a winning strategy. Instances are encoded as $1^n\,0\,1^m\,0$ followed by the $mn$ incidence bits "$x_i\in C_j$", clause by clause.
--
--   The game is the source of the reduction; the variant models the extra pass and either-value moves that the graph $G_\varphi$ offers.
--
--   **Formalization Note** The pass budget is shared by both players and finite. The paper's variant does not say who wins an infinite play of passes; the budget is how the passes of $G_\varphi$ arise, since that graph has finitely many pass edges, used by both players.
-- source:
--   Édouard Bonnet, Arc Kayles is PSPACE-complete, STOC 2027 submission #192 (October 2026), source.pdf SHA-256 f8b3a1c14347452b03dab2f19656aa6d2b17ba3956fefe2abc190b98ce44fc53, p.4 §2.2 (Pos CNF game, True first; outcome-equivalence; the variant of Lemma 5)

import Mathlib

namespace ArcKayles192.PSPACE

/-! # The Pos CNF game and its relaxed variant

A Pos CNF instance `φ = C₁ ∧ ⋯ ∧ C_m` over the variables `x₁, …, x_n` (here `Fin n`), each clause
`C_j` a set of positive literals, i.e. a set of variables (`Fin m → Finset (Fin n)`; empty and
repeated clauses are allowed). A position is a pair `(T, F)` of sets of variables: `T` the
variables set to true, `F` those set to false; the unclaimed variables are those outside `T ∪ F`.
The game ends when every variable is claimed; True wins iff every clause contains a variable of
`T`. -/

/-- A CNF formula with only positive literals: `m` clauses over `n` variables. -/
structure PosCNF : Type where
  /-- number of variables -/
  n : ℕ
  /-- number of clauses -/
  m : ℕ
  /-- the clause `C_j`, as the set of (indices of) its variables -/
  clause : Fin m → Finset (Fin n)

namespace PosCNF

/-- Claiming an unclaimed variable strictly decreases the number of unclaimed variables. -/
theorem card_unclaimed_lt {n : ℕ} {T F : Finset (Fin n)} {x : Fin n} (hx : x ∉ T ∪ F)
    (T' F' : Finset (Fin n)) (h : T' ∪ F' = insert x (T ∪ F)) :
    (Finset.univ \ (T' ∪ F')).card < (Finset.univ \ (T ∪ F)).card := by
  rw [h]
  apply Finset.card_lt_card
  refine ⟨Finset.sdiff_subset_sdiff (Finset.Subset.refl _) (Finset.subset_insert _ _), ?_⟩
  intro hsub
  have : x ∈ Finset.univ \ (T ∪ F) := by simp [hx]
  have := hsub this
  simp at this

/-- The final evaluation: True wins iff every clause contains a variable set to true. -/
def AllSatisfied (φ : PosCNF) (T : Finset (Fin φ.n)) : Prop :=
  ∀ j : Fin φ.m, ∃ x ∈ φ.clause j, x ∈ T

set_option linter.unusedVariables false in
/-- **The Pos CNF game** (normal Pos CNF rules). `TrueWins φ T F trueToMove` holds when True
has a winning strategy from the position where the variables of `T` have been claimed by True
(set to true), those of `F` by False (set to false), and `trueToMove` says whether True is to
move. The players alternate claiming one unclaimed variable each; True's claims are set to true
and False's to false. When every variable is claimed the game ends and True wins iff every clause
is satisfied. Defined by backward induction on the number of unclaimed variables. -/
def TrueWins (φ : PosCNF) (T F : Finset (Fin φ.n)) (trueToMove : Bool) : Prop :=
  if T ∪ F = Finset.univ then AllSatisfied φ T
  else if trueToMove then
    ∃ x, ∃ hx : x ∉ T ∪ F, TrueWins φ (insert x T) F false
  else
    ∀ x, ∀ hx : x ∉ T ∪ F, TrueWins φ T (insert x F) true
termination_by (Finset.univ \ (T ∪ F)).card
decreasing_by
  · exact card_unclaimed_lt hx _ _ (by rw [Finset.insert_union])
  · exact card_unclaimed_lt hx _ _ (by rw [Finset.union_insert])

set_option linter.unusedVariables false in
/-- **The relaxed variant** of Lemma 5, with a shared pass budget `p`. From the position `(T, F)`
with `trueToMove` saying who moves, the player to move may (a) pass, if `p > 0`, which uses one
unit of the budget and hands the move to the opponent, or (b) claim any unclaimed variable and
give it **either** truth value (put it into `T` or into `F`). When every variable is claimed the
game ends, whatever budget remains, and True wins iff every clause contains a variable of `T`.
Defined by backward induction on (unclaimed variables) + (remaining passes). -/
def TrueWinsVar (φ : PosCNF) (T F : Finset (Fin φ.n)) (trueToMove : Bool) (p : ℕ) : Prop :=
  if T ∪ F = Finset.univ then AllSatisfied φ T
  else if trueToMove then
    (∃ q, ∃ hq : p = q + 1, TrueWinsVar φ T F false q) ∨
    ∃ x, ∃ hx : x ∉ T ∪ F,
      (TrueWinsVar φ (insert x T) F false p ∨ TrueWinsVar φ T (insert x F) false p)
  else
    (∀ q, ∀ hq : p = q + 1, TrueWinsVar φ T F true q) ∧
    ∀ x, ∀ hx : x ∉ T ∪ F,
      (TrueWinsVar φ (insert x T) F true p ∧ TrueWinsVar φ T (insert x F) true p)
termination_by (Finset.univ \ (T ∪ F)).card + p
decreasing_by
  all_goals first
    | omega
    | (have := card_unclaimed_lt hx _ _ (by rw [Finset.insert_union]); omega)
    | (have := card_unclaimed_lt hx _ _ (by rw [Finset.union_insert]); omega)

/-- The binary encoding of a Pos CNF instance: `n` in unary, a separator `0`, `m` in unary, a
separator `0`, then the `m·n` incidence bits "`x_i ∈ C_j`", clause by clause (row-major in
`(j, i)`). -/
def enc (φ : PosCNF) : List Bool :=
  List.replicate φ.n true ++ [false] ++ List.replicate φ.m true ++ [false] ++
    (List.finRange φ.m).flatMap fun j =>
      (List.finRange φ.n).map fun i => decide (i ∈ φ.clause j)

end PosCNF

/-- The decision problem POS CNF: does True, moving first from the position where no variable is
claimed, have a winning strategy in the Pos CNF game on `φ`? -/
def posCNF (φ : PosCNF) : Prop :=
  PosCNF.TrueWins φ ∅ ∅ true

end ArcKayles192.PSPACE


