-- Prove2me | Definitions.Def_qpr_alphabet_relabelling
-- name    : qpr_alphabet_relabelling
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-08-12T02:04:42.434284+00:00
-- url     : https://prove2.me/theorems/59133843-6fa3-40c7-b514-fff2d4053353
-- title:
--   Alphabet relabelling for entangled games
-- statement:
--   Transport of a two-player game, and of a strategy for it, along equivalences of the question and answer alphabets.
--
--   Given a game $G$ with alphabets $X, Y, A, B$ and equivalences $e_X : X \simeq X'$, $e_Y : Y \simeq Y'$, $e_A : A \simeq A'$, $e_B : B \simeq B'$, the relabelled game assigns the question pair $(x', y')$ the weight $G$ gave $(e_X^{-1}x', e_Y^{-1}y')$ and accepts $(a', b')$ exactly when $G$ accepted the corresponding preimages. A strategy transports the same way: it keeps its local systems and its shared state, and precomposes its measurement families with the equivalences, so the POVM conditions carry over by reindexing a finite sum.
--
--   The point of the construction is universe-lowering. A parallel-repetition theorem proved for alphabets in `Type` applies verbatim to arbitrary finite alphabets once one knows every finite type is equivalent to $\mathrm{Fin}\,|{\cdot}|$, which lives in `Type`.
--
--   The transport of a strategy needs no compatibility hypothesis between the two games, because a strategy never mentions the game it plays: the game argument of `Strategy` is a phantom parameter. A single transport therefore serves both directions of the resulting equality of entangled values, and no extensionality principle for games is required.
-- source:
--   Prove2me bridge for openai/ten-proofs, QuantumParallelRepetition.lean, https://github.com/openai/ten-proofs — universe transport, not part of the upstream development (which states parallel repetition for alphabets in `Type` only).

import Definitions.Def_quantum_parallel_repetition_game
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Logic.Equiv.Fin.Basic

/-!
# Alphabet relabelling for entangled games

Transport of a game, and of a strategy for it, along equivalences of the question and answer
alphabets.  This is the interface that lets a parallel-repetition theorem proved for alphabets
in `Type` be applied to alphabets in an arbitrary universe: every finite alphabet is equivalent
to `Fin (Fintype.card ·)`, which lives in `Type`.

The structural point is that `Strategy`'s game argument is a *phantom* parameter — a strategy is
a choice of local systems, a state, and measurements indexed by the alphabets, and it never
mentions the game.  A single transport therefore serves both directions of the induced equality
of entangled values, and no extensionality principle for `Game` is needed.
-/

namespace QuantumParallelRepetition

noncomputable section

open scoped BigOperators

variable {X Y A B X' Y' A' B' : Type*}
variable [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
variable [Fintype X'] [Fintype Y'] [Fintype A'] [Fintype B']

/-- Relabel the question and answer alphabets of a game along equivalences. -/
def Game.relabel (G : Game X Y A B) (eX : X ≃ X') (eY : Y ≃ Y') (eA : A ≃ A') (eB : B ≃ B') :
    Game X' Y' A' B' where
  questionWeight x' y' := G.questionWeight (eX.symm x') (eY.symm y')
  weight_nonneg _ _ := G.weight_nonneg _ _
  weight_normalized := by
    rw [← G.weight_normalized]
    refine (Fintype.sum_equiv eX _ _ fun x => ?_).symm
    exact Fintype.sum_equiv eY _ _ fun _ => by simp
  predicate x' y' a' b' :=
    G.predicate (eX.symm x') (eY.symm y') (eA.symm a') (eB.symm b')

@[simp] theorem Game.relabel_questionWeight (G : Game X Y A B)
    (eX : X ≃ X') (eY : Y ≃ Y') (eA : A ≃ A') (eB : B ≃ B') (x' : X') (y' : Y') :
    (G.relabel eX eY eA eB).questionWeight x' y' =
      G.questionWeight (eX.symm x') (eY.symm y') := rfl

@[simp] theorem Game.relabel_predicate (G : Game X Y A B)
    (eX : X ≃ X') (eY : Y ≃ Y') (eA : A ≃ A') (eB : B ≃ B')
    (x' : X') (y' : Y') (a' : A') (b' : B') :
    (G.relabel eX eY eA eB).predicate x' y' a' b' =
      G.predicate (eX.symm x') (eY.symm y') (eA.symm a') (eB.symm b') := rfl

/-- Transport a strategy along equivalences of the alphabets.  The target game `H` is
unconstrained because `Strategy`'s game argument is phantom; the hypotheses relating `H` to `G`
are needed only for the winning probability. -/
def Strategy.relabel {G : Game X Y A B} {H : Game X' Y' A' B'} (S : Strategy G)
    (eX : X ≃ X') (eY : Y ≃ Y') (eA : A ≃ A') (eB : B ≃ B') : Strategy H where
  Alice := S.Alice
  Bob := S.Bob
  state := S.state
  aliceMeasurement x' :=
    { operator := fun a' => (S.aliceMeasurement (eX.symm x')).operator (eA.symm a')
      positive := fun a' => (S.aliceMeasurement (eX.symm x')).positive _
      complete := by
        rw [← (S.aliceMeasurement (eX.symm x')).complete]
        exact Fintype.sum_equiv eA.symm _ _ fun _ => rfl }
  bobMeasurement y' :=
    { operator := fun b' => (S.bobMeasurement (eY.symm y')).operator (eB.symm b')
      positive := fun b' => (S.bobMeasurement (eY.symm y')).positive _
      complete := by
        rw [← (S.bobMeasurement (eY.symm y')).complete]
        exact Fintype.sum_equiv eB.symm _ _ fun _ => rfl }

end

end QuantumParallelRepetition


