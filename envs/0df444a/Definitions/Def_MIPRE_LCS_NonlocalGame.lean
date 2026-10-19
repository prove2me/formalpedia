-- Prove2me | Definitions.Def_MIPRE_LCS_NonlocalGame
-- name    : MIPRE_LCS_NonlocalGame
-- status  : Definition
-- author  : @thomasvidick
-- created : 2026-10-17T00:56:46.452535+00:00
-- url     : https://prove2.me/theorems/0a36b7cd-dee2-4c5b-9618-2cf2d3e26736
-- title:
--   Definitions of NonlocalGame: The nonlocal game of a linear constraint system This file interprets an LCS instance (`MIPRE.LCS.Game`) as a two-player…
-- statement:
--   The definitions of the module `MIPRE.LCS.NonlocalGame` of the MIP\* = RE formalization (commit `70cbf1c` of vidick/MIPRE-formalization). The nonlocal game of a linear constraint system. This file interprets an LCS instance (`MIPRE.LCS.Game`) as a two-player one-round nonlocal game in the sense of `MIPRE.Game`, connecting the operator-algebraic perfect-play formalism of `MIPRE.LCS` with the game-value framework of `MIPRE.Foundations.Games`.
--
--   **Definitions** (5): `MIPRE.LCS.Game.accepts` (The decider: the answer shapes must match the questions, the incidence must be on support, the assignment must satisfy its equation, and it…); `MIPRE.LCS.Game.toNonlocalGame` (**The nonlocal game of an LCS instance.** The referee samples an incidence `(i, j)` with `j ∈ G.V i` and a uniform orientation; the player…); `MIPRE.LCS.Layout.Answer` (An answer: an assignment to all the variables (`inl`), which is what an equation question is answered with, or a single bit (`inr`), which…); `MIPRE.LCS.Layout.Question` (A question of the LCS game: an equation (`inl`) or a variable (`inr`).); `MIPRE.LCS.Layout.questionDist` (The oriented-incidence distribution: an incidence `(i, j)` with `j ∈ G.V i`, then a uniform orientation.).
--
--   **Embedded lemmas** (9): the small results the bodies of these definitions need (proof fields, `simp` rules, decidability and finiteness instances), proved inside the bundle so that it imports no unproved statement: `accepts_inl_inr_of_inl`, `accepts_inl_inr_of_inr`, `accepts_same_kind_left`, `accepts_same_kind_right`, `toNonlocalGame_D`, `toNonlocalGame_μ`, `questionDist_nonneg`, `sum_questionDist`, `sum_questionDist_inl`.
--
--   **Formalization Note** The bundle is the module `MIPRE.LCS.NonlocalGame` (`MIPRE/LCS/NonlocalGame.lean`) with every declaration not listed removed, imports rewritten to the bundles of the module's import closure; the declarations keep their names, statements and bodies; the source module is split over 12 imported bundle(s).
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/LCS/NonlocalGame.lean; blueprint def:lcs-game

/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/LCS/NonlocalGame.lean (definition bundle: declarations the uploaded statements rest on);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/
import Mathlib.Algebra.Algebra.Basic
import Mathlib.Algebra.Module.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Star.Basic
import Mathlib.Algebra.Star.Module
import Mathlib.Analysis.CStarAlgebra.CStarMatrix
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Order
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.RCLike.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.Data.ENat.Lattice
import Mathlib.Data.Finset.Sum
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.LinearAlgebra.Matrix.ConjTranspose
import Mathlib.LinearAlgebra.Matrix.DotProduct
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Order.Fin.Basic
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Module
import Mathlib.Tactic.Ring
import Definitions.Def_MIPRE_Foundations_Games
import Definitions.Def_MIPRE_Foundations_Distances
import Definitions.Def_MIPRE_Foundations_POVMValue
import Definitions.Def_MIPRE_Foundations_PVM
import Definitions.Def_MIPRE_Foundations_PVM_B
import Definitions.Def_MIPRE_Foundations_RegisterReindex
import Definitions.Def_MIPRE_Foundations_RegisterReindex_B
import Definitions.Def_MIPRE_LCS_Basic
import Definitions.Def_MIPRE_LCS_Common
import Definitions.Def_MIPRE_LCS_Measurement
import Definitions.Def_MIPRE_LCS_Observable
import Definitions.Def_MIPRE_LCS_Strategy_ObservableToProjector

/-!
# The nonlocal game of a linear constraint system

This file interprets an LCS instance (`MIPRE.LCS.Game`) as a two-player one-round
nonlocal game in the sense of `MIPRE.Game`, connecting the operator-algebraic
perfect-play formalism of `MIPRE.LCS` with the game-value framework of
`MIPRE.Foundations.Games`.

## The game is symmetric in the players

Both players receive questions from the same alphabet `Fin G.r ⊕ Fin G.s` --- an equation
or a variable --- and answer in the same alphabet `(Fin G.s → ZMod 2) ⊕ ZMod 2` --- an
assignment or a bit. The referee samples an incidence `(i, j)` with `j ∈ G.V i` and then a
uniform *orientation*: one player is asked the equation and the other the variable. So there
are `2 r |V i|`-many equiprobable oriented pairs, and both players have measurements at both
kinds of question.

That is deliberate, and it is what the literature's `game^MS` means. An earlier version of
this file sent the equation to Alice and the variable to Bob always. Nothing in the repository
depended on that choice, and it made statements about *both* players' variable observables ---
which is what the Pauli basis test consumes from the Magic Square, blueprint
`lem:ms-direct-anticomm` --- inexpressible: Alice never received a variable question, so
`A^{Variable_j}` did not exist. The orientation also fixes the constant of that lemma: the sum
of the conditional failures over the oriented incidences is `2 r |V i|` times the failure
probability rather than `r |V i|` times it.

## The decider checks the shape

`Game.accepts` rejects an answer whose shape does not match its question, and rejects an
off-support pair `(i, j)` with `j ∉ G.V i`. Neither check is redundant with the question
distribution vanishing there. `reports/clgame-format-check-missing.md` records what a missing
format check cost the seeded CL game: the test became vacuous and a soundness theorem about it
false. The `accepts_*` simp lemmas below and the
`decide`-checked witnesses in `MIPRE/LCS/MagicSquare/Game.lean` --- an accepted pair in each
orientation, and one rejected for each of the three reasons --- are the guard against a
repeat.

## Main definitions

- `MIPRE.LCS.Layout.Question`, `MIPRE.LCS.Layout.Answer`: the shared question and answer
  alphabets;
- `MIPRE.LCS.Layout.questionDist`: the oriented-incidence distribution;
- `MIPRE.LCS.Game.accepts`: the decider;
- `MIPRE.LCS.Game.toNonlocalGame`: the nonlocal game of an LCS instance.

## Main statements

- `MIPRE.LCS.exists_tensorStrategy_value_eq_one_of_localLoss_annihilates_epr`:
  a bipartite observable strategy whose local loss operators annihilate the
  (unnormalized) EPR vector yields a perfect tensor-product strategy for the
  associated nonlocal game.
-/

namespace MIPRE.LCS

open Matrix
open scoped Kronecker

variable {G : Layout}

/-! ## The alphabets -/

/-- A question of the LCS game: an equation (`inl`) or a variable (`inr`). Both players
receive questions from this alphabet. -/
abbrev Layout.Question (G : Layout) : Type := Fin G.r ⊕ Fin G.s

/-- An answer: an assignment to all the variables (`inl`), which is what an equation question
is answered with, or a single bit (`inr`), which is what a variable question is answered with.
The decider rejects the shape that does not match the question, so the two are not
interchangeable --- a player who answers a variable question with an assignment loses. -/
abbrev Layout.Answer (G : Layout) : Type := (Fin G.s → ZMod 2) ⊕ ZMod 2

/-! ## The question distribution -/

/-- The oriented-incidence distribution: an incidence `(i, j)` with `j ∈ G.V i`, then a
uniform orientation. Each of the `2 ∑_i |V i|` oriented pairs has probability
`1 / (2 r |V i|)`. -/
noncomputable def Layout.questionDist (G : Layout) : G.Question → G.Question → ℝ
  | .inl i, .inr j => if j ∈ G.V i then 1 / (2 * (G.r : ℝ) * ((G.V i).card : ℝ)) else 0
  | .inr j, .inl i => if j ∈ G.V i then 1 / (2 * (G.r : ℝ) * ((G.V i).card : ℝ)) else 0
  | _, _ => 0

theorem Layout.questionDist_nonneg (G : Layout) (x y : G.Question) :
    0 ≤ G.questionDist x y := by
  cases x <;> cases y <;> simp only [questionDist] <;>
    first
      | exact le_refl 0
      | (split_ifs <;> positivity)

/-- One player's row sums to `1 / (2 r)` at an equation question: the variable is uniform in
the equation's support and the orientation costs the factor two. -/
theorem Layout.sum_questionDist_inl (hr : 0 < G.r) (hV : ∀ i, (G.V i).Nonempty)
    (i : Fin G.r) : ∑ y : G.Question, G.questionDist (.inl i) y = 1 / (2 * (G.r : ℝ)) := by
  classical
  have hr' : ((G.r : ℝ)) ≠ 0 := by exact_mod_cast hr.ne'
  have hcard : (((G.V i).card : ℝ)) ≠ 0 := by exact_mod_cast (hV i).card_pos.ne'
  rw [Fintype.sum_sum_type]
  have hleft : ∑ _i' : Fin G.r, G.questionDist (.inl i) (.inl _i') = 0 := by
    simp [Layout.questionDist]
  rw [hleft, zero_add]
  have hright : ∑ j : Fin G.s, G.questionDist (.inl i) (.inr j)
      = ∑ j : Fin G.s, (if j ∈ G.V i then 1 / (2 * (G.r : ℝ) * ((G.V i).card : ℝ)) else 0) :=
    rfl
  rw [hright, Finset.sum_ite_mem, Finset.univ_inter, Finset.sum_const, nsmul_eq_mul]
  field_simp

theorem Layout.sum_questionDist (hr : 0 < G.r) (hV : ∀ i, (G.V i).Nonempty) :
    ∑ x : G.Question, ∑ y : G.Question, G.questionDist x y = 1 := by
  classical
  have hr' : ((G.r : ℝ)) ≠ 0 := by exact_mod_cast hr.ne'
  rw [Fintype.sum_sum_type]
  -- the equation rows
  have hL : ∑ i : Fin G.r, ∑ y : G.Question, G.questionDist (.inl i) y = 1 / 2 := by
    rw [Finset.sum_congr rfl fun i (_ : i ∈ Finset.univ) =>
      Layout.sum_questionDist_inl hr hV i, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul]
    field_simp
  -- the variable rows: the same mass, summed in the other order
  have hR : ∑ j : Fin G.s, ∑ y : G.Question, G.questionDist (.inr j) y = 1 / 2 := by
    have hrow : ∀ j : Fin G.s, ∑ y : G.Question, G.questionDist (.inr j) y
        = ∑ i : Fin G.r,
            (if j ∈ G.V i then 1 / (2 * (G.r : ℝ) * ((G.V i).card : ℝ)) else 0) := by
      intro j
      rw [Fintype.sum_sum_type]
      have hz : ∑ _j' : Fin G.s, G.questionDist (.inr j) (.inr _j') = 0 := by
        simp [Layout.questionDist]
      rw [hz, add_zero]
      rfl
    have hcol : ∀ i : Fin G.r,
        ∑ j : Fin G.s, (if j ∈ G.V i then 1 / (2 * (G.r : ℝ) * ((G.V i).card : ℝ)) else 0)
          = 1 / (2 * (G.r : ℝ)) := by
      intro i
      have hcard : (((G.V i).card : ℝ)) ≠ 0 := by exact_mod_cast (hV i).card_pos.ne'
      rw [Finset.sum_ite_mem, Finset.univ_inter, Finset.sum_const, nsmul_eq_mul]
      field_simp
    rw [Finset.sum_congr rfl fun j (_ : j ∈ Finset.univ) => hrow j, Finset.sum_comm,
      Finset.sum_congr rfl fun i (_ : i ∈ Finset.univ) => hcol i, Finset.sum_const,
      Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    field_simp
  rw [hL, hR]
  norm_num

/-! ## The decider -/

/-- The decider: the answer shapes must match the questions, the incidence must be on
support, the assignment must satisfy its equation, and it must agree with the other player's
bit at his variable. Every other combination is rejected. -/
def Game.accepts (game : Game G) : G.Question → G.Question → G.Answer → G.Answer → Bool
  | .inl i, .inr j, .inl a, .inr v =>
      decide (j ∈ G.V i) && decide ((∑ k ∈ G.V i, a k) = game.b i) && decide (a j = v)
  | .inr j, .inl i, .inr v, .inl a =>
      decide (j ∈ G.V i) && decide ((∑ k ∈ G.V i, a k) = game.b i) && decide (a j = v)
  | _, _, _, _ => false

/-- **The decider rejects a mismatched shape.** Answering an equation question with a bit, or
a variable question with an assignment, loses --- whatever the other player does. -/
@[simp] theorem Game.accepts_inl_inr_of_inr (game : Game G) (i : Fin G.r) (j : Fin G.s)
    (v : ZMod 2) (c : G.Answer) : game.accepts (.inl i) (.inr j) (.inr v) c = false := by
  cases c <;> rfl

@[simp] theorem Game.accepts_inl_inr_of_inl (game : Game G) (i : Fin G.r) (j : Fin G.s)
    (a b : Fin G.s → ZMod 2) : game.accepts (.inl i) (.inr j) (.inl a) (.inl b) = false := rfl

@[simp] theorem Game.accepts_same_kind_left (game : Game G) (i i' : Fin G.r)
    (c d : G.Answer) : game.accepts (.inl i) (.inl i') c d = false := by
  cases c <;> cases d <;> rfl

@[simp] theorem Game.accepts_same_kind_right (game : Game G) (j j' : Fin G.s)
    (c d : G.Answer) : game.accepts (.inr j) (.inr j') c d = false := by
  cases c <;> cases d <;> rfl

/-! ## The symmetry between the players

The orientation is sampled uniformly and the decider reads the two sides symmetrically, so
exchanging the players is an automorphism of the game. This is what lets a one-sided soundness
statement be applied twice --- as blueprint `lem:ms-direct-anticomm` does, whose Alice half is
its Bob half for the swapped strategy. -/

/-! ## The game -/

/-- **The nonlocal game of an LCS instance.** The referee samples an incidence `(i, j)` with
`j ∈ G.V i` and a uniform orientation; the player who receives the equation answers an
assignment (only its restriction to `G.V i` is read), the player who receives the variable
answers a bit, and they win if the assignment satisfies the equation and agrees with the bit.
The hypotheses `hr` and `hV` are what make `questionDist` a probability distribution.

Blueprint `def:lcs-game`. -/
noncomputable def Game.toNonlocalGame (game : Game G)
    (hr : 0 < G.r) (hV : ∀ i, (G.V i).Nonempty) :
    MIPRE.Game G.Question G.Question G.Answer G.Answer where
  μ := G.questionDist
  μ_nonneg := G.questionDist_nonneg
  μ_sum_one := Layout.sum_questionDist hr hV
  D := game.accepts

@[simp] theorem Game.toNonlocalGame_μ (game : Game G) (hr : 0 < G.r)
    (hV : ∀ i, (G.V i).Nonempty) (x y : G.Question) :
    (game.toNonlocalGame hr hV).μ x y = G.questionDist x y := rfl

@[simp] theorem Game.toNonlocalGame_D (game : Game G) (hr : 0 < G.r)
    (hV : ∀ i, (G.V i).Nonempty) (x y : G.Question) (c d : G.Answer) :
    (game.toNonlocalGame hr hV).D x y c d = game.accepts x y c d := rfl

/-! ## Perfect strategies from operator solutions -/

section Perfect

variable {G : Layout} {n : Type*} [Fintype n] [DecidableEq n]

namespace BipartiteObservableStrategy

end BipartiteObservableStrategy

/-! ## Kronecker products of sums -/

/-! ## The normalized EPR state -/

section EPRState

variable (n)

end EPRState

/-! ## The measurements of the perfect strategy -/

namespace BipartiteObservableStrategy

end BipartiteObservableStrategy

/-! ## The accepted probability as one quadratic form -/

namespace BipartiteObservableStrategy

end BipartiteObservableStrategy

end Perfect

end MIPRE.LCS


