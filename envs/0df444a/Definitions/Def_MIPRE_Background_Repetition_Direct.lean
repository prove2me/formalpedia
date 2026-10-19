-- Prove2me | Definitions.Def_MIPRE_Background_Repetition_Direct
-- name    : MIPRE_Background_Repetition_Direct
-- status  : Definition
-- author  : @thomasvidick
-- created : 2026-10-16T14:37:18.355503+00:00
-- url     : https://prove2.me/theorems/370ff774-d2b8-4dbd-b01f-27881900fa8a
-- title:
--   Direct parallel repetition of a game and of a synchronous game
-- statement:
--   Let $G = (\mathcal X, \mathcal Y, \mathcal A, \mathcal B, \mu, D)$ be a two-player game with finite question alphabets $\mathcal X, \mathcal Y$, finite answer alphabets $\mathcal A, \mathcal B$, question distribution $\mu$ and decision predicate $D$, and let $n \geq 0$. This bundle holds the two definitions of the module `MIPRE.Background.Repetition.Direct`, both forms of blueprint `def:direct-repetition`.
--
--   `MIPRE.Game.repeat G n : Game (Fin n → X) (Fin n → Y) (Fin n → A) (Fin n → B)` is the $n$-fold direct repetition $G^{\otimes n}$: questions and answers are $n$-tuples, and
--
--   $$\mu^{n}(\bar x, \bar y) = \prod_{i < n} \mu(x_i, y_i), \qquad D^{n}(\bar x, \bar y, \bar a, \bar b) = \bigwedge_{i < n} D(x_i, y_i, a_i, b_i),$$
--
--   with the proof fields `μ_nonneg` and `μ_sum_one` that $\mu^n$ is a probability distribution. `MIPRE.SynchronousGame.repeat G n : SynchronousGame (Fin n → X) (Fin n → A)`, for `G : SynchronousGame X A` with `[DecidableEq A]`, has the same distribution and predicate and in addition the field `synchronous`: unequal answer tuples to equal question tuples differ in some coordinate, which `G` rejects. The bundle embeds no lemmas; the module's one theorem, `SynchronousGame.repeat_toGame` (the underlying game of the repeated synchronous game is the repetition of the underlying game, by `rfl`), is not part of it.
--
--   The construction is the one the vendored parallel repetition developments under `MIPRE/Background/Repetition/` use, so their theorems apply to `G.repeat n` without bookkeeping: `MIPRE.Repetition.quantumValue_repeat_le` (blueprint `thm:direct-repetition-q`) bounds `quantumValue (G.repeat n)`, and the game of the repeated verifier of `thm:parallel-repetition` is a `Game.repeat` up to relabeling (`MIPRE.valStar_repVerifier`).
--
--   **Formalization Note** A `Game X Y A B` has fields `μ : X → Y → ℝ`, `μ_nonneg`, `μ_sum_one : ∑ x, ∑ y, μ x y = 1` and `D : X → Y → A → B → Bool`; a `SynchronousGame X A` has one question and one answer alphabet and the extra field `synchronous : ∀ x a b, a ≠ b → D x x a b = false`. Tuples are functions out of `Fin n`, the product is `∏ i : Fin n`, and the predicate is `decide (∀ i : Fin n, G.D (xs i) (ys i) (as i) (bs i) = true)`, a `Bool`. No positivity of `n` is assumed: at `n = 0` the repeated game has a single question pair, of probability one, and accepts the single answer pair. The bundle imports one definition bundle, that of `MIPRE.Foundations.Games`.
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Background/Repetition/Direct.lean; blueprint def:direct-repetition

/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Background/Repetition/Direct.lean (definition bundle: declarations the uploaded statements rest on);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.GroupWithZero.Defs
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Algebra.Order.Ring.Defs
import Mathlib.Algebra.Ring.Defs
import Mathlib.Analysis.CStarAlgebra.CStarMatrix
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Matrix.Order
import Mathlib.Data.ENat.Lattice
import Mathlib.Data.Finset.Defs
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.Defs
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Real.Basic
import Mathlib.Data.SetLike.Basic
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.Order.Defs.PartialOrder
import Mathlib.Tactic
import Definitions.Def_MIPRE_Foundations_Games

/-!
# Direct parallel repetition of a game

The `n`-fold direct repetition `G^{⊗n}` of a game (blueprint `def:direct-repetition`):
the referee samples `n` independent question pairs, sends the tuples to the players, and
accepts if and only if every coordinate is accepted. The construction is that of the two
vendored developments (`MIPRE/Background/Repetition/`), so that their theorems transfer
without bookkeeping; the repetition of a synchronous game is synchronous.
-/

namespace MIPRE

open scoped BigOperators

variable {X Y A B : Type*} [Fintype X] [Fintype Y] [Fintype A] [Fintype B]

/-- The `n`-fold direct repetition of a game (blueprint `def:direct-repetition`):
product question distribution on `(Fin n → X) × (Fin n → Y)` and the conjunction of the
coordinate predicates. -/
def Game.repeat (G : Game X Y A B) (n : ℕ) :
    Game (Fin n → X) (Fin n → Y) (Fin n → A) (Fin n → B) where
  μ xs ys := ∏ i : Fin n, G.μ (xs i) (ys i)
  μ_nonneg xs ys := Finset.prod_nonneg fun i _ => G.μ_nonneg (xs i) (ys i)
  μ_sum_one := by
    classical
    calc
      (∑ xs : Fin n → X, ∑ ys : Fin n → Y, ∏ i : Fin n, G.μ (xs i) (ys i)) =
          ∑ xs : Fin n → X, ∏ i : Fin n, ∑ y : Y, G.μ (xs i) y := by
            apply Finset.sum_congr rfl
            intro xs _
            exact (Fintype.prod_sum (fun i : Fin n => fun y : Y => G.μ (xs i) y)).symm
      _ = ∏ _i : Fin n, ∑ x : X, ∑ y : Y, G.μ x y := by
            exact (Fintype.prod_sum
              (fun _i : Fin n => fun x : X => ∑ y : Y, G.μ x y)).symm
      _ = 1 := by simp [G.μ_sum_one]
  D xs ys as bs := decide (∀ i : Fin n, G.D (xs i) (ys i) (as i) (bs i) = true)

/-- The `n`-fold direct repetition of a synchronous game is synchronous: unequal answer
tuples to equal question tuples differ in some coordinate, which is then rejected. -/
def SynchronousGame.repeat [DecidableEq A] (G : SynchronousGame X A) (n : ℕ) :
    SynchronousGame (Fin n → X) (Fin n → A) where
  μ xs ys := ∏ i : Fin n, G.μ (xs i) (ys i)
  μ_nonneg xs ys := Finset.prod_nonneg fun i _ => G.μ_nonneg (xs i) (ys i)
  μ_sum_one := by
    classical
    calc
      (∑ xs : Fin n → X, ∑ ys : Fin n → X, ∏ i : Fin n, G.μ (xs i) (ys i)) =
          ∑ xs : Fin n → X, ∏ i : Fin n, ∑ y : X, G.μ (xs i) y := by
            apply Finset.sum_congr rfl
            intro xs _
            exact (Fintype.prod_sum (fun i : Fin n => fun y : X => G.μ (xs i) y)).symm
      _ = ∏ _i : Fin n, ∑ x : X, ∑ y : X, G.μ x y := by
            exact (Fintype.prod_sum
              (fun _i : Fin n => fun x : X => ∑ y : X, G.μ x y)).symm
      _ = 1 := by simp [G.μ_sum_one]
  D xs ys as bs := decide (∀ i : Fin n, G.D (xs i) (ys i) (as i) (bs i) = true)
  synchronous := by
    intro xs as bs hne
    rw [decide_eq_false_iff_not]
    intro h
    apply hne
    funext i
    by_contra hi
    have hfalse := G.synchronous (xs i) (as i) (bs i) hi
    rw [h i] at hfalse
    exact absurd hfalse (by simp)

end MIPRE


