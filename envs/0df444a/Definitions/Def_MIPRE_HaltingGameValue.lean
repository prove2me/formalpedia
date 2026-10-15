-- Prove2me | Definitions.Def_MIPRE_HaltingGameValue
-- name    : MIPRE_HaltingGameValue
-- status  : Definition
-- author  : @thomasvidick
-- created : 2026-10-15T08:29:39.382979+00:00
-- url     : https://prove2.me/theorems/e13c860d-1e46-4a0a-94b2-1db2266f64bb
-- title:
--   Synchronous games, strategies and value; game descriptions; halting: the Mathlib-only statement surface of MIP* = RE
-- statement:
--   The definitions from which the main theorem of "MIP\* = RE" (Ji, Natarajan, Vidick, Wright, Yuen, arXiv:2001.04383, Theorem 12.2) is stated, written from scratch over Mathlib: elementary linear algebra and computability, and nothing from the rest of the formalization.
--
--   1. **POVM.** For a finite index set $X$ and a finite dimension index $d$, a POVM is a family $(E_x)_{x \in X}$ of self-adjoint complex $d \times d$ matrices that are positive semidefinite (nonnegative in the Loewner order) and sum to the identity.
--
--   2. **Synchronous game.** A synchronous game on a finite question alphabet $X$ and a finite answer alphabet $A$ consists of a probability distribution $\mu$ on $X \times X$ (nonnegative weights summing to one) and a decision predicate $D : X \times X \times A \times A \to \{\text{accept}, \text{reject}\}$ such that on equal questions $x = y$ every pair of unequal answers $a \ne b$ is rejected.
--
--   3. **Synchronous strategy.** A synchronous strategy for such a game is a dimension $d \ge 1$ together with, for every question $x$, a POVM $(M^x_a)_{a \in A}$ on $\mathbb{C}^d$ each of whose elements is idempotent, $M^x_a M^x_a = M^x_a$, that is, a projective measurement. Measurements for different questions need not commute. There is no state vector: outcome probabilities are computed in the normalized trace $\tau(M) = \operatorname{Tr}(M)/d$.
--
--   4. **Strategy value and synchronous value.** The value of a strategy is
--   $$
--   \omega(G, M) = \sum_{x, y} \sum_{a, b} \mu(x, y)\, D(x, y, a, b)\, \frac{\operatorname{Re}\operatorname{Tr}\bigl(M^x_a M^y_b\bigr)}{d},
--   $$
--   the probability that the players, measuring the shared maximally entangled state of dimension $d$ with the same measurements, give accepted answers. The synchronous value $\omega_{\mathrm{s}}(G)$ is the supremum of $\omega(G, M)$ over all synchronous strategies of all dimensions.
--
--   5. **Game descriptions.** A game description is a tuple of two natural numbers $n_X, n_A$, a finite list of weighted question pairs $(x, y, w) \in \mathbb{N}^3$ and a finite list of accepted tuples $(x, y, a, b) \in \mathbb{N}^4$. Game descriptions are in computable bijection with such tuples, hence codable as natural numbers. The description is interpreted as the synchronous game on $X = \{0, \dots, n_X\}$ and $A = \{0, \dots, n_A\}$ whose question distribution is proportional to the listed weights, with the point mass at $(0, 0)$ when the total listed weight is zero so that the interpretation is total, and whose decision predicate accepts exactly the listed tuples except that unequal answers to equal questions are rejected.
--
--   6. **Halting.** A Turing machine is a Gödel number of a partial recursive function; it halts on the empty input when its value at $0$ is defined.
--
--   7. **The statement.** The proposition *halting reduces to the game value* asserts the existence of a computable map $g$ from machines to game descriptions such that, for every machine $c$, the game $G_{g(c)}$ has synchronous value $1$ if $c$ halts on the empty input and synchronous value at most $\tfrac12$ if it does not. This proposition is the goal theorem of the mission.
--
--   These definitions are the fixed interface of the mission: every milestone and every proof is stated against them, so that an auditor can check the goal from first principles without reading the rest of the development.
--
--   **Formalization Note** The file is `MIPRE/HaltingGameValue.lean` of https://github.com/vidick/MIPRE-formalization at commit `70cbf1c`, reproduced verbatim. Matrices are Mathlib matrices over $\mathbb{C}$ with the Loewner order (`MatrixOrder`); `POVM` matches the QuantumLib definition with `selfAdjoint (Matrix d d ℂ)` spelled out. Machines are `Nat.Partrec.Code`, computability is Mathlib's `Computable`, and `GameData` is `Primcodable` through its bijection with a tuple of naturals and lists. The real part of the trace is taken in the strategy value, and the synchronous value is Lean's `iSup` over strategies in $\mathbb{R}$. The normalization proof inside `GameData.toGame` is the only proof in the file.
-- source:
--   Z. Ji, A. Natarajan, T. Vidick, J. Wright, H. Yuen, MIP* = RE, arXiv:2001.04383 (2020, revised 2022): nonlocal games, synchronous games and strategies, the synchronous value, and the game descriptions of Theorem 12.2. Lean source, reproduced verbatim: https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/HaltingGameValue.lean (namespace HaltingGameValue: POVM, SynchronousGame, SyncStrategy, strategyValue, gameValue, GameData, GameData.toGame, HaltsOnEmptyInput, HaltingReducesToGameValue).

/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Prove2Me mission "MIP* = RE": definition bundle, the Mathlib-only statement surface of the main theorem.
   Taken verbatim from vidick/MIPRE-formalization@70cbf1c, MIPRE/HaltingGameValue.lean (Lean v4.33.0 / Mathlib db584cd,
   the parent of the platform's pin 0df444a); produced by prove2me/tools/mission_items.py, never edited by hand. -/
/-
# A self-contained statement of Theorem 12.2 of "MIP* = RE"

This file states the main result of the paper "MIP* = RE" (Ji, Natarajan,
Vidick, Wright, Yuen, arXiv:2001.04383), Theorem 12.2: there is a computable
map from Turing machines to nonlocal games that sends halting machines to
games of value 1 and non-halting machines to games of value at most 1/2.

All definitions are given from scratch on top of Mathlib only:

* `POVM`: positive operator-valued measures on a finite-dimensional space,
  represented as self-adjoint complex matrices that are nonnegative in the
  Loewner order. The definition matches the QuantumLib (Lean-QuantumInfo)
  `POVM`, with `selfAdjoint (Matrix d d ℂ)` spelled out for its definitionally
  equal `HermitianMat d ℂ`.
* `SynchronousGame`: two-player one-round synchronous games, where the two
  question sets and answer sets are identical and unequal answers lose on
  equal questions.
* `SyncStrategy`: synchronous strategies, i.e. a single question-indexed
  projective measurement family measured against the dimension-normalized
  trace (tracial) state `τ(M) = Tr(M)/d`.
* `gameValue`: the synchronous value of a game, the supremum of strategy
  values over all synchronous strategies.
* `GameData` / `GameData.toGame`: a codable (first-order) description of a
  game and its interpretation as a `SynchronousGame`, so that computability of
  the reduction can be expressed.

The model of computation is Mathlib's `Nat.Partrec.Code` (Gödel-numbered
partial recursive functions, equivalent to Turing machines); "the machine
halts on the empty input" is `(c.eval 0).Dom`, and computability of the
reduction is Mathlib's `Computable`.
-/

import Mathlib.Analysis.Matrix.Order
import Mathlib.Computability.PartrecCode

namespace HaltingGameValue

/- The Loewner order on matrices (`0 ≤ A ↔ A.PosSemidef`) is scoped. -/
open scoped MatrixOrder

/-! ## POVMs -/

/-- A POVM is a (finite) collection of PSD matrices on the same Hilbert space
that sum to the identity. Here `X` indexes the matrices, and `d` is the space
dimension.

This is the QuantumLib (Lean-QuantumInfo) definition of `POVM`, with
`selfAdjoint (Matrix d d ℂ)` spelled out for its definitionally equal
`HermitianMat d ℂ`; `0 ≤ mats x` is the Loewner order, i.e. positive
semidefiniteness. -/
structure POVM (X : Type*) (d : Type*) [Fintype X] [Fintype d] [DecidableEq d] where
  mats : X → selfAdjoint (Matrix d d ℂ)
  nonneg : ∀ x, 0 ≤ mats x
  normalized : ∑ x, mats x = 1

/-! ## Synchronous games -/

/-- A synchronous game: both players receive questions from the same alphabet
and answer from the same alphabet; on equal questions, unequal answers always
lose. -/
structure SynchronousGame (X A : Type*) [Fintype X] [Fintype A] [DecidableEq A] where
  μ : X → X → ℝ
  μ_nonneg : ∀ x y, 0 ≤ μ x y
  μ_sum_one : ∑ x, ∑ y, μ x y = 1
  D : X → X → A → A → Bool
  synchronous : ∀ x a b, a ≠ b → D x x a b = false

variable {X A : Type*} [Fintype X] [Fintype A] [DecidableEq A]

/-! ## Synchronous strategies -/

/-- A synchronous strategy for a synchronous game: a finite-dimensional
strategy with a single question-indexed projective measurement family. The
operators act on `ℂ^d` (`d > 0`); each measurement operator is idempotent,
hence (being positive semidefinite) an orthogonal projection. Measurements for
different questions need not commute. There is no state vector: outcome
probabilities are computed with the dimension-normalized trace
`τ(M) = Tr(M)/d` (see `strategyValue`). -/
structure SyncStrategy (G : SynchronousGame X A) where
  d : ℕ
  d_pos : 0 < d
  povm : X → POVM A (Fin d)
  projective : ∀ x a,
    ((povm x).mats a).val * ((povm x).mats a).val = ((povm x).mats a).val

/-! ## Game value -/

/-- The winning probability of a synchronous strategy: the players answer
questions `(x, y)` with `(a, b)` with probability `Tr(M^x_a M^y_b)/d`.
For positive semidefinite matrices this trace is a nonnegative real; we
take the real part so that the definition typechecks with no proof
obligations. -/
noncomputable def strategyValue (G : SynchronousGame X A) (S : SyncStrategy G) : ℝ :=
  ∑ x, ∑ y, ∑ a, ∑ b,
    G.μ x y * (if G.D x y a b then 1 else 0) *
      ((((S.povm x).mats a).val * ((S.povm y).mats b).val).trace.re / (S.d : ℝ))

/-- The synchronous value of a synchronous game: the supremum of winning
probabilities over all synchronous strategies. -/
noncomputable def gameValue (G : SynchronousGame X A) : ℝ :=
  ⨆ S : SyncStrategy G, strategyValue G S

/-! ## Codable game descriptions -/

/-- A first-order description of a synchronous game, suitable for computability
statements. The question alphabet is `Fin (nX + 1)` and the answer alphabet is
`Fin (nA + 1)`. The question
distribution is given by a finite list `w` of unnormalized natural-number
weights `(x, y, weight)`, and the decision predicate by the list `acc` of
accepted tuples `(x, y, a, b)`. -/
structure GameData where
  nX : ℕ
  nA : ℕ
  w : List (ℕ × ℕ × ℕ)
  acc : List (ℕ × ℕ × ℕ × ℕ)

namespace GameData

/-- `GameData` is just a tuple of naturals and lists. -/
def equivTuple : GameData ≃ ℕ × ℕ × List (ℕ × ℕ × ℕ) × List (ℕ × ℕ × ℕ × ℕ) where
  toFun g := (g.nX, g.nA, g.w, g.acc)
  invFun t := ⟨t.1, t.2.1, t.2.2.1, t.2.2.2⟩

instance : Primcodable GameData := Primcodable.ofEquiv _ equivTuple

/-- Total weight assigned by the list `w` to the question pair `(x, y)`. -/
def questionWeight (g : GameData) (x y : ℕ) : ℕ :=
  ((g.w.filter fun t => decide (t.1 = x ∧ t.2.1 = y)).map fun t => t.2.2).sum

/-- Total weight assigned by the list `w` to valid question pairs. -/
def totalWeight (g : GameData) : ℕ :=
  ∑ x : Fin (g.nX + 1), ∑ y : Fin (g.nX + 1), g.questionWeight x.val y.val

/-- Interpret a `GameData` as a `SynchronousGame`: normalize the question
weights (falling back to a point mass on `(0, 0)` when the total weight is
zero, so that the interpretation is total), and accept exactly the answer
tuples listed in `acc`, except that unequal answers on equal questions always
lose. -/
noncomputable def toGame (g : GameData) :
    SynchronousGame (Fin (g.nX + 1)) (Fin (g.nA + 1)) where
  μ x y :=
    if g.totalWeight = 0 then (if x = 0 ∧ y = 0 then 1 else 0)
    else (g.questionWeight x.val y.val : ℝ) / (g.totalWeight : ℝ)
  μ_nonneg x y := by
    split_ifs
    · norm_num
    · norm_num
    · positivity
  μ_sum_one := by
    by_cases h : g.totalWeight = 0
    · simp only [if_pos h]
      rw [Finset.sum_eq_single (0 : Fin (g.nX + 1))]
      · simp
      · intro b _ hb
        simp [hb]
      · intro hmem
        exact absurd (Finset.mem_univ _) hmem
    · simp only [if_neg h]
      have hT : (g.totalWeight : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr h
      have hsum : ∑ x : Fin (g.nX + 1), ∑ y : Fin (g.nX + 1),
          (g.questionWeight x.val y.val : ℝ) = (g.totalWeight : ℝ) := by
        unfold totalWeight
        push_cast
        rfl
      simp_rw [← Finset.sum_div]
      rw [hsum, div_self hT]
  D x y a b := if x = y ∧ a ≠ b then false else decide ((x.val, y.val, a.val, b.val) ∈ g.acc)
  synchronous x a b hne := by
    simp [hne]

end GameData

/-! ## The halting problem and Theorem 12.2 -/

/-- The program `c` halts on the empty input. (`Nat.Partrec.Code` is
Mathlib's Gödel numbering of partial recursive functions, an equivalent
model of computation to Turing machines; the empty input is encoded by
`0`.) -/
def HaltsOnEmptyInput (c : Nat.Partrec.Code) : Prop := (c.eval 0).Dom

/-- **Theorem 12.2 of "MIP* = RE"** (arXiv:2001.04383), stated with respect
to the synchronous game value and with "polynomial-time" relaxed to
"computable": there is a computable map from Turing machines to nonlocal
games such that

1. (completeness) if the machine halts on the empty input then the game has
   synchronous value `1`, and
2. (soundness) if the machine does not halt on the empty input then the
   synchronous value of the game is at most `1/2`.

This is the statement. Its proof, `HaltingGameValue.halting_reduces_to_gameValue` in
`MIPRE/MainTheorem.lean`, needs the whole formalization, so it cannot live in this file, which
imports Mathlib only; that file proves exactly this proposition. -/
def HaltingReducesToGameValue : Prop :=
  ∃ g : Nat.Partrec.Code → GameData, Computable g ∧
    ∀ c : Nat.Partrec.Code,
      (HaltsOnEmptyInput c → gameValue (g c).toGame = 1) ∧
      (¬HaltsOnEmptyInput c → gameValue (g c).toGame ≤ 1 / 2)

end HaltingGameValue


