-- Prove2me | Definitions.Def_MIPRE_Background_Repetition_TensorPower
-- name    : MIPRE_Background_Repetition_TensorPower
-- status  : Definition
-- author  : @thomasvidick
-- created : 2026-10-16T15:38:55.205232+00:00
-- url     : https://prove2.me/theorems/1523e4bc-e689-4ad8-a152-12556dc9e862
-- title:
--   Tensor powers of projective measurements and of synchronous strategies
-- statement:
--   Let `H : SynchronousGame X A` be a synchronous game and $k \geq 0$. A synchronous strategy `S : SyncStrategy H` is a dimension `d > 0` and a question-indexed family of projective measurements `P : ProjectiveMeasurement X A (Matrix (Fin d) (Fin d) ℂ)`. This bundle holds the five definitions of `MIPRE.Background.Repetition.TensorPower` that build the $k$-fold tensor power of such a strategy, a strategy for the direct repetition `H.repeat k` (blueprint `lem:tensor-power-pcc`).
--
--   Measurement families. `MIPRE.ProjectiveMeasurement.tensorPow P k` is the family on the repeated alphabets `Fin k → X`, `Fin k → A`, with operators on `Matrix (Fin k → Fin d) (Fin k → Fin d) ℂ`
--
--   $$M^{\bar x}_{\bar a} \;=\; \bigotimes_{i<k} M^{x_i}_{a_i}$$
--
--   (`MIPRE.tensorFamily fun i => P.M (x i) (a i)`), with the three measurement axioms. `MIPRE.ProjectiveMeasurement.reindexMat e P`, for `e : ι ≃ κ`, transports a family on `Matrix ι ι ℂ` to `Matrix κ κ ℂ` by `(P.M x a).submatrix e.symm e.symm`. `MIPRE.equivFinPow d k : (Fin k → Fin d) ≃ Fin (d ^ k)` renumbers the $k$-tuples.
--
--   Strategies. `MIPRE.SyncStrategy.tensorPow S k : SyncStrategy (H.repeat k)` has dimension `S.d ^ k` and measurements `(S.P.tensorPow k).reindexMat (equivFinPow S.d k)`. `MIPRE.SyncStrategy.tensorPowDoubled S k : SyncStrategy (G.repeat k).doubled`, for `S : SyncStrategy G.doubled` with `G : Game X X A A`, is `(S.tensorPow k).relabel` along the question map $(t, \bar x) \mapsto (i \mapsto (t, x_i))$ with the identity on answers: the tag is read on every coordinate.
--
--   The two embedded lemmas, `reindexMat_M` and `tensorPow_M`, are the `@[simp]` unfolding rules for the `M` fields, both by `rfl`. The module's theorems (`value_tensorPow`: `(S.tensorPow k).value = S.value ^ k`; `isPCC_tensorPow`; their doubled forms; and `exists_perfectPCC_repeat_doubled`, game-level completeness) are not part of this bundle.
--
--   **Formalization Note** `SyncStrategy` fixes the matrix type `Matrix (Fin d) (Fin d) ℂ`, so the tensor power on `Fin k → Fin d` is carried to `Fin (d ^ k)`; `equivFinPow` is `Fintype.equivFinOfCardEq (by simp)`, noncomputable, and `SyncStrategy.tensorPow` and `tensorPowDoubled` are noncomputable with it. `H.repeat k` is `MIPRE.SynchronousGame.repeat`; `G.doubled : SynchronousGame (Bool × X) A` tags Alice's questions `false` and Bob's `true`. `relabel` takes any map on questions, here `fun p i => (p.1, p.2 i)`, and an equivalence on answers, here `Equiv.refl _`.
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Background/Repetition/TensorPower.lean; blueprint lem:tensor-power-pcc

/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Background/Repetition/TensorPower.lean (definition bundle: declarations the uploaded statements rest on);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.Algebra.BigOperators.Pi
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.GroupWithZero.Defs
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Algebra.Order.Ring.Defs
import Mathlib.Algebra.Ring.Defs
import Mathlib.Algebra.Star.BigOperators
import Mathlib.Analysis.CStarAlgebra.CStarMatrix
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Matrix.Order
import Mathlib.Data.Complex.Basic
import Mathlib.Data.ENat.Lattice
import Mathlib.Data.Finset.Defs
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.Defs
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Real.Basic
import Mathlib.Data.SetLike.Basic
import Mathlib.LinearAlgebra.Matrix.Hermitian
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.LinearAlgebra.Matrix.Reindex
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Order.Defs.PartialOrder
import Mathlib.Tactic
import Definitions.Def_MIPRE_Foundations_Games
import Definitions.Def_MIPRE_Background_Repetition_Direct
import Definitions.Def_MIPRE_Foundations_GameTransport
import Definitions.Def_MIPRE_Foundations_GameDouble
import Definitions.Def_MIPRE_Foundations_TensorFamily
import Theorems.Thm_MIPRE_sum_tensorFamily
import Theorems.Thm_MIPRE_tensorFamily_mul_self
import Theorems.Thm_MIPRE_tensorFamily_one
import Theorems.Thm_MIPRE_tensorFamily_star

/-!
# Tensor powers of synchronous strategies

The completeness half of `thm:parallel-repetition` at the level of games: the `k`-fold tensor
power of a PCC synchronous strategy of value `1` is a PCC synchronous strategy of value `1` for
the `k`-fold direct repetition (blueprint `def:direct-repetition`).

* `ProjectiveMeasurement.tensorPow P k`: the family `x⃗ ↦ a⃗ ↦ ⊗ᵢ M^{xᵢ}_{aᵢ}` on
  `ℂ^{Fin k → Fin d}` (`MIPRE.tensorFamily`), a projective measurement family on the repeated
  alphabets; `ProjectiveMeasurement.reindexMat` carries it to `ℂ^{d^k}`, the shape
  `SyncStrategy` asks for.
* `SyncStrategy.tensorPow S k : SyncStrategy (H.repeat k)`, with `value = S.value ^ k`
  (`value_tensorPow`) and PCC when `S` is (`isPCC_tensorPow`): the normalized trace on
  `ℂ^{d^k}` of a tensor product is the product of the normalized traces, and the direct
  repetition's distribution and predicate are products, so every summand of the value
  factorizes and the sum over `k`-tuples of questions and answers is the `k`-th power of the sum
  (`sum_pi_prod`).
* The doubled reading that `Verifier.HasPerfectPCC` uses: a strategy of `G.doubled` gives, by
  the tensor power read on the tag of the first coordinate, one of `(G.repeat k).doubled`
  (`SyncStrategy.tensorPowDoubled`), with the same value power and PCC, and
  `exists_perfectPCC_repeat_doubled` is the statement consumed downstream.
-/

namespace MIPRE

open Matrix

variable {X A : Type*} [Fintype X] [Fintype A] [DecidableEq A]

/-! ## Reindexing a measurement family along an equivalence of the index set -/

namespace ProjectiveMeasurement

/-- Transport of a projective measurement family on `ℂ^ι` to `ℂ^κ` along `ι ≃ κ`. -/
def reindexMat {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ] (e : ι ≃ κ)
    (P : ProjectiveMeasurement X A (Matrix ι ι ℂ)) : ProjectiveMeasurement X A (Matrix κ κ ℂ) where
  M x a := (P.M x a).submatrix e.symm e.symm
  selfAdjoint x a := by
    rw [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_submatrix,
      ← Matrix.star_eq_conjTranspose, P.selfAdjoint]
  projective x a := by rw [Matrix.submatrix_mul_equiv, P.projective]
  normalized x := by
    ext i j
    rw [Matrix.sum_apply]
    simp only [Matrix.submatrix_apply]
    rw [← Matrix.sum_apply, P.normalized]
    simp [Matrix.one_apply]

omit [Fintype X] [DecidableEq A] in
@[simp] theorem reindexMat_M {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
    (e : ι ≃ κ) (P : ProjectiveMeasurement X A (Matrix ι ι ℂ)) (x : X) (a : A) :
    (P.reindexMat e).M x a = (P.M x a).submatrix e.symm e.symm := rfl

/-- The `k`-fold tensor power of a measurement family: `x⃗ ↦ a⃗ ↦ ⊗ᵢ M^{xᵢ}_{aᵢ}`. -/
def tensorPow {d : ℕ} (P : ProjectiveMeasurement X A (Matrix (Fin d) (Fin d) ℂ)) (k : ℕ) :
    ProjectiveMeasurement (Fin k → X) (Fin k → A)
      (Matrix (Fin k → Fin d) (Fin k → Fin d) ℂ) where
  M x a := tensorFamily fun i => P.M (x i) (a i)
  selfAdjoint x a := tensorFamily_star fun i => P.selfAdjoint _ _
  projective x a := tensorFamily_mul_self fun i => P.projective _ _
  normalized x := by
    rw [sum_tensorFamily]
    simp only [P.normalized]
    exact tensorFamily_one

omit [Fintype X] [DecidableEq A] in
@[simp] theorem tensorPow_M {d : ℕ} (P : ProjectiveMeasurement X A (Matrix (Fin d) (Fin d) ℂ))
    (k : ℕ) (x : Fin k → X) (a : Fin k → A) :
    (P.tensorPow k).M x a = tensorFamily fun i => P.M (x i) (a i) := rfl

end ProjectiveMeasurement

/-- `(Fin k → Fin d) ≃ Fin (d ^ k)`. -/
noncomputable def equivFinPow (d k : ℕ) : (Fin k → Fin d) ≃ Fin (d ^ k) :=
  Fintype.equivFinOfCardEq (by simp)

/-! ## The trace of a product of two projections is real -/

/-! ## Sums over tuples -/

/-! ## The tensor power of a synchronous strategy -/

namespace SyncStrategy

variable {H : SynchronousGame X A}

/-- The `k`-fold tensor power of a synchronous strategy, a strategy for the `k`-fold direct
repetition: dimension `d ^ k`, measurements `⊗ᵢ M^{xᵢ}_{aᵢ}`. -/
noncomputable def tensorPow (S : SyncStrategy H) (k : ℕ) : SyncStrategy (H.repeat k) where
  d := S.d ^ k
  d_pos := pow_pos S.d_pos k
  P := (S.P.tensorPow k).reindexMat (equivFinPow S.d k)

end SyncStrategy

/-! ## The doubled reading -/

namespace SyncStrategy

variable {G : Game X X A A}

/-- The tensor power of a strategy of the doubled game, read on the doubled repeated game: the
tag is that of every coordinate. -/
noncomputable def tensorPowDoubled (S : SyncStrategy G.doubled) (k : ℕ) :
    SyncStrategy (G.repeat k).doubled :=
  (S.tensorPow k).relabel (G.repeat k).doubled (fun p i => (p.1, p.2 i)) (Equiv.refl _)

end SyncStrategy

end MIPRE


