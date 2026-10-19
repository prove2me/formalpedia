-- Prove2me | Definitions.Def_MIPRE_Foundations_TensorFamily
-- name    : MIPRE_Foundations_TensorFamily
-- status  : Definition
-- author  : @thomasvidick
-- created : 2026-10-16T14:37:14.782981+00:00
-- url     : https://prove2.me/theorems/6a2737b9-b085-4940-b1a6-d63105351d57
-- title:
--   The Kronecker product of a family of matrices
-- statement:
--   Let $k \geq 0$, let $\iota$ be an index type and let $M_0, \ldots, M_{k-1}$ be complex matrices on $\mathbb C^{\iota}$, given as `M : Fin k → Matrix ι ι ℂ`. `MIPRE.tensorFamily M : Matrix (Fin k → ι) (Fin k → ι) ℂ` is their tensor product $M_0 \otimes \cdots \otimes M_{k-1}$, realized as a matrix on $\mathbb C^{\iota^k}$ whose rows and columns are indexed by $k$-tuples $v, w : \mathrm{Fin}\,k \to \iota$:
--
--   $$\Big(\bigotimes_{i<k} M_i\Big)_{v,w} \;=\; \prod_{i<k} (M_i)_{v_i,\,w_i}.$$
--
--   This is the only definition of the module `MIPRE.Foundations.TensorFamily`. The bundle embeds one lemma, `MIPRE.tensorFamily_apply`, the `@[simp]` unfolding rule stating the displayed entry formula, which holds by `rfl`. The module's other results (multiplicativity `tensorFamily_mul`, compatibility with the conjugate transpose `tensorFamily_conjTranspose`, `tensorFamily_one`, the coordinatewise sum rule `sum_tensorFamily`, `trace_tensorFamily`, and the closure of idempotents and of self-adjoint matrices under the product, `tensorFamily_mul_self` and `tensorFamily_star`) are not part of this bundle.
--
--   The construction is what the $k$-fold tensor power of a synchronous strategy measures with (`MIPRE.SyncStrategy.tensorPow`, bundle `MIPRE.Background.Repetition.TensorPower`), the completeness half of blueprint `thm:parallel-repetition` at the level of games (`lem:tensor-power-pcc`). Mathlib's `Matrix.kronecker` is the binary case with the product index `ι × ι`; the family form is used because `Fin k → ι` needs no reassociation.
--
--   **Formalization Note** `tensorFamily M` is `Matrix.of fun v w => ∏ i, M i (v i) (w i)`, the product running over `i : Fin k`. The index type `ι : Type*` is arbitrary and the definition needs no `Fintype ι` instance (finiteness enters only in the module's multiplication and trace lemmas); the entries are in `ℂ`. At `k = 0` the index type `Fin 0 → ι` is a singleton and the matrix is the `1 × 1` matrix with entry `1`. The bundle imports no other definition bundle, only Mathlib.
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Foundations/TensorFamily.lean; blueprint lem:tensor-power-pcc

/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/TensorFamily.lean (definition bundle: declarations the uploaded statements rest on);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/
import Mathlib.Algebra.BigOperators.Pi
import Mathlib.Algebra.Star.BigOperators
import Mathlib.Analysis.Complex.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.LinearAlgebra.Matrix.Hermitian
import Mathlib.LinearAlgebra.Matrix.Reindex
import Mathlib.LinearAlgebra.Matrix.Trace

/-!
# The Kronecker product of a family of matrices

The `k`-fold tensor product `M₁ ⊗ ⋯ ⊗ M_k` of matrices on `ℂ^ι`, as a matrix on
`ℂ^{Fin k → ι}`: `(⊗ᵢ Mᵢ) v w = ∏ᵢ Mᵢ (v i) (w i)`. This is what the `k`-fold tensor power of a
strategy measures with (`MIPRE.SyncStrategy.tensorPow`, `Background/Repetition/TensorPower.lean`),
and the four facts about it that the value and PCC computations use: it is multiplicative
(`tensorFamily_mul`), compatible with the adjoint (`tensorFamily_conjTranspose`), sends the
constant family `1` to `1` (`tensorFamily_one`), sums coordinatewise (`sum_tensorFamily`) and
has trace the product of the traces (`trace_tensorFamily`). All are `Fintype.prod_sum`, the
distributivity of a product of sums over `Fin k` into a sum over `Fin k → ι`.

Mathlib's `Matrix.kronecker` is the binary case with the product index `ι × ι`; the family
form is more convenient than iterating it, because `Fin k → ι` needs no reassociation.
-/

namespace MIPRE

open Matrix

variable {k : ℕ} {ι : Type*}

/-- The tensor product `⊗ᵢ Mᵢ` of a family of matrices, as a matrix indexed by `Fin k → ι`. -/
def tensorFamily (M : Fin k → Matrix ι ι ℂ) : Matrix (Fin k → ι) (Fin k → ι) ℂ :=
  Matrix.of fun v w => ∏ i, M i (v i) (w i)

@[simp] theorem tensorFamily_apply (M : Fin k → Matrix ι ι ℂ) (v w : Fin k → ι) :
    tensorFamily M v w = ∏ i, M i (v i) (w i) := rfl

end MIPRE


