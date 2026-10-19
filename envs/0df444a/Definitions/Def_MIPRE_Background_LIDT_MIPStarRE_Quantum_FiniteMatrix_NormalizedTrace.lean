-- Prove2me | Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_Quantum_FiniteMatrix_NormalizedTrace
-- name    : MIPRE_Background_LIDT_MIPStarRE_Quantum_FiniteMatrix_NormalizedTrace
-- status  : Definition
-- author  : @thomasvidick
-- created : 2026-10-16T23:12:19.389725+00:00
-- url     : https://prove2.me/theorems/eb88a27b-ac52-410b-b8ec-761cc5bf13f1
-- title:
--   Definitions of NormalizedTrace: Normalized trace, projectors, and spectral truncation This module contains the normalized trace `τ`, the squared…
-- statement:
--   The definitions of the module `MIPRE.Background.LIDT.MIPStarRE.Quantum.FiniteMatrix.NormalizedTrace` of the MIP\* = RE formalization (commit `70cbf1c` of vidick/MIPRE-formalization). Normalized trace, projectors, and spectral truncation. This module contains the normalized trace `τ`, the squared `τ`-norm, the paper-facing orthogonal-projection name, and the spectral-truncation witness used in the low individual degree test formalization.
--
--   The module is vendored read-only, with the authors' permission, from [LionSR/MIPStarRE](https://github.com/LionSR/MIPStarRE) (Sirui Lu and the MIPStarRE contributors, Apache 2.0; commit and upstream path in the file header) by `scripts/vendor-lidt.py`.
--
--   **Definitions** (3): `MIPStarRE.Quantum.IsProj` (Paper-facing name for Mathlib's predicate that a matrix is a self-adjoint idempotent.); `MIPStarRE.Quantum.normalizedTrace` (The normalized trace `τ(A) = tr(A) / |d|`.); `MIPStarRE.Quantum.tauNormSq` (The squared τ-norm: `‖A‖²_τ = τ(A⋆ A)`.).
--
--   **Embedded lemmas** (3): the small results the bodies of these definitions need (proof fields, `simp` rules, decidability and finiteness instances), proved inside the bundle so that it imports no unproved statement: `normalizedTrace_one`, `normalizedTrace_zero`, `tauNormSq_zero`.
--
--   **Formalization Note** The bundle is the module `MIPRE.Background.LIDT.MIPStarRE.Quantum.FiniteMatrix.NormalizedTrace` (`MIPRE/Background/LIDT/MIPStarRE/Quantum/FiniteMatrix/NormalizedTrace.lean`) with every declaration not listed removed, imports rewritten to the bundles of the module's import closure; the declarations keep their names, statements and bodies; the source module is split over 1 imported bundle(s).
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Background/LIDT/MIPStarRE/Quantum/FiniteMatrix/NormalizedTrace.lean

/-
Copyright (c) 2026 Sirui Lu and the MIPStarRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE, with the
authors' permission. Vendored from https://github.com/LionSR/MIPStarRE
(commit 507e8122, 2026-08-25) by scripts/vendor-lidt.py; do not edit by hand.
Upstream path: MIPStarRE/Quantum/FiniteMatrix/NormalizedTrace.lean
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Background/LIDT/MIPStarRE/Quantum/FiniteMatrix/NormalizedTrace.lean (definition bundle: declarations the uploaded statements rest on);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/
import Mathlib.Algebra.Algebra.Basic
import Mathlib.Algebra.Algebra.Defs
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.Algebra.Group.Action.Defs
import Mathlib.Algebra.Group.Basic
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Group.Hom.Defs
import Mathlib.Algebra.GroupWithZero.Action.Defs
import Mathlib.Algebra.GroupWithZero.Defs
import Mathlib.Algebra.Module.Defs
import Mathlib.Algebra.Module.LinearMap.Defs
import Mathlib.Algebra.Ring.Defs
import Mathlib.Algebra.Ring.Hom.Defs
import Mathlib.Analysis.Matrix.Normed
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Normed.Lp.WithLp
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Finset.Defs
import Mathlib.Data.Fintype.Defs
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.FunLike.Basic
import Mathlib.Data.FunLike.Equiv
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Matrix.Block
import Mathlib.Data.Matrix.Diagonal
import Mathlib.Data.Matrix.Mul
import Mathlib.Data.SetLike.Basic
import Mathlib.LinearAlgebra.Matrix.Defs
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Logic.Equiv.Defs
import Mathlib.Tactic
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_Quantum_FiniteMatrix_Basic

set_option backward.isDefEq.respectTransparency false

/-!
# Normalized trace, projectors, and spectral truncation

This module contains the normalized trace `τ`, the squared `τ`-norm, the
paper-facing orthogonal-projection name, and the spectral-truncation witness used
in the low individual degree test formalization.
-/

open scoped BigOperators MatrixOrder Matrix ComplexOrder Matrix.Norms.Elementwise
open WithLp

namespace MIPStarRE.Quantum

variable {d : Type*} [Fintype d]

/-! ### Normalized trace -/

/-- The normalized trace `τ(A) = tr(A) / |d|`. -/
noncomputable def normalizedTrace (A : Op d) : ℂ :=
  A.trace / (Fintype.card d : ℂ)

/-- The normalized trace of the zero operator is zero. -/
@[simp] theorem normalizedTrace_zero : normalizedTrace (0 : Op d) = 0 := by
  simp [normalizedTrace]

/-- The normalized trace of the identity operator is one. -/
@[simp] theorem normalizedTrace_one [DecidableEq d] [Nonempty d] :
    normalizedTrace (1 : Op d) = 1 := by
  unfold normalizedTrace
  rw [Matrix.trace_one]
  exact div_self (Nat.cast_ne_zero.mpr Fintype.card_ne_zero)

/-! ### Squared τ-norm -/

/--
The squared τ-norm: `‖A‖²_τ = τ(A⋆ A)`.
In finite dimensions this is `(1/d) ∑ᵢⱼ |Aᵢⱼ|²`, the normalized squared
Frobenius norm.
-/
noncomputable def tauNormSq (A : Op d) : ℂ :=
  normalizedTrace (Aᴴ * A)

/-- The squared τ-norm of the zero operator is zero. -/
@[simp] theorem tauNormSq_zero : tauNormSq (0 : Op d) = 0 := by
  simp [tauNormSq]

/-! ### Projector predicate -/

/-- Paper-facing name for Mathlib's predicate that a matrix is a self-adjoint idempotent. -/
abbrev IsProj (P : Op d) : Prop := IsStarProjection P

/-! ### Spectral truncation -/

end MIPStarRE.Quantum


