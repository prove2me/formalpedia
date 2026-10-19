-- Prove2me | Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_Quantum_Measurement
-- name    : MIPRE_Background_LIDT_MIPStarRE_Quantum_Measurement
-- status  : Definition
-- author  : @thomasvidick
-- created : 2026-10-16T23:13:10.379473+00:00
-- url     : https://prove2.me/theorems/6298bce1-fb33-4e90-ab7c-a0a6fb61728e
-- title:
--   Definitions of Measurement: Matrix-valued measurements for the MIP*=RE project This file provides the matrix-valued measurement layer used by the…
-- statement:
--   The definitions of the module `MIPRE.Background.LIDT.MIPStarRE.Quantum.Measurement` of the MIP\* = RE formalization (commit `70cbf1c` of vidick/MIPRE-formalization). Matrix-valued measurements for the MIP*=RE project. This file provides the matrix-valued measurement layer used by the LDT formalization.
--
--   The module is vendored read-only, with the authors' permission, from [LionSR/MIPStarRE](https://github.com/LionSR/MIPStarRE) (Sirui Lu and the MIPStarRE contributors, Apache 2.0; commit and upstream path in the file header) by `scripts/vendor-lidt.py`.
--
--   **Definitions** (6): `MIPStarRE.Quantum.Measurement` (A measurement is a submeasurement whose effects sum exactly to the identity.); `MIPStarRE.Quantum.Measurement.ofSumEqOne` (Build a complete measurement from effects whose sum is exactly the identity.); `MIPStarRE.Quantum.Measurement.postprocess` (Postprocess a complete measurement by relabeling outcomes.); `MIPStarRE.Quantum.Submeasurement` (A submeasurement on a finite answer type `α` is a family of PSD matrices `M : α → Op d` with `∑ a, M a ≤ 1`.); `MIPStarRE.Quantum.Submeasurement.postprocess` (Data processing: relabel the answer set by `f : α → β`, summing the effects over fibers.); `MIPStarRE.Quantum.Submeasurement.total` (The total operator `∑ a, M_a`.).
--
--   **Embedded lemmas** (2): the small results the bodies of these definitions need (proof fields, `simp` rules, decidability and finiteness instances), proved inside the bundle so that it imports no unproved statement: `postprocess_effect`, `postprocess_to_submeasurement`.
--
--   **Formalization Note** The bundle is the module `MIPRE.Background.LIDT.MIPStarRE.Quantum.Measurement` (`MIPRE/Background/LIDT/MIPStarRE/Quantum/Measurement.lean`) with every declaration not listed removed, imports rewritten to the bundles of the module's import closure; the declarations keep their names, statements and bodies; the source module is split over 2 imported bundle(s).
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Background/LIDT/MIPStarRE/Quantum/Measurement.lean

/-
Copyright (c) 2026 Sirui Lu and the MIPStarRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE, with the
authors' permission. Vendored from https://github.com/LionSR/MIPStarRE
(commit 507e8122, 2026-08-25) by scripts/vendor-lidt.py; do not edit by hand.
Upstream path: MIPStarRE/Quantum/Measurement.lean
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Background/LIDT/MIPStarRE/Quantum/Measurement.lean (definition bundle: declarations the uploaded statements rest on);
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
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_Quantum_FiniteMatrix_NormalizedTrace

set_option backward.isDefEq.respectTransparency false

/-!
# Matrix-valued measurements for the MIP*=RE project

This file provides the matrix-valued measurement layer used by the LDT formalization.

## Main definitions

* `Submeasurement` — a family of PSD matrices summing to at most the identity.
* `Measurement` — a family of PSD matrices summing to exactly the identity.
* `Submeasurement.postprocess` — data-processed submeasurements via answer relabeling.
* `Measurement.postprocess` — the paper's postprocessing proposition for complete POVMs.
* `inconsistency` — the off-diagonal mass `∑_{a ≠ b} τ(M_a N_b)`.
* `diagOverlap` — the diagonal mass `∑_a τ(M_a N_a)`.

## References

This file builds the project's finite-dimensional measurement layer on top of
the normalized-trace and positive-operator facts in `MIPStarRE.Quantum.FiniteMatrix`
for the quantum formalization in `references/ldt-paper/`.
-/

open scoped BigOperators MatrixOrder Matrix ComplexOrder

namespace MIPStarRE.Quantum

/-! ## Submeasurements and measurements -/

/--
A submeasurement on a finite answer type `α` is a family of PSD matrices
`M : α → Op d` with `∑ a, M a ≤ 1`.
-/
structure Submeasurement (α : Type*) [Fintype α] (d : Type*) [Fintype d] [DecidableEq d] where
  /-- The effect operators. -/
  effect : α → Op d
  /-- Each effect is positive semidefinite. -/
  pos : ∀ a, 0 ≤ effect a
  /-- The effects sum to at most the identity. -/
  sum_le_one : ∑ a, effect a ≤ 1

/--
A measurement is a submeasurement whose effects sum exactly to the identity.
-/
structure Measurement (α : Type*) [Fintype α] (d : Type*) [Fintype d] [DecidableEq d]
    extends Submeasurement α d where
  /-- The effects sum to the identity. -/
  sum_eq_one : ∑ a, effect a = 1

/-! ## Totals and postprocessing -/

namespace Submeasurement

variable {d : Type*} [Fintype d] [DecidableEq d]
variable {α β : Type*} [Fintype α] [Fintype β]

/-! ### Totals and postprocessing -/

/-- The total operator `∑ a, M_a`. -/
noncomputable def total (M : Submeasurement α d) : Op d :=
  ∑ a, M.effect a

/--
Data processing: relabel the answer set by `f : α → β`, summing the effects over
fibers.
-/
noncomputable def postprocess [DecidableEq α] [DecidableEq β]
    (M : Submeasurement α d) (f : α → β) : Submeasurement β d where
  effect b := ∑ a ∈ Finset.univ.filter (fun a => f a = b), M.effect a
  pos b := Finset.sum_nonneg fun a _ => M.pos a
  sum_le_one := by
    calc
      ∑ b, ∑ a ∈ Finset.univ.filter (fun a => f a = b), M.effect a
          = ∑ a, M.effect a := Finset.sum_fiberwise Finset.univ f M.effect
      _ ≤ 1 := M.sum_le_one

end Submeasurement

namespace Measurement

variable {d : Type*} [Fintype d] [DecidableEq d]
variable {α β : Type*} [Fintype α] [Fintype β]

/--
Build a complete measurement from effects whose sum is exactly the identity.

This constructor keeps the equality proof as the primary hypothesis and derives
the inherited submeasurement inequality automatically.  It is useful at paper
sites that are explicitly POVMs rather than relaxed sub-POVMs.
-/
def ofSumEqOne (effect : α → Op d) (pos : ∀ a, 0 ≤ effect a)
    (sum_eq_one : ∑ a, effect a = 1) : Measurement α d where
  effect := effect
  pos := pos
  sum_le_one := le_of_eq sum_eq_one
  sum_eq_one := sum_eq_one

/--
Postprocess a complete measurement by relabeling outcomes.

This formalizes `references/ldt-paper/preliminaries.tex:169--180`: regrouping
the effects along the fibers of `f` preserves the total operator, so a POVM
remains a POVM after postprocessing.
-/
noncomputable def postprocess [DecidableEq α] [DecidableEq β]
    (M : Measurement α d) (f : α → β) : Measurement β d where
  toSubmeasurement := M.toSubmeasurement.postprocess f
  sum_eq_one := by
    calc
      ∑ b, ∑ a ∈ Finset.univ.filter (fun a => f a = b), M.effect a
          = ∑ a, M.effect a := Finset.sum_fiberwise Finset.univ f M.effect
      _ = 1 := M.sum_eq_one

@[simp] theorem postprocess_effect [DecidableEq α] [DecidableEq β]
    (M : Measurement α d) (f : α → β) (b : β) :
    (M.postprocess f).effect b =
      ∑ a ∈ Finset.univ.filter (fun a => f a = b), M.effect a :=
  rfl

@[simp] theorem postprocess_to_submeasurement [DecidableEq α] [DecidableEq β]
    (M : Measurement α d) (f : α → β) :
    (M.postprocess f).toSubmeasurement = M.toSubmeasurement.postprocess f :=
  rfl

end Measurement

/-! ## Overlap definitions -/

section Overlap

variable {d : Type*} [Fintype d] [DecidableEq d]
variable {α : Type*} [Fintype α] [DecidableEq α]

end Overlap

end MIPStarRE.Quantum


