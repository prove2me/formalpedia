-- Prove2me | Definitions.Def_MIPRE_Foundations_Introspection_CommutatorParseval
-- name    : MIPRE_Foundations_Introspection_CommutatorParseval
-- status  : Definition
-- author  : @thomasvidick
-- created : 2026-10-17T01:41:11.212981+00:00
-- url     : https://prove2.me/theorems/a98421da-2c22-4de8-a910-159fae6c989c
-- title:
--   Definitions of CommutatorParseval: Parseval for commutators with linear-map readouts The character transform on the kernel's perpendicular identifies the…
-- statement:
--   The definitions of the module `MIPRE.Foundations.Introspection.CommutatorParseval` of the MIP\* = RE formalization (commit `70cbf1c` of vidick/MIPRE-formalization). Parseval for commutators with linear-map readouts. The character transform on the kernel's perpendicular identifies the outcome-summed commutator error of a linear-map measurement with the uniformly averaged error of its Pauli observables. This proves the characteristic-two form of the paper's `lem:W`. The identity holds on every state, with ancillary spaces and empty fibres allowed.
--
--   **Definitions** (1): `MIPRE.Introspection.commutatorAction` (Commute a register operator with `M` and apply the result to a bipartite state.).
--
--   **Formalization Note** The bundle is the module `MIPRE.Foundations.Introspection.CommutatorParseval` (`MIPRE/Foundations/Introspection/CommutatorParseval.lean`) with every declaration not listed removed, imports rewritten to the bundles of the module's import closure; the declarations keep their names, statements and bodies; the source module is split over 16 imported bundle(s).
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Foundations/Introspection/CommutatorParseval.lean

/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/Introspection/CommutatorParseval.lean (definition bundle: declarations the uploaded statements rest on);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/
import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Algebra.MvPolynomial.Degrees
import Mathlib.Algebra.MvPolynomial.SchwartzZippel
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Analysis.CStarAlgebra.CStarMatrix
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Data.ENat.Lattice
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Data.Real.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.FieldTheory.Finite.GaloisField
import Mathlib.LinearAlgebra.BilinearForm.Orthogonal
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.LinearAlgebra.Pi
import Mathlib.RingTheory.Trace.Basic
import Mathlib.Tactic.IntervalCases
import Definitions.Def_MIPRE_Foundations_Games
import Definitions.Def_MIPRE_Foundations_Distances
import Definitions.Def_MIPRE_Foundations_CL_Register
import Definitions.Def_MIPRE_Foundations_CL_Canonical
import Definitions.Def_MIPRE_Foundations_LowDegree_Encoding
import Definitions.Def_MIPRE_Foundations_Closeness
import Definitions.Def_MIPRE_Foundations_OpBound
import Definitions.Def_MIPRE_Foundations_OpBound_B
import Definitions.Def_MIPRE_Foundations_StateDistance
import Definitions.Def_MIPRE_Foundations_StateDistance_B
import Definitions.Def_MIPRE_Foundations_Sign
import Definitions.Def_MIPRE_Foundations_LowDegree_SchwartzZippel
import Definitions.Def_MIPRE_Foundations_LowDegree_Anticomm
import Definitions.Def_MIPRE_Foundations_Weyl
import Definitions.Def_MIPRE_Foundations_Parseval
import Definitions.Def_MIPRE_Foundations_Introspection_LinearMeasurement
import Theorems.Thm_MIPRE_aOp_add
import Theorems.Thm_MIPRE_aOp_smul

/-! # Parseval for commutators with linear-map readouts

The character transform on the kernel's perpendicular identifies the outcome-summed
commutator error of a linear-map measurement with the uniformly averaged error of its
Pauli observables. This proves the characteristic-two form of the paper's `lem:W`.
The identity holds on every state, with ancillary spaces and empty fibres allowed.
-/

noncomputable section

namespace MIPRE.Introspection

open Finset Weyl Matrix Classical

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F]
variable {n : ℕ} {N : Type*} [Fintype N]

variable {H B : Type*} [Fintype H] [DecidableEq H] [Fintype B] [DecidableEq B]

/-- Commute a register operator with `M` and apply the result to a bipartite state. -/
def commutatorAction (ψ : ((Fin n → F) × H) × B → ℂ)
    (M : Matrix ((Fin n → F) × H) ((Fin n → F) × H) ℂ) :
    Matrix (Fin n → F) (Fin n → F) ℂ →ₗ[ℂ] (((Fin n → F) × H) × B → ℂ) where
  toFun P := aOp (M * aOp P - aOp P * M) *ᵥ ψ
  map_add' P Q := by
    simp only [aOp_add, mul_add, add_mul, add_sub_add_comm, Matrix.add_mulVec]
  map_smul' c P := by
    simp only [aOp_smul, Matrix.mul_smul, Matrix.smul_mul, ← smul_sub, Matrix.smul_mulVec,
      RingHom.id_apply]

end MIPRE.Introspection

end


