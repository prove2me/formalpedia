-- Prove2me | Definitions.Def_MIPRE_Foundations_Introspection_HidingInductionDilation
-- name    : MIPRE_Foundations_Introspection_HidingInductionDilation
-- status  : Definition
-- author  : @thomasvidick
-- created : 2026-10-17T01:48:26.733975+00:00
-- url     : https://prove2.me/theorems/37f46c22-d062-4fbe-bcef-e744329d2a0f
-- title:
--   Definitions of HidingInductionDilation: Projectivizing a conditional residual measurement One fixed ancilla is added on the residual side of every prefix
-- statement:
--   The definitions of the module `MIPRE.Foundations.Introspection.HidingInductionDilation` of the MIP\* = RE formalization (commit `70cbf1c` of vidick/MIPRE-formalization). Projectivizing a conditional residual measurement. One fixed ancilla is added on the residual side of every prefix. The prefix projectors are unchanged. Squared distance to the old projective measurement costs `2 sqrt(delta)`; a dilation does not in general preserve that distance.
--
--   **Definitions** (1): `MIPRE.Introspection.conditionalDilationOp` (Keep the prefix register outside the new ancilla, in the original party ordering `(prefix × residual) × ancilla`.).
--
--   **Formalization Note** The bundle is the module `MIPRE.Foundations.Introspection.HidingInductionDilation` (`MIPRE/Foundations/Introspection/HidingInductionDilation.lean`) with every declaration not listed removed, imports rewritten to the bundles of the module's import closure; the declarations keep their names, statements and bodies; the source module is split over 39 imported bundle(s).
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Foundations/Introspection/HidingInductionDilation.lean

/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/Introspection/HidingInductionDilation.lean (definition bundle: declarations the uploaded statements rest on);
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
import Definitions.Def_MIPRE_Foundations_POVMValue
import Definitions.Def_MIPRE_Foundations_Sign
import Definitions.Def_MIPRE_Foundations_CrossConsistency
import Definitions.Def_MIPRE_Foundations_CrossConsistency_B
import Definitions.Def_MIPRE_Foundations_PVM
import Definitions.Def_MIPRE_Foundations_PVM_B
import Definitions.Def_MIPRE_Foundations_Commutation
import Definitions.Def_MIPRE_Foundations_Dilation
import Definitions.Def_MIPRE_Foundations_Expanded
import Definitions.Def_MIPRE_Foundations_LowDegree_SchwartzZippel
import Definitions.Def_MIPRE_Foundations_LowDegree_Anticomm
import Definitions.Def_MIPRE_Foundations_Weyl
import Definitions.Def_MIPRE_Foundations_Parseval
import Definitions.Def_MIPRE_Foundations_Linearity
import Definitions.Def_MIPRE_Foundations_Sandwich
import Definitions.Def_MIPRE_Foundations_Pasting
import Definitions.Def_MIPRE_Foundations_WeylEPR
import Definitions.Def_MIPRE_Foundations_Introspection_TwirlDistance
import Definitions.Def_MIPRE_Foundations_Introspection_LinearMeasurement
import Definitions.Def_MIPRE_Foundations_Introspection_CommutatorParseval
import Definitions.Def_MIPRE_Foundations_Introspection_BlockTwirl
import Definitions.Def_MIPRE_Foundations_Introspection_BlockPOVM
import Definitions.Def_MIPRE_Foundations_Introspection_EPR
import Definitions.Def_MIPRE_Foundations_Introspection_BlockRetention
import Definitions.Def_MIPRE_Foundations_Introspection_PauliMixing
import Definitions.Def_MIPRE_Foundations_Introspection_RegisterTransport
import Definitions.Def_MIPRE_Foundations_Introspection_RegisterEPR
import Definitions.Def_MIPRE_Foundations_Swap
import Definitions.Def_MIPRE_Foundations_Introspection_ValueStability
import Theorems.Thm_MIPRE_aOp_conjTranspose
import Theorems.Thm_MIPRE_aOp_sum
import Theorems.Thm_MIPRE_ancillaEmbed_isometry

/-! # Projectivizing a conditional residual measurement

One fixed ancilla is added on the residual side of every prefix. The prefix
projectors are unchanged. Squared distance to the old projective measurement
costs `2 sqrt(delta)`; a dilation does not in general preserve that distance.
-/

noncomputable section

namespace MIPRE.Introspection

open Finset Matrix Classical
open scoped Kronecker ComplexOrder MatrixOrder

set_option linter.unusedSectionVars false

section Distance

variable {H K A T : Type*}
  [Fintype H] [DecidableEq H] [Fintype K] [DecidableEq K]
  [Fintype A] [DecidableEq A] [Fintype T] [DecidableEq T]

end Distance

section Conditional

variable {I H K Y A J : Type*}
  [Fintype I] [DecidableEq I] [Fintype H] [DecidableEq H]
  [Fintype K] [DecidableEq K] [Fintype Y] [DecidableEq Y]
  [Fintype A] [DecidableEq A] [Fintype J]

/-- Keep the prefix register outside the new ancilla, in the original party
ordering `(prefix × residual) × ancilla`. -/
def conditionalDilationOp (Z : Y → Matrix I I ℂ)
    (P : Y → A → Matrix (H × A) (H × A) ℂ) (p : Y × A) :
    Matrix ((I × H) × A) ((I × H) × A) ℂ :=
  registerOp (Equiv.prodAssoc I H A) (Z p.1 ⊗ₖ P p.1 p.2)

end Conditional

section Varying

variable {J A : Type*} [Fintype J] [Fintype A] [DecidableEq A]
  {I H K Y : J → Type*}
  [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)]
  [∀ j, Fintype (H j)] [∀ j, DecidableEq (H j)]
  [∀ j, Fintype (K j)] [∀ j, DecidableEq (K j)]
  [∀ j, Fintype (Y j)] [∀ j, DecidableEq (Y j)]

end Varying

end MIPRE.Introspection

end


