-- Prove2me | Definitions.Def_MIPRE_Foundations_Introspection_AmbientMixing
-- name    : MIPRE_Foundations_Introspection_AmbientMixing
-- status  : Definition
-- author  : @thomasvidick
-- created : 2026-10-17T01:50:46.89619+00:00
-- url     : https://prove2.me/theorems/305a1ecf-bf70-4516-88fb-4193556bf277
-- title:
--   Definitions of AmbientMixing: Pauli mixing for nested registers in one ambient EPR state This is the ambient-register form of the paper's…
-- statement:
--   The definitions of the module `MIPRE.Foundations.Introspection.AmbientMixing` of the MIP\* = RE formalization (commit `70cbf1c` of vidick/MIPRE-formalization). Pauli mixing for nested registers in one ambient EPR state. This is the ambient-register form of the paper's `lem:mixing`. A measurement acts on `V` and the original ancilla, and the selected Pauli readout acts on `U ⊆ V`. Its extracted POVMs act on `V \ U` and that same ancilla. All three hypotheses and the conclusion use the one ambient EPR state. Restricting to the local register and returning to the ambient register are exact operations.
--
--   **Definitions** (4): `MIPRE.Introspection.ambientCommutatorError` (Ambient commutation with a selected Pauli readout.); `MIPRE.Introspection.ambientMarginalError` (Ambient consistency of the first outcome with the selected `Z` readout.); `MIPRE.Introspection.ambientOperator` (Extend an operator on `V` and the ancilla by identity on `V`'s ambient complement.); `MIPRE.Introspection.ambientReadout` (The selected readout, embedded into the original ambient space.).
--
--   **Formalization Note** The bundle is the module `MIPRE.Foundations.Introspection.AmbientMixing` (`MIPRE/Foundations/Introspection/AmbientMixing.lean`) with every declaration not listed removed, imports rewritten to the bundles of the module's import closure; the declarations keep their names, statements and bodies; the source module is split over 39 imported bundle(s).
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Foundations/Introspection/AmbientMixing.lean

/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/Introspection/AmbientMixing.lean (definition bundle: declarations the uploaded statements rest on);
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
import Definitions.Def_MIPRE_Foundations_Introspection_RegisterMixing
import Definitions.Def_MIPRE_Foundations_Introspection_RegisterCoordinates

/-! # Pauli mixing for nested registers in one ambient EPR state

This is the ambient-register form of the paper's `lem:mixing`. A measurement
acts on `V` and the original ancilla, and the selected Pauli readout acts on
`U ⊆ V`. Its extracted POVMs act on `V \ U` and that same ancilla. All three
hypotheses and the conclusion use the one ambient EPR state. Restricting to
the local register and returning to the ambient register are exact operations.
-/

noncomputable section

namespace MIPRE.Introspection

open Finset Matrix Weyl Classical
open scoped Kronecker

set_option linter.unusedSectionVars false

variable {ι F H K A : Type*} [Fintype ι] [DecidableEq ι]
  [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F]
  [Fintype H] [DecidableEq H] [Fintype K] [DecidableEq K]
  [Fintype A] [DecidableEq A]

/-- Extend an operator on `V` and the ancilla by identity on `V`'s ambient complement. -/
def ambientOperator (V : Finset ι) (M : Matrix ((V → F) × H) ((V → F) × H) ℂ) :
    Matrix ((ι → F) × H) ((ι → F) × H) ℂ := registerExtend (ambientSplit V) M

/-- The selected readout, embedded into the original ambient space. -/
def ambientReadout (U V : Finset ι) (hUV : U ⊆ V)
    (w : (Fin (Fintype.card U) → F) →
      Matrix (Fin (Fintype.card U) → F) (Fin (Fintype.card U) → F) ℂ)
    (L : (Fin (Fintype.card U) → F) →ₗ[F] (Fin (Fintype.card U) → F))
    (y : Fin (Fintype.card U) → F) : Matrix ((ι → F) × H) ((ι → F) × H) ℂ :=
  ambientOperator V (registerReadout (coordinateSplit U V hUV) w L y)

/-- Ambient consistency of the first outcome with the selected `Z` readout. -/
def ambientMarginalError (U V : Finset ι) (hUV : U ⊆ V)
    (L : CL.RegLinear F U) (ξ : H × K → ℂ)
    (M : (Fin (Fintype.card U) → F) × A → Matrix ((V → F) × H) ((V → F) × H) ℂ) : ℝ :=
  ∑ y, stateSqNorm (registerState (ι → F) ξ)
    ((∑ a, ambientOperator V (M (y, a))) - ambientReadout U V hUV wZ (coordinateLinear L) y)

/-- Ambient commutation with a selected Pauli readout. -/
def ambientCommutatorError (U V : Finset ι) (hUV : U ⊆ V) (ξ : H × K → ℂ)
    (M : (Fin (Fintype.card U) → F) × A → Matrix ((V → F) × H) ((V → F) × H) ℂ)
    (w : (Fin (Fintype.card U) → F) →
      Matrix (Fin (Fintype.card U) → F) (Fin (Fintype.card U) → F) ℂ)
    (L : (Fin (Fintype.card U) → F) →ₗ[F] (Fin (Fintype.card U) → F)) : ℝ :=
  ∑ p, ∑ y, stateSqNorm (registerState (ι → F) ξ)
    (ambientOperator V (M p) * ambientReadout U V hUV w L y -
      ambientReadout U V hUV w L y * ambientOperator V (M p))

end MIPRE.Introspection

end


