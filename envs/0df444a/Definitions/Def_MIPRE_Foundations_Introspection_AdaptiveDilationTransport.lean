-- Prove2me | Definitions.Def_MIPRE_Foundations_Introspection_AdaptiveDilationTransport
-- name    : MIPRE_Foundations_Introspection_AdaptiveDilationTransport
-- status  : Definition
-- author  : @thomasvidick
-- created : 2026-10-17T01:56:54.78944+00:00
-- url     : https://prove2.me/theorems/35ce82d2-de85-46b6-a53c-be7916392d9c
-- title:
--   Definitions of AdaptiveDilationTransport: Conditional Naimark projectors in adaptive register coordinates A residual dilation is pulled back through the actual…
-- statement:
--   The definitions of the module `MIPRE.Foundations.Introspection.AdaptiveDilationTransport` of the MIP\* = RE formalization (commit `70cbf1c` of vidick/MIPRE-formalization). Conditional Naimark projectors in adaptive register coordinates. A residual dilation is pulled back through the actual coordinate split. Compression and reassociation are exact, and the next linear-map readout is retained as an explicit tensor factor of the new projective measurement.
--
--   **Definitions** (2): `MIPRE.Introspection.reassociatedConditionalDilation` (The same PVM with the fresh ancilla absorbed into the auxiliary register.); `MIPRE.Introspection.transportedConditionalDilation` (The conditional joint PVM on the original remaining register plus one fixed ancilla.).
--
--   **Formalization Note** The bundle is the module `MIPRE.Foundations.Introspection.AdaptiveDilationTransport` (`MIPRE/Foundations/Introspection/AdaptiveDilationTransport.lean`) with every declaration not listed removed, imports rewritten to the bundles of the module's import closure; the declarations keep their names, statements and bodies; the source module is split over 47 imported bundle(s).
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Foundations/Introspection/AdaptiveDilationTransport.lean

/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/Introspection/AdaptiveDilationTransport.lean (definition bundle: declarations the uploaded statements rest on);
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
import Definitions.Def_MIPRE_Foundations_POVMMix
import Definitions.Def_MIPRE_Foundations_POVMMix_B
import Definitions.Def_MIPRE_Foundations_RegisterReindex
import Definitions.Def_MIPRE_Foundations_RegisterReindex_B
import Definitions.Def_MIPRE_Foundations_StrategyDilation
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
import Definitions.Def_MIPRE_Foundations_Introspection_HidingInductionDilation
import Definitions.Def_MIPRE_Foundations_Introspection_StrategyReplacement
import Definitions.Def_MIPRE_Foundations_Introspection_StrategyReplacementRegister

/-! # Conditional Naimark projectors in adaptive register coordinates

A residual dilation is pulled back through the actual coordinate split.
Compression and reassociation are exact, and the next linear-map readout is
retained as an explicit tensor factor of the new projective measurement.
-/

noncomputable section
namespace MIPRE.Introspection

open Finset Matrix Classical
open scoped Kronecker
set_option linter.unusedSectionVars false

variable {V I R H K Y A : Type*}
  [Fintype V] [DecidableEq V] [Fintype I] [DecidableEq I]
  [Fintype R] [DecidableEq R] [Fintype H] [DecidableEq H]
  [Fintype K] [DecidableEq K] [Fintype Y] [DecidableEq Y]
  [Fintype A] [DecidableEq A]

/-- The conditional joint PVM on the original remaining register plus one
fixed ancilla. -/
def transportedConditionalDilation (e : V ≃ I × R) (Z : Y → Matrix I I ℂ)
    (P : Y → A → Matrix ((R × H) × A) ((R × H) × A) ℂ) (p : Y × A) :
    Matrix ((V × H) × A) ((V × H) × A) ℂ :=
  registerOp ((registerParty e H).prodCongr (Equiv.refl A)) (conditionalDilationOp Z P p)

/-- The same PVM with the fresh ancilla absorbed into the auxiliary register. -/
def reassociatedConditionalDilation (e : V ≃ I × R) (Z : Y → Matrix I I ℂ)
    (P : Y → A → Matrix ((R × H) × A) ((R × H) × A) ℂ) (p : Y × A) :
    Matrix (V × (H × A)) (V × (H × A)) ℂ :=
  registerOp (Equiv.prodAssoc V H A).symm (transportedConditionalDilation e Z P p)

end MIPRE.Introspection
end


