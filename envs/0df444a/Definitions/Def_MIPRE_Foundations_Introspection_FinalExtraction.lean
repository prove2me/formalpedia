-- Prove2me | Definitions.Def_MIPRE_Foundations_Introspection_FinalExtraction
-- name    : MIPRE_Foundations_Introspection_FinalExtraction
-- status  : Definition
-- author  : @thomasvidick
-- created : 2026-10-17T01:49:51.798128+00:00
-- url     : https://prove2.me/theorems/345187d1-e3aa-4f6e-9ff6-ea9e01994ad1
-- title:
--   Definitions of FinalExtraction: Extracting the original strategy from introspective readouts This proves the final game-value calculation in the…
-- statement:
--   The definitions of the module `MIPRE.Foundations.Introspection.FinalExtraction` of the MIP\* = RE formalization (commit `70cbf1c` of vidick/MIPRE-formalization). Extracting the original strategy from introspective readouts. This proves the final game-value calculation in the soundness proof of `introspection.tex`. Once the induction has produced a question readout tensored with an auxiliary measurement depending on that question, the original strategy uses precisely those auxiliary measurements and the auxiliary state. The value identity below is exact, including the question-distribution normalization.
--
--   **Definitions** (2): `MIPRE.Introspection.conditionalReadout` (Read the question from the EPR seed and then measure the auxiliary system.); `MIPRE.Introspection.readoutAcceptance` (Acceptance probability of the introspective test on the terminal measurements.).
--
--   **Formalization Note** The bundle is the module `MIPRE.Foundations.Introspection.FinalExtraction` (`MIPRE/Foundations/Introspection/FinalExtraction.lean`) with every declaration not listed removed, imports rewritten to the bundles of the module's import closure; the declarations keep their names, statements and bodies; the source module is split over 48 imported bundle(s).
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Foundations/Introspection/FinalExtraction.lean

/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/Introspection/FinalExtraction.lean (definition bundle: declarations the uploaded statements rest on);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Algebra.MvPolynomial.Degrees
import Mathlib.Algebra.MvPolynomial.SchwartzZippel
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Analysis.CStarAlgebra.CStarMatrix
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Data.ENat.Lattice
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.List.Basic
import Mathlib.Data.Nat.Bits
import Mathlib.Data.Nat.Notation
import Mathlib.Data.Nat.Size
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
import Definitions.Def_MIPRE_Foundations_CL_Basic
import Definitions.Def_MIPRE_Foundations_Cost_Basic_B
import Definitions.Def_MIPRE_Foundations_Cost_Encoding_B
import Definitions.Def_MIPRE_Foundations_Cost_PolyTime
import Definitions.Def_MIPRE_Foundations_CL_Closure_B
import Definitions.Def_MIPRE_Foundations_CL_Sampler
import Definitions.Def_MIPRE_Foundations_Verifier
import Definitions.Def_MIPRE_Foundations_LowDegree_Encoding
import Definitions.Def_MIPRE_Foundations_Closeness
import Definitions.Def_MIPRE_Foundations_GameTransport
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
import Definitions.Def_MIPRE_Foundations_GameAdapt
import Definitions.Def_MIPRE_Foundations_SampledGame
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
import Definitions.Def_MIPRE_Foundations_Introspection_Readout

/-! # Extracting the original strategy from introspective readouts

This proves the final game-value calculation in the soundness proof of
`introspection.tex`. Once the induction has produced a question readout tensored
with an auxiliary measurement depending on that question, the original strategy
uses precisely those auxiliary measurements and the auxiliary state. The value
identity below is exact, including the question-distribution normalization.
-/

noncomputable section

namespace MIPRE.Introspection

open Finset Matrix Classical
open scoped Kronecker ComplexOrder MatrixOrder

variable {I X Y A B H K : Type*}
  [Fintype I] [DecidableEq I] [Fintype X] [DecidableEq X]
  [Fintype Y] [DecidableEq Y] [Fintype A] [DecidableEq A]
  [Fintype B] [DecidableEq B] [Fintype H] [DecidableEq H]
  [Fintype K] [DecidableEq K]

set_option linter.unusedSectionVars false

/-- Read the question from the EPR seed and then measure the auxiliary system. -/
def conditionalReadout (f : I → X) (P : X → A → Matrix H H ℂ)
    (xa : X × A) : Matrix (I × H) (I × H) ℂ := readout f xa.1 ⊗ₖ P xa.1 xa.2

/-- Acceptance probability of the introspective test on the terminal measurements. -/
def readoutAcceptance (f : I → X) (g : I → Y) (ξ : H × K → ℂ)
    (P : X → A → Matrix H H ℂ) (Q : Y → B → Matrix K K ℂ)
    (D : X → Y → A → B → Bool) : ℝ :=
  ∑ xa : X × A, ∑ yb : Y × B,
    (if D xa.1 yb.1 xa.2 yb.2 then 1 else 0) *
      bornProb (registerState I ξ) (conditionalReadout f P xa) (conditionalReadout g Q yb)

end MIPRE.Introspection

end


