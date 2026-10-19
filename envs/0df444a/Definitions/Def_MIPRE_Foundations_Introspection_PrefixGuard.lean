-- Prove2me | Definitions.Def_MIPRE_Foundations_Introspection_PrefixGuard
-- name    : MIPRE_Foundations_Introspection_PrefixGuard
-- status  : Definition
-- author  : @thomasvidick
-- created : 2026-10-17T01:53:27.485875+00:00
-- url     : https://prove2.me/theorems/7151a1b0-b2c4-4bdd-a0ba-0dddd75a00d0
-- title:
--   Definitions of PrefixGuard: Semantic prefix guards for executable introspection A Hide answer at level `k` must have an attained `k`-stage prefix
-- statement:
--   The definitions of the module `MIPRE.Foundations.Introspection.PrefixGuard` of the MIP\* = RE formalization (commit `70cbf1c` of vidick/MIPRE-formalization). Semantic prefix guards for executable introspection. A Hide answer at level `k` must have an attained `k`-stage prefix. A Read answer must have an attained penultimate prefix. Constructor validity remains the responsibility of the existing typed format check.
--
--   **Definitions** (2): `MIPRE.Introspection.PrefixGuard.check` (Boolean presentation of the local guard; executable scans implement this proposition.); `MIPRE.Introspection.PrefixGuard.holds` (The local image condition imposed by the executable prefix scan.).
--
--   **Embedded lemmas** (1): the small results the bodies of these definitions need (proof fields, `simp` rules, decidability and finiteness instances), proved inside the bundle so that it imports no unproved statement: `check_eq_true`.
--
--   **Formalization Note** The bundle is the module `MIPRE.Foundations.Introspection.PrefixGuard` (`MIPRE/Foundations/Introspection/PrefixGuard.lean`) with every declaration not listed removed, imports rewritten to the bundles of the module's import closure; the declarations keep their names, statements and bodies; the source module is split over 46 imported bundle(s).
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Foundations/Introspection/PrefixGuard.lean

/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/Introspection/PrefixGuard.lean (definition bundle: declarations the uploaded statements rest on);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
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
import Mathlib.Data.Fintype.Option
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Sum
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
import Mathlib.Tactic.DeriveFintype
import Mathlib.Tactic.IntervalCases
import Definitions.Def_MIPRE_Foundations_Games
import Definitions.Def_MIPRE_Foundations_Distances
import Definitions.Def_MIPRE_Foundations_CL_Register
import Definitions.Def_MIPRE_Foundations_CL_Canonical
import Definitions.Def_MIPRE_Foundations_CL_Basic
import Definitions.Def_MIPRE_Foundations_Cost_Basic_B
import Definitions.Def_MIPRE_Foundations_Cost_Encoding_B
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
import Definitions.Def_MIPRE_Foundations_Introspection_Types
import Definitions.Def_MIPRE_Foundations_Introspection_SamplingPrefix
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
import Definitions.Def_MIPRE_Foundations_Introspection_AuxiliaryChecks
import Definitions.Def_MIPRE_Foundations_Introspection_TypedPredicate

/-! # Semantic prefix guards for executable introspection

A Hide answer at level `k` must have an attained `k`-stage prefix. A Read
answer must have an attained penultimate prefix. Constructor validity remains
the responsibility of the existing typed format check.
-/

noncomputable section
namespace MIPRE.Introspection.PrefixGuard
open Classical

variable {F ι A PA P : Type*} [Field F] [Fintype ι] [DecidableEq ι] {ℓ : ℕ}

/-- The local image condition imposed by the executable prefix scan. -/
def holds (L : Bool → CL.CLFun F ι ℓ) :
    QuestionType P ℓ → ParsedAnswer (ι → F) A PA → Prop
  | .inr (.hide k, w), .hide y _ _ =>
      ∃ x, ((L w).truncate k.val).eval x = (L w).outputPrefix k.val y
  | .inr (.read, w), .read y _ _ =>
      ∃ x, ((L w).truncate (ℓ - 1)).eval x = (L w).outputPrefix (ℓ - 1) y
  | _, _ => True

/-- Boolean presentation of the local guard; executable scans implement this proposition. -/
def check (L : Bool → CL.CLFun F ι ℓ) (t : QuestionType P ℓ)
    (a : ParsedAnswer (ι → F) A PA) : Bool := decide (holds L t a)

@[simp] theorem check_eq_true (L : Bool → CL.CLFun F ι ℓ) (t : QuestionType P ℓ)
    (a : ParsedAnswer (ι → F) A PA) : check L t a = true ↔ holds L t a := by
  simp [check]

end MIPRE.Introspection.PrefixGuard


