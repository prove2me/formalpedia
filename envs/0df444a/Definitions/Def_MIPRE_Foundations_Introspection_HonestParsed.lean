-- Prove2me | Definitions.Def_MIPRE_Foundations_Introspection_HonestParsed
-- name    : MIPRE_Foundations_Introspection_HonestParsed
-- status  : Definition
-- author  : @thomasvidick
-- created : 2026-10-17T02:04:12.862696+00:00
-- url     : https://prove2.me/theorems/9a4e6614-cbdc-4690-bdfc-fcfdf8be915f
-- title:
--   Definitions of HonestParsed: Honest measurements on the complete parsed-answer alphabet The actual core, Read and Hide operators act on one common…
-- statement:
--   The definitions of the module `MIPRE.Foundations.Introspection.HonestParsed` of the MIP\* = RE formalization (commit `70cbf1c` of vidick/MIPRE-formalization). Honest measurements on the complete parsed-answer alphabet. The actual core, Read and Hide operators act on one common register/source space. Wrong constructors have zero effect. This retains every answer label, gives genuine PVMs, and makes the Introspect/Read operator tests apply without a promise that the reported constructors are well formed.
--
--   **Definitions** (3): `MIPRE.Introspection.Honest.parsedCoreOp` (Introspect and Sample use their actual core operators on pair answers.); `MIPRE.Introspection.Honest.parsedHideOp` (Hide acts on the genuine adaptive hiding register, leaving the source register alone.); `MIPRE.Introspection.Honest.parsedReadOp` (Read uses the full adaptive register and source-answer measurement.).
--
--   **Embedded lemmas** (4): the small results the bodies of these definitions need (proof fields, `simp` rules, decidability and finiteness instances), proved inside the bundle so that it imports no unproved statement: `parsedCoreOp_pair`, `parsedHideOp_hide`, `parsedReadOp_read`, `sum_supported`.
--
--   **Formalization Note** The bundle is the module `MIPRE.Foundations.Introspection.HonestParsed` (`MIPRE/Foundations/Introspection/HonestParsed.lean`) with every declaration not listed removed, imports rewritten to the bundles of the module's import closure; the declarations keep their names, statements and bodies; the source module is split over 65 imported bundle(s).
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Foundations/Introspection/HonestParsed.lean

/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/Introspection/HonestParsed.lean (definition bundle: declarations the uploaded statements rest on);
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
import Mathlib.Data.Fintype.Option
import Mathlib.Data.Fintype.Pi
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
import Definitions.Def_MIPRE_Foundations_Cost_PolyTime
import Definitions.Def_MIPRE_Foundations_CL_Closure_B
import Definitions.Def_MIPRE_Foundations_CL_Sampler
import Definitions.Def_MIPRE_Foundations_Verifier
import Definitions.Def_MIPRE_Foundations_LowDegree_Encoding
import Definitions.Def_MIPRE_Foundations_Closeness
import Definitions.Def_MIPRE_Foundations_PerfectStrategy
import Definitions.Def_MIPRE_Foundations_GameTransport
import Definitions.Def_MIPRE_Foundations_GameDouble
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
import Definitions.Def_MIPRE_Foundations_CL_Graph
import Definitions.Def_MIPRE_Foundations_SampledGame
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
import Definitions.Def_MIPRE_Foundations_Introspection_Readout
import Definitions.Def_MIPRE_Foundations_Introspection_FinalExtraction
import Definitions.Def_MIPRE_Foundations_Introspection_TypeGraph
import Definitions.Def_MIPRE_Foundations_Introspection_HonestCore
import Definitions.Def_MIPRE_Foundations_Introspection_HonestFirstHide
import Definitions.Def_MIPRE_Foundations_Introspection_HonestAdaptive
import Definitions.Def_MIPRE_Foundations_Introspection_HonestRead
import Definitions.Def_MIPRE_Foundations_Introspection_HonestHiding
import Definitions.Def_MIPRE_Foundations_Introspection_HonestReading

/-! # Honest measurements on the complete parsed-answer alphabet

The actual core, Read and Hide operators act on one common register/source
space. Wrong constructors have zero effect. This retains every answer label,
gives genuine PVMs, and makes the Introspect/Read operator tests apply without
a promise that the reported constructors are well formed.
-/

noncomputable section

namespace MIPRE.Introspection.Honest

open Finset Matrix Classical
open scoped Kronecker

set_option linter.unusedSectionVars false

variable {F ι A PA : Type*} [Field F] [Fintype F] [DecidableEq F]
  [Algebra (ZMod 2) F] [Fintype ι] [DecidableEq ι]
  [Fintype A] [DecidableEq A] [Fintype PA] {ℓ : ℕ}
  (L : Bool → CL.CLFun F ι ℓ) (D : (ι → F) → (ι → F) → A → A → Bool)
  (R : SyncStrategy (sourceGame L D).doubled)

theorem sum_supported {B C M : Type*} [Fintype B] [Fintype C] [AddCommMonoid M]
    (f : B → C) (hf : Function.Injective f) (g : C → M)
    (hz : ∀ c, c ∉ Set.range f → g c = 0) : (∑ c, g c) = ∑ b, g (f b) := by
  symm
  exact Fintype.sum_of_injective f hf _ g hz (fun _ => rfl)

/-- Introspect and Sample use their actual core operators on pair answers. -/
def parsedCoreOp (t : CoreType) : ParsedAnswer (ι → F) A PA →
    Matrix ((ι → F) × Fin R.d) ((ι → F) × Fin R.d) ℂ
  | .pair y a => coreOp L D R t (y, a)
  | _ => 0

/-- Read uses the full adaptive register and source-answer measurement. -/
def parsedReadOp (w : Bool) (h : (L w).SupportedOn Finset.univ) :
    ParsedAnswer (ι → F) A PA → Matrix ((ι → F) × Fin R.d) ((ι → F) × Fin R.d) ℂ
  | .read y yp a => fullReadOp L D R w h ((y, yp), a)
  | _ => 0

/-- Hide acts on the genuine adaptive hiding register, leaving the source register alone. -/
def parsedHideOp (w : Bool) (k : ℕ) (h : (L w).SupportedOn Finset.univ) :
    ParsedAnswer (ι → F) A PA → Matrix ((ι → F) × Fin R.d) ((ι → F) × Fin R.d) ℂ
  | .hide y yp x => hideOp (L w) k h (y, yp, x) ⊗ₖ (1 : Matrix (Fin R.d) (Fin R.d) ℂ)
  | _ => 0

@[simp] theorem parsedCoreOp_pair (t : CoreType) (y : ι → F) (a : A) :
    parsedCoreOp (PA := PA) L D R t (.pair y a) = coreOp L D R t (y, a) := rfl

@[simp] theorem parsedReadOp_read (w : Bool) (h : (L w).SupportedOn Finset.univ)
    (y yp : ι → F) (a : A) : parsedReadOp (PA := PA) L D R w h (.read y yp a) =
      fullReadOp L D R w h ((y, yp), a) := rfl

@[simp] theorem parsedHideOp_hide (w : Bool) (k : ℕ) (h : (L w).SupportedOn Finset.univ)
    (y yp x : ι → F) : parsedHideOp (PA := PA) L D R w k h (.hide y yp x) =
      hideOp (L w) k h (y, yp, x) ⊗ₖ (1 : Matrix (Fin R.d) (Fin R.d) ℂ) := rfl

end MIPRE.Introspection.Honest

end


