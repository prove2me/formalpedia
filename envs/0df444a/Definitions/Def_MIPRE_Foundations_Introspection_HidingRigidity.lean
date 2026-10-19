-- Prove2me | Definitions.Def_MIPRE_Foundations_Introspection_HidingRigidity
-- name    : MIPRE_Foundations_Introspection_HidingRigidity
-- status  : Definition
-- author  : @thomasvidick
-- created : 2026-10-17T01:54:27.990557+00:00
-- url     : https://prove2.me/theorems/3d9feb3d-d40f-4a21-8886-93db3c654381
-- title:
--   Definitions of HidingRigidity: The conditional estimate for the actual adjacent hiding test The earlier answer is processed using the question…
-- statement:
--   The definitions of the module `MIPRE.Foundations.Introspection.HidingRigidity` of the MIP\* = RE formalization (commit `70cbf1c` of vidick/MIPRE-formalization). The conditional estimate for the actual adjacent hiding test. The earlier answer is processed using the question reported in the later answer. This is a conditional measurement, not a single fixed coarse-graining. The resulting estimate is derived from the parsed game and its actual uniform ordered-edge law, including the malformed-answer outcomes.
--
--   **Definitions** (4): `MIPRE.Introspection.TypedEstimates.hidingNextCondition` (Retain exactly the later hiding answer's preceding question prefix as the conditioning index.); `MIPRE.Introspection.TypedEstimates.hidingNextEarlier` (Process the earlier answer using the later reported question.); `MIPRE.Introspection.TypedEstimates.hidingNextLater` (The actual coarse later answer.); `MIPRE.Introspection.conditionalCoarseDistance` (Squared error of the conditional coarse comparison, retaining Bob's conditioning index and summing every coarse outcome.).
--
--   **Formalization Note** The bundle is the module `MIPRE.Foundations.Introspection.HidingRigidity` (`MIPRE/Foundations/Introspection/HidingRigidity.lean`) with every declaration not listed removed, imports rewritten to the bundles of the module's import closure; the declarations keep their names, statements and bodies; the source module is split over 58 imported bundle(s).
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Foundations/Introspection/HidingRigidity.lean

/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/Introspection/HidingRigidity.lean (definition bundle: declarations the uploaded statements rest on);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
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
import Mathlib.Data.Finset.Image
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
import Definitions.Def_MIPRE_Foundations_CL_Closure_B
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
import Definitions.Def_MIPRE_Foundations_CL_Embedding
import Definitions.Def_MIPRE_Foundations_CL_Graph
import Definitions.Def_MIPRE_Foundations_CL_Detyping
import Definitions.Def_MIPRE_Foundations_CL_DetypingLaw
import Definitions.Def_MIPRE_Foundations_SampledGame
import Definitions.Def_MIPRE_Foundations_CL_DetypingGame
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
import Definitions.Def_MIPRE_Foundations_Introspection_TypeGraph
import Definitions.Def_MIPRE_Foundations_Introspection_TypedPresentation
import Definitions.Def_MIPRE_Foundations_Introspection_TypedEstimates
import Theorems.Thm_MIPRE_POVM_posSemidef
import Theorems.Thm_MIPRE_POVM_sum_val

/-! # The conditional estimate for the actual adjacent hiding test

The earlier answer is processed using the question reported in the later
answer. This is a conditional measurement, not a single fixed coarse-graining.
The resulting estimate is derived from the parsed game and its actual uniform
ordered-edge law, including the malformed-answer outcomes.
-/

noncomputable section

namespace MIPRE.Introspection

open Finset Matrix Classical
open scoped Kronecker ComplexOrder MatrixOrder

set_option linter.unusedSectionVars false

section Conditional

variable {H K A B Y Z : Type*}
  [Fintype H] [DecidableEq H] [Fintype K] [DecidableEq K]
  [Fintype A] [Fintype B] [DecidableEq B]
  [Fintype Y] [DecidableEq Y] [Fintype Z] [DecidableEq Z]

/-- Squared error of the conditional coarse comparison, retaining Bob's
conditioning index and summing every coarse outcome. -/
def conditionalCoarseDistance (ψ : H × K → ℂ) (M : POVM A H) (N : POVM B K)
    (f : Y → A → Z) (g : B → Y × Z) : ℝ :=
  ∑ p : Y × Z, snorm ψ
    (bOp (((N.map g).mats p).val) -
      (((M.map (f p.1)).mats p.2).val ⊗ₖ (∑ z, ((N.map g).mats (p.1, z)).val))) ^ 2

end Conditional

namespace CLChecks

variable {F ι : Type*} [Field F] [Fintype ι] [DecidableEq ι] {ℓ : ℕ}

end CLChecks

namespace TypedEstimates

section Parsed

variable {PauliType PauliAnswer F ι κ A H K : Type*}
  [Fintype PauliType] [DecidableEq PauliType] [Fintype PauliAnswer]
  [Field F] [Fintype F] [DecidableEq F] [Fintype ι] [DecidableEq ι]
  [Fintype κ] [DecidableEq κ] [Fintype A]
  [Fintype H] [DecidableEq H] [Fintype K] [DecidableEq K] {ℓ : ℕ}

/-- Retain exactly the later hiding answer's preceding question prefix as
the conditioning index. Malformed answers retain a separate index. -/
def hidingNextCondition (P : CL.CLFun F ι ℓ) (k : ℕ) :
    ParsedAnswer (ι → F) A PauliAnswer → Option (ι → F)
  | .hide y _ _ => some (P.outputPrefix (k + 1) y)
  | _ => none

/-- Process the earlier answer using the later reported question. The output
retains the earlier prefix, the new dual readout, and the untouched tail. -/
def hidingNextEarlier (P : CL.CLFun F ι ℓ) (k : ℕ) (v : Option (ι → F)) :
    ParsedAnswer (ι → F) A PauliAnswer → Option ((ι → F) × (ι → F) × (ι → F))
  | .hide y _ x => v.map fun z =>
      (P.outputPrefix k y, CLChecks.dualReadout P (k + 1) z x,
        CL.proj (CLChecks.prefixRegister P (k + 2) z)ᶜ x)
  | _ => none

/-- The actual coarse later answer. Both the factor for the new dual output
and the tail projector use that answer's own reported question. -/
def hidingNextLater (P : CL.CLFun F ι ℓ) (k : ℕ)
    (a : ParsedAnswer (ι → F) A PauliAnswer) :
    Option (ι → F) × Option ((ι → F) × (ι → F) × (ι → F)) :=
  (hidingNextCondition P k a, match a with
    | .hide y yp x => some
        (P.outputPrefix k y,
          CL.proj (P.factorOfPrefix (k + 1) (P.outputPrefix (k + 1) y)) yp,
          CL.proj (CLChecks.prefixRegister P (k + 2) y)ᶜ x)
    | _ => none)

end Parsed

end TypedEstimates

end MIPRE.Introspection

end


