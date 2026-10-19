-- Prove2me | Definitions.Def_MIPRE_Foundations_Introspection_SourcePaddingValue
-- name    : MIPRE_Foundations_Introspection_SourcePaddingValue
-- status  : Definition
-- author  : @thomasvidick
-- created : 2026-10-17T01:57:21.026088+00:00
-- url     : https://prove2.me/theorems/bcc27df6-6860-4dd2-817f-b210d1a714ac
-- title:
--   Definitions of SourcePaddingValue: Removing padding from arbitrary source-game strategies Canonical zero-extension of questions pulls every padded…
-- statement:
--   The definitions of the module `MIPRE.Foundations.Introspection.SourcePaddingValue` of the MIP\* = RE formalization (commit `70cbf1c` of vidick/MIPRE-formalization). Removing padding from arbitrary source-game strategies. Canonical zero-extension of questions pulls every padded strategy back with exactly its state, dimensions, and value. The unused seed coordinates average out uniformly; this is not restricted to perfect strategies or PCC strategies.
--
--   **Definitions** (2): `MIPRE.Introspection.SourcePadding.restrictStrategy` (Ask the padded strategy the canonical extension of the original question.); `MIPRE.Introspection.SourcePadding.seedSplit`.
--
--   **Formalization Note** The bundle is the module `MIPRE.Foundations.Introspection.SourcePaddingValue` (`MIPRE/Foundations/Introspection/SourcePaddingValue.lean`) with every declaration not listed removed, imports rewritten to the bundles of the module's import closure; the declarations keep their names, statements and bodies; the source module is split over 63 imported bundle(s).
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Foundations/Introspection/SourcePaddingValue.lean

/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/Introspection/SourcePaddingValue.lean (definition bundle: declarations the uploaded statements rest on);
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
import Definitions.Def_MIPRE_Foundations_CL_Embedding
import Definitions.Def_MIPRE_Foundations_CL_Graph
import Definitions.Def_MIPRE_Foundations_CL_Detyping
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
import Definitions.Def_MIPRE_Foundations_Introspection_SourcePadding

/-! # Removing padding from arbitrary source-game strategies

Canonical zero-extension of questions pulls every padded strategy back with
exactly its state, dimensions, and value. The unused seed coordinates average
out uniformly; this is not restricted to perfect strategies or PCC strategies.
-/

noncomputable section
namespace MIPRE.Introspection.SourcePadding
open Matrix Finset Classical
set_option linter.unusedSectionVars false

variable {F I J A : Type*} [Field F] [Fintype F] [DecidableEq F]
  [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J] [Fintype A] [DecidableEq A]
  {ℓ : ℕ} (e : I ↪ J)

def seedSplit : (J → F) ≃ ((I → F) × ({j : J // j ∉ Set.range e} → F)) where
  toFun x := (CL.pull e x, fun j => x j.val)
  invFun p j := if h : j ∈ Set.range e then p.1 h.choose else p.2 ⟨j,h⟩
  left_inv x := by
    funext j
    dsimp only
    split_ifs with h
    · exact congrArg x h.choose_spec
    · rfl
  right_inv p := by
    apply Prod.ext
    · funext i
      have h : e i ∈ Set.range e := ⟨i,rfl⟩
      simp only [CL.pull, dif_pos h]
      exact congrArg p.1 (e.injective h.choose_spec)
    · funext j
      simp only [dif_neg j.property]

variable (L : Bool → CL.CLFun F I ℓ) (D : (I → F) → (I → F) → A → A → Bool)

/-- Ask the padded strategy the canonical extension of the original question. -/
def restrictStrategy (S : TensorProductStrategy (Honest.sourceGame (family e L) (decider e D))) :
    TensorProductStrategy (Honest.sourceGame L D) :=
  S.relabel _ (CL.push e) (CL.push e) (Equiv.refl A) (Equiv.refl A)

end MIPRE.Introspection.SourcePadding
end


