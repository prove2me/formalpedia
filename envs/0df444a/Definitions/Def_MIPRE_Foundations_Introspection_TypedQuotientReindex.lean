-- Prove2me | Definitions.Def_MIPRE_Foundations_Introspection_TypedQuotientReindex
-- name    : MIPRE_Foundations_Introspection_TypedQuotientReindex
-- status  : Definition
-- author  : @thomasvidick
-- created : 2026-10-17T03:01:20.079386+00:00
-- url     : https://prove2.me/theorems/00b11e26-c6d7-410a-9e58-5e0eaec5d9e8
-- title:
--   Definitions of TypedQuotientReindex: Exact game and PCC transport of quotient answers between coordinate types
-- statement:
--   The definitions of the module `MIPRE.Foundations.Introspection.TypedQuotientReindex` of the MIP\* = RE formalization (commit `70cbf1c` of vidick/MIPRE-formalization). # Exact game and PCC transport of quotient answers between coordinate types
--
--   **Definitions** (4): `MIPRE.Introspection.AuxiliaryQuotient.originalPCC`; `MIPRE.Introspection.AuxiliaryQuotient.reindexedGame`; `MIPRE.Introspection.AuxiliaryQuotient.reindexedPCC` (Carry the same honest operators to the concrete coordinate numbering.); `MIPRE.Introspection.AuxiliaryQuotient.reindexedStrategy`.
--
--   **Embedded lemmas** (2): the small results the bodies of these definitions need (proof fields, `simp` rules, decidability and finiteness instances), proved inside the bundle so that it imports no unproved statement: `originalPCC_dimension`, `reindexedPCC_dimension`.
--
--   **Formalization Note** The bundle is the module `MIPRE.Foundations.Introspection.TypedQuotientReindex` (`MIPRE/Foundations/Introspection/TypedQuotientReindex.lean`) with every declaration not listed removed, imports rewritten to the bundles of the module's import closure; the declarations keep their names, statements and bodies; the source module is split over 104 imported bundle(s).
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Foundations/Introspection/TypedQuotientReindex.lean

/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/Introspection/TypedQuotientReindex.lean (definition bundle: declarations the uploaded statements rest on);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.CharP.Two
import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Algebra.MvPolynomial.Degrees
import Mathlib.Algebra.MvPolynomial.SchwartzZippel
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Algebra.Polynomial.Monic
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
import Mathlib.Data.Matrix.Mul
import Mathlib.Data.Nat.Bits
import Mathlib.Data.Nat.Notation
import Mathlib.Data.Nat.Size
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Data.Real.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.FieldTheory.Finite.GaloisField
import Mathlib.LinearAlgebra.Basis.Defs
import Mathlib.LinearAlgebra.BilinearForm.Orthogonal
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.Pi
import Mathlib.RingTheory.Trace.Basic
import Mathlib.Tactic.DeriveFintype
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Definitions.Def_MIPRE_Foundations_Games
import Definitions.Def_MIPRE_Foundations_Distances
import Definitions.Def_MIPRE_Foundations_CL_Register
import Definitions.Def_MIPRE_Foundations_CL_Canonical
import Definitions.Def_MIPRE_Foundations_CL_Basic
import Definitions.Def_MIPRE_Foundations_Cost_Basic_B
import Definitions.Def_MIPRE_Foundations_Cost_Encoding_B
import Definitions.Def_MIPRE_Foundations_SAT_Circuit
import Definitions.Def_MIPRE_Foundations_Cost_PolyTime
import Definitions.Def_MIPRE_Foundations_CL_Closure_B
import Definitions.Def_MIPRE_Foundations_Cost_Closure
import Definitions.Def_MIPRE_Foundations_Cost_Loops_B
import Definitions.Def_MIPRE_Foundations_Cost_Fold
import Definitions.Def_MIPRE_Foundations_Cost_Unary
import Definitions.Def_MIPRE_Foundations_Cost_Numeric_B
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
import Definitions.Def_MIPRE_Foundations_CL_DetypingLaw
import Definitions.Def_MIPRE_Foundations_SampledGame
import Definitions.Def_MIPRE_Foundations_CL_DetypingGame
import Definitions.Def_MIPRE_Foundations_CL_Downsize
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryRepresentation
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryPolynomial
import Definitions.Def_MIPRE_Foundations_Cost_Binary
import Definitions.Def_MIPRE_Foundations_SAT_Formula
import Definitions.Def_MIPRE_Foundations_SAT_FmlLib
import Definitions.Def_MIPRE_Foundations_SAT_Flatten
import Definitions.Def_MIPRE_Foundations_Cost_Reader
import Definitions.Def_MIPRE_Foundations_SAT_FmlProg
import Definitions.Def_MIPRE_Foundations_SAT_ArrayProg
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryLinear
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryElimination
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryBasisProg
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryEchelon
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryEchelon_B
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryBasis
import Definitions.Def_MIPRE_Foundations_LowDegree_BinarySolve
import Definitions.Def_MIPRE_Foundations_LowDegree_BinarySolve_B
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryMatrixSolve
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryMatrixSolve_B
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryKernel
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
import Definitions.Def_MIPRE_Foundations_Introspection_HidingRigidity
import Definitions.Def_MIPRE_Foundations_Introspection_HidingMaps
import Definitions.Def_MIPRE_Foundations_Introspection_TypedPrefixChain
import Definitions.Def_MIPRE_Foundations_Introspection_ReadChainMaps
import Definitions.Def_MIPRE_Foundations_Introspection_AdaptiveResidual
import Definitions.Def_MIPRE_Foundations_Introspection_AuxiliaryCanonicalProgram
import Definitions.Def_MIPRE_Foundations_Introspection_AuxiliaryDualProgram
import Definitions.Def_MIPRE_Foundations_Introspection_AuxiliaryDualKernel
import Definitions.Def_MIPRE_Foundations_Introspection_AuxiliaryDualDecode
import Definitions.Def_MIPRE_Foundations_Introspection_AuxiliaryQuotientChecks
import Definitions.Def_MIPRE_Foundations_Introspection_PrefixGuard
import Definitions.Def_MIPRE_Foundations_Introspection_TypedQuotientPredicate
import Definitions.Def_MIPRE_Foundations_GameTransportByQuestion
import Definitions.Def_MIPRE_Foundations_Introspection_TypedQuotientGame
import Definitions.Def_MIPRE_Foundations_Introspection_AuxiliaryQuotientReindex
import Definitions.Def_MIPRE_Foundations_Introspection_PrefixGuardGame
import Theorems.Thm_MIPRE_CL_CLFun_eval_reindex
import Theorems.Thm_MIPRE_CL_CLFun_truncate_reindex
import Theorems.Thm_MIPRE_SyncStrategy_isPCC_relabel
import Theorems.Thm_MIPRE_SyncStrategy_value_relabel

/-! # Exact game and PCC transport of quotient answers between coordinate types -/

noncomputable section
namespace MIPRE.Introspection.AuxiliaryQuotient
open Finset CL CLChecks Classical
set_option linter.unusedSectionVars false
set_option backward.isDefEq.respectTransparency true
variable {F ι κ A PA PT Q : Type*} [Field F]
  [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] {ℓ : ℕ}

variable [Fintype F] [DecidableEq F] [Fintype A] [Fintype PA]
  [Fintype PT] [DecidableEq PT] [Fintype Q] [DecidableEq Q]
  (e : ι ≃ κ) (E : PT → PT → Bool) (X Z : PT)
  (P : PT → CLFun (ZMod 2) Q 3) (L : Bool → CLFun F ι ℓ)
  (project : PA → ι → F) (D : (ι → F) → (ι → F) → A → A → Bool)
  (DP : PT → PT → (Q → ZMod 2) → (Q → ZMod 2) → PA → PA → Bool)

abbrev reindexedGame := game E X Z P (fun w => (L w).reindex e)
  (fun a => reindexEquiv e (project a))
  (fun x y => D ((reindexEquiv e).symm x) ((reindexEquiv e).symm y)) DP

abbrev reindexedStrategy (S : TensorProductStrategy (game E X Z P L project D DP)) :
    TensorProductStrategy (reindexedGame e E X Z P L project D DP) :=
  S.relabel _ (Equiv.refl _) (Equiv.refl _) (answerEquiv e).symm (answerEquiv e).symm

variable [DecidableEq A] [DecidableEq PA]

abbrev originalPCC (S : SyncStrategy (reindexedGame e E X Z P L project D DP).doubled) :
    SyncStrategy (game E X Z P L project D DP).doubled :=
  S.relabel _ (Equiv.refl _) (answerEquiv e)

@[simp] theorem originalPCC_dimension
    (S : SyncStrategy (reindexedGame e E X Z P L project D DP).doubled) :
    (originalPCC e E X Z P L project D DP S).d = S.d := rfl

/-- Carry the same honest operators to the concrete coordinate numbering. -/
abbrev reindexedPCC (S : SyncStrategy (game E X Z P L project D DP).doubled) :
    SyncStrategy (reindexedGame e E X Z P L project D DP).doubled :=
  S.relabel _ (Equiv.refl _) (answerEquiv e).symm

@[simp] theorem reindexedPCC_dimension
    (S : SyncStrategy (game E X Z P L project D DP).doubled) :
    (reindexedPCC e E X Z P L project D DP S).d = S.d := rfl

end MIPRE.Introspection.AuxiliaryQuotient
end


