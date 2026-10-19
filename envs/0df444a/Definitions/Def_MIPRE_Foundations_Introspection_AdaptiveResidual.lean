-- Prove2me | Definitions.Def_MIPRE_Foundations_Introspection_AdaptiveResidual
-- name    : MIPRE_Foundations_Introspection_AdaptiveResidual
-- status  : Definition
-- author  : @thomasvidick
-- created : 2026-10-17T02:02:24.073207+00:00
-- url     : https://prove2.me/theorems/fc5c97b2-25d5-4059-bb0f-0b3778332be7
-- title:
--   Definitions of AdaptiveResidual: The actual CL continuation on the unvisited registers The residual presentation follows a claimed output, including an…
-- statement:
--   The definitions of the module `MIPRE.Foundations.Introspection.AdaptiveResidual` of the MIP\* = RE formalization (commit `70cbf1c` of vidick/MIPRE-formalization). The actual CL continuation on the unvisited registers. The residual presentation follows a claimed output, including an off-image one. It acts only on the complement of the registers already visited. The next local map and register are computed from the original presentation.
--
--   **Definitions** (3): `MIPRE.Introspection.CLChecks.residual` (Continue after `k` reported components; the remaining depth is `ℓ-k`.); `MIPRE.Introspection.CLChecks.residualDepth` (Recursively compute the remaining depth, retaining definitional equations.); `MIPRE.Introspection.CLChecks.stageLinear` (The local linear map at a claimed prefix, with its actual finite-set support.).
--
--   **Embedded lemmas** (1): the small results the bodies of these definitions need (proof fields, `simp` rules, decidability and finiteness instances), proved inside the bundle so that it imports no unproved statement: `residual_zero`.
--
--   **Formalization Note** The bundle is the module `MIPRE.Foundations.Introspection.AdaptiveResidual` (`MIPRE/Foundations/Introspection/AdaptiveResidual.lean`) with every declaration not listed removed, imports rewritten to the bundles of the module's import closure; the declarations keep their names, statements and bodies; the source module is split over 62 imported bundle(s).
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Foundations/Introspection/AdaptiveResidual.lean

/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/Introspection/AdaptiveResidual.lean (definition bundle: declarations the uploaded statements rest on);
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
import Definitions.Def_MIPRE_Foundations_Introspection_HidingRigidity
import Definitions.Def_MIPRE_Foundations_Introspection_HidingMaps
import Definitions.Def_MIPRE_Foundations_Introspection_TypedPrefixChain
import Definitions.Def_MIPRE_Foundations_Introspection_ReadChainMaps

/-! # The actual CL continuation on the unvisited registers

The residual presentation follows a claimed output, including an off-image
one. It acts only on the complement of the registers already visited.
The next local map and register are computed from the original presentation.
-/

noncomputable section

namespace MIPRE.Introspection.CLChecks

open Finset Classical
set_option linter.unusedSectionVars false

variable {F ι : Type*} [Field F] [Fintype ι] [DecidableEq ι] {ℓ : ℕ}

/-- Recursively compute the remaining depth, retaining definitional equations. -/
def residualDepth : ℕ → ℕ → ℕ
  | 0, ℓ => ℓ
  | _ + 1, 0 => 0
  | k + 1, ℓ + 1 => residualDepth k ℓ
termination_by structural k _ => k

/-- Continue after `k` reported components; the remaining depth is `ℓ-k`. -/
def residual : {ℓ : ℕ} → CL.CLFun F ι ℓ → (k : ℕ) → (ι → F) →
    CL.CLFun F ι (residualDepth k ℓ)
  | _, P, 0, _ => P
  | _, .zero, _ + 1, _ => .zero
  | _, .cons S _ next, k + 1, y => residual (next (CL.proj S y)) k (CL.proj Sᶜ y)

@[simp] theorem residual_zero (P : CL.CLFun F ι ℓ) (y : ι → F) : residual P 0 y = P := by
  cases P <;> rfl

/-- The local linear map at a claimed prefix, with its actual finite-set support. -/
def stageLinear : {ℓ : ℕ} → (P : CL.CLFun F ι ℓ) → (k : ℕ) →
    (y : ι → F) → CL.RegLinear F (P.factorOfPrefix k y)
  | _, .zero, _, _ => 0
  | _, .cons _ L _, 0, _ => L
  | _, .cons S _ next, k + 1, y => stageLinear (next (CL.proj S y)) k (CL.proj Sᶜ y)

end MIPRE.Introspection.CLChecks

end


