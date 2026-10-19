-- Prove2me | Definitions.Def_MIPRE_Foundations_Introspection_HidingInduction
-- name    : MIPRE_Foundations_Introspection_HidingInduction
-- status  : Definition
-- author  : @thomasvidick
-- created : 2026-10-17T03:40:22.725592+00:00
-- url     : https://prove2.me/theorems/ca6dfe27-f754-49d2-a83e-203def88477a
-- title:
--   Definitions of HidingInduction: One product-form induction step from the coarse joint measurements The two commutators needed by Pauli mixing are…
-- statement:
--   The definitions of the module `MIPRE.Foundations.Introspection.HidingInduction` of the MIP\* = RE formalization (commit `70cbf1c` of vidick/MIPRE-formalization). One product-form induction step from the coarse joint measurements. The two commutators needed by Pauli mixing are derived from the tested marginals of actual projective measurements on the other party. Coarse-graining is performed before applying the commutation analysis. The error does not depend on the size of a coarse-graining fibre. The final theorem constructs the residual POVMs on `V \ U`, from averaged cross-party errors on one ambient EPR state. Identifying these measurements with the prefix-conditioned introspection strategy is a separate obligation.
--
--   **Definitions** (4): `MIPRE.Introspection.ambientProjectivePOVM` (The actual ambient POVM of a projective local measurement.); `MIPRE.Introspection.ambientReadoutPOVM` (The selected Pauli readout as a normalized positive measurement.); `MIPRE.Introspection.coarseJointLeftError` (Consistency with the first marginal of an actual coarse joint measurement.); `MIPRE.Introspection.coarseJointRightError` (Consistency with the second marginal of the same coarse joint measurement.).
--
--   **Embedded lemmas** (4): the small results the bodies of these definitions need (proof fields, `simp` rules, decidability and finiteness instances), proved inside the bundle so that it imports no unproved statement: `ambientOperator_isPVM`, `ambientProjectivePOVM_mats`, `ambientReadoutPOVM_mats`, `ambientReadout_isPVM`.
--
--   **Formalization Note** The bundle is the module `MIPRE.Foundations.Introspection.HidingInduction` (`MIPRE/Foundations/Introspection/HidingInduction.lean`) with every declaration not listed removed, imports rewritten to the bundles of the module's import closure; the declarations keep their names, statements and bodies; the source module is split over 42 imported bundle(s).
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Foundations/Introspection/HidingInduction.lean

/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/Introspection/HidingInduction.lean (definition bundle: declarations the uploaded statements rest on);
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
import Definitions.Def_MIPRE_Foundations_Introspection_AmbientMixing
import Theorems.Thm_MIPRE_Introspection_linear_measurement_isPVM
import Theorems.Thm_MIPRE_Introspection_registerOp_isPVM
import Theorems.Thm_MIPRE_IsPVM_aOp

/-! # One product-form induction step from the coarse joint measurements

The two commutators needed by Pauli mixing are derived from the tested
marginals of actual projective measurements on the other party. Coarse-graining
is performed before applying the commutation analysis. The error does not
depend on the size of a coarse-graining fibre.

The final theorem constructs the residual POVMs on `V \ U`, from averaged
cross-party errors on one ambient EPR state. Identifying these measurements
with the prefix-conditioned introspection strategy is a separate obligation.
-/

noncomputable section

namespace MIPRE.Introspection

open Finset Matrix Weyl Classical
open scoped Kronecker

set_option linter.unusedSectionVars false

section Coarse

variable {H K A B C O : Type*}
  [Fintype H] [DecidableEq H] [Fintype K] [DecidableEq K]
  [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
  [Fintype C] [DecidableEq C] [Fintype O] [DecidableEq O]

/-- Consistency with the first marginal of an actual coarse joint measurement. -/
def coarseJointLeftError (ψ : H × K → ℂ) (M : POVM A H) (B : POVM O K)
    (f : O → A × C) : ℝ :=
  ∑ a, xSqNorm ψ (M.mats a).val (∑ c, ((B.map f).mats (a, c)).val)

/-- Consistency with the second marginal of the same coarse joint measurement. -/
def coarseJointRightError (ψ : H × K → ℂ) (N : POVM C H) (B : POVM O K)
    (f : O → A × C) : ℝ :=
  ∑ c, xSqNorm ψ (N.mats c).val (∑ a, ((B.map f).mats (a, c)).val)

end Coarse

section Ambient

variable {ι F H K A : Type*} [Fintype ι] [DecidableEq ι]
  [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F]
  [Fintype H] [DecidableEq H] [Fintype K] [DecidableEq K]
  [Fintype A] [DecidableEq A]

/-- Embedding in the ambient register preserves the projective measurement. -/
theorem ambientOperator_isPVM (V : Finset ι)
    {M : A → Matrix ((V → F) × H) ((V → F) × H) ℂ} (hM : IsPVM M) :
    IsPVM (fun a => ambientOperator V (M a)) := by
  apply registerOp_isPVM
  exact hM.aOp

/-- The actual ambient POVM of a projective local measurement. -/
def ambientProjectivePOVM (V : Finset ι) (M : POVM A ((V → F) × H))
    (hM : IsPVM (fun a => (M.mats a).val)) : POVM A ((ι → F) × H) :=
  (ambientOperator_isPVM V hM).toPOVM

@[simp] theorem ambientProjectivePOVM_mats (V : Finset ι)
    (M : POVM A ((V → F) × H)) (hM : IsPVM (fun a => (M.mats a).val)) (a : A) :
    ((ambientProjectivePOVM V M hM).mats a).val = ambientOperator V (M.mats a).val := rfl

/-- Projectivity of a selected linear Pauli readout in the original register. -/
theorem ambientReadout_isPVM (U V : Finset ι) (hUV : U ⊆ V)
    (w : (Fin (Fintype.card U) → F) →
      Matrix (Fin (Fintype.card U) → F) (Fin (Fintype.card U) → F) ℂ)
    (hw : IsWeylFamily w)
    (L : (Fin (Fintype.card U) → F) →ₗ[F] (Fin (Fintype.card U) → F)) :
    IsPVM (ambientReadout (H := H) U V hUV w L) :=
  ambientOperator_isPVM V
    (registerOp_isPVM (registerParty (coordinateSplit U V hUV) H)
      (linear_measurement_isPVM w hw L).aOp)

/-- The selected Pauli readout as a normalized positive measurement. -/
def ambientReadoutPOVM (U V : Finset ι) (hUV : U ⊆ V)
    (w : (Fin (Fintype.card U) → F) →
      Matrix (Fin (Fintype.card U) → F) (Fin (Fintype.card U) → F) ℂ)
    (hw : IsWeylFamily w)
    (L : (Fin (Fintype.card U) → F) →ₗ[F] (Fin (Fintype.card U) → F)) :
    POVM (Fin (Fintype.card U) → F) ((ι → F) × H) :=
  (ambientReadout_isPVM U V hUV w hw L).toPOVM

@[simp] theorem ambientReadoutPOVM_mats (U V : Finset ι) (hUV : U ⊆ V)
    (w : (Fin (Fintype.card U) → F) →
      Matrix (Fin (Fintype.card U) → F) (Fin (Fintype.card U) → F) ℂ)
    (hw : IsWeylFamily w)
    (L : (Fin (Fintype.card U) → F) →ₗ[F] (Fin (Fintype.card U) → F))
    (y : Fin (Fintype.card U) → F) :
    ((ambientReadoutPOVM (H := H) U V hUV w hw L).mats y).val =
      ambientReadout U V hUV w L y := rfl

variable {B C : Type*} [Fintype B] [DecidableEq B] [Fintype C] [DecidableEq C]

end Ambient

end MIPRE.Introspection

end


