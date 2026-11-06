-- Prove2me | Definitions.Def_QEC_Semantics_Dynamics_ProtectedObservableDecay
-- name    : QEC_Semantics_Dynamics_ProtectedObservableDecay
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-05T10:50:50.875485+00:00
-- url     : https://prove2.me/theorems/2a0fe17e-a946-47ae-9386-58a5e5eefd1d
-- title:
--   Protected Observable Decay
-- statement:
--   Definitions and structural lemmas for Protected Observable Decay, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Dynamics/ProtectedObservableDecay.lean

import Definitions.Def_QEC_Semantics_Dynamics_FourBlockGenerator
import Definitions.Def_QEC_Semantics_Dynamics_ThermalEncoding
import Theorems.Thm_QEC_Semantics_traceNorm_add_le
import Theorems.Thm_QEC_Semantics_traceNorm_eq_zero_iff
import Theorems.Thm_QEC_Semantics_traceNorm_neg
import Theorems.Thm_QEC_Semantics_traceNorm_smul
attribute [local simp] QEC.Semantics.traceNorm_neg


set_option autoImplicit false
universe u v
namespace QEC.Semantics
open scoped ComplexOrder
noncomputable section
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 100000
variable {H : Type u} {ι : Type v}
variable [NormedAddCommGroup H] [InnerProductSpace ℂ H] [FiniteQuantumSystem H]
noncomputable local instance clbtFiniteQuantumSystemComplete : CompleteSpace H :=
  FiniteDimensional.complete ℂ H
def CLBTTraceNormedOperator (H : Type u) [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [FiniteQuantumSystem H] := Operator H
instance : AddCommGroup (CLBTTraceNormedOperator H) :=
  inferInstanceAs (AddCommGroup (Operator H))
instance : Module ℂ (CLBTTraceNormedOperator H) :=
  inferInstanceAs (Module ℂ (Operator H))
instance : Module ℝ (CLBTTraceNormedOperator H) :=
  Module.restrictScalars ℝ ℂ (CLBTTraceNormedOperator H)
def clbtTraceNormedOperatorSeminorm :
    AddGroupSeminorm (CLBTTraceNormedOperator H) where
  toFun A := traceNorm (H := H) A
  map_zero' := (traceNorm_eq_zero_iff (H := H) 0).2 rfl
  neg' := traceNorm_neg
  add_le' := traceNorm_add_le
instance clbtTraceNormedOperatorSeminormedAddCommGroup :
    SeminormedAddCommGroup (CLBTTraceNormedOperator H) :=
  clbtTraceNormedOperatorSeminorm.toSeminormedAddCommGroup
instance clbtTraceNormedOperatorNormedAddCommGroup :
    NormedAddCommGroup (CLBTTraceNormedOperator H) :=
  NormedAddCommGroup.ofSeparation fun A hA =>
    (traceNorm_eq_zero_iff (H := H) A).1 hA
instance clbtTraceNormedOperatorNormedSpaceComplex :
    NormedSpace ℂ (CLBTTraceNormedOperator H) where
  norm_smul_le c A := by
    change traceNorm (c • (A : Operator H)) ≤ ‖c‖ * traceNorm (A : Operator H)
    exact le_of_eq (traceNorm_smul c A)
instance clbtTraceNormedOperatorNormedSpaceReal :
    NormedSpace ℝ (CLBTTraceNormedOperator H) :=
  NormedSpace.restrictScalars ℝ ℂ (CLBTTraceNormedOperator H)
def clbtTraceNormedOperatorToOperator :
    CLBTTraceNormedOperator H →ₗ[ℂ] Operator H :=
  LinearMap.id
instance clbtTraceNormedOperatorFiniteDimensional :
    FiniteDimensional ℂ (CLBTTraceNormedOperator H) :=
  FiniteDimensional.of_injective clbtTraceNormedOperatorToOperator
    (LinearMap.ker_eq_bot.mp rfl)
noncomputable instance clbtTraceNormedOperatorComplete :
    CompleteSpace (CLBTTraceNormedOperator H) :=
  FiniteDimensional.complete ℂ (CLBTTraceNormedOperator H)
noncomputable def continuousOperatorToCLBTTraceNormed :
    ContinuousOperator H →L[ℝ] CLBTTraceNormedOperator H :=
  LinearMap.toContinuousLinearMap
    { toFun := fun A => A.toLinearMap
      map_add' := by intro A B; rfl
      map_smul' := by
        intro r A
        change ((r : ℂ) • A).toLinearMap = (r : ℂ) • A.toLinearMap
        rfl }
noncomputable instance
    ThermalEncoding.PauliLikePair.auxiliarySpaceNontrivial
    {K : Type}
    [NormedAddCommGroup K] [InnerProductSpace ℂ K] [FiniteQuantumSystem K]
    [Nontrivial K]
    (logical : ThermalEncoding.PauliLikePair K) :
    Nontrivial logical.AuxiliarySpace := by
  let e : (logical.AuxiliarySpace × logical.AuxiliarySpace) ≃ₗ[ℂ] K :=
    (LinearEquiv.prodCongr (LinearEquiv.refl ℂ logical.AuxiliarySpace)
      logical.xEigenspaceEquiv).trans
        (Submodule.prodEquivOfIsCompl
          (Module.End.eigenspace logical.z (1 : ℂ))
          (Module.End.eigenspace logical.z (-1 : ℂ))
          logical.positive_negative_isCompl)
  have hprod : Nontrivial
      (logical.AuxiliarySpace × logical.AuxiliarySpace) :=
    e.toEquiv.nontrivial
  rw [← not_subsingleton_iff_nontrivial]
  intro haux
  letI : Subsingleton logical.AuxiliarySpace := haux
  exact (not_nontrivial
    (logical.AuxiliarySpace × logical.AuxiliarySpace)) hprod
noncomputable def ThermalEncoding.PauliLikePair.liftQubitOperator
    {K : Type}
    [NormedAddCommGroup K] [InnerProductSpace ℂ K] [FiniteQuantumSystem K]
    (logical : ThermalEncoding.PauliLikePair K)
    (A : Operator Qubit.QubitSpace) : Operator K :=
  logical.factorization.conjOperator
    (TensorProduct.map A (1 : Operator logical.AuxiliarySpace))
end
end QEC.Semantics


