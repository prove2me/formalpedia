-- Prove2me | Definitions.Def_QEC_Semantics_ErrorCorrection_QuditReplacement
-- name    : QEC_Semantics_ErrorCorrection_QuditReplacement
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-05T11:47:28.974606+00:00
-- url     : https://prove2.me/theorems/1364e7e1-e135-4f86-a886-d7a71fcd6063
-- title:
--   Qudit Replacement
-- statement:
--   Definitions and structural lemmas for Qudit Replacement, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/ErrorCorrection/QuditReplacement.lean

import Definitions.Def_QEC_Semantics_ErrorCorrection_QuditSubsystem
import Definitions.Def_QEC_Semantics_Channels_Kraus
import Theorems.Thm_QEC_Semantics_QuantumChannel_comp_apply
import Theorems.Thm_QEC_Semantics_QuantumChannel_id_apply
import Theorems.Thm_QEC_Semantics_QuditSubsystem_additionalRetainedFactorSwap_apply_tmul
import Theorems.Thm_QEC_Semantics_Qudit_finrank_quditRegister_ne_zero
import Theorems.Thm_QEC_Semantics_UnitaryTransport_conjDensity_apply
import Theorems.Thm_QEC_Semantics_UnitaryTransport_conjDensity_toOperator
import Theorems.Thm_QEC_Semantics_partialTraceRightRaw_cptp_toLinearMap
import Theorems.Thm_QEC_Semantics_partialTraceRightRaw_mapDensity_toOperator
attribute [local simp] QEC.Semantics.QuantumChannel.comp_apply
attribute [local simp] QEC.Semantics.QuantumChannel.id_apply
attribute [local simp] QEC.Semantics.QuditSubsystem.additionalRetainedFactorSwap_apply_tmul
attribute [local simp] QEC.Semantics.UnitaryTransport.conjDensity_apply
attribute [local simp] QEC.Semantics.UnitaryTransport.conjDensity_toOperator
attribute [local simp] QEC.Semantics.partialTraceRightRaw_cptp_toLinearMap
attribute [local simp] QEC.Semantics.partialTraceRightRaw_mapDensity_toOperator


set_option autoImplicit false
noncomputable section
namespace QEC
namespace Semantics
namespace QuditSubsystem
open Classical
open scoped BigOperators ComplexOrder TensorProduct
universe u v
variable {ι : Type u} [Fintype ι] [DecidableEq ι]
variable {q : ι → Nat}
noncomputable def prepareFactorizedBranch (S : QuditSubsystem q) (u : S.selectedSystem) :
    S.complementSystem →ₗ[Complex] S.factorizedSystem :=
  (TensorProduct.mk Complex S.selectedSystem S.complementSystem) u
@[simp]
theorem prepareFactorizedBranch_apply (S : QuditSubsystem q) (u : S.selectedSystem)
    (k : S.complementSystem) :
    S.prepareFactorizedBranch u k = u ⊗ₜ[Complex] k :=
  rfl
noncomputable def prepareFactorizedKraus (S : QuditSubsystem q) {m : Nat}
    (u : Fin m → S.selectedSystem) :
    FiniteKrausFamily (Fin m) S.complementSystem S.factorizedSystem where
  operator i := S.prepareFactorizedBranch (u i)
@[simp]
theorem prepareFactorizedKraus_operator (S : QuditSubsystem q) {m : Nat}
    (u : Fin m → S.selectedSystem) (i : Fin m) :
    (S.prepareFactorizedKraus u).operator i = S.prepareFactorizedBranch (u i) :=
  rfl
set_option maxHeartbeats 800000 in
theorem adjoint_prepareFactorizedBranch_comp (S : QuditSubsystem q) (u : S.selectedSystem) :
    (LinearMap.adjoint (S.prepareFactorizedBranch u)).comp (S.prepareFactorizedBranch u) =
      (inner Complex u u) • (1 : Operator S.complementSystem) := by
  apply LinearMap.ext
  intro k
  apply (ext_iff_inner_left Complex).mpr
  intro l
  change inner Complex l (LinearMap.adjoint (S.prepareFactorizedBranch u)
    (S.prepareFactorizedBranch u k)) =
      inner Complex l (((inner Complex u u) • (1 : Operator S.complementSystem)) k)
  rw [LinearMap.adjoint_inner_right]
  simp [prepareFactorizedBranch, TensorProduct.inner_tmul]
theorem prepareFactorizedKraus_complete_of_trace_one (S : QuditSubsystem q) {m : Nat}
    (u : Fin m → S.selectedSystem)
    (htrace : ∑ i, inner Complex (u i) (u i) = 1) :
    (S.prepareFactorizedKraus u).Complete := by
  rw [FiniteKrausFamily.Complete]
  simp only [prepareFactorizedKraus_operator, S.adjoint_prepareFactorizedBranch_comp]
  apply LinearMap.ext
  intro k
  calc
    (∑ i, (inner Complex (u i) (u i) • (1 : Operator S.complementSystem))) k =
        (∑ i, inner Complex (u i) (u i)) • k := by
          simp [Finset.sum_smul]
    _ = k := by rw [htrace]; simp
theorem density_exists_rankOne_ensemble (S : QuditSubsystem q)
    (rho : DensityOperator S.selectedSystem) :
    ∃ (m : Nat) (u : Fin m → S.selectedSystem),
      rho.toOperator = ∑ i, (InnerProductSpace.rankOne Complex (u i) (u i)).toLinearMap := by
  have hpositive : (LinearMap.toContinuousLinearMap rho.toOperator).IsPositive :=
    (LinearMap.isPositive_toContinuousLinearMap_iff rho.toOperator).2 rho.positive
  rcases (ContinuousLinearMap.isPositive_iff_eq_sum_rankOne).1 hpositive with ⟨m, u, hu⟩
  refine ⟨m, u, ?_⟩
  simpa using congrArg ContinuousLinearMap.toLinearMap hu
theorem rankOne_ensemble_trace_one (S : QuditSubsystem q) {m : Nat}
    (u : Fin m → S.selectedSystem)
    (rho : DensityOperator S.selectedSystem)
    (hensemble : rho.toOperator =
      ∑ i, (InnerProductSpace.rankOne Complex (u i) (u i)).toLinearMap) :
    ∑ i, inner Complex (u i) (u i) = 1 := by
  have htrace := rho.trace_one
  rw [hensemble] at htrace
  simpa [map_sum, InnerProductSpace.trace_rankOne] using htrace
noncomputable def densityEnsembleSize (S : QuditSubsystem q)
    (rho : DensityOperator S.selectedSystem) : Nat :=
  Classical.choose (S.density_exists_rankOne_ensemble rho)
noncomputable def densityEnsembleVectors (S : QuditSubsystem q)
    (rho : DensityOperator S.selectedSystem) :
    Fin (S.densityEnsembleSize rho) → S.selectedSystem :=
  Classical.choose (Classical.choose_spec (S.density_exists_rankOne_ensemble rho))
theorem densityEnsemble_specification (S : QuditSubsystem q)
    (rho : DensityOperator S.selectedSystem) :
    rho.toOperator = ∑ i,
      (InnerProductSpace.rankOne Complex (S.densityEnsembleVectors rho i)
        (S.densityEnsembleVectors rho i)).toLinearMap :=
  Classical.choose_spec (Classical.choose_spec (S.density_exists_rankOne_ensemble rho))
theorem densityEnsemble_trace_one (S : QuditSubsystem q)
    (rho : DensityOperator S.selectedSystem) :
    ∑ i, inner Complex (S.densityEnsembleVectors rho i) (S.densityEnsembleVectors rho i) = 1 :=
  S.rankOne_ensemble_trace_one (S.densityEnsembleVectors rho) rho
    (S.densityEnsemble_specification rho)
noncomputable def prepareFactorized (S : QuditSubsystem q)
    (rho : DensityOperator S.selectedSystem) :
    QuantumChannel S.complementSystem S.factorizedSystem :=
  (S.prepareFactorizedKraus (S.densityEnsembleVectors rho)).toQuantumChannel
    (S.prepareFactorizedKraus_complete_of_trace_one (S.densityEnsembleVectors rho)
      (S.densityEnsemble_trace_one rho))
noncomputable def prepareSelected (S : QuditSubsystem q)
    (rho : DensityOperator S.selectedSystem) :
    QuantumChannel S.complementSystem (Qudit.QuditRegister q) :=
  QuantumChannel.comp (QuantumChannel.unitaryConj S.registerFactorization.symm)
    (S.prepareFactorized rho)
noncomputable def maximallyMixedSelected (S : QuditSubsystem q) (hq : ∀ i, 0 < q i) :
    DensityOperator S.selectedSystem where
  toOperator :=
    ((Module.finrank Complex S.selectedSystem : Complex)⁻¹) •
      (1 : Operator S.selectedSystem)
  positive := by
    have hdim_nonneg : 0 ≤ (Module.finrank Complex S.selectedSystem : Complex) := by
      exact_mod_cast Nat.zero_le (Module.finrank Complex S.selectedSystem)
    exact LinearMap.isPositive_one.smul_of_nonneg ((inv_nonneg).2 hdim_nonneg)
  trace_one := by
    have hdim : (Module.finrank Complex S.selectedSystem : Complex) ≠ 0 :=
      Qudit.finrank_quditRegister_ne_zero S.selectedDimensions (fun i => hq i)
    rw [map_smul, LinearMap.trace_one]
    exact inv_mul_cancel₀ hdim
noncomputable def replacementAfterErasureWith (S : QuditSubsystem q)
    (rho : DensityOperator S.selectedSystem) :
    QuantumChannel (Qudit.QuditRegister q) (Qudit.QuditRegister q) :=
  QuantumChannel.comp (S.prepareSelected rho) S.erasureChannelFromRegister
noncomputable def replacementAfterErasure (S : QuditSubsystem q) (hq : ∀ i, 0 < q i) :
    QuantumChannel (Qudit.QuditRegister q) (Qudit.QuditRegister q) :=
  S.replacementAfterErasureWith (S.maximallyMixedSelected hq)
end QuditSubsystem
end Semantics
end QEC


