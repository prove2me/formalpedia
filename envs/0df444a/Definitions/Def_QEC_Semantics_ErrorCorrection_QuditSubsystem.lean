-- Prove2me | Definitions.Def_QEC_Semantics_ErrorCorrection_QuditSubsystem
-- name    : QEC_Semantics_ErrorCorrection_QuditSubsystem
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-05T09:59:41.810029+00:00
-- url     : https://prove2.me/theorems/996c39a7-9f5f-417e-be2e-6ed122cf62b4
-- title:
--   Qudit Subsystem
-- statement:
--   Definitions and structural lemmas for Qudit Subsystem, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/ErrorCorrection/QuditSubsystem.lean

import Definitions.Def_QEC_Semantics_Channels_Core
import Mathlib.Analysis.InnerProductSpace.PiL2
import Theorems.Thm_QEC_Semantics_QuantumChannel_comp_apply
import Theorems.Thm_QEC_Semantics_QuantumChannel_id_apply
import Theorems.Thm_QEC_Semantics_UnitaryTransport_conjDensity_apply
import Theorems.Thm_QEC_Semantics_UnitaryTransport_conjDensity_toOperator
import Theorems.Thm_QEC_Semantics_partialTraceRightRaw_cptp_toLinearMap
import Theorems.Thm_QEC_Semantics_partialTraceRightRaw_mapDensity_toOperator
attribute [local simp] QEC.Semantics.QuantumChannel.comp_apply
attribute [local simp] QEC.Semantics.QuantumChannel.id_apply
attribute [local simp] QEC.Semantics.UnitaryTransport.conjDensity_apply
attribute [local simp] QEC.Semantics.UnitaryTransport.conjDensity_toOperator
attribute [local simp] QEC.Semantics.partialTraceRightRaw_cptp_toLinearMap
attribute [local simp] QEC.Semantics.partialTraceRightRaw_mapDensity_toOperator


set_option autoImplicit false
noncomputable section
namespace QEC
namespace Semantics
open Classical
open scoped BigOperators ComplexOrder TensorProduct
universe u v
namespace Qudit
abbrev Label {ι : Type u} (q : ι → Nat) : Type u :=
  ∀ i, Fin (q i)
abbrev QuditRegister {ι : Type u} [Fintype ι] (q : ι → Nat) : Type u :=
  EuclideanSpace Complex (Label q)
def zeroLabel {ι : Type u} (q : ι → Nat) (hq : ∀ i, 0 < q i) : Label q :=
  fun i => ⟨0, hq i⟩
theorem label_nonempty {ι : Type u} [Fintype ι] (q : ι → Nat) (hq : ∀ i, 0 < q i) :
    Nonempty (Label q) :=
  ⟨zeroLabel q hq⟩
end Qudit
structure QuditSubsystem {ι : Type u} [Fintype ι] [DecidableEq ι]
    (q : ι → Nat) where
  selected : Finset ι
namespace QuditSubsystem
variable {ι : Type u} [Fintype ι] [DecidableEq ι]
variable {q : ι → Nat}
abbrev SelectedCoordinates (S : QuditSubsystem q) : Type u :=
  {i : ι // i ∈ S.selected}
abbrev ComplementCoordinates (S : QuditSubsystem q) : Type u :=
  {i : ι // i ∉ S.selected}
abbrev selectedDimensions (S : QuditSubsystem q) : S.SelectedCoordinates → Nat :=
  fun i => q i
abbrev complementDimensions (S : QuditSubsystem q) : S.ComplementCoordinates → Nat :=
  fun i => q i
abbrev selectedSystem (S : QuditSubsystem q) : Type u :=
  Qudit.QuditRegister S.selectedDimensions
abbrev complementSystem (S : QuditSubsystem q) : Type u :=
  Qudit.QuditRegister S.complementDimensions
abbrev factorizedSystem (S : QuditSubsystem q) : Type u :=
  CompositeSystem S.selectedSystem S.complementSystem
def splitLabel (S : QuditSubsystem q) (labels : Qudit.Label q) :
    Qudit.Label S.selectedDimensions × Qudit.Label S.complementDimensions :=
  (fun i => labels i, fun i => labels i)
def recombineLabel (S : QuditSubsystem q)
    (labels : Qudit.Label S.selectedDimensions × Qudit.Label S.complementDimensions) :
    Qudit.Label q :=
  fun i => if hi : i ∈ S.selected then labels.1 ⟨i, hi⟩ else labels.2 ⟨i, hi⟩
def labelFactorization (S : QuditSubsystem q) :
    Qudit.Label q ≃ Qudit.Label S.selectedDimensions × Qudit.Label S.complementDimensions where
  toFun := S.splitLabel
  invFun := S.recombineLabel
  left_inv := by
    intro labels
    funext i
    by_cases hi : i ∈ S.selected <;> simp [splitLabel, recombineLabel, hi]
  right_inv := by
    rintro ⟨left, right⟩
    apply Prod.ext
    · funext i
      simp [splitLabel, recombineLabel]
    · funext i
      have hi : (i : ι) ∉ S.selected := i.property
      simp [splitLabel, recombineLabel, hi]
noncomputable def registerFactorization (S : QuditSubsystem q) :
    UnitaryTransport (Qudit.QuditRegister q) S.factorizedSystem := by
  let sourceBasis := EuclideanSpace.basisFun (Qudit.Label q) Complex
  let selectedBasis := EuclideanSpace.basisFun (Qudit.Label S.selectedDimensions) Complex
  let complementBasis := EuclideanSpace.basisFun (Qudit.Label S.complementDimensions) Complex
  let targetBasis := selectedBasis.tensorProduct complementBasis
  let U := sourceBasis.equiv targetBasis S.labelFactorization
  exact
    { toLinearEquiv := U.toLinearEquiv
      map_inner := U.inner_map_map }
def complementBasisIndex (S : QuditSubsystem q) (hq : ∀ i, 0 < q i) :
    Fin (Module.finrank Complex S.complementSystem) :=
  ⟨0, by
    letI : Nonempty (Qudit.Label S.complementDimensions) :=
      Qudit.label_nonempty S.complementDimensions (fun i => hq i)
    rw [finrank_euclideanSpace]
    exact Fintype.card_pos⟩
noncomputable def complementAnchor (S : QuditSubsystem q) (hq : ∀ i, 0 < q i) :
    S.complementSystem :=
  (stdOrthonormalBasis Complex S.complementSystem) (S.complementBasisIndex hq)
noncomputable def localEmbedding (S : QuditSubsystem q) (hq : ∀ i, 0 < q i) :
    S.selectedSystem →ₗ[Complex] S.factorizedSystem :=
  (TensorProduct.mk Complex S.selectedSystem S.complementSystem).flip (S.complementAnchor hq)
@[simp]
theorem localEmbedding_apply (S : QuditSubsystem q) (hq : ∀ i, 0 < q i)
    (h : S.selectedSystem) :
    S.localEmbedding hq h = h ⊗ₜ[Complex] S.complementAnchor hq :=
  rfl
noncomputable def extendLocal (S : QuditSubsystem q) (A : Operator S.selectedSystem) :
    Operator S.factorizedSystem :=
  TensorProduct.map A (LinearMap.id : S.complementSystem →ₗ[Complex] S.complementSystem)
@[simp]
theorem extendLocal_apply_tmul (S : QuditSubsystem q) (A : Operator S.selectedSystem)
    (selected : S.selectedSystem) (complement : S.complementSystem) :
    S.extendLocal A (selected ⊗ₜ[Complex] complement) =
      (A selected) ⊗ₜ[Complex] complement := by
  simp [extendLocal]
noncomputable def extendLocalToRegister (S : QuditSubsystem q) (A : Operator S.selectedSystem) :
    Operator (Qudit.QuditRegister q) :=
  S.registerFactorization.symm.conjOperator (S.extendLocal A)
@[simp]
theorem extendLocal_apply_localEmbedding (S : QuditSubsystem q) (hq : ∀ i, 0 < q i)
    (A : Operator S.selectedSystem) (h : S.selectedSystem) :
    S.extendLocal A (S.localEmbedding hq h) = S.localEmbedding hq (A h) := by
  simp [extendLocal, localEmbedding]
noncomputable def restrictLocal (S : QuditSubsystem q) (hq : ∀ i, 0 < q i)
    (A : Operator S.factorizedSystem) : Operator S.selectedSystem :=
  (LinearMap.adjoint (S.localEmbedding hq)).comp (A.comp (S.localEmbedding hq))
noncomputable def restrictLocalFromRegister (S : QuditSubsystem q) (hq : ∀ i, 0 < q i)
    (A : Operator (Qudit.QuditRegister q)) : Operator S.selectedSystem :=
  S.restrictLocal hq (S.registerFactorization.conjOperator A)
def OperatorSupportedOn (S : QuditSubsystem q) (A : Operator S.factorizedSystem) : Prop :=
  ∃ localOperator : Operator S.selectedSystem, S.extendLocal localOperator = A
def OperatorSupportedOnRegister (S : QuditSubsystem q)
    (A : Operator (Qudit.QuditRegister q)) : Prop :=
  ∃ localOperator : Operator S.selectedSystem, S.extendLocalToRegister localOperator = A
noncomputable def selectedPartialTrace (S : QuditSubsystem q) :
    QuantumChannel S.factorizedSystem S.selectedSystem :=
  partialTraceRightRaw_cptp S.selectedSystem S.complementSystem
noncomputable def factorSwap (S : QuditSubsystem q) :
    UnitaryTransport S.factorizedSystem (CompositeSystem S.complementSystem S.selectedSystem) := by
  let U := TensorProduct.commIsometry Complex S.selectedSystem S.complementSystem
  exact
    { toLinearEquiv := U.toLinearEquiv
      map_inner := U.inner_map_map }
@[simp]
theorem factorSwap_apply_tmul (S : QuditSubsystem q)
    (selected : S.selectedSystem) (complement : S.complementSystem) :
    S.factorSwap (selected ⊗ₜ[Complex] complement) = complement ⊗ₜ[Complex] selected :=
  rfl
noncomputable def erasureChannel (S : QuditSubsystem q) :
    QuantumChannel S.factorizedSystem S.complementSystem :=
  QuantumChannel.comp
    (partialTraceRightRaw_cptp S.complementSystem S.selectedSystem)
    (QuantumChannel.unitaryConj S.factorSwap)
noncomputable def selectedPartialTraceFromRegister (S : QuditSubsystem q) :
    QuantumChannel (Qudit.QuditRegister q) S.selectedSystem :=
  QuantumChannel.comp S.selectedPartialTrace
    (QuantumChannel.unitaryConj S.registerFactorization)
noncomputable def erasureChannelFromRegister (S : QuditSubsystem q) :
    QuantumChannel (Qudit.QuditRegister q) S.complementSystem :=
  QuantumChannel.comp S.erasureChannel
    (QuantumChannel.unitaryConj S.registerFactorization)
@[simp]
theorem selectedPartialTrace_toLinearMap (S : QuditSubsystem q) :
    S.selectedPartialTrace.toLinearMap = partialTraceRightRaw S.selectedSystem S.complementSystem :=
  rfl
abbrev AdditionalRetainedCoordinates (S T : QuditSubsystem q) : Type u :=
  {i : ι // i ∉ S.selected ∧ i ∈ T.selected}
abbrev additionalRetainedDimensions (S T : QuditSubsystem q) :
    S.AdditionalRetainedCoordinates T → Nat :=
  fun i => q i
abbrev additionalRetainedSystem (S T : QuditSubsystem q) : Type u :=
  Qudit.QuditRegister (S.additionalRetainedDimensions T)
def splitComplementLabel (S T : QuditSubsystem q)
    (hST : S.selected ⊆ T.selected) (labels : Qudit.Label S.complementDimensions) :
    Qudit.Label (S.additionalRetainedDimensions T) × Qudit.Label T.complementDimensions :=
  (fun i => labels ⟨i, i.property.1⟩,
    fun i => labels ⟨i, fun hiS => i.property (hST hiS)⟩)
def recombineComplementLabel (S T : QuditSubsystem q)
    (labels : Qudit.Label (S.additionalRetainedDimensions T) × Qudit.Label T.complementDimensions) :
    Qudit.Label S.complementDimensions :=
  fun i => if hiT : (i : ι) ∈ T.selected then
    labels.1 ⟨i, ⟨i.property, hiT⟩⟩
  else labels.2 ⟨i, hiT⟩
def complementLabelFactorization (S T : QuditSubsystem q) (hST : S.selected ⊆ T.selected) :
    Qudit.Label S.complementDimensions ≃
      Qudit.Label (S.additionalRetainedDimensions T) × Qudit.Label T.complementDimensions where
  toFun := S.splitComplementLabel T hST
  invFun := S.recombineComplementLabel T
  left_inv := by
    intro labels
    funext i
    by_cases hiT : (i : ι) ∈ T.selected
    · simp [splitComplementLabel, recombineComplementLabel, hiT]
    · simp [splitComplementLabel, recombineComplementLabel, hiT]
  right_inv := by
    rintro ⟨additional, complement⟩
    apply Prod.ext
    · funext i
      simp [splitComplementLabel, recombineComplementLabel, i.property.2]
    · funext i
      simp [splitComplementLabel, recombineComplementLabel, i.property]
noncomputable def complementFactorization (S T : QuditSubsystem q) (hST : S.selected ⊆ T.selected) :
    UnitaryTransport S.complementSystem
      (CompositeSystem (S.additionalRetainedSystem T) T.complementSystem) := by
  let sourceBasis := EuclideanSpace.basisFun (Qudit.Label S.complementDimensions) Complex
  let additionalBasis :=
    EuclideanSpace.basisFun (Qudit.Label (S.additionalRetainedDimensions T)) Complex
  let complementBasis := EuclideanSpace.basisFun (Qudit.Label T.complementDimensions) Complex
  let targetBasis := additionalBasis.tensorProduct complementBasis
  let U := sourceBasis.equiv targetBasis (S.complementLabelFactorization T hST)
  exact
    { toLinearEquiv := U.toLinearEquiv
      map_inner := U.inner_map_map }
def splitSelectedLabel (S T : QuditSubsystem q)
    (hST : S.selected ⊆ T.selected) (labels : Qudit.Label T.selectedDimensions) :
    Qudit.Label S.selectedDimensions × Qudit.Label (S.additionalRetainedDimensions T) :=
  (fun i => labels ⟨i, hST i.property⟩,
    fun i => labels ⟨i, i.property.2⟩)
def recombineSelectedLabel (S T : QuditSubsystem q)
    (labels : Qudit.Label S.selectedDimensions × Qudit.Label (S.additionalRetainedDimensions T)) :
    Qudit.Label T.selectedDimensions :=
  fun i => if hiS : (i : ι) ∈ S.selected then
    labels.1 ⟨i, hiS⟩
  else labels.2 ⟨i, ⟨hiS, i.property⟩⟩
def selectedLabelFactorization (S T : QuditSubsystem q) (hST : S.selected ⊆ T.selected) :
    Qudit.Label T.selectedDimensions ≃
      Qudit.Label S.selectedDimensions × Qudit.Label (S.additionalRetainedDimensions T) where
  toFun := S.splitSelectedLabel T hST
  invFun := S.recombineSelectedLabel T
  left_inv := by
    intro labels
    funext i
    by_cases hiS : (i : ι) ∈ S.selected
    · simp [splitSelectedLabel, recombineSelectedLabel, hiS]
    · simp [splitSelectedLabel, recombineSelectedLabel, hiS]
  right_inv := by
    rintro ⟨selected, additional⟩
    apply Prod.ext
    · funext i
      simp [splitSelectedLabel, recombineSelectedLabel]
    · funext i
      simp [splitSelectedLabel, recombineSelectedLabel, i.property.1]
noncomputable def selectedFactorization (S T : QuditSubsystem q) (hST : S.selected ⊆ T.selected) :
    UnitaryTransport T.selectedSystem
      (CompositeSystem S.selectedSystem (S.additionalRetainedSystem T)) := by
  let sourceBasis := EuclideanSpace.basisFun (Qudit.Label T.selectedDimensions) Complex
  let selectedBasis := EuclideanSpace.basisFun (Qudit.Label S.selectedDimensions) Complex
  let additionalBasis :=
    EuclideanSpace.basisFun (Qudit.Label (S.additionalRetainedDimensions T)) Complex
  let targetBasis := selectedBasis.tensorProduct additionalBasis
  let U := sourceBasis.equiv targetBasis (S.selectedLabelFactorization T hST)
  exact
    { toLinearEquiv := U.toLinearEquiv
      map_inner := U.inner_map_map }
noncomputable def additionalRetainedFactorSwap (S T : QuditSubsystem q) :
    UnitaryTransport (CompositeSystem (S.additionalRetainedSystem T) T.complementSystem)
      (CompositeSystem T.complementSystem (S.additionalRetainedSystem T)) := by
  let U := TensorProduct.commIsometry Complex (S.additionalRetainedSystem T) T.complementSystem
  exact
    { toLinearEquiv := U.toLinearEquiv
      map_inner := U.inner_map_map }
noncomputable def discardAdditionalRetained (S T : QuditSubsystem q)
    (hST : S.selected ⊆ T.selected) : QuantumChannel S.complementSystem T.complementSystem :=
  QuantumChannel.comp
    (partialTraceRightRaw_cptp T.complementSystem (S.additionalRetainedSystem T))
    (QuantumChannel.comp
      (QuantumChannel.unitaryConj (S.additionalRetainedFactorSwap T))
      (QuantumChannel.unitaryConj (S.complementFactorization T hST)))
def ErasureCorrectable (S : QuditSubsystem q) (C : QuantumCode S.factorizedSystem)
    (recovery : QuantumChannel S.complementSystem S.factorizedSystem) : Prop :=
  Correctable S.factorizedSystem S.complementSystem C S.erasureChannel recovery
def ErasureCorrectableFromRegister (S : QuditSubsystem q)
    (C : QuantumCode (Qudit.QuditRegister q))
    (recovery : QuantumChannel S.complementSystem (Qudit.QuditRegister q)) : Prop :=
  Correctable (Qudit.QuditRegister q) S.complementSystem C S.erasureChannelFromRegister recovery
def ErasureRecoverable (S : QuditSubsystem q) (C : QuantumCode S.factorizedSystem) : Prop :=
  ∃ recovery : QuantumChannel S.complementSystem S.factorizedSystem,
    S.ErasureCorrectable C recovery
def ErasureRecoverableFromRegister (S : QuditSubsystem q)
    (C : QuantumCode (Qudit.QuditRegister q)) : Prop :=
  ∃ recovery : QuantumChannel S.complementSystem (Qudit.QuditRegister q),
    S.ErasureCorrectableFromRegister C recovery
end QuditSubsystem
end Semantics
end QEC


