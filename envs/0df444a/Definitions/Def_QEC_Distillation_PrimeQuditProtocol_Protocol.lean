-- Prove2me | Definitions.Def_QEC_Distillation_PrimeQuditProtocol_Protocol
-- name    : QEC_Distillation_PrimeQuditProtocol_Protocol
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-09T14:26:24.281424+00:00
-- url     : https://prove2.me/theorems/45fb8f94-a63f-4d1e-b33e-16a9ea479df7
-- title:
--   Protocol
-- statement:
--   Definitions and structural lemmas for Protocol, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/PrimeQuditProtocol/Protocol.lean

import Definitions.Def_QEC_Coding_Core_Definitions
import Definitions.Def_QEC_Distillation_PrimeQuditProtocol_MagicResource
import Definitions.Def_QEC_Distillation_PrimeQuditProtocol_P11CubicBridge
import Definitions.Def_QEC_Distillation_Core_MagicStateProtocol
import Definitions.Def_QEC_Distillation_Core_Overhead
import Definitions.Def_QEC_Distillation_Core_FiniteInstrumentBinaryRun
import Definitions.Def_QEC_Distillation_Core_FiniteDecodedTrace
import Definitions.Def_QEC_Semantics_Instruments_Branches_BranchOperatorLinear
import Definitions.Def_QEC_Semantics_Instruments_Sequential_Composition
import Theorems.Thm_QEC_Coding_ChainComplexData_pureZLogicalQuotientEquivMiddleHomology_mk
import Theorems.Thm_QEC_Coding_KT19ReedSolomon_mem_reedSolomonCode
import Theorems.Thm_QEC_Distillation_DistillationRun_postprocess_conditionalOutput
import Theorems.Thm_QEC_Distillation_DistillationRun_postprocess_successProbability
import Theorems.Thm_QEC_Distillation_EncodedCode_ImplementsLogicalGate_symm
import Theorems.Thm_QEC_Distillation_KT19MagicResource_KT19PrimeQuditCSS_characterKet_inner
import Theorems.Thm_QEC_Distillation_KT19MagicResource_KT19PrimeQuditCSS_magicRegisterKet_inner
import Theorems.Thm_QEC_Distillation_KT19MagicResource_KT19PrimeQuditCSS_magicRegisterKrausFamily_complete
import Theorems.Thm_QEC_Distillation_KT19MagicResource_KT19PrimeQuditCSS_phase_eq_one_iff
import Theorems.Thm_QEC_Distillation_KT19MagicResource_KT19PrimeQuditCSS_physicalU13_symm_magicRegisterKet
import Theorems.Thm_QEC_Distillation_KT19MagicResource_KT19PrimeQuditCSS_sum_characterKet_rankOne_eq_one
import Theorems.Thm_QEC_Distillation_KT19P11ReedSolomonCubicBridge_p11_stabilizerCarrier_eq_shortenedReedSolomon
import Theorems.Thm_QEC_Distillation_KT19PrimeQuditCSS_CubicRowFamily_cosetLabel_eq_combinedWord
import Theorems.Thm_QEC_Distillation_KT19PrimeQuditCSS_CubicRowFamily_cubicExponent_cosetLabel
import Theorems.Thm_QEC_Distillation_KT19PrimeQuditCSS_physicalU13_apply_phase
import Theorems.Thm_QEC_Semantics_Correctable_unitaryTransport
import Theorems.Thm_QEC_Semantics_DensityOperator_convexCombination_toOperator
import Theorems.Thm_QEC_Semantics_DensityOperator_ext_toOperator
import Theorems.Thm_QEC_Semantics_DensityOperator_tensorDensity_toOperator
import Theorems.Thm_QEC_Semantics_DensityOperator_trace_toOperator
import Theorems.Thm_QEC_Semantics_FiniteInstrument_binaryCoarsen_branchOperator_accepted
import Theorems.Thm_QEC_Semantics_FiniteInstrument_binaryCoarsen_branchOperator_rejected
import Theorems.Thm_QEC_Semantics_FiniteInstrument_binaryDistillationRun_successProbability
import Theorems.Thm_QEC_Semantics_FiniteInstrument_bind_complete
import Theorems.Thm_QEC_Semantics_FiniteInstrument_bornWeight_nonneg
import Theorems.Thm_QEC_Semantics_FiniteInstrument_branchOperator_smul
import Theorems.Thm_QEC_Semantics_FiniteInstrument_branchOperator_sum
import Theorems.Thm_QEC_Semantics_FiniteInstrument_branchOperator_zero
import Theorems.Thm_QEC_Semantics_FiniteInstrument_conditionalDensity_toOperator
import Theorems.Thm_QEC_Semantics_FiniteInstrument_sum_bornWeight_eq_one
import Theorems.Thm_QEC_Semantics_QuantumChannel_comp_apply
import Theorems.Thm_QEC_Semantics_QuantumChannel_id_apply
import Theorems.Thm_QEC_Semantics_QuditSubsystem_additionalRetainedFactorSwap_apply_tmul
import Theorems.Thm_QEC_Semantics_UnitaryTransport_conjDensity_apply
import Theorems.Thm_QEC_Semantics_UnitaryTransport_conjDensity_toOperator
import Theorems.Thm_QEC_Semantics_partialTraceRightRaw_cptp_toLinearMap
import Theorems.Thm_QEC_Semantics_partialTraceRightRaw_mapDensity_toOperator
import Theorems.Thm_QEC_Semantics_traceNorm_neg
attribute [local simp] QEC.Coding.ChainComplexData.pureZLogicalQuotientEquivMiddleHomology_mk
attribute [local simp] QEC.Coding.KT19ReedSolomon.mem_reedSolomonCode
attribute [local simp] QEC.Distillation.DistillationRun.postprocess_conditionalOutput
attribute [local simp] QEC.Distillation.DistillationRun.postprocess_successProbability
attribute [local simp] QEC.Semantics.DensityOperator.convexCombination_toOperator
attribute [local simp] QEC.Semantics.DensityOperator.tensorDensity_toOperator
attribute [local simp] QEC.Semantics.FiniteInstrument.binaryDistillationRun_successProbability
attribute [local simp] QEC.Semantics.FiniteInstrument.branchOperator_zero
attribute [local simp] QEC.Semantics.FiniteInstrument.conditionalDensity_toOperator
attribute [local simp] QEC.Semantics.QuantumChannel.comp_apply
attribute [local simp] QEC.Semantics.QuantumChannel.id_apply
attribute [local simp] QEC.Semantics.QuditSubsystem.additionalRetainedFactorSwap_apply_tmul
attribute [local simp] QEC.Semantics.UnitaryTransport.conjDensity_apply
attribute [local simp] QEC.Semantics.UnitaryTransport.conjDensity_toOperator
attribute [local simp] QEC.Semantics.partialTraceRightRaw_cptp_toLinearMap
attribute [local simp] QEC.Semantics.partialTraceRightRaw_mapDensity_toOperator
attribute [local simp] QEC.Semantics.traceNorm_neg


set_option autoImplicit false
noncomputable section
namespace QEC.Distillation.KT19Protocol
open Semantics
open QEC.Coding
open QEC.Coding.KT19ReedSolomon
open QEC.Distillation.KT19PrimeQuditCSS
open QEC.Distillation.KT19MagicResource.KT19PrimeQuditCSS
open QEC.Distillation.KT19P11ReedSolomonCubicBridge
attribute [local instance]
  QEC.Distillation.KT19PrimeQuditCSS.primeQuditRegisterLabelFintype
local instance instKT19ProtocolClassicalDecidable (p : Prop) : Decidable p :=
  Classical.propDecidable p
attribute [local instance] QEC.Distillation.KT19Protocol.instKT19ProtocolClassicalDecidable
universe u
variable (p : Nat) [NeZero p]
variable {Site : Type u} [Fintype Site] [DecidableEq Site]
def xWordLabelEquiv (word : PrimeQuditRegisterLabel p Site) :
    PrimeQuditRegisterLabel p Site ≃ PrimeQuditRegisterLabel p Site where
  toFun label := label + word
  invFun label := label - word
  left_inv label := by
    funext site
    simp
  right_inv label := by
    funext site
    simp
noncomputable def xWordLinearIsometry (word : PrimeQuditRegisterLabel p Site) :
    PrimeQuditRegister p Site ≃ₗᵢ[Complex] PrimeQuditRegister p Site :=
  LinearIsometryEquiv.piLpCongrLeft 2 Complex Complex (xWordLabelEquiv p word)
noncomputable def xWordTransport (word : PrimeQuditRegisterLabel p Site) :
    UnitaryTransport (PrimeQuditRegister p Site) (PrimeQuditRegister p Site) where
  toLinearEquiv := (xWordLinearIsometry p word).toLinearEquiv
  map_inner := fun psi chi => (xWordLinearIsometry p word).inner_map_map psi chi
@[simp]
theorem xWordTransport_apply (word : PrimeQuditRegisterLabel p Site)
    (psi : PrimeQuditRegister p Site) (label : PrimeQuditRegisterLabel p Site) :
    xWordTransport p word psi label = psi (label - word) :=
  rfl
theorem inverseTransversal_magicRegisterKet
    (error : PrimeQuditRegisterLabel p Site) :
    (physicalU13 p).symm (magicRegisterKet p error) = characterKet p error :=
  physicalU13_symm_magicRegisterKet p error
section Syndromes
variable {q : Nat} [NeZero q] [Fact q.Prime]
variable {Logical Stabilizer : Type u} [Fintype Logical] [Fintype Stabilizer]
def rowCarrier (R : CubicRowFamily q Logical Stabilizer Site) :
    Submodule (ZMod q) (PrimeQuditRegisterLabel q Site) :=
  Submodule.span (ZMod q) (Set.range R.row)
def stabilizerCarrier (R : CubicRowFamily q Logical Stabilizer Site) :
    Submodule (ZMod q) (PrimeQuditRegisterLabel q Site) :=
  Submodule.span (ZMod q) (Set.range R.stabilizerRow)
def kt19StabilizerCode (R : CubicRowFamily q Logical Stabilizer Site) :
    LinearCode (ZMod q) Site where
  carrier := stabilizerCarrier R
abbrev ZSyndrome (R : CubicRowFamily q Logical Stabilizer Site) :=
  PrimeQuditRegisterLabel q Site ⧸ rowCarrier R
noncomputable instance zSyndromeDecidableEq
    (R : CubicRowFamily q Logical Stabilizer Site) : DecidableEq (ZSyndrome R) :=
  Classical.decEq _
def zSyndrome (R : CubicRowFamily q Logical Stabilizer Site)
    (word : PrimeQuditRegisterLabel q Site) : ZSyndrome R :=
  Submodule.Quotient.mk word
theorem zSyndrome_add_mem_rowCarrier
    (R : CubicRowFamily q Logical Stabilizer Site)
    (word carrier : PrimeQuditRegisterLabel q Site)
    (hcarrier : carrier ∈ rowCarrier R) :
    zSyndrome R (word + carrier) = zSyndrome R word := by
  change Submodule.Quotient.mk (word + carrier) = Submodule.Quotient.mk word
  rw [Submodule.Quotient.eq]
  simpa using hcarrier
theorem zSyndrome_eq_zero_iff_mem_rowCarrier
    (R : CubicRowFamily q Logical Stabilizer Site)
    (word : PrimeQuditRegisterLabel q Site) :
    zSyndrome R word = 0 ↔ word ∈ rowCarrier R := by
  change Submodule.Quotient.mk word = Submodule.Quotient.mk 0 ↔ _
  rw [Submodule.Quotient.eq]
  simp
theorem cubicExponent_sub_stabilizerRow_of_mem_rowCarrier
    (R : CubicRowFamily q Logical Stabilizer Site)
    (word : PrimeQuditRegisterLabel q Site) (hword : word ∈ rowCarrier R)
    (index : Stabilizer) :
    cubicExponent q (word - R.stabilizerRow index) = cubicExponent q word := by
  classical
  obtain ⟨coefficient, hcoefficient⟩ :=
    (Submodule.mem_span_range_iff_exists_fun (ZMod q)).mp hword
  change R.combinedWord coefficient = word at hcoefficient
  let logicalCoefficient : Logical → ZMod q :=
    fun logical => -coefficient (Sum.inl logical)
  let stabilizerCoefficient : Stabilizer → ZMod q :=
    fun stabilizer => coefficient (Sum.inr stabilizer)
  have hcoefficient_eq :
      CubicRowFamily.combinedCoefficient logicalCoefficient stabilizerCoefficient =
        coefficient := by
    funext row
    rcases row with logical | stabilizer
    · simp [logicalCoefficient, CubicRowFamily.combinedCoefficient]
    · simp [stabilizerCoefficient, CubicRowFamily.combinedCoefficient]
  have hcoset :
      R.cosetLabel logicalCoefficient stabilizerCoefficient = word := by
    rw [R.cosetLabel_eq_combinedWord, hcoefficient_eq, hcoefficient]
  let delta : Stabilizer → ZMod q :=
    fun stabilizer => if stabilizer = index then 1 else 0
  have hdelta : R.stabilizerWord delta = R.stabilizerRow index := by
    unfold CubicRowFamily.stabilizerWord
    rw [Finset.sum_eq_single index]
    · simp [delta]
    · intro other _ hother
      simp [delta, hother]
    · simp
  have hcoset_sub :
      R.cosetLabel logicalCoefficient (stabilizerCoefficient - delta) =
        R.cosetLabel logicalCoefficient stabilizerCoefficient - R.stabilizerRow index := by
    unfold CubicRowFamily.cosetLabel
    rw [R.stabilizerWord_sub, hdelta]
    abel
  calc
    cubicExponent q (word - R.stabilizerRow index) =
        cubicExponent q
          (R.cosetLabel logicalCoefficient (stabilizerCoefficient - delta)) := by
      rw [hcoset_sub, hcoset]
    _ = -(∑ logical : Logical, logicalCoefficient logical ^ 3 * R.epsilon logical) :=
      R.cubicExponent_cosetLabel logicalCoefficient (stabilizerCoefficient - delta)
    _ = cubicExponent q (R.cosetLabel logicalCoefficient stabilizerCoefficient) :=
      (R.cubicExponent_cosetLabel logicalCoefficient stabilizerCoefficient).symm
    _ = cubicExponent q word := by rw [hcoset]
noncomputable def zSyndromeRepresentative
    (R : CubicRowFamily q Logical Stabilizer Site) (syndrome : ZSyndrome R) :
    PrimeQuditRegisterLabel q Site :=
  Classical.choose (Submodule.Quotient.mk_surjective (rowCarrier R) syndrome)
theorem zSyndrome_representative
    (R : CubicRowFamily q Logical Stabilizer Site) (syndrome : ZSyndrome R) :
    zSyndrome R (zSyndromeRepresentative R syndrome) = syndrome :=
  Classical.choose_spec (Submodule.Quotient.mk_surjective (rowCarrier R) syndrome)
theorem zSyndrome_add_representative_eq_iff
    (R : CubicRowFamily q Logical Stabilizer Site)
    (word : PrimeQuditRegisterLabel q Site) (syndrome : ZSyndrome R) :
    zSyndrome R (word + zSyndromeRepresentative R syndrome) = syndrome ↔
      zSyndrome R word = 0 := by
  have hrepresentative :
      Submodule.Quotient.mk (zSyndromeRepresentative R syndrome) = syndrome :=
    zSyndrome_representative R syndrome
  change Submodule.Quotient.mk
      (word + zSyndromeRepresentative R syndrome) = syndrome ↔
    Submodule.Quotient.mk word = 0
  rw [Submodule.Quotient.mk_add, hrepresentative]
  constructor
  · intro h
    have h' : Submodule.Quotient.mk word + syndrome = 0 + syndrome := by
      simpa using h
    exact add_right_cancel h'
  · intro h
    simpa [h]
def xSyndrome (R : CubicRowFamily q Logical Stabilizer Site)
    (word : PrimeQuditRegisterLabel q Site) : Stabilizer → ZMod q :=
  fun index => wordPairing word (R.stabilizerRow index)
def kt19AcceptedWord (R : CubicRowFamily q Logical Stabilizer Site)
    (word : PrimeQuditRegisterLabel q Site) : Prop :=
  xSyndrome R word = 0
def kt19LogicalRouting (R : CubicRowFamily q Logical Stabilizer Site)
    (error : PrimeQuditRegisterLabel q Site) :
    PrimeQuditRegisterLabel q Logical :=
  fun port => -wordPairing error (R.logicalRow port)
omit [Fact q.Prime] in
theorem registerBasisKet_inner_self
    (word : PrimeQuditRegisterLabel q Site) :
    inner ℂ (registerBasisKet q word) (registerBasisKet q word) = 1 := by
  simp [registerBasisKet, EuclideanSpace.basisFun_apply]
omit [Fact q.Prime] in
theorem registerBasisKet_inner_zero
    (left right : PrimeQuditRegisterLabel q Site) (hne : left ≠ right) :
    inner ℂ (registerBasisKet q left) (registerBasisKet q right) = 0 := by
  rw [registerBasisKet, registerBasisKet]
  simp only [EuclideanSpace.basisFun_apply, EuclideanSpace.inner_single_left]
  simp [hne]
omit [Fact q.Prime] in
theorem computationalRankOne_mul
    (left right : PrimeQuditRegisterLabel q Site) :
    (InnerProductSpace.rankOne ℂ (registerBasisKet q left)
      (registerBasisKet q left)).toLinearMap *
        (InnerProductSpace.rankOne ℂ (registerBasisKet q right)
          (registerBasisKet q right)).toLinearMap =
      if left = right then
        (InnerProductSpace.rankOne ℂ (registerBasisKet q right)
          (registerBasisKet q right)).toLinearMap
      else 0 := by
  classical
  ext psi
  simp only [Module.End.mul_apply, InnerProductSpace.toLinearMap_rankOne,
    LinearMap.smulRight_apply, innerₛₗ_apply_apply]
  rw [inner_smul_right]
  by_cases hsame : left = right
  · subst left
    rw [registerBasisKet_inner_self]
    simp
  · rw [registerBasisKet_inner_zero left right hsame]
    simp [hsame]
theorem characterRankOne_mul
    (left right : PrimeQuditRegisterLabel q Site) :
    (InnerProductSpace.rankOne ℂ (characterKet q left)
      (characterKet q left)).toLinearMap *
        (InnerProductSpace.rankOne ℂ (characterKet q right)
          (characterKet q right)).toLinearMap =
      if left = right then
        (InnerProductSpace.rankOne ℂ (characterKet q right)
          (characterKet q right)).toLinearMap
      else 0 := by
  classical
  ext psi
  simp only [Module.End.mul_apply, InnerProductSpace.toLinearMap_rankOne,
    LinearMap.smulRight_apply, innerₛₗ_apply_apply]
  rw [inner_smul_right]
  by_cases hsame : left = right
  · subst left
    rw [characterKet_inner]
    simp
  · rw [characterKet_inner]
    simp [hsame]
noncomputable def zSyndromeProjector
    (R : CubicRowFamily q Logical Stabilizer Site) (syndrome : ZSyndrome R) :
    Operator (PrimeQuditRegister q Site) :=
  ∑ word : PrimeQuditRegisterLabel q Site,
    if zSyndrome R word = syndrome then
      (InnerProductSpace.rankOne ℂ (registerBasisKet q word)
        (registerBasisKet q word)).toLinearMap
    else 0
theorem zSyndromeProjector_apply_basis
    (R : CubicRowFamily q Logical Stabilizer Site) (syndrome : ZSyndrome R)
    (word : PrimeQuditRegisterLabel q Site) :
    zSyndromeProjector R syndrome (registerBasisKet q word) =
      if zSyndrome R word = syndrome then registerBasisKet q word else 0 := by
  classical
  unfold zSyndromeProjector
  simp only [LinearMap.sum_apply]
  by_cases hsector : zSyndrome R word = syndrome
  · rw [if_pos hsector, Finset.sum_eq_single word]
    · rw [if_pos hsector]
      simp only [InnerProductSpace.toLinearMap_rankOne, LinearMap.smulRight_apply,
        innerₛₗ_apply_apply]
      rw [registerBasisKet_inner_self]
      simp
    · intro other _ hne
      by_cases hother : zSyndrome R other = syndrome
      · rw [if_pos hother]
        simp only [InnerProductSpace.toLinearMap_rankOne, LinearMap.smulRight_apply,
          innerₛₗ_apply_apply]
        rw [registerBasisKet_inner_zero other word hne]
        simp
      · simp [hother]
    · simp
  · rw [if_neg hsector]
    apply Finset.sum_eq_zero
    intro other _
    by_cases hother : zSyndrome R other = syndrome
    · rw [if_pos hother]
      simp only [InnerProductSpace.toLinearMap_rankOne, LinearMap.smulRight_apply,
        innerₛₗ_apply_apply]
      have hne : other ≠ word := by
        intro heq
        subst other
        exact hsector hother
      rw [registerBasisKet_inner_zero other word hne]
      simp
    · simp [hother]
theorem sum_zSyndromeProjector_eq_one
    (R : CubicRowFamily q Logical Stabilizer Site) :
    ∑ syndrome : ZSyndrome R, zSyndromeProjector R syndrome = 1 := by
  classical
  unfold zSyndromeProjector
  rw [Finset.sum_comm]
  simp_rw [Fintype.sum_ite_eq]
  simpa [registerBasisKet, Module.End.one_eq_id] using congrArg ContinuousLinearMap.toLinearMap
    (OrthonormalBasis.sum_rankOne_eq_id
      (EuclideanSpace.basisFun (PrimeQuditRegisterLabel q Site) ℂ))
theorem zSyndromeProjector_adjoint
    (R : CubicRowFamily q Logical Stabilizer Site) (syndrome : ZSyndrome R) :
    LinearMap.adjoint (zSyndromeProjector R syndrome) = zSyndromeProjector R syndrome := by
  classical
  unfold zSyndromeProjector
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro word _
  by_cases hsector : zSyndrome R word = syndrome
  · rw [if_pos hsector]
    rw [LinearMap.adjoint_eq_toCLM_adjoint]
    change ((InnerProductSpace.rankOne ℂ (registerBasisKet q word)
      (registerBasisKet q word)).adjoint).toLinearMap = _
    rw [InnerProductSpace.adjoint_rankOne]
  · simp [hsector]
theorem zSyndromeProjector_apply
    (R : CubicRowFamily q Logical Stabilizer Site) (syndrome : ZSyndrome R)
    (psi : PrimeQuditRegister q Site) (word : PrimeQuditRegisterLabel q Site) :
    zSyndromeProjector R syndrome psi word =
      if zSyndrome R word = syndrome then psi word else 0 := by
  have hinner := LinearMap.adjoint_inner_right
    (zSyndromeProjector R syndrome) (registerBasisKet q word) psi
  rw [zSyndromeProjector_adjoint] at hinner
  rw [zSyndromeProjector_apply_basis] at hinner
  by_cases hsector : zSyndrome R word = syndrome
  · rw [if_pos hsector]
    rw [if_pos hsector] at hinner
    rw [registerBasisKet, EuclideanSpace.basisFun_inner,
      EuclideanSpace.basisFun_inner] at hinner
    exact hinner
  · rw [if_neg hsector]
    rw [if_neg hsector] at hinner
    rw [registerBasisKet, EuclideanSpace.basisFun_inner] at hinner
    simpa using hinner
theorem physicalU13_symm_zSyndromeProjector_apply
    (R : CubicRowFamily q Logical Stabilizer Site) (syndrome : ZSyndrome R)
    (psi : PrimeQuditRegister q Site) (word : PrimeQuditRegisterLabel q Site) :
    (physicalU13 q).symm (zSyndromeProjector R syndrome psi) word =
      zSyndromeProjector R syndrome ((physicalU13 q).symm psi) word := by
  have inversePhase (chi : PrimeQuditRegister q Site) :
      (physicalU13 q).symm chi word =
        phase q (-cubicExponent q word) * chi word := by
    exact physicalU13_symm_apply_phase q chi word
  by_cases hsector : zSyndrome R word = syndrome
  · calc
      (physicalU13 q).symm (zSyndromeProjector R syndrome psi) word =
          phase q (-cubicExponent q word) *
            zSyndromeProjector R syndrome psi word :=
        inversePhase (zSyndromeProjector R syndrome psi)
      _ = phase q (-cubicExponent q word) * psi word := by
            rw [zSyndromeProjector_apply, if_pos hsector]
      _ = zSyndromeProjector R syndrome ((physicalU13 q).symm psi) word := by
            rw [zSyndromeProjector_apply, if_pos hsector]
            exact (inversePhase psi).symm
  · calc
      (physicalU13 q).symm (zSyndromeProjector R syndrome psi) word =
          phase q (-cubicExponent q word) *
            zSyndromeProjector R syndrome psi word :=
        inversePhase (zSyndromeProjector R syndrome psi)
      _ = 0 := by
            rw [zSyndromeProjector_apply, if_neg hsector, mul_zero]
      _ = zSyndromeProjector R syndrome ((physicalU13 q).symm psi) word := by
            rw [zSyndromeProjector_apply, if_neg hsector]
theorem physicalU13_symm_zSyndromeProjector
    (R : CubicRowFamily q Logical Stabilizer Site) (syndrome : ZSyndrome R)
    (psi : PrimeQuditRegister q Site) :
    (physicalU13 q).symm (zSyndromeProjector R syndrome psi) =
      zSyndromeProjector R syndrome ((physicalU13 q).symm psi) := by
  ext word
  exact physicalU13_symm_zSyndromeProjector_apply R syndrome psi word
theorem xWordTransport_neg_zSyndromeProjector_apply
    (R : CubicRowFamily q Logical Stabilizer Site) (syndrome : ZSyndrome R)
    (psi : PrimeQuditRegister q Site) (word : PrimeQuditRegisterLabel q Site) :
    xWordTransport q (-zSyndromeRepresentative R syndrome)
        (zSyndromeProjector R syndrome psi) word =
      zSyndromeProjector R 0
        (xWordTransport q (-zSyndromeRepresentative R syndrome) psi) word := by
  by_cases hzero : zSyndrome R word = 0
  · have hsector :
        zSyndrome R (word + zSyndromeRepresentative R syndrome) = syndrome :=
      (zSyndrome_add_representative_eq_iff R word syndrome).2 hzero
    simp [xWordTransport_apply, zSyndromeProjector_apply, sub_neg_eq_add,
      hzero, hsector]
  · have hsector :
        zSyndrome R (word + zSyndromeRepresentative R syndrome) ≠ syndrome := by
      intro h
      exact hzero ((zSyndrome_add_representative_eq_iff R word syndrome).1 h)
    simp [xWordTransport_apply, zSyndromeProjector_apply, sub_neg_eq_add,
      hzero, hsector]
theorem xWordTransport_neg_zSyndromeProjector
    (R : CubicRowFamily q Logical Stabilizer Site) (syndrome : ZSyndrome R)
    (psi : PrimeQuditRegister q Site) :
    xWordTransport q (-zSyndromeRepresentative R syndrome)
        (zSyndromeProjector R syndrome psi) =
      zSyndromeProjector R 0
        (xWordTransport q (-zSyndromeRepresentative R syndrome) psi) := by
  ext word
  exact xWordTransport_neg_zSyndromeProjector_apply R syndrome psi word
theorem xWordTransport_neg_characterKet
    (error shift : PrimeQuditRegisterLabel q Site) :
    xWordTransport q (-shift) (characterKet q error) =
      phase q (registerPairing q error shift) • characterKet q error := by
  ext label
  simp only [xWordTransport_apply, WithLp.ofLp_smul, Pi.smul_apply, smul_eq_mul,
    characterKet_apply, sub_neg_eq_add]
  have hpairing : registerPairing q error (label + shift) =
      registerPairing q error label + registerPairing q error shift := by
    simp [registerPairing, mul_add, Finset.sum_add_distrib]
  rw [hpairing, phase_add]
  ring
theorem xWordTransport_stabilizerRow_characterKet
    (R : CubicRowFamily q Logical Stabilizer Site)
    (error : PrimeQuditRegisterLabel q Site) (index : Stabilizer) :
    xWordTransport q (R.stabilizerRow index) (characterKet q error) =
      phase q (-xSyndrome R error index) • characterKet q error := by
  simpa [xSyndrome, registerPairing, wordPairing_apply, dotProduct,
    Finset.sum_neg_distrib] using
    (xWordTransport_neg_characterKet (q := q) error (-R.stabilizerRow index))
theorem xWordTransport_stabilizerRow_physicalU13_zSyndromeProjector
    (R : CubicRowFamily q Logical Stabilizer Site)
    (error : PrimeQuditRegisterLabel q Site) (index : Stabilizer) :
    xWordTransport q (R.stabilizerRow index)
        (physicalU13 q (zSyndromeProjector R 0 (characterKet q error))) =
      phase q (-xSyndrome R error index) •
        physicalU13 q (zSyndromeProjector R 0 (characterKet q error)) := by
  ext word
  have hrow : R.stabilizerRow index ∈ rowCarrier R := by
    unfold rowCarrier
    exact Submodule.subset_span ⟨Sum.inr index, rfl⟩
  have hshift :
      zSyndrome R (word - R.stabilizerRow index) = zSyndrome R word := by
    have htranslate := zSyndrome_add_mem_rowCarrier R
      (word - R.stabilizerRow index) (R.stabilizerRow index) hrow
    simpa using htranslate.symm
  by_cases hsector : zSyndrome R word = 0
  · have hshiftSector : zSyndrome R (word - R.stabilizerRow index) = 0 := by
      rw [hshift]
      exact hsector
    have hcarrier : word ∈ rowCarrier R :=
      (zSyndrome_eq_zero_iff_mem_rowCarrier R word).1 hsector
    have hcubic := cubicExponent_sub_stabilizerRow_of_mem_rowCarrier
      R word hcarrier index
    have hpairing :
        registerPairing q error (word - R.stabilizerRow index) =
          registerPairing q error word - xSyndrome R error index := by
      simp only [registerPairing, xSyndrome, wordPairing_apply, dotProduct,
        Pi.sub_apply, mul_sub, Finset.sum_sub_distrib]
    simp only [xWordTransport_apply, WithLp.ofLp_smul, Pi.smul_apply,
      smul_eq_mul]
    rw [physicalU13_apply_phase, physicalU13_apply_phase,
      zSyndromeProjector_apply, zSyndromeProjector_apply,
      if_pos hshiftSector, if_pos hsector, characterKet_apply, hcubic, hpairing]
    rw [show registerPairing q error word - xSyndrome R error index =
        registerPairing q error word + -xSyndrome R error index by abel,
      phase_add]
    rw [characterKet_apply]
    ring
  · have hshiftSector : zSyndrome R (word - R.stabilizerRow index) ≠ 0 := by
      intro hzero
      apply hsector
      rw [← hshift]
      exact hzero
    simp only [xWordTransport_apply, WithLp.ofLp_smul, Pi.smul_apply,
      smul_eq_mul]
    rw [physicalU13_apply_phase, physicalU13_apply_phase,
      zSyndromeProjector_apply, zSyndromeProjector_apply,
      if_neg hshiftSector, if_neg hsector]
    simp
theorem characterKet_inner_physicalU13_zSyndromeProjector_eq_zero_of_xSyndrome_ne
    (R : CubicRowFamily q Logical Stabilizer Site)
    (label error : PrimeQuditRegisterLabel q Site)
    (hsyndrome : xSyndrome R label ≠ xSyndrome R error) :
    inner ℂ (characterKet q label)
      (physicalU13 q (zSyndromeProjector R 0 (characterKet q error))) = 0 := by
  classical
  obtain ⟨index, hindex⟩ :
      ∃ index, xSyndrome R label index ≠ xSyndrome R error index := by
    by_contra h
    push_neg at h
    exact hsyndrome (funext h)
  have hunit := (xWordTransport q (R.stabilizerRow index)).map_inner
    (characterKet q label)
    (physicalU13 q (zSyndromeProjector R 0 (characterKet q error)))
  have heigen :
      (phase q (-xSyndrome R error index) *
          starRingEnd ℂ (phase q (-xSyndrome R label index))) *
        inner ℂ (characterKet q label)
          (physicalU13 q (zSyndromeProjector R 0 (characterKet q error))) =
      inner ℂ (characterKet q label)
        (physicalU13 q (zSyndromeProjector R 0 (characterKet q error))) := by
    rw [xWordTransport_stabilizerRow_characterKet,
      xWordTransport_stabilizerRow_physicalU13_zSyndromeProjector] at hunit
    simpa only [inner_smul_left, inner_smul_right, ← mul_assoc] using hunit
  have hphase :
      phase q (-xSyndrome R error index) *
          starRingEnd ℂ (phase q (-xSyndrome R label index)) =
        phase q (xSyndrome R label index - xSyndrome R error index) := by
    rw [phase_conj, ← phase_add]
    congr 1
    abel
  rw [hphase] at heigen
  have hphase_ne_one :
      phase q (xSyndrome R label index - xSyndrome R error index) ≠ 1 := by
    intro hphase
    apply hindex
    exact sub_eq_zero.mp ((phase_eq_one_iff q _).1 hphase)
  have hfactor_ne_zero :
      phase q (xSyndrome R label index - xSyndrome R error index) - 1 ≠ 0 :=
    sub_ne_zero.mpr hphase_ne_one
  have hmul_zero :
      (phase q (xSyndrome R label index - xSyndrome R error index) - 1) *
        inner ℂ (characterKet q label)
          (physicalU13 q (zSyndromeProjector R 0 (characterKet q error))) = 0 := by
    rw [sub_mul, one_mul, heigen, sub_self]
  exact (mul_eq_zero.mp hmul_zero).resolve_left hfactor_ne_zero
theorem zSyndromeProjector_idempotent
    (R : CubicRowFamily q Logical Stabilizer Site) (syndrome : ZSyndrome R) :
    (zSyndromeProjector R syndrome).comp (zSyndromeProjector R syndrome) =
      zSyndromeProjector R syndrome := by
  classical
  rw [← Module.End.mul_eq_comp]
  unfold zSyndromeProjector
  rw [Fintype.sum_mul_sum]
  simp_rw [ite_mul, mul_ite, zero_mul, mul_zero, computationalRankOne_mul]
  apply Finset.sum_congr rfl
  intro left _
  by_cases hsector : zSyndrome R left = syndrome
  · rw [if_pos hsector]
    rw [Finset.sum_eq_single left]
    · simp [hsector]
    · intro right _ hne
      have hleftRight : left ≠ right := Ne.symm hne
      simp [hsector, hleftRight]
    · simp
  · simp [hsector]
theorem zSyndromeProjector_adjoint_comp
    (R : CubicRowFamily q Logical Stabilizer Site) (syndrome : ZSyndrome R) :
    (LinearMap.adjoint (zSyndromeProjector R syndrome)).comp
        (zSyndromeProjector R syndrome) = zSyndromeProjector R syndrome := by
  rw [zSyndromeProjector_adjoint]
  exact zSyndromeProjector_idempotent R syndrome
noncomputable def xSyndromeProjector
    (R : CubicRowFamily q Logical Stabilizer Site) (syndrome : Stabilizer → ZMod q) :
    Operator (PrimeQuditRegister q Site) :=
  ∑ word : PrimeQuditRegisterLabel q Site,
    if xSyndrome R word = syndrome then
      (InnerProductSpace.rankOne ℂ (characterKet q word)
        (characterKet q word)).toLinearMap
    else 0
theorem xSyndromeProjector_apply_physicalU13_zSyndromeProjector_characterKet
    (R : CubicRowFamily q Logical Stabilizer Site)
    (syndrome : Stabilizer → ZMod q)
    (error : PrimeQuditRegisterLabel q Site) :
    xSyndromeProjector R syndrome
        (physicalU13 q (zSyndromeProjector R 0 (characterKet q error))) =
      if xSyndrome R error = syndrome then
        physicalU13 q (zSyndromeProjector R 0 (characterKet q error))
      else 0 := by
  classical
  by_cases hsector : xSyndrome R error = syndrome
  · rw [if_pos hsector]
    unfold xSyndromeProjector
    simp only [LinearMap.sum_apply]
    have hcomplete :
        (∑ label : PrimeQuditRegisterLabel q Site,
          (InnerProductSpace.rankOne ℂ (characterKet q label)
            (characterKet q label)).toLinearMap)
          (physicalU13 q (zSyndromeProjector R 0 (characterKet q error))) =
        physicalU13 q (zSyndromeProjector R 0 (characterKet q error)) := by
      rw [sum_characterKet_rankOne_eq_one q]
      rfl
    calc
      (∑ label : PrimeQuditRegisterLabel q Site,
          (if xSyndrome R label = syndrome then
            (InnerProductSpace.rankOne ℂ (characterKet q label)
              (characterKet q label)).toLinearMap
          else 0)
            (physicalU13 q (zSyndromeProjector R 0 (characterKet q error)))) =
          ∑ label : PrimeQuditRegisterLabel q Site,
            (InnerProductSpace.rankOne ℂ (characterKet q label)
              (characterKet q label)).toLinearMap
                (physicalU13 q (zSyndromeProjector R 0 (characterKet q error))) := by
        apply Finset.sum_congr rfl
        intro label _
        by_cases hlabel : xSyndrome R label = syndrome
        · rw [if_pos hlabel]
        · rw [if_neg hlabel]
          simp only [LinearMap.zero_apply, InnerProductSpace.toLinearMap_rankOne,
            LinearMap.smulRight_apply, innerₛₗ_apply_apply]
          have hlabelError : xSyndrome R label ≠ xSyndrome R error := by
            intro heq
            exact hlabel (heq.trans hsector)
          rw [characterKet_inner_physicalU13_zSyndromeProjector_eq_zero_of_xSyndrome_ne
            R label error hlabelError]
          simp
      _ = physicalU13 q (zSyndromeProjector R 0 (characterKet q error)) := by
        simpa only [LinearMap.sum_apply] using hcomplete
  · rw [if_neg hsector]
    unfold xSyndromeProjector
    simp only [LinearMap.sum_apply]
    apply Finset.sum_eq_zero
    intro label _
    by_cases hlabel : xSyndrome R label = syndrome
    · rw [if_pos hlabel]
      simp only [InnerProductSpace.toLinearMap_rankOne, LinearMap.smulRight_apply,
        innerₛₗ_apply_apply]
      have hlabelError : xSyndrome R label ≠ xSyndrome R error := by
        intro heq
        exact hsector (heq.symm.trans hlabel)
      rw [characterKet_inner_physicalU13_zSyndromeProjector_eq_zero_of_xSyndrome_ne
        R label error hlabelError]
      simp
    · simp [hlabel]
theorem sum_xSyndromeProjector_eq_one
    (R : CubicRowFamily q Logical Stabilizer Site) :
    ∑ syndrome : Stabilizer → ZMod q, xSyndromeProjector R syndrome = 1 := by
  classical
  unfold xSyndromeProjector
  rw [Finset.sum_comm]
  simp_rw [Fintype.sum_ite_eq]
  exact sum_characterKet_rankOne_eq_one q
theorem xSyndromeProjector_adjoint
    (R : CubicRowFamily q Logical Stabilizer Site) (syndrome : Stabilizer → ZMod q) :
    LinearMap.adjoint (xSyndromeProjector R syndrome) = xSyndromeProjector R syndrome := by
  classical
  unfold xSyndromeProjector
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro word _
  by_cases hsector : xSyndrome R word = syndrome
  · rw [if_pos hsector]
    rw [LinearMap.adjoint_eq_toCLM_adjoint]
    change ((InnerProductSpace.rankOne ℂ (characterKet q word)
      (characterKet q word)).adjoint).toLinearMap = _
    rw [InnerProductSpace.adjoint_rankOne]
  · simp [hsector]
theorem xSyndromeProjector_idempotent
    (R : CubicRowFamily q Logical Stabilizer Site) (syndrome : Stabilizer → ZMod q) :
    (xSyndromeProjector R syndrome).comp (xSyndromeProjector R syndrome) =
      xSyndromeProjector R syndrome := by
  classical
  rw [← Module.End.mul_eq_comp]
  unfold xSyndromeProjector
  rw [Fintype.sum_mul_sum]
  simp_rw [ite_mul, mul_ite, zero_mul, mul_zero, characterRankOne_mul]
  apply Finset.sum_congr rfl
  intro left _
  by_cases hsector : xSyndrome R left = syndrome
  · rw [if_pos hsector]
    rw [Finset.sum_eq_single left]
    · simp [hsector]
    · intro right _ hne
      have hleftRight : left ≠ right := Ne.symm hne
      simp [hsector, hleftRight]
    · simp
  · simp [hsector]
theorem xSyndromeProjector_adjoint_comp
    (R : CubicRowFamily q Logical Stabilizer Site) (syndrome : Stabilizer → ZMod q) :
    (LinearMap.adjoint (xSyndromeProjector R syndrome)).comp
        (xSyndromeProjector R syndrome) = xSyndromeProjector R syndrome := by
  rw [xSyndromeProjector_adjoint]
  exact xSyndromeProjector_idempotent R syndrome
noncomputable def zSyndromeKrausFamily
    (R : CubicRowFamily q Logical Stabilizer Site) :
    FiniteKrausFamily (ZSyndrome R)
      (PrimeQuditRegister q Site) (PrimeQuditRegister q Site) where
  operator syndrome := zSyndromeProjector R syndrome
theorem zSyndromeKrausFamily_complete
    (R : CubicRowFamily q Logical Stabilizer Site) :
    (zSyndromeKrausFamily R).Complete := by
  rw [FiniteKrausFamily.Complete]
  simp only [zSyndromeKrausFamily]
  rw [Finset.sum_congr rfl (fun syndrome _ =>
    zSyndromeProjector_adjoint_comp R syndrome)]
  exact sum_zSyndromeProjector_eq_one R
noncomputable def zSyndromeInstrument
    (R : CubicRowFamily q Logical Stabilizer Site) :
    FiniteInstrument (ZSyndrome R) (ZSyndrome R)
      (PrimeQuditRegister q Site) (PrimeQuditRegister q Site) where
  kraus := zSyndromeKrausFamily R
  observe := id
theorem zSyndromeInstrument_complete
    (R : CubicRowFamily q Logical Stabilizer Site) :
    (zSyndromeInstrument R).kraus.Complete :=
  zSyndromeKrausFamily_complete R
noncomputable def xSyndromeKrausFamily
    (R : CubicRowFamily q Logical Stabilizer Site) :
    FiniteKrausFamily (Stabilizer → ZMod q)
      (PrimeQuditRegister q Site) (PrimeQuditRegister q Site) where
  operator syndrome := xSyndromeProjector R syndrome
theorem xSyndromeKrausFamily_complete
    (R : CubicRowFamily q Logical Stabilizer Site) :
    (xSyndromeKrausFamily R).Complete := by
  rw [FiniteKrausFamily.Complete]
  simp only [xSyndromeKrausFamily]
  rw [Finset.sum_congr rfl (fun syndrome _ =>
    xSyndromeProjector_adjoint_comp R syndrome)]
  exact sum_xSyndromeProjector_eq_one R
noncomputable def xSyndromeInstrument
    (R : CubicRowFamily q Logical Stabilizer Site) :
    FiniteInstrument (Stabilizer → ZMod q) (Stabilizer → ZMod q)
      (PrimeQuditRegister q Site) (PrimeQuditRegister q Site) where
  kraus := xSyndromeKrausFamily R
  observe := id
noncomputable def zSyndromeCorrection
    (R : CubicRowFamily q Logical Stabilizer Site) (mu : ZSyndrome R) :
    UnitaryTransport (PrimeQuditRegister q Site) (PrimeQuditRegister q Site) :=
  ((physicalU13 q).symm.trans
    (xWordTransport q (-zSyndromeRepresentative R mu))).trans (physicalU13 q)
theorem zSyndromeCorrection_apply_zSyndromeProjector_magicRegisterKet
    (R : CubicRowFamily q Logical Stabilizer Site) (mu : ZSyndrome R)
    (error : PrimeQuditRegisterLabel q Site) :
    zSyndromeCorrection R mu
        (zSyndromeProjector R mu (magicRegisterKet q error)) =
      phase q (registerPairing q error (zSyndromeRepresentative R mu)) •
        physicalU13 q (zSyndromeProjector R 0 (characterKet q error)) := by
  change physicalU13 q
      (xWordTransport q (-zSyndromeRepresentative R mu)
        ((physicalU13 q).symm
          (zSyndromeProjector R mu (magicRegisterKet q error)))) = _
  rw [physicalU13_symm_zSyndromeProjector,
    inverseTransversal_magicRegisterKet,
    xWordTransport_neg_zSyndromeProjector,
    xWordTransport_neg_characterKet]
  simp only [map_smul]
noncomputable def correctionThenXKrausFamily
    (R : CubicRowFamily q Logical Stabilizer Site) (mu : ZSyndrome R) :
    FiniteKrausFamily (Stabilizer → ZMod q)
      (PrimeQuditRegister q Site) (PrimeQuditRegister q Site) :=
  (xSyndromeKrausFamily R).unitaryTransport (zSyndromeCorrection R mu).symm
    (UnitaryTransport.identity (PrimeQuditRegister q Site))
theorem correctionThenXKrausFamily_complete
    (R : CubicRowFamily q Logical Stabilizer Site) (mu : ZSyndrome R) :
    (correctionThenXKrausFamily R mu).Complete := by
  exact (xSyndromeKrausFamily R).unitaryTransport_complete
    (zSyndromeCorrection R mu).symm
    (UnitaryTransport.identity (PrimeQuditRegister q Site))
    (xSyndromeKrausFamily_complete R)
noncomputable def kt19ProtocolKrausFamily
    (R : CubicRowFamily q Logical Stabilizer Site) :
    FiniteKrausFamily (ZSyndrome R × (Stabilizer → ZMod q))
      (PrimeQuditRegister q Site) (PrimeQuditRegister q Site) where
  operator branch :=
    (xSyndromeProjector R branch.2).comp
      ((zSyndromeCorrection R branch.1).toLinearEquiv.toLinearMap.comp
        (zSyndromeProjector R branch.1))
theorem kt19ProtocolKrausFamily_apply_magicRegisterKet
    (R : CubicRowFamily q Logical Stabilizer Site)
    (mu : ZSyndrome R) (sigma : Stabilizer → ZMod q)
    (error : PrimeQuditRegisterLabel q Site) :
    (kt19ProtocolKrausFamily R).operator (mu, sigma) (magicRegisterKet q error) =
      if xSyndrome R error = sigma then
        phase q (registerPairing q error (zSyndromeRepresentative R mu)) •
          physicalU13 q (zSyndromeProjector R 0 (characterKet q error))
      else 0 := by
  change xSyndromeProjector R sigma
      (zSyndromeCorrection R mu
        (zSyndromeProjector R mu (magicRegisterKet q error))) = _
  rw [zSyndromeCorrection_apply_zSyndromeProjector_magicRegisterKet]
  rw [map_smul,
    xSyndromeProjector_apply_physicalU13_zSyndromeProjector_characterKet]
  by_cases hsyndrome : xSyndrome R error = sigma <;> simp [hsyndrome]
noncomputable def kt19ProtocolInstrument
    (R : CubicRowFamily q Logical Stabilizer Site) :
    FiniteInstrument (ZSyndrome R × (Stabilizer → ZMod q))
      (ZSyndrome R × (Stabilizer → ZMod q))
      (PrimeQuditRegister q Site) (PrimeQuditRegister q Site) where
  kraus := kt19ProtocolKrausFamily R
  observe := id
theorem kt19ProtocolInstrument_complete
    (R : CubicRowFamily q Logical Stabilizer Site) :
    (kt19ProtocolInstrument R).kraus.Complete := by
  let afterZ : (mu : ZSyndrome R) →
      FiniteInstrument (Stabilizer → ZMod q) (Stabilizer → ZMod q)
        (PrimeQuditRegister q Site) (PrimeQuditRegister q Site) :=
    fun mu =>
      { kraus := correctionThenXKrausFamily R mu
        observe := id }
  have hbound := (zSyndromeInstrument R).bind_complete afterZ
    (zSyndromeInstrument_complete R) (fun mu => correctionThenXKrausFamily_complete R mu)
  simpa [kt19ProtocolInstrument, kt19ProtocolKrausFamily, afterZ,
    correctionThenXKrausFamily, FiniteInstrument.bind, UnitaryTransport.symm,
    UnitaryTransport.identity, xSyndromeKrausFamily, zSyndromeInstrument,
    zSyndromeKrausFamily, LinearMap.comp_assoc] using hbound
noncomputable def kt19ProtocolChannel
    (R : CubicRowFamily q Logical Stabilizer Site) :
    QuantumChannel (PrimeQuditRegister q Site) (PrimeQuditRegister q Site) :=
  (kt19ProtocolInstrument R).kraus.toQuantumChannel
    (kt19ProtocolInstrument_complete R)
def kt19SyndromeOutcome (sigma : Stabilizer → ZMod q) : DistillationOutcome :=
  if sigma = 0 then .accepted else .rejected
def kt19Accepts (R : CubicRowFamily q Logical Stabilizer Site)
    (branch : ZSyndrome R × (Stabilizer → ZMod q)) : Bool :=
  decide (branch.2 = 0)
noncomputable def kt19DistillationInstrument
    (R : CubicRowFamily q Logical Stabilizer Site) :
    FiniteInstrument (ZSyndrome R × (Stabilizer → ZMod q)) DistillationOutcome
      (PrimeQuditRegister q Site) (PrimeQuditRegister q Site) :=
  (kt19ProtocolInstrument R).binaryCoarsen (kt19Accepts R)
theorem kt19DistillationInstrument_complete
    (R : CubicRowFamily q Logical Stabilizer Site) :
    (kt19DistillationInstrument R).kraus.Complete :=
  (kt19ProtocolInstrument R).binaryCoarsen_complete (kt19Accepts R)
    (kt19ProtocolInstrument_complete R)
noncomputable def kt19DecoderEncodingIsometry
    (R : CubicRowFamily q Logical Stabilizer Site) :
    PrimeQuditRegister q Logical →ₗᵢ[Complex] PrimeQuditRegister q Site := by
  letI : DecidableEq Logical := Classical.decEq _
  let physical : UnitaryTransport (PrimeQuditRegister q Site)
      (PrimeQuditRegister q Site) := physicalU13 q
  let logical : UnitaryTransport (PrimeQuditRegister q Logical)
      (PrimeQuditRegister q Logical) := physicalU13 q
  exact physical.toLinearIsometryEquiv.toLinearIsometry.comp
    (R.encodingIsometry.comp logical.symm.toLinearIsometryEquiv.toLinearIsometry)
def kt19DecoderCodeBranch
    (R : CubicRowFamily q Logical Stabilizer Site) :
    PrimeQuditRegister q Site →ₗ[Complex] PrimeQuditRegister q Logical :=
  LinearMap.adjoint (kt19DecoderEncodingIsometry R).toLinearMap
@[simp]
theorem kt19DecoderCodeBranch_encoded
    (R : CubicRowFamily q Logical Stabilizer Site)
    (psi : PrimeQuditRegister q Logical) :
    kt19DecoderCodeBranch R (kt19DecoderEncodingIsometry R psi) = psi := by
  change LinearMap.adjoint (kt19DecoderEncodingIsometry R).toLinearMap
    ((kt19DecoderEncodingIsometry R).toLinearMap psi) = psi
  exact LinearMap.congr_fun (kt19DecoderEncodingIsometry R).adjoint_comp_self' psi
theorem adjoint_kt19DecoderCodeBranch
    (R : CubicRowFamily q Logical Stabilizer Site) :
    LinearMap.adjoint (kt19DecoderCodeBranch R) =
      (kt19DecoderEncodingIsometry R).toLinearMap := by
  rw [kt19DecoderCodeBranch, LinearMap.adjoint_adjoint]
def kt19DecoderCodeProjector
    (R : CubicRowFamily q Logical Stabilizer Site) :
    Operator (PrimeQuditRegister q Site) :=
  (LinearMap.adjoint (kt19DecoderCodeBranch R)).comp (kt19DecoderCodeBranch R)
@[simp]
theorem kt19DecoderCodeProjector_encoded
    (R : CubicRowFamily q Logical Stabilizer Site)
    (psi : PrimeQuditRegister q Logical) :
    kt19DecoderCodeProjector R (kt19DecoderEncodingIsometry R psi) =
      kt19DecoderEncodingIsometry R psi := by
  change LinearMap.adjoint (kt19DecoderCodeBranch R)
    (kt19DecoderCodeBranch R (kt19DecoderEncodingIsometry R psi)) =
      kt19DecoderEncodingIsometry R psi
  rw [kt19DecoderCodeBranch_encoded, adjoint_kt19DecoderCodeBranch]
  rfl
theorem kt19DecoderCodeBranch_comp_adjoint
    (R : CubicRowFamily q Logical Stabilizer Site) :
    (kt19DecoderCodeBranch R).comp
        (LinearMap.adjoint (kt19DecoderCodeBranch R)) = 1 := by
  rw [adjoint_kt19DecoderCodeBranch, kt19DecoderCodeBranch]
  exact (kt19DecoderEncodingIsometry R).adjoint_comp_self'
theorem kt19DecoderCodeProjector_idempotent
    (R : CubicRowFamily q Logical Stabilizer Site) :
    (kt19DecoderCodeProjector R).comp (kt19DecoderCodeProjector R) =
      kt19DecoderCodeProjector R := by
  rw [kt19DecoderCodeProjector]
  calc
    ((LinearMap.adjoint (kt19DecoderCodeBranch R)).comp (kt19DecoderCodeBranch R)).comp
        ((LinearMap.adjoint (kt19DecoderCodeBranch R)).comp
          (kt19DecoderCodeBranch R)) =
        (LinearMap.adjoint (kt19DecoderCodeBranch R)).comp
          (((kt19DecoderCodeBranch R).comp
            (LinearMap.adjoint (kt19DecoderCodeBranch R))).comp
              (kt19DecoderCodeBranch R)) := by
            ext psi
            rfl
    _ = (LinearMap.adjoint (kt19DecoderCodeBranch R)).comp
          ((1 : Operator (PrimeQuditRegister q Logical)).comp
            (kt19DecoderCodeBranch R)) := by
            rw [kt19DecoderCodeBranch_comp_adjoint]
    _ = (LinearMap.adjoint (kt19DecoderCodeBranch R)).comp
          (kt19DecoderCodeBranch R) := by
            ext psi
            rfl
theorem kt19DecoderCodeProjector_adjoint
    (R : CubicRowFamily q Logical Stabilizer Site) :
    LinearMap.adjoint (kt19DecoderCodeProjector R) = kt19DecoderCodeProjector R := by
  simp [kt19DecoderCodeProjector, LinearMap.adjoint_comp]
def kt19DecoderComplementProjector
    (R : CubicRowFamily q Logical Stabilizer Site) :
    Operator (PrimeQuditRegister q Site) :=
  1 - kt19DecoderCodeProjector R
theorem kt19DecoderComplementProjector_adjoint
    (R : CubicRowFamily q Logical Stabilizer Site) :
    LinearMap.adjoint (kt19DecoderComplementProjector R) =
      kt19DecoderComplementProjector R := by
  simp [kt19DecoderComplementProjector, kt19DecoderCodeProjector_adjoint]
theorem kt19DecoderComplementProjector_idempotent
    (R : CubicRowFamily q Logical Stabilizer Site) :
    (kt19DecoderComplementProjector R).comp
        (kt19DecoderComplementProjector R) =
      kt19DecoderComplementProjector R := by
  ext psi
  have hprojector := LinearMap.congr_fun
    (kt19DecoderCodeProjector_idempotent R) psi
  simp only [kt19DecoderComplementProjector, LinearMap.comp_apply,
    LinearMap.sub_apply, Module.End.one_apply, map_sub] at hprojector ⊢
  rw [hprojector]
  abel_nf
@[simp]
theorem kt19DecoderComplementProjector_encoded
    (R : CubicRowFamily q Logical Stabilizer Site)
    (psi : PrimeQuditRegister q Logical) :
    kt19DecoderComplementProjector R (kt19DecoderEncodingIsometry R psi) = 0 := by
  simp only [kt19DecoderComplementProjector, LinearMap.sub_apply, Module.End.one_apply]
  rw [kt19DecoderCodeProjector_encoded]
  abel_nf
noncomputable def kt19DecoderFallbackState
    (R : CubicRowFamily q Logical Stabilizer Site) : PrimeQuditRegister q Logical := by
  classical
  exact registerBasisKet q (fun _ => 0)
theorem kt19DecoderFallbackState_inner_self
    (R : CubicRowFamily q Logical Stabilizer Site) :
    inner Complex (kt19DecoderFallbackState R) (kt19DecoderFallbackState R) = 1 := by
  classical
  simp [kt19DecoderFallbackState, registerBasisKet, EuclideanSpace.basisFun_apply]
theorem kt19DecoderFallbackState_normSq
    (R : CubicRowFamily q Logical Stabilizer Site) :
    ‖kt19DecoderFallbackState R‖ ^ 2 = 1 := by
  rw [InnerProductSpace.norm_sq_eq_re_inner (𝕜 := Complex),
    kt19DecoderFallbackState_inner_self]
  norm_num
noncomputable def kt19DecoderPhysicalBasis
    (R : CubicRowFamily q Logical Stabilizer Site) :=
  stdOrthonormalBasis Complex (PrimeQuditRegister q Site)
def kt19ComplementDecoderBranch
    (R : CubicRowFamily q Logical Stabilizer Site)
    (i : Fin (Module.finrank Complex (PrimeQuditRegister q Site))) :
    PrimeQuditRegister q Site →ₗ[Complex] PrimeQuditRegister q Logical :=
  (InnerProductSpace.rankOne Complex (kt19DecoderFallbackState R)
    (kt19DecoderComplementProjector R (kt19DecoderPhysicalBasis R i))).toLinearMap
theorem kt19ComplementDecoderBranch_adjoint_comp
    (R : CubicRowFamily q Logical Stabilizer Site)
    (i : Fin (Module.finrank Complex (PrimeQuditRegister q Site))) :
    (LinearMap.adjoint (kt19ComplementDecoderBranch R i)).comp
        (kt19ComplementDecoderBranch R i) =
      (InnerProductSpace.rankOne Complex
        (kt19DecoderComplementProjector R (kt19DecoderPhysicalBasis R i))
        (kt19DecoderComplementProjector R (kt19DecoderPhysicalBasis R i))).toLinearMap := by
  have hadjoint : LinearMap.adjoint
      ((InnerProductSpace.rankOne Complex (kt19DecoderFallbackState R)
        (kt19DecoderComplementProjector R (kt19DecoderPhysicalBasis R i))).toLinearMap) =
      (InnerProductSpace.rankOne Complex
        (kt19DecoderComplementProjector R (kt19DecoderPhysicalBasis R i))
        (kt19DecoderFallbackState R)).toLinearMap := by
    rw [LinearMap.adjoint_eq_toCLM_adjoint]
    change ((InnerProductSpace.rankOne Complex (kt19DecoderFallbackState R)
      (kt19DecoderComplementProjector R (kt19DecoderPhysicalBasis R i))).adjoint).toLinearMap = _
    rw [InnerProductSpace.adjoint_rankOne]
  apply LinearMap.ext
  intro psi
  simp only [kt19ComplementDecoderBranch]
  rw [hadjoint]
  have hnormSq : (↑‖kt19DecoderFallbackState R‖ : Complex) ^ 2 = 1 := by
    norm_cast
    exact kt19DecoderFallbackState_normSq R
  simp [LinearMap.comp_apply, hnormSq]
theorem sum_kt19ComplementDecoderBranch_adjoint_comp
    (R : CubicRowFamily q Logical Stabilizer Site) :
    ∑ i : Fin (Module.finrank Complex (PrimeQuditRegister q Site)),
        (LinearMap.adjoint (kt19ComplementDecoderBranch R i)).comp
          (kt19ComplementDecoderBranch R i) =
      kt19DecoderComplementProjector R := by
  simp_rw [kt19ComplementDecoderBranch_adjoint_comp]
  calc
    (∑ i, (InnerProductSpace.rankOne Complex
      (kt19DecoderComplementProjector R (kt19DecoderPhysicalBasis R i))
      (kt19DecoderComplementProjector R (kt19DecoderPhysicalBasis R i))).toLinearMap) =
      (kt19DecoderComplementProjector R).comp
        (LinearMap.adjoint (kt19DecoderComplementProjector R)) := by
        apply LinearMap.ext
        intro psi
        simp only [LinearMap.sum_apply, LinearMap.comp_apply]
        rw [← (kt19DecoderPhysicalBasis R).sum_repr'
          (LinearMap.adjoint (kt19DecoderComplementProjector R) psi)]
        simp only [map_sum, map_smul]
        apply Finset.sum_congr rfl
        intro i _hi
        rw [LinearMap.adjoint_inner_right]
        rfl
    _ = (kt19DecoderComplementProjector R).comp
        (kt19DecoderComplementProjector R) := by
      rw [kt19DecoderComplementProjector_adjoint]
    _ = kt19DecoderComplementProjector R :=
      kt19DecoderComplementProjector_idempotent R
def kt19DecoderKrausFamily
    (R : CubicRowFamily q Logical Stabilizer Site) :
    FiniteKrausFamily
      (Sum Unit (Fin (Module.finrank Complex (PrimeQuditRegister q Site))))
      (PrimeQuditRegister q Site) (PrimeQuditRegister q Logical) where
  operator
    | .inl _ => kt19DecoderCodeBranch R
    | .inr i => kt19ComplementDecoderBranch R i
theorem kt19DecoderKrausFamily_complete
    (R : CubicRowFamily q Logical Stabilizer Site) :
    (kt19DecoderKrausFamily R).Complete := by
  rw [FiniteKrausFamily.Complete, Fintype.sum_sum_type]
  change (∑ _ : Unit, kt19DecoderCodeProjector R) +
      (∑ i : Fin (Module.finrank Complex (PrimeQuditRegister q Site)),
        (LinearMap.adjoint (kt19ComplementDecoderBranch R i)).comp
          (kt19ComplementDecoderBranch R i)) = 1
  rw [Fintype.sum_unique, sum_kt19ComplementDecoderBranch_adjoint_comp]
  simp [kt19DecoderComplementProjector]
noncomputable def kt19DecoderChannel
    (R : CubicRowFamily q Logical Stabilizer Site) :
    QuantumChannel (PrimeQuditRegister q Site) (PrimeQuditRegister q Logical) :=
  (kt19DecoderKrausFamily R).toQuantumChannel (kt19DecoderKrausFamily_complete R)
theorem kt19SandwichRankOne {H K : Type u}
    [NormedAddCommGroup H] [InnerProductSpace Complex H] [FiniteQuantumSystem H]
    [NormedAddCommGroup K] [InnerProductSpace Complex K] [FiniteQuantumSystem K]
    (L : H →ₗ[Complex] K) (psi : H) :
    L.comp ((InnerProductSpace.rankOne Complex psi psi).toLinearMap.comp
      (LinearMap.adjoint L)) =
      (InnerProductSpace.rankOne Complex (L psi) (L psi)).toLinearMap := by
  ext x
  simp [LinearMap.comp_apply, InnerProductSpace.rankOne_apply,
    LinearMap.adjoint_inner_right]
noncomputable def kt19IIDResource
    (mu : ZMod q → ℝ) (hmu_nonneg : ∀ a : ZMod q, 0 ≤ mu a)
    (hmu_sum : ∑ a : ZMod q, mu a = 1) :
    DensityOperator (PrimeQuditRegister q Site) :=
  magicRegisterResource q mu hmu_nonneg hmu_sum
noncomputable def kt19WordInputDensity
    (error : PrimeQuditRegisterLabel q Site) :
    DensityOperator (PrimeQuditRegister q Site) :=
  DensityOperator.pureDensity (magicRegisterKet q error) (by
    rw [InnerProductSpace.norm_sq_eq_re_inner (𝕜 := Complex),
      magicRegisterKet_inner_self]
    norm_num)
abbrev KT19SingleResourceSite : Type u := ULift.{u} PUnit
abbrev KT19SingleQudit (q : Nat) [NeZero q] : Type u :=
  PrimeQuditRegister q KT19SingleResourceSite.{u}
def kt19SingleSiteLabelEquiv :
    ZMod q ≃ PrimeQuditRegisterLabel q KT19SingleResourceSite.{u} where
  toFun label := fun _ => label
  invFun word := word default
  left_inv _ := rfl
  right_inv word := by
    funext site
    rw [Subsingleton.elim site default]
def kt19SingleSiteLabel (label : ZMod q) :
    PrimeQuditRegisterLabel q KT19SingleResourceSite.{u} :=
  kt19SingleSiteLabelEquiv label
noncomputable def kt19SingleSiteWordDensity
    (word : PrimeQuditRegisterLabel q KT19SingleResourceSite.{u}) :
    DensityOperator (KT19SingleQudit.{u} q) :=
  DensityOperator.pureDensity (magicRegisterKet q word) (by
    rw [InnerProductSpace.norm_sq_eq_re_inner (𝕜 := Complex),
      magicRegisterKet_inner_self]
    norm_num)
noncomputable def kt19SingleSiteResource
    (mu : ZMod q → ℝ) (hmu_nonneg : ∀ a : ZMod q, 0 ≤ mu a)
    (hmu_sum : ∑ a : ZMod q, mu a = 1) :
    DensityOperator (KT19SingleQudit.{u} q) :=
  magicRegisterResource q mu hmu_nonneg hmu_sum
theorem kt19SingleSiteResource_toOperator
    (mu : ZMod q → ℝ) (hmu_nonneg : ∀ a : ZMod q, 0 ≤ mu a)
    (hmu_sum : ∑ a : ZMod q, mu a = 1) :
    (kt19SingleSiteResource mu hmu_nonneg hmu_sum).toOperator =
      ∑ word : PrimeQuditRegisterLabel q KT19SingleResourceSite.{u},
        (wordProbability q mu word : Complex) •
          (kt19SingleSiteWordDensity word).toOperator := by
  unfold kt19SingleSiteResource magicRegisterResource
  rw [DensityOperator.convexCombination_toOperator]
  rfl
theorem kt19SingleSite_sandwich_rankOne
    (observed : PrimeQuditRegisterLabel q KT19SingleResourceSite.{u})
    (psi : KT19SingleQudit.{u} q) :
    ((magicRegisterKrausFamily q).operator observed).comp
        ((InnerProductSpace.rankOne Complex psi psi).toLinearMap.comp
          (LinearMap.adjoint ((magicRegisterKrausFamily q).operator observed))) =
      (InnerProductSpace.rankOne Complex
        ((magicRegisterKrausFamily q).operator observed psi)
        ((magicRegisterKrausFamily q).operator observed psi)).toLinearMap := by
  ext x
  simp [LinearMap.comp_apply, InnerProductSpace.rankOne_apply,
    LinearMap.adjoint_inner_right]
theorem kt19SingleSiteKraus_apply_magicRegisterKet
    (observed actual : PrimeQuditRegisterLabel q KT19SingleResourceSite.{u}) :
    (magicRegisterKrausFamily q).operator observed (magicRegisterKet q actual) =
      if observed = actual then magicRegisterKet q actual else 0 := by
  simp only [magicRegisterKrausFamily, InnerProductSpace.toLinearMap_rankOne,
    LinearMap.smulRight_apply, innerₛₗ_apply_apply]
  by_cases hlabel : observed = actual
  · subst actual
    rw [magicRegisterKet_inner_self]
    simp only [one_smul, if_pos]
  · rw [magicRegisterKet_inner]
    simp only [if_neg hlabel, zero_smul]
theorem kt19SingleSiteInstrument_branchOperator_eq_sandwich
    (observed : PrimeQuditRegisterLabel q KT19SingleResourceSite.{u})
    (A : Operator (KT19SingleQudit.{u} q)) :
    (magicRegisterInstrument q).branchOperator observed A =
      ((magicRegisterKrausFamily q).operator observed).comp
        (A.comp (LinearMap.adjoint ((magicRegisterKrausFamily q).operator observed))) := by
  classical
  rw [FiniteInstrument.branchOperator_apply]
  rw [Fintype.sum_eq_single observed]
  · simp [magicRegisterInstrument]
  · intro other hother
    simp [magicRegisterInstrument, hother]
theorem kt19SingleSiteInstrument_branch_wordDensity
    (observed actual : PrimeQuditRegisterLabel q KT19SingleResourceSite.{u}) :
    (magicRegisterInstrument q).branchOperator observed
        (kt19SingleSiteWordDensity actual).toOperator =
      if observed = actual then (kt19SingleSiteWordDensity actual).toOperator else 0 := by
  rw [kt19SingleSiteInstrument_branchOperator_eq_sandwich]
  unfold kt19SingleSiteWordDensity
  rw [DensityOperator.pureDensity_toOperator, kt19SingleSite_sandwich_rankOne,
    kt19SingleSiteKraus_apply_magicRegisterKet]
  by_cases hlabel : observed = actual
  · rw [if_pos hlabel]
    simp only [if_pos hlabel]
  · rw [if_neg hlabel]
    apply LinearMap.ext
    intro psi
    simp only [InnerProductSpace.toLinearMap_rankOne,
      LinearMap.smulRight_apply, innerₛₗ_apply_apply, inner_zero_left,
      zero_smul, if_neg hlabel]
    simp only [LinearMap.zero_apply]
theorem kt19SingleSiteInstrument_bornWeight_resource
    (mu : ZMod q → ℝ) (hmu_nonneg : ∀ a : ZMod q, 0 ≤ mu a)
    (hmu_sum : ∑ a : ZMod q, mu a = 1)
    (observed : PrimeQuditRegisterLabel q KT19SingleResourceSite.{u}) :
    (magicRegisterInstrument q).bornWeight observed
        (kt19SingleSiteResource mu hmu_nonneg hmu_sum) =
      wordProbability q mu observed := by
  classical
  unfold FiniteInstrument.bornWeight
  rw [kt19SingleSiteResource_toOperator,
    FiniteInstrument.branchOperator_sum, map_sum, Complex.re_sum]
  simp_rw [FiniteInstrument.branchOperator_smul, map_smul,
    kt19SingleSiteInstrument_branch_wordDensity]
  rw [Finset.sum_eq_single observed]
  · simp [DensityOperator.trace_toOperator]
  · intro other _ hother
    simp [hother.symm]
  · simp
theorem kt19SingleSite_wordProbability
    (mu : ZMod q → ℝ) (label : ZMod q) :
    wordProbability q mu (kt19SingleSiteLabel label) = mu label := by
  unfold wordProbability kt19SingleSiteLabel kt19SingleSiteLabelEquiv
  rw [Fintype.prod_unique]
  rfl
noncomputable def kt19NoisySingleSiteResources
    (mu : ZMod q → ℝ) (hmu_nonneg : ∀ a : ZMod q, 0 ≤ mu a)
    (hmu_sum : ∑ a : ZMod q, mu a = 1) :
    ResourceInput (Fintype.card Site) (KT19SingleQudit.{u} q) :=
  fun _ => kt19SingleSiteResource mu hmu_nonneg hmu_sum
noncomputable def kt19ResourceSiteEquiv :
    Site ≃ Fin (Fintype.card Site) :=
  Fintype.equivFin Site
noncomputable def kt19MeasuredWordProbability
    (inputs : ResourceInput (Fintype.card Site) (KT19SingleQudit.{u} q))
    (error : PrimeQuditRegisterLabel q Site) : ℝ :=
  ∏ site : Site,
    (magicRegisterInstrument q).bornWeight (kt19SingleSiteLabel (error site))
      (inputs (kt19ResourceSiteEquiv (Site := Site) site))
theorem kt19MeasuredWordProbability_nonneg
    (inputs : ResourceInput (Fintype.card Site) (KT19SingleQudit.{u} q))
    (error : PrimeQuditRegisterLabel q Site) :
    0 ≤ kt19MeasuredWordProbability (q := q) inputs error := by
  unfold kt19MeasuredWordProbability
  exact Finset.prod_nonneg (fun site _ =>
    (magicRegisterInstrument q).bornWeight_nonneg (kt19SingleSiteLabel (error site))
      (inputs (kt19ResourceSiteEquiv (Site := Site) site)))
theorem kt19MeasuredWordProbability_sum_eq_one
    (inputs : ResourceInput (Fintype.card Site) (KT19SingleQudit.{u} q)) :
    ∑ error : PrimeQuditRegisterLabel q Site,
      kt19MeasuredWordProbability (q := q) inputs error = 1 := by
  classical
  have hsite (site : Site) :
      ∑ label : ZMod q,
        (magicRegisterInstrument q).bornWeight (kt19SingleSiteLabel label)
          (inputs (kt19ResourceSiteEquiv (Site := Site) site)) = 1 := by
    calc
      _ = ∑ word : PrimeQuditRegisterLabel q KT19SingleResourceSite.{u},
          (magicRegisterInstrument q).bornWeight word
            (inputs (kt19ResourceSiteEquiv (Site := Site) site)) := by
        exact Fintype.sum_equiv kt19SingleSiteLabelEquiv _ _ (fun _ => rfl)
      _ = 1 := (magicRegisterInstrument q).sum_bornWeight_eq_one
        (magicRegisterKrausFamily_complete q)
        (inputs (kt19ResourceSiteEquiv (Site := Site) site))
  change (∑ error : Site → ZMod q, ∏ site : Site,
      (magicRegisterInstrument q).bornWeight (kt19SingleSiteLabel (error site))
        (inputs (kt19ResourceSiteEquiv (Site := Site) site))) = 1
  rw [labelUniv_eq_piUniv]
  rw [Fintype_sum_fn_prod (R := ℝ) (ι := Site) (α := ZMod q)
    (fun site label =>
      (magicRegisterInstrument q).bornWeight (kt19SingleSiteLabel label)
        (inputs (kt19ResourceSiteEquiv (Site := Site) site)))]
  simp_rw [hsite]
  simp
noncomputable def kt19PrepareInput
    (inputs : ResourceInput (Fintype.card Site) (KT19SingleQudit.{u} q)) :
    DensityOperator (PrimeQuditRegister q Site) :=
  DensityOperator.convexCombination Finset.univ
    (kt19MeasuredWordProbability (q := q) inputs)
    (kt19WordInputDensity (q := q) (Site := Site))
    (fun error _ => kt19MeasuredWordProbability_nonneg inputs error)
    (kt19MeasuredWordProbability_sum_eq_one inputs)
theorem kt19MeasuredWordProbability_noisySingleSiteResources
    (mu : ZMod q → ℝ) (hmu_nonneg : ∀ a : ZMod q, 0 ≤ mu a)
    (hmu_sum : ∑ a : ZMod q, mu a = 1)
    (error : PrimeQuditRegisterLabel q Site) :
    kt19MeasuredWordProbability (q := q)
        (kt19NoisySingleSiteResources (Site := Site) mu hmu_nonneg hmu_sum) error =
      wordProbability q mu error := by
  unfold kt19MeasuredWordProbability kt19NoisySingleSiteResources wordProbability
  apply Finset.prod_congr rfl
  intro site _
  rw [kt19SingleSiteInstrument_bornWeight_resource,
    kt19SingleSite_wordProbability]
theorem kt19PrepareInput_noisySingleSiteResources
    (mu : ZMod q → ℝ) (hmu_nonneg : ∀ a : ZMod q, 0 ≤ mu a)
    (hmu_sum : ∑ a : ZMod q, mu a = 1) :
    kt19PrepareInput (Site := Site)
        (kt19NoisySingleSiteResources (Site := Site) mu hmu_nonneg hmu_sum) =
      kt19IIDResource (Site := Site) mu hmu_nonneg hmu_sum := by
  apply DensityOperator.ext_toOperator
  unfold kt19PrepareInput kt19IIDResource magicRegisterResource
  rw [DensityOperator.convexCombination_toOperator,
    DensityOperator.convexCombination_toOperator]
  unfold DensityOperator.convexCombinationOperator
  apply Finset.sum_congr rfl
  intro error _
  rw [kt19MeasuredWordProbability_noisySingleSiteResources]
  rfl
theorem kt19ProtocolInstrument_branchOperator_wordInputDensity
    (R : CubicRowFamily q Logical Stabilizer Site)
    (mu : ZSyndrome R) (sigma : Stabilizer → ZMod q)
    (error : PrimeQuditRegisterLabel q Site) :
    (kt19ProtocolInstrument R).branchOperator (mu, sigma)
        (kt19WordInputDensity (Site := Site) error).toOperator =
      if xSyndrome R error = sigma then
        (InnerProductSpace.rankOne Complex
          (phase q (registerPairing q error (zSyndromeRepresentative R mu)) •
            physicalU13 q (zSyndromeProjector R 0 (characterKet q error)))
          (phase q (registerPairing q error (zSyndromeRepresentative R mu)) •
            physicalU13 q (zSyndromeProjector R 0 (characterKet q error)))).toLinearMap
      else 0 := by
  classical
  rw [FiniteInstrument.branchOperator_apply]
  simp only [kt19ProtocolInstrument, id_eq]
  rw [Finset.sum_eq_single (mu, sigma)]
  · simp only [if_pos, kt19WordInputDensity, DensityOperator.pureDensity_toOperator]
    rw [kt19SandwichRankOne,
      kt19ProtocolKrausFamily_apply_magicRegisterKet]
    by_cases hsyndrome : xSyndrome R error = sigma <;> simp [hsyndrome]
  · intro branch _ hbranch
    simp [hbranch]
  · simp
theorem kt19ProtocolInstrument_branchOperator_wordInputDensity_eq_zero_of_xSyndrome_ne
    (R : CubicRowFamily q Logical Stabilizer Site)
    (mu : ZSyndrome R) (sigma : Stabilizer → ZMod q)
    (error : PrimeQuditRegisterLabel q Site)
    (hsyndrome : xSyndrome R error ≠ sigma) :
    (kt19ProtocolInstrument R).branchOperator (mu, sigma)
    (kt19WordInputDensity (Site := Site) error).toOperator = 0 := by
  rw [kt19ProtocolInstrument_branchOperator_wordInputDensity, if_neg hsyndrome]
theorem kt19DistillationInstrument_accepted_branchOperator_wordInputDensity_eq_zero_of_xSyndrome_ne_zero
    (R : CubicRowFamily q Logical Stabilizer Site)
    (error : PrimeQuditRegisterLabel q Site)
    (hsyndrome : xSyndrome R error ≠ 0) :
    (kt19DistillationInstrument R).branchOperator .accepted
        (kt19WordInputDensity (Site := Site) error).toOperator = 0 := by
  classical
  rw [kt19DistillationInstrument,
    FiniteInstrument.binaryCoarsen_branchOperator_accepted]
  apply Finset.sum_eq_zero
  rintro ⟨mu, sigma⟩ hmember
  have hsigma : sigma = 0 := by
    simpa [kt19Accepts] using (Finset.mem_filter.mp hmember).2
  apply kt19ProtocolInstrument_branchOperator_wordInputDensity_eq_zero_of_xSyndrome_ne
  intro hmatch
  exact hsyndrome (hmatch.trans hsigma)
theorem kt19DistillationInstrument_rejected_branchOperator_wordInputDensity_eq_zero_of_xSyndrome_eq_zero
    (R : CubicRowFamily q Logical Stabilizer Site)
    (error : PrimeQuditRegisterLabel q Site)
    (hsyndrome : xSyndrome R error = 0) :
    (kt19DistillationInstrument R).branchOperator .rejected
        (kt19WordInputDensity (Site := Site) error).toOperator = 0 := by
  classical
  rw [kt19DistillationInstrument,
    FiniteInstrument.binaryCoarsen_branchOperator_rejected]
  apply Finset.sum_eq_zero
  rintro ⟨mu, sigma⟩ hmember
  have hsigma : sigma ≠ 0 := by
    simpa [kt19Accepts, Bool.not_eq_true] using (Finset.mem_filter.mp hmember).2
  apply kt19ProtocolInstrument_branchOperator_wordInputDensity_eq_zero_of_xSyndrome_ne
  intro hmatch
  apply hsigma
  exact hmatch.symm.trans hsyndrome
noncomputable def kt19WordSuccessMass
    (R : CubicRowFamily q Logical Stabilizer Site)
    (error : PrimeQuditRegisterLabel q Site) : ℝ :=
  (kt19DistillationInstrument R).bornWeight .accepted
    (kt19WordInputDensity (Site := Site) error)
theorem kt19WordSuccessMass_eq_ite_acceptedWord
    (R : CubicRowFamily q Logical Stabilizer Site)
    (error : PrimeQuditRegisterLabel q Site) :
    kt19WordSuccessMass R error =
      if kt19AcceptedWord R error then 1 else 0 := by
  classical
  unfold kt19AcceptedWord
  by_cases hsyndrome : xSyndrome R error = 0
  · rw [if_pos hsyndrome]
    have hrejectOperator :=
      kt19DistillationInstrument_rejected_branchOperator_wordInputDensity_eq_zero_of_xSyndrome_eq_zero
        R error hsyndrome
    have hreject :
        (kt19DistillationInstrument R).bornWeight .rejected
          (kt19WordInputDensity (Site := Site) error) = 0 := by
      unfold FiniteInstrument.bornWeight
      rw [hrejectOperator]
      simp
    have hsum := (kt19DistillationInstrument R).sum_bornWeight_eq_one
      (kt19DistillationInstrument_complete R)
      (kt19WordInputDensity (Site := Site) error)
    rw [show (Finset.univ : Finset DistillationOutcome) =
        {.accepted, .rejected} by decide] at hsum
    simpa [kt19WordSuccessMass, hreject] using hsum
  · rw [if_neg hsyndrome]
    unfold kt19WordSuccessMass FiniteInstrument.bornWeight
    rw [kt19DistillationInstrument_accepted_branchOperator_wordInputDensity_eq_zero_of_xSyndrome_ne_zero
      R error hsyndrome]
    simp
noncomputable def kt19EndpointFallback :
    DensityOperator (PrimeQuditRegister q Site) :=
  DensityOperator.pureDensity (magicRegisterKet q 0) (by
    rw [InnerProductSpace.norm_sq_eq_re_inner (𝕜 := Complex),
      magicRegisterKet_inner_self]
    norm_num)
noncomputable def kt19RawEndpoint
    (R : CubicRowFamily q Logical Stabilizer Site)
    (mu : ZMod q → ℝ) (hmu_nonneg : ∀ a : ZMod q, 0 ≤ mu a)
    (hmu_sum : ∑ a : ZMod q, mu a = 1)
    (outcome : DistillationOutcome) : Operator (PrimeQuditRegister q Site) :=
  (kt19DistillationInstrument R).branchOperator outcome
    (kt19IIDResource (Site := Site) mu hmu_nonneg hmu_sum).toOperator
noncomputable def kt19EndpointWeight
    (R : CubicRowFamily q Logical Stabilizer Site)
    (mu : ZMod q → ℝ) (hmu_nonneg : ∀ a : ZMod q, 0 ≤ mu a)
    (hmu_sum : ∑ a : ZMod q, mu a = 1)
    (outcome : DistillationOutcome) : ℝ :=
  (kt19DistillationInstrument R).bornWeight outcome
    (kt19IIDResource (Site := Site) mu hmu_nonneg hmu_sum)
noncomputable def kt19EndpointConditional
    (R : CubicRowFamily q Logical Stabilizer Site)
    (mu : ZMod q → ℝ) (hmu_nonneg : ∀ a : ZMod q, 0 ≤ mu a)
    (hmu_sum : ∑ a : ZMod q, mu a = 1)
    (outcome : DistillationOutcome)
    (hpos : 0 < kt19EndpointWeight R mu hmu_nonneg hmu_sum outcome) :
    DensityOperator (PrimeQuditRegister q Site) :=
  (kt19DistillationInstrument R).conditionalDensity outcome
    (kt19IIDResource (Site := Site) mu hmu_nonneg hmu_sum) hpos
noncomputable def kt19EndpointCompletion
    (R : CubicRowFamily q Logical Stabilizer Site)
    (mu : ZMod q → ℝ) (hmu_nonneg : ∀ a : ZMod q, 0 ≤ mu a)
    (hmu_sum : ∑ a : ZMod q, mu a = 1)
    (outcome : DistillationOutcome) : DensityOperator (PrimeQuditRegister q Site) :=
  FiniteInstrument.binaryCoarsenCompletion (kt19ProtocolInstrument R) (kt19Accepts R)
    (kt19IIDResource (Site := Site) mu hmu_nonneg hmu_sum)
    (kt19EndpointFallback (Site := Site)) outcome
noncomputable def kt19SyndromeRun
    (R : CubicRowFamily q Logical Stabilizer Site)
    (mu : ZMod q → ℝ) (hmu_nonneg : ∀ a : ZMod q, 0 ≤ mu a)
    (hmu_sum : ∑ a : ZMod q, mu a = 1) :
    DistillationRun (KT19SingleQudit.{u} q)
      (PrimeQuditRegister q Site) (PrimeQuditRegister q Site) :=
  FiniteInstrument.binaryDistillationRun (kt19ProtocolInstrument R) (kt19Accepts R)
    (kt19ProtocolInstrument_complete R) (Fintype.card Site)
    (kt19NoisySingleSiteResources (Site := Site) mu hmu_nonneg hmu_sum)
    (kt19PrepareInput (q := q) (Site := Site))
    (kt19EndpointFallback (Site := Site))
noncomputable def kt19Run
    (R : CubicRowFamily q Logical Stabilizer Site)
    (mu : ZMod q → ℝ) (hmu_nonneg : ∀ a : ZMod q, 0 ≤ mu a)
    (hmu_sum : ∑ a : ZMod q, mu a = 1) :
    DistillationRun (KT19SingleQudit.{u} q)
      (PrimeQuditRegister q Site) (PrimeQuditRegister q Logical) :=
  (kt19SyndromeRun R mu hmu_nonneg hmu_sum).postprocess (kt19DecoderChannel R)
@[simp] theorem kt19Run_resourceCount
    (R : CubicRowFamily q Logical Stabilizer Site)
    (mu : ZMod q → ℝ) (hmu_nonneg : ∀ a : ZMod q, 0 ≤ mu a)
    (hmu_sum : ∑ a : ZMod q, mu a = 1) :
    (kt19Run R mu hmu_nonneg hmu_sum).resourceCount = Fintype.card Site :=
  rfl
@[simp] theorem kt19Run_successProbability
    (R : CubicRowFamily q Logical Stabilizer Site)
    (mu : ZMod q → ℝ) (hmu_nonneg : ∀ a : ZMod q, 0 ≤ mu a)
    (hmu_sum : ∑ a : ZMod q, mu a = 1) :
    (kt19Run R mu hmu_nonneg hmu_sum).successProbability =
      kt19EndpointWeight R mu hmu_nonneg hmu_sum .accepted := by
  change (kt19DistillationInstrument R).bornWeight .accepted
      (kt19PrepareInput (Site := Site)
        (kt19NoisySingleSiteResources (Site := Site) mu hmu_nonneg hmu_sum)) = _
  rw [kt19PrepareInput_noisySingleSiteResources]
  rfl
@[simp] theorem kt19SyndromeRun_acceptedOutput
    (R : CubicRowFamily q Logical Stabilizer Site)
    (mu : ZMod q → ℝ) (hmu_nonneg : ∀ a : ZMod q, 0 ≤ mu a)
    (hmu_sum : ∑ a : ZMod q, mu a = 1) :
    (kt19SyndromeRun R mu hmu_nonneg hmu_sum).acceptedOutput =
      kt19EndpointCompletion R mu hmu_nonneg hmu_sum .accepted :=
  by
    unfold kt19SyndromeRun
    change FiniteInstrument.binaryCoarsenCompletion
      (kt19ProtocolInstrument R) (kt19Accepts R)
      (kt19PrepareInput (Site := Site)
        (kt19NoisySingleSiteResources (Site := Site) mu hmu_nonneg hmu_sum))
      (kt19EndpointFallback (Site := Site)) .accepted = _
    rw [kt19PrepareInput_noisySingleSiteResources]
    rfl
@[simp] theorem kt19SyndromeRun_rejectedOutput
    (R : CubicRowFamily q Logical Stabilizer Site)
    (mu : ZMod q → ℝ) (hmu_nonneg : ∀ a : ZMod q, 0 ≤ mu a)
    (hmu_sum : ∑ a : ZMod q, mu a = 1) :
    (kt19SyndromeRun R mu hmu_nonneg hmu_sum).rejectedOutput =
      kt19EndpointCompletion R mu hmu_nonneg hmu_sum .rejected :=
  by
    unfold kt19SyndromeRun
    change FiniteInstrument.binaryCoarsenCompletion
      (kt19ProtocolInstrument R) (kt19Accepts R)
      (kt19PrepareInput (Site := Site)
        (kt19NoisySingleSiteResources (Site := Site) mu hmu_nonneg hmu_sum))
      (kt19EndpointFallback (Site := Site)) .rejected = _
    rw [kt19PrepareInput_noisySingleSiteResources]
    rfl
@[simp] theorem kt19Run_acceptedOutput
    (R : CubicRowFamily q Logical Stabilizer Site)
    (mu : ZMod q → ℝ) (hmu_nonneg : ∀ a : ZMod q, 0 ≤ mu a)
    (hmu_sum : ∑ a : ZMod q, mu a = 1) :
    (kt19Run R mu hmu_nonneg hmu_sum).acceptedOutput =
      (kt19DecoderChannel R).mapDensity
        (kt19EndpointCompletion R mu hmu_nonneg hmu_sum .accepted) :=
  by
    change (kt19DecoderChannel R).mapDensity
      (kt19SyndromeRun R mu hmu_nonneg hmu_sum).acceptedOutput = _
    rw [kt19SyndromeRun_acceptedOutput]
@[simp] theorem kt19Run_rejectedOutput
    (R : CubicRowFamily q Logical Stabilizer Site)
    (mu : ZMod q → ℝ) (hmu_nonneg : ∀ a : ZMod q, 0 ≤ mu a)
    (hmu_sum : ∑ a : ZMod q, mu a = 1) :
    (kt19Run R mu hmu_nonneg hmu_sum).rejectedOutput =
      (kt19DecoderChannel R).mapDensity
        (kt19EndpointCompletion R mu hmu_nonneg hmu_sum .rejected) :=
  by
    change (kt19DecoderChannel R).mapDensity
      (kt19SyndromeRun R mu hmu_nonneg hmu_sum).rejectedOutput = _
    rw [kt19SyndromeRun_rejectedOutput]
noncomputable def kt19OutputLabelDistribution
    (rho : DensityOperator (PrimeQuditRegister q Logical))
    (label : PrimeQuditRegisterLabel q Logical) : ℝ :=
  (magicRegisterInstrument q (Site := Logical)).bornWeight label rho
theorem kt19OutputLabelDistribution_nonneg
    (rho : DensityOperator (PrimeQuditRegister q Logical))
    (label : PrimeQuditRegisterLabel q Logical) :
    0 ≤ kt19OutputLabelDistribution rho label :=
  (magicRegisterInstrument q (Site := Logical)).bornWeight_nonneg label rho
noncomputable def kt19OutputPortError
    (rho : DensityOperator (PrimeQuditRegister q Logical))
    (port : Logical) : ℝ :=
  ∑ label : PrimeQuditRegisterLabel q Logical,
    if label port = 0 then 0 else kt19OutputLabelDistribution rho label
theorem kt19OutputPortError_nonneg
    (rho : DensityOperator (PrimeQuditRegister q Logical))
    (port : Logical) :
    0 ≤ kt19OutputPortError rho port := by
  unfold kt19OutputPortError
  apply Finset.sum_nonneg
  intro label _
  by_cases hlabel : label port = 0
  · simp [hlabel]
  · simpa [hlabel] using kt19OutputLabelDistribution_nonneg rho label
noncomputable def kt19OutputWorstPortError [Nonempty Logical]
    (rho : DensityOperator (PrimeQuditRegister q Logical)) : ℝ :=
  (Finset.univ : Finset Logical).sup' Finset.univ_nonempty
    (fun port => kt19OutputPortError rho port)
theorem kt19OutputPortError_le_worst [Nonempty Logical]
    (rho : DensityOperator (PrimeQuditRegister q Logical))
    (port : Logical) :
    kt19OutputPortError rho port ≤ kt19OutputWorstPortError rho := by
  unfold kt19OutputWorstPortError
  exact Finset.le_sup' _ (Finset.mem_univ port)
theorem kt19OutputWorstPortError_nonneg [Nonempty Logical]
    (rho : DensityOperator (PrimeQuditRegister q Logical)) :
    0 ≤ kt19OutputWorstPortError rho := by
  let port : Logical := Classical.choice (inferInstance : Nonempty Logical)
  exact (kt19OutputPortError_nonneg rho port).trans
    (kt19OutputPortError_le_worst rho port)
noncomputable def kt19AcceptedOutputDistribution
    (R : CubicRowFamily q Logical Stabilizer Site)
    (mu : ZMod q → ℝ) (hmu_nonneg : ∀ a : ZMod q, 0 ≤ mu a)
    (hmu_sum : ∑ a : ZMod q, mu a = 1)
    (hpos : 0 < kt19EndpointWeight R mu hmu_nonneg hmu_sum .accepted)
    (label : PrimeQuditRegisterLabel q Logical) : ℝ :=
  kt19OutputLabelDistribution
    ((kt19DecoderChannel R).mapDensity
      (kt19EndpointConditional R mu hmu_nonneg hmu_sum .accepted hpos)) label
noncomputable def kt19PortError
    (R : CubicRowFamily q Logical Stabilizer Site)
    (mu : ZMod q → ℝ) (hmu_nonneg : ∀ a : ZMod q, 0 ≤ mu a)
    (hmu_sum : ∑ a : ZMod q, mu a = 1)
    (hpos : 0 < kt19EndpointWeight R mu hmu_nonneg hmu_sum .accepted)
    (port : Logical) : ℝ :=
  ∑ label : PrimeQuditRegisterLabel q Logical,
    if label port = 0 then 0 else
      kt19AcceptedOutputDistribution R mu hmu_nonneg hmu_sum hpos label
noncomputable def kt19WorstPortError [Nonempty Logical]
    (R : CubicRowFamily q Logical Stabilizer Site)
    (mu : ZMod q → ℝ) (hmu_nonneg : ∀ a : ZMod q, 0 ≤ mu a)
    (hmu_sum : ∑ a : ZMod q, mu a = 1)
    (hpos : 0 < kt19EndpointWeight R mu hmu_nonneg hmu_sum .accepted) : ℝ :=
  (Finset.univ : Finset Logical).sup' Finset.univ_nonempty
    (fun port => kt19PortError R mu hmu_nonneg hmu_sum hpos port)
def kt19ErrorRate (mu : ZMod q → ℝ) : ℝ :=
  1 - mu 0
theorem kt19Mu_zero_le_one
    (mu : ZMod q → ℝ) (hmu_nonneg : ∀ a : ZMod q, 0 ≤ mu a)
    (hmu_sum : ∑ a : ZMod q, mu a = 1) :
    mu 0 ≤ 1 := by
  have hle : mu 0 ≤ ∑ a : ZMod q, mu a :=
    Finset.single_le_sum (s := Finset.univ) (f := mu)
      (fun a _ => hmu_nonneg a) (Finset.mem_univ 0)
  simpa [hmu_sum] using hle
theorem kt19ErrorRate_nonneg
    (mu : ZMod q → ℝ) (hmu_nonneg : ∀ a : ZMod q, 0 ≤ mu a)
    (hmu_sum : ∑ a : ZMod q, mu a = 1) :
    0 ≤ kt19ErrorRate mu :=
  sub_nonneg.mpr (kt19Mu_zero_le_one mu hmu_nonneg hmu_sum)
theorem kt19ErrorRate_le_one
    (mu : ZMod q → ℝ) (hmu_nonneg : ∀ a : ZMod q, 0 ≤ mu a) :
    kt19ErrorRate mu ≤ 1 := by
  unfold kt19ErrorRate
  linarith [hmu_nonneg 0]
def kt19IIDInputErrorModel
    (mu : ZMod q → ℝ) (hmu_nonneg : ∀ a : ZMod q, 0 ≤ mu a)
    (hmu_sum : ∑ a : ZMod q, mu a = 1) :
    InputErrorModel (Fintype.card Site) (KT19SingleQudit.{u} q) :=
  .independent
    { rate := fun _ => kt19ErrorRate mu
      rate_nonneg := fun _ => kt19ErrorRate_nonneg mu hmu_nonneg hmu_sum
      rate_le_one := fun _ => kt19ErrorRate_le_one mu hmu_nonneg
      admissible := fun rates inputs =>
        (∀ index, rates index = kt19ErrorRate mu) ∧
          ∀ index, inputs index = kt19SingleSiteResource mu hmu_nonneg hmu_sum }
theorem kt19IIDInputErrorModel_permits
    (mu : ZMod q → ℝ) (hmu_nonneg : ∀ a : ZMod q, 0 ≤ mu a)
    (hmu_sum : ∑ a : ZMod q, mu a = 1) :
    (kt19IIDInputErrorModel (Site := Site) mu hmu_nonneg hmu_sum).Permits
      (kt19NoisySingleSiteResources (Site := Site) mu hmu_nonneg hmu_sum) := by
  change (∀ index, kt19ErrorRate mu = kt19ErrorRate mu) ∧
    ∀ index, kt19SingleSiteResource mu hmu_nonneg hmu_sum =
      kt19SingleSiteResource mu hmu_nonneg hmu_sum
  exact ⟨fun _ => rfl, fun _ => rfl⟩
noncomputable def kt19IdealOutput :
    DensityOperator (PrimeQuditRegister q Logical) :=
  DensityOperator.pureDensity (magicRegisterKet q 0) (by
    rw [InnerProductSpace.norm_sq_eq_re_inner (𝕜 := Complex),
      magicRegisterKet_inner_self]
    norm_num)
noncomputable def kt19MagicStateDistillationProtocol [Nonempty Logical]
    (R : CubicRowFamily q Logical Stabilizer Site)
    (mu : ZMod q → ℝ) (hmu_nonneg : ∀ a : ZMod q, 0 ≤ mu a)
    (hmu_sum : ∑ a : ZMod q, mu a = 1) :
    MagicStateDistillationProtocol
      (KT19SingleQudit.{u} q)
      (PrimeQuditRegister q Site)
      (PrimeQuditRegister q Logical) where
  run := kt19Run R mu hmu_nonneg hmu_sum
  inputErrorModel := kt19IIDInputErrorModel (Site := Site) mu hmu_nonneg hmu_sum
  inputPermitted := by
    change (kt19IIDInputErrorModel (Site := Site) mu hmu_nonneg hmu_sum).Permits
      (kt19NoisySingleSiteResources (Site := Site) mu hmu_nonneg hmu_sum)
    exact kt19IIDInputErrorModel_permits (Site := Site) mu hmu_nonneg hmu_sum
  behavior := .postselected
  idealOutput := kt19IdealOutput (q := q) (Logical := Logical)
  outputError := fun rho _ => kt19OutputWorstPortError rho
  outputError_nonneg := fun rho _ => kt19OutputWorstPortError_nonneg rho
noncomputable def kt19OverheadFamily [Nonempty Logical]
    (R : CubicRowFamily q Logical Stabilizer Site)
    (mu : ZMod q → ℝ) (hmu_nonneg : ∀ a : ZMod q, 0 ≤ mu a)
    (hmu_sum : ∑ a : ZMod q, mu a = 1) :
    DistillationProtocolFamily (KT19SingleQudit.{u} q)
      (PrimeQuditRegister q Site) (PrimeQuditRegister q Logical) PUnit where
  targetError := fun _ =>
    kt19OutputWorstPortError
      (kt19Run R mu hmu_nonneg hmu_sum).acceptedOutput
  protocol := fun _ =>
    kt19MagicStateDistillationProtocol R mu hmu_nonneg hmu_sum
  outputResourceCount := fun _ => Fintype.card Logical
  outputResourceCount_pos := fun _ => Fintype.card_pos
  successfulOutputError_le_targetError := fun _ => le_rfl
noncomputable def kt19Success
    (R : CubicRowFamily q Logical Stabilizer Site)
    (mu : ZMod q → ℝ) (hmu_nonneg : ∀ a : ZMod q, 0 ≤ mu a)
    (hmu_sum : ∑ a : ZMod q, mu a = 1) : ℝ :=
  kt19EndpointWeight R mu hmu_nonneg hmu_sum .accepted
noncomputable def kt19SuccessfulOutputCost [Nonempty Logical]
    (R : CubicRowFamily q Logical Stabilizer Site)
    (mu : ZMod q → ℝ) (hmu_nonneg : ∀ a : ZMod q, 0 ≤ mu a)
    (hmu_sum : ∑ a : ZMod q, mu a = 1) : ℝ :=
  (kt19OverheadFamily R mu hmu_nonneg hmu_sum).successfulOutputCost PUnit.unit
structure KT19DistillationFamily (p l k : Nat) [NeZero p] [Fact p.Prime] where
  primeAtLeastFive : PrimeAtLeastFive p
  admissible : Admissible p l k
  rowFamily : CubicRowFamily p (Fin k) (Fin (l - k))
    (KeptPunctureLocation p k)
  stabilizerCarrier_eq_shortened :
    stabilizerCarrier rowFamily = (shortenedReedSolomonCode p l k).carrier
namespace KT19DistillationFamily
variable {p l k : Nat} [NeZero p] [Fact p.Prime]
noncomputable def inputResource (family : KT19DistillationFamily p l k)
    (mu : ZMod p → ℝ) (hmu_nonneg : ∀ a : ZMod p, 0 ≤ mu a)
    (hmu_sum : ∑ a : ZMod p, mu a = 1) :
    DensityOperator (KT19SingleQudit.{0} p) :=
  kt19SingleSiteResource mu hmu_nonneg hmu_sum
noncomputable def preparedInput (family : KT19DistillationFamily p l k)
    (mu : ZMod p → ℝ) (hmu_nonneg : ∀ a : ZMod p, 0 ≤ mu a)
    (hmu_sum : ∑ a : ZMod p, mu a = 1) :
    DensityOperator (PrimeQuditRegister p (KeptPunctureLocation p k)) :=
  kt19PrepareInput (Site := KeptPunctureLocation p k)
    (kt19NoisySingleSiteResources (Site := KeptPunctureLocation p k)
      mu hmu_nonneg hmu_sum :
        ResourceInput (Fintype.card (KeptPunctureLocation p k))
          (KT19SingleQudit.{0} p))
noncomputable def physicalGate (family : KT19DistillationFamily p l k) :
    UnitaryTransport (PrimeQuditRegister p (KeptPunctureLocation p k))
      (PrimeQuditRegister p (KeptPunctureLocation p k)) :=
  family.rowFamily.physicalU13
noncomputable def encodedCode (family : KT19DistillationFamily p l k) :=
  family.rowFamily.encodedCode
noncomputable def protocolInstrument (family : KT19DistillationFamily p l k) :=
  kt19ProtocolInstrument family.rowFamily
noncomputable def distillationInstrument
    (family : KT19DistillationFamily p l k) :=
  kt19DistillationInstrument family.rowFamily
noncomputable def decoder (family : KT19DistillationFamily p l k) :=
  kt19DecoderChannel family.rowFamily
noncomputable def run (family : KT19DistillationFamily p l k)
    (mu : ZMod p → ℝ) (hmu_nonneg : ∀ a : ZMod p, 0 ≤ mu a)
    (hmu_sum : ∑ a : ZMod p, mu a = 1) :=
  kt19Run family.rowFamily mu hmu_nonneg hmu_sum
theorem outputPort_nonempty (family : KT19DistillationFamily p l k) :
    Nonempty (Fin k) := by
  rcases family.admissible with ⟨_, hk, _, _, _⟩
  exact ⟨⟨0, by omega⟩⟩
noncomputable def protocol (family : KT19DistillationFamily p l k)
    (mu : ZMod p → ℝ) (hmu_nonneg : ∀ a : ZMod p, 0 ≤ mu a)
    (hmu_sum : ∑ a : ZMod p, mu a = 1) :
    MagicStateDistillationProtocol
      (KT19SingleQudit.{0} p)
      (PrimeQuditRegister p (KeptPunctureLocation p k))
      (PrimeQuditRegister p (Fin k)) := by
  letI : Nonempty (Fin k) := outputPort_nonempty family
  exact kt19MagicStateDistillationProtocol family.rowFamily mu hmu_nonneg hmu_sum
noncomputable def overheadFamily (family : KT19DistillationFamily p l k)
    (mu : ZMod p → ℝ) (hmu_nonneg : ∀ a : ZMod p, 0 ≤ mu a)
    (hmu_sum : ∑ a : ZMod p, mu a = 1) :
    DistillationProtocolFamily (KT19SingleQudit.{0} p)
      (PrimeQuditRegister p (KeptPunctureLocation p k))
      (PrimeQuditRegister p (Fin k)) PUnit := by
  letI : Nonempty (Fin k) := outputPort_nonempty family
  exact kt19OverheadFamily family.rowFamily mu hmu_nonneg hmu_sum
def kt19Routing (family : KT19DistillationFamily p l k)
    (error : Word (ZMod p) (KeptPunctureLocation p k)) :
    PrimeQuditRegisterLabel p (Fin k) :=
  kt19LogicalRouting family.rowFamily error
noncomputable def successfulOutputCost
    (family : KT19DistillationFamily p l k)
    (mu : ZMod p → ℝ) (hmu_nonneg : ∀ a : ZMod p, 0 ≤ mu a)
    (hmu_sum : ∑ a : ZMod p, mu a = 1) : ℝ := by
  exact (overheadFamily family mu hmu_nonneg hmu_sum).successfulOutputCost PUnit.unit
noncomputable def outputWorstPortError
    (family : KT19DistillationFamily p l k)
    (mu : ZMod p → ℝ) (hmu_nonneg : ∀ a : ZMod p, 0 ≤ mu a)
    (hmu_sum : ∑ a : ZMod p, mu a = 1) : ℝ := by
  letI : Nonempty (Fin k) := outputPort_nonempty family
  exact kt19OutputWorstPortError
    ((kt19Run family.rowFamily mu hmu_nonneg hmu_sum).acceptedOutput)
noncomputable def acceptedResidualMass
    (family : KT19DistillationFamily p l k)
    (mu : ZMod p → ℝ) : ℝ :=
  ∑ error : Word (ZMod p) (KeptPunctureLocation p k),
    if kt19AcceptedWord family.rowFamily error ∧ error ≠ 0 then
      wordProbability p mu error
    else 0
noncomputable def acceptedResidualError
    (family : KT19DistillationFamily p l k)
    (mu : ZMod p → ℝ) (hmu_nonneg : ∀ a : ZMod p, 0 ≤ mu a)
    (hmu_sum : ∑ a : ZMod p, mu a = 1) : ℝ :=
  acceptedResidualMass family mu /
    kt19Success family.rowFamily mu hmu_nonneg hmu_sum
end KT19DistillationFamily
local instance p11Prime : Fact (Nat.Prime 11) := ⟨by norm_num⟩
local instance p11NeZero : NeZero 11 := ⟨by norm_num⟩
attribute [local instance] QEC.Distillation.KT19Protocol.p11Prime QEC.Distillation.KT19Protocol.p11NeZero
noncomputable def p11DistillationFamily : KT19DistillationFamily 11 4 2 where
  primeAtLeastFive := by
    constructor <;> norm_num
  admissible := by
    norm_num [Admissible]
  rowFamily := p11CubicRowFamily
  stabilizerCarrier_eq_shortened := by
    change p11StabilizerCarrier = (shortenedReedSolomonCode 11 4 2).carrier
    exact p11_stabilizerCarrier_eq_shortenedReedSolomon
noncomputable def p11AcceptedResidualMass
    (mu : ZMod 11 → ℝ) : ℝ :=
  ∑ error : Word (ZMod 11) (KeptPunctureLocation 11 2),
    if kt19AcceptedWord p11CubicRowFamily error ∧ error ≠ 0 then
      wordProbability 11 mu error
    else 0
noncomputable def p11AcceptedResidualError
    (mu : ZMod 11 → ℝ) (hmu_nonneg : ∀ a : ZMod 11, 0 ≤ mu a)
    (hmu_sum : ∑ a : ZMod 11, mu a = 1) : ℝ :=
  p11AcceptedResidualMass mu /
    kt19Success p11CubicRowFamily mu hmu_nonneg hmu_sum
noncomputable def kt19AcceptedDecodedBranch
    (R : CubicRowFamily q Logical Stabilizer Site)
    (error : PrimeQuditRegisterLabel q Site) :
    Operator (PrimeQuditRegister q Logical) :=
  if kt19AcceptedWord R error then
    kt19DecoderChannel R
      ((kt19DistillationInstrument R).branchOperator .accepted
        (kt19WordInputDensity (Site := Site) error).toOperator)
  else (kt19IdealOutput (q := q) (Logical := Logical)).toOperator
noncomputable def kt19AcceptedDecodedDensity
    (R : CubicRowFamily q Logical Stabilizer Site)
    (error : PrimeQuditRegisterLabel q Site)
    (haccepted : kt19AcceptedWord R error) :
    DensityOperator (PrimeQuditRegister q Logical) :=
  (kt19DecoderChannel R).mapDensity
    ((kt19DistillationInstrument R).conditionalDensity .accepted
      (kt19WordInputDensity (Site := Site) error) (by
        change 0 < kt19WordSuccessMass R error
        rw [kt19WordSuccessMass_eq_ite_acceptedWord, if_pos haccepted]
        norm_num))
noncomputable def p11AcceptedResidualDecodedDifference
    (mu : ZMod 11 → ℝ) : Operator (PrimeQuditRegister 11 (Fin 2)) :=
  ∑ error : Word (ZMod 11) (KeptPunctureLocation 11 2),
    if kt19AcceptedWord p11CubicRowFamily error ∧ error ≠ 0 then
      (wordProbability 11 mu error : Complex) •
        (kt19AcceptedDecodedBranch p11CubicRowFamily error -
          (kt19IdealOutput (q := 11) (Logical := Fin 2)).toOperator)
    else 0
namespace KT19DistillationFamily
variable {p l k : Nat} [NeZero p] [Fact p.Prime]
noncomputable def acceptedResidualDecodedDifference
    (family : KT19DistillationFamily p l k)
    (mu : ZMod p → ℝ) : Operator (PrimeQuditRegister p (Fin k)) :=
  ∑ error : Word (ZMod p) (KeptPunctureLocation p k),
    if kt19AcceptedWord family.rowFamily error ∧ error ≠ 0 then
      (wordProbability p mu error : Complex) •
        (kt19AcceptedDecodedBranch family.rowFamily error -
          (kt19IdealOutput (q := p) (Logical := Fin k)).toOperator)
    else 0
noncomputable def routedAcceptedMass
    (family : KT19DistillationFamily p l k)
    (mu : ZMod p → ℝ) (label : PrimeQuditRegisterLabel p (Fin k)) : ℝ :=
  ∑ error : Word (ZMod p) (KeptPunctureLocation p k),
    if kt19AcceptedWord family.rowFamily error ∧
        label = kt19Routing family error then
      wordProbability p mu error
    else 0
noncomputable def smallErrorRecurrenceConstant
    (_family : KT19DistillationFamily p l k) : ℝ :=
  4 * (Fintype.card (PrimeQuditRegisterLabel p (Fin k)) : ℝ) *
    (Fintype.card (Word (ZMod p) (KeptPunctureLocation p k)) : ℝ)
end KT19DistillationFamily
end Syndromes
end QEC.Distillation.KT19Protocol


