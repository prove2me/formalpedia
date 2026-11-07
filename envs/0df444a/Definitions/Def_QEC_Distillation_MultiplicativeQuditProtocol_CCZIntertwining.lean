-- Prove2me | Definitions.Def_QEC_Distillation_MultiplicativeQuditProtocol_CCZIntertwining
-- name    : QEC_Distillation_MultiplicativeQuditProtocol_CCZIntertwining
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-06T14:17:09.819431+00:00
-- url     : https://prove2.me/theorems/a0553f78-9f82-4bd7-9699-6a6d42dc4276
-- title:
--   CCZIntertwining
-- statement:
--   Definitions and structural lemmas for CCZIntertwining, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/MultiplicativeQuditProtocol/CCZIntertwining.lean

import Definitions.Def_QEC_Distillation_MultiplicativeQuditProtocol_CSSShortening
import Definitions.Def_QEC_Distillation_MultiplicativeQuditProtocol_PhysicalCCZ
import Theorems.Thm_QEC_Coding_ChainComplexData_pureZLogicalQuotientEquivMiddleHomology_mk
import Theorems.Thm_QEC_Distillation_EncodedCode_ImplementsLogicalGate_symm
import Theorems.Thm_QEC_Distillation_Ngu24MultiplicativeCSS_SourceInput_starSquare_triple_pairing_eq_zero
import Theorems.Thm_QEC_Distillation_Ngu24MultiplicativeCSS_SourceInput_systematicLogicalWord_mem_code
import Theorems.Thm_QEC_Distillation_Ngu24MultiplicativeCSS_SourceInput_systematicLogicalWord_pivot
import Theorems.Thm_QEC_Distillation_Ngu24MultiplicativeCSS_SourceInput_wordPairing_partition
import Theorems.Thm_QEC_Distillation_additiveCharacter_add
import Theorems.Thm_QEC_Distillation_assembleTagged_extractBlock
import Theorems.Thm_QEC_Distillation_extractBlock_assembleTagged
import Theorems.Thm_QEC_Distillation_mem_coordinateSupport
import Theorems.Thm_QEC_Distillation_taggedCczLinearEquiv_apply
import Theorems.Thm_QEC_Distillation_taggedCczLinearEquiv_symm_apply
import Theorems.Thm_QEC_Distillation_taggedCczPhysicalTransport_apply_basis
import Theorems.Thm_QEC_Distillation_taggedCczTransport_apply
import Theorems.Thm_QEC_Semantics_DensityOperator_pureOfNonzero_apply
import Theorems.Thm_QEC_Semantics_DensityOperator_pureOfNonzero_toOperator
import Theorems.Thm_QEC_Semantics_OperatorMatrix_matrixUnit_apply
import Theorems.Thm_QEC_Semantics_QuantumChannel_comp_apply
import Theorems.Thm_QEC_Semantics_QuantumChannel_id_apply
import Theorems.Thm_QEC_Semantics_Qubit_localXSupport_apply
import Theorems.Thm_QEC_Semantics_Qubit_localZSupport_apply
import Theorems.Thm_QEC_Semantics_UnitaryTransport_conjDensity_apply
import Theorems.Thm_QEC_Semantics_UnitaryTransport_conjDensity_toOperator
import Theorems.Thm_QEC_Semantics_partialTraceRightRaw_cptp_toLinearMap
import Theorems.Thm_QEC_Semantics_partialTraceRightRaw_mapDensity_toOperator
attribute [local simp] QEC.Coding.ChainComplexData.pureZLogicalQuotientEquivMiddleHomology_mk
attribute [local simp] QEC.Distillation.assembleTagged_extractBlock
attribute [local simp] QEC.Distillation.extractBlock_assembleTagged
attribute [local simp] QEC.Distillation.mem_coordinateSupport
attribute [local simp] QEC.Distillation.taggedCczLinearEquiv_apply
attribute [local simp] QEC.Distillation.taggedCczLinearEquiv_symm_apply
attribute [local simp] QEC.Distillation.taggedCczTransport_apply
attribute [local simp] QEC.Semantics.DensityOperator.pureOfNonzero_apply
attribute [local simp] QEC.Semantics.DensityOperator.pureOfNonzero_toOperator
attribute [local simp] QEC.Semantics.OperatorMatrix.matrixUnit_apply
attribute [local simp] QEC.Semantics.QuantumChannel.comp_apply
attribute [local simp] QEC.Semantics.QuantumChannel.id_apply
attribute [local simp] QEC.Semantics.Qubit.localXSupport_apply
attribute [local simp] QEC.Semantics.Qubit.localZSupport_apply
attribute [local simp] QEC.Semantics.UnitaryTransport.conjDensity_apply
attribute [local simp] QEC.Semantics.UnitaryTransport.conjDensity_toOperator
attribute [local simp] QEC.Semantics.partialTraceRightRaw_cptp_toLinearMap
attribute [local simp] QEC.Semantics.partialTraceRightRaw_mapDensity_toOperator


set_option autoImplicit false
noncomputable section
namespace QEC.Distillation.Ngu24MultiplicativeCCZ
open Coding Semantics
open scoped BigOperators
open Ngu24MultiplicativeCSS
universe u
variable {F I Logical : Type u} [Field F] [Fintype F] [Algebra (ZMod 2) F]
  [Fintype I] [Fintype Logical]
local instance _p2m_local_instance_df646da45e_25 : DecidableEq Logical := Classical.decEq _
local instance _p2m_local_instance_df646da45e_26 : DecidableEq (Word F Logical) := Classical.decEq _
def wordTriplePairing {J : Type u} [Fintype J]
    (x y z : Word F J) : F :=
  wordPairing (wordStar x y) z
omit [Fintype F] [Algebra (ZMod 2) F] in
@[simp]
theorem wordTriplePairing_apply {J : Type u} [Fintype J]
    (x y z : Word F J) :
    wordTriplePairing x y z = ∑ j : J, x j * y j * z j := by
  rfl
omit [Algebra (ZMod 2) F] in
/-- Partitioning full coordinates into pivots and their complement also
partitions the cubic pairing. -/
theorem wordTriplePairing_partition (data : SourceInput F I Logical)
    (x y z : Word F I) :
    wordTriplePairing x y z =
      wordTriplePairing (data.pivotCoordinates x) (data.pivotCoordinates y)
        (data.pivotCoordinates z) +
      wordTriplePairing (data.puncture x) (data.puncture y) (data.puncture z) := by
  exact data.wordPairing_partition (wordStar x y) z
def fullShortenedCosetWord (data : SourceInput F I Logical) (u : Word F Logical)
    (h : data.H0) : Word F I :=
  data.systematicLogicalWord u + h.1.1
omit [Algebra (ZMod 2) F] in
theorem fullShortenedCosetWord_mem_code (data : SourceInput F I Logical)
    (u : Word F Logical) (h : data.H0) :
    fullShortenedCosetWord data u h ∈ data.code.carrier :=
  data.code.carrier.add_mem (data.systematicLogicalWord_mem_code u) h.1.2
omit [Algebra (ZMod 2) F] in
theorem pivotCoordinates_fullShortenedCosetWord (data : SourceInput F I Logical)
    (u : Word F Logical) (h : data.H0) :
    data.pivotCoordinates (fullShortenedCosetWord data u h) = u := by
  ext a
  change data.systematicLogicalWord u (data.pivotEmbedding a) +
      h.1.1 (data.pivotEmbedding a) = u a
  rw [data.systematicLogicalWord_pivot, data.shortenedKernel_pivot_zero]
  simp
omit [Algebra (ZMod 2) F] in
theorem puncture_fullShortenedCosetWord (data : SourceInput F I Logical)
    (u : Word F Logical) (h : data.H0) :
    data.puncture (fullShortenedCosetWord data u h) = data.shortenedCosetLabel u h := by
  rfl
omit [Algebra (ZMod 2) F] in
/-- The multiplication-code hypothesis annihilates every full cubic pairing
of the three actual coset words. -/
theorem fullShortenedCosetWord_triple_pairing_eq_zero (data : SourceInput F I Logical)
    (u v w : Word F Logical) (h₁ h₂ h₃ : data.H0) :
    wordTriplePairing (fullShortenedCosetWord data u h₁)
      (fullShortenedCosetWord data v h₂) (fullShortenedCosetWord data w h₃) = 0 :=
  data.starSquare_triple_pairing_eq_zero
    (fullShortenedCosetWord_mem_code data u h₁)
    (fullShortenedCosetWord_mem_code data v h₂)
    (fullShortenedCosetWord_mem_code data w h₃)
omit [Algebra (ZMod 2) F] in
/-- Before imposing characteristic two, puncturing contributes the negative
logical cubic pairing. -/
theorem puncturedTriplePairing_eq_neg_logical (data : SourceInput F I Logical)
    (u v w : Word F Logical) (h₁ h₂ h₃ : data.H0) :
    wordTriplePairing (data.shortenedCosetLabel u h₁)
      (data.shortenedCosetLabel v h₂) (data.shortenedCosetLabel w h₃) =
        -wordTriplePairing u v w := by
  have hpartition := wordTriplePairing_partition data
    (fullShortenedCosetWord data u h₁) (fullShortenedCosetWord data v h₂)
      (fullShortenedCosetWord data w h₃)
  rw [fullShortenedCosetWord_triple_pairing_eq_zero data u v w h₁ h₂ h₃,
    pivotCoordinates_fullShortenedCosetWord,
    pivotCoordinates_fullShortenedCosetWord,
    pivotCoordinates_fullShortenedCosetWord,
    puncture_fullShortenedCosetWord,
    puncture_fullShortenedCosetWord,
    puncture_fullShortenedCosetWord] at hpartition
  exact eq_neg_of_add_eq_zero_right hpartition.symm
omit [Fintype F] [Algebra (ZMod 2) F] in
theorem neg_eq_self_of_char_two [CharP F 2] (x : F) : -x = x := by
  apply (eq_neg_of_add_eq_zero_left ?_).symm
  have htwo : (2 : F) = 0 := CharP.cast_eq_zero F 2
  rw [← two_mul, htwo, zero_mul]
omit [Algebra (ZMod 2) F] in
/-- In characteristic two the actual punctured coset labels obey Ngu24's
positive cubic identity. -/
theorem puncturedTriplePairing_eq_logical_of_char_two (data : SourceInput F I Logical)
    [CharP F 2] (u v w : Word F Logical) (h₁ h₂ h₃ : data.H0) :
    wordTriplePairing (data.shortenedCosetLabel u h₁)
      (data.shortenedCosetLabel v h₂) (data.shortenedCosetLabel w h₃) =
        wordTriplePairing u v w := by
  rw [puncturedTriplePairing_eq_neg_logical data]
  exact neg_eq_self_of_char_two _
def taggedShortenedCosetLabel (data : SourceInput F I Logical)
    (label : TaggedThreeCopyRegisterLabel F Logical)
    (h : ThreeCopyTag → data.H0) :
    TaggedThreeCopyRegisterLabel F data.PivotComplement :=
  assembleTagged fun tag =>
    data.shortenedCosetLabel (extractBlock label tag) (h tag)
omit [Algebra (ZMod 2) F] in
theorem taggedShortenedCosetLabel_eq_implies_logical_eq (data : SourceInput F I Logical)
    (label label' : TaggedThreeCopyRegisterLabel F Logical)
    (h k : ThreeCopyTag → data.H0)
    (hEq : taggedShortenedCosetLabel data label h = taggedShortenedCosetLabel data label' k) :
    label = label' := by
  have hblock (tag : ThreeCopyTag) : extractBlock label tag = extractBlock label' tag := by
    have htag := congrArg (fun target => extractBlock target tag) hEq
    simpa [taggedShortenedCosetLabel] using
      data.shortenedCosetLabel_eq_implies_logical_eq
        (extractBlock label tag) (extractBlock label' tag) (h tag) (k tag) htag
  funext coordinate
  rcases coordinate with ⟨tag, site⟩
  exact congrFun (hblock tag) site
omit [Algebra (ZMod 2) F] in
/-- For one tagged logical label, the three shortened-kernel choices have
different tagged physical labels. -/
theorem taggedShortenedCosetLabel_injective (data : SourceInput F I Logical)
    (label : TaggedThreeCopyRegisterLabel F Logical) :
    Function.Injective (taggedShortenedCosetLabel data label) := by
  intro h k hEq
  funext tag
  apply data.shortenedCosetLabel_injective (extractBlock label tag)
  have htag := congrArg (fun target => extractBlock target tag) hEq
  simpa [taggedShortenedCosetLabel] using htag
def taggedCosetNormalization (data : SourceInput F I Logical) : Complex :=
  (SourceInput.cosetNormalization data.H0) ^ 3
omit [Algebra (ZMod 2) F] in
theorem taggedH0_card (data : SourceInput F I Logical) :
    Nat.card (ThreeCopyTag → data.H0) = (Nat.card data.H0) ^ 3 := by
  rw [Nat.card_pi]
  simp only [Nat.card_eq_fintype_card, Finset.prod_const, Finset.card_univ]
  have htags : Fintype.card ThreeCopyTag = 3 := by decide
  rw [htags]
omit [Algebra (ZMod 2) F] in
theorem taggedCosetNormalization_conj_mul_card (data : SourceInput F I Logical) :
    starRingEnd Complex (taggedCosetNormalization data) * taggedCosetNormalization data *
        (Nat.card (ThreeCopyTag → data.H0) : Complex) = 1 := by
  rw [taggedCosetNormalization, map_pow]
  have hcard : (Nat.card (ThreeCopyTag → data.H0) : Complex) =
      (Nat.card data.H0 : Complex) ^ 3 := by
    norm_cast
    exact taggedH0_card data
  rw [hcard]
  calc
    (starRingEnd Complex (SourceInput.cosetNormalization data.H0)) ^ 3 *
        SourceInput.cosetNormalization data.H0 ^ 3 * (Nat.card data.H0 : Complex) ^ 3 =
        (starRingEnd Complex (SourceInput.cosetNormalization data.H0) *
          SourceInput.cosetNormalization data.H0 * (Nat.card data.H0 : Complex)) ^ 3 := by ring
    _ = 1 := by rw [data.cosetNormalization_conj_mul_card]; simp
def taggedShortenedCosetKet (data : SourceInput F I Logical)
    (label : TaggedThreeCopyRegisterLabel F Logical) :
    TaggedThreeCopyRegister F data.PivotComplement :=
  taggedCosetNormalization data •
    ∑ h : ThreeCopyTag → data.H0,
      registerBasisKet (taggedShortenedCosetLabel data label h)
omit [Algebra (ZMod 2) F] in
theorem taggedUniformCosetSum_inner (data : SourceInput F I Logical)
    (label label' : TaggedThreeCopyRegisterLabel F Logical) :
    inner Complex
        (∑ h : ThreeCopyTag → data.H0,
          registerBasisKet (taggedShortenedCosetLabel data label h))
        (∑ k : ThreeCopyTag → data.H0,
          registerBasisKet (taggedShortenedCosetLabel data label' k)) =
      if label = label' then (Nat.card (ThreeCopyTag → data.H0) : Complex) else 0 := by
  classical
  rw [inner_sum]
  simp_rw [sum_inner]
  by_cases hlabels : label = label'
  · subst label'
    have hinner (h k : ThreeCopyTag → data.H0) :
        inner Complex (registerBasisKet (taggedShortenedCosetLabel data label h))
          (registerBasisKet (taggedShortenedCosetLabel data label k)) =
            if h = k then 1 else 0 := by
      simp only [registerBasisKet, EuclideanSpace.basisFun_apply]
      rw [EuclideanSpace.inner_single_left]
      simp [PiLp.single_apply, (taggedShortenedCosetLabel_injective data label).eq_iff]
    simp_rw [hinner]
    simp [Nat.card_eq_fintype_card]
  · rw [if_neg hlabels]
    apply Finset.sum_eq_zero
    intro h _
    apply Finset.sum_eq_zero
    intro k _
    have hdistinct : taggedShortenedCosetLabel data label k ≠
        taggedShortenedCosetLabel data label' h := fun hEq =>
      hlabels (taggedShortenedCosetLabel_eq_implies_logical_eq data label label' k h hEq)
    simp only [registerBasisKet, EuclideanSpace.basisFun_apply]
    rw [EuclideanSpace.inner_single_left]
    simp [hdistinct]
omit [Algebra (ZMod 2) F] in
/-- The three-tag uniform coset states are orthonormal. -/
theorem taggedShortenedCosetKet_inner (data : SourceInput F I Logical)
    (label label' : TaggedThreeCopyRegisterLabel F Logical) :
    inner Complex (taggedShortenedCosetKet data label)
      (taggedShortenedCosetKet data label') = if label = label' then 1 else 0 := by
  unfold taggedShortenedCosetKet
  rw [inner_smul_left, inner_smul_right, taggedUniformCosetSum_inner]
  by_cases hlabels : label = label'
  · subst label'
    simp only [ite_true]
    rw [← mul_assoc]
    exact taggedCosetNormalization_conj_mul_card data
  · simp [hlabels]
omit [Algebra (ZMod 2) F] in
/-- The tagged normalized coset family is orthonormal in the three-block
physical register. -/
theorem taggedShortenedCosetKet_orthonormal (data : SourceInput F I Logical) :
    Orthonormal Complex (taggedShortenedCosetKet data) := by
  rw [orthonormal_iff_ite]
  intro label label'
  exact taggedShortenedCosetKet_inner data label label'
noncomputable def taggedEncodingLinearMap (data : SourceInput F I Logical) :
    TaggedThreeCopyRegister F Logical →ₗ[Complex]
      TaggedThreeCopyRegister F data.PivotComplement where
  toFun psi := ∑ label : TaggedThreeCopyRegisterLabel F Logical,
    psi label • taggedShortenedCosetKet data label
  map_add' psi chi := by
    simp only [WithLp.ofLp_add, Pi.add_apply, add_smul, Finset.sum_add_distrib]
  map_smul' scalar psi := by
    simp only [WithLp.ofLp_smul, Pi.smul_apply, smul_eq_mul, Finset.smul_sum]
    apply Finset.sum_congr rfl
    intro label _
    simp only [RingHom.id_apply]
    rw [smul_smul, mul_comm]
omit [Algebra (ZMod 2) F] in
theorem taggedEncodingLinearMap_map_inner (data : SourceInput F I Logical)
    (psi chi : TaggedThreeCopyRegister F Logical) :
    inner Complex (taggedEncodingLinearMap data psi) (taggedEncodingLinearMap data chi) =
      inner Complex psi chi := by
  change inner Complex
      (∑ label : TaggedThreeCopyRegisterLabel F Logical,
        psi label • taggedShortenedCosetKet data label)
      (∑ label : TaggedThreeCopyRegisterLabel F Logical,
        chi label • taggedShortenedCosetKet data label) =
      inner Complex psi chi
  rw [(taggedShortenedCosetKet_orthonormal data).inner_sum psi chi Finset.univ]
  simp [PiLp.inner_apply, mul_comm]
noncomputable def taggedEncodingIsometry (data : SourceInput F I Logical) :
    TaggedThreeCopyRegister F Logical →ₗᵢ[Complex]
      TaggedThreeCopyRegister F data.PivotComplement :=
  (taggedEncodingLinearMap data).isometryOfInner (taggedEncodingLinearMap_map_inner data)
noncomputable def taggedEncodedCarrier (data : SourceInput F I Logical) :
    Submodule Complex (TaggedThreeCopyRegister F data.PivotComplement) :=
  (taggedEncodingIsometry data).toLinearMap.range
noncomputable def taggedQuantumCode (data : SourceInput F I Logical) :
    QuantumCode (TaggedThreeCopyRegister F data.PivotComplement) where
  carrier := taggedEncodedCarrier data
noncomputable def taggedEncodedCode (data : SourceInput F I Logical) :
    EncodedCode (TaggedThreeCopyRegister F Logical)
      (TaggedThreeCopyRegister F data.PivotComplement) where
  code := taggedQuantumCode data
  encoding := LinearIsometry.equivRange (taggedEncodingIsometry data)
omit [Algebra (ZMod 2) F] in
theorem taggedEncodingLinearMap_apply_logical_basis (data : SourceInput F I Logical)
    (label : TaggedThreeCopyRegisterLabel F Logical) :
    taggedEncodingLinearMap data (registerBasisKet label) = taggedShortenedCosetKet data label := by
  change (∑ label' : TaggedThreeCopyRegisterLabel F Logical,
      registerBasisKet label label' • taggedShortenedCosetKet data label') =
        taggedShortenedCosetKet data label
  simp [registerBasisKet, EuclideanSpace.basisFun_apply]
omit [Algebra (ZMod 2) F] in
theorem taggedEncodedCode_apply_logical_basis (data : SourceInput F I Logical)
    (label : TaggedThreeCopyRegisterLabel F Logical) :
    (taggedEncodedCode data).encode (registerBasisKet label) =
      taggedShortenedCosetKet data label :=
  taggedEncodingLinearMap_apply_logical_basis data label
def taggedLogicalCczExponent (label : TaggedThreeCopyRegisterLabel F Logical) : F :=
  wordTriplePairing (extractBlock label ThreeCopyTag.first)
    (extractBlock label ThreeCopyTag.second) (extractBlock label ThreeCopyTag.third)
def taggedLogicalCczAmplitude (label : TaggedThreeCopyRegisterLabel F Logical) : Complex :=
  additiveCharacter (taggedLogicalCczExponent label)
omit [Fintype F] in
theorem taggedLogicalCczAmplitude_square (label : TaggedThreeCopyRegisterLabel F Logical) :
    taggedLogicalCczAmplitude label * taggedLogicalCczAmplitude label = 1 :=
  additiveCharacter_square _
omit [Fintype F] in
theorem taggedLogicalCczAmplitude_mul_conj (label : TaggedThreeCopyRegisterLabel F Logical) :
    taggedLogicalCczAmplitude label *
        starRingEnd Complex (taggedLogicalCczAmplitude label) = 1 := by
  rw [taggedLogicalCczAmplitude, additiveCharacter_conj]
  exact additiveCharacter_square _
def taggedLogicalCczDiagonalOperator :
    Operator (TaggedThreeCopyRegister F Logical) where
  toFun psi := WithLp.toLp 2 fun label => taggedLogicalCczAmplitude label * psi label
  map_add' := by
    intro psi chi
    ext label
    change taggedLogicalCczAmplitude label * (psi label + chi label) =
      taggedLogicalCczAmplitude label * psi label + taggedLogicalCczAmplitude label * chi label
    ring
  map_smul' := by
    intro scalar psi
    ext label
    change taggedLogicalCczAmplitude label * (scalar * psi label) =
      scalar * (taggedLogicalCczAmplitude label * psi label)
    ring
@[simp]
theorem taggedLogicalCczDiagonalOperator_apply (psi : TaggedThreeCopyRegister F Logical)
    (label : TaggedThreeCopyRegisterLabel F Logical) :
    taggedLogicalCczDiagonalOperator psi label = taggedLogicalCczAmplitude label * psi label :=
  rfl
theorem taggedLogicalCczDiagonalOperator_square :
    taggedLogicalCczDiagonalOperator (F := F) * taggedLogicalCczDiagonalOperator =
      (1 : Operator (TaggedThreeCopyRegister F Logical)) := by
  ext psi label
  simp only [Module.End.mul_apply, taggedLogicalCczDiagonalOperator_apply]
  rw [← mul_assoc, taggedLogicalCczAmplitude_square]
  simp
theorem taggedLogicalCczDiagonalOperator_map_inner
    (psi chi : TaggedThreeCopyRegister F Logical) :
    inner Complex (taggedLogicalCczDiagonalOperator psi) (taggedLogicalCczDiagonalOperator chi) =
      inner Complex psi chi := by
  rw [PiLp.inner_apply, PiLp.inner_apply]
  apply Finset.sum_congr rfl
  intro label _
  simp only [taggedLogicalCczDiagonalOperator_apply, RCLike.inner_apply, map_mul]
  calc
    (taggedLogicalCczAmplitude label * chi label) *
        (starRingEnd Complex (taggedLogicalCczAmplitude label) * starRingEnd Complex (psi label)) =
        (taggedLogicalCczAmplitude label * starRingEnd Complex (taggedLogicalCczAmplitude label)) *
          (chi label * starRingEnd Complex (psi label)) := by ring
    _ = chi label * starRingEnd Complex (psi label) := by
      rw [taggedLogicalCczAmplitude_mul_conj]
      ring
noncomputable def taggedLogicalCczLinearEquiv :
    TaggedThreeCopyRegister F Logical ≃ₗ[Complex] TaggedThreeCopyRegister F Logical where
  toFun psi := taggedLogicalCczDiagonalOperator psi
  invFun psi := taggedLogicalCczDiagonalOperator psi
  left_inv := by
    intro psi
    have h := LinearMap.congr_fun (taggedLogicalCczDiagonalOperator_square (F := F)) psi
    simpa only [Module.End.mul_apply, Module.End.one_apply] using h
  right_inv := by
    intro psi
    have h := LinearMap.congr_fun (taggedLogicalCczDiagonalOperator_square (F := F)) psi
    simpa only [Module.End.mul_apply, Module.End.one_apply] using h
  map_add' := taggedLogicalCczDiagonalOperator.map_add
  map_smul' := taggedLogicalCczDiagonalOperator.map_smul
noncomputable def taggedLogicalCczTransport :
    UnitaryTransport (TaggedThreeCopyRegister F Logical) (TaggedThreeCopyRegister F Logical) where
  toLinearEquiv := taggedLogicalCczLinearEquiv
  map_inner := taggedLogicalCczDiagonalOperator_map_inner
@[simp]
theorem taggedLogicalCczTransport_apply (psi : TaggedThreeCopyRegister F Logical)
    (label : TaggedThreeCopyRegisterLabel F Logical) :
    taggedLogicalCczTransport psi label = taggedLogicalCczAmplitude label * psi label :=
  rfl
theorem taggedLogicalCczTransport_apply_basis (label : TaggedThreeCopyRegisterLabel F Logical) :
    taggedLogicalCczTransport (registerBasisKet label) =
      taggedLogicalCczAmplitude label • registerBasisKet label := by
  classical
  ext target
  by_cases htarget : target = label
  · subst target
    simp [taggedLogicalCczTransport_apply, registerBasisKet, EuclideanSpace.basisFun_apply]
  · simp [taggedLogicalCczTransport_apply, registerBasisKet, EuclideanSpace.basisFun_apply,
      htarget]
omit [Fintype F] in
theorem additiveCharacter_zero : additiveCharacter (F := F) 0 = 1 := by
  simp [additiveCharacter, fieldTrace]
omit [Fintype F] in
theorem additiveCharacter_finset_sum {J : Type u} [Fintype J]
    (f : J → F) :
    additiveCharacter (∑ j : J, f j) = ∏ j : J, additiveCharacter (f j) := by
  classical
  let sites : Finset J := Finset.univ
  change additiveCharacter (sites.sum f) = sites.prod (fun j => additiveCharacter (f j))
  induction sites using Finset.induction_on with
  | empty => exact additiveCharacter_zero (F := F)
  | insert j s hnotmem ih =>
      rw [Finset.sum_insert hnotmem, Finset.prod_insert hnotmem, additiveCharacter_add, ih]
omit [Algebra (ZMod 2) F] in
/-- The cubic identity applies to all three actual shortened-coset labels at
once, with tags retained throughout. -/
theorem taggedShortenedCosetLabel_cubic_identity (data : SourceInput F I Logical)
    [CharP F 2] (label : TaggedThreeCopyRegisterLabel F Logical)
    (h : ThreeCopyTag → data.H0) :
    wordTriplePairing
      (extractBlock (taggedShortenedCosetLabel data label h) ThreeCopyTag.first)
      (extractBlock (taggedShortenedCosetLabel data label h) ThreeCopyTag.second)
      (extractBlock (taggedShortenedCosetLabel data label h) ThreeCopyTag.third) =
        taggedLogicalCczExponent label := by
  simpa [taggedShortenedCosetLabel, taggedLogicalCczExponent] using
    puncturedTriplePairing_eq_logical_of_char_two data
      (extractBlock label ThreeCopyTag.first) (extractBlock label ThreeCopyTag.second)
      (extractBlock label ThreeCopyTag.third)
      (h ThreeCopyTag.first) (h ThreeCopyTag.second) (h ThreeCopyTag.third)
theorem taggedCczPhysicalPhase_eq_logical (data : SourceInput F I Logical)
    [CharP F 2] (label : TaggedThreeCopyRegisterLabel F Logical)
    (h : ThreeCopyTag → data.H0) :
    (∏ site : data.PivotComplement,
      taggedCczAmplitude site (taggedShortenedCosetLabel data label h)) =
        taggedLogicalCczAmplitude label := by
  calc
    (∏ site : data.PivotComplement,
      taggedCczAmplitude site (taggedShortenedCosetLabel data label h)) =
        ∏ site : data.PivotComplement,
          additiveCharacter
            ((extractBlock (taggedShortenedCosetLabel data label h) ThreeCopyTag.first) site *
              (extractBlock (taggedShortenedCosetLabel data label h) ThreeCopyTag.second) site *
                (extractBlock (taggedShortenedCosetLabel data label h) ThreeCopyTag.third) site) := by
          apply Finset.prod_congr rfl
          intro site _
          rfl
    _ = additiveCharacter
        (wordTriplePairing
          (extractBlock (taggedShortenedCosetLabel data label h) ThreeCopyTag.first)
          (extractBlock (taggedShortenedCosetLabel data label h) ThreeCopyTag.second)
          (extractBlock (taggedShortenedCosetLabel data label h) ThreeCopyTag.third)) := by
            rw [wordTriplePairing_apply, additiveCharacter_finset_sum]
    _ = taggedLogicalCczAmplitude label := by
      rw [taggedShortenedCosetLabel_cubic_identity]
      rfl
theorem taggedCczPhysicalTransport_apply_taggedShortenedCosetKet
    (data : SourceInput F I Logical) [CharP F 2]
    (label : TaggedThreeCopyRegisterLabel F Logical) :
    taggedCczPhysicalTransport (F := F) (ι := data.PivotComplement)
        (taggedShortenedCosetKet data label) =
      taggedLogicalCczAmplitude label • taggedShortenedCosetKet data label := by
  unfold taggedShortenedCosetKet
  calc
    taggedCczPhysicalTransport (F := F) (ι := data.PivotComplement)
        (taggedCosetNormalization data •
          ∑ h : ThreeCopyTag → data.H0,
            registerBasisKet (taggedShortenedCosetLabel data label h)) =
        taggedCosetNormalization data •
          taggedCczPhysicalTransport (F := F) (ι := data.PivotComplement)
            (∑ h : ThreeCopyTag → data.H0,
              registerBasisKet (taggedShortenedCosetLabel data label h)) := by
                rw [map_smul]
    _ = taggedCosetNormalization data •
          ∑ h : ThreeCopyTag → data.H0,
            taggedCczPhysicalTransport (F := F) (ι := data.PivotComplement)
              (registerBasisKet (taggedShortenedCosetLabel data label h)) := by
                rw [map_sum]
    _ = taggedCosetNormalization data •
          ∑ h : ThreeCopyTag → data.H0,
            taggedLogicalCczAmplitude label •
              registerBasisKet (taggedShortenedCosetLabel data label h) := by
                apply congrArg (fun vector => taggedCosetNormalization data • vector)
                apply Finset.sum_congr rfl
                intro h _
                rw [show taggedCczPhysicalTransport (F := F) (ι := data.PivotComplement)
                    (registerBasisKet (taggedShortenedCosetLabel data label h)) =
                    (∏ site : data.PivotComplement,
                      taggedCczAmplitude site (taggedShortenedCosetLabel data label h)) •
                      registerBasisKet (taggedShortenedCosetLabel data label h) by
                    simpa [registerBasisKet] using
                      taggedCczPhysicalTransport_apply_basis (F := F)
                        (ι := data.PivotComplement) (taggedShortenedCosetLabel data label h),
                  taggedCczPhysicalPhase_eq_logical data label h]
    _ = taggedLogicalCczAmplitude label •
          (taggedCosetNormalization data •
            ∑ h : ThreeCopyTag → data.H0,
              registerBasisKet (taggedShortenedCosetLabel data label h)) := by
                simp only [Finset.smul_sum]
                apply Finset.sum_congr rfl
                intro h _
                rw [smul_smul, smul_smul, mul_comm]
theorem taggedCczPhysicalTransport_intertwines_basis
    (data : SourceInput F I Logical) [CharP F 2]
    (label : TaggedThreeCopyRegisterLabel F Logical) :
    taggedCczPhysicalTransport (F := F) (ι := data.PivotComplement)
        ((taggedEncodedCode data).encode (registerBasisKet label)) =
      (taggedEncodedCode data).encode
        (taggedLogicalCczTransport (F := F) (Logical := Logical) (registerBasisKet label)) := by
  rw [taggedEncodedCode_apply_logical_basis,
    taggedCczPhysicalTransport_apply_taggedShortenedCosetKet,
    taggedLogicalCczTransport_apply_basis]
  change taggedLogicalCczAmplitude label • taggedShortenedCosetKet data label =
    ((taggedEncodedCode data).encoding
      (taggedLogicalCczAmplitude label • registerBasisKet label) :
        TaggedThreeCopyRegister F data.PivotComplement)
  simpa [EncodedCode.encode] using congrArg (fun vector =>
    taggedLogicalCczAmplitude label • vector)
      (taggedEncodedCode_apply_logical_basis data label).symm
omit [Field F] [Algebra (ZMod 2) F] in
theorem taggedBasis_expansion (psi : TaggedThreeCopyRegister F Logical) :
    (∑ label : TaggedThreeCopyRegisterLabel F Logical,
      psi label • registerBasisKet label) = psi := by
  classical
  simpa [registerBasisKet] using
    (EuclideanSpace.basisFun (TaggedThreeCopyRegisterLabel F Logical) Complex).sum_repr psi
theorem taggedCczPhysicalTransport_implements_logical
    (data : SourceInput F I Logical) [CharP F 2] :
    (taggedEncodedCode data).ImplementsLogicalGate
      (taggedCczPhysicalTransport (F := F) (ι := data.PivotComplement))
      (taggedLogicalCczTransport (F := F) (Logical := Logical)) := by
  intro psi
  change taggedCczPhysicalTransport (F := F) (ι := data.PivotComplement)
      (taggedEncodingLinearMap data psi) =
    taggedEncodingLinearMap data (taggedLogicalCczTransport (F := F) (Logical := Logical) psi)
  have hencode : taggedEncodingLinearMap data psi =
      ∑ label : TaggedThreeCopyRegisterLabel F Logical,
        psi label • taggedEncodingLinearMap data (registerBasisKet label) := by
    calc
      taggedEncodingLinearMap data psi =
          taggedEncodingLinearMap data (∑ label : TaggedThreeCopyRegisterLabel F Logical,
            psi label • registerBasisKet label) := by rw [taggedBasis_expansion psi]
      _ = ∑ label : TaggedThreeCopyRegisterLabel F Logical,
          taggedEncodingLinearMap data (psi label • registerBasisKet label) := by rw [map_sum]
      _ = ∑ label : TaggedThreeCopyRegisterLabel F Logical,
          psi label • taggedEncodingLinearMap data (registerBasisKet label) := by
            simp_rw [map_smul]
  have hlogical : taggedLogicalCczTransport (F := F) (Logical := Logical) psi =
      ∑ label : TaggedThreeCopyRegisterLabel F Logical,
        psi label • taggedLogicalCczTransport (F := F) (Logical := Logical)
          (registerBasisKet label) := by
    calc
      taggedLogicalCczTransport (F := F) (Logical := Logical) psi =
          taggedLogicalCczTransport (F := F) (Logical := Logical)
            (∑ label : TaggedThreeCopyRegisterLabel F Logical,
              psi label • registerBasisKet label) := by rw [taggedBasis_expansion psi]
      _ = ∑ label : TaggedThreeCopyRegisterLabel F Logical,
          taggedLogicalCczTransport (F := F) (Logical := Logical)
            (psi label • registerBasisKet label) := by rw [map_sum]
      _ = ∑ label : TaggedThreeCopyRegisterLabel F Logical,
          psi label • taggedLogicalCczTransport (F := F) (Logical := Logical)
            (registerBasisKet label) := by
              simp_rw [map_smul]
  calc
    taggedCczPhysicalTransport (F := F) (ι := data.PivotComplement)
        (taggedEncodingLinearMap data psi) =
        taggedCczPhysicalTransport (F := F) (ι := data.PivotComplement)
          (∑ label : TaggedThreeCopyRegisterLabel F Logical,
            psi label • taggedEncodingLinearMap data (registerBasisKet label)) := by rw [hencode]
    _ = ∑ label : TaggedThreeCopyRegisterLabel F Logical,
          psi label • taggedCczPhysicalTransport (F := F) (ι := data.PivotComplement)
            (taggedEncodingLinearMap data (registerBasisKet label)) := by
              rw [map_sum]
              simp_rw [map_smul]
    _ = ∑ label : TaggedThreeCopyRegisterLabel F Logical,
          psi label • taggedEncodingLinearMap data
            (taggedLogicalCczTransport (F := F) (Logical := Logical)
              (registerBasisKet label)) := by
              apply Finset.sum_congr rfl
              intro label _
              congr 1
              have hbasis := taggedCczPhysicalTransport_intertwines_basis data label
              change taggedCczPhysicalTransport (F := F) (ι := data.PivotComplement)
                  (taggedEncodingLinearMap data (registerBasisKet label)) =
                taggedEncodingLinearMap data
                  (taggedLogicalCczTransport (F := F) (Logical := Logical)
                    (registerBasisKet label)) at hbasis
              exact hbasis
    _ = taggedEncodingLinearMap data
          (∑ label : TaggedThreeCopyRegisterLabel F Logical,
            psi label • taggedLogicalCczTransport (F := F) (Logical := Logical)
              (registerBasisKet label)) := by
              rw [map_sum]
              simp_rw [map_smul]
    _ = taggedEncodingLinearMap data
          (taggedLogicalCczTransport (F := F) (Logical := Logical) psi) := by rw [← hlogical]
def taggedCczPermittedSupports (data : SourceInput F I Logical) :
    Finset (Finset (TaggedThreeCopyCoordinate data.PivotComplement)) :=
  Finset.univ.image coordinateSupport
theorem taggedCczPhysicalFactorization_support_permitted (data : SourceInput F I Logical)
    (j : Fin (Fintype.card data.PivotComplement)) :
    (taggedCczPhysicalFactorization (F := F) (ι := data.PivotComplement)).support j ∈
      taggedCczPermittedSupports data := by
  simp [taggedCczPhysicalFactorization, taggedCczPermittedSupports]
noncomputable def taggedCczSubsetTransversality (data : SourceInput F I Logical) :
    SubsetTransversalityData
      (taggedCczPhysicalGateModel (F := F) (ι := data.PivotComplement))
      (taggedCczPhysicalTransport (F := F) (ι := data.PivotComplement))
      (taggedCczPermittedSupports data) where
  toPhysicalGateFactorization :=
    taggedCczPhysicalFactorization (F := F) (ι := data.PivotComplement)
  support_permitted := taggedCczPhysicalFactorization_support_permitted data
noncomputable def taggedCczSubsetTransversalLogicalGate
    (data : SourceInput F I Logical) [CharP F 2] :
    SubsetTransversalLogicalGate
      (taggedEncodedCode data)
      (taggedLogicalCczTransport (F := F) (Logical := Logical))
      (taggedCczPhysicalGateModel (F := F) (ι := data.PivotComplement))
      (taggedCczPermittedSupports data) where
  physicalGate := taggedCczPhysicalTransport (F := F) (ι := data.PivotComplement)
  implements := taggedCczPhysicalTransport_implements_logical data
  transversality := taggedCczSubsetTransversality data
end QEC.Distillation.Ngu24MultiplicativeCCZ


