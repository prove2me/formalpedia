-- Prove2me | Definitions.Def_QEC_Distillation_MultiplicativeQuditProtocol_CSSShortening
-- name    : QEC_Distillation_MultiplicativeQuditProtocol_CSSShortening
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-06T12:44:22.668385+00:00
-- url     : https://prove2.me/theorems/d92ef121-1b2d-4f03-aac9-c2e220ad0661
-- title:
--   CSSShortening
-- statement:
--   Definitions and structural lemmas for CSSShortening, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/MultiplicativeQuditProtocol/CSSShortening.lean

import Definitions.Def_QEC_Coding_Core_Definitions
import Definitions.Def_QEC_Distillation_MultiplicativeQuditProtocol_Register
import Definitions.Def_QEC_Distillation_Core_TransversalGate
import Theorems.Thm_QEC_Coding_ChainComplexData_pureZLogicalQuotientEquivMiddleHomology_mk
import Theorems.Thm_QEC_Distillation_EncodedCode_ImplementsLogicalGate_symm
import Theorems.Thm_QEC_Distillation_assembleTagged_extractBlock
import Theorems.Thm_QEC_Distillation_extractBlock_assembleTagged
import Theorems.Thm_QEC_Distillation_mem_coordinateSupport
import Theorems.Thm_QEC_Semantics_UnitaryTransport_conjDensity_apply
import Theorems.Thm_QEC_Semantics_UnitaryTransport_conjDensity_toOperator
attribute [local simp] QEC.Coding.ChainComplexData.pureZLogicalQuotientEquivMiddleHomology_mk
attribute [local simp] QEC.Distillation.assembleTagged_extractBlock
attribute [local simp] QEC.Distillation.extractBlock_assembleTagged
attribute [local simp] QEC.Distillation.mem_coordinateSupport
attribute [local simp] QEC.Semantics.UnitaryTransport.conjDensity_apply
attribute [local simp] QEC.Semantics.UnitaryTransport.conjDensity_toOperator


set_option autoImplicit false
noncomputable section
namespace QEC.Distillation.Ngu24MultiplicativeCSS
open Coding Semantics
open scoped BigOperators
universe u
variable {F I Logical : Type u} [Field F] [Fintype F] [Fintype I] [Fintype Logical]
local instance _p2m_local_instance_7d0f4269de_23 : DecidableEq Logical := Classical.decEq _
local instance _p2m_local_instance_7d0f4269de_24 : DecidableEq (Word F Logical) := Classical.decEq _
local instance _p2m_local_instance_7d0f4269de_25 : Fintype (Word F Logical) := Fintype.ofFinite _
def wordStar (x y : Word F I) : Word F I := fun i => x i * y i
omit [Fintype F] [Fintype I] in
@[simp] theorem wordStar_apply (x y : Word F I) (i : I) : wordStar x y i = x i * y i := rfl
def starSquare (C : LinearCode F I) : Submodule F (Word F I) :=
  Submodule.span F {w | ∃ x ∈ C.carrier, ∃ y ∈ C.carrier, wordStar x y = w}
theorem wordStar_mem_starSquare (C : LinearCode F I) {x y : Word F I}
    (hx : x ∈ C.carrier) (hy : y ∈ C.carrier) : wordStar x y ∈ starSquare C :=
  Submodule.subset_span ⟨x, hx, y, hy, rfl⟩
def pivotRestrict (C : LinearCode F I) (pivotEmbedding : Logical ↪ I) :
    C.carrier →ₗ[F] (Logical → F) where
  toFun x := fun a => x.1 (pivotEmbedding a)
  map_add' := by
    intro x y
    ext a
    rfl
  map_smul' := by
    intro a x
    ext b
    rfl
structure SourceInput (F I Logical : Type u) [Field F] [Fintype F] [Fintype I]
    [Fintype Logical] where
  code : LinearCode F I
  pivotEmbedding : Logical ↪ I
  pivotRestrict_surjective : Function.Surjective (pivotRestrict code pivotEmbedding)
  one_mem_code : (1 : Word F I) ∈ (code : Submodule F (Word F I))
  starSquare_le_dual : starSquare code ≤ (code.dual : Submodule F (Word F I))
namespace SourceInput
noncomputable def pivotSection (data : SourceInput F I Logical) :
    (Logical → F) →ₗ[F] data.code.carrier :=
  (pivotRestrict data.code data.pivotEmbedding).splittingOfFunOnFintypeSurjective
    data.pivotRestrict_surjective
theorem pivotRestrict_pivotSection (data : SourceInput F I Logical) (u : Logical → F) :
    pivotRestrict data.code data.pivotEmbedding (data.pivotSection u) = u :=
  (pivotRestrict data.code data.pivotEmbedding).leftInverse_splittingOfFunOnFintypeSurjective
    data.pivotRestrict_surjective u
def PivotComplement (data : SourceInput F I Logical) : Type u :=
  {i : I // i ∉ Set.range data.pivotEmbedding}
noncomputable instance pivotComplementFintype (data : SourceInput F I Logical) :
    Fintype data.PivotComplement := by
  classical
  exact Fintype.subtype (Finset.univ.filter fun i => i ∉ Set.range data.pivotEmbedding)
    (by simp)
noncomputable instance pivotComplementDecidableEq (data : SourceInput F I Logical) :
    DecidableEq data.PivotComplement := Classical.decEq _
def puncture (data : SourceInput F I Logical) :
    Word F I →ₗ[F] Word F data.PivotComplement where
  toFun x := fun i => x i.1
  map_add' := by
    intro x y
    ext i
    rfl
  map_smul' := by
    intro a x
    ext i
    rfl
def shortenedKernel (data : SourceInput F I Logical) : Submodule F data.code.carrier :=
  (pivotRestrict data.code data.pivotEmbedding).ker
def shortenedCode (data : SourceInput F I Logical) :
    Submodule F (Word F data.PivotComplement) :=
  data.shortenedKernel.map (data.puncture.comp data.code.carrier.subtype)
def systematicLogicalWord (data : SourceInput F I Logical) (u : Logical → F) : Word F I :=
  data.pivotSection u
def puncturedLogicalWord (data : SourceInput F I Logical) (u : Logical → F) :
    Word F data.PivotComplement :=
  data.puncture (data.systematicLogicalWord u)
def pivotCoordinates (data : SourceInput F I Logical) (x : Word F I) : Word F Logical :=
  fun a => x (data.pivotEmbedding a)
@[simp]
theorem pivotCoordinates_systematicLogicalWord (data : SourceInput F I Logical)
    (u : Word F Logical) : data.pivotCoordinates (data.systematicLogicalWord u) = u := by
  ext a
  exact congrFun (data.pivotRestrict_pivotSection u) a
theorem shortenedKernel_pivot_zero (data : SourceInput F I Logical)
    (h : data.shortenedKernel) (a : Logical) : h.1.1 (data.pivotEmbedding a) = 0 := by
  have hzero : pivotRestrict data.code data.pivotEmbedding h.1 = 0 := h.2
  exact congrFun hzero a
theorem wordPairing_pivot_eq_of_puncture_eq_zero (data : SourceInput F I Logical)
    (left right : Word F I) (hzero : data.puncture left = 0) :
    wordPairing (data.pivotCoordinates left) (data.pivotCoordinates right) =
      wordPairing left right := by
  classical
  letI : Fintype (Set.range data.pivotEmbedding) :=
    Fintype.subtype (Finset.univ.filter fun i => i ∈ Set.range data.pivotEmbedding)
      (by simp)
  have hcomplement (point : data.PivotComplement) : left point.1 = 0 :=
    congrFun hzero point
  have hsplit := Fintype.sum_subtype_add_sum_subtype
    (fun i : I => i ∈ Set.range data.pivotEmbedding)
    (fun i => left i * right i)
  have hcomplement_sum :
      (∑ point : data.PivotComplement, left point.1 * right point.1) = 0 := by
    apply Finset.sum_eq_zero
    intro point _
    rw [hcomplement point]
    simp
  have hsplit' :
      (∑ point : {i : I // i ∈ Set.range data.pivotEmbedding},
        left point.1 * right point.1) +
      (∑ point : {i : I // ¬ i ∈ Set.range data.pivotEmbedding},
        left point.1 * right point.1) =
        ∑ point : I, left point * right point := by
    exact hsplit
  let rangeEquiv : Logical ≃ Set.range data.pivotEmbedding :=
    Equiv.ofInjective data.pivotEmbedding data.pivotEmbedding.injective
  have hrange :
      (∑ point : Set.range data.pivotEmbedding, left point.1 * right point.1) =
        ∑ a : Logical, left (data.pivotEmbedding a) * right (data.pivotEmbedding a) := by
    exact Fintype.sum_equiv rangeEquiv.symm
      (fun point => left point.1 * right point.1)
      (fun a => left (data.pivotEmbedding a) * right (data.pivotEmbedding a))
      (fun point => by
        have hpoint : data.pivotEmbedding (rangeEquiv.symm point) = point.1 :=
          congrArg Subtype.val (rangeEquiv.apply_symm_apply point)
        change left point.1 * right point.1 =
          left (data.pivotEmbedding (rangeEquiv.symm point)) *
            right (data.pivotEmbedding (rangeEquiv.symm point))
        rw [hpoint])
  let complementEquiv : {i : I // ¬ i ∈ Set.range data.pivotEmbedding} ≃
      data.PivotComplement := Equiv.refl _
  have hcomplement_equiv :
      (∑ point : {i : I // ¬ i ∈ Set.range data.pivotEmbedding},
        left point.1 * right point.1) =
        ∑ point : data.PivotComplement, left point.1 * right point.1 := by
    exact Fintype.sum_equiv complementEquiv
      (fun point => left point.1 * right point.1)
      (fun point => left point.1 * right point.1) (fun _ => rfl)
  calc
    wordPairing (data.pivotCoordinates left) (data.pivotCoordinates right) =
        ∑ a : Logical, left (data.pivotEmbedding a) * right (data.pivotEmbedding a) := rfl
    _ = ∑ point : Set.range data.pivotEmbedding, left point.1 * right point.1 := hrange.symm
    _ = ∑ point : I, left point * right point := by
      rw [hcomplement_equiv, hcomplement_sum, add_zero] at hsplit'
      exact hsplit'
    _ = wordPairing left right := rfl
omit [Fintype F] in
/-- Pairing against a coordinate unit reads that coordinate. -/
theorem wordPairing_canonicalBasisWord_right (x : Word F Logical) (a : Logical) :
    wordPairing x (canonicalBasisWord a) = x a := by
  classical
  rw [wordPairing_apply, canonicalBasisWord, dotProduct_single_one]
theorem puncture_injective_on_shortenedKernel (data : SourceInput F I Logical) :
    Function.Injective (fun h : data.shortenedKernel => data.puncture h.1.1) := by
  intro h k hEq
  apply Subtype.ext
  apply Subtype.ext
  funext i
  by_cases hpivot : i ∈ Set.range data.pivotEmbedding
  · rcases hpivot with ⟨a, rfl⟩
    rw [data.shortenedKernel_pivot_zero h a, data.shortenedKernel_pivot_zero k a]
  · exact congrFun hEq ⟨i, hpivot⟩
def shortenedCosetLabel (data : SourceInput F I Logical) (u : Word F Logical)
    (h : data.shortenedKernel) : Word F data.PivotComplement :=
  data.puncturedLogicalWord u + data.puncture h.1.1
theorem shortenedCosetLabel_eq_implies_logical_eq (data : SourceInput F I Logical)
    (u v : Word F Logical) (h k : data.shortenedKernel)
    (hEq : data.shortenedCosetLabel u h = data.shortenedCosetLabel v k) : u = v := by
  let difference : Word F I :=
    (data.systematicLogicalWord u + h.1.1) - (data.systematicLogicalWord v + k.1.1)
  have hdifference : difference ∈ data.code.carrier := by
    exact data.code.carrier.sub_mem
      (data.code.carrier.add_mem (data.pivotSection u).property h.1.2)
      (data.code.carrier.add_mem (data.pivotSection v).property k.1.2)
  have hpuncture : data.puncture difference = 0 := by
    change (data.puncture (data.systematicLogicalWord u) + data.puncture h.1.1) -
        (data.puncture (data.systematicLogicalWord v) + data.puncture k.1.1) = 0
    rw [sub_eq_zero]
    exact hEq
  funext a
  have hstar : wordStar difference (data.systematicLogicalWord (canonicalBasisWord a)) ∈
      data.code.dual.carrier :=
    data.starSquare_le_dual (wordStar_mem_starSquare data.code hdifference
      (data.pivotSection (canonicalBasisWord a)).property)
  have hpairRaw := data.code.dual_orthogonal data.one_mem_code hstar
  have hpair : wordPairing difference (data.systematicLogicalWord (canonicalBasisWord a)) = 0 := by
    simpa [wordPairing_apply, wordStar, dotProduct, mul_comm] using hpairRaw
  have hpivot := data.wordPairing_pivot_eq_of_puncture_eq_zero difference
    (data.systematicLogicalWord (canonicalBasisWord a)) hpuncture
  have hzero : wordPairing (data.pivotCoordinates difference)
      (canonicalBasisWord a) = 0 := by
    have hsystematic : data.pivotCoordinates
        (data.systematicLogicalWord (canonicalBasisWord a)) = canonicalBasisWord a :=
      data.pivotCoordinates_systematicLogicalWord (canonicalBasisWord a)
    calc
      wordPairing (data.pivotCoordinates difference) (canonicalBasisWord a) =
          wordPairing (data.pivotCoordinates difference)
            (data.pivotCoordinates (data.systematicLogicalWord (canonicalBasisWord a))) := by
              rw [hsystematic]
      _ = wordPairing difference (data.systematicLogicalWord (canonicalBasisWord a)) := hpivot
      _ = 0 := hpair
  have hcoordinate : data.pivotCoordinates difference a = 0 := by
    rw [wordPairing_canonicalBasisWord_right] at hzero
    exact hzero
  change u a = v a
  have hu : data.systematicLogicalWord u (data.pivotEmbedding a) = u a :=
    congrFun (data.pivotRestrict_pivotSection u) a
  have hv : data.systematicLogicalWord v (data.pivotEmbedding a) = v a :=
    congrFun (data.pivotRestrict_pivotSection v) a
  change (data.systematicLogicalWord u + h.1.1 -
      (data.systematicLogicalWord v + k.1.1)) (data.pivotEmbedding a) = 0 at hcoordinate
  simp only [Pi.add_apply, Pi.sub_apply] at hcoordinate
  rw [hu, hv, data.shortenedKernel_pivot_zero h a,
    data.shortenedKernel_pivot_zero k a] at hcoordinate
  simpa using sub_eq_zero.mp hcoordinate
abbrev H0 (data : SourceInput F I Logical) := data.shortenedKernel
noncomputable instance h0Fintype (data : SourceInput F I Logical) : Fintype (H0 data) :=
  Fintype.ofFinite _
def cosetNormalization (H0 : Type u) [Fintype H0] : Complex :=
  (Real.sqrt (Nat.card H0 : Real) : Complex)⁻¹
theorem shortenedCosetLabel_injective (data : SourceInput F I Logical)
    (u : Word F Logical) : Function.Injective (data.shortenedCosetLabel u) := by
  intro h k hEq
  apply data.puncture_injective_on_shortenedKernel
  apply add_left_cancel (a := data.puncturedLogicalWord u)
  simpa [shortenedCosetLabel] using hEq
def shortenedCosetKet (data : SourceInput F I Logical) (u : Word F Logical) :
    ComputationalBasisRegister F data.PivotComplement :=
  cosetNormalization (H0 data) •
    ∑ h : H0 data, registerBasisKet (data.shortenedCosetLabel u h)
theorem uniformCosetSum_inner (data : SourceInput F I Logical)
    (u v : Word F Logical) :
    inner Complex
        (∑ h : H0 data, registerBasisKet (data.shortenedCosetLabel u h))
        (∑ k : H0 data, registerBasisKet (data.shortenedCosetLabel v k)) =
      if u = v then (Nat.card (H0 data) : Complex) else 0 := by
  classical
  rw [inner_sum]
  simp_rw [sum_inner]
  by_cases huv : u = v
  · subst v
    have hinner (h k : H0 data) :
        inner Complex (registerBasisKet (data.shortenedCosetLabel u h))
          (registerBasisKet (data.shortenedCosetLabel u k)) = if h = k then 1 else 0 := by
      simp only [registerBasisKet, EuclideanSpace.basisFun_apply]
      rw [EuclideanSpace.inner_single_left]
      simp [PiLp.single_apply, (data.shortenedCosetLabel_injective u).eq_iff]
    simp_rw [hinner]
    simp [Nat.card_eq_fintype_card]
  · rw [if_neg huv]
    apply Finset.sum_eq_zero
    intro h _
    apply Finset.sum_eq_zero
    intro k _
    have hlabel : data.shortenedCosetLabel u k ≠ data.shortenedCosetLabel v h :=
      fun heq => huv (data.shortenedCosetLabel_eq_implies_logical_eq u v k h heq)
    simp only [registerBasisKet, EuclideanSpace.basisFun_apply]
    rw [EuclideanSpace.inner_single_left]
    simp [hlabel]
theorem cosetNormalization_conj_mul_card (data : SourceInput F I Logical) :
    starRingEnd Complex (cosetNormalization (H0 data)) * cosetNormalization (H0 data) *
        (Nat.card (H0 data) : Complex) = 1 := by
  have hpos : (0 : Real) < Nat.card (H0 data) := by
    exact_mod_cast (Nat.card_pos : 0 < Nat.card (H0 data))
  have hsqrt : (Real.sqrt (Nat.card (H0 data) : Real) : Complex) ≠ 0 := by
    exact_mod_cast Real.sqrt_ne_zero'.mpr hpos
  unfold cosetNormalization
  rw [map_inv₀, Complex.conj_ofReal]
  field_simp
  norm_cast
  exact (Real.sq_sqrt hpos.le).symm
theorem shortenedCosetKet_inner (data : SourceInput F I Logical)
    (u v : Word F Logical) :
    inner Complex (data.shortenedCosetKet u) (data.shortenedCosetKet v) =
      if u = v then 1 else 0 := by
  unfold shortenedCosetKet
  rw [inner_smul_left, inner_smul_right, uniformCosetSum_inner]
  by_cases huv : u = v
  · subst v
    simp only [ite_true]
    rw [← mul_assoc]
    exact data.cosetNormalization_conj_mul_card
  · simp [huv]
theorem shortenedCosetKet_orthonormal (data : SourceInput F I Logical) :
    Orthonormal Complex (data.shortenedCosetKet) := by
  rw [orthonormal_iff_ite]
  intro u v
  exact data.shortenedCosetKet_inner u v
noncomputable def encodingLinearMap (data : SourceInput F I Logical) :
    ComputationalBasisRegister F Logical →ₗ[Complex]
      ComputationalBasisRegister F data.PivotComplement where
  toFun psi := ∑ u : Word F Logical, psi u • data.shortenedCosetKet u
  map_add' psi chi := by
    simp only [WithLp.ofLp_add, Pi.add_apply, add_smul, Finset.sum_add_distrib]
  map_smul' a psi := by
    simp only [WithLp.ofLp_smul, Pi.smul_apply, smul_eq_mul, Finset.smul_sum]
    apply Finset.sum_congr rfl
    intro u _
    simp only [RingHom.id_apply]
    rw [smul_smul, mul_comm]
theorem encodingLinearMap_map_inner (data : SourceInput F I Logical)
    (psi chi : ComputationalBasisRegister F Logical) :
    inner Complex (data.encodingLinearMap psi) (data.encodingLinearMap chi) =
      inner Complex psi chi := by
  change inner Complex
      (∑ u : Word F Logical, psi u • data.shortenedCosetKet u)
      (∑ u : Word F Logical, chi u • data.shortenedCosetKet u) =
        inner Complex psi chi
  rw [data.shortenedCosetKet_orthonormal.inner_sum psi chi Finset.univ]
  simp [PiLp.inner_apply, mul_comm]
noncomputable def encodingIsometry (data : SourceInput F I Logical) :
    ComputationalBasisRegister F Logical →ₗᵢ[Complex]
      ComputationalBasisRegister F data.PivotComplement :=
  data.encodingLinearMap.isometryOfInner data.encodingLinearMap_map_inner
noncomputable def encodedCarrier (data : SourceInput F I Logical) :
    Submodule Complex (ComputationalBasisRegister F data.PivotComplement) :=
  (encodingIsometry data).toLinearMap.range
noncomputable def quantumCode (data : SourceInput F I Logical) :
    QuantumCode (ComputationalBasisRegister F data.PivotComplement) where
  carrier := data.encodedCarrier
noncomputable def encodedCode (data : SourceInput F I Logical) :
    EncodedCode (ComputationalBasisRegister F Logical)
      (ComputationalBasisRegister F data.PivotComplement) where
  code := data.quantumCode
  encoding := LinearIsometry.equivRange (data.encodingIsometry)
end SourceInput
end QEC.Distillation.Ngu24MultiplicativeCSS


