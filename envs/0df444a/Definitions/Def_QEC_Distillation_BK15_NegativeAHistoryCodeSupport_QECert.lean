-- Prove2me | Definitions.Def_QEC_Distillation_BK15_NegativeAHistoryCodeSupport_QECert
-- name    : QEC_Distillation_BK15_NegativeAHistoryCodeSupport_QECert
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-21T11:21:39.788743+00:00
-- url     : https://prove2.me/theorems/870ddca6-1ca5-4f60-9638-6972dd3705ae
-- title:
--   BK15 negative-A history code support
-- statement:
--   Exact coding identities used to evaluate the BK15 negative-A history sum.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/FifteenQubitH/Recurrence.lean

import Definitions.Def_QEC_Distillation_FifteenQubitH_Recurrence

section

set_option autoImplicit false
open QEC QEC.Distillation QEC.Distillation.BK15
open QEC Coding
namespace QEC.Distillation.BK15
theorem _root_.QEC.Distillation.BK15.l1DualModel_l1_pairing_zero_QECertNegativeAHistorySupport :
    ∀ (bc : (Sum (Fin 4) QuadraticIndex → Bit) × Bit) (a : Fin 4 → Bit),
      wordPairing (l1DualCoefficientMap bc) (l1CoefficientMap a) = 0 := by
  intro bc a
  have hpair : ∀ (b : Sum (Fin 4) QuadraticIndex → Bit) (a : Fin 4 → Bit),
      wordPairing (l2CoefficientMap b) (l1CoefficientMap a) = 0 := by
    have hrows : ∀ (g : Sum (Fin 4) QuadraticIndex) (j : Fin 4),
        wordPairing (l2Generator g) (linearGenerator j) = 0 := by decide +kernel
    intro b a
    have hb : l2CoefficientMap b = ∑ g, b g • l2Generator g := by
      funext i
      change (∑ g, b g * l2Generator g i) = _
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    have ha : l1CoefficientMap a = ∑ j, a j • linearGenerator j := by
      funext i
      change (∑ j, a j * linearGenerator j i) = _
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    rw [hb, ha]
    simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply, hrows,
      smul_zero, Finset.sum_const_zero]
  have hones : ∀ a : Fin 4 → Bit, wordPairing allOnes (l1CoefficientMap a) = 0 := by decide +kernel
  change wordPairing (l2CoefficientMap bc.1 + bc.2 • allOnes) (l1CoefficientMap a) = 0
  simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, hpair,
    hones, smul_zero, add_zero]
end QEC.Distillation.BK15
end

section

set_option autoImplicit false
open QEC QEC.Distillation QEC.Distillation.BK15
open QEC Coding
namespace QEC.Distillation.BK15
theorem _root_.QEC.Distillation.BK15.L1DualModel_le_L1_dual_QECertNegativeAHistorySupport : L1DualModel.carrier ≤ L1.dual.carrier := by
  rintro w ⟨bc, rfl⟩
  refine (L1.mem_dual _).2 ?_
  rintro c ⟨a, rfl⟩
  exact l1DualModel_l1_pairing_zero_QECertNegativeAHistorySupport bc a
end QEC.Distillation.BK15
end

section

set_option autoImplicit false
open QEC QEC.Distillation QEC.Distillation.BK15
open QEC Coding
namespace QEC.Distillation.BK15
theorem _root_.QEC.Distillation.BK15.l2DualModel_l2_pairing_zero_QECertNegativeAHistorySupport :
    ∀ (ac : (Fin 4 → Bit) × Bit) (b : Sum (Fin 4) QuadraticIndex → Bit),
      wordPairing (l2DualCoefficientMap ac) (l2CoefficientMap b) = 0 := by
  intro ac b
  have hpair : ∀ (b : Sum (Fin 4) QuadraticIndex → Bit) (a : Fin 4 → Bit),
      wordPairing (l2CoefficientMap b) (l1CoefficientMap a) = 0 := by
    have hrows : ∀ (g : Sum (Fin 4) QuadraticIndex) (j : Fin 4),
        wordPairing (l2Generator g) (linearGenerator j) = 0 := by decide +kernel
    intro b a
    have hb : l2CoefficientMap b = ∑ g, b g • l2Generator g := by
      funext i
      change (∑ g, b g * l2Generator g i) = _
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    have ha : l1CoefficientMap a = ∑ j, a j • linearGenerator j := by
      funext i
      change (∑ j, a j * linearGenerator j i) = _
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    rw [hb, ha]
    simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply, hrows,
      smul_zero, Finset.sum_const_zero]
  have hones : ∀ g : Sum (Fin 4) QuadraticIndex, wordPairing allOnes (l2Generator g) = 0 := by decide +kernel
  have hb : l2CoefficientMap b = ∑ g, b g • l2Generator g := by
    funext i
    change (∑ g, b g * l2Generator g i) = _
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  have hz : wordPairing allOnes (l2CoefficientMap b) = 0 := by
    rw [hb]
    simp only [map_sum, map_smul, hones, smul_zero, Finset.sum_const_zero]
  have hswap : wordPairing (l1CoefficientMap ac.1) (l2CoefficientMap b) = 0 := by
    rw [wordPairing_apply, dotProduct_comm, ← wordPairing_apply]
    exact hpair b ac.1
  change wordPairing (l1CoefficientMap ac.1 + ac.2 • allOnes) (l2CoefficientMap b) = 0
  simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, hswap,
    hz, smul_zero, add_zero]
end QEC.Distillation.BK15
end

section

set_option autoImplicit false
open QEC QEC.Distillation QEC.Distillation.BK15
open QEC Coding
namespace QEC.Distillation.BK15
theorem _root_.QEC.Distillation.BK15.L2DualModel_le_L2_dual_QECertNegativeAHistorySupport : L2DualModel.carrier ≤ L2.dual.carrier := by
  rintro w ⟨ac, rfl⟩
  refine (L2.mem_dual _).2 ?_
  rintro c ⟨b, rfl⟩
  exact l2DualModel_l2_pairing_zero_QECertNegativeAHistorySupport ac b
end QEC.Distillation.BK15
end

section

set_option autoImplicit false
open QEC QEC.Distillation QEC.Distillation.BK15
open QEC Coding
namespace QEC.Distillation.BK15
theorem _root_.QEC.Distillation.BK15.allOnes_not_l2_coefficient_image_QECertNegativeAHistorySupport :
    ∀ b : Sum (Fin 4) QuadraticIndex → Bit, l2CoefficientMap b ≠ allOnes := by
  decide +kernel
end QEC.Distillation.BK15
end

section

set_option autoImplicit false
open QEC QEC.Distillation QEC.Distillation.BK15
open QEC Coding
namespace QEC.Distillation.BK15
theorem _root_.QEC.Distillation.BK15.allOnes_not_mem_L2_QECertNegativeAHistorySupport : allOnes ∉ L2.carrier := by
  rintro ⟨b, hb⟩
  exact allOnes_not_l2_coefficient_image_QECertNegativeAHistorySupport b hb
end QEC.Distillation.BK15
end

section
attribute [local simp] QEC.Coding.ChainComplexData.pureZLogicalQuotientEquivMiddleHomology_mk
attribute [local simp] QEC.Semantics.UnitaryTransport.conjDensity_apply
attribute [local simp] QEC.Semantics.UnitaryTransport.conjDensity_toOperator



set_option autoImplicit false
open QEC QEC.Distillation QEC.Distillation.BK15
open QEC Coding
namespace QEC.Distillation.BK15
theorem _root_.QEC.Distillation.BK15.l1CoefficientMap_eq_sum_QECertNegativeAHistorySupport (a : Fin 4 → Bit) :
    l1CoefficientMap a = ∑ j : Fin 4, a j • linearGenerator j := by
  ext i
  simp [l1CoefficientMap, Pi.smul_apply]
end QEC.Distillation.BK15
end

section

set_option autoImplicit false
open QEC QEC.Distillation QEC.Distillation.BK15
open QEC Coding
namespace QEC.Distillation.BK15
theorem _root_.QEC.Distillation.BK15.l1CoefficientMap_injective_QECertNegativeAHistorySupport : Function.Injective l1CoefficientMap := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  decide +kernel
end QEC.Distillation.BK15
end

section

set_option autoImplicit false
open QEC QEC.Distillation QEC.Distillation.BK15
open QEC Coding
namespace QEC.Distillation.BK15
theorem _root_.QEC.Distillation.BK15.l1DualCoefficientMap_injective_QECertNegativeAHistorySupport : Function.Injective l1DualCoefficientMap := by
  -- A linear map is injective iff its kernel is zero; enumerate inputs, not pairs.
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  decide +kernel
end QEC.Distillation.BK15
end

section

set_option autoImplicit false
open QEC QEC.Distillation QEC.Distillation.BK15
open QEC Coding
namespace QEC.Distillation.BK15
theorem _root_.QEC.Distillation.BK15.quadraticIndex_card_QECertNegativeAHistorySupport : Fintype.card QuadraticIndex = 6 := by
  decide +kernel
end QEC.Distillation.BK15
end

section
attribute [local simp] QEC.Coding.ChainComplexData.pureZLogicalQuotientEquivMiddleHomology_mk
attribute [local simp] QEC.Semantics.UnitaryTransport.conjDensity_apply
attribute [local simp] QEC.Semantics.UnitaryTransport.conjDensity_toOperator



set_option autoImplicit false
open QEC QEC.Distillation QEC.Distillation.BK15
open QEC Coding
namespace QEC.Distillation.BK15
theorem _root_.QEC.Distillation.BK15.l1DualModel_dimension_QECertNegativeAHistorySupport : Dimension L1DualModel = 11 := by
  rw [Dimension_eq_finrank_carrier]
  change Module.finrank Bit (LinearMap.range l1DualCoefficientMap) = 11
  rw [LinearMap.finrank_range_of_inj l1DualCoefficientMap_injective_QECertNegativeAHistorySupport,
    Module.finrank_prod, Module.finrank_pi]
  simp [quadraticIndex_card_QECertNegativeAHistorySupport]
end QEC.Distillation.BK15
end

section
attribute [local simp] QEC.Coding.ChainComplexData.pureZLogicalQuotientEquivMiddleHomology_mk
attribute [local simp] QEC.Semantics.UnitaryTransport.conjDensity_apply
attribute [local simp] QEC.Semantics.UnitaryTransport.conjDensity_toOperator



set_option autoImplicit false
open QEC QEC.Distillation QEC.Distillation.BK15
open QEC Coding
namespace QEC.Distillation.BK15
theorem _root_.QEC.Distillation.BK15.wordPairing_l1CoefficientMap_QECertNegativeAHistorySupport (w : Word) (a : Fin 4 → Bit) :
    wordPairing w (l1CoefficientMap a) =
      ∑ j : Fin 4, a j • wordPairing w (linearGenerator j) := by
  simp only [l1CoefficientMap_eq_sum_QECertNegativeAHistorySupport, map_sum, map_smul]
end QEC.Distillation.BK15
end

section

set_option autoImplicit false
open QEC QEC.Distillation QEC.Distillation.BK15
open QEC Coding
namespace QEC.Distillation.BK15
theorem _root_.QEC.Distillation.BK15.l1Syndrome_zero_pairing_QECertNegativeAHistorySupport (w : Word) (a : Fin 4 → Bit)
    (hzero : l1Syndrome w = 0) : wordPairing w (l1CoefficientMap a) = 0 := by
  rw [wordPairing_l1CoefficientMap_QECertNegativeAHistorySupport]
  apply Finset.sum_eq_zero
  intro j _
  have hj := congrFun hzero j
  change wordPairing w (linearGenerator j) = 0 at hj
  rw [hj, smul_zero]
end QEC.Distillation.BK15
end

section
attribute [local simp] QEC.Coding.ChainComplexData.pureZLogicalQuotientEquivMiddleHomology_mk
attribute [local simp] QEC.Semantics.UnitaryTransport.conjDensity_apply
attribute [local simp] QEC.Semantics.UnitaryTransport.conjDensity_toOperator



set_option autoImplicit false
open QEC QEC.Distillation QEC.Distillation.BK15
open QEC Coding
namespace QEC.Distillation.BK15
theorem _root_.QEC.Distillation.BK15.l1_dimension_QECertNegativeAHistorySupport : Dimension L1 = 4 := by
  rw [Dimension_eq_finrank_carrier]
  change Module.finrank Bit (LinearMap.range l1CoefficientMap) = 4
  rw [LinearMap.finrank_range_of_inj l1CoefficientMap_injective_QECertNegativeAHistorySupport,
    Module.finrank_pi]
  simp
end QEC.Distillation.BK15
end

section

set_option autoImplicit false
open QEC QEC.Distillation QEC.Distillation.BK15
open QEC Coding
namespace QEC.Distillation.BK15
theorem _root_.QEC.Distillation.BK15.linearGenerator_is_l1_coefficient_image_QECertNegativeAHistorySupport :
    ∀ j : Fin 4, l1CoefficientMap (Pi.single j 1) = linearGenerator j := by
  decide +kernel
end QEC.Distillation.BK15
end

section

set_option autoImplicit false
open QEC QEC.Distillation QEC.Distillation.BK15
open QEC Coding
namespace QEC.Distillation.BK15
theorem _root_.QEC.Distillation.BK15.linearGenerator_mem_L1_QECertNegativeAHistorySupport (j : Fin 4) : linearGenerator j ∈ L1.carrier :=
  ⟨Pi.single j 1, linearGenerator_is_l1_coefficient_image_QECertNegativeAHistorySupport j⟩
end QEC.Distillation.BK15
end

section
attribute [local simp] QEC.Coding.ChainComplexData.pureZLogicalQuotientEquivMiddleHomology_mk
attribute [local simp] QEC.Semantics.UnitaryTransport.conjDensity_apply
attribute [local simp] QEC.Semantics.UnitaryTransport.conjDensity_toOperator



set_option autoImplicit false
open QEC QEC.Distillation QEC.Distillation.BK15
open QEC Coding
namespace QEC.Distillation.BK15
theorem _root_.QEC.Distillation.BK15.l1_dual_carrier_eq_l1Syndrome_ker_QECertNegativeAHistorySupport :
    L1.dual.carrier = LinearMap.ker l1Syndrome := by
  apply le_antisymm
  · intro w hw
    change l1Syndrome w = 0
    funext j
    have hj := (L1.mem_dual w).1 hw (linearGenerator j) (linearGenerator_mem_L1_QECertNegativeAHistorySupport j)
    simpa [l1Syndrome] using hj
  · intro w hw
    change l1Syndrome w = 0 at hw
    refine (L1.mem_dual w).2 ?_
    rintro c ⟨a, rfl⟩
    exact l1Syndrome_zero_pairing_QECertNegativeAHistorySupport w a hw
end QEC.Distillation.BK15
end

section


set_option autoImplicit false
open QEC QEC.Distillation QEC.Distillation.BK15
open QEC Coding
namespace QEC.Distillation.BK15
theorem _root_.QEC.Distillation.BK15.l1_dual_dimension_QECertNegativeAHistorySupport : Dimension L1.dual = 11 := by
  rw [LinearCode.dual_dimension_eq_length_sub_dimension, l1_dimension_QECertNegativeAHistorySupport]
  decide +kernel
end QEC.Distillation.BK15
end

section
attribute [local simp] QEC.Coding.ChainComplexData.pureZLogicalQuotientEquivMiddleHomology_mk
attribute [local simp] QEC.Semantics.UnitaryTransport.conjDensity_apply
attribute [local simp] QEC.Semantics.UnitaryTransport.conjDensity_toOperator



set_option autoImplicit false
open QEC QEC.Distillation QEC.Distillation.BK15
open QEC Coding
namespace QEC.Distillation.BK15
theorem _root_.QEC.Distillation.BK15.l1_dual_carrier_eq_model_QECertNegativeAHistorySupport : L1.dual.carrier = L1DualModel.carrier := by
  symm
  apply Submodule.eq_of_le_of_finrank_eq L1DualModel_le_L1_dual_QECertNegativeAHistorySupport
  simpa only [Dimension_eq_finrank_carrier] using
    l1DualModel_dimension_QECertNegativeAHistorySupport.trans l1_dual_dimension_QECertNegativeAHistorySupport.symm
end QEC.Distillation.BK15
end

section
attribute [local simp] QEC.Coding.ChainComplexData.pureZLogicalQuotientEquivMiddleHomology_mk
attribute [local simp] QEC.Semantics.UnitaryTransport.conjDensity_apply
attribute [local simp] QEC.Semantics.UnitaryTransport.conjDensity_toOperator



set_option autoImplicit false
open QEC QEC.Distillation QEC.Distillation.BK15
open QEC Coding
namespace QEC.Distillation.BK15
theorem _root_.QEC.Distillation.BK15.l2CoefficientMap_eq_sum_QECertNegativeAHistorySupport (b : Sum (Fin 4) QuadraticIndex → Bit) :
    l2CoefficientMap b = ∑ g : Sum (Fin 4) QuadraticIndex, b g • l2Generator g := by
  ext i
  simp [l2CoefficientMap, Pi.smul_apply]
end QEC.Distillation.BK15
end

section

set_option autoImplicit false
open QEC QEC.Distillation QEC.Distillation.BK15
open QEC Coding
namespace QEC.Distillation.BK15
theorem _root_.QEC.Distillation.BK15.l2CoefficientMap_injective_QECertNegativeAHistorySupport : Function.Injective l2CoefficientMap := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  decide +kernel
end QEC.Distillation.BK15
end

section

set_option autoImplicit false
open QEC QEC.Distillation QEC.Distillation.BK15
open QEC Coding
namespace QEC.Distillation.BK15
theorem _root_.QEC.Distillation.BK15.l2CoefficientMap_mem_QECertNegativeAHistorySupport (a : Sum (Fin 4) QuadraticIndex → Bit) :
    l2CoefficientMap a ∈ L2.carrier :=
  ⟨a, rfl⟩
end QEC.Distillation.BK15
end

section

set_option autoImplicit false
open QEC QEC.Distillation QEC.Distillation.BK15
open QEC Coding
namespace QEC.Distillation.BK15
theorem _root_.QEC.Distillation.BK15.l2DualCoefficientMap_injective_QECertNegativeAHistorySupport : Function.Injective l2DualCoefficientMap := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  decide +kernel
end QEC.Distillation.BK15
end

section
attribute [local simp] QEC.Coding.ChainComplexData.pureZLogicalQuotientEquivMiddleHomology_mk
attribute [local simp] QEC.Semantics.UnitaryTransport.conjDensity_apply
attribute [local simp] QEC.Semantics.UnitaryTransport.conjDensity_toOperator



set_option autoImplicit false
open QEC QEC.Distillation QEC.Distillation.BK15
open QEC Coding
namespace QEC.Distillation.BK15
theorem _root_.QEC.Distillation.BK15.l2DualModel_dimension_QECertNegativeAHistorySupport : Dimension L2DualModel = 5 := by
  rw [Dimension_eq_finrank_carrier]
  change Module.finrank Bit (LinearMap.range l2DualCoefficientMap) = 5
  rw [LinearMap.finrank_range_of_inj l2DualCoefficientMap_injective_QECertNegativeAHistorySupport,
    Module.finrank_prod, Module.finrank_pi]
  simp
end QEC.Distillation.BK15
end

section

set_option autoImplicit false
open QEC QEC.Distillation QEC.Distillation.BK15
open QEC Coding
namespace QEC.Distillation.BK15
theorem _root_.QEC.Distillation.BK15.l2Generator_is_l2_coefficient_image_QECertNegativeAHistorySupport :
    ∀ g : Sum (Fin 4) QuadraticIndex,
      l2CoefficientMap (Pi.single g 1) = l2Generator g := by
  decide +kernel
end QEC.Distillation.BK15
end

section

set_option autoImplicit false
open QEC QEC.Distillation QEC.Distillation.BK15
open QEC Coding
namespace QEC.Distillation.BK15
theorem _root_.QEC.Distillation.BK15.l2Generator_mem_L2_QECertNegativeAHistorySupport (g : Sum (Fin 4) QuadraticIndex) :
    l2Generator g ∈ L2.carrier :=
  ⟨Pi.single g 1, l2Generator_is_l2_coefficient_image_QECertNegativeAHistorySupport g⟩
end QEC.Distillation.BK15
end

section
attribute [local simp] QEC.Coding.ChainComplexData.pureZLogicalQuotientEquivMiddleHomology_mk
attribute [local simp] QEC.Semantics.UnitaryTransport.conjDensity_apply
attribute [local simp] QEC.Semantics.UnitaryTransport.conjDensity_toOperator



set_option autoImplicit false
open QEC QEC.Distillation QEC.Distillation.BK15
open QEC Coding
namespace QEC.Distillation.BK15
theorem _root_.QEC.Distillation.BK15.wordPairing_l2CoefficientMap_QECertNegativeAHistorySupport (w : Word)
    (b : Sum (Fin 4) QuadraticIndex → Bit) :
    wordPairing w (l2CoefficientMap b) =
      ∑ g : Sum (Fin 4) QuadraticIndex, b g • wordPairing w (l2Generator g) := by
  simp only [l2CoefficientMap_eq_sum_QECertNegativeAHistorySupport, map_sum, map_smul]
end QEC.Distillation.BK15
end

section

set_option autoImplicit false
open QEC QEC.Distillation QEC.Distillation.BK15
open QEC Coding
namespace QEC.Distillation.BK15
theorem _root_.QEC.Distillation.BK15.l2Syndrome_zero_pairing_QECertNegativeAHistorySupport (w : Word)
    (b : Sum (Fin 4) QuadraticIndex → Bit)
    (hzero : l2Syndrome w = 0) : wordPairing w (l2CoefficientMap b) = 0 := by
  rw [wordPairing_l2CoefficientMap_QECertNegativeAHistorySupport]
  apply Finset.sum_eq_zero
  intro g _
  have hg := congrFun hzero g
  change wordPairing w (l2Generator g) = 0 at hg
  rw [hg, smul_zero]
end QEC.Distillation.BK15
end

section

set_option autoImplicit false
open QEC QEC.Distillation QEC.Distillation.BK15
open QEC Coding
namespace QEC.Distillation.BK15
theorem _root_.QEC.Distillation.BK15.l2Words_disjoint_l2LogicalCosetWords_QECertNegativeAHistorySupport : Disjoint l2Words l2LogicalCosetWords := by
  apply Finset.disjoint_left.mpr
  intro w hw hcoset
  rw [l2Words, Finset.mem_image] at hw
  rcases hw with ⟨a, _, ha⟩
  rw [l2LogicalCosetWords, Finset.mem_image] at hcoset
  rcases hcoset with ⟨u, hu, hu_eq⟩
  rw [l2Words, Finset.mem_image] at hu
  rcases hu with ⟨b, _, hb⟩
  apply allOnes_not_mem_L2_QECertNegativeAHistorySupport
  have hdiff : l2CoefficientMap a - l2CoefficientMap b = allOnes := by
    rw [ha, hb, ← hu_eq]
    abel
  rw [← hdiff]
  exact L2.carrier.sub_mem (l2CoefficientMap_mem_QECertNegativeAHistorySupport a) (l2CoefficientMap_mem_QECertNegativeAHistorySupport b)
end QEC.Distillation.BK15
end

section
attribute [local simp] QEC.Coding.ChainComplexData.pureZLogicalQuotientEquivMiddleHomology_mk
attribute [local simp] QEC.Semantics.UnitaryTransport.conjDensity_apply
attribute [local simp] QEC.Semantics.UnitaryTransport.conjDensity_toOperator



set_option autoImplicit false
open QEC QEC.Distillation QEC.Distillation.BK15
open QEC Coding
namespace QEC.Distillation.BK15
theorem _root_.QEC.Distillation.BK15.l2_dimension_QECertNegativeAHistorySupport : Dimension L2 = 10 := by
  rw [Dimension_eq_finrank_carrier]
  change Module.finrank Bit (LinearMap.range l2CoefficientMap) = 10
  rw [LinearMap.finrank_range_of_inj l2CoefficientMap_injective_QECertNegativeAHistorySupport,
    Module.finrank_pi]
  simp [quadraticIndex_card_QECertNegativeAHistorySupport]
end QEC.Distillation.BK15
end

section
attribute [local simp] QEC.Coding.ChainComplexData.pureZLogicalQuotientEquivMiddleHomology_mk
attribute [local simp] QEC.Semantics.UnitaryTransport.conjDensity_apply
attribute [local simp] QEC.Semantics.UnitaryTransport.conjDensity_toOperator



set_option autoImplicit false
open QEC QEC.Distillation QEC.Distillation.BK15
open QEC Coding
namespace QEC.Distillation.BK15
theorem _root_.QEC.Distillation.BK15.l2_dual_carrier_eq_l2Syndrome_ker_QECertNegativeAHistorySupport :
    L2.dual.carrier = LinearMap.ker l2Syndrome := by
  apply le_antisymm
  · intro w hw
    change l2Syndrome w = 0
    funext g
    have hg := (L2.mem_dual w).1 hw (l2Generator g) (l2Generator_mem_L2_QECertNegativeAHistorySupport g)
    simpa [l2Syndrome] using hg
  · intro w hw
    change l2Syndrome w = 0 at hw
    refine (L2.mem_dual w).2 ?_
    rintro c ⟨b, rfl⟩
    exact l2Syndrome_zero_pairing_QECertNegativeAHistorySupport w b hw
end QEC.Distillation.BK15
end

section


set_option autoImplicit false
open QEC QEC.Distillation QEC.Distillation.BK15
open QEC Coding
namespace QEC.Distillation.BK15
theorem _root_.QEC.Distillation.BK15.l2_dual_dimension_QECertNegativeAHistorySupport : Dimension L2.dual = 5 := by
  rw [LinearCode.dual_dimension_eq_length_sub_dimension, l2_dimension_QECertNegativeAHistorySupport]
  decide +kernel
end QEC.Distillation.BK15
end

section
attribute [local simp] QEC.Coding.ChainComplexData.pureZLogicalQuotientEquivMiddleHomology_mk
attribute [local simp] QEC.Semantics.UnitaryTransport.conjDensity_apply
attribute [local simp] QEC.Semantics.UnitaryTransport.conjDensity_toOperator



set_option autoImplicit false
open QEC QEC.Distillation QEC.Distillation.BK15
open QEC Coding
namespace QEC.Distillation.BK15
theorem _root_.QEC.Distillation.BK15.l2_dual_carrier_eq_model_QECertNegativeAHistorySupport : L2.dual.carrier = L2DualModel.carrier := by
  symm
  apply Submodule.eq_of_le_of_finrank_eq L2DualModel_le_L2_dual_QECertNegativeAHistorySupport
  simpa only [Dimension_eq_finrank_carrier] using
    l2DualModel_dimension_QECertNegativeAHistorySupport.trans l2_dual_dimension_QECertNegativeAHistorySupport.symm
end QEC.Distillation.BK15
end

section

set_option autoImplicit false
open QEC QEC.Distillation QEC.Distillation.BK15
open QEC Coding
set_option maxRecDepth 16384
namespace QEC.Distillation.BK15
theorem _root_.QEC.Distillation.BK15.mem_l1DualWords_iff_QECertNegativeAHistorySupport (w : Word) : w ∈ l1DualWords ↔ w ∈ L1.dual.carrier := by
  constructor
  · intro hw
    rw [l1DualWords, Finset.mem_image] at hw
    rcases hw with ⟨bc, -, hbc⟩
    rw [l1_dual_carrier_eq_model_QECertNegativeAHistorySupport]
    exact ⟨bc, hbc⟩
  · intro hw
    rw [l1_dual_carrier_eq_model_QECertNegativeAHistorySupport] at hw
    rcases hw with ⟨bc, hbc⟩
    rw [l1DualWords, Finset.mem_image]
    exact ⟨bc, Finset.mem_univ _, hbc⟩
end QEC.Distillation.BK15
end

section

set_option autoImplicit false
open QEC QEC.Distillation QEC.Distillation.BK15
open QEC Coding
namespace QEC.Distillation.BK15
theorem _root_.QEC.Distillation.BK15.mem_l1_dual_iff_exists_l2_plus_allOnes_QECertNegativeAHistorySupport (w : Word) :
    w ∈ L1.dual.carrier ↔
      ∃ b : Sum (Fin 4) QuadraticIndex → Bit, ∃ c : Bit,
        w = l2CoefficientMap b + c • allOnes := by
  constructor
  · intro hw
    rw [l1_dual_carrier_eq_model_QECertNegativeAHistorySupport] at hw
    rcases hw with ⟨bc, hbc⟩
    exact ⟨bc.1, bc.2, hbc.symm⟩
  · rintro ⟨b, c, rfl⟩
    rw [l1_dual_carrier_eq_model_QECertNegativeAHistorySupport]
    exact ⟨(b, c), rfl⟩
end QEC.Distillation.BK15
end

section
attribute [local simp] QEC.Coding.ChainComplexData.pureZLogicalQuotientEquivMiddleHomology_mk
attribute [local simp] QEC.Semantics.UnitaryTransport.conjDensity_apply
attribute [local simp] QEC.Semantics.UnitaryTransport.conjDensity_toOperator



set_option autoImplicit false
open QEC QEC.Distillation QEC.Distillation.BK15
open QEC Coding
namespace QEC.Distillation.BK15
theorem _root_.QEC.Distillation.BK15.mem_l2LogicalCosetWords_iff_QECertNegativeAHistorySupport (w : Word) :
    w ∈ l2LogicalCosetWords ↔
      ∃ b : Sum (Fin 4) QuadraticIndex → Bit, w = l2CoefficientMap b + allOnes := by
  constructor
  · intro hw
    rw [l2LogicalCosetWords, Finset.mem_image] at hw
    rcases hw with ⟨u, hu, huEq⟩
    rw [l2Words, Finset.mem_image] at hu
    rcases hu with ⟨b, -, hbEq⟩
    exact ⟨b, by simpa [hbEq] using huEq.symm⟩
  · rintro ⟨b, rfl⟩
    rw [l2LogicalCosetWords, Finset.mem_image]
    refine ⟨l2CoefficientMap b, ?_, rfl⟩
    rw [l2Words, Finset.mem_image]
    exact ⟨b, Finset.mem_univ _, rfl⟩
end QEC.Distillation.BK15
end

section

set_option autoImplicit false
open QEC QEC.Distillation QEC.Distillation.BK15
open QEC Coding
namespace QEC.Distillation.BK15
theorem _root_.QEC.Distillation.BK15.mem_l2_dual_iff_exists_l1_plus_allOnes_QECertNegativeAHistorySupport (w : Word) :
    w ∈ L2.dual.carrier ↔
      ∃ a : Fin 4 → Bit, ∃ c : Bit,
        w = l1CoefficientMap a + c • allOnes := by
  constructor
  · intro hw
    rw [l2_dual_carrier_eq_model_QECertNegativeAHistorySupport] at hw
    rcases hw with ⟨ac, hac⟩
    exact ⟨ac.1, ac.2, hac.symm⟩
  · rintro ⟨a, c, rfl⟩
    rw [l2_dual_carrier_eq_model_QECertNegativeAHistorySupport]
    exact ⟨(a, c), rfl⟩
end QEC.Distillation.BK15
end


