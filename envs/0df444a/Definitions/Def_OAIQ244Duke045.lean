-- Prove2me | Definitions.Def_OAIQ244Duke045
-- name    : OAIQ244Duke045
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-13T06:52:22.906136+00:00
-- url     : https://prove2.me/theorems/848ab9bd-a8cd-4303-a55c-ea3da38e1b67
-- title:
--   Definitions bundle OAIQ244Duke045 of the split of OpenAI, Equidistribution of Prime-Degree Torus Packets with Arbitrary Local Type
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.DukePrimeDegree.prime_degree_packet_measure_equidistribution_unconditional` and `OAI.DukePrimeDegree.prime_degree_packet_measures_tendsto_haar_unconditional`, carved from OpenAI's openai/math development (OpenAI, *Equidistribution of Prime-Degree Torus Packets with Arbitrary Local Type*, OpenAI Math Release, September 24, 2026, result family 15, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 89 declarations of OpenAI's Lean: 30 definitions, 1 instance and 58 theorems. The definitions and types are `ClassFormation.DegreeData.finiteReciprocityHom`, `ClassFormation.DegreeData.finiteReciprocityHom_of_mul`, `ClassFormation.DegreeData.finiteReciprocityNaturalityConjugateNormAddZero`, `ClassFormation.DegreeData.finiteReciprocityNaturalityFrobeniusConjugationEquiv`, `ClassFormation.DegreeData.finiteReciprocityNaturalityFrobeniusConjugationLift`, `ClassFormation.DegreeData.finiteReciprocityNaturalityFrobeniusTowerLift`, `ClassFormation.DegreeData.finiteReciprocityNaturalityFrobeniusTowerMap`, `ClassFormation.DegreeData.finiteReciprocityNaturalityFrobeniusTowerMapContinuous`, `ClassFormation.DegreeData.transferNormNaturalityAbelianizedReciprocity`, `ClassFormation.DegreeData.transferNormNaturalityFrobeniusIntermediateEquiv`, `ClassFormation.DegreeData.transferNormNaturalityFrobeniusIntermediateSubgroup`, `ClassFormation.DegreeData.transferNormNaturalityFrobeniusTransferTerm`, `ClassFormation.DegreeData.transferNormNaturalityFrobeniusTransferTermPreimage`, `ClassFormation.DegreeData.transferNormNaturalityIntermediateToFrobeniusSubgroup`, `ClassFormation.DegreeData.transferNormNaturalityTransferFrobeniusLift`, `ClassFormation.DegreeData.transferNormNaturalityTransferNormOrbitEquiv`, `ClassFormation.Internal.chosenTransferNormNaturalityNormOrbitRepresentative`, `ClassFormation.ValuationData.unramifiedReciprocityEquiv`, `ClassFormation.chosenTransferNormNaturalityRightTransversal`, `ClassFormation.conjugateFixedElementHom`, `ClassFormation.finiteReciprocityNaturalityConjugationNormMap`, `ClassFormation.finiteReciprocityNaturalityNormMap`, `ClassFormation.finiteReciprocityNaturalityRestriction`, `ClassFormation.transferNormNaturalityExtensionFixedEquiv`, `ClassFormation.transferNormNaturalityIntermediateAbsoluteEquiv`, `ClassFormation.transferNormNaturalityIntermediateInclusion`, `ClassFormation.transferNormNaturalityIntermediateQuotientEquiv`, `ClassFormation.transferNormNaturalityIntermediateSubgroup`, `ClassFormation.transferNormNaturalityNormWitness`, `ClassFormation.transferNormNaturalityRightCosetProductEquiv`.
--
--   **Sources.** They come from these modules of lean/OAI/NumberTheory, in whole or in part: `AbstractClassFieldTheory_Reciprocity_Construction_FrobeniusField`, `AbstractClassFieldTheory_Reciprocity_Construction_MainFiniteReciprocity`, `AbstractClassFieldTheory_Reciprocity_Construction_MainMultiplicativity_ReciprocityMapMul`, `AbstractClassFieldTheory_Reciprocity_Construction_MainNaturality`, `AbstractClassFieldTheory_Reciprocity_Construction_MainTransfer`, `AbstractClassFieldTheory_Reciprocity_Construction_MainTransferFrobenius`, `AbstractClassFieldTheory_Reciprocity_Construction_MainTransferFrobeniusGeometry`, `AbstractClassFieldTheory_Reciprocity_Construction_Universal`.
--
--   **Imports.** It imports the bundles `OAIQ244Duke037` and `OAIQ244Duke038` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ244Duke053` and `OAIQ244Duke061`.
-- source:
--   OpenAI, Equidistribution of Prime-Degree Torus Packets with Arbitrary Local Type, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 15; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Equidistribution-of-Prime-Degree-Torus-Packets-with-Arbitrary-Local-Type-September-24-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/NumberTheory at commit 7ef5c0c

import Mathlib
import Mathlib.Algebra.Group.Subgroup.Ker
import Mathlib.Data.ZMod.Basic
import Mathlib.Dynamics.BirkhoffSum.Basic
import Mathlib.GroupTheory.Abelianization.Defs
import Mathlib.GroupTheory.DoubleCoset
import Mathlib.GroupTheory.FiniteAbelian.Basic
import Mathlib.GroupTheory.GroupAction.Quotient
import Mathlib.GroupTheory.Index
import Mathlib.GroupTheory.QuotientGroup.Basic
import Mathlib.GroupTheory.Transfer
import Mathlib.RepresentationTheory.Homological.FiniteCyclic
import Mathlib.RepresentationTheory.Homological.GroupCohomology.FiniteCyclic
import Mathlib.RepresentationTheory.Homological.TateCohomology.Basic
import Mathlib.RepresentationTheory.Invariants
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Topology.Algebra.Category.ProfiniteGrp.Basic
import Mathlib.Topology.Algebra.ClopenNhdofOne
import Mathlib.Topology.Algebra.ContinuousMonoidHom
import Mathlib.Topology.Algebra.Group.ClosedSubgroup
import Mathlib.Topology.Algebra.Group.Quotient
import Mathlib.Topology.Algebra.Group.SubmonoidClosure
import Mathlib.Topology.Algebra.Ring.Basic
import Mathlib.Topology.Instances.ZMod
import Mathlib.Topology.Neighborhoods
import Definitions.Def_OAIQ244Duke037
import Definitions.Def_OAIQ244Duke038

section
-- module Solutions.OAIQ244_DUKE.AbstractClassFieldTheory_Reciprocity_Construction_FrobeniusField
attribute [-instance] _root_.ClassFormation.DegreeData.FiniteAmbientFrobeniusFixedFieldTower.ambientQuotientFinite _root_.ClassFormation.DegreeData.FiniteAmbientFrobeniusFixedFieldTower.ambientRepresentedQuotientFinite _root_.ClassFormation.DegreeData.FiniteTower.totalQuotientFinite _root_.ClassFormation.DegreeData.FrobeniusFixedFieldTower.baseAbsoluteFiniteInstance _root_.ClassFormation.DegreeData.FrobeniusFixedFieldTower.extensionFinite _root_.ClassFormation.DegreeData.FrobeniusFixedFieldTower.extensionNormal _root_.ClassFormation.DegreeData.FrobeniusFixedFieldTower.fieldAbsoluteFiniteInstance _root_.ClassFormation.DegreeData.FrobeniusPowerFixedFieldTower.baseRepresentedAbsoluteFinite _root_.ClassFormation.DegreeData.FrobeniusPowerFixedFieldTower.fieldRepresentedAbsoluteFinite _root_.ClassFormation.DegreeData.FrobeniusPowerFixedFieldTower.relativeRepresentedQuotientFinite _root_.ClassFormation.DegreeData.frobeniusElementsMul _root_.ClassFormation.DegreeData.frobeniusElementsSemigroup _root_.ClassFormation.DegreeData.maximalUnramifiedNormQuotientAddCommGroup _root_.ClassFormation.FiniteAbstractField.toFiniteResidueAbstractField_extensionFinite _root_.ClassFormation.FiniteAbstractField.toFiniteResidueAbstractField_extensionNormal _root_.ClassFormation.FiniteCyclicSubextension.instFiniteQuotientSubtypeMemSubgroupFieldExtensionSubgroupField _root_.ClassFormation.FiniteCyclicSubextension.instFintypeQuotientSubtypeMemSubgroupFieldExtensionSubgroupField _root_.ClassFormation.FiniteCyclicSubextension.instNormalSubtypeMemSubgroupFieldExtensionSubgroupField _root_.ClassFormation.FiniteGaloisSubextension.extensionSubgroup_normalInstance _root_.ClassFormation.FiniteGaloisSubextension.extensionSubgroup_over_intermediate_normalInstance _root_.ClassFormation.FiniteGaloisSubextension.intermediateField_normalInstance _root_.ClassFormation.FiniteIntermediateField.galoisRefinement_normal _root_.ClassFormation.FiniteUnramifiedCyclicExtension.instFiniteQuotientSubtypeMemSubgroupBaseFieldExtensionSubgroupField _root_.ClassFormation.FiniteUnramifiedCyclicExtension.instFiniteQuotientSubtypeMemSubgroupFieldExtensionSubgroupField _root_.ClassFormation.FiniteUnramifiedCyclicExtension.instFintypeQuotientSubtypeMemSubgroupFieldExtensionSubgroupField _root_.ClassFormation.FiniteUnramifiedCyclicExtension.instNormalSubtypeMemSubgroupFieldExtensionSubgroupField _root_.ClassFormation.conjugateExtension_normal _root_.ClassFormation.finiteNormQuotientAddCommGroup _root_.ClassFormation.instIsAddTorsionFreeZHat _root_.ClassFormation.instIsMulTorsionFreeMultiplicativeZHat _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalClassFieldTheory.baseFixingExtensionQuotient_finite _root_.LocalClassFieldTheory.extensionSubgroupBase_normal _root_.LocalClassFieldTheory.finiteGaloisExtensionSubgroupOfEmbedding_normal _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.LubinTate.compatibleGroupFamiliesGroup _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen
attribute [-simp] _root_.ClassFormation.DegreeData.chosenUnramifiedFrobeniusLift_exponent _root_.ClassFormation.DegreeData.extensionNormalizedDegree_frobenius_mul _root_.ClassFormation.DegreeData.finiteReciprocityCandidate_apply _root_.ClassFormation.DegreeData.finiteReciprocityCandidate_zero _root_.ClassFormation.DegreeData.frobeniusActionConjugate_coe _root_.ClassFormation.DegreeData.frobeniusExponent_actionConjugate _root_.ClassFormation.DegreeData.frobeniusExponent_chosenDegreeOneFrobeniusElement _root_.ClassFormation.DegreeData.frobeniusExponent_mul _root_.ClassFormation.DegreeData.frobeniusExponent_powerOfDegreeOne _root_.ClassFormation.DegreeData.frobeniusFixedFieldAction_coe _root_.ClassFormation.DegreeData.frobeniusLiftDifference_coe _root_.ClassFormation.DegreeData.frobeniusMul_coe _root_.ClassFormation.DegreeData.frobeniusPowerOfDegreeOne_coe _root_.ClassFormation.DegreeData.frobeniusPowerSum_coe _root_.ClassFormation.DegreeData.frobeniusQuotientAction_mk _root_.ClassFormation.DegreeData.frobeniusQuotientRepresentation_apply _root_.ClassFormation.DegreeData.frobeniusRestriction_chosenFiniteReciprocityFrobeniusLift _root_.ClassFormation.DegreeData.frobeniusRestriction_mul _root_.ClassFormation.DegreeData.maximalUnramifiedNormClass_eq_zero_iff _root_.ClassFormation.DegreeData.maximalUnramifiedNormQuotientInfiniteEquiv_maximalUnramifiedNormClass _root_.ClassFormation.DegreeData.maximalUnramifiedNormQuotientLift_maximalUnramifiedNormClass _root_.ClassFormation.DegreeData.maximalUnramifiedToFiniteNormQuotient_maximalUnramifiedNormClass _root_.ClassFormation.DegreeData.mem_maximalUnramifiedField_iff _root_.ClassFormation.DegreeData.mem_maximalUnramifiedNormSubgroup_iff _root_.ClassFormation.FiniteAbelianSubextension.extensionQuotientMk_apply _root_.ClassFormation.FiniteAbstractField.normToBase_index_eq_degree _root_.ClassFormation.FiniteGaloisSubextension.extensionQuotientMk_apply _root_.ClassFormation.FiniteGaloisSubextension.extensionQuotientMk_eq_one_iff _root_.ClassFormation.FiniteGaloisSubextension.toGaloisSubextension_isTotallyRamified_iff _root_.ClassFormation.FiniteGaloisSubextension.toGaloisSubextension_isUnramified_iff _root_.ClassFormation.ValuationData.canonicalUnramifiedNormQuotientValuation_finiteNormClass _root_.ClassFormation.ValuationData.canonicalValueQuotientHom_mk _root_.ClassFormation.ValuationData.canonicalValueReduction_one _root_.ClassFormation.ValuationData.mem_infiniteUnitAddSubgroup_iff _root_.ClassFormation.ValuationData.mem_infiniteUnitNormSubgroup_iff _root_.ClassFormation.ValuationData.mem_unitAddSubgroup_iff _root_.ClassFormation.ValuationData.oneValue_coe _root_.ClassFormation.ValuationData.unitRepresentation_quotient_mk_apply _root_.ClassFormation.ValuationData.unramifiedNormQuotientValuation_finiteNormClass _root_.ClassFormation.ValuationData.unramifiedReciprocity_equiv_of_generator_apply _root_.ClassFormation.ValuationData.valuationAt_chosenPrimeElement _root_.ClassFormation.ValuationData.valuationAt_coe _root_.ClassFormation.ValuationData.valueModulo_apply _root_.ClassFormation.absoluteConjugateCosetEquiv_mk _root_.ClassFormation.canonicalValueQuotientMap_mk _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.ClassFormation.cyclicNormClassHom_apply _root_.ClassFormation.extensionFixedRepresentationEquiv_apply_coe _root_.ClassFormation.extensionFixedRepresentationEquiv_symm_apply_coe _root_.ClassFormation.finiteNormClass_add _root_.ClassFormation.finiteNormClass_eq_zero_iff _root_.ClassFormation.finiteNormClass_nsmul _root_.ClassFormation.finiteNormClass_sub _root_.ClassFormation.finiteNormClass_zero _root_.ClassFormation.finiteNormQuotientConcreteEquiv_finiteNormClass _root_.ClassFormation.finiteNormQuotientLift_finiteNormClass _root_.ClassFormation.finiteReciprocityNaturalityConjugation_mk _root_.ClassFormation.mem_nsmulImage_iff _root_.ClassFormation.normalExtensionAction_coe _root_.ClassFormation.nsmulImage_top _root_.ClassFormation.relativeConjugateCosetEquiv_mk _root_.ClassFormation.relativeCosetAction_mk _root_.ClassFormation.relativeCosetAction_zero _root_.ClassFormation.relativeNorm_apply_coe _root_.ClassFormation.relativeNorm_self _root_.ClassFormation.toZModPow_zHatToPadicInt _root_.ClassFormation.zHatReductionRingHom_apply _root_.ClassFormation.zHatRingEquivProfiniteIntegerPrimeProduct_apply _root_.ClassFormation.zHatToPadicInt_intCast _root_.ClassFormation.zHatToProfiniteIntegerPrimeProduct_apply _root_.ClassFormation.zHatToProfiniteIntegerPrimeProduct_intCast _root_.ClassFormation.zHatUnitsContinuousMulEquivPrimeProduct_coe_apply _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.IsDiscreteValuationRing.addVal_ringEquiv _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.KummerTheory.extensionFixedEndomorphism_apply_val _root_.KummerTheory.extensionFixedKernelElement_val _root_.KummerTheory.extensionFixedRepresentation_quotient_mk_apply_val _root_.KummerTheory.mem_extensionSubgroup_iff _root_.KummerTheory.torsionQuotientEquivOfZHatMulDecomposition_mk _root_.KummerTheory.zHatUnitsContinuousMulEquivPrimeProduct_rationalCyclotomicCharacter _root_.LocalClassFieldTheory.baseFixingExtensionQuotientEquivAmbient_mk _root_.LocalClassFieldTheory.finiteResidueFrobeniusFromZHat_apply _root_.LocalClassFieldTheory.finiteResidueFrobeniusFromZHat_one _root_.LocalClassFieldTheory.residueAbsoluteDegreeIn_frobenius _root_.LocalClassFieldTheory.residueAbsoluteFrobenius_one _root_.LocalClassFieldTheory.residueFrobeniusToLimit_apply_component _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.LocalFieldTheory.residueField_algebraMap_residue _root_.OAI.PrimeDegreePackets.ThetaConstruction.schwartzCM_apply _root_.ClassFormation.DegreeData.inertiaConjugationCosetEquiv_mk _root_.infinitePlace_mult_smul
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

namespace ClassFormation

open CyclicCohomology

/-!
# The abstract reciprocity construction: the field fixed by a Frobenius lift

This file passes from the group-dual `Γ` of the Frobenius fixed-field theorem to the actual
abstract field `Σ`.  Thus `G_Σ` is the inverse image of `Γ` under
`G_K → G_K / I_L`, embedded back into the ambient profinite group.
-/

noncomputable section

variable {G : Type*} [Group G] [TopologicalSpace G]

namespace DegreeData

/-- The Frobenius fixed-field residue-degree formula on the finite extension
object: `f_{Σ|K} = d_K(σ)`. -/
theorem frobeniusFixedField_residueDegreeOverBase (D : DegreeData G)
    [IsTopologicalGroup G] [CompactSpace G] [T2Space G]
    (K : FiniteResidueAbstractField D) (L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.field.toSubgroup)
    [hLnormal : (extensionSubgroup K.field L hLK).Normal]
    [hLfinite : Finite (K.field.toSubgroup ⧸ extensionSubgroup K.field L hLK)]
    (σ : D.FrobeniusElements K L hLK) :
    ((D.frobeniusFixedFiniteExtension K L hLK σ).residueDegree D : ℕ) =
      D.frobeniusExponent K L hLK σ := by
  let E := D.frobeniusFixedFiniteExtension K L hLK σ
  rw [← E.mapped_relIndex_eq_residueDegree D]
  simpa [E, frobeniusFixedFiniteExtension] using
    D.frobeniusFixedField_mappedRelIndex K L hLK σ

end DegreeData

end
end ClassFormation
end

section
-- module Solutions.OAIQ244_DUKE.AbstractClassFieldTheory_Reciprocity_Construction_Universal
attribute [-instance] _root_.ClassFormation.FiniteGaloisSubextension.extensionSubgroup_over_intermediate_normalInstance _root_.ClassFormation.FiniteGaloisSubextension.intermediateField_normalInstance _root_.ClassFormation.FiniteGaloisSubextension.intermediateSubgroup_normalInstance _root_.ClassFormation.FiniteGaloisSubextension.upperQuotient_groupInstance _root_.ClassFormation.instIsAddTorsionFreeZHat _root_.ClassFormation.instIsMulTorsionFreeMultiplicativeZHat _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.DiscreteNthRootsSubgroup.instTopologicalSpaceSubtypeUnitsMemSubgroup _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.KummerTheory.finite_finsupp_nsmulQuotient _root_.KummerTheory.nthRootsSubgroupFintype _root_.LocalClassFieldTheory.baseFixingExtensionQuotient_finite _root_.LocalClassFieldTheory.extensionSubgroupBase_normal _root_.LocalClassFieldTheory.finiteGaloisExtensionSubgroupOfEmbedding_normal _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitQuotientCarrier_finite _root_.LocalFieldTheory.DiscreteValuationField.finite_padicInt_finPi_nsmulQuotient _root_.LocalFieldTheory.DiscreteValuationField.finite_padicInt_pi_nsmulQuotient_of_coprime _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_multiplicative_nthPowerQuotient _root_.LocalFieldTheory.finite_nsmulAddQuotient_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.LubinTate.compatibleGroupFamiliesGroup _root_.OAI.PrimeDegreePackets.boundedRealFields_finite _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.RamificationTheory.HilbertRamification.ValuationSubring.inertiaGroup_normal _root_.RamificationTheory.HilbertRamification.ValuationSubring.ramificationGroupInInertiaAut_normal _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.maximalIdealPowSuccQuotModule _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen
attribute [-simp] _root_.ClassFormation.DegreeData.chosenUnramifiedFrobeniusLift_exponent _root_.ClassFormation.DegreeData.finiteReciprocityCandidate_apply _root_.ClassFormation.DegreeData.finiteReciprocityCandidate_zero _root_.ClassFormation.DegreeData.frobeniusActionConjugate_coe _root_.ClassFormation.DegreeData.frobeniusExponent_actionConjugate _root_.ClassFormation.DegreeData.frobeniusExponent_chosenDegreeOneFrobeniusElement _root_.ClassFormation.DegreeData.frobeniusExponent_mul _root_.ClassFormation.DegreeData.frobeniusLiftDifference_coe _root_.ClassFormation.DegreeData.frobeniusRestriction_chosenFiniteReciprocityFrobeniusLift _root_.ClassFormation.DegreeData.frobeniusRestriction_mul _root_.ClassFormation.FiniteAbelianSubextension.extensionQuotientMk_apply _root_.ClassFormation.FiniteGaloisSubextension.classFieldCandidate_field _root_.ClassFormation.FiniteGaloisSubextension.intermediateFiniteAbelianOfCommutatorLe_field _root_.ClassFormation.FiniteGaloisSubextension.lowerQuotientEquiv_mk _root_.ClassFormation.FiniteGaloisSubextension.lowerQuotientEquiv_mk_coe _root_.ClassFormation.FiniteGaloisSubextension.lowerRestrictionHom_apply_coe _root_.ClassFormation.FiniteGaloisSubextension.mem_intermediateSubgroup_iff _root_.ClassFormation.FiniteGaloisSubextension.upperQuotientEquiv_mk_mk _root_.ClassFormation.FiniteGaloisSubextension.upperQuotientMk_apply _root_.ClassFormation.ValuationData.canonicalUnramifiedNormQuotientValuation_finiteNormClass _root_.ClassFormation.ValuationData.canonicalValueQuotientHom_mk _root_.ClassFormation.ValuationData.canonicalValueReduction_one _root_.ClassFormation.ValuationData.unramifiedNormQuotientValuation_finiteNormClass _root_.ClassFormation.ValuationData.unramifiedReciprocity_equiv_of_generator_apply _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.ClassFormation.cyclicNormClassHom_apply _root_.ClassFormation.extensionFixedRepresentationEquiv_apply_coe _root_.ClassFormation.extensionFixedRepresentationEquiv_symm_apply_coe _root_.ClassFormation.mem_normFilterBasis_iff _root_.ClassFormation.toZModPow_zHatToPadicInt _root_.ClassFormation.zHatReductionRingHom_apply _root_.ClassFormation.zHatRingEquivProfiniteIntegerPrimeProduct_apply _root_.ClassFormation.zHatToPadicInt_intCast _root_.ClassFormation.zHatToProfiniteIntegerPrimeProduct_apply _root_.ClassFormation.zHatToProfiniteIntegerPrimeProduct_intCast _root_.ClassFormation.zHatUnitsContinuousMulEquivPrimeProduct_coe_apply _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.IsDiscreteValuationRing.addVal_ringEquiv _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.KummerTheory.torsionQuotientEquivOfZHatMulDecomposition_mk _root_.KummerTheory.zHatUnitsContinuousMulEquivPrimeProduct_rationalCyclotomicCharacter _root_.LocalClassFieldTheory.baseFixingExtensionQuotientEquivAmbient_mk _root_.LocalClassFieldTheory.baseUnitsEquivGaloisAmbientFixed_val _root_.LocalClassFieldTheory.embeddedFieldUnitsEquivGaloisFixed_coe _root_.LocalClassFieldTheory.finiteGaloisUnitsEquivAbstractFixedOfEmbedding_coe _root_.LocalClassFieldTheory.finiteGaloisUnitsEquivAbstractFixed_coe _root_.LocalClassFieldTheory.finiteResidueFrobeniusFromZHat_apply _root_.LocalClassFieldTheory.finiteResidueFrobeniusFromZHat_one _root_.LocalClassFieldTheory.intermediateFieldUnitsEquivGaloisFixed_coe _root_.LocalClassFieldTheory.intrinsicFiniteAbstractBase_eq_base _root_.LocalClassFieldTheory.residueAbsoluteDegreeIn_frobenius _root_.LocalClassFieldTheory.residueAbsoluteFrobenius_one _root_.LocalClassFieldTheory.residueFrobeniusToLimit_apply_component _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.LocalFieldTheory.residueField_algebraMap_residue _root_.OAI.PrimeDegreePackets.ThetaConstruction.schwartzCM_apply _root_.infinitePlace_mult_smul
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false
/-!
Proves the universal norm-descent argument from maximal-unramified units to finite intermediate
norm subgroups.
-/

namespace ClassFormation

open KummerTheory

open CyclicCohomology

noncomputable section
open CategoryTheory
open scoped BigOperators
-- Mathlib's `Rep ℤ G` currently fixes the acting group to universe zero.
variable {G : IntegralRepGroupType} [Group G] [TopologicalSpace G]
namespace ValuationData
variable {D : DegreeData G} {A : Rep ℤ G}

/-- The universal norm-descent lemma, finite target step.  After placing the finite support in a
common finite Galois overfield, the descended unit is a norm from every
prescribed finite intermediate field. -/
theorem universalNormDescent_mem_finiteUnitNormRange
    (v : ValuationData D A)
    [IsTopologicalGroup G] [CompactSpace G] [T2Space G]
    [TotallyDisconnectedSpace G]
    (hAxiom : v.SatisfiesUnramifiedUnitCohomology)
    (K : FiniteAbstractField G) (L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.field.toSubgroup)
    [hLnormal : (extensionSubgroup K.field L hLK).Normal]
    [hLfinite : Finite
      (K.field.toSubgroup ⧸ extensionSubgroup K.field L hLK)]
    (φ : D.FrobeniusElements (K.toFiniteResidueAbstractField D) L hLK)
    (hφ : D.frobeniusExponent
      (K.toFiniteResidueAbstractField D) L hLK φ = 1)
    {ι : Type*} (s : Finset ι)
    (τ : ι →
      (D.extensionNormalizedDegreeContinuous
        (K.toFiniteResidueAbstractField D) L hLK).toMonoidHom.ker)
    (u : v.infiniteUnitAddSubgroup (D.maximalUnramifiedField L) K
      (D.maximalUnramifiedField_le_of_le hLK))
    (uᵢ : ι → v.infiniteUnitAddSubgroup (D.maximalUnramifiedField L) K
      (D.maximalUnramifiedField_le_of_le hLK))
    (hstar : D.frobeniusQuotientAction A K.field L hLK φ.1 u.1 - u.1 =
      ∑ i ∈ s,
        (D.frobeniusQuotientAction A K.field L hLK (τ i).1 (uᵢ i).1 -
          (uᵢ i).1))
    (aK : v.unitAddSubgroup K)
    (haK :
      letI : Finite
          ((D.maximalUnramifiedField K.field).toSubgroup ⧸
            extensionSubgroup (D.maximalUnramifiedField K.field)
              (D.maximalUnramifiedField L)
              (D.maximalUnramifiedField_mono hLK)) :=
        D.maximalUnramifiedExtension_finite K.field L hLK
      fixedFieldInclusion A K.field (D.maximalUnramifiedField K.field)
        (D.maximalUnramifiedField_le K.field) aK.1 =
        relativeNorm A (D.maximalUnramifiedField K.field)
          (D.maximalUnramifiedField L) (D.maximalUnramifiedField_mono hLK) u.1)
    (M : FiniteIntermediateField (D.maximalUnramifiedField L) K.field) :
    aK.1 ∈ v.finiteIntermediateUnitNormRange
      (D.maximalUnramifiedField L) K M := by
  classical
  let : Finite
      ((D.maximalUnramifiedField K.field).toSubgroup ⧸
        extensionSubgroup (D.maximalUnramifiedField K.field)
          (D.maximalUnramifiedField L)
          (D.maximalUnramifiedField_mono hLK)) :=
    D.maximalUnramifiedExtension_finite K.field L hLK
  let KR := K.toFiniteResidueAbstractField D
  let I := D.maximalUnramifiedField K.field
  let E := D.maximalUnramifiedField L
  let hEI := D.maximalUnramifiedField_mono hLK
  let N := relativeNorm A I E hEI
  let J := fixedFieldInclusion A I E hEI
  let hEK := D.maximalUnramifiedField_le_of_le hLK
  let hEnormal : (extensionSubgroup K.field E hEK).Normal :=
    D.extensionSubgroup_maximalUnramifiedField_normal K.field L hLK
  rcases u.2 with ⟨Mu, uMu, huMu⟩
  let ιs := {i : ι // i ∈ s}
  have huᵢsupport (j : ιs) := (uᵢ j.1).2
  choose Mi uMi huMi using huᵢsupport
  let ML : FiniteIntermediateField E K.field :=
    { field := L
      above := D.maximalUnramifiedField_le L
      below := hLK
      finite := hLfinite }
  let B₀ := M.compositum ML
  let B := B₀.compositum Mu
  obtain ⟨Q, hQB, hQMi⟩ :=
    FiniteIntermediateField.exists_common_compositum B
      (Finset.univ : Finset ιs) Mi
  let P := Q.galoisRefinement
  let hPQ : P.field.toSubgroup ≤ Q.field.toSubgroup :=
    Q.galoisRefinement_le_field
  let hPB : P.field.toSubgroup ≤ B.field.toSubgroup := hPQ.trans hQB
  let hPM : P.field.toSubgroup ≤ M.field.toSubgroup :=
    hPB.trans ((B₀.compositum_le_left Mu).trans (M.compositum_le_left ML))
  let hPL : P.field.toSubgroup ≤ L.toSubgroup :=
    hPB.trans ((B₀.compositum_le_left Mu).trans (M.compositum_le_right ML))
  let hPMu : P.field.toSubgroup ≤ Mu.field.toSubgroup :=
    hPB.trans (B₀.compositum_le_right Mu)
  let hPMi (j : ιs) : P.field.toSubgroup ≤ (Mi j).field.toSubgroup :=
    hPQ.trans (hQMi j (Finset.mem_univ j))
  let hPfinite : Finite
      (K.field.toSubgroup ⧸ extensionSubgroup K.field P.field P.below) := P.finite
  let hPnormal : (extensionSubgroup K.field P.field P.below).Normal :=
    FiniteIntermediateField.galoisRefinement_normal Q
  let n := P.quotientCard
  have hn : 0 < n := P.quotientCard_pos
  let σ := D.frobeniusPowerOfDegreeOne KR L hLK φ hφ n hn
  let σn := D.frobeniusPowerOfDegreeOne KR L hLK φ hφ (n * n)
    (Nat.mul_pos hn hn)
  let S := D.frobeniusFixedField KR L hLK σ
  let T := D.frobeniusFixedField KR L hLK σn
  let hSP : S.toSubgroup ≤ P.field.toSubgroup :=
    D.frobeniusPowerFixedField_le_finiteField KR L hLK P φ hφ
  let hSK := D.frobeniusFixedField_le KR L hLK σ
  let hTK := D.frobeniusFixedField_le KR L hLK σn
  let hTS := D.frobeniusPowerFixedField_le KR L hLK φ hφ n n hn hn
  let hTE := D.fieldInertia_le_frobeniusFixedField KR L hLK σn
  let hSE := D.fieldInertia_le_frobeniusFixedField KR L hLK σ
  let hSfinite : Finite
      (K.field.toSubgroup ⧸ extensionSubgroup K.field S hSK) :=
    D.frobeniusFixedField_finite KR L hLK σ
  let hSabsolute : Finite ((baseField G).toSubgroup ⧸
      extensionSubgroup (baseField G) S (le_baseField S)) :=
    D.frobeniusFixedField_absoluteFinite K L hLK σ
  let hTabsolute : Finite ((baseField G).toSubgroup ⧸
      extensionSubgroup (baseField G) T (le_baseField T)) :=
    D.frobeniusFixedField_absoluteFinite K L hLK σn
  let hTSfinite : Finite
      (S.toSubgroup ⧸ extensionSubgroup S T hTS) :=
    D.frobeniusPowerFixedField_finite KR L hLK φ hφ n n hn hn
  let hTSnormal : (extensionSubgroup S T hTS).Normal :=
    D.frobeniusPowerFixedField_normal KR L hLK φ hφ n n hn hn
  let : (extensionSubgroup S T hTS).Normal := hTSnormal
  let ambientExtension : FiniteGaloisSubextension KR.field :=
    { field := L
      below := hLK
      normal := hLnormal
      finite := hLfinite }
  let powerTower : DegreeData.FrobeniusPowerFixedFieldTower D :=
    { ambientBase := KR
      ambient := ambientExtension
      frobenius := φ
      exponent_one := hφ
      n := n
      n_pos := hn
      baseAbsoluteFinite := hSabsolute
      fieldAbsoluteFinite := hTabsolute
      relativeFinite := hTSfinite }
  let fixedTower := powerTower.toFrobeniusFixedFieldTower
  let finiteFixedTower :=
    powerTower.toFiniteAmbientFrobeniusFixedFieldTower
  let SF := fixedTower.base
  let TF := fixedTower.field
  let hSMu : S.toSubgroup ≤ Mu.field.toSubgroup := hSP.trans hPMu
  let hSMufinite : Finite
      (Mu.field.toSubgroup ⧸ extensionSubgroup Mu.field S hSMu) :=
    FiniteIntermediateField.finite_extension_of_le hSK Mu.below hSMu
  let : Finite
      ((Mu.toFiniteAbstractField K).field.toSubgroup ⧸
        extensionSubgroup (Mu.toFiniteAbstractField K).field S hSMu) := by
    change Finite
      (Mu.field.toSubgroup ⧸ extensionSubgroup Mu.field S hSMu)
    exact hSMufinite
  let ESMu : FiniteAbstractFieldExtension G :=
    FiniteAbstractFieldExtension.ofInclusion
      S (Mu.toFiniteAbstractField K) hSMu
  have hESMuField : ESMu.field = SF :=
    FiniteAbstractField.eq_of_field_eq _ _ rfl
  let uS : v.unitAddSubgroup SF :=
    hESMuField ▸ v.finiteUnitInclusion ESMu uMu
  let hSMi (j : ιs) : S.toSubgroup ≤ (Mi j).field.toSubgroup :=
    hSP.trans (hPMi j)
  let hSMifinite (j : ιs) : Finite
      ((Mi j).field.toSubgroup ⧸ extensionSubgroup (Mi j).field S (hSMi j)) :=
    FiniteIntermediateField.finite_extension_of_le hSK (Mi j).below (hSMi j)
  let hSMifiniteBundled (j : ιs) : Finite
      (((Mi j).toFiniteAbstractField K).field.toSubgroup ⧸
        extensionSubgroup ((Mi j).toFiniteAbstractField K).field S (hSMi j)) := by
    change Finite
      ((Mi j).field.toSubgroup ⧸
        extensionSubgroup (Mi j).field S (hSMi j))
    exact hSMifinite j
  let ESMi (j : ιs) : FiniteAbstractFieldExtension G :=
    FiniteAbstractFieldExtension.ofInclusion
      S ((Mi j).toFiniteAbstractField K) (hSMi j)
  have hESMiField (j : ιs) : (ESMi j).field = SF :=
    FiniteAbstractField.eq_of_field_eq _ _ rfl
  let uᵢS (j : ιs) : v.unitAddSubgroup SF :=
    hESMiField j ▸ v.finiteUnitInclusion (ESMi j) (uMi j)
  have huSval : uS.1.1 = u.1.1 := by
    have huMuVal := congrArg Subtype.val huMu
    change uMu.1.1 = u.1.1 at huMuVal
    have huStransport : uS.1.1 = uMu.1.1 := by
      dsimp only [uS]
      cases hESMuField
      rfl
    calc
      uS.1.1 = uMu.1.1 := huStransport
      _ = u.1.1 := huMuVal
  have huᵢSval (j : ιs) : (uᵢS j).1.1 = (uᵢ j.1).1.1 := by
    have huMiVal := congrArg Subtype.val (huMi j)
    change (uMi j).1.1 = (uᵢ j.1).1.1 at huMiVal
    have huᵢStransport : (uᵢS j).1.1 = (uMi j).1.1 := by
      dsimp only [uᵢS]
      cases hESMiField j
      rfl
    calc
      (uᵢS j).1.1 = (uMi j).1.1 := huᵢStransport
      _ = (uᵢ j.1).1.1 := huMiVal
  have hstarVal :
      (D.frobeniusQuotientAction A K.field L hLK φ.1 u.1).1 - u.1.1 =
        ∑ i ∈ s,
          ((D.frobeniusQuotientAction A K.field L hLK (τ i).1 (uᵢ i).1).1 -
            (uᵢ i).1.1) := by
    have h := congrArg
      (AddSubgroup.subtype
        (ambientFixedAddSubgroup A (D.maximalUnramifiedField L))) hstar
    rw [map_sub, map_sum] at h
    exact h
  simp_rw [D.frobeniusQuotientAction_coe_out] at hstarVal
  have hstarS :
      A.ρ (Quotient.out φ.1).1 uS.1.1 - uS.1.1 =
        ∑ j : ιs,
          (A.ρ (Quotient.out (τ j.1).1).1 (uᵢS j).1.1 - (uᵢS j).1.1) := by
    rw [huSval]
    calc
      A.ρ (Quotient.out φ.1).1 u.1.1 - u.1.1 =
          ∑ i ∈ s,
            (A.ρ (Quotient.out (τ i).1).1 (uᵢ i).1.1 - (uᵢ i).1.1) := hstarVal
      _ = ∑ j : ιs,
            (A.ρ (Quotient.out (τ j.1).1).1 (uᵢ j.1).1.1 -
              (uᵢ j.1).1.1) :=
        Finset.sum_subtype s (fun _ => Iff.rfl) _
      _ = _ := by simp_rw [huᵢSval]
  let τs : ιs →
      (D.extensionNormalizedDegreeContinuous KR L hLK).toMonoidHom.ker :=
    fun j => τ j.1
  have hφσ : φ.1 * σ.1 = σ.1 * φ.1 :=
    powerTower.frobenius_commute_base
  have hφσn : φ.1 * σn.1 = σn.1 * φ.1 :=
    powerTower.frobenius_commute_field
  have hτσ (j : ιs) : (τs j).1 * (φ.1 ^ n) =
      (φ.1 ^ n) * (τs j).1 := by
    exact (D.quotientPower_card_commutes_degreeZero KR L hLK P hPL
      φ.1 (τs j).1 (τs j).2).symm
  have hτσn (j : ιs) : (τs j).1 * (φ.1 ^ (n * n)) =
      (φ.1 ^ (n * n)) * (τs j).1 := by
    have hcomm : Commute (τs j).1 (φ.1 ^ n) := hτσ j
    simpa only [pow_mul] using (hcomm.pow_right n).eq
  have hσσn : σ.1 * σn.1 = σn.1 * σ.1 :=
    fixedTower.commute
  obtain ⟨uBar, uBarᵢ, yBar, huBar, huBarᵢ, hyBar⟩ :=
    v.universalNormDescent_fixedTower_solution hAxiom powerTower
      (Finset.univ : Finset ιs) τs hτσ hτσn uS uᵢS hstarS
  let uBarE := fixedFieldInclusion A T E hTE uBar.1
  let uBarᵢE := fun j : ιs => fixedFieldInclusion A T E hTE (uBarᵢ j).1
  let yBarE := fixedFieldInclusion A T E hTE yBar.1
  let φnyBarE := D.frobeniusPowerSum A K.field L hLK φ.1 n yBarE
  let w := uBarE - φnyBarE
  have hstarW := v.universalNormDescent_correctedEquation KR L hLK σ σn
    (Finset.univ : Finset ιs) φ.1 hφσn (fun j => (τs j).1) hτσn
      hσσn n rfl uBar uBarᵢ yBar hyBar
  have huBarEmem : uBarE ∈ v.infiniteUnitAddSubgroup E K hEK := by
    let MT := D.frobeniusFixedIntermediateField KR L hLK σn
    have hTFMT : TF = MT.toFiniteAbstractField K :=
      FiniteAbstractField.eq_of_field_eq _ _ rfl
    let uBarMT : v.unitAddSubgroup (MT.toFiniteAbstractField K) :=
      hTFMT ▸ uBar
    refine ⟨MT, uBarMT, ?_⟩
    apply Subtype.ext
    change uBarMT.1.1 = uBar.1.1
    dsimp only [uBarMT]
  have hyBarEmem : yBarE ∈ v.infiniteUnitAddSubgroup E K hEK := by
    let MT := D.frobeniusFixedIntermediateField KR L hLK σn
    have hTFMT : TF = MT.toFiniteAbstractField K :=
      FiniteAbstractField.eq_of_field_eq _ _ rfl
    let yBarMT : v.unitAddSubgroup (MT.toFiniteAbstractField K) :=
      hTFMT ▸ yBar
    refine ⟨MT, yBarMT, ?_⟩
    apply Subtype.ext
    change yBarMT.1.1 = yBar.1.1
    dsimp only [yBarMT]
  have hφnyMem : φnyBarE ∈ v.infiniteUnitAddSubgroup E K hEK :=
    v.frobeniusPowerSum_mem_infiniteUnit_universalNormDescent K L hLK φ.1 n yBarE hyBarEmem
  have hwMem : w ∈ v.infiniteUnitAddSubgroup E K hEK :=
    (v.infiniteUnitAddSubgroup E K hEK).sub_mem huBarEmem hφnyMem
  have hfixedZ := D.maximalUnramifiedNorm_fixed_of_hstar A KR L hLK
    (Finset.univ : Finset ιs) φ.1 τs w uBarᵢE hstarW
  obtain ⟨zK, hzK⟩ :=
    v.descend_maximalUnramifiedNorm_unit K L hLK φ hφ w hwMem hfixedZ
  let powerT : ambientFixedAddSubgroup A T :=
    ∑ i : Fin n, D.frobeniusFixedFieldAction A KR L hLK σn
      (φ.1 ^ i.1) (Commute.pow_left hφσn i.1) yBar.1
  let powerTUnit : v.unitAddSubgroup TF :=
    ∑ i : Fin n, v.frobeniusFixedFieldUnitAction KR L hLK σn
      (φ.1 ^ i.1) (Commute.pow_left hφσn i.1) yBar
  have hsumUnit (f : Fin n → v.unitAddSubgroup TF) :
      ((∑ i, f i).1.1 : A.V) = ∑ i, (f i).1.1 := by
    calc
      ((∑ i, f i).1.1 : A.V) =
          (ambientFixedAddSubgroup A TF.field).subtype
            (∑ i, (v.unitAddSubgroup TF).subtype (f i)) := by
        exact congrArg (ambientFixedAddSubgroup A TF.field).subtype
          (map_sum (v.unitAddSubgroup TF).subtype f Finset.univ)
      _ = _ :=
        map_sum (ambientFixedAddSubgroup A TF.field).subtype
          (fun i => (v.unitAddSubgroup TF).subtype (f i)) Finset.univ
  have hsumAmbient (f : Fin n → ambientFixedAddSubgroup A T) :
      ((∑ i, f i).1 : A.V) = ∑ i, (f i).1 :=
    map_sum (ambientFixedAddSubgroup A T).subtype f Finset.univ
  have hpowerTUnit : powerTUnit.1 = powerT := by
    apply Subtype.ext
    calc
      (powerTUnit.1.1 : A.V) =
          ∑ i : Fin n, (v.frobeniusFixedFieldUnitAction KR L hLK σn
            (φ.1 ^ i.1) (Commute.pow_left hφσn i.1) yBar).1.1 :=
        hsumUnit (fun i : Fin n =>
          v.frobeniusFixedFieldUnitAction KR L hLK σn
            (φ.1 ^ i.1) (Commute.pow_left hφσn i.1) yBar)
      _ = ∑ i : Fin n,
          (D.frobeniusFixedFieldAction A KR L hLK σn
            (φ.1 ^ i.1) (Commute.pow_left hφσn i.1) yBar.1).1 := rfl
      _ = powerT.1 :=
        (hsumAmbient (fun i : Fin n =>
          D.frobeniusFixedFieldAction A KR L hLK σn
            (φ.1 ^ i.1) (Commute.pow_left hφσn i.1) yBar.1)).symm
  let wBar : v.unitAddSubgroup TF := uBar - powerTUnit
  have hwBarIncl : fixedFieldInclusion A T E hTE wBar.1 = w := by
    have hpIncl := D.fixedFieldPowerSum_inclusion A KR L hLK σn
      φ.1 hφσn n yBar.1
    apply Subtype.ext
    have hpVal := congrArg Subtype.val hpIncl
    change uBar.1.1 - powerTUnit.1.1 = uBar.1.1 - φnyBarE.1
    rw [hpowerTUnit]
    exact congrArg (fun z => uBar.1.1 - z) hpVal
  let EST : FiniteAbstractFieldExtension G := fixedTower.extension
  let yS : v.unitAddSubgroup SF := v.finiteUnitNorm EST yBar
  let uSraw : ambientFixedAddSubgroup A S :=
    ⟨uS.1.1, by
      intro g
      have hg : g.1 ∈ SF.field := by
        change g.1 ∈ D.frobeniusFixedField KR L hLK σ
        exact g.2
      exact uS.1.2 ⟨g.1, hg⟩⟩
  let ySraw : ambientFixedAddSubgroup A S :=
    ⟨yS.1.1, by
      intro g
      have hg : g.1 ∈ SF.field := by
        change g.1 ∈ D.frobeniusFixedField KR L hLK σ
        exact g.2
      exact yS.1.2 ⟨g.1, hg⟩⟩
  let uBarraw : ambientFixedAddSubgroup A T :=
    ⟨uBar.1.1, by
      intro g
      have hg : g.1 ∈
          (D.frobeniusFixedAbstractField KR L hLK σn).field := by
        change g.1 ∈ D.frobeniusFixedField KR L hLK σn
        exact g.2
      exact uBar.1.2 ⟨g.1, hg⟩⟩
  let wBarraw : ambientFixedAddSubgroup A T :=
    ⟨wBar.1.1, by
      intro g
      have hg : g.1 ∈ TF.field := by
        change g.1 ∈ D.frobeniusFixedField KR L hLK σn
        exact g.2
      exact wBar.1.2 ⟨g.1, hg⟩⟩
  let powerS : ambientFixedAddSubgroup A S :=
    ∑ i : Fin n, D.frobeniusFixedFieldAction A KR L hLK σ
      (φ.1 ^ i.1) (Commute.pow_left hφσ i.1) ySraw
  have hpowerNorm := D.fixedFieldPowerSum_relativeNorm A KR L hLK
    σ σn hTS φ.1 hφσ hφσn n yBar.1
  have huBarraw : relativeNorm A S T hTS uBarraw = uSraw := by
    apply Subtype.ext
    have h := congrArg Subtype.val huBar
    change
      (relativeNorm A S T hTS uBar.1).1 = uS.1.1 at h
    change
      (relativeNorm A S T hTS uBarraw).1 = uSraw.1
    exact h
  have hySraw : relativeNorm A S T hTS yBar.1 = ySraw := by
    apply Subtype.ext
    rfl
  have hpowerNormRaw : relativeNorm A S T hTS powerT = powerS := by
    simpa [powerT, powerS, S, T, σ, σn, hySraw] using hpowerNorm
  have hwBarNorm : relativeNorm A S T hTS wBarraw = uSraw - powerS := by
    have hwBarCoe : wBarraw = uBarraw - powerT := by
      apply Subtype.ext
      change uBar.1.1 - powerTUnit.1.1 = uBar.1.1 - powerT.1
      exact congrArg (fun z => uBar.1.1 - z)
        (congrArg Subtype.val hpowerTUnit)
    rw [hwBarCoe]
    rw [map_sub, huBarraw]
    exact congrArg (fun z => uSraw - z) hpowerNormRaw
  obtain ⟨gS, hgClosure, _hgDegree, hg⟩ :=
    D.frobeniusPowerFixedField_generator KR L hLK φ hφ n n hn hn
  let fixedGenerator :
      finiteFixedTower.toFrobeniusFixedFieldTower.CyclicGenerator :=
    { element := gS
      mapsToFrobenius := hgClosure
      generates := hg }
  have hcard := D.frobeniusPowerFixedField_quotientCard
    KR L hLK φ hφ n n hn hn
  have hdegree : (finiteFixedTower.extension.degree : ℕ) = n := by
    calc
      (finiteFixedTower.extension.degree : ℕ) =
          Nat.card
            finiteFixedTower.extension.toFiniteAbstractExtension.quotient :=
        finiteFixedTower.extension.toFiniteAbstractExtension.degree_coe
      _ = n := hcard
  have hnormW := v.maximalNorm_relativeNorm_fixedTower
    finiteFixedTower fixedGenerator n hdegree wBar
  have hnormWraw :
      J (N (fixedFieldInclusion A S E hSE
        (relativeNorm A S T hTS wBarraw))) =
      D.frobeniusPowerSum A K.field L hLK σ.1 n
        (J (N (fixedFieldInclusion A T E hTE wBarraw))) := by
    change
      J (N (fixedFieldInclusion A S E hSE
        (relativeNorm A S T hTS wBar.1))) =
      D.frobeniusPowerSum A K.field L hLK σ.1 n
        (J (N (fixedFieldInclusion A T E hTE wBar.1))) at hnormW
    exact hnormW
  have hσfixedZ : D.frobeniusQuotientAction A K.field L hLK σ.1 (J (N w)) =
      J (N w) := by
    let B := D.frobeniusQuotientRepresentation A K.field L hLK
    have hpow := rep_action_pow_fixed
      B φ.1 (J (N w)) hfixedZ n
    change D.frobeniusQuotientAction A K.field L hLK
      (φ.1 ^ n) (J (N w)) = J (N w) at hpow
    simpa only [σ, D.frobeniusPowerOfDegreeOne_coe] using hpow
  have hpowerZ : D.frobeniusPowerSum A K.field L hLK σ.1 n (J (N w)) =
      n • J (N w) :=
    D.frobeniusPowerSum_eq_nsmul_of_fixed A K.field L hLK
      σ.1 n (J (N w)) hσfixedZ
  have hnormW' :
      J (N (fixedFieldInclusion A S E hSE (uSraw - powerS))) =
        n • J (N w) := by
    rw [← hwBarNorm, hnormWraw]
    have hwBarInclRaw : fixedFieldInclusion A T E hTE wBarraw = w := by
      apply Subtype.ext
      exact congrArg Subtype.val hwBarIncl
    rw [hwBarInclRaw, hpowerZ]
  have hpowerSIncl := D.fixedFieldPowerSum_inclusion A KR L hLK σ
    φ.1 hφσ n ySraw
  have huSIncl : fixedFieldInclusion A S E hSE uSraw = u.1 := by
    apply Subtype.ext
    change uSraw.1 = u.1.1
    exact huSval
  have hnormRelationE :
      J (N u.1) =
        J (N (D.frobeniusPowerSum A K.field L hLK φ.1 n
          (fixedFieldInclusion A S E hSE ySraw))) + n • J (N w) := by
    have h := hnormW'
    simp only [map_sub] at h
    rw [huSIncl, hpowerSIncl] at h
    calc
      J (N u.1) = n • J (N w) +
          J (N (D.frobeniusPowerSum A K.field L hLK φ.1 n
            (fixedFieldInclusion A S E hSE ySraw))) :=
        sub_eq_iff_eq_add.mp h
      _ = _ := add_comm _ _
  have hlemma53 := (D.frobeniusNormIdentities A KR L hLK φ σ hφ ySraw).1
  have hbaseRelation :
      aK.1 = relativeNorm A K.field S hSK ySraw + n • zK.1 := by
    apply Subtype.ext
    have haKval := congrArg Subtype.val haK
    have hzKval := congrArg Subtype.val hzK
    have hrelVal := congrArg Subtype.val hnormRelationE
    have h53 := hlemma53
    have h53' :
        (N (D.frobeniusPowerSum A K.field L hLK φ.1 n
          (fixedFieldInclusion A S E hSE ySraw))).1 =
          (relativeNorm A K.field S hSK ySraw).1 := by
      have h53' := h53.symm
      have hσexp : D.frobeniusExponent KR L hLK σ = n :=
        D.frobeniusExponent_powerOfDegreeOne KR L hLK φ hφ n hn
      rw [hσexp] at h53'
      change
        (N (D.frobeniusPowerSum A K.field L hLK φ.1 n
          (fixedFieldInclusion A S E hSE ySraw))).1 =
          (relativeNorm A K.field S hSK ySraw).1 at h53'
      exact h53'
    change aK.1.1 =
      (relativeNorm A K.field S hSK ySraw).1 + n • zK.1.1
    change aK.1.1 = (N u.1).1 at haKval
    change zK.1.1 = (N w).1 at hzKval
    change (N u.1).1 =
      (N (D.frobeniusPowerSum A K.field L hLK φ.1 n
        (fixedFieldInclusion A S E hSE ySraw))).1 + n • (N w).1 at hrelVal
    rw [haKval, hrelVal, ← hzKval]
    rw [h53']
  let hPSfinite : Finite
      (P.field.toSubgroup ⧸ extensionSubgroup P.field S hSP) :=
    FiniteIntermediateField.finite_extension_of_le hSK P.below hSP
  let : Finite
      ((P.toFiniteAbstractField K).field.toSubgroup ⧸
        extensionSubgroup (P.toFiniteAbstractField K).field S hSP) := by
    change Finite
      (P.field.toSubgroup ⧸ extensionSubgroup P.field S hSP)
    exact hPSfinite
  let EPS : FiniteAbstractFieldExtension G :=
    FiniteAbstractFieldExtension.ofInclusion
      S (P.toFiniteAbstractField K) hSP
  let yP : v.unitAddSubgroup (P.toFiniteAbstractField K) := by
    simpa [SF, EPS, FiniteAbstractFieldExtension.ofInclusion,
      DegreeData.frobeniusFixedAbstractField] using
        v.finiteUnitNorm EPS yS
  let EP := P.toFiniteAbstractFieldExtension K
  let zP : v.unitAddSubgroup (P.toFiniteAbstractField K) :=
    v.finiteUnitInclusion EP zK
  let aP : v.unitAddSubgroup (P.toFiniteAbstractField K) := yP + zP
  let FT : DegreeData.FiniteTower G := {
    top := S
    middle := P.field
    base := K.field
    top_le_middle := hSP
    middle_le_base := P.below
    finiteTopQuotient := hPSfinite
    finiteBaseQuotient := P.finite }
  have hnDegree : (EP.degree : ℕ) = n := by
    change (EP.toFiniteAbstractExtension.degree : ℕ) = n
    rw [EP.toFiniteAbstractExtension.degree_coe]
    change
      Nat.card
        (K.field.toSubgroup ⧸ extensionSubgroup K.field P.field P.below) = n
    rfl
  let yPraw : ambientFixedAddSubgroup A P.field :=
    ⟨yP.1.1, by
      intro g
      apply yP.1.2⟩
  let zPraw : ambientFixedAddSubgroup A P.field :=
    ⟨zP.1.1, by
      intro g
      apply zP.1.2⟩
  let aPraw : ambientFixedAddSubgroup A P.field :=
    ⟨aP.1.1, by
      intro g
      apply aP.1.2⟩
  have haPnorm : relativeNorm A K.field P.field P.below aP.1 = aK.1 := by
    change relativeNorm A K.field P.field P.below aPraw = aK.1
    have haPraw : aPraw = yPraw + zPraw := by
      apply Subtype.ext
      rfl
    rw [haPraw, map_add]
    have hyTower := FT.norm_trans_apply A yS.1
    have hzNorm := relativeNorm_fixedFieldInclusion A
      EP.toFiniteAbstractExtension zK.1
    change relativeNorm A K.field P.field P.below
        (fixedFieldInclusion A K.field P.field P.below zK.1) =
      (EP.degree : ℕ) • zK.1 at hzNorm
    change relativeNorm A K.field P.field P.below yPraw +
      relativeNorm A K.field P.field P.below zPraw = aK.1
    change relativeNorm A K.field P.field P.below
        (relativeNorm A P.field S hSP yS.1) +
      relativeNorm A K.field P.field P.below
        (fixedFieldInclusion A K.field P.field P.below zK.1) = aK.1
    rw [hyTower]
    rw [hzNorm, hnDegree]
    exact hbaseRelation.symm
  exact v.mem_finiteIntermediateUnitNormRange_of_overfield
    E K M P hPM aP aK.1 haPnorm

/-- **The universal norm-descent lemma.**  A finite Frobenius coboundary
relation for an infinite-level unit forces its maximal-unramified norm to
descend to a `K`-unit which is a unit norm from every finite intermediate
field. -/
theorem universalNormDescent
    (v : ValuationData D A)
    [IsTopologicalGroup G] [CompactSpace G] [T2Space G]
    [TotallyDisconnectedSpace G]
    (hAxiom : v.SatisfiesUnramifiedUnitCohomology)
    (K : FiniteAbstractField G) (L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.field.toSubgroup)
    [hLnormal : (extensionSubgroup K.field L hLK).Normal]
    [hLfinite : Finite
      (K.field.toSubgroup ⧸ extensionSubgroup K.field L hLK)]
    (φ : D.FrobeniusElements (K.toFiniteResidueAbstractField D) L hLK)
    (hφ : D.frobeniusExponent
      (K.toFiniteResidueAbstractField D) L hLK φ = 1)
    {ι : Type*} (s : Finset ι)
    (τ : ι →
      (D.extensionNormalizedDegreeContinuous
        (K.toFiniteResidueAbstractField D) L hLK).toMonoidHom.ker)
    (u : v.infiniteUnitAddSubgroup (D.maximalUnramifiedField L) K
      (D.maximalUnramifiedField_le_of_le hLK))
    (uᵢ : ι → v.infiniteUnitAddSubgroup (D.maximalUnramifiedField L) K
      (D.maximalUnramifiedField_le_of_le hLK))
    (hstar : D.frobeniusQuotientAction A K.field L hLK φ.1 u.1 - u.1 =
      ∑ i ∈ s,
        (D.frobeniusQuotientAction A K.field L hLK (τ i).1 (uᵢ i).1 -
          (uᵢ i).1)) :
    letI : Finite
        ((D.maximalUnramifiedField K.field).toSubgroup ⧸
          extensionSubgroup (D.maximalUnramifiedField K.field)
            (D.maximalUnramifiedField L)
            (D.maximalUnramifiedField_mono hLK)) :=
      D.maximalUnramifiedExtension_finite K.field L hLK
    ∃ aK : v.unitAddSubgroup K,
      fixedFieldInclusion A K.field (D.maximalUnramifiedField K.field)
          (D.maximalUnramifiedField_le K.field) aK.1 =
        relativeNorm A (D.maximalUnramifiedField K.field)
          (D.maximalUnramifiedField L)
          (D.maximalUnramifiedField_mono hLK) u.1 ∧
      aK.1 ∈ v.infiniteUnitNormSubgroup (D.maximalUnramifiedField L) K := by
  let : Finite
      ((D.maximalUnramifiedField K.field).toSubgroup ⧸
        extensionSubgroup (D.maximalUnramifiedField K.field)
          (D.maximalUnramifiedField L)
          (D.maximalUnramifiedField_mono hLK)) :=
    D.maximalUnramifiedExtension_finite K.field L hLK
  obtain ⟨aK, haK⟩ := v.universalNormDescent_endpoint_descent K L hLK φ hφ
    s τ u uᵢ hstar
  refine ⟨aK, haK, ?_⟩
  rw [v.mem_infiniteUnitNormSubgroup_iff]
  intro M
  exact v.universalNormDescent_mem_finiteUnitNormRange hAxiom K L hLK φ hφ
    s τ u uᵢ hstar aK haK M

end ValuationData

end
end ClassFormation
end

section
-- module Solutions.OAIQ244_DUKE.AbstractClassFieldTheory_Reciprocity_Construction_MainMultiplicativity_ReciprocityMapMul
attribute [-instance] _root_.ClassFormation.FiniteGaloisSubextension.extensionSubgroup_over_intermediate_normalInstance _root_.ClassFormation.FiniteGaloisSubextension.intermediateField_normalInstance _root_.ClassFormation.instIsAddTorsionFreeZHat _root_.ClassFormation.instIsMulTorsionFreeMultiplicativeZHat _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.DiscreteNthRootsSubgroup.instTopologicalSpaceSubtypeUnitsMemSubgroup _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalClassFieldTheory.baseFixingExtensionQuotient_finite _root_.LocalClassFieldTheory.extensionSubgroupBase_normal _root_.LocalClassFieldTheory.finiteGaloisExtensionSubgroupOfEmbedding_normal _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.LubinTate.compatibleGroupFamiliesGroup _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.RamificationTheory.HilbertRamification.ValuationSubring.inertiaGroup_normal _root_.RamificationTheory.HilbertRamification.ValuationSubring.ramificationGroupInInertiaAut_normal _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.maximalIdealPowSuccQuotModule _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen
attribute [-simp] _root_.ClassFormation.DegreeData.finiteReciprocityCandidate_apply _root_.ClassFormation.DegreeData.finiteReciprocityCandidate_zero _root_.ClassFormation.DegreeData.frobeniusLiftDifference_coe _root_.ClassFormation.DegreeData.frobeniusRestriction_chosenFiniteReciprocityFrobeniusLift _root_.ClassFormation.FiniteAbelianSubextension.extensionQuotientMk_apply _root_.ClassFormation.FiniteGaloisSubextension.classFieldCandidate_field _root_.ClassFormation.ValuationData.unramifiedReciprocity_equiv_of_generator_apply _root_.ClassFormation.cyclicNormClassHom_apply _root_.ClassFormation.extensionFixedRepresentationEquiv_apply_coe _root_.ClassFormation.extensionFixedRepresentationEquiv_symm_apply_coe _root_.ClassFormation.mem_normFilterBasis_iff _root_.ClassFormation.toZModPow_zHatToPadicInt _root_.ClassFormation.zHatReductionRingHom_apply _root_.ClassFormation.zHatRingEquivProfiniteIntegerPrimeProduct_apply _root_.ClassFormation.zHatToPadicInt_intCast _root_.ClassFormation.zHatToProfiniteIntegerPrimeProduct_apply _root_.ClassFormation.zHatToProfiniteIntegerPrimeProduct_intCast _root_.ClassFormation.zHatUnitsContinuousMulEquivPrimeProduct_coe_apply _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.IsDiscreteValuationRing.addVal_ringEquiv _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.KummerTheory.torsionQuotientEquivOfZHatMulDecomposition_mk _root_.KummerTheory.zHatUnitsContinuousMulEquivPrimeProduct_rationalCyclotomicCharacter _root_.LocalClassFieldTheory.baseFixingExtensionQuotientEquivAmbient_mk _root_.LocalClassFieldTheory.baseUnitsEquivGaloisAmbientFixed_val _root_.LocalClassFieldTheory.embeddedFieldUnitsEquivGaloisFixed_coe _root_.LocalClassFieldTheory.finiteGaloisUnitsEquivAbstractFixedOfEmbedding_coe _root_.LocalClassFieldTheory.finiteGaloisUnitsEquivAbstractFixed_coe _root_.LocalClassFieldTheory.finiteResidueFrobeniusFromZHat_apply _root_.LocalClassFieldTheory.finiteResidueFrobeniusFromZHat_one _root_.LocalClassFieldTheory.intermediateFieldUnitsEquivGaloisFixed_coe _root_.LocalClassFieldTheory.intrinsicFiniteAbstractBase_eq_base _root_.LocalClassFieldTheory.residueAbsoluteDegreeIn_frobenius _root_.LocalClassFieldTheory.residueAbsoluteFrobenius_one _root_.LocalClassFieldTheory.residueFrobeniusToLimit_apply_component _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.LocalFieldTheory.residueField_algebraMap_residue _root_.OAI.PrimeDegreePackets.ThetaConstruction.schwartzCM_apply _root_.infinitePlace_mult_smul
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

/-!
# Multiplicativity of the abstract reciprocity map

This file assembles the Frobenius conjugation, finite-stage unit, correction
sum, and universal norm-descent results into reciprocity-map multiplicativity.
-/

universe u

namespace ClassFormation

open KummerTheory
open CyclicCohomology

noncomputable section

open CategoryTheory
open scoped BigOperators

section reciprocityMapMultiplicativity

/-!
Mathlib's `Rep ℤ G` requires its coefficient ring and acting group in the
same universe, so this representation-bearing portion has `G : IntegralRepGroupType`.
-/
variable {G : IntegralRepGroupType} [Group G] [TopologicalSpace G]

namespace DegreeData

/-- **reciprocity multiplicativity.** The reciprocity function is multiplicative on
Frobenius elements (written additively on the norm-class quotient).

This is the endpoint of the calculation: the
group-ring identity `(*)` supplies the hypothesis of the universal norm-descent lemma, whose
universal-unit norm descends the resulting norm relation to `K`. -/
theorem reciprocityMap_mul
    (D : DegreeData G) (A : Rep ℤ G) (v : ValuationData D A)
    [IsTopologicalGroup G] [CompactSpace G] [T2Space G]
    [TotallyDisconnectedSpace G]
    (hAxiom : v.SatisfiesUnramifiedUnitCohomology D)
    (K : FiniteAbstractField G) (L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.field.toSubgroup)
    [hLnormal : (extensionSubgroup K.field L hLK).Normal]
    [hLfinite : Finite (K.field.toSubgroup ⧸ extensionSubgroup K.field L hLK)]
    (sigma1 sigma2 : D.FrobeniusElements
      (K.toFiniteResidueAbstractField D) L hLK) :
    D.reciprocityMap A v K L hLK (sigma1 * sigma2) =
      D.reciprocityMap A v K L hLK sigma1 +
        D.reciprocityMap A v K L hLK sigma2 := by
  let KR := K.toFiniteResidueAbstractField D
  let hLnormalKR : (extensionSubgroup KR.field L hLK).Normal := by
    simpa only [KR, FiniteAbstractField.toFiniteResidueAbstractField] using hLnormal
  let hLfiniteKR : Finite
      (KR.field.toSubgroup ⧸ extensionSubgroup KR.field L hLK) := by
    simpa only [KR, FiniteAbstractField.toFiniteResidueAbstractField] using hLfinite
  let phi := D.chosenDegreeOneFrobeniusElement KR L hLK
  have hphi : D.frobeniusExponent KR L hLK phi = 1 :=
    D.frobeniusExponent_chosenDegreeOneFrobeniusElement KR L hLK
  let sigma3 := sigma1 * sigma2
  let m := D.frobeniusExponent KR L hLK sigma1
  let sigma4 := D.frobeniusActionConjugate KR L hLK phi sigma2 m
  let S1 := D.frobeniusFixedField KR L hLK sigma1
  let S2 := D.frobeniusFixedField KR L hLK sigma2
  let S3 := D.frobeniusFixedField KR L hLK sigma3
  let S4 := D.frobeniusFixedField KR L hLK sigma4
  let hS1K := D.frobeniusFixedField_le KR L hLK sigma1
  let hS2K := D.frobeniusFixedField_le KR L hLK sigma2
  let hS3K := D.frobeniusFixedField_le KR L hLK sigma3
  let hS4K := D.frobeniusFixedField_le KR L hLK sigma4
  let hS1finite : Finite
      (K.field.toSubgroup ⧸ extensionSubgroup K.field S1 hS1K) :=
    D.frobeniusFixedField_finite KR L hLK sigma1
  let hS2finite : Finite
      (K.field.toSubgroup ⧸ extensionSubgroup K.field S2 hS2K) :=
    D.frobeniusFixedField_finite KR L hLK sigma2
  let hS3finite : Finite
      (K.field.toSubgroup ⧸ extensionSubgroup K.field S3 hS3K) :=
    D.frobeniusFixedField_finite KR L hLK sigma3
  let hS4finite : Finite
      (K.field.toSubgroup ⧸ extensionSubgroup K.field S4 hS4K) :=
    D.frobeniusFixedField_finite KR L hLK sigma4
  let hS1absolute : Finite ((baseField G).toSubgroup ⧸
      extensionSubgroup (baseField G) S1 (le_baseField S1)) :=
    D.frobeniusFixedField_absoluteFinite K L hLK sigma1
  let hS2absolute : Finite ((baseField G).toSubgroup ⧸
      extensionSubgroup (baseField G) S2 (le_baseField S2)) :=
    D.frobeniusFixedField_absoluteFinite K L hLK sigma2
  let hS3absolute : Finite ((baseField G).toSubgroup ⧸
      extensionSubgroup (baseField G) S3 (le_baseField S3)) :=
    D.frobeniusFixedField_absoluteFinite K L hLK sigma3
  let hS4absolute : Finite ((baseField G).toSubgroup ⧸
      extensionSubgroup (baseField G) S4 (le_baseField S4)) :=
    D.frobeniusFixedField_absoluteFinite K L hLK sigma4
  let Sigma1 : FiniteAbstractField G := ⟨S1, hS1absolute⟩
  let Sigma2 : FiniteAbstractField G := ⟨S2, hS2absolute⟩
  let Sigma3 : FiniteAbstractField G := ⟨S3, hS3absolute⟩
  let pi1 : ambientFixedAddSubgroup A S1 := by
    simpa [Sigma1] using v.chosenPrimeElement Sigma1
  let pi2 : ambientFixedAddSubgroup A S2 := by
    simpa [Sigma2] using v.chosenPrimeElement Sigma2
  let pi3 : ambientFixedAddSubgroup A S3 := by
    simpa [Sigma3] using v.chosenPrimeElement Sigma3
  have hpi1 : v.IsPrimeElement Sigma1 pi1 := by
    simpa [Sigma1, pi1] using v.chosenPrimeElement_isPrime Sigma1
  have hpi2 : v.IsPrimeElement Sigma2 pi2 := by
    simpa [Sigma2, pi2] using v.chosenPrimeElement_isPrime Sigma2
  have hpi3 : v.IsPrimeElement Sigma3 pi3 := by
    simpa [Sigma3, pi3] using v.chosenPrimeElement_isPrime Sigma3
  obtain ⟨pi4, hpi4, hnorm42⟩ :=
    D.exists_primeElement_frobeniusActionConjugate_norm_eq A v K L hLK
      phi sigma2 m pi2 hpi2
  let E := D.maximalUnramifiedField L
  let I := D.maximalUnramifiedField KR.field
  let hEI := D.maximalUnramifiedField_mono hLK
  let p1 := fixedFieldInclusion A S1 E
    (D.fieldInertia_le_frobeniusFixedField KR L hLK sigma1) pi1
  let p3 := fixedFieldInclusion A S3 E
    (D.fieldInertia_le_frobeniusFixedField KR L hLK sigma3) pi3
  let p4 := fixedFieldInclusion A S4 E
    (D.fieldInertia_le_frobeniusFixedField KR L hLK sigma4) pi4
  let u := D.frobeniusPowerSum A KR.field L hLK phi.1
        (D.frobeniusExponent KR L hLK sigma4) p4 +
      D.frobeniusPowerSum A KR.field L hLK phi.1
        (D.frobeniusExponent KR L hLK sigma1) p1 -
      D.frobeniusPowerSum A KR.field L hLK phi.1
        (D.frobeniusExponent KR L hLK sigma3) p3
  let tau1 := D.frobeniusActionRemainder KR L hLK phi sigma1
  let tau4 := D.frobeniusActionRemainder KR L hLK phi sigma4
  let B := D.frobeniusQuotientRepresentation A KR.field L hLK
  let correction : Fin 3 → ambientFixedAddSubgroup A E :=
    frobeniusMultiplicativityCorrectionTerm B tau1 p1 p3 p4
  have hcorrectionMem : ∀ i : Fin 3,
      correction i ∈ v.infiniteUnitAddSubgroup E K
        (D.maximalUnramifiedField_le_of_le hLK) := by
    have hmem :=
      D.frobeniusCorrectionTerms_mem_infiniteUnitAddSubgroup
        A v K L hLK phi sigma1 sigma2 pi1 pi3 pi4 hpi1 hpi3 hpi4
    change ∀ i : Fin 3,
      (![p4 - p3, p1 - p3,
          p3 - D.frobeniusQuotientAction A KR.field L hLK tau1 p3] :
        Fin 3 → ambientFixedAddSubgroup A E) i ∈
          v.infiniteUnitAddSubgroup E K
            (D.maximalUnramifiedField_le_of_le hLK)
    change ∀ i : Fin 3,
      (![p4 - p3, p1 - p3,
          p3 - D.frobeniusQuotientAction A KR.field L hLK tau1 p3] :
        Fin 3 → ambientFixedAddSubgroup A E) i ∈
          v.infiniteUnitAddSubgroup E K
            (D.maximalUnramifiedField_le_of_le hLK) at hmem
    exact hmem
  have huMem : u ∈ v.infiniteUnitAddSubgroup E K
      (D.maximalUnramifiedField_le_of_le hLK) := by
    simpa [u, p1, p3, p4, E, S1, S3, S4, sigma3, sigma4, m,
      pi1, pi3] using
      D.frobeniusPowerSum_alternating_mem_infiniteUnitAddSubgroup
        A v K L hLK phi sigma1 sigma2 pi1 pi3 pi4 hpi1 hpi3 hpi4
  have hactionMem :=
    D.frobeniusMultiplicativityCorrectionAction_mem_degreeKernel
      KR L hLK phi sigma1 sigma2 hphi
  let tau : Fin 3 →
      (D.extensionNormalizedDegreeContinuous KR L hLK).toMonoidHom.ker :=
    fun i ↦ ⟨frobeniusMultiplicativityCorrectionAction tau1 tau4 i, by
      simpa [tau1, tau4, sigma4, m] using hactionMem i⟩
  let uU : v.infiniteUnitAddSubgroup E K
      (D.maximalUnramifiedField_le_of_le hLK) := ⟨u, huMem⟩
  let uiU : Fin 3 → v.infiniteUnitAddSubgroup E K
      (D.maximalUnramifiedField_le_of_le hLK) :=
    fun i ↦ ⟨correction i, hcorrectionMem i⟩
  have hraw := D.frobeniusPowerSum_mul_action_sub A KR L hLK
    phi sigma1 sigma2 pi1 pi3 pi4
  have hdiff :=
    frobeniusMultiplicativity_actionDifference_eq_correctionSum
      B tau1 tau4 p1 p3 p4
  change
      (D.frobeniusQuotientAction A KR.field L hLK tau4 p4 - p4) +
          (D.frobeniusQuotientAction A KR.field L hLK tau1 p1 - p1) +
        (p3 - D.frobeniusQuotientAction A KR.field L hLK (tau4 * tau1) p3) =
      ∑ i : Fin 3,
        (D.frobeniusQuotientAction A KR.field L hLK
            (frobeniusMultiplicativityCorrectionAction tau1 tau4 i)
            (correction i) - correction i) at hdiff
  have hstar :
      D.frobeniusQuotientAction A KR.field L hLK phi.1 uU.1 - uU.1 =
        ∑ i ∈ (Finset.univ : Finset (Fin 3)),
          (D.frobeniusQuotientAction A KR.field L hLK (tau i).1 (uiU i).1 -
            (uiU i).1) := by
    change D.frobeniusQuotientAction A KR.field L hLK phi.1 u - u = _
    rw [show D.frobeniusQuotientAction A KR.field L hLK phi.1 u - u =
      (D.frobeniusQuotientAction A KR.field L hLK tau4 p4 - p4) +
      (D.frobeniusQuotientAction A KR.field L hLK tau1 p1 - p1) +
      (p3 - D.frobeniusQuotientAction A KR.field L hLK (tau4 * tau1) p3) by
        simpa [u, p1, p3, p4, tau1, tau4, sigma3, sigma4, m,
          E, S1, S3, S4, pi1, pi3] using hraw]
    simpa only [tau, uiU, correction, B,
      D.frobeniusQuotientRepresentation_apply] using hdiff
  let hIfinite : Finite
      (I.toSubgroup ⧸ extensionSubgroup I E hEI) :=
    D.maximalUnramifiedExtension_finite KR.field L hLK
  obtain ⟨aK, haKdescend, haKunitNorm⟩ :=
    v.universalNormDescent hAxiom K L hLK phi hphi
      (Finset.univ : Finset (Fin 3)) tau uU uiU hstar
  have haKnormRaw : aK.1 ∈ infiniteNormSubgroup A E K.field :=
    v.infiniteUnitNormSubgroup_le_normSubgroup E K haKunitNorm
  let r1 := relativeNorm A K.field S1 hS1K pi1
  let r2 := relativeNorm A K.field S2 hS2K pi2
  let r3 := relativeNorm A K.field S3 hS3K pi3
  let r4 := relativeNorm A K.field S4 hS4K pi4
  have hnormu := D.relativeNorm_frobeniusPowerSum_alternating A KR L hLK
    phi sigma1 sigma2 hphi pi1 pi3 pi4
  have hclasses41 :
      D.maximalUnramifiedNormClass A K.field L r4 +
        D.maximalUnramifiedNormClass A K.field L r1 =
          D.maximalUnramifiedNormClass A K.field L r3 := by
    apply D.maximalUnramifiedNormClass_add_eq_of_relativeNorm A KR L hLK
      r4 r1 r3 u hnormu
    refine ⟨aK.1, haKdescend, ?_⟩
    exact (D.mem_maximalUnramifiedNormSubgroup_iff A K.field L aK.1).2 (by
      simpa only [E] using haKnormRaw)
  have hclasses12 :
      D.maximalUnramifiedNormClass A K.field L r1 +
        D.maximalUnramifiedNormClass A K.field L r2 =
          D.maximalUnramifiedNormClass A K.field L r3 := by
    have hr42 : r4 = r2 := by
      simpa [r4, r2, S4, S2, sigma4, m] using hnorm42
    rw [← hr42, add_comm]
    exact hclasses41
  apply D.reciprocityMap_mul_of_primeNormClass_eq
    A v hAxiom K L hLK sigma1 sigma2 pi1 pi2 pi3
      hpi1 hpi2 hpi3
  simpa [r1, r2, r3, E, S1, S2, S3, sigma3, pi1, pi2, pi3]
    using hclasses12

end DegreeData
end reciprocityMapMultiplicativity

end

end ClassFormation
end

section
-- module Solutions.OAIQ244_DUKE.AbstractClassFieldTheory_Reciprocity_Construction_MainFiniteReciprocity
attribute [-instance] _root_.ClassFormation.FiniteGaloisSubextension.extensionSubgroup_over_intermediate_normalInstance _root_.ClassFormation.FiniteGaloisSubextension.intermediateField_normalInstance _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.KummerTheory.finite_finsupp_nsmulQuotient _root_.LocalClassFieldTheory.baseFixingExtensionQuotient_finite _root_.LocalClassFieldTheory.extensionSubgroupBase_normal _root_.LocalClassFieldTheory.finiteGaloisExtensionSubgroupOfEmbedding_normal _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitQuotientCarrier_finite _root_.LocalFieldTheory.DiscreteValuationField.finite_padicInt_finPi_nsmulQuotient _root_.LocalFieldTheory.DiscreteValuationField.finite_padicInt_pi_nsmulQuotient_of_coprime _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_multiplicative_nthPowerQuotient _root_.LocalFieldTheory.finite_nsmulAddQuotient_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.LubinTate.compatibleGroupFamiliesGroup _root_.OAI.PrimeDegreePackets.boundedRealFields_finite _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.RamificationTheory.HilbertRamification.ValuationSubring.inertiaGroup_normal _root_.RamificationTheory.HilbertRamification.ValuationSubring.ramificationGroupInInertiaAut_normal _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen
attribute [-simp] _root_.ClassFormation.FiniteAbelianSubextension.extensionQuotientMk_apply _root_.ClassFormation.FiniteGaloisSubextension.classFieldCandidate_field _root_.ClassFormation.cyclicNormClassHom_apply _root_.ClassFormation.extensionFixedRepresentationEquiv_apply_coe _root_.ClassFormation.extensionFixedRepresentationEquiv_symm_apply_coe _root_.ClassFormation.mem_normFilterBasis_iff _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.IsDiscreteValuationRing.addVal_ringEquiv _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.LocalClassFieldTheory.baseFixingExtensionQuotientEquivAmbient_mk _root_.LocalClassFieldTheory.baseUnitsEquivGaloisAmbientFixed_val _root_.LocalClassFieldTheory.embeddedFieldUnitsEquivGaloisFixed_coe _root_.LocalClassFieldTheory.finiteGaloisUnitsEquivAbstractFixedOfEmbedding_coe _root_.LocalClassFieldTheory.finiteGaloisUnitsEquivAbstractFixed_coe _root_.LocalClassFieldTheory.intermediateFieldUnitsEquivGaloisFixed_coe _root_.LocalClassFieldTheory.intrinsicFiniteAbstractBase_eq_base _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.LocalFieldTheory.residueField_algebraMap_residue _root_.OAI.PrimeDegreePackets.ThetaConstruction.schwartzCM_apply _root_.infinitePlace_mult_smul
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

universe u

namespace ClassFormation

open KummerTheory

open CyclicCohomology

open CategoryTheory
open scoped BigOperators


/-!
# The abstract reciprocity construction, the finite reciprocity equivalence

This file carries out the descent preparation.  The reciprocity
value on the Frobenius semigroup is first mapped to the finite norm quotient.
We then compare two lifts by their positive Frobenius exponents, construct
the degree-zero quotient between unequal lifts, and prove that this quotient
has zero finite reciprocity value.  Finally reciprocity multiplicativity supplies
additivity on the Frobenius semigroup, so the lift supplied by the finite degree-quotient decomposition descends to the additive reciprocity homomorphism of the finite reciprocity equivalence.
-/

noncomputable section

section finiteReciprocityValues

/-! Mathlib's `Rep ℤ G` forces its representation-bearing group `G` to `Type 0`. -/
variable {G : IntegralRepGroupType} [Group G] [TopologicalSpace G]

namespace DegreeData

/-- reciprocity multiplicativity remains additive after passage from the universal norm
quotient to the finite quotient by `N_{L/K} A_L`. -/
theorem finiteReciprocityValue_mul
    (D : DegreeData G) (A : Rep ℤ G) (v : ValuationData D A)
    [IsTopologicalGroup G] [CompactSpace G] [T2Space G]
    [TotallyDisconnectedSpace G]
    (hAxiom : v.SatisfiesUnramifiedUnitCohomology D)
    (K : FiniteAbstractField G) (L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.field.toSubgroup)
    [hLnormal : (extensionSubgroup K.field L hLK).Normal]
    [hLfinite : Finite
      (K.field.toSubgroup ⧸ extensionSubgroup K.field L hLK)]
    (α β : D.FrobeniusElements (K.toFiniteResidueAbstractField D) L hLK) :
    D.finiteReciprocityValue A v K L hLK (α * β) =
      D.finiteReciprocityValue A v K L hLK α +
        D.finiteReciprocityValue A v K L hLK β := by
  unfold finiteReciprocityValue
  rw [D.reciprocityMap_mul A v hAxiom K L hLK α β]
  exact map_add
    (D.maximalUnramifiedToFiniteNormQuotient A K.field L hLK) _ _

end DegreeData

end finiteReciprocityValues

section liftComparison

/-! Mathlib's `Rep ℤ G` forces its representation-bearing group `G` to `Type 0`. -/
variable {G : IntegralRepGroupType} [Group G] [TopologicalSpace G]

namespace DegreeData

/-- The complete degree comparison. Two lifts of the same
finite automorphism are either equal, or the larger-degree lift is the
smaller one times a positive Frobenius lift which restricts trivially and
therefore has zero value in the finite norm quotient. -/
theorem finiteReciprocityHom_lift_comparison
    (D : DegreeData G) (A : Rep ℤ G) (v : ValuationData D A)
    [IsTopologicalGroup G] [CompactSpace G] [T2Space G]
    (K : FiniteAbstractField G) (L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.field.toSubgroup)
    [hLnormal : (extensionSubgroup K.field L hLK).Normal]
    [hLfinite : Finite
      (K.field.toSubgroup ⧸ extensionSubgroup K.field L hLK)]
    (σ τ : D.FrobeniusElements (K.toFiniteResidueAbstractField D) L hLK)
    (hRestriction : D.frobeniusRestriction
      (K.toFiniteResidueAbstractField D) L hLK σ =
      D.frobeniusRestriction
      (K.toFiniteResidueAbstractField D) L hLK τ) :
    σ = τ ∨
      (∃ ι : D.FrobeniusElements (K.toFiniteResidueAbstractField D) L hLK,
        τ = σ * ι ∧
        D.frobeniusRestriction
      (K.toFiniteResidueAbstractField D) L hLK ι = 1 ∧
        D.finiteReciprocityValue A v K L hLK ι = 0) ∨
      (∃ ι : D.FrobeniusElements (K.toFiniteResidueAbstractField D) L hLK,
        σ = τ * ι ∧
        D.frobeniusRestriction
      (K.toFiniteResidueAbstractField D) L hLK ι = 1 ∧
        D.finiteReciprocityValue A v K L hLK ι = 0) := by
  let KR := K.toFiniteResidueAbstractField D
  let hLnormalKR : (extensionSubgroup KR.field L hLK).Normal := by
    simpa only [KR, FiniteAbstractField.toFiniteResidueAbstractField] using hLnormal
  rcases lt_trichotomy
      (D.frobeniusExponent KR L hLK σ)
      (D.frobeniusExponent KR L hLK τ) with hlt | heq | hgt
  · right
    left
    let ι := D.frobeniusLiftDifference KR L hLK σ τ hlt
    refine ⟨ι, ?_, ?_, ?_⟩
    · exact (D.mul_frobeniusLiftDifference KR L hLK σ τ hlt).symm
    · exact D.frobeniusRestriction_frobeniusLiftDifference
        KR L hLK σ τ hRestriction hlt
    · exact D.finiteReciprocityValue_eq_zero_of_restriction_eq_one
        A v K L hLK ι
        (D.frobeniusRestriction_frobeniusLiftDifference
          KR L hLK σ τ hRestriction hlt)
  · left
    exact D.frobenius_eq_of_restriction_eq_of_exponent_eq
      KR L hLK hRestriction heq
  · right
    right
    let ι := D.frobeniusLiftDifference KR L hLK τ σ hgt
    refine ⟨ι, ?_, ?_, ?_⟩
    · exact (D.mul_frobeniusLiftDifference KR L hLK τ σ hgt).symm
    · exact D.frobeniusRestriction_frobeniusLiftDifference
        KR L hLK τ σ hRestriction.symm hgt
    · exact D.finiteReciprocityValue_eq_zero_of_restriction_eq_one
        A v K L hLK ι
        (D.frobeniusRestriction_frobeniusLiftDifference
          KR L hLK τ σ hRestriction.symm hgt)

end DegreeData

end liftComparison

section finiteReciprocityHom

/-! Mathlib's `Rep ℤ G` forces its representation-bearing group `G` to `Type 0`. -/
variable {G : IntegralRepGroupType} [Group G] [TopologicalSpace G]

namespace DegreeData

/-- Once reciprocity multiplicativity supplies additivity on the Frobenius semigroup,
the degree comparison proves that the finite reciprocity value is
independent of the chosen lift.  This is the full three-case argument. -/
theorem finiteReciprocityValue_eq_of_same_restriction_of_mul
    (D : DegreeData G) (A : Rep ℤ G) (v : ValuationData D A)
    [IsTopologicalGroup G] [CompactSpace G] [T2Space G]
    (K : FiniteAbstractField G) (L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.field.toSubgroup)
    [hLnormal : (extensionSubgroup K.field L hLK).Normal]
    [hLfinite : Finite
      (K.field.toSubgroup ⧸ extensionSubgroup K.field L hLK)]
    (hmul : ∀ α β : D.FrobeniusElements
        (K.toFiniteResidueAbstractField D) L hLK,
      D.finiteReciprocityValue A v K L hLK (α * β) =
        D.finiteReciprocityValue A v K L hLK α +
          D.finiteReciprocityValue A v K L hLK β)
    (σ τ : D.FrobeniusElements (K.toFiniteResidueAbstractField D) L hLK)
    (hRestriction : D.frobeniusRestriction
      (K.toFiniteResidueAbstractField D) L hLK σ =
      D.frobeniusRestriction
      (K.toFiniteResidueAbstractField D) L hLK τ) :
    D.finiteReciprocityValue A v K L hLK σ =
      D.finiteReciprocityValue A v K L hLK τ := by
  rcases D.finiteReciprocityHom_lift_comparison A v K L hLK
      σ τ hRestriction with h | h | h
  · rw [h]
  · rcases h with ⟨ι, hτ, _, hι⟩
    rw [hτ, hmul, hι, add_zero]
  · rcases h with ⟨ι, hσ, _, hι⟩
    rw [hσ, hmul, hι, add_zero]

/-- The finite degree-quotient decomposition candidate is additive as soon as reciprocity multiplicativity
is available.  Lift-independence is invoked for the chosen lift of a
product and the product of the two chosen lifts. -/
theorem finiteReciprocityCandidate_add_of_mul
    (D : DegreeData G) (A : Rep ℤ G) (v : ValuationData D A)
    [IsTopologicalGroup G] [CompactSpace G] [T2Space G]
    (K : FiniteAbstractField G) (L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.field.toSubgroup)
    [hLnormal : (extensionSubgroup K.field L hLK).Normal]
    [hLfinite : Finite
      (K.field.toSubgroup ⧸ extensionSubgroup K.field L hLK)]
    (hmul : ∀ α β : D.FrobeniusElements
        (K.toFiniteResidueAbstractField D) L hLK,
      D.finiteReciprocityValue A v K L hLK (α * β) =
        D.finiteReciprocityValue A v K L hLK α +
          D.finiteReciprocityValue A v K L hLK β)
    (q r : Additive
      (K.field.toSubgroup ⧸ extensionSubgroup K.field L hLK)) :
    D.finiteReciprocityCandidate A v K L hLK (q + r) =
      D.finiteReciprocityCandidate A v K L hLK q +
        D.finiteReciprocityCandidate A v K L hLK r := by
  let KR := K.toFiniteResidueAbstractField D
  let hLnormalKR : (extensionSubgroup KR.field L hLK).Normal := by
    simpa only [KR, FiniteAbstractField.toFiniteResidueAbstractField] using hLnormal
  let σ₁ := D.chosenFiniteReciprocityFrobeniusLift KR L hLK q.toMul
  let σ₂ := D.chosenFiniteReciprocityFrobeniusLift KR L hLK r.toMul
  let σ₃ := D.chosenFiniteReciprocityFrobeniusLift KR L hLK (q + r).toMul
  change D.finiteReciprocityValue A v K L hLK σ₃ =
    D.finiteReciprocityValue A v K L hLK σ₁ +
      D.finiteReciprocityValue A v K L hLK σ₂
  have hRestriction :
      D.frobeniusRestriction KR L hLK σ₃ =
        D.frobeniusRestriction KR L hLK (σ₁ * σ₂) := by
    dsimp [σ₁, σ₂, σ₃]
    rw [D.frobeniusRestriction_chosenFiniteReciprocityFrobeniusLift,
      D.frobeniusRestriction_mul,
      D.frobeniusRestriction_chosenFiniteReciprocityFrobeniusLift,
      D.frobeniusRestriction_chosenFiniteReciprocityFrobeniusLift]
  calc
    D.finiteReciprocityValue A v K L hLK σ₃ =
        D.finiteReciprocityValue A v K L hLK (σ₁ * σ₂) :=
      D.finiteReciprocityValue_eq_of_same_restriction_of_mul
        A v K L hLK hmul σ₃ (σ₁ * σ₂) hRestriction
    _ = D.finiteReciprocityValue A v K L hLK σ₁ +
        D.finiteReciprocityValue A v K L hLK σ₂ := hmul σ₁ σ₂

/-- The finite reciprocity equivalence with the semigroup-additivity input isolated.  The
final theorem discharges this input directly from reciprocity multiplicativity. -/
def finiteReciprocityHom_of_mul
    (D : DegreeData G) (A : Rep ℤ G) (v : ValuationData D A)
    [IsTopologicalGroup G] [CompactSpace G] [T2Space G]
    (K : FiniteAbstractField G) (L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.field.toSubgroup)
    [hLnormal : (extensionSubgroup K.field L hLK).Normal]
    [hLfinite : Finite
      (K.field.toSubgroup ⧸ extensionSubgroup K.field L hLK)]
    (hmul : ∀ α β : D.FrobeniusElements
        (K.toFiniteResidueAbstractField D) L hLK,
      D.finiteReciprocityValue A v K L hLK (α * β) =
        D.finiteReciprocityValue A v K L hLK α +
          D.finiteReciprocityValue A v K L hLK β) :
    Additive (K.field.toSubgroup ⧸ extensionSubgroup K.field L hLK) →+
      FiniteNormQuotient A K.field L hLK where
  toFun := D.finiteReciprocityCandidate A v K L hLK
  map_zero' := D.finiteReciprocityCandidate_zero A v K L hLK
  map_add' := D.finiteReciprocityCandidate_add_of_mul
    A v K L hLK hmul

/-- Evaluation of the conditional finite reciprocity homomorphism using any
Frobenius lift of the specified finite automorphism. -/
theorem finiteReciprocityHom_of_mul_apply_of_frobeniusLift
    (D : DegreeData G) (A : Rep ℤ G) (v : ValuationData D A)
    [IsTopologicalGroup G] [CompactSpace G] [T2Space G]
    (K : FiniteAbstractField G) (L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.field.toSubgroup)
    [hLnormal : (extensionSubgroup K.field L hLK).Normal]
    [hLfinite : Finite
      (K.field.toSubgroup ⧸ extensionSubgroup K.field L hLK)]
    (hmul : ∀ α β : D.FrobeniusElements
        (K.toFiniteResidueAbstractField D) L hLK,
      D.finiteReciprocityValue A v K L hLK (α * β) =
        D.finiteReciprocityValue A v K L hLK α +
          D.finiteReciprocityValue A v K L hLK β)
    (q : Additive
      (K.field.toSubgroup ⧸ extensionSubgroup K.field L hLK))
    (σ : D.FrobeniusElements (K.toFiniteResidueAbstractField D) L hLK)
    (hσ : D.frobeniusRestriction
      (K.toFiniteResidueAbstractField D) L hLK σ = q.toMul) :
    D.finiteReciprocityHom_of_mul A v K L hLK hmul q =
      D.finiteReciprocityValue A v K L hLK σ := by
  change D.finiteReciprocityValue A v K L hLK
      (D.chosenFiniteReciprocityFrobeniusLift
        (K.toFiniteResidueAbstractField D) L hLK q.toMul) =
    D.finiteReciprocityValue A v K L hLK σ
  apply D.finiteReciprocityValue_eq_of_same_restriction_of_mul
    A v K L hLK hmul
  rw [D.frobeniusRestriction_chosenFiniteReciprocityFrobeniusLift, hσ]

/-- Prime-norm formula for the conditional finite reciprocity equivalence map, using
an arbitrary Frobenius lift and an arbitrary prime of its fixed field. -/
theorem finiteReciprocityHom_of_mul_apply_eq_primeNormClass
    (D : DegreeData G) (A : Rep ℤ G) (v : ValuationData D A)
    [IsTopologicalGroup G] [CompactSpace G] [T2Space G]
    [TotallyDisconnectedSpace G]
    (hAxiom : v.SatisfiesUnramifiedUnitCohomology D)
    (K : FiniteAbstractField G) (L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.field.toSubgroup)
    [hLnormal : (extensionSubgroup K.field L hLK).Normal]
    [hLfinite : Finite
      (K.field.toSubgroup ⧸ extensionSubgroup K.field L hLK)]
    (hmul : ∀ α β : D.FrobeniusElements
        (K.toFiniteResidueAbstractField D) L hLK,
      D.finiteReciprocityValue A v K L hLK (α * β) =
        D.finiteReciprocityValue A v K L hLK α +
          D.finiteReciprocityValue A v K L hLK β)
    (q : Additive
      (K.field.toSubgroup ⧸ extensionSubgroup K.field L hLK))
    (σ : D.FrobeniusElements (K.toFiniteResidueAbstractField D) L hLK)
    (hσ : D.frobeniusRestriction
      (K.toFiniteResidueAbstractField D) L hLK σ = q.toMul)
    (π : ambientFixedAddSubgroup A
      (D.frobeniusFixedField (K.toFiniteResidueAbstractField D) L hLK σ))
    (hπ :
      let Sigma : FiniteAbstractField G :=
        { field := D.frobeniusFixedField
            (K.toFiniteResidueAbstractField D) L hLK σ
          finite := D.frobeniusFixedField_absoluteFinite K L hLK σ }
      v.IsPrimeElement Sigma π) :
    let KR := K.toFiniteResidueAbstractField D
    let S := D.frobeniusFixedField KR L hLK σ
    let hSK := D.frobeniusFixedField_le KR L hLK σ
    letI : Finite
        (K.field.toSubgroup ⧸ extensionSubgroup K.field S hSK) :=
      D.frobeniusFixedField_finite KR L hLK σ
    D.finiteReciprocityHom_of_mul A v K L hLK hmul q =
      finiteNormClass A K.field L hLK
        (relativeNorm A K.field S hSK π) := by
  dsimp only
  rw [D.finiteReciprocityHom_of_mul_apply_of_frobeniusLift
    A v K L hLK hmul q σ hσ]
  exact D.finiteReciprocityValue_eq_primeNormClass_of_isPrime
    A v hAxiom K L hLK σ π hπ

/-- **the finite reciprocity equivalence.** The prime-norm construction descends from positive
Frobenius lifts to an additive reciprocity homomorphism on the finite Galois
group. -/
def finiteReciprocityHom
    (D : DegreeData G) (A : Rep ℤ G) (v : ValuationData D A)
    [IsTopologicalGroup G] [CompactSpace G] [T2Space G]
    [TotallyDisconnectedSpace G]
    (hAxiom : v.SatisfiesUnramifiedUnitCohomology D)
    (K : FiniteAbstractField G) (L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.field.toSubgroup)
    [hLnormal : (extensionSubgroup K.field L hLK).Normal]
    [hLfinite : Finite
      (K.field.toSubgroup ⧸ extensionSubgroup K.field L hLK)] :
    Additive (K.field.toSubgroup ⧸ extensionSubgroup K.field L hLK) →+
      FiniteNormQuotient A K.field L hLK :=
  D.finiteReciprocityHom_of_mul A v K L hLK
    (D.finiteReciprocityValue_mul A v hAxiom K L hLK)

/-- Prime-norm evaluation formula for the finite reciprocity equivalence, using any prime
element in the fixed field of a chosen Frobenius lift. -/
theorem finiteReciprocityHom_apply_eq_primeNormClass
    (D : DegreeData G) (A : Rep ℤ G) (v : ValuationData D A)
    [IsTopologicalGroup G] [CompactSpace G] [T2Space G]
    [TotallyDisconnectedSpace G]
    (hAxiom : v.SatisfiesUnramifiedUnitCohomology D)
    (K : FiniteAbstractField G) (L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.field.toSubgroup)
    [hLnormal : (extensionSubgroup K.field L hLK).Normal]
    [hLfinite : Finite
      (K.field.toSubgroup ⧸ extensionSubgroup K.field L hLK)]
    (q : Additive
      (K.field.toSubgroup ⧸ extensionSubgroup K.field L hLK))
    (σ : D.FrobeniusElements (K.toFiniteResidueAbstractField D) L hLK)
    (hσ : D.frobeniusRestriction
      (K.toFiniteResidueAbstractField D) L hLK σ = q.toMul)
    (π : ambientFixedAddSubgroup A
      (D.frobeniusFixedField (K.toFiniteResidueAbstractField D) L hLK σ))
    (hπ :
      let Sigma : FiniteAbstractField G :=
        { field := D.frobeniusFixedField
            (K.toFiniteResidueAbstractField D) L hLK σ
          finite := D.frobeniusFixedField_absoluteFinite K L hLK σ }
      v.IsPrimeElement Sigma π) :
    let KR := K.toFiniteResidueAbstractField D
    let S := D.frobeniusFixedField KR L hLK σ
    let hSK := D.frobeniusFixedField_le KR L hLK σ
    letI : Finite
        (K.field.toSubgroup ⧸ extensionSubgroup K.field S hSK) :=
      D.frobeniusFixedField_finite KR L hLK σ
    D.finiteReciprocityHom A v hAxiom K L hLK q =
      finiteNormClass A K.field L hLK
        (relativeNorm A K.field S hSK π) := by
  exact D.finiteReciprocityHom_of_mul_apply_eq_primeNormClass
    A v hAxiom K L hLK
      (D.finiteReciprocityValue_mul A v hAxiom K L hLK)
      q σ hσ π hπ

end DegreeData

end finiteReciprocityHom

/-!
# The abstract reciprocity construction, the unramified norm-quotient equivalence

This file proves the generator calculation in the unramified case: the finite reciprocity equivalence sends arithmetic Frobenius to the prime
class.  That class generates the finite norm quotient, so the resulting
reciprocity homomorphism is promoted to an additive equivalence.
-/

noncomputable section

section unramifiedFixedFields

variable {G : Type u} [Group G] [TopologicalSpace G]

namespace DegreeData

/-- The fixed field of the degree-one lift has degree one over `K` in the
unramified case.  This is `f_{Σ/K}=d_K(φ_K)=1` together with
`[Σ:K]=f_{Σ/K}`. -/
theorem unramifiedFrobenius_fixedField_degree
    (D : DegreeData G)
    [IsTopologicalGroup G] [CompactSpace G] [T2Space G]
    (K : FiniteResidueAbstractField D) (L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.field.toSubgroup)
    [hnormal : (extensionSubgroup K.field L hLK).Normal]
    [hfinite : Finite
      (K.field.toSubgroup ⧸ extensionSubgroup K.field L hLK)]
    (hUnramified :
      (DegreeData.AbstractExtension.mk L K.field hLK).IsUnramified D) :
    let σ := D.chosenUnramifiedFrobeniusLift K L hLK
    let S := D.frobeniusFixedField K L hLK σ
    let hSK := D.frobeniusFixedField_le K L hLK σ
    letI : Finite
        (K.field.toSubgroup ⧸ extensionSubgroup K.field S hSK) :=
      D.frobeniusFixedField_finite K L hLK σ
    ((DegreeData.FiniteAbstractExtension.ofInclusion S K.field hSK).degree : ℕ) = 1 := by
  let σ := D.chosenUnramifiedFrobeniusLift K L hLK
  let S := D.frobeniusFixedField K L hLK σ
  let hSK : S.toSubgroup ≤ K.field.toSubgroup :=
    D.frobeniusFixedField_le K L hLK σ
  let : Finite
      (K.field.toSubgroup ⧸ extensionSubgroup K.field S hSK) :=
    D.frobeniusFixedField_finite K L hLK σ
  let E : DegreeData.FiniteAbstractExtension G :=
    DegreeData.FiniteAbstractExtension.ofInclusion S K.field hSK
  have hSUnramified :
      (DegreeData.AbstractExtension.mk S K.field hSK).IsUnramified D :=
    D.unramifiedFrobenius_fixedField_isUnramified
      K L hLK hUnramified
  calc
    (E.degree : ℕ) = (E.residueDegree D : ℕ) := by
      symm
      exact E.residueDegree_eq_degree_of_isUnramified D (by
        simpa [E, DegreeData.FiniteAbstractExtension.ofInclusion] using hSUnramified)
    _ = D.frobeniusExponent K L hLK σ :=
      D.frobeniusFixedField_residueDegreeOverBase K L hLK σ
    _ = 1 := D.chosenUnramifiedFrobeniusLift_exponent K L hLK

end DegreeData

end unramifiedFixedFields

section unramifiedReciprocity

/-! Mathlib's `Rep ℤ G` forces its representation-bearing group `G` to `Type 0`. -/
variable {G : IntegralRepGroupType} [Group G] [TopologicalSpace G]
variable {D : DegreeData G} {A : Rep ℤ G}

namespace ValuationData

/-- The prime-norm calculation in the unramified norm-quotient equivalence: the prime element of
`K`, included into the fixed field of the degree-one lift, has norm equal
to the original prime element. -/
theorem unramifiedFrobenius_primeNorm
    (v : ValuationData D A)
    [IsTopologicalGroup G] [CompactSpace G] [T2Space G]
    (K : FiniteAbstractField G) (L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.field.toSubgroup)
    [hnormal : (extensionSubgroup K.field L hLK).Normal]
    [Finite (K.field.toSubgroup ⧸ extensionSubgroup K.field L hLK)]
    (hUnramified :
      (DegreeData.AbstractExtension.mk L K.field hLK).IsUnramified D) :
    let KR := K.toFiniteResidueAbstractField D
    letI hLnormalKR : (extensionSubgroup KR.field L hLK).Normal := by
      simpa only [KR, FiniteAbstractField.toFiniteResidueAbstractField] using hnormal
    let σ := D.chosenUnramifiedFrobeniusLift KR L hLK
    let S := D.frobeniusFixedField KR L hLK σ
    let hSK := D.frobeniusFixedField_le KR L hLK σ
    letI : Finite
        (K.field.toSubgroup ⧸ extensionSubgroup K.field S hSK) :=
      D.frobeniusFixedField_finite KR L hLK σ
    relativeNorm A K.field S hSK
        (fixedFieldInclusion A K.field S hSK (v.chosenPrimeElement K)) =
      v.chosenPrimeElement K := by
  dsimp only
  let KR := K.toFiniteResidueAbstractField D
  let hLnormalKR : (extensionSubgroup KR.field L hLK).Normal := by
    simpa only [KR, FiniteAbstractField.toFiniteResidueAbstractField] using hnormal
  let σ := D.chosenUnramifiedFrobeniusLift KR L hLK
  let : Finite
      (K.field.toSubgroup ⧸ extensionSubgroup K.field
        (D.frobeniusFixedField KR L hLK σ)
        (D.frobeniusFixedField_le KR L hLK σ)) :=
    D.frobeniusFixedField_finite KR L hLK σ
  let S := D.frobeniusFixedField KR L hLK σ
  let hSK : S.toSubgroup ≤ K.field.toSubgroup :=
    D.frobeniusFixedField_le KR L hLK σ
  let E : DegreeData.FiniteAbstractExtension G :=
    DegreeData.FiniteAbstractExtension.ofInclusion S K.field hSK
  change relativeNorm A K.field S hSK
      (fixedFieldInclusion A K.field S hSK (v.chosenPrimeElement K)) =
    v.chosenPrimeElement K
  calc
    relativeNorm A K.field S hSK
        (fixedFieldInclusion A K.field S hSK (v.chosenPrimeElement K)) =
        (E.degree : ℕ) • v.chosenPrimeElement K := by
      have hnorm :=
        relativeNorm_fixedFieldInclusion A E (v.chosenPrimeElement K)
      change relativeNorm A K.field S hSK
          (fixedFieldInclusion A K.field S hSK (v.chosenPrimeElement K)) =
        (E.degree : ℕ) • v.chosenPrimeElement K at hnorm
      exact hnorm
    _ = 1 • v.chosenPrimeElement K := by
      rw [show (E.degree : ℕ) = 1 by
        have hdegree :=
          D.unramifiedFrobenius_fixedField_degree
            KR L hLK hUnramified
        change (E.degree : ℕ) = 1 at hdegree
        exact hdegree]
    _ = v.chosenPrimeElement K := one_nsmul _

/-- The finite reciprocity equivalence sends arithmetic Frobenius to the class of a prime
element when `L / K` is unramified.  This is the generator calculation. -/
theorem unramifiedReciprocity_frobenius_image
    (v : ValuationData D A) (hAxiom : SatisfiesUnramifiedUnitCohomology D v)
    [IsTopologicalGroup G] [CompactSpace G] [T2Space G]
    [TotallyDisconnectedSpace G]
    (K : FiniteAbstractField G) (L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.field.toSubgroup)
    [hnormal : (extensionSubgroup K.field L hLK).Normal]
    [Finite (K.field.toSubgroup ⧸ extensionSubgroup K.field L hLK)]
    (hUnramified :
      (DegreeData.AbstractExtension.mk L K.field hLK).IsUnramified D) :
    D.finiteReciprocityHom A v hAxiom K L hLK
        (Additive.ofMul (D.unramifiedFrobenius
          (K.toFiniteResidueAbstractField D) L hLK)) =
      finiteNormClass A K.field L hLK (v.chosenPrimeElement K) := by
  let KR := K.toFiniteResidueAbstractField D
  let hLnormalKR : (extensionSubgroup KR.field L hLK).Normal := by
    simpa only [KR, FiniteAbstractField.toFiniteResidueAbstractField] using hnormal
  let σ := D.chosenUnramifiedFrobeniusLift KR L hLK
  let S := D.frobeniusFixedField KR L hLK σ
  let hSK := D.frobeniusFixedField_le KR L hLK σ
  let hSfinite : Finite
      (K.field.toSubgroup ⧸ extensionSubgroup K.field S hSK) :=
    D.frobeniusFixedField_finite KR L hLK σ
  let hSabsolute : Finite ((baseField G).toSubgroup ⧸
      extensionSubgroup (baseField G) S (le_baseField S)) :=
    D.frobeniusFixedField_absoluteFinite K L hLK σ
  let Sigma : FiniteAbstractField G := ⟨S, hSabsolute⟩
  let π : ambientFixedAddSubgroup A S :=
    fixedFieldInclusion A K.field S hSK (v.chosenPrimeElement K)
  have hπ : v.IsPrimeElement Sigma π := by
    simpa [σ, S, hSK, π] using
      v.unramifiedFrobenius_includedPrime_isPrime K L hLK hUnramified
  rw [D.finiteReciprocityHom_apply_eq_primeNormClass
    A v hAxiom K L hLK
      (Additive.ofMul (D.unramifiedFrobenius KR L hLK)) σ
      (by rfl) π hπ]
  rw [show relativeNorm A K.field S hSK π = v.chosenPrimeElement K by
    simpa [σ, S, hSK, π] using
      v.unramifiedFrobenius_primeNorm K L hLK hUnramified]

/-- **the unramified norm-quotient equivalence.** For a finite unramified Galois extension, the
reciprocity homomorphism of the finite reciprocity equivalence is an additive equivalence. -/
noncomputable def unramifiedReciprocityEquiv
    (v : ValuationData D A) (hAxiom : SatisfiesUnramifiedUnitCohomology D v)
    [IsTopologicalGroup G] [CompactSpace G] [T2Space G]
    [TotallyDisconnectedSpace G]
    (K : FiniteAbstractField G) (L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.field.toSubgroup)
    [hnormal : (extensionSubgroup K.field L hLK).Normal]
    [Finite (K.field.toSubgroup ⧸ extensionSubgroup K.field L hLK)]
    (hUnramified :
      (DegreeData.AbstractExtension.mk L K.field hLK).IsUnramified D) :
    Additive (K.field.toSubgroup ⧸ extensionSubgroup K.field L hLK) ≃+
      FiniteNormQuotient A K.field L hLK :=
  v.unramifiedReciprocity_equiv_of_generator hAxiom K L hLK hUnramified
    (D.finiteReciprocityHom A v hAxiom K L hLK)
    (v.unramifiedReciprocity_frobenius_image hAxiom
      K L hLK hUnramified)

/-- The canonical unramified reciprocity equivalence evaluates by the normalized valuation class. -/
@[simp]
theorem unramifiedReciprocityEquiv_apply
    (v : ValuationData D A) (hAxiom : SatisfiesUnramifiedUnitCohomology D v)
    [IsTopologicalGroup G] [CompactSpace G] [T2Space G]
    [TotallyDisconnectedSpace G]
    (K : FiniteAbstractField G) (L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.field.toSubgroup)
    [hnormal : (extensionSubgroup K.field L hLK).Normal]
    [Finite (K.field.toSubgroup ⧸ extensionSubgroup K.field L hLK)]
    (hUnramified :
      (DegreeData.AbstractExtension.mk L K.field hLK).IsUnramified D)
    (q : Additive
      (K.field.toSubgroup ⧸ extensionSubgroup K.field L hLK)) :
    v.unramifiedReciprocityEquiv hAxiom K L hLK hUnramified q =
      D.finiteReciprocityHom A v hAxiom K L hLK q :=
  rfl

end ValuationData
end unramifiedReciprocity
end
end

end ClassFormation
end

section
-- module Solutions.OAIQ244_DUKE.AbstractClassFieldTheory_Reciprocity_Construction_MainNaturality
attribute [-instance] _root_.ClassFormation.FiniteGaloisSubextension.extensionSubgroup_over_intermediate_normalInstance _root_.ClassFormation.FiniteGaloisSubextension.intermediateField_normalInstance _root_.ClassFormation.instIsAddTorsionFreeZHat _root_.ClassFormation.instIsMulTorsionFreeMultiplicativeZHat _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.DiscreteNthRootsSubgroup.instTopologicalSpaceSubtypeUnitsMemSubgroup _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.KummerTheory.finite_finsupp_nsmulQuotient _root_.LocalClassFieldTheory.baseFixingExtensionQuotient_finite _root_.LocalClassFieldTheory.extensionSubgroupBase_normal _root_.LocalClassFieldTheory.finiteGaloisExtensionSubgroupOfEmbedding_normal _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitQuotientCarrier_finite _root_.LocalFieldTheory.DiscreteValuationField.finite_padicInt_finPi_nsmulQuotient _root_.LocalFieldTheory.DiscreteValuationField.finite_padicInt_pi_nsmulQuotient_of_coprime _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_multiplicative_nthPowerQuotient _root_.LocalFieldTheory.finite_nsmulAddQuotient_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.LubinTate.compatibleGroupFamiliesGroup _root_.OAI.PrimeDegreePackets.boundedRealFields_finite _root_.OAI.PrimeDegreePackets.diagonalLogAction _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.RamificationTheory.HilbertRamification.ValuationSubring.inertiaGroup_normal _root_.RamificationTheory.HilbertRamification.ValuationSubring.ramificationGroupInInertiaAut_normal _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.RelativeIdeleGroup.relativeIdeleMulAction _root_.ValuationTheory.DiscreteValuationField.DVF.maximalIdealPowSuccQuotModule _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteIdeleGroupIsTopologicalGroup _root_.finiteLocalUnitsOpen _root_.ideleGroupIsTopologicalGroup
attribute [-simp] _root_.ClassFormation.FiniteAbelianSubextension.extensionQuotientMk_apply _root_.ClassFormation.FiniteGaloisSubextension.classFieldCandidate_field _root_.ClassFormation.cyclicNormClassHom_apply _root_.ClassFormation.extensionFixedRepresentationEquiv_apply_coe _root_.ClassFormation.extensionFixedRepresentationEquiv_symm_apply_coe _root_.ClassFormation.mem_normFilterBasis_iff _root_.ClassFormation.toZModPow_zHatToPadicInt _root_.ClassFormation.zHatReductionRingHom_apply _root_.ClassFormation.zHatRingEquivProfiniteIntegerPrimeProduct_apply _root_.ClassFormation.zHatToPadicInt_intCast _root_.ClassFormation.zHatToProfiniteIntegerPrimeProduct_apply _root_.ClassFormation.zHatToProfiniteIntegerPrimeProduct_intCast _root_.ClassFormation.zHatUnitsContinuousMulEquivPrimeProduct_coe_apply _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.IsDiscreteValuationRing.addVal_ringEquiv _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.KummerTheory.torsionQuotientEquivOfZHatMulDecomposition_mk _root_.KummerTheory.zHatUnitsContinuousMulEquivPrimeProduct_rationalCyclotomicCharacter _root_.LocalClassFieldTheory.baseFixingExtensionQuotientEquivAmbient_mk _root_.LocalClassFieldTheory.baseUnitsEquivGaloisAmbientFixed_val _root_.LocalClassFieldTheory.embeddedFieldUnitsEquivGaloisFixed_coe _root_.LocalClassFieldTheory.finiteGaloisUnitsEquivAbstractFixedOfEmbedding_coe _root_.LocalClassFieldTheory.finiteGaloisUnitsEquivAbstractFixed_coe _root_.LocalClassFieldTheory.finiteResidueFrobeniusFromZHat_apply _root_.LocalClassFieldTheory.finiteResidueFrobeniusFromZHat_one _root_.LocalClassFieldTheory.intermediateFieldUnitsEquivGaloisFixed_coe _root_.LocalClassFieldTheory.residueAbsoluteDegreeIn_frobenius _root_.LocalClassFieldTheory.residueAbsoluteFrobenius_one _root_.LocalClassFieldTheory.residueFrobeniusToLimit_apply_component _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.LocalFieldTheory.residueField_algebraMap_residue _root_.OAI.PrimeDegreePackets.ThetaConstruction.schwartzCM_apply _root_.infinitePlace_mult_smul
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

universe u

namespace ClassFormation

open KummerTheory

open CyclicCohomology

open CategoryTheory


/-!
# The abstract reciprocity construction, norm--conjugation naturality: naturality of reciprocity

The two vertical maps are constructed here on the actual finite
Galois quotients and the actual finite norm quotients.  Their defining
commutativities are proved from norm transitivity and conjugation, so the
eventual the finite reciprocity equivalence reciprocity homomorphisms can be connected without
any additional comparison datum.
-/

noncomputable section

open scoped BigOperators

section GroupOnly

variable {G : Type u} [Group G] [TopologicalSpace G]

/-- The left vertical map in the first diagram of norm--conjugation naturality:
restriction from `G(L'/K')` to `G(L/K)`. -/
def finiteReciprocityNaturalityRestriction
    (K K' L L' : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.toSubgroup)
    (hL'K' : L'.toSubgroup ≤ K'.toSubgroup)
    (hK'K : K'.toSubgroup ≤ K.toSubgroup)
    (hL'L : L'.toSubgroup ≤ L.toSubgroup)
    [hLnormal : (extensionSubgroup K L hLK).Normal]
    [hL'normal : (extensionSubgroup K' L' hL'K').Normal] :
    (K'.toSubgroup ⧸ extensionSubgroup K' L' hL'K') →*
      (K.toSubgroup ⧸ extensionSubgroup K L hLK) := by
  apply QuotientGroup.map
    (extensionSubgroup K' L' hL'K')
    (extensionSubgroup K L hLK)
    (Subgroup.inclusion hK'K)
  intro k' hk'L'
  change k'.1 ∈ L'.toSubgroup at hk'L'
  change (Subgroup.inclusion hK'K k').1 ∈ L.toSubgroup
  exact hL'L hk'L'

/-- Restriction sends a represented finite reciprocity class to the corresponding
lower-level class. -/
@[simp]
theorem finiteReciprocityNaturalityRestriction_mk
    (K K' L L' : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.toSubgroup)
    (hL'K' : L'.toSubgroup ≤ K'.toSubgroup)
    (hK'K : K'.toSubgroup ≤ K.toSubgroup)
    (hL'L : L'.toSubgroup ≤ L.toSubgroup)
    [hLnormal : (extensionSubgroup K L hLK).Normal]
    [hL'normal : (extensionSubgroup K' L' hL'K').Normal]
    (k' : K'.toSubgroup) :
    finiteReciprocityNaturalityRestriction K K' L L' hLK hL'K' hK'K hL'L
        (QuotientGroup.mk k') =
      QuotientGroup.mk (Subgroup.inclusion hK'K k') :=
  rfl

namespace DegreeData

/-- Restriction on the infinite Frobenius quotients underlying the first
diagram of norm--conjugation naturality. -/
def finiteReciprocityNaturalityFrobeniusTowerMap
    (D : DegreeData G) [IsTopologicalGroup G]
    (K K' L L' : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.toSubgroup)
    (hL'K' : L'.toSubgroup ≤ K'.toSubgroup)
    (hK'K : K'.toSubgroup ≤ K.toSubgroup)
    (hL'L : L'.toSubgroup ≤ L.toSubgroup)
    [hLnormal : (extensionSubgroup K L hLK).Normal]
    [hL'normal : (extensionSubgroup K' L' hL'K').Normal] :
    (K'.toSubgroup ⧸ D.extensionInertiaWithin K' L' hL'K') →*
      (K.toSubgroup ⧸ D.extensionInertiaWithin K L hLK) := by
  apply QuotientGroup.map
    (D.extensionInertiaWithin K' L' hL'K')
    (D.extensionInertiaWithin K L hLK)
    (Subgroup.inclusion hK'K)
  rintro k' ⟨hk'L', hk'I⟩
  constructor
  · change k'.1 ∈ L'.toSubgroup at hk'L'
    change (Subgroup.inclusion hK'K k').1 ∈ L.toSubgroup
    exact hL'L hk'L'
  · exact hk'I

/-- The Frobenius tower map has the expected value on a quotient representative. -/
@[simp]
theorem finiteReciprocityNaturalityFrobeniusTowerMap_mk
    (D : DegreeData G) [IsTopologicalGroup G]
    (K K' L L' : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.toSubgroup)
    (hL'K' : L'.toSubgroup ≤ K'.toSubgroup)
    (hK'K : K'.toSubgroup ≤ K.toSubgroup)
    (hL'L : L'.toSubgroup ≤ L.toSubgroup)
    [hLnormal : (extensionSubgroup K L hLK).Normal]
    [hL'normal : (extensionSubgroup K' L' hL'K').Normal]
    (k' : K'.toSubgroup) :
    D.finiteReciprocityNaturalityFrobeniusTowerMap K K' L L'
        hLK hL'K' hK'K hL'L (QuotientGroup.mk k') =
      QuotientGroup.mk (Subgroup.inclusion hK'K k') := rfl

/-- Continuous form of `finiteReciprocityNaturalityFrobeniusTowerMap`, used to transport
the closed cyclic subgroup generated by a Frobenius lift. -/
def finiteReciprocityNaturalityFrobeniusTowerMapContinuous
    (D : DegreeData G) [IsTopologicalGroup G]
    (K K' L L' : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.toSubgroup)
    (hL'K' : L'.toSubgroup ≤ K'.toSubgroup)
    (hK'K : K'.toSubgroup ≤ K.toSubgroup)
    (hL'L : L'.toSubgroup ≤ L.toSubgroup)
    [hLnormal : (extensionSubgroup K L hLK).Normal]
    [hL'normal : (extensionSubgroup K' L' hL'K').Normal] :
    (K'.toSubgroup ⧸ D.extensionInertiaWithin K' L' hL'K') →ₜ*
      (K.toSubgroup ⧸ D.extensionInertiaWithin K L hLK) where
  toMonoidHom := D.finiteReciprocityNaturalityFrobeniusTowerMap
    K K' L L' hLK hL'K' hK'K hL'L
  continuous_toFun := by
    rw [← QuotientGroup.isOpenQuotientMap_mk.continuous_comp_iff]
    change Continuous (fun k' : K'.toSubgroup =>
      QuotientGroup.mk (Subgroup.inclusion hK'K k'))
    apply QuotientGroup.continuous_mk.comp
    exact continuous_subtype_val.subtype_mk _

/-- Frobenius residue-degree compatibility's normalized-degree square on the two infinite
Frobenius quotients. -/
theorem finiteReciprocityNaturalityFrobeniusTowerMap_degree
    (D : DegreeData G) [IsTopologicalGroup G]
    (E : DegreeData.FiniteResidueAbstractExtension D)
    (L L' : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ E.base.toSubgroup)
    (hL'K' : L'.toSubgroup ≤ E.field.toSubgroup)
    (hL'L : L'.toSubgroup ≤ L.toSubgroup)
    [hLnormal : (extensionSubgroup E.base.field L hLK).Normal]
    [hL'normal : (extensionSubgroup E.field.field L' hL'K').Normal]
    (q : E.field.toSubgroup ⧸
      D.extensionInertiaWithin E.field.field L' hL'K') :
    (D.extensionNormalizedDegree E.base L hLK
      (D.finiteReciprocityNaturalityFrobeniusTowerMap
        E.base.field E.field.field L L'
        hLK hL'K' E.below hL'L q)).toAdd =
      (E.residueDegree : ℕ) •
        (D.extensionNormalizedDegree E.field L' hL'K' q).toAdd := by
  refine Quotient.inductionOn' q ?_
  intro k'
  change (D.normalizedDegree E.base (Subgroup.inclusion E.below k')).toAdd =
    (E.residueDegree : ℕ) • (D.normalizedDegree E.field k').toAdd
  exact D.frobeniusRestrictionNaturality_normalizedDegree E k'

/-- A positive Frobenius lift over `K'` remains a positive Frobenius lift
over `K`; its exponent is multiplied by `f_{K'/K}`. -/
def finiteReciprocityNaturalityFrobeniusTowerLift
    (D : DegreeData G) [IsTopologicalGroup G]
    (E : DegreeData.FiniteResidueAbstractExtension D)
    (L L' : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ E.base.toSubgroup)
    (hL'K' : L'.toSubgroup ≤ E.field.toSubgroup)
    (hL'L : L'.toSubgroup ≤ L.toSubgroup)
    [hLnormal : (extensionSubgroup E.base.field L hLK).Normal]
    [hL'normal : (extensionSubgroup E.field.field L' hL'K').Normal]
    (σ : D.FrobeniusElements E.field L' hL'K') :
    D.FrobeniusElements E.base L hLK := by
  let f := (E.residueDegree : ℕ)
  let n := D.frobeniusExponent E.field L' hL'K' σ
  refine ⟨D.finiteReciprocityNaturalityFrobeniusTowerMap
      E.base.field E.field.field L L' hLK hL'K' E.below hL'L σ.1,
    f * n, Nat.mul_pos E.residueDegree.property
      (D.frobeniusExponent_pos E.field L' hL'K' σ), ?_⟩
  apply Multiplicative.ext
  rw [D.finiteReciprocityNaturalityFrobeniusTowerMap_degree E L L'
    hLK hL'K' hL'L σ.1]
  rw [D.extensionNormalizedDegree_frobenius_eq_pow E.field L' hL'K' σ]
  change f • (n • (1 : ZHat)) = (f * n) • (1 : ZHat)
  rw [smul_smul]

/-- The chosen Frobenius tower lift coerces to the represented ambient automorphism. -/
@[simp]
theorem finiteReciprocityNaturalityFrobeniusTowerLift_coe
    (D : DegreeData G) [IsTopologicalGroup G]
    (E : DegreeData.FiniteResidueAbstractExtension D)
    (L L' : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ E.base.toSubgroup)
    (hL'K' : L'.toSubgroup ≤ E.field.toSubgroup)
    (hL'L : L'.toSubgroup ≤ L.toSubgroup)
    [hLnormal : (extensionSubgroup E.base.field L hLK).Normal]
    [hL'normal : (extensionSubgroup E.field.field L' hL'K').Normal]
    (σ : D.FrobeniusElements E.field L' hL'K') :
    (D.finiteReciprocityNaturalityFrobeniusTowerLift
      E L L' hLK hL'K' hL'L σ).1 =
      D.finiteReciprocityNaturalityFrobeniusTowerMap
        E.base.field E.field.field L L' hLK hL'K' E.below hL'L σ.1 := by
  simp [finiteReciprocityNaturalityFrobeniusTowerLift]

/-- The Frobenius tower lift has the prescribed Frobenius exponent. -/
@[simp]
theorem finiteReciprocityNaturalityFrobeniusTowerLift_exponent
    (D : DegreeData G) [IsTopologicalGroup G]
    (E : DegreeData.FiniteResidueAbstractExtension D)
    (L L' : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ E.base.toSubgroup)
    (hL'K' : L'.toSubgroup ≤ E.field.toSubgroup)
    (hL'L : L'.toSubgroup ≤ L.toSubgroup)
    [hLnormal : (extensionSubgroup E.base.field L hLK).Normal]
    [hL'normal : (extensionSubgroup E.field.field L' hL'K').Normal]
    (σ : D.FrobeniusElements E.field L' hL'K') :
    D.frobeniusExponent E.base L hLK
        (D.finiteReciprocityNaturalityFrobeniusTowerLift
          E L L' hLK hL'K' hL'L σ) =
      (E.residueDegree : ℕ) *
        D.frobeniusExponent E.field L' hL'K' σ := by
  apply proCIntegerOne_pow_nat_injective
  let f := (E.residueDegree : ℕ)
  let n := D.frobeniusExponent E.field L' hL'K' σ
  calc
    (Multiplicative.ofAdd (1 : ZHat)) ^
        D.frobeniusExponent E.base L hLK
          (D.finiteReciprocityNaturalityFrobeniusTowerLift
            E L L' hLK hL'K' hL'L σ) =
      D.extensionNormalizedDegree E.base L hLK
        (D.finiteReciprocityNaturalityFrobeniusTowerLift
          E L L' hLK hL'K' hL'L σ).1 :=
      (D.extensionNormalizedDegree_frobenius_eq_pow E.base L hLK _).symm
    _ = (Multiplicative.ofAdd (1 : ZHat)) ^ (f * n) := by
      apply Multiplicative.ext
      rw [D.finiteReciprocityNaturalityFrobeniusTowerLift_coe]
      rw [D.finiteReciprocityNaturalityFrobeniusTowerMap_degree E L L'
        hLK hL'K' hL'L σ.1]
      rw [D.extensionNormalizedDegree_frobenius_eq_pow
        E.field L' hL'K' σ]
      change f • (n • (1 : ZHat)) = (f * n) • (1 : ZHat)
      rw [smul_smul]
    _ = (Multiplicative.ofAdd (1 : ZHat)) ^
        ((E.residueDegree : ℕ) *
          D.frobeniusExponent E.field L' hL'K' σ) := by rfl

/-- Restriction of the transported lift is the restriction of the original
lift along the left vertical map of norm--conjugation naturality. -/
theorem finiteReciprocityNaturalityRestriction_frobeniusTowerLift
    (D : DegreeData G) [IsTopologicalGroup G]
    (E : DegreeData.FiniteResidueAbstractExtension D)
    (L L' : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ E.base.toSubgroup)
    (hL'K' : L'.toSubgroup ≤ E.field.toSubgroup)
    (hL'L : L'.toSubgroup ≤ L.toSubgroup)
    [hLnormal : (extensionSubgroup E.base.field L hLK).Normal]
    [hL'normal : (extensionSubgroup E.field.field L' hL'K').Normal]
    (σ : D.FrobeniusElements E.field L' hL'K') :
    finiteReciprocityNaturalityRestriction
        E.base.field E.field.field L L' hLK hL'K' E.below hL'L
        (D.frobeniusRestriction E.field L' hL'K' σ) =
      D.frobeniusRestriction E.base L hLK
        (D.finiteReciprocityNaturalityFrobeniusTowerLift
          E L L' hLK hL'K' hL'L σ) := by
  change finiteReciprocityNaturalityRestriction
      E.base.field E.field.field L L' hLK hL'K' E.below hL'L
      (D.extensionRestriction E.field.field L' hL'K' σ.1) =
    D.extensionRestriction E.base.field L hLK
      (D.finiteReciprocityNaturalityFrobeniusTowerLift
        E L L' hLK hL'K' hL'L σ).1
  rw [D.finiteReciprocityNaturalityFrobeniusTowerLift_coe]
  refine Quotient.inductionOn' σ.1 ?_
  intro k'
  rfl

end DegreeData

/-- Finiteness of the upper-left-to-lower-right composite extension in the
first diagram. -/
theorem finiteReciprocityNaturality_tower_finite
    (K K' L' : ClosedSubgroup G)
    (hK'K : K'.toSubgroup ≤ K.toSubgroup)
    (hL'K' : L'.toSubgroup ≤ K'.toSubgroup)
    [Finite (K.toSubgroup ⧸ extensionSubgroup K K' hK'K)]
    [Finite (K'.toSubgroup ⧸ extensionSubgroup K' L' hL'K')] :
    Finite (K.toSubgroup ⧸
      extensionSubgroup K L' (hL'K'.trans hK'K)) :=
  relativeTowerQuotientFinite K K' L' hL'K' hK'K

end GroupOnly

section Representation

/-! Mathlib's `Rep ℤ G` forces its representation-bearing group `G` to `Type 0`. -/
variable {G : IntegralRepGroupType} [Group G] [TopologicalSpace G]

/-- The right vertical map in the first diagram of norm--conjugation naturality.  It is
the actual norm `N_{K'/K}`, descended to the actual finite norm quotients. -/
def finiteReciprocityNaturalityNormMap
    (A : Rep ℤ G) (K K' L L' : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.toSubgroup)
    (hL'K' : L'.toSubgroup ≤ K'.toSubgroup)
    (hK'K : K'.toSubgroup ≤ K.toSubgroup)
    (hL'L : L'.toSubgroup ≤ L.toSubgroup)
    [hLKfinite : Finite
      (K.toSubgroup ⧸ extensionSubgroup K L hLK)]
    [hL'K'finite : Finite
      (K'.toSubgroup ⧸ extensionSubgroup K' L' hL'K')]
    [hK'Kfinite : Finite
      (K.toSubgroup ⧸ extensionSubgroup K K' hK'K)] :
    FiniteNormQuotient A K' L' hL'K' →+
      FiniteNormQuotient A K L hLK := by
  letI hL'Kfinite : Finite (K.toSubgroup ⧸
      extensionSubgroup K L' (hL'K'.trans hK'K)) :=
    finiteReciprocityNaturality_tower_finite K K' L' hK'K hL'K'
  letI hL'Lfinite : Finite
      (L.toSubgroup ⧸ extensionSubgroup L L' hL'L) :=
    FiniteIntermediateField.finite_extension_of_le
      (hL'L.trans hLK) hLK hL'L
  let f : ambientFixedAddSubgroup A K' →+ FiniteNormQuotient A K L hLK :=
    (finiteNormClassHom A K L hLK).comp (relativeNorm A K K' hK'K)
  apply finiteNormQuotientLift A K' L' hL'K' f
  rintro _ ⟨a, rfl⟩
  let TLL' : DegreeData.FiniteTower G :=
    { top := L'
      middle := L
      base := K
      top_le_middle := hL'L
      middle_le_base := hLK
      finiteTopQuotient := hL'Lfinite
      finiteBaseQuotient := hLKfinite }
  let TKK' : DegreeData.FiniteTower G :=
    { top := L'
      middle := K'
      base := K
      top_le_middle := hL'K'
      middle_le_base := hK'K
      finiteTopQuotient := hL'K'finite
      finiteBaseQuotient := hK'Kfinite }
  apply (finiteNormClass_eq_zero_iff A K L hLK _).2
  refine ⟨relativeNorm A L L' hL'L a, ?_⟩
  calc
    relativeNorm A K L hLK (relativeNorm A L L' hL'L a) =
        relativeNorm A K L' (hL'L.trans hLK) a :=
      TLL'.norm_trans_apply A a
    _ = relativeNorm A K L' (hL'K'.trans hK'K) a := by
      congr 2
    _ = relativeNorm A K K' hK'K (relativeNorm A K' L' hL'K' a) :=
      (TKK'.norm_trans_apply A a).symm

/-- The norm map carries a finite norm class to the corresponding class over the base. -/
@[simp]
theorem finiteReciprocityNaturalityNormMap_finiteNormClass
    (A : Rep ℤ G) (K K' L L' : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.toSubgroup)
    (hL'K' : L'.toSubgroup ≤ K'.toSubgroup)
    (hK'K : K'.toSubgroup ≤ K.toSubgroup)
    (hL'L : L'.toSubgroup ≤ L.toSubgroup)
    [hLKfinite : Finite
      (K.toSubgroup ⧸ extensionSubgroup K L hLK)]
    [Finite
      (K'.toSubgroup ⧸ extensionSubgroup K' L' hL'K')]
    [hK'Kfinite : Finite
      (K.toSubgroup ⧸ extensionSubgroup K K' hK'K)]
    (a : ambientFixedAddSubgroup A K') :
    finiteReciprocityNaturalityNormMap A K K' L L' hLK hL'K' hK'K hL'L
        (finiteNormClass A K' L' hL'K' a) =
      finiteNormClass A K L hLK (relativeNorm A K K' hK'K a) :=
  by
    simp [finiteReciprocityNaturalityNormMap]
    rfl

/-- The additive map `a ↦ a^s` between the two actual fixed subgroups. -/
def conjugateFixedElementHom [ContinuousMul G]
    (A : Rep ℤ G) (K : ClosedSubgroup G) (s : G) :
    ambientFixedAddSubgroup A K →+
      ambientFixedAddSubgroup A (conjugateClosedSubgroup K s) where
  toFun := conjugateFixedElement A K s
  map_zero' := by
    apply Subtype.ext
    exact map_zero (A.ρ s⁻¹)
  map_add' a b := by
    apply Subtype.ext
    exact map_add (A.ρ s⁻¹) a.1 b.1

/-- The homomorphism on conjugate-fixed elements evaluates by the underlying conjugation map. -/
@[simp]
theorem conjugateFixedElementHom_apply [ContinuousMul G]
    (A : Rep ℤ G) (K : ClosedSubgroup G) (s : G)
    (a : ambientFixedAddSubgroup A K) :
    conjugateFixedElementHom A K s a = conjugateFixedElement A K s a :=
  rfl

/-- The right vertical map in the conjugation diagram of norm--conjugation naturality,
descended to the actual finite norm quotients. -/
def finiteReciprocityNaturalityConjugationNormMap
    [ContinuousMul G] (A : Rep ℤ G)
    (K L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.toSubgroup) (s : G)
    [hLfinite : Finite
      (K.toSubgroup ⧸ extensionSubgroup K L hLK)] :
    letI : Finite ((conjugateClosedSubgroup K s).toSubgroup ⧸
        extensionSubgroup (conjugateClosedSubgroup K s)
          (conjugateClosedSubgroup L s)
          (conjugateClosedSubgroup_mono hLK s)) :=
      finite_conjugateExtension K L hLK s
    FiniteNormQuotient A K L hLK →+
      FiniteNormQuotient A (conjugateClosedSubgroup K s)
        (conjugateClosedSubgroup L s)
        (conjugateClosedSubgroup_mono hLK s) := by
  letI hConjFinite : Finite ((conjugateClosedSubgroup K s).toSubgroup ⧸
      extensionSubgroup (conjugateClosedSubgroup K s)
        (conjugateClosedSubgroup L s)
        (conjugateClosedSubgroup_mono hLK s)) :=
    finite_conjugateExtension K L hLK s
  let f : ambientFixedAddSubgroup A K →+
      FiniteNormQuotient A (conjugateClosedSubgroup K s)
        (conjugateClosedSubgroup L s)
        (conjugateClosedSubgroup_mono hLK s) :=
    (finiteNormClassHom A (conjugateClosedSubgroup K s)
      (conjugateClosedSubgroup L s)
      (conjugateClosedSubgroup_mono hLK s)).comp
        (conjugateFixedElementHom A K s)
  apply finiteNormQuotientLift A K L hLK f
  rintro _ ⟨a, rfl⟩
  apply (finiteNormClass_eq_zero_iff A (conjugateClosedSubgroup K s)
    (conjugateClosedSubgroup L s) (conjugateClosedSubgroup_mono hLK s) _).2
  refine ⟨conjugateFixedElement A L s a, ?_⟩
  exact relativeNorm_conjugate_apply A K L hLK s a

/-- The conjugation norm map preserves canonical finite norm classes. -/
@[simp]
theorem finiteReciprocityNaturalityConjugationNormMap_finiteNormClass
    [ContinuousMul G] (A : Rep ℤ G)
    (K L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.toSubgroup) (s : G)
    [Finite (K.toSubgroup ⧸ extensionSubgroup K L hLK)]
    (a : ambientFixedAddSubgroup A K) :
    letI : Finite ((conjugateClosedSubgroup K s).toSubgroup ⧸
        extensionSubgroup (conjugateClosedSubgroup K s)
          (conjugateClosedSubgroup L s)
          (conjugateClosedSubgroup_mono hLK s)) :=
      finite_conjugateExtension K L hLK s
    finiteReciprocityNaturalityConjugationNormMap A K L hLK s
        (finiteNormClass A K L hLK a) =
      finiteNormClass A (conjugateClosedSubgroup K s)
        (conjugateClosedSubgroup L s) (conjugateClosedSubgroup_mono hLK s)
        (conjugateFixedElement A K s a) := by
  let hConjFinite : Finite ((conjugateClosedSubgroup K s).toSubgroup ⧸
      extensionSubgroup (conjugateClosedSubgroup K s)
        (conjugateClosedSubgroup L s)
        (conjugateClosedSubgroup_mono hLK s)) :=
    finite_conjugateExtension K L hLK s
  simp [finiteReciprocityNaturalityConjugationNormMap]
  rfl

end Representation

section GroupOnly

variable {G : Type u} [Group G] [TopologicalSpace G]

namespace DegreeData

/-- The global degree is invariant under conjugation. -/
theorem finiteReciprocityNaturalityDegree_conjugateSubgroupEquiv
    (D : DegreeData G) [IsTopologicalGroup G]
    (K : ClosedSubgroup G) (s : G) (k : K.toSubgroup) :
    D.degree (conjugateSubgroupEquiv K s k).1 = D.degree k.1 := by
  rw [conjugateSubgroupEquiv_apply_coe, map_mul, map_mul, map_inv]
  simp [mul_comm]

/-- The normalized degree is invariant under the conjugation equivalence
of field subgroups. -/
theorem finiteReciprocityNaturalityNormalizedDegree_conjugateSubgroupEquiv
    (D : DegreeData G) [IsTopologicalGroup G]
    (K : FiniteResidueAbstractField D) (s : G)
    (k : K.field.toSubgroup) :
    D.normalizedDegree (K.conjugate s : D.FiniteResidueAbstractField)
        (conjugateSubgroupEquiv K.field s k) =
      D.normalizedDegree K k := by
  apply Multiplicative.ext
  apply zHatMulNat_injective K.residueDegree.property
  change (K.residueDegree : ℕ) •
      (D.normalizedDegree (K.conjugate s : D.FiniteResidueAbstractField)
        (conjugateSubgroupEquiv K.field s k)).toAdd =
    (K.residueDegree : ℕ) • (D.normalizedDegree K k).toAdd
  rw [D.residueDegree_nsmul_normalizedDegree K k]
  rw [← K.residueDegree_conjugate s]
  exact (D.residueDegree_nsmul_normalizedDegree
    (K.conjugate s : D.FiniteResidueAbstractField)
    (show (K.conjugate s).field.toSubgroup from
      conjugateSubgroupEquiv K.field s k)).trans
    (congrArg Multiplicative.toAdd
      (D.finiteReciprocityNaturalityDegree_conjugateSubgroupEquiv K.field s k))

/-- Conjugation carries `I_L` inside `G_K` exactly to the corresponding
inertia subgroup for `L^s / K^s`. -/
theorem finiteReciprocityNaturalityMap_extensionInertiaWithin_conjugate
    (D : DegreeData G) [IsTopologicalGroup G]
    (K L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.toSubgroup) (s : G) :
    (D.extensionInertiaWithin K L hLK).map
        (conjugateSubgroupEquiv K s).toMonoidHom =
      D.extensionInertiaWithin (conjugateClosedSubgroup K s)
        (conjugateClosedSubgroup L s)
        (conjugateClosedSubgroup_mono hLK s) := by
  ext x
  constructor
  · rintro ⟨k, ⟨hkL, hkI⟩, rfl⟩
    constructor
    · rw [← map_extensionSubgroup_conjugate K L hLK s]
      exact ⟨k, hkL, rfl⟩
    · change conjugateSubgroupEquiv K s k ∈
        D.fieldInertiaWithin (conjugateClosedSubgroup K s)
      rw [D.mem_fieldInertiaWithin_iff,
        D.finiteReciprocityNaturalityDegree_conjugateSubgroupEquiv K s,
        ← D.mem_fieldInertiaWithin_iff]
      exact hkI
  · intro hx
    let k := (conjugateSubgroupEquiv K s).symm x
    refine ⟨k, ?_, (conjugateSubgroupEquiv K s).apply_symm_apply x⟩
    constructor
    · have hxL : x ∈ extensionSubgroup (conjugateClosedSubgroup K s)
          (conjugateClosedSubgroup L s)
          (conjugateClosedSubgroup_mono hLK s) := hx.1
      rw [← map_extensionSubgroup_conjugate K L hLK s] at hxL
      rcases hxL with ⟨k', hk'L, hk'eq⟩
      have : k' = k := by
        apply (conjugateSubgroupEquiv K s).injective
        exact hk'eq.trans
          ((conjugateSubgroupEquiv K s).apply_symm_apply x).symm
      simpa [this] using hk'L
    · change k ∈ D.fieldInertiaWithin K
      rw [D.mem_fieldInertiaWithin_iff]
      rw [← D.finiteReciprocityNaturalityDegree_conjugateSubgroupEquiv K s k]
      rw [(conjugateSubgroupEquiv K s).apply_symm_apply x]
      exact (D.mem_fieldInertiaWithin_iff _ _).mp hx.2

/-- Conjugation as a continuous multiplicative equivalence on the infinite
Frobenius quotients. -/
noncomputable def finiteReciprocityNaturalityFrobeniusConjugationEquiv
    (D : DegreeData G) [IsTopologicalGroup G]
    (K L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.toSubgroup) (s : G)
    [hLnormal : (extensionSubgroup K L hLK).Normal] :
    (K.toSubgroup ⧸ D.extensionInertiaWithin K L hLK) ≃ₜ*
      ((conjugateClosedSubgroup K s).toSubgroup ⧸
        D.extensionInertiaWithin (conjugateClosedSubgroup K s)
          (conjugateClosedSubgroup L s)
          (conjugateClosedSubgroup_mono hLK s)) := by
  let e : (K.toSubgroup ⧸ D.extensionInertiaWithin K L hLK) ≃*
      ((conjugateClosedSubgroup K s).toSubgroup ⧸
        D.extensionInertiaWithin (conjugateClosedSubgroup K s)
          (conjugateClosedSubgroup L s)
          (conjugateClosedSubgroup_mono hLK s)) :=
    QuotientGroup.congr
      (D.extensionInertiaWithin K L hLK)
      (D.extensionInertiaWithin (conjugateClosedSubgroup K s)
        (conjugateClosedSubgroup L s)
        (conjugateClosedSubgroup_mono hLK s))
      (conjugateSubgroupEquiv K s)
      (D.finiteReciprocityNaturalityMap_extensionInertiaWithin_conjugate K L hLK s)
  refine { e with
    continuous_toFun := ?_
    continuous_invFun := ?_ }
  · rw [← QuotientGroup.isOpenQuotientMap_mk.continuous_comp_iff]
    change Continuous (fun k : K.toSubgroup =>
      QuotientGroup.mk (conjugateSubgroupEquiv K s k))
    apply QuotientGroup.continuous_mk.comp
    change Continuous (fun k : K.toSubgroup =>
      (⟨s⁻¹ * k.1 * s, by
        change s⁻¹ * k.1 * s ∈ conjugateClosedSubgroup K s
        rw [conjugateClosedSubgroup_mem]
        simp [mul_assoc]⟩ :
          (conjugateClosedSubgroup K s).toSubgroup))
    exact ((continuous_const.mul continuous_subtype_val).mul
      continuous_const).subtype_mk _
  · rw [← QuotientGroup.isOpenQuotientMap_mk.continuous_comp_iff]
    change Continuous (fun x : (conjugateClosedSubgroup K s).toSubgroup =>
      QuotientGroup.mk ((conjugateSubgroupEquiv K s).symm x))
    apply QuotientGroup.continuous_mk.comp
    change Continuous (fun x : (conjugateClosedSubgroup K s).toSubgroup =>
      (⟨s * x.1 * s⁻¹,
        (conjugateClosedSubgroup_mem K s x.1).mp x.2⟩ : K.toSubgroup))
    exact ((continuous_const.mul continuous_subtype_val).mul
      continuous_const).subtype_mk _

/-- The Frobenius conjugation equivalence has the expected value on quotient representatives. -/
@[simp]
theorem finiteReciprocityNaturalityFrobeniusConjugationEquiv_mk
    (D : DegreeData G) [IsTopologicalGroup G]
    (K L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.toSubgroup) (s : G)
    [(extensionSubgroup K L hLK).Normal]
    (k : K.toSubgroup) :
    D.finiteReciprocityNaturalityFrobeniusConjugationEquiv K L hLK s
        (QuotientGroup.mk k) =
      QuotientGroup.mk (conjugateSubgroupEquiv K s k) := by
  exact QuotientGroup.congr_mk
    (D.extensionInertiaWithin K L hLK)
    (D.extensionInertiaWithin (conjugateClosedSubgroup K s)
      (conjugateClosedSubgroup L s) (conjugateClosedSubgroup_mono hLK s))
    (conjugateSubgroupEquiv K s)
    (D.finiteReciprocityNaturalityMap_extensionInertiaWithin_conjugate K L hLK s) k

/-- The normality transported by conjugation is exposed at the
residue-finite field boundary.  Keeping this bridge as an instance prevents
clients from unfolding the bundled conjugate merely to recover the existing
normality instance for the literal conjugate subgroup. -/
instance finiteReciprocityNaturalityFiniteResidueConjugate_normal
    (D : DegreeData G) [IsTopologicalGroup G]
    (K : FiniteResidueAbstractField D) (L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.field.toSubgroup) (s : G)
    [hLnormal : (extensionSubgroup K.field L hLK).Normal] :
    (extensionSubgroup (K.conjugate s).field
      (conjugateClosedSubgroup L s)
      (conjugateClosedSubgroup_mono hLK s)).Normal := by
  change
    (extensionSubgroup (conjugateClosedSubgroup K.field s)
      (conjugateClosedSubgroup L s)
      (conjugateClosedSubgroup_mono hLK s)).Normal
  infer_instance

/-- The conjugation equivalence preserves normalized degree. -/
theorem finiteReciprocityNaturalityFrobeniusConjugationEquiv_degree
    (D : DegreeData G) [IsTopologicalGroup G]
    (K : FiniteResidueAbstractField D) (L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.field.toSubgroup) (s : G)
    [hLnormal : (extensionSubgroup K.field L hLK).Normal]
    (q : K.field.toSubgroup ⧸ D.extensionInertiaWithin K.field L hLK) :
    D.extensionNormalizedDegree
        (K.conjugate s : D.FiniteResidueAbstractField)
        (conjugateClosedSubgroup L s)
        (conjugateClosedSubgroup_mono hLK s)
        (D.finiteReciprocityNaturalityFrobeniusConjugationEquiv K.field L hLK s q) =
      D.extensionNormalizedDegree K L hLK q := by
  refine Quotient.inductionOn' q ?_
  intro k
  change D.normalizedDegree (K.conjugate s)
      (conjugateSubgroupEquiv K.field s k) =
    D.normalizedDegree K k
  exact D.finiteReciprocityNaturalityNormalizedDegree_conjugateSubgroupEquiv
    K s k

/-- Conjugation transports positive Frobenius lifts without changing their
exponent. -/
def finiteReciprocityNaturalityFrobeniusConjugationLift
    (D : DegreeData G) [IsTopologicalGroup G]
    (K : FiniteResidueAbstractField D) (L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.field.toSubgroup) (s : G)
    [hLnormal : (extensionSubgroup K.field L hLK).Normal]
    (σ : D.FrobeniusElements K L hLK) :
    D.FrobeniusElements (K.conjugate s : D.FiniteResidueAbstractField)
      (conjugateClosedSubgroup L s)
      (conjugateClosedSubgroup_mono hLK s) := by
  let n := D.frobeniusExponent K L hLK σ
  refine ⟨D.finiteReciprocityNaturalityFrobeniusConjugationEquiv K.field L hLK s σ.1,
    n, D.frobeniusExponent_pos K L hLK σ, ?_⟩
  rw [D.finiteReciprocityNaturalityFrobeniusConjugationEquiv_degree]
  exact D.extensionNormalizedDegree_frobenius_eq_pow K L hLK σ

/-- The Frobenius conjugation lift has the stated ambient coercion. -/
@[simp]
theorem finiteReciprocityNaturalityFrobeniusConjugationLift_coe
    (D : DegreeData G) [IsTopologicalGroup G]
    (K : FiniteResidueAbstractField D) (L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.field.toSubgroup) (s : G)
    [hLnormal : (extensionSubgroup K.field L hLK).Normal]
    (σ : D.FrobeniusElements K L hLK) :
    (D.finiteReciprocityNaturalityFrobeniusConjugationLift K L hLK s σ).1 =
      D.finiteReciprocityNaturalityFrobeniusConjugationEquiv K.field L hLK s σ.1 := by
  rfl

/-- The Frobenius conjugation lift preserves the selected exponent. -/
@[simp]
theorem finiteReciprocityNaturalityFrobeniusConjugationLift_exponent
    (D : DegreeData G) [IsTopologicalGroup G]
    (K : FiniteResidueAbstractField D) (L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.field.toSubgroup) (s : G)
    [hLnormal : (extensionSubgroup K.field L hLK).Normal]
    (σ : D.FrobeniusElements K L hLK) :
    D.frobeniusExponent (K.conjugate s : D.FiniteResidueAbstractField)
        (conjugateClosedSubgroup L s)
        (conjugateClosedSubgroup_mono hLK s)
        (D.finiteReciprocityNaturalityFrobeniusConjugationLift K L hLK s σ) =
      D.frobeniusExponent K L hLK σ := by
  apply proCIntegerOne_pow_nat_injective
  calc
    (Multiplicative.ofAdd (1 : ZHat)) ^
        D.frobeniusExponent
          (K.conjugate s : D.FiniteResidueAbstractField)
          (conjugateClosedSubgroup L s)
          (conjugateClosedSubgroup_mono hLK s)
          (D.finiteReciprocityNaturalityFrobeniusConjugationLift K L hLK s σ) =
      D.extensionNormalizedDegree
        (K.conjugate s : D.FiniteResidueAbstractField)
        (conjugateClosedSubgroup L s)
        (conjugateClosedSubgroup_mono hLK s)
        (D.finiteReciprocityNaturalityFrobeniusConjugationLift K L hLK s σ).1 :=
      (D.extensionNormalizedDegree_frobenius_eq_pow
        (K.conjugate s : D.FiniteResidueAbstractField)
        (conjugateClosedSubgroup L s)
        (conjugateClosedSubgroup_mono hLK s)
        _).symm
    _ = D.extensionNormalizedDegree K L hLK σ.1 := by
      rw [D.finiteReciprocityNaturalityFrobeniusConjugationLift_coe,
        D.finiteReciprocityNaturalityFrobeniusConjugationEquiv_degree]
    _ = (Multiplicative.ofAdd (1 : ZHat)) ^
        D.frobeniusExponent K L hLK σ :=
      D.extensionNormalizedDegree_frobenius_eq_pow K L hLK σ

section ConjugateFrobeniusQuotients

theorem finiteReciprocityNaturalityConjugateInertia_normal
    (D : DegreeData G) [IsTopologicalGroup G]
    (K : FiniteResidueAbstractField D) (L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.field.toSubgroup) (s : G)
    [hLnormal : (extensionSubgroup K.field L hLK).Normal] :
    (D.extensionInertiaWithin (K.conjugate s).field
      (conjugateClosedSubgroup L s)
      (conjugateClosedSubgroup_mono hLK s)).Normal :=
  D.extensionInertiaWithin_normal
    (K.conjugate s).field (conjugateClosedSubgroup L s)
    (conjugateClosedSubgroup_mono hLK s)
    (hLnormal := D.finiteReciprocityNaturalityFiniteResidueConjugate_normal
      K L hLK s (hLnormal := hLnormal))

attribute [local instance] finiteReciprocityNaturalityConjugateInertia_normal


end ConjugateFrobeniusQuotients

end DegreeData

end GroupOnly

section Representation

/-! Mathlib's `Rep ℤ G` forces its representation-bearing group `G` to `Type 0`. -/
variable {G : IntegralRepGroupType} [Group G] [TopologicalSpace G]

namespace DegreeData

section ConjugateFiniteNormQuotient

@[instance_reducible]
def finiteReciprocityNaturalityConjugateNormAddZero
    (A : Rep ℤ G) [IsTopologicalGroup G]
    (K : FiniteAbstractField G) (L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.field.toSubgroup) (s : G)
    [hLfinite : Finite
      (K.field.toSubgroup ⧸ extensionSubgroup K.field L hLK)] :=
  letI : Finite
      ((K.conjugate s).field.toSubgroup ⧸
        extensionSubgroup (K.conjugate s).field (conjugateClosedSubgroup L s)
          (conjugateClosedSubgroup_mono hLK s)) :=
    finite_conjugateExtension K.field L hLK s (hLfinite := hLfinite)
  show AddZero (FiniteNormQuotient A (K.conjugate s).field
    (conjugateClosedSubgroup L s) (conjugateClosedSubgroup_mono hLK s)) from
    (finiteNormQuotientAddCommGroup A (K.conjugate s).field
      (conjugateClosedSubgroup L s)
      (conjugateClosedSubgroup_mono hLK s)).toAddZeroClass.toAddZero

attribute [local instance] finiteReciprocityNaturalityConjugateNormAddZero


end ConjugateFiniteNormQuotient

end DegreeData

end Representation

end

end ClassFormation
end

section
-- module Solutions.OAIQ244_DUKE.AbstractClassFieldTheory_Reciprocity_Construction_MainTransferFrobeniusGeometry
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 400000
attribute [-instance] _root_.ClassFormation.FiniteGaloisSubextension.extensionSubgroup_over_intermediate_normalInstance _root_.ClassFormation.FiniteGaloisSubextension.intermediateField_normalInstance _root_.ClassFormation.instIsAddTorsionFreeZHat _root_.ClassFormation.instIsMulTorsionFreeMultiplicativeZHat _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.DiscreteNthRootsSubgroup.instTopologicalSpaceSubtypeUnitsMemSubgroup _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.KummerTheory.finite_finsupp_nsmulQuotient _root_.LocalClassFieldTheory.baseFixingExtensionQuotient_finite _root_.LocalClassFieldTheory.extensionSubgroupBase_normal _root_.LocalClassFieldTheory.finiteGaloisExtensionSubgroupOfEmbedding_normal _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitQuotientCarrier_finite _root_.LocalFieldTheory.DiscreteValuationField.finite_padicInt_finPi_nsmulQuotient _root_.LocalFieldTheory.DiscreteValuationField.finite_padicInt_pi_nsmulQuotient_of_coprime _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_multiplicative_nthPowerQuotient _root_.LocalFieldTheory.finite_nsmulAddQuotient_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.LubinTate.compatibleGroupFamiliesGroup _root_.OAI.PrimeDegreePackets.boundedRealFields_finite _root_.OAI.PrimeDegreePackets.diagonalLogAction _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.OAI.PrimeDegreePackets.xT2Space _root_.RamificationTheory.HilbertRamification.ValuationSubring.inertiaGroup_normal _root_.RamificationTheory.HilbertRamification.ValuationSubring.ramificationGroupInInertiaAut_normal _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.RelativeIdeleGroup.relativeIdeleMulAction _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.LocalClassFieldTheory.intrinsicAbsoluteGaloisT2 _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteIdeleGroupIsTopologicalGroup _root_.finiteLocalUnitsOpen _root_.ideleGroupIsTopologicalGroup
attribute [-simp] _root_.ClassFormation.FiniteAbelianSubextension.extensionQuotientMk_apply _root_.ClassFormation.cyclicNormClassHom_apply _root_.ClassFormation.extensionFixedRepresentationEquiv_apply_coe _root_.ClassFormation.extensionFixedRepresentationEquiv_symm_apply_coe _root_.ClassFormation.toZModPow_zHatToPadicInt _root_.ClassFormation.zHatReductionRingHom_apply _root_.ClassFormation.zHatRingEquivProfiniteIntegerPrimeProduct_apply _root_.ClassFormation.zHatToPadicInt_intCast _root_.ClassFormation.zHatToProfiniteIntegerPrimeProduct_apply _root_.ClassFormation.zHatToProfiniteIntegerPrimeProduct_intCast _root_.ClassFormation.zHatUnitsContinuousMulEquivPrimeProduct_coe_apply _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.IsDiscreteValuationRing.addVal_ringEquiv _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.KummerTheory.torsionQuotientEquivOfZHatMulDecomposition_mk _root_.KummerTheory.zHatUnitsContinuousMulEquivPrimeProduct_rationalCyclotomicCharacter _root_.LocalClassFieldTheory.baseFixingExtensionQuotientEquivAmbient_mk _root_.LocalClassFieldTheory.finiteResidueFrobeniusFromZHat_apply _root_.LocalClassFieldTheory.finiteResidueFrobeniusFromZHat_one _root_.LocalClassFieldTheory.residueAbsoluteDegreeIn_frobenius _root_.LocalClassFieldTheory.residueAbsoluteFrobenius_one _root_.LocalClassFieldTheory.residueFrobeniusToLimit_apply_component _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.LocalFieldTheory.residueField_algebraMap_residue _root_.OAI.PrimeDegreePackets.ThetaConstruction.schwartzCM_apply _root_.infinitePlace_mult_smul
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

/-!
# Transfer--norm Frobenius geometry

For a finite Galois extension and an intermediate field, this module builds the
Frobenius-side subgroup and orbit equivalences used in transfer--norm
naturality.  The reusable orbit and double-coset constructions are isolated in
`DoubleCosetOrbitGeometry`.
-/

universe u

namespace ClassFormation

open KummerTheory
open CyclicCohomology
open CategoryTheory

noncomputable section

open scoped BigOperators
open MulAction

section transferFrobeniusGeometry

variable {G : Type u} [Group G] [TopologicalSpace G]

/-- The absolute group of an intermediate field, identified with its
literal copy inside the absolute group of the base field. -/
noncomputable def transferNormNaturalityIntermediateAbsoluteEquiv
    (K K' : ClosedSubgroup G)
    (hK'K : K'.toSubgroup ≤ K.toSubgroup) :
    K'.toSubgroup ≃* extensionSubgroup K K' hK'K :=
  MulEquiv.ofBijective
    ((Subgroup.inclusion hK'K).codRestrict
      (extensionSubgroup K K' hK'K) (fun k' => k'.2))
    ⟨fun _ _ h => Subtype.ext (congrArg (fun z => z.1.1) h), by
      rintro ⟨k, hk'⟩
      let k' : K'.toSubgroup := ⟨k.1, hk'⟩
      exact ⟨k', Subtype.ext rfl⟩⟩

/-- The absolute intermediate-field equivalence evaluates by the underlying transfer map. -/
@[simp]
theorem transferNormNaturalityIntermediateAbsoluteEquiv_apply
    (K K' : ClosedSubgroup G)
    (hK'K : K'.toSubgroup ≤ K.toSubgroup)
    (k' : K'.toSubgroup) :
    ((transferNormNaturalityIntermediateAbsoluteEquiv K K' hK'K k').1 : G) = k'.1 :=
  rfl

/-- Normality of `L | K` restricts to every intermediate field `K'`. -/
theorem transferNormNaturality_intermediateExtension_normal
    (K K' L : ClosedSubgroup G)
    (hLK' : L.toSubgroup ≤ K'.toSubgroup)
    (hK'K : K'.toSubgroup ≤ K.toSubgroup)
    [hLnormal : (extensionSubgroup K L (hLK'.trans hK'K)).Normal] :
    (extensionSubgroup K' L hLK').Normal := by
  have hcomap : extensionSubgroup K' L hLK' =
      (extensionSubgroup K L (hLK'.trans hK'K)).comap
        (Subgroup.inclusion hK'K) := by
    ext k'
    rw [Subgroup.mem_comap, mem_extensionSubgroup_iff,
      mem_extensionSubgroup_iff]
    rfl
  rw [hcomap]
  exact hLnormal.comap (Subgroup.inclusion hK'K)

namespace DegreeData

/-- The restriction map on the infinite Frobenius quotients is injective
when the top field is unchanged. -/
theorem transferNormNaturalityFrobeniusTowerMap_injective
    (D : DegreeData G) [IsTopologicalGroup G]
    (E : FiniteResidueAbstractExtension D) (L : ClosedSubgroup G)
    (hL : L.toSubgroup ≤ E.field.field.toSubgroup)
    [hLnormal :
      (extensionSubgroup E.base.field L (hL.trans E.below)).Normal]
    [hL'normal : (extensionSubgroup E.field.field L hL).Normal] :
    Function.Injective
      (D.finiteReciprocityNaturalityFrobeniusTowerMap
        E.base.field E.field.field L L
        (hL.trans E.below) hL E.below le_rfl) := by
  intro x y
  refine QuotientGroup.induction_on x ?_
  intro k'
  refine QuotientGroup.induction_on y ?_
  intro l' h
  apply QuotientGroup.eq.mpr
  have hmem :
      (Subgroup.inclusion E.below k')⁻¹ * Subgroup.inclusion E.below l' ∈
        D.extensionInertiaWithin E.base.field L (hL.trans E.below) :=
    QuotientGroup.eq.mp h
  constructor
  · apply (mem_extensionSubgroup_iff E.field.field L hL (k'⁻¹ * l')).2
    have hG := (mem_extensionSubgroup_iff E.base.field L
      (hL.trans E.below)
      ((Subgroup.inclusion E.below k')⁻¹ *
        Subgroup.inclusion E.below l')).1 hmem.1
    simpa using hG
  · have hI := hmem.2
    change D.degree (((Subgroup.inclusion E.below k')⁻¹ *
      Subgroup.inclusion E.below l' : E.base.field.toSubgroup) : G) = 1 at hI
    change D.degree ((k'⁻¹ * l' : E.field.field.toSubgroup) : G) = 1
    exact hI

/-- The copy of `G(\widetilde L/K')` inside
`G(\widetilde L/K)`.  This is the subgroup `H` used in the classical
double-coset proof of transfer--norm naturality. -/
def transferNormNaturalityFrobeniusIntermediateSubgroup
    (D : DegreeData G) [IsTopologicalGroup G]
    (E : FiniteResidueAbstractExtension D) (L : ClosedSubgroup G)
    (hL : L.toSubgroup ≤ E.field.field.toSubgroup)
    [hLnormal :
      (extensionSubgroup E.base.field L (hL.trans E.below)).Normal]
    [hL'normal : (extensionSubgroup E.field.field L hL).Normal] :
    Subgroup (E.base.field.toSubgroup ⧸
      D.extensionInertiaWithin E.base.field L (hL.trans E.below)) :=
  (D.finiteReciprocityNaturalityFrobeniusTowerMap
    E.base.field E.field.field L L
    (hL.trans E.below) hL E.below le_rfl).range

/-- The subgroup above is also the image of `G_K'` under the quotient
projection `G_K → G(\widetilde L/K)`. -/
theorem transferNormNaturalityFrobeniusIntermediateSubgroup_eq_map
    (D : DegreeData G) [IsTopologicalGroup G]
    (E : FiniteResidueAbstractExtension D) (L : ClosedSubgroup G)
    (hL : L.toSubgroup ≤ E.field.field.toSubgroup)
    [hLnormal :
      (extensionSubgroup E.base.field L (hL.trans E.below)).Normal]
    [hL'normal : (extensionSubgroup E.field.field L hL).Normal] :
    D.transferNormNaturalityFrobeniusIntermediateSubgroup E L hL =
      (extensionSubgroup E.base.field E.field.field E.below).map
        (QuotientGroup.mk'
          (D.extensionInertiaWithin E.base.field L
            (hL.trans E.below))) := by
  ext q
  constructor
  · rintro ⟨x, rfl⟩
    refine QuotientGroup.induction_on x ?_
    intro k'
    refine ⟨Subgroup.inclusion E.below k', ?_, rfl⟩
    exact k'.2
  · rintro ⟨k, hk', rfl⟩
    let k' : E.field.field.toSubgroup := ⟨k.1, hk'⟩
    refine ⟨QuotientGroup.mk k', ?_⟩
    change QuotientGroup.mk (Subgroup.inclusion E.below k') =
      QuotientGroup.mk k
    rfl

/-- Quotient projection maps the literal absolute subgroup belonging to
`K'` onto its copy `H` inside `G(\widetilde L/K)`. -/
noncomputable def transferNormNaturalityIntermediateToFrobeniusSubgroup
    (D : DegreeData G) [IsTopologicalGroup G]
    (E : FiniteResidueAbstractExtension D) (L : ClosedSubgroup G)
    (hL : L.toSubgroup ≤ E.field.field.toSubgroup)
    [hLnormal :
      (extensionSubgroup E.base.field L (hL.trans E.below)).Normal]
    [hL'normal : (extensionSubgroup E.field.field L hL).Normal] :
    extensionSubgroup E.base.field E.field.field E.below →*
      D.transferNormNaturalityFrobeniusIntermediateSubgroup E L hL := by
  refine ((QuotientGroup.mk'
    (D.extensionInertiaWithin E.base.field L (hL.trans E.below))).comp
      (extensionSubgroup E.base.field E.field.field E.below).subtype).codRestrict
        (D.transferNormNaturalityFrobeniusIntermediateSubgroup E L hL) ?_
  intro m
  change QuotientGroup.mk m.1 ∈
    D.transferNormNaturalityFrobeniusIntermediateSubgroup E L hL
  rw [D.transferNormNaturalityFrobeniusIntermediateSubgroup_eq_map
    E L hL]
  exact ⟨m.1, m.2, rfl⟩

/-- The map from the intermediate quotient onto the Frobenius subgroup is surjective. -/
theorem transferNormNaturalityIntermediateToFrobeniusSubgroup_surjective
    (D : DegreeData G) [IsTopologicalGroup G]
    (E : FiniteResidueAbstractExtension D) (L : ClosedSubgroup G)
    (hL : L.toSubgroup ≤ E.field.field.toSubgroup)
    [hLnormal :
      (extensionSubgroup E.base.field L (hL.trans E.below)).Normal]
    [hL'normal : (extensionSubgroup E.field.field L hL).Normal] :
    Function.Surjective
      (D.transferNormNaturalityIntermediateToFrobeniusSubgroup
        E L hL) := by
  intro h
  have hh : h.1 ∈
      (extensionSubgroup E.base.field E.field.field E.below).map
      (QuotientGroup.mk'
        (D.extensionInertiaWithin E.base.field L (hL.trans E.below))) := by
    rw [← D.transferNormNaturalityFrobeniusIntermediateSubgroup_eq_map
      E L hL]
    exact h.2
  obtain ⟨m, hm, hval⟩ := hh
  refine ⟨⟨m, hm⟩, ?_⟩
  apply Subtype.ext
  unfold transferNormNaturalityIntermediateToFrobeniusSubgroup
  simpa only [MonoidHom.codRestrict_apply, MonoidHom.comp_apply,
    Subgroup.subtype_apply] using hval

/-- The intermediate-to-Frobenius map has the stated value on each representative. -/
@[simp]
theorem transferNormNaturalityIntermediateToFrobeniusSubgroup_apply
    (D : DegreeData G) [IsTopologicalGroup G]
    (E : FiniteResidueAbstractExtension D) (L : ClosedSubgroup G)
    (hL : L.toSubgroup ≤ E.field.field.toSubgroup)
    [hLnormal :
      (extensionSubgroup E.base.field L (hL.trans E.below)).Normal]
    [hL'normal : (extensionSubgroup E.field.field L hL).Normal]
    (m : extensionSubgroup E.base.field E.field.field E.below) :
    (D.transferNormNaturalityIntermediateToFrobeniusSubgroup
      E L hL m).1 =
        (QuotientGroup.mk m.1 : E.base.field.toSubgroup ⧸
          D.extensionInertiaWithin E.base.field L (hL.trans E.below)) := by
  rfl

/-- The canonical coset equivalence from `G_K/G_Σ` to
`G(\widetilde L/K)/Γ` intertwines the two copies of the `K'`-action. -/
theorem frobeniusFixedCosetClosureEquiv_equivariant
    (D : DegreeData G) [IsTopologicalGroup G]
    (E : FiniteResidueAbstractExtension D) (L : ClosedSubgroup G)
    (hL : L.toSubgroup ≤ E.field.field.toSubgroup)
    [hLnormal :
      (extensionSubgroup E.base.field L (hL.trans E.below)).Normal]
    [hL'normal : (extensionSubgroup E.field.field L hL).Normal]
    (σ : D.FrobeniusElements E.base L (hL.trans E.below))
    (m : extensionSubgroup E.base.field E.field.field E.below)
    (x : E.base.field.toSubgroup ⧸ extensionSubgroup E.base.field
      (D.frobeniusFixedField E.base L (hL.trans E.below) σ)
      (D.frobeniusFixedField_le E.base L (hL.trans E.below) σ)) :
    D.frobeniusFixedCosetClosureEquiv E.base L (hL.trans E.below) σ (m • x) =
      (D.transferNormNaturalityIntermediateToFrobeniusSubgroup
        E L hL m) •
        D.frobeniusFixedCosetClosureEquiv E.base L
          (hL.trans E.below) σ x := by
  refine Quotient.inductionOn' x ?_
  intro k
  change QuotientGroup.mk (QuotientGroup.mk (m.1 * k)) =
    QuotientGroup.mk
      ((D.transferNormNaturalityIntermediateToFrobeniusSubgroup
        E L hL m).1 * QuotientGroup.mk k)
  rw [D.transferNormNaturalityIntermediateToFrobeniusSubgroup_apply]
  rfl

/-- `H` has finite index in `G(\widetilde L/K)`, with no normality
assumption on the intermediate extension `K'/K`. -/
theorem transferNormNaturalityFrobeniusIntermediateFiniteIndex
    (D : DegreeData G) [IsTopologicalGroup G]
    (R : FiniteResidueAbstractExtension D) (L : ClosedSubgroup G)
    (hL : L.toSubgroup ≤ R.field.field.toSubgroup)
    [hLnormal :
      (extensionSubgroup R.base.field L (hL.trans R.below)).Normal]
    [hL'normal : (extensionSubgroup R.field.field L hL).Normal] :
    (D.transferNormNaturalityFrobeniusIntermediateSubgroup R L hL).FiniteIndex := by
  rw [D.transferNormNaturalityFrobeniusIntermediateSubgroup_eq_map
    R L hL]
  let I := D.extensionInertiaWithin R.base.field L (hL.trans R.below)
  let M := extensionSubgroup R.base.field R.field.field R.below
  have hIM : I ≤ M := by
    intro k hk
    apply (mem_extensionSubgroup_iff
      R.base.field R.field.field R.below k).2
    exact hL ((mem_extensionSubgroup_iff R.base.field L
      (hL.trans R.below) k).1 hk.1)
  let p := QuotientGroup.mk' I
  have hker : p.ker ≤ M := by
    simpa [p] using hIM
  let : M.FiniteIndex := Subgroup.finiteIndex_of_finite_quotient
  rw [Subgroup.finiteIndex_iff,
    M.index_map_eq (QuotientGroup.mk'_surjective I) hker]
  exact Subgroup.FiniteIndex.index_ne_zero

/-- The copy of `G(\widetilde L/K')` is closed in
`G(\widetilde L/K)`. -/
theorem transferNormNaturalityFrobeniusIntermediate_isClosed
    (D : DegreeData G) [IsTopologicalGroup G] [CompactSpace G] [T2Space G]
    (E : FiniteResidueAbstractExtension D) (L : ClosedSubgroup G)
    (hL : L.toSubgroup ≤ E.field.field.toSubgroup)
    [hLnormal :
      (extensionSubgroup E.base.field L (hL.trans E.below)).Normal]
    [hL'normal : (extensionSubgroup E.field.field L hL).Normal] :
    IsClosed (D.transferNormNaturalityFrobeniusIntermediateSubgroup
      E L hL : Set
        (E.base.field.toSubgroup ⧸ D.extensionInertiaWithin E.base.field L
          (hL.trans E.below))) := by
  let : CompactSpace E.field.field.toSubgroup :=
    isCompact_iff_compactSpace.mp E.field.field.isClosed'.isCompact
  let : IsClosed
      (D.extensionInertiaWithin E.field.field L hL :
        Set E.field.field.toSubgroup) :=
    D.extensionInertiaWithin_isClosed E.field L hL
  let : IsClosed (D.extensionInertiaWithin E.base.field L
      (hL.trans E.below) : Set E.base.field.toSubgroup) :=
    D.extensionInertiaWithin_isClosed E.base L (hL.trans E.below)
  let f := D.finiteReciprocityNaturalityFrobeniusTowerMapContinuous
    E.base.field E.field.field L L
    (hL.trans E.below) hL E.below le_rfl
  change IsClosed (Set.range f)
  have hrange : Set.range f = Set.range f.toContinuousMap := by
    ext y
    constructor <;> rintro ⟨x, rfl⟩ <;> exact ⟨x, rfl⟩
  rw [hrange]
  simpa only [Set.image_univ] using
    (isCompact_univ.image f.continuous).isClosed

/-- The transfer-orbit index set
`⟨σ⟩ \ G(\widetilde L/K) / H` is canonically the norm double-coset
index set `G_K' \ G_K / G_Σ`.  The equivalence is inversion of double
cosets, followed by passage from powers of `σ` to their closure `Γ` and
the canonical identification `G_K/G_Σ ≃ G(\widetilde L/K)/Γ`. -/
noncomputable def transferNormNaturalityTransferNormOrbitEquiv
    (D : DegreeData G) [IsTopologicalGroup G] [CompactSpace G] [T2Space G]
    (E : FiniteResidueAbstractExtension D) (L : ClosedSubgroup G)
    (hL : L.toSubgroup ≤ E.field.field.toSubgroup)
    [hLnormal :
      (extensionSubgroup E.base.field L (hL.trans E.below)).Normal]
    [hL'normal : (extensionSubgroup E.field.field L hL).Normal]
    (σ : D.FrobeniusElements E.base L (hL.trans E.below)) :
    Quotient (orbitRel (Subgroup.zpowers σ.1)
      ((E.base.field.toSubgroup ⧸ D.extensionInertiaWithin E.base.field L
        (hL.trans E.below)) ⧸
          D.transferNormNaturalityFrobeniusIntermediateSubgroup
            E L hL)) ≃
      Quotient (orbitRel
        (extensionSubgroup E.base.field E.field.field E.below)
        (E.base.field.toSubgroup ⧸ extensionSubgroup E.base.field
          (D.frobeniusFixedField E.base L (hL.trans E.below) σ)
          (D.frobeniusFixedField_le E.base L
            (hL.trans E.below) σ))) := by
  let P := E.base.field.toSubgroup ⧸ D.extensionInertiaWithin E.base.field L
    (hL.trans E.below)
  let H := D.transferNormNaturalityFrobeniusIntermediateSubgroup E L hL
  let M := extensionSubgroup E.base.field E.field.field E.below
  let Γ := D.frobeniusClosure E.base L (hL.trans E.below) σ
  let S := D.frobeniusFixedField E.base L (hL.trans E.below) σ
  let hSK := D.frobeniusFixedField_le E.base L (hL.trans E.below) σ
  let f : M →* H := D.transferNormNaturalityIntermediateToFrobeniusSubgroup
    E L hL
  let e := D.frobeniusFixedCosetClosureEquiv
    E.base L (hL.trans E.below) σ
  letI : H.FiniteIndex :=
    D.transferNormNaturalityFrobeniusIntermediateFiniteIndex E L hL
  have hHclosed : IsClosed (H : Set P) :=
    D.transferNormNaturalityFrobeniusIntermediate_isClosed E L hL
  have hΓ :
      (closedSubgroupGenerated ({σ.1} : Set P)).toSubgroup = Γ.toSubgroup := by
    simp [Γ, DegreeData.frobeniusClosure]
  let eΓ : P ⧸ (closedSubgroupGenerated ({σ.1} : Set P)).toSubgroup ≃
      P ⧸ Γ.toSubgroup := Subgroup.quotientEquivOfEq hΓ
  have heΓ (h : H)
      (x : P ⧸ (closedSubgroupGenerated ({σ.1} : Set P)).toSubgroup) :
      eΓ (h • x) = h • eΓ x := by
    refine Quotient.inductionOn' x ?_
    intro p
    rfl
  let eΓorbit := orbitQuotientEquivOfSurjectiveEquivariant
    (MonoidHom.id H) Function.surjective_id eΓ heΓ
  have hf : Function.Surjective f :=
    D.transferNormNaturalityIntermediateToFrobeniusSubgroup_surjective
      E L hL
  have he (m : M)
      (x : E.base.field.toSubgroup ⧸ extensionSubgroup E.base.field S hSK) :
      e (m • x) = f m • e x := by
    exact D.frobeniusFixedCosetClosureEquiv_equivariant
      E L hL σ m x
  let eAction := orbitQuotientEquivOfSurjectiveEquivariant f hf e he
  exact (orbitQuotientSwapEquiv (Subgroup.zpowers σ.1) H).trans
    ((orbitQuotientClosedCyclicEquiv H hHclosed σ.1).trans
      (eΓorbit.trans eAction.symm))

/-- The transfer-norm orbit equivalence sends quotient representatives to their norm orbits. -/
@[simp]
theorem transferNormNaturalityTransferNormOrbitEquiv_mk
    (D : DegreeData G) [IsTopologicalGroup G] [CompactSpace G] [T2Space G]
    (E : FiniteResidueAbstractExtension D) (L : ClosedSubgroup G)
    (hL : L.toSubgroup ≤ E.field.field.toSubgroup)
    [hLnormal :
      (extensionSubgroup E.base.field L (hL.trans E.below)).Normal]
    [hL'normal : (extensionSubgroup E.field.field L hL).Normal]
    (σ : D.FrobeniusElements E.base L (hL.trans E.below))
    (k : E.base.field.toSubgroup) :
    D.transferNormNaturalityTransferNormOrbitEquiv E L hL σ
        (Quotient.mk'' (QuotientGroup.mk
          (QuotientGroup.mk k : E.base.field.toSubgroup ⧸
            D.extensionInertiaWithin E.base.field L (hL.trans E.below)) :
          (E.base.field.toSubgroup ⧸ D.extensionInertiaWithin E.base.field L
            (hL.trans E.below)) ⧸
              D.transferNormNaturalityFrobeniusIntermediateSubgroup
                E L hL)) =
      Quotient.mk'' (QuotientGroup.mk k⁻¹ :
        E.base.field.toSubgroup ⧸ extensionSubgroup E.base.field
          (D.frobeniusFixedField E.base L (hL.trans E.below) σ)
          (D.frobeniusFixedField_le E.base L
            (hL.trans E.below) σ)) := by
  unfold transferNormNaturalityTransferNormOrbitEquiv
  simp only [Equiv.trans_apply, orbitQuotientSwapEquiv_mk,
    orbitQuotientClosedCyclicEquiv_mk,
    orbitQuotientEquivOfSurjectiveEquivariant_mk,
    orbitQuotientEquivOfSurjectiveEquivariant_symm_mk,
    Subgroup.quotientEquivOfEq_mk]
  apply congrArg Quotient.mk''
  exact (D.frobeniusFixedCosetClosureEquiv E.base L
    (hL.trans E.below) σ).symm_apply_apply (QuotientGroup.mk k⁻¹)

end DegreeData

end transferFrobeniusGeometry
end

end ClassFormation
end

section
-- module Solutions.OAIQ244_DUKE.AbstractClassFieldTheory_Reciprocity_Construction_MainTransferFrobenius
attribute [-instance] _root_.ClassFormation.FiniteGaloisSubextension.extensionSubgroup_over_intermediate_normalInstance _root_.ClassFormation.FiniteGaloisSubextension.intermediateField_normalInstance _root_.ClassFormation.instIsAddTorsionFreeZHat _root_.ClassFormation.instIsMulTorsionFreeMultiplicativeZHat _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.KummerTheory.finite_finsupp_nsmulQuotient _root_.LocalClassFieldTheory.baseFixingExtensionQuotient_finite _root_.LocalClassFieldTheory.extensionSubgroupBase_normal _root_.LocalClassFieldTheory.finiteGaloisExtensionSubgroupOfEmbedding_normal _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitQuotientCarrier_finite _root_.LocalFieldTheory.DiscreteValuationField.finite_nsmulAddKernel_padicInt_pi _root_.LocalFieldTheory.DiscreteValuationField.finite_padicInt_finPi_nsmulQuotient _root_.LocalFieldTheory.DiscreteValuationField.finite_padicInt_pi_nsmulQuotient_of_coprime _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_multiplicative_nthPowerKernel _root_.LocalFieldTheory.finite_multiplicative_nthPowerQuotient _root_.LocalFieldTheory.finite_nsmulAddKernel_prod _root_.LocalFieldTheory.finite_nsmulAddQuotient_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.LubinTate.compatibleGroupFamiliesGroup _root_.OAI.PrimeDegreePackets.boundedRealFields_finite _root_.OAI.PrimeDegreePackets.diagonalLogAction _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.RamificationTheory.HilbertRamification.ValuationSubring.inertiaGroup_normal _root_.RamificationTheory.HilbertRamification.ValuationSubring.ramificationGroupInInertiaAut_normal _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.RelativeIdeleGroup.principalQuotientAction _root_.RelativeIdeleGroup.relativeIdeleMulAction _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen
attribute [-simp] _root_.ClassFormation.FiniteAbelianSubextension.extensionQuotientMk_apply _root_.ClassFormation.cyclicNormClassHom_apply _root_.ClassFormation.extensionFixedRepresentationEquiv_apply_coe _root_.ClassFormation.extensionFixedRepresentationEquiv_symm_apply_coe _root_.ClassFormation.toZModPow_zHatToPadicInt _root_.ClassFormation.zHatReductionRingHom_apply _root_.ClassFormation.zHatRingEquivProfiniteIntegerPrimeProduct_apply _root_.ClassFormation.zHatToPadicInt_intCast _root_.ClassFormation.zHatToProfiniteIntegerPrimeProduct_apply _root_.ClassFormation.zHatToProfiniteIntegerPrimeProduct_intCast _root_.ClassFormation.zHatUnitsContinuousMulEquivPrimeProduct_coe_apply _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.IsDiscreteValuationRing.addVal_ringEquiv _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.KummerTheory.torsionQuotientEquivOfZHatMulDecomposition_mk _root_.KummerTheory.zHatUnitsContinuousMulEquivPrimeProduct_rationalCyclotomicCharacter _root_.LocalClassFieldTheory.baseFixingExtensionQuotientEquivAmbient_mk _root_.LocalClassFieldTheory.finiteResidueFrobeniusFromZHat_apply _root_.LocalClassFieldTheory.finiteResidueFrobeniusFromZHat_one _root_.LocalClassFieldTheory.residueAbsoluteDegreeIn_frobenius _root_.LocalClassFieldTheory.residueAbsoluteFrobenius_one _root_.LocalClassFieldTheory.residueFrobeniusToLimit_apply_component _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.LocalFieldTheory.residueField_algebraMap_residue _root_.OAI.PrimeDegreePackets.ThetaConstruction.schwartzCM_apply _root_.infinitePlace_mult_smul
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

universe u

namespace ClassFormation

open KummerTheory

open CyclicCohomology

open CategoryTheory

/-!
# The abstract reciprocity construction, transfer--norm naturality: Frobenius fibers

This module continues the geometric transfer construction with the chosen
norm-orbit representatives, fiber calculations, fixed-field arithmetic, and
the final Frobenius transfer formula.
-/

noncomputable section

open scoped BigOperators

open MulAction

section transferFrobeniusGeometry

variable {G : Type u} [Group G] [TopologicalSpace G]

namespace Internal

/-- The chosen representative of a norm orbit is the inverse of the
representative of the corresponding transfer orbit. -/
noncomputable def chosenTransferNormNaturalityNormOrbitRepresentative
    (D : DegreeData G) [IsTopologicalGroup G] [CompactSpace G] [T2Space G]
    (E : DegreeData.FiniteResidueAbstractExtension D) (L : ClosedSubgroup G)
    (hL : L.toSubgroup ≤ E.field.field.toSubgroup)
    [hLnormal :
      (extensionSubgroup E.base.field L (hL.trans E.below)).Normal]
    [hL'normal : (extensionSubgroup E.field.field L hL).Normal]
    (σ : D.FrobeniusElements E.base L (hL.trans E.below))
    (qN : Quotient (orbitRel
      (extensionSubgroup E.base.field E.field.field E.below)
      (E.base.field.toSubgroup ⧸ extensionSubgroup E.base.field
        (D.frobeniusFixedField E.base L (hL.trans E.below) σ)
        (D.frobeniusFixedField_le E.base L
          (hL.trans E.below) σ)))) :
    E.base.field.toSubgroup ⧸ extensionSubgroup E.base.field
      (D.frobeniusFixedField E.base L (hL.trans E.below) σ)
      (D.frobeniusFixedField_le E.base L (hL.trans E.below) σ) :=
  let qT := (D.transferNormNaturalityTransferNormOrbitEquiv
    E L hL σ).symm qN
  QuotientGroup.mk (Quotient.out qT.out.out)⁻¹

end Internal

end transferFrobeniusGeometry

section transferFrobeniusFibers

variable {G : Type u} [Group G] [TopologicalSpace G]

namespace DegreeData

/-- Canonical identification of the two realizations of
`G(\widetilde L/K')`. -/
noncomputable def transferNormNaturalityFrobeniusIntermediateEquiv
    (D : DegreeData G) [IsTopologicalGroup G]
    (E : FiniteResidueAbstractExtension D) (L : ClosedSubgroup G)
    (hL : L.toSubgroup ≤ E.field.field.toSubgroup)
    [hLnormal :
      (extensionSubgroup E.base.field L (hL.trans E.below)).Normal]
    [hL'normal : (extensionSubgroup E.field.field L hL).Normal] :
    (E.field.field.toSubgroup ⧸
      D.extensionInertiaWithin E.field.field L hL) ≃*
      D.transferNormNaturalityFrobeniusIntermediateSubgroup E L hL :=
  MulEquiv.ofBijective
    (D.finiteReciprocityNaturalityFrobeniusTowerMap
      E.base.field E.field.field L L
      (hL.trans E.below) hL E.below le_rfl).rangeRestrict
    ⟨fun _ _ h => D.transferNormNaturalityFrobeniusTowerMap_injective
        E L hL (congrArg Subtype.val h),
      MonoidHom.rangeRestrict_surjective _⟩

/--
Establishes the identity `(D.transferNormNaturalityFrobeniusIntermediateEquiv E L hL
(QuotientGroup.mk k')).1 = QuotientGroup.mk (Subgroup.inclusion E.below k')`.
-/
@[simp]
theorem transferNormNaturalityFrobeniusIntermediateEquiv_mk
    (D : DegreeData G) [IsTopologicalGroup G]
    (E : FiniteResidueAbstractExtension D) (L : ClosedSubgroup G)
    (hL : L.toSubgroup ≤ E.field.field.toSubgroup)
    [hLnormal :
      (extensionSubgroup E.base.field L (hL.trans E.below)).Normal]
    [hL'normal : (extensionSubgroup E.field.field L hL).Normal]
    (k' : E.field.field.toSubgroup) :
    (D.transferNormNaturalityFrobeniusIntermediateEquiv
      E L hL (QuotientGroup.mk k')).1 =
      QuotientGroup.mk (Subgroup.inclusion E.below k') := rfl

/-- A divisibility fact in `ℤ̂` used to recognize every transfer term as
a positive Frobenius element over `K'`. -/
theorem transferNormNaturality_zHat_positive_nat_of_nsmul_eq_nat
    (f N : ℕ) (hf : 0 < f) (hN : 0 < N) (z : ZHat)
    (h : f • z = N • (1 : ZHat)) :
    ∃ n : ℕ, 0 < n ∧ z = n • (1 : ZHat) := by
  have hRange : N • (1 : ZHat) ∈
      (zHatMulNat f).toAddMonoidHom.range := by
    refine ⟨z, ?_⟩
    change f • z = N • (1 : ZHat)
    exact h
  have hKer : N • (1 : ZHat) ∈
      (zHatReduction f hf).toAddMonoidHom.ker := by
    rw [← zHatMulNat_range_eq_ker_reduction f hf]
    exact hRange
  have hmod : (N : ZMod f) = 0 := by
    change zHatReduction f hf (N • (1 : ZHat)) = 0 at hKer
    rw [map_nsmul] at hKer
    have hredOne : zHatReduction f hf (1 : ZHat) = 1 := by
      rfl
    simpa [hredOne] using hKer
  have hdiv : f ∣ N := (ZMod.natCast_eq_zero_iff N f).1 hmod
  let n := N / f
  have hN_eq : N = f * n := (Nat.mul_div_cancel' hdiv).symm
  have hn : 0 < n := Nat.div_pos (Nat.le_of_dvd hN hdiv) hf
  refine ⟨n, hn, ?_⟩
  apply zHatMulNat_injective hf
  change f • z = f • (n • (1 : ZHat))
  rw [h, smul_smul, ← hN_eq]

/-- The element `τ⁻¹ σ ^ f(τ) τ` of `H` attached to one double coset in
the transfer formula on `G(\widetilde L/K)`. -/
noncomputable def transferNormNaturalityFrobeniusTransferTerm
    (D : DegreeData G) [IsTopologicalGroup G]
    (E : FiniteResidueAbstractExtension D) (L : ClosedSubgroup G)
    (hL : L.toSubgroup ≤ E.field.field.toSubgroup)
    [hLnormal :
      (extensionSubgroup E.base.field L (hL.trans E.below)).Normal]
    [hL'normal : (extensionSubgroup E.field.field L hL).Normal]
    (σ : D.FrobeniusElements E.base L (hL.trans E.below))
    (q : Quotient (orbitRel (Subgroup.zpowers σ.1)
      ((E.base.field.toSubgroup ⧸ D.extensionInertiaWithin E.base.field L
        (hL.trans E.below)) ⧸
          D.transferNormNaturalityFrobeniusIntermediateSubgroup
            E L hL))) :
    D.transferNormNaturalityFrobeniusIntermediateSubgroup E L hL := by
  let H := D.transferNormNaturalityFrobeniusIntermediateSubgroup E L hL
  exact ⟨q.out.out⁻¹ * σ.1 ^ Function.minimalPeriod (σ.1 • ·) q.out *
      q.out.out,
    QuotientGroup.out_conj_pow_minimalPeriod_mem H σ.1 q.out⟩

/-- The transfer term pulled back from `H` to
`G(\widetilde L/K')`. -/
noncomputable def transferNormNaturalityFrobeniusTransferTermPreimage
    (D : DegreeData G) [IsTopologicalGroup G]
    (E : FiniteResidueAbstractExtension D) (L : ClosedSubgroup G)
    (hL : L.toSubgroup ≤ E.field.field.toSubgroup)
    [hLnormal :
      (extensionSubgroup E.base.field L (hL.trans E.below)).Normal]
    [hL'normal : (extensionSubgroup E.field.field L hL).Normal]
    (σ : D.FrobeniusElements E.base L (hL.trans E.below))
    (q : Quotient (orbitRel (Subgroup.zpowers σ.1)
      ((E.base.field.toSubgroup ⧸ D.extensionInertiaWithin E.base.field L
        (hL.trans E.below)) ⧸
          D.transferNormNaturalityFrobeniusIntermediateSubgroup
            E L hL))) :
    E.field.field.toSubgroup ⧸ D.extensionInertiaWithin E.field.field L hL :=
  (D.transferNormNaturalityFrobeniusIntermediateEquiv E L hL).symm
    (D.transferNormNaturalityFrobeniusTransferTerm E L hL σ q)

/-- The pullback of each double-coset term has strictly positive integral
normalized degree, as asserted. -/
theorem transferNormNaturalityFrobeniusTransferTermPreimage_degree
    (D : DegreeData G) [IsTopologicalGroup G]
    (E : FiniteResidueAbstractExtension D) (L : ClosedSubgroup G)
    (hL : L.toSubgroup ≤ E.field.field.toSubgroup)
    [hLnormal :
      (extensionSubgroup E.base.field L (hL.trans E.below)).Normal]
    [hL'normal : (extensionSubgroup E.field.field L hL).Normal]
    (σ : D.FrobeniusElements E.base L (hL.trans E.below))
    (q : Quotient (orbitRel (Subgroup.zpowers σ.1)
      ((E.base.field.toSubgroup ⧸ D.extensionInertiaWithin E.base.field L
        (hL.trans E.below)) ⧸
          D.transferNormNaturalityFrobeniusIntermediateSubgroup
            E L hL))) :
    ∃ n : ℕ, 0 < n ∧
      D.extensionNormalizedDegree E.field L hL
        (D.transferNormNaturalityFrobeniusTransferTermPreimage
          E L hL σ q) =
          (Multiplicative.ofAdd (1 : ZHat)) ^ n := by
  let H := D.transferNormNaturalityFrobeniusIntermediateSubgroup E L hL
  let : H.FiniteIndex :=
    D.transferNormNaturalityFrobeniusIntermediateFiniteIndex E L hL
  let := H.fintypeQuotientOfFiniteIndex
  let m := Function.minimalPeriod (σ.1 • ·) q.out
  let N := m * D.frobeniusExponent E.base L (hL.trans E.below) σ
  let u := D.transferNormNaturalityFrobeniusTransferTermPreimage
    E L hL σ q
  let f := (E.residueDegree : ℕ)
  let : Finite (orbit (Subgroup.zpowers σ.1) q.out) :=
    Finite.of_injective Subtype.val Subtype.val_injective
  have hf : 0 < f := E.residueDegree.property
  have hm : 0 < m := by
    have hm0 : Function.minimalPeriod (σ.1 • ·) q.out ≠ 0 :=
      NeZero.ne _
    simpa [m] using Nat.pos_of_ne_zero hm0
  have hN : 0 < N := Nat.mul_pos hm
    (D.frobeniusExponent_pos E.base L (hL.trans E.below) σ)
  have hu :
      D.finiteReciprocityNaturalityFrobeniusTowerMap
          E.base.field E.field.field L L
          (hL.trans E.below) hL E.below le_rfl u =
        (D.transferNormNaturalityFrobeniusTransferTerm
          E L hL σ q).1 := by
    exact congrArg Subtype.val
      ((D.transferNormNaturalityFrobeniusIntermediateEquiv
        E L hL).apply_symm_apply
          (D.transferNormNaturalityFrobeniusTransferTerm
            E L hL σ q))
  have hconj :
      D.extensionNormalizedDegree E.base L (hL.trans E.below)
          (D.transferNormNaturalityFrobeniusTransferTerm
            E L hL σ q).1 =
        D.extensionNormalizedDegree E.base L (hL.trans E.below)
          (σ.1 ^ m) := by
    change D.extensionNormalizedDegree E.base L (hL.trans E.below)
        (q.out.out⁻¹ * σ.1 ^ m * q.out.out) = _
    rw [map_mul, map_mul, map_inv]
    simp [mul_comm]
  have hdegree : f •
      (D.extensionNormalizedDegree E.field L hL u).toAdd =
        N • (1 : ZHat) := by
    calc
      f • (D.extensionNormalizedDegree E.field L hL u).toAdd =
          (D.extensionNormalizedDegree E.base L (hL.trans E.below)
            (D.finiteReciprocityNaturalityFrobeniusTowerMap
              E.base.field E.field.field L L
              (hL.trans E.below) hL E.below le_rfl u)).toAdd := by
        symm
        exact D.finiteReciprocityNaturalityFrobeniusTowerMap_degree
          E L L (hL.trans E.below) hL le_rfl u
      _ = (D.extensionNormalizedDegree E.base L (hL.trans E.below)
          (σ.1 ^ m)).toAdd := by rw [hu, hconj]
      _ = N • (1 : ZHat) := by
        rw [map_pow,
          D.extensionNormalizedDegree_frobenius_eq_pow
            E.base L (hL.trans E.below) σ]
        change m •
            (D.frobeniusExponent E.base L (hL.trans E.below) σ •
              (1 : ZHat)) = N • (1 : ZHat)
        rw [smul_smul]
  obtain ⟨n, hn, hnEq⟩ :=
    transferNormNaturality_zHat_positive_nat_of_nsmul_eq_nat f N hf hN
      (D.extensionNormalizedDegree E.field L hL u).toAdd hdegree
  refine ⟨n, hn, ?_⟩
  apply Multiplicative.ext
  exact hnEq

/-- The actual Frobenius lift over `K'` represented by one term of the
transfer product. -/
noncomputable def transferNormNaturalityTransferFrobeniusLift
    (D : DegreeData G) [IsTopologicalGroup G]
    (E : FiniteResidueAbstractExtension D) (L : ClosedSubgroup G)
    (hL : L.toSubgroup ≤ E.field.field.toSubgroup)
    [hLnormal :
      (extensionSubgroup E.base.field L (hL.trans E.below)).Normal]
    [hL'normal : (extensionSubgroup E.field.field L hL).Normal]
    (σ : D.FrobeniusElements E.base L (hL.trans E.below))
    (q : Quotient (orbitRel (Subgroup.zpowers σ.1)
      ((E.base.field.toSubgroup ⧸ D.extensionInertiaWithin E.base.field L
        (hL.trans E.below)) ⧸
          D.transferNormNaturalityFrobeniusIntermediateSubgroup
            E L hL))) :
    D.FrobeniusElements E.field L hL :=
  ⟨D.transferNormNaturalityFrobeniusTransferTermPreimage
      E L hL σ q,
    D.transferNormNaturalityFrobeniusTransferTermPreimage_degree
      E L hL σ q⟩

/--
Establishes the identity `(D.transferNormNaturalityTransferFrobeniusLift E L hL σ q).1 =
D.transferNormNaturalityFrobeniusTransferTermPreimage E L hL σ q`.
-/
@[simp]
theorem transferNormNaturalityTransferFrobeniusLift_coe
    (D : DegreeData G) [IsTopologicalGroup G]
    (E : FiniteResidueAbstractExtension D) (L : ClosedSubgroup G)
    (hL : L.toSubgroup ≤ E.field.field.toSubgroup)
    [hLnormal :
      (extensionSubgroup E.base.field L (hL.trans E.below)).Normal]
    [hL'normal : (extensionSubgroup E.field.field L hL).Normal]
    (σ : D.FrobeniusElements E.base L (hL.trans E.below))
    (q : Quotient (orbitRel (Subgroup.zpowers σ.1)
      ((E.base.field.toSubgroup ⧸ D.extensionInertiaWithin E.base.field L
        (hL.trans E.below)) ⧸
          D.transferNormNaturalityFrobeniusIntermediateSubgroup
            E L hL))) :
    (D.transferNormNaturalityTransferFrobeniusLift
      E L hL σ q).1 =
      D.transferNormNaturalityFrobeniusTransferTermPreimage
        E L hL σ q := rfl

end DegreeData

end transferFrobeniusFibers

end

end ClassFormation
end

section
-- module Solutions.OAIQ244_DUKE.AbstractClassFieldTheory_Reciprocity_Construction_MainTransfer
attribute [-instance] _root_.ClassFormation.FiniteGaloisSubextension.extensionSubgroup_over_intermediate_normalInstance _root_.ClassFormation.FiniteGaloisSubextension.intermediateField_normalInstance _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalClassFieldTheory.baseFixingExtensionQuotient_finite _root_.LocalClassFieldTheory.extensionSubgroupBase_normal _root_.LocalClassFieldTheory.finiteGaloisExtensionSubgroupOfEmbedding_normal _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.LubinTate.compatibleGroupFamiliesGroup _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.maximalIdealPowSuccQuotModule _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.CyclicCohomology.binaryCoefficientFamilyCommGroup _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen
attribute [-simp] _root_.ClassFormation.FiniteAbelianSubextension.extensionQuotientMk_apply _root_.ClassFormation.FiniteGaloisSubextension.classFieldCandidate_field _root_.ClassFormation.cyclicNormClassHom_apply _root_.ClassFormation.extensionFixedRepresentationEquiv_apply_coe _root_.ClassFormation.extensionFixedRepresentationEquiv_symm_apply_coe _root_.ClassFormation.mem_normFilterBasis_iff _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.IsDiscreteValuationRing.addVal_ringEquiv _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.LocalClassFieldTheory.baseFixingExtensionQuotientEquivAmbient_mk _root_.LocalClassFieldTheory.baseUnitsEquivGaloisAmbientFixed_val _root_.LocalClassFieldTheory.embeddedFieldUnitsEquivGaloisFixed_coe _root_.LocalClassFieldTheory.finiteGaloisUnitsEquivAbstractFixedOfEmbedding_coe _root_.LocalClassFieldTheory.finiteGaloisUnitsEquivAbstractFixed_coe _root_.LocalClassFieldTheory.intermediateFieldUnitsEquivGaloisFixed_coe _root_.LocalClassFieldTheory.intrinsicFiniteAbstractBase_eq_base _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.LocalFieldTheory.residueField_algebraMap_residue _root_.OAI.PrimeDegreePackets.ThetaConstruction.schwartzCM_apply _root_.infinitePlace_mult_smul
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false
/-!
Constructs the transfer map for intermediate Galois quotients and relates it to Frobenius
restriction and norm naturality.
-/

universe u

namespace ClassFormation

open KummerTheory

open CyclicCohomology

noncomputable section

open CategoryTheory
open scoped BigOperators
open MulAction

section GroupOnly

variable {G : Type u} [Group G] [TopologicalSpace G]


/-- The inclusion `G(L/K') → G(L/K)` induced by `K' ⊆ K`. -/
def transferNormNaturalityIntermediateInclusion
    (K K' L : ClosedSubgroup G)
    (hLK' : L.toSubgroup ≤ K'.toSubgroup)
    (hK'K : K'.toSubgroup ≤ K.toSubgroup)
    [hLnormal : (extensionSubgroup K L (hLK'.trans hK'K)).Normal]
    [hL'normal : (extensionSubgroup K' L hLK').Normal] :
    (K'.toSubgroup ⧸ extensionSubgroup K' L hLK') →*
      (K.toSubgroup ⧸ extensionSubgroup K L (hLK'.trans hK'K)) :=
  finiteReciprocityNaturalityRestriction K K' L L (hLK'.trans hK'K) hLK'
    hK'K le_rfl

/--
Establishes the identity `transferNormNaturalityIntermediateInclusion K K' L hLK' hK'K
(QuotientGroup.mk k') = QuotientGroup.mk (Subgroup.inclusion hK'K k')`.
-/
@[simp]
theorem transferNormNaturalityIntermediateInclusion_mk
    (K K' L : ClosedSubgroup G)
    (hLK' : L.toSubgroup ≤ K'.toSubgroup)
    (hK'K : K'.toSubgroup ≤ K.toSubgroup)
    [hLnormal : (extensionSubgroup K L (hLK'.trans hK'K)).Normal]
    [hL'normal : (extensionSubgroup K' L hLK').Normal]
    (k' : K'.toSubgroup) :
    transferNormNaturalityIntermediateInclusion K K' L hLK' hK'K
        (QuotientGroup.mk k') =
      QuotientGroup.mk (Subgroup.inclusion hK'K k') :=
  rfl

/-- The inclusion of finite Galois groups attached to an intermediate field
is injective. -/
theorem transferNormNaturalityIntermediateInclusion_injective
    (K K' L : ClosedSubgroup G)
    (hLK' : L.toSubgroup ≤ K'.toSubgroup)
    (hK'K : K'.toSubgroup ≤ K.toSubgroup)
    [hLnormal : (extensionSubgroup K L (hLK'.trans hK'K)).Normal]
    [hL'normal : (extensionSubgroup K' L hLK').Normal] :
    Function.Injective
      (transferNormNaturalityIntermediateInclusion K K' L hLK' hK'K) := by
  intro x y
  refine QuotientGroup.induction_on x ?_
  intro k'
  refine QuotientGroup.induction_on y ?_
  intro l' h
  apply QuotientGroup.eq.mpr
  apply (mem_extensionSubgroup_iff K' L hLK' (k'⁻¹ * l')).2
  have hmem :
      (Subgroup.inclusion hK'K k')⁻¹ *
          Subgroup.inclusion hK'K l' ∈
        extensionSubgroup K L (hLK'.trans hK'K) :=
    QuotientGroup.eq.mp h
  have hG := (mem_extensionSubgroup_iff K L (hLK'.trans hK'K)
    ((Subgroup.inclusion hK'K k')⁻¹ *
      Subgroup.inclusion hK'K l')).1 hmem
  simpa using hG

/-- The copy of `G(L/K')` inside `G(L/K)`. -/
def transferNormNaturalityIntermediateSubgroup
    (K K' L : ClosedSubgroup G)
    (hLK' : L.toSubgroup ≤ K'.toSubgroup)
    (hK'K : K'.toSubgroup ≤ K.toSubgroup)
    [hLnormal : (extensionSubgroup K L (hLK'.trans hK'K)).Normal]
    [hL'normal : (extensionSubgroup K' L hLK').Normal] :
    Subgroup (K.toSubgroup ⧸
      extensionSubgroup K L (hLK'.trans hK'K)) :=
  (transferNormNaturalityIntermediateInclusion K K' L hLK' hK'K).range

/-- The canonical identification of `G(L/K')` with its image in
`G(L/K)`. -/
noncomputable def transferNormNaturalityIntermediateQuotientEquiv
    (K K' L : ClosedSubgroup G)
    (hLK' : L.toSubgroup ≤ K'.toSubgroup)
    (hK'K : K'.toSubgroup ≤ K.toSubgroup)
    [hLnormal : (extensionSubgroup K L (hLK'.trans hK'K)).Normal]
    [hL'normal : (extensionSubgroup K' L hLK').Normal] :
    (K'.toSubgroup ⧸ extensionSubgroup K' L hLK') ≃*
      transferNormNaturalityIntermediateSubgroup K K' L hLK' hK'K :=
  MulEquiv.ofBijective
    (transferNormNaturalityIntermediateInclusion K K' L hLK' hK'K).rangeRestrict
    ⟨fun _ _ h =>
        transferNormNaturalityIntermediateInclusion_injective K K' L hLK' hK'K
          (congrArg Subtype.val h),
      MonoidHom.rangeRestrict_surjective _⟩

/--
Establishes the identity `(transferNormNaturalityIntermediateQuotientEquiv K K' L hLK' hK'K
(QuotientGroup.mk k')).1 = QuotientGroup.mk (Subgroup.inclusion hK'K k')`.
-/
@[simp]
theorem transferNormNaturalityIntermediateQuotientEquiv_mk
    (K K' L : ClosedSubgroup G)
    (hLK' : L.toSubgroup ≤ K'.toSubgroup)
    (hK'K : K'.toSubgroup ≤ K.toSubgroup)
    [hLnormal : (extensionSubgroup K L (hLK'.trans hK'K)).Normal]
    [hL'normal : (extensionSubgroup K' L hLK').Normal]
    (k' : K'.toSubgroup) :
    (transferNormNaturalityIntermediateQuotientEquiv K K' L hLK' hK'K
      (QuotientGroup.mk k')).1 =
      QuotientGroup.mk (Subgroup.inclusion hK'K k') :=
  rfl

end GroupOnly

section Representation

/-! Mathlib's `Rep ℤ G` forces its representation-bearing group `G` to `Type 0`. -/
variable {G : IntegralRepGroupType} [Group G] [TopologicalSpace G]

namespace DegreeData

/-- The finite reciprocity equivalence factored through the maximal abelian quotient.  This
is the horizontal reciprocity arrow in transfer--norm naturality. -/
noncomputable def transferNormNaturalityAbelianizedReciprocity
    (D : DegreeData G) (A : Rep ℤ G) (v : ValuationData D A)
    [IsTopologicalGroup G] [CompactSpace G] [T2Space G]
    [TotallyDisconnectedSpace G]
    (hAxiom : v.SatisfiesUnramifiedUnitCohomology D)
    (K : FiniteAbstractField G) (L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.field.toSubgroup)
    [hLnormal : (extensionSubgroup K.field L hLK).Normal]
    [hLfinite : Finite
      (K.field.toSubgroup ⧸ extensionSubgroup K.field L hLK)] :
    Additive (Abelianization
        (K.field.toSubgroup ⧸ extensionSubgroup K.field L hLK)) →+
      FiniteNormQuotient A K.field L hLK :=
  MonoidHom.toAdditiveLeft
    (Abelianization.lift
      (AddMonoidHom.toMultiplicativeRight
        (D.finiteReciprocityHom A v hAxiom K L hLK)))

/--
Establishes the identity `D.transferNormNaturalityAbelianizedReciprocity A v hAxiom K L hLK
(Additive.ofMul (Abelianization.of q)) = D.finiteReciprocityHom A v hAxiom K L hLK (Additive.ofMul
q)`.
-/
@[simp]
theorem transferNormNaturalityAbelianizedReciprocity_of
    (D : DegreeData G) (A : Rep ℤ G) (v : ValuationData D A)
    [IsTopologicalGroup G] [CompactSpace G] [T2Space G]
    [TotallyDisconnectedSpace G]
    (hAxiom : v.SatisfiesUnramifiedUnitCohomology D)
    (K : FiniteAbstractField G) (L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.field.toSubgroup)
    [hLnormal : (extensionSubgroup K.field L hLK).Normal]
    [hLfinite : Finite
      (K.field.toSubgroup ⧸ extensionSubgroup K.field L hLK)]
    (q : K.field.toSubgroup ⧸ extensionSubgroup K.field L hLK) :
    D.transferNormNaturalityAbelianizedReciprocity A v hAxiom K L hLK
        (Additive.ofMul (Abelianization.of q)) =
      D.finiteReciprocityHom A v hAxiom K L hLK (Additive.ofMul q) := by
  exact Abelianization.lift_apply_of
    (AddMonoidHom.toMultiplicativeRight
      (D.finiteReciprocityHom A v hAxiom K L hLK)) q

end DegreeData

end Representation

section Representation

/-! Mathlib's `Rep ℤ G` forces its representation-bearing group `G` to `Type 0`. -/
variable {G : IntegralRepGroupType} [Group G] [TopologicalSpace G]

/-- The invariant carrier used by `extensionFixedRepresentation` is
canonically the ambient fixed subgroup `A_L`. -/
def transferNormNaturalityExtensionFixedEquiv
    (A : Rep ℤ G) (K L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.toSubgroup)
    (hnormal : (extensionSubgroup K L hLK).Normal) :
    (extensionFixedRepresentation A K L hLK hnormal).V ≃+
      ambientFixedAddSubgroup A L where
  toFun a := ⟨a.1, by
    intro l
    let s : extensionSubgroup K L hLK :=
      ⟨Subgroup.inclusion hLK l, l.2⟩
    exact a.2 s⟩
  invFun a := ⟨a.1, by
    rintro ⟨k, hk⟩
    exact a.2 ⟨k.1, hk⟩⟩
  left_inv _ := by rfl
  right_inv _ := by rfl
  map_add' _ _ := rfl

/--
Establishes the identity `((transferNormNaturalityExtensionFixedEquiv A K L hLK hnormal a :
ambientFixedAddSubgroup A L) : A.V) = a.1`.
-/
@[simp]
theorem transferNormNaturalityExtensionFixedEquiv_apply_coe
    (A : Rep ℤ G) (K L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.toSubgroup)
    (hnormal : (extensionSubgroup K L hLK).Normal)
    (a : (extensionFixedRepresentation A K L hLK hnormal).V) :
    ((transferNormNaturalityExtensionFixedEquiv A K L hLK hnormal a :
      ambientFixedAddSubgroup A L) : A.V) = a.1 :=
  rfl

/--
Establishes the identity `((transferNormNaturalityExtensionFixedEquiv A K L hLK hnormal).symm a).1
= a.1`.
-/
@[simp]
theorem transferNormNaturalityExtensionFixedEquiv_symm_coe
    (A : Rep ℤ G) (K L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.toSubgroup)
    (hnormal : (extensionSubgroup K L hLK).Normal)
    (a : ambientFixedAddSubgroup A L) :
    ((transferNormNaturalityExtensionFixedEquiv A K L hLK hnormal).symm a).1 =
      a.1 :=
  rfl

end Representation

section GroupOnly

variable {G : Type u} [Group G] [TopologicalSpace G]

/-- A fixed choice of right-coset representatives for the intermediate
subgroup in `G(L/K)`. -/
noncomputable def chosenTransferNormNaturalityRightTransversal
    (K K' L : ClosedSubgroup G)
    (hLK' : L.toSubgroup ≤ K'.toSubgroup)
    (hK'K : K'.toSubgroup ≤ K.toSubgroup)
    [hLnormal : (extensionSubgroup K L (hLK'.trans hK'K)).Normal]
    [hL'normal : (extensionSubgroup K' L hLK').Normal] :
    (transferNormNaturalityIntermediateSubgroup K K' L hLK' hK'K).RightTransversal :=
  ⟨Set.range Quotient.out, Subgroup.isComplement_range_right Quotient.out_eq'⟩

/-- Multiplication gives the right-coset decomposition
`G(L/K') × T ≃ G(L/K)` used. -/
noncomputable def transferNormNaturalityRightCosetProductEquiv
    (K K' L : ClosedSubgroup G)
    (hLK' : L.toSubgroup ≤ K'.toSubgroup)
    (hK'K : K'.toSubgroup ≤ K.toSubgroup)
    [hLnormal : (extensionSubgroup K L (hLK'.trans hK'K)).Normal]
    [hL'normal : (extensionSubgroup K' L hLK').Normal] :
    (K'.toSubgroup ⧸ extensionSubgroup K' L hLK') ×
        (chosenTransferNormNaturalityRightTransversal K K' L hLK' hK'K :
          Set (K.toSubgroup ⧸
            extensionSubgroup K L (hLK'.trans hK'K))) ≃
      (K.toSubgroup ⧸ extensionSubgroup K L (hLK'.trans hK'K)) :=
  (Equiv.prodCongr
      (transferNormNaturalityIntermediateQuotientEquiv K K' L hLK' hK'K).toEquiv
      (Equiv.refl _)).trans
    (chosenTransferNormNaturalityRightTransversal K K' L hLK' hK'K).2.equiv.symm

@[simp]
theorem transferNormNaturalityRightCosetProductEquiv_apply
    (K K' L : ClosedSubgroup G)
    (hLK' : L.toSubgroup ≤ K'.toSubgroup)
    (hK'K : K'.toSubgroup ≤ K.toSubgroup)
    [hLnormal : (extensionSubgroup K L (hLK'.trans hK'K)).Normal]
    [hL'normal : (extensionSubgroup K' L hLK').Normal]
    (r : K'.toSubgroup ⧸ extensionSubgroup K' L hLK')
    (t : (chosenTransferNormNaturalityRightTransversal K K' L hLK' hK'K :
      Set (K.toSubgroup ⧸
        extensionSubgroup K L (hLK'.trans hK'K)))) :
    transferNormNaturalityRightCosetProductEquiv K K' L hLK' hK'K (r, t) =
      transferNormNaturalityIntermediateInclusion K K' L hLK' hK'K r * t.1 :=
  rfl

end GroupOnly

section Representation

/-! Mathlib's `Rep ℤ G` forces its representation-bearing group `G` to `Type 0`. -/
variable {G : IntegralRepGroupType} [Group G] [TopologicalSpace G]

/-- The quotient action on the invariant carrier agrees with the relative
coset action used to define the norm. -/
theorem transferNormNaturality_relativeCosetAction_eq_extensionAction
    (A : Rep ℤ G) (K L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.toSubgroup)
    (hnormal : (extensionSubgroup K L hLK).Normal)
    (a : (extensionFixedRepresentation A K L hLK hnormal).V)
    (q : K.toSubgroup ⧸ extensionSubgroup K L hLK) :
    relativeCosetAction A K L hLK
        (transferNormNaturalityExtensionFixedEquiv A K L hLK hnormal a) q =
      ((extensionFixedRepresentation A K L hLK hnormal).ρ q a).1 := by
  let := hnormal
  refine QuotientGroup.induction_on q ?_
  intro k
  rw [relativeCosetAction_mk]
  change A.ρ k.1 a.1 =
    ((extensionFixedRepresentation A K L hLK hnormal).ρ
      (QuotientGroup.mk k) a).1
  exact (extensionFixedRepresentation_quotient_mk_apply_val
    A K L hLK a k).symm

/-- Restricting the quotient action to `G(L/K')` agrees with the relative
coset action for `L | K'`. -/
theorem transferNormNaturality_relativeCosetAction_intermediate
    (A : Rep ℤ G) (K K' L : ClosedSubgroup G)
    (hLK' : L.toSubgroup ≤ K'.toSubgroup)
    (hK'K : K'.toSubgroup ≤ K.toSubgroup)
    [hLnormal : (extensionSubgroup K L (hLK'.trans hK'K)).Normal]
    [hL'normal : (extensionSubgroup K' L hLK').Normal]
    (a : (extensionFixedRepresentation A K L
      (hLK'.trans hK'K) hLnormal).V)
    (r : K'.toSubgroup ⧸ extensionSubgroup K' L hLK') :
    relativeCosetAction A K' L hLK'
        (transferNormNaturalityExtensionFixedEquiv A K L
          (hLK'.trans hK'K) hLnormal a) r =
      ((extensionFixedRepresentation A K L
        (hLK'.trans hK'K) hLnormal).ρ
          (transferNormNaturalityIntermediateInclusion K K' L hLK' hK'K r) a).1 := by
  refine QuotientGroup.induction_on r ?_
  intro k'
  rw [relativeCosetAction_mk, transferNormNaturalityIntermediateInclusion_mk]
  change A.ρ k'.1 a.1 =
    ((extensionFixedRepresentation A K L (hLK'.trans hK'K) hLnormal).ρ
      (QuotientGroup.mk (Subgroup.inclusion hK'K k')) a).1
  exact (extensionFixedRepresentation_quotient_mk_apply_val
    A K L (hLK'.trans hK'K) a (Subgroup.inclusion hK'K k')).symm

/-- The element of `A_L` obtained by summing the conjugates indexed by a
right transversal for `G(L/K')` in `G(L/K)`.  Its `L | K'` norm is the
`L | K` norm of the original element. -/
noncomputable def transferNormNaturalityNormWitness
    (A : Rep ℤ G) (K K' L : ClosedSubgroup G)
    (hLK' : L.toSubgroup ≤ K'.toSubgroup)
    (hK'K : K'.toSubgroup ≤ K.toSubgroup)
    [hLnormal : (extensionSubgroup K L (hLK'.trans hK'K)).Normal]
    [hL'normal : (extensionSubgroup K' L hLK').Normal]
    [Finite (K.toSubgroup ⧸
      extensionSubgroup K L (hLK'.trans hK'K))]
    (a : ambientFixedAddSubgroup A L) :
    ambientFixedAddSubgroup A L := by
  let H := transferNormNaturalityIntermediateSubgroup K K' L hLK' hK'K
  let T := chosenTransferNormNaturalityRightTransversal K K' L hLK' hK'K
  letI : H.FiniteIndex := Subgroup.finiteIndex_of_finite
  letI : Fintype (T : Set (K.toSubgroup ⧸
      extensionSubgroup K L (hLK'.trans hK'K))) :=
    T.2.finite_right.fintype
  let E := extensionFixedRepresentation A K L
    (hLK'.trans hK'K) hLnormal
  let eA := transferNormNaturalityExtensionFixedEquiv A K L
    (hLK'.trans hK'K) hLnormal
  exact eA (∑ t : (T : Set _), E.ρ t.1 (eA.symm a))

theorem transferNormNaturality_extensionAction_product
    (A : Rep ℤ G) (K K' L : ClosedSubgroup G)
    (hLK' : L.toSubgroup ≤ K'.toSubgroup)
    (hK'K : K'.toSubgroup ≤ K.toSubgroup)
    [hLnormal : (extensionSubgroup K L (hLK'.trans hK'K)).Normal]
    [hL'normal : (extensionSubgroup K' L hLK').Normal]
    (a : (extensionFixedRepresentation A K L
      (hLK'.trans hK'K) hLnormal).V)
    (r : K'.toSubgroup ⧸ extensionSubgroup K' L hLK')
    (t : (chosenTransferNormNaturalityRightTransversal K K' L hLK' hK'K :
      Set (K.toSubgroup ⧸
        extensionSubgroup K L (hLK'.trans hK'K)))) :
    (extensionFixedRepresentation A K L
        (hLK'.trans hK'K) hLnormal).ρ
        (transferNormNaturalityRightCosetProductEquiv K K' L hLK' hK'K (r, t)) a =
      (extensionFixedRepresentation A K L
        (hLK'.trans hK'K) hLnormal).ρ
        (transferNormNaturalityIntermediateInclusion K K' L hLK' hK'K r)
        ((extensionFixedRepresentation A K L
          (hLK'.trans hK'K) hLnormal).ρ t.1 a) := by
  rw [transferNormNaturalityRightCosetProductEquiv_apply, map_mul]
  rfl

/-- The norm identity underlying the right vertical arrow of transfer--norm naturality.  It is the additive form of the product calculation. -/
theorem transferNormNaturality_norm_doubleCoset_formula
    (A : Rep ℤ G) (K K' L : ClosedSubgroup G)
    (hLK' : L.toSubgroup ≤ K'.toSubgroup)
    (hK'K : K'.toSubgroup ≤ K.toSubgroup)
    [hLnormal : (extensionSubgroup K L (hLK'.trans hK'K)).Normal]
    [Finite (K.toSubgroup ⧸
      extensionSubgroup K L (hLK'.trans hK'K))]
    (a : ambientFixedAddSubgroup A L) :
    letI : (extensionSubgroup K' L hLK').Normal :=
      transferNormNaturality_intermediateExtension_normal K K' L hLK' hK'K
    letI : Finite (K'.toSubgroup ⧸ extensionSubgroup K' L hLK') :=
      Finite.of_injective
        (transferNormNaturalityIntermediateInclusion K K' L hLK' hK'K)
        (transferNormNaturalityIntermediateInclusion_injective
          K K' L hLK' hK'K)
    fixedFieldInclusion A K K' hK'K
        (relativeNorm A K L (hLK'.trans hK'K) a) =
      relativeNorm A K' L hLK'
        (transferNormNaturalityNormWitness A K K' L hLK' hK'K a) := by
  let hL'normal : (extensionSubgroup K' L hLK').Normal :=
    transferNormNaturality_intermediateExtension_normal K K' L hLK' hK'K
  let hL'finite : Finite
      (K'.toSubgroup ⧸ extensionSubgroup K' L hLK') :=
    Finite.of_injective
      (transferNormNaturalityIntermediateInclusion K K' L hLK' hK'K)
      (transferNormNaturalityIntermediateInclusion_injective
        K K' L hLK' hK'K)
  let : Fintype (K.toSubgroup ⧸
      extensionSubgroup K L (hLK'.trans hK'K)) := Fintype.ofFinite _
  let : Fintype (K'.toSubgroup ⧸
      extensionSubgroup K' L hLK') := Fintype.ofFinite _
  let H := transferNormNaturalityIntermediateSubgroup K K' L hLK' hK'K
  let T := chosenTransferNormNaturalityRightTransversal K K' L hLK' hK'K
  let : H.FiniteIndex := Subgroup.finiteIndex_of_finite
  let : Fintype (T : Set (K.toSubgroup ⧸
      extensionSubgroup K L (hLK'.trans hK'K))) :=
    T.2.finite_right.fintype
  let E := extensionFixedRepresentation A K L
    (hLK'.trans hK'K) hLnormal
  let eA := transferNormNaturalityExtensionFixedEquiv A K L
    (hLK'.trans hK'K) hLnormal
  let aE := eA.symm a
  let valHom : E.V →+ A.V :=
    (ambientFixedAddSubgroup A L).subtype.comp eA.toAddMonoidHom
  apply Subtype.ext
  simp only [fixedFieldInclusion_coe, relativeNorm_apply_coe,
    relativeNormValue]
  have ha : eA aE = a := eA.apply_symm_apply a
  have hwitness :
      eA.symm (transferNormNaturalityNormWitness A K K' L hLK' hK'K a) =
        ∑ t : (T : Set (K.toSubgroup ⧸
          extensionSubgroup K L (hLK'.trans hK'K))), E.ρ t.1 aE := by
    simp [transferNormNaturalityNormWitness, T, E, eA, aE]
  have hE :
      (∑ q : K.toSubgroup ⧸
          extensionSubgroup K L (hLK'.trans hK'K), E.ρ q aE) =
        ∑ r : K'.toSubgroup ⧸ extensionSubgroup K' L hLK',
          E.ρ (transferNormNaturalityIntermediateInclusion K K' L hLK' hK'K r)
            (∑ t : (T : Set (K.toSubgroup ⧸
              extensionSubgroup K L (hLK'.trans hK'K))), E.ρ t.1 aE) := by
    calc
      (∑ q : K.toSubgroup ⧸
          extensionSubgroup K L (hLK'.trans hK'K), E.ρ q aE) =
          ∑ p : (K'.toSubgroup ⧸ extensionSubgroup K' L hLK') ×
              (T : Set (K.toSubgroup ⧸
                extensionSubgroup K L (hLK'.trans hK'K))),
            E.ρ (transferNormNaturalityRightCosetProductEquiv
              K K' L hLK' hK'K p) aE :=
        (transferNormNaturalityRightCosetProductEquiv K K' L hLK' hK'K).sum_comp
          (fun q => E.ρ q aE) |>.symm
      _ = ∑ p : (K'.toSubgroup ⧸ extensionSubgroup K' L hLK') ×
              (T : Set (K.toSubgroup ⧸
                extensionSubgroup K L (hLK'.trans hK'K))),
            E.ρ (transferNormNaturalityIntermediateInclusion
              K K' L hLK' hK'K p.1) (E.ρ p.2.1 aE) := by
        apply Fintype.sum_congr
        intro p
        exact transferNormNaturality_extensionAction_product
          A K K' L hLK' hK'K aE p.1 p.2
      _ = ∑ r : K'.toSubgroup ⧸ extensionSubgroup K' L hLK',
            ∑ t : (T : Set (K.toSubgroup ⧸
              extensionSubgroup K L (hLK'.trans hK'K))),
              E.ρ (transferNormNaturalityIntermediateInclusion
                K K' L hLK' hK'K r) (E.ρ t.1 aE) := by
        rw [Fintype.sum_prod_type]
      _ = ∑ r : K'.toSubgroup ⧸ extensionSubgroup K' L hLK',
          E.ρ (transferNormNaturalityIntermediateInclusion K K' L hLK' hK'K r)
            (∑ t : (T : Set (K.toSubgroup ⧸
              extensionSubgroup K L (hLK'.trans hK'K))), E.ρ t.1 aE) := by
        apply Fintype.sum_congr
        intro r
        rw [map_sum]
  calc
    (∑ q : K.toSubgroup ⧸
        extensionSubgroup K L (hLK'.trans hK'K),
      relativeCosetAction A K L (hLK'.trans hK'K) a q) =
        ∑ q : K.toSubgroup ⧸
          extensionSubgroup K L (hLK'.trans hK'K), (E.ρ q aE).1 := by
      apply Fintype.sum_congr
      intro q
      rw [← ha]
      exact transferNormNaturality_relativeCosetAction_eq_extensionAction
        A K L (hLK'.trans hK'K) hLnormal aE q
    _ = (∑ q : K.toSubgroup ⧸
        extensionSubgroup K L (hLK'.trans hK'K), E.ρ q aE).1 := by
      change (∑ q, valHom (E.ρ q aE)) = valHom (∑ q, E.ρ q aE)
      rw [map_sum]
    _ = (∑ r : K'.toSubgroup ⧸ extensionSubgroup K' L hLK',
        E.ρ (transferNormNaturalityIntermediateInclusion K K' L hLK' hK'K r)
          (∑ t : (T : Set (K.toSubgroup ⧸
            extensionSubgroup K L (hLK'.trans hK'K))), E.ρ t.1 aE)).1 :=
      congrArg Subtype.val hE
    _ = ∑ r : K'.toSubgroup ⧸ extensionSubgroup K' L hLK',
        (E.ρ (transferNormNaturalityIntermediateInclusion K K' L hLK' hK'K r)
          (∑ t : (T : Set (K.toSubgroup ⧸
            extensionSubgroup K L (hLK'.trans hK'K))), E.ρ t.1 aE)).1 := by
      change valHom (∑ r,
          E.ρ (transferNormNaturalityIntermediateInclusion K K' L hLK' hK'K r)
            (∑ t : (T : Set (K.toSubgroup ⧸
              extensionSubgroup K L (hLK'.trans hK'K))), E.ρ t.1 aE)) =
        ∑ r, valHom
          (E.ρ (transferNormNaturalityIntermediateInclusion K K' L hLK' hK'K r)
            (∑ t : (T : Set (K.toSubgroup ⧸
              extensionSubgroup K L (hLK'.trans hK'K))), E.ρ t.1 aE))
      rw [map_sum]
    _ = ∑ r : K'.toSubgroup ⧸ extensionSubgroup K' L hLK',
        relativeCosetAction A K' L hLK'
          (transferNormNaturalityNormWitness A K K' L hLK' hK'K a) r := by
      apply Fintype.sum_congr
      intro r
      rw [← hwitness]
      have hr := transferNormNaturality_relativeCosetAction_intermediate
        A K K' L hLK' hK'K
        (eA.symm (transferNormNaturalityNormWitness A K K' L hLK' hK'K a)) r
      calc
        _ = relativeCosetAction A K' L hLK'
            (eA (eA.symm
              (transferNormNaturalityNormWitness A K K' L hLK' hK'K a))) r := by
          simpa only [E, eA] using hr.symm
        _ = relativeCosetAction A K' L hLK'
            (transferNormNaturalityNormWitness A K K' L hLK' hK'K a) r := by
          rw [eA.apply_symm_apply]

end Representation

end

end ClassFormation
end


