-- Prove2me | Definitions.Def_OAIQ244Duke037
-- name    : OAIQ244Duke037
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-13T06:37:34.737828+00:00
-- url     : https://prove2.me/theorems/54c3d673-3fda-4b3a-93ce-98096d120936
-- title:
--   Definitions bundle OAIQ244Duke037 of the split of OpenAI, Equidistribution of Prime-Degree Torus Packets with Arbitrary Local Type
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.DukePrimeDegree.prime_degree_packet_measure_equidistribution_unconditional` and `OAI.DukePrimeDegree.prime_degree_packet_measures_tendsto_haar_unconditional`, carved from OpenAI's openai/math development (OpenAI, *Equidistribution of Prime-Degree Torus Packets with Arbitrary Local Type*, OpenAI Math Release, September 24, 2026, result family 15, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 109 declarations of OpenAI's Lean: 35 definitions, 18 instances and 56 theorems. The definitions and types are `ChosenFinitePlaceDecompositionGroup`, `ChosenFinitePlaceInducedIntegerUnits`, `ChosenFinitePlaceIsUnramified`, `ChosenFinitePlaceLocalPlaceBlock`, `ChosenFinitePlaceLocalizedCompletion`, `ChosenFinitePlaceLocalizedFieldUnits`, `ChosenFinitePlaceLocalizedIntegerUnits`, `ChosenFinitePlaceNormQuotient`, `ClassFormation.DegreeData.frobeniusFixedResidueField`, `ClassFormation.FiniteIntermediateField.quotientCard`, `ClassFormation.ValuationData.finiteUnitNorm`, `ClassFormation.ValuationData.fixedTowerCorrection`, `ClassFormation.ValuationData.fixedTowerUnitAction`, `ClassFormation.ValuationData.frobeniusFixedFieldUnitAction`, `ClassFormation.ValuationData.powerTowerCorrection`, `ClassFormation.frobeniusMultiplicativityCorrectionTerm`, `FinitePlaceLocalTensorDecompositionIntegralUnitProduct`, `LocalInductionInternal.completionAlgebra`, `LocalInductionInternal.extensionCompletionAlgebra`, `LocalInductionInternal.extensionCompletionSMul`, `LocalInductionInternal.integerAlgebra`, `LocalInductionInternal.localizedValuativeRel`, `LocalInductionInternal.localizedValued`, `chosenFinitePlaceDecompositionGroupIntegerUnitsAction`, `chosenFinitePlaceDecompositionGroupLocalUnitsAction`, `chosenFinitePlaceLocalNormSubgroup`, `decompositionGroupLocalizedIntegerUnitsAction`, `finitePlaceLocalTensorDecompositionComponent`, `finitePlaceLocalTensorDecompositionComponentRingHom`, `finitePlaceLocalTensorDecompositionIntegralUnitProductEquivPi`, `finitePlaceLocalTensorDecompositionUnitsComponent`, `finitePlaceLocalTensorDecompositionUnitsEquiv`, `localBlockFamilyAction`, `localizedCompletionFinitePlaceValuativeRel`, `localizedCompletionFinitePlaceValued`.
--
--   **Sources.** They come from these modules of lean/OAI/NumberTheory, in whole or in part: `AbstractClassFieldTheory_Reciprocity_Construction_FiniteFieldUnitMaps`, `AbstractClassFieldTheory_Reciprocity_Construction_FiniteIntermediateFieldCompositum`, `AbstractClassFieldTheory_Reciprocity_Construction_FixedTowerUnitCorrection`, `AbstractClassFieldTheory_Reciprocity_Construction_FixedTowerUnitDescent`, `AbstractClassFieldTheory_Reciprocity_Construction_FrobeniusField`, `AbstractClassFieldTheory_Reciprocity_Construction_FrobeniusFixedFieldAction`, `AbstractClassFieldTheory_Reciprocity_Construction_FrobeniusPowerFixedField`, `AbstractClassFieldTheory_Reciprocity_Construction_FrobeniusQuotientDescent`, `AbstractClassFieldTheory_Reciprocity_Construction_InfiniteUnitNormSubgroup`, `AbstractClassFieldTheory_Reciprocity_Construction_MainFiniteReciprocity`, `AbstractClassFieldTheory_Reciprocity_Construction_MainMultiplicativity_CorrectionSum`, `AbstractClassFieldTheory_Reciprocity_Construction_Universal`, `AbstractClassFieldTheory_Reciprocity_Construction_UniversalNormDescent`, `AlgebraicNumberTheory_Adele_IntegralLocalFactor`, `AlgebraicNumberTheory_Adele_IntegralTensorSupport_LocalTensorDecomposition`, `AlgebraicNumberTheory_Completion_ChosenLocalization`, `AlgebraicNumberTheory_Completion_LocalizedValuation`, `AlgebraicNumberTheory_Idele_Cohomology_Decomposition`, `AlgebraicNumberTheory_Idele_Cohomology_SPlaces_OutsideIntegralInduced_ChosenPlaceAction`, `AlgebraicNumberTheory_Idele_Cohomology_SPlaces_OutsideIntegralInduced_LocalInduction_Action`, `AlgebraicNumberTheory_Idele_Cohomology_SPlaces_OutsideIntegralInduced_LocalInduction_Spine`, `AlgebraicNumberTheory_Idele_NormApproximation_FinitePlaces`, `LocalField_NonarchimedeanLocalField_NormQuotient`.
--
--   **Imports.** It imports the bundles `OAIQ244Duke025` and `OAIQ244Duke026` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ244Duke045`, `OAIQ244Duke046`, `OAIQ244Duke048`, `OAIQ244Duke049`, `OAIQ244Duke050`, `OAIQ244Duke051` and `OAIQ244Duke052`.
-- source:
--   OpenAI, Equidistribution of Prime-Degree Torus Packets with Arbitrary Local Type, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 15; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Equidistribution-of-Prime-Degree-Torus-Packets-with-Arbitrary-Local-Type-September-24-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/NumberTheory at commit 7ef5c0c

import Mathlib
import Mathlib.Algebra.Algebra.Basic
import Mathlib.Algebra.Algebra.Pi
import Mathlib.Algebra.Algebra.Tower
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Category.ModuleCat.Basic
import Mathlib.Algebra.CharP.Lemmas
import Mathlib.Algebra.CharP.Subring
import Mathlib.Algebra.Exact.Basic
import Mathlib.Algebra.Group.Action.Basic
import Mathlib.Algebra.Group.Hom.Basic
import Mathlib.Algebra.Group.Int.TypeTags
import Mathlib.Algebra.Group.Pi.Basic
import Mathlib.Algebra.Group.Pi.Units
import Mathlib.Algebra.Group.Subgroup.Basic
import Mathlib.Algebra.Group.Subgroup.Ker
import Mathlib.Algebra.Group.Subgroup.Map
import Mathlib.Algebra.Group.Submonoid.Units
import Mathlib.Algebra.Group.TransferInstance
import Mathlib.Algebra.Group.Units.Equiv
import Mathlib.Algebra.Group.Units.Hom
import Mathlib.Algebra.Module.Equiv.Basic
import Mathlib.Algebra.Module.LinearMap.Polynomial
import Mathlib.Algebra.Module.Shrink
import Mathlib.Algebra.Module.Torsion.Basic
import Mathlib.Algebra.Module.ZLattice.Basic
import Mathlib.Algebra.Order.Hom.Units
import Mathlib.Algebra.Order.Ring.IsNonarchimedean
import Mathlib.Algebra.Order.WithTop.Untop0
import Mathlib.Algebra.Polynomial.Div
import Mathlib.Algebra.Polynomial.FieldDivision
import Mathlib.Algebra.Polynomial.Lifts
import Mathlib.Analysis.AbsoluteValue.Equivalence
import Mathlib.Analysis.Complex.Convex
import Mathlib.Analysis.Normed.Algebra.GelfandMazur
import Mathlib.Analysis.Normed.Field.Instances
import Mathlib.Analysis.Normed.Field.ProperSpace
import Mathlib.Analysis.Normed.Field.WithAbs
import Mathlib.Analysis.Normed.Module.Completion
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Normed.Unbundled.RingSeminorm
import Mathlib.Analysis.Normed.Unbundled.SpectralNorm
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Int.ModEq
import Mathlib.Data.Rat.Lemmas
import Mathlib.Data.Set.Finite.Range
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.ZMod.QuotientGroup
import Mathlib.Dynamics.BirkhoffSum.Basic
import Mathlib.FieldTheory.AbsoluteGaloisGroup
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.FieldTheory.Finite.Extension
import Mathlib.FieldTheory.Finite.GaloisField
import Mathlib.FieldTheory.Galois.Basic
import Mathlib.FieldTheory.Galois.Infinite
import Mathlib.FieldTheory.Galois.IsGaloisGroup
import Mathlib.FieldTheory.Galois.NormalBasis
import Mathlib.FieldTheory.Galois.Profinite
import Mathlib.FieldTheory.IntermediateField.Adjoin.Algebra
import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.FieldTheory.IsSepClosed
import Mathlib.FieldTheory.KrullTopology
import Mathlib.FieldTheory.Minpoly.IsConjRoot
import Mathlib.FieldTheory.Minpoly.IsIntegrallyClosed
import Mathlib.FieldTheory.Normal.Basic
import Mathlib.FieldTheory.PrimitiveElement
import Mathlib.FieldTheory.PurelyInseparable.Basic
import Mathlib.FieldTheory.Separable
import Mathlib.FieldTheory.SeparableClosure
import Mathlib.GroupTheory.Abelianization.Defs
import Mathlib.GroupTheory.Coset.Card
import Mathlib.GroupTheory.DoubleCoset
import Mathlib.GroupTheory.FiniteAbelian.Basic
import Mathlib.GroupTheory.GroupAction.Basic
import Mathlib.GroupTheory.GroupAction.Defs
import Mathlib.GroupTheory.GroupAction.Quotient
import Mathlib.GroupTheory.Index
import Mathlib.GroupTheory.Nilpotent
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.GroupTheory.QuotientGroup.Basic
import Mathlib.GroupTheory.QuotientGroup.Finite
import Mathlib.GroupTheory.SpecificGroups.Cyclic
import Mathlib.GroupTheory.Transfer
import Mathlib.LinearAlgebra.Basis.SMul
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.LinearAlgebra.Charpoly.BaseChange
import Mathlib.LinearAlgebra.Determinant
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Dimension.DivisionRing
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.LinearAlgebra.Dimension.Localization
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.FreeModule.IdealQuotient
import Mathlib.LinearAlgebra.Quotient.Pi
import Mathlib.LinearAlgebra.TensorProduct.Basis
import Mathlib.LinearAlgebra.TensorProduct.RightExactness
import Mathlib.LinearAlgebra.Trace
import Mathlib.Logic.Equiv.Fin.Rotate
import Mathlib.NumberTheory.LocalField.Basic
import Mathlib.NumberTheory.NumberField.AdeleRing
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.NumberTheory.NumberField.ClassNumber
import Mathlib.NumberTheory.NumberField.Completion.FinitePlace
import Mathlib.NumberTheory.NumberField.Completion.InfinitePlace
import Mathlib.NumberTheory.NumberField.ProductFormula
import Mathlib.NumberTheory.NumberField.Units.DirichletTheorem
import Mathlib.NumberTheory.Ostrowski
import Mathlib.NumberTheory.RamificationInertia.Galois
import Mathlib.NumberTheory.RamificationInertia.Inertia
import Mathlib.NumberTheory.RamificationInertia.Ramification
import Mathlib.RepresentationTheory.Homological.FiniteCyclic
import Mathlib.RepresentationTheory.Homological.GroupCohomology.FiniteCyclic
import Mathlib.RepresentationTheory.Homological.GroupCohomology.Hilbert90
import Mathlib.RepresentationTheory.Homological.GroupHomology.FiniteCyclic
import Mathlib.RepresentationTheory.Homological.TateCohomology.Basic
import Mathlib.RepresentationTheory.Invariants
import Mathlib.RepresentationTheory.Rep.Basic
import Mathlib.RingTheory.AdicCompletion.AsTensorProduct
import Mathlib.RingTheory.AdicCompletion.Basic
import Mathlib.RingTheory.AdicCompletion.Functoriality
import Mathlib.RingTheory.AdicCompletion.Noetherian
import Mathlib.RingTheory.AdicCompletion.Topology
import Mathlib.RingTheory.Adjoin.PowerBasis
import Mathlib.RingTheory.AdjoinRoot
import Mathlib.RingTheory.AlgebraTower
import Mathlib.RingTheory.Algebraic.Integral
import Mathlib.RingTheory.ClassGroup.Basic
import Mathlib.RingTheory.Complex
import Mathlib.RingTheory.DedekindDomain.Factorization
import Mathlib.RingTheory.DedekindDomain.IntegralClosure
import Mathlib.RingTheory.DedekindDomain.SInteger
import Mathlib.RingTheory.DiscreteValuationRing.Basic
import Mathlib.RingTheory.DiscreteValuationRing.TFAE
import Mathlib.RingTheory.Discriminant
import Mathlib.RingTheory.Filtration
import Mathlib.RingTheory.FractionalIdeal.Norm
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Ideal.GoingUp
import Mathlib.RingTheory.Ideal.IsPrincipalPowQuotient
import Mathlib.RingTheory.Ideal.Norm.AbsNorm
import Mathlib.RingTheory.Ideal.Norm.RelNorm
import Mathlib.RingTheory.Ideal.Quotient.Index
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.RingTheory.IntegralClosure.IsIntegralClosure.Basic
import Mathlib.RingTheory.Invariant.Profinite
import Mathlib.RingTheory.IsTensorProduct
import Mathlib.RingTheory.LocalRing.Basic
import Mathlib.RingTheory.LocalRing.ResidueField.Basic
import Mathlib.RingTheory.Localization.Finiteness
import Mathlib.RingTheory.Nakayama
import Mathlib.RingTheory.Norm.Basic
import Mathlib.RingTheory.Norm.Defs
import Mathlib.RingTheory.Norm.Transitivity
import Mathlib.RingTheory.Polynomial.ContentIdeal
import Mathlib.RingTheory.Polynomial.GaussLemma
import Mathlib.RingTheory.Polynomial.Vieta
import Mathlib.RingTheory.QuasiFinite.Basic
import Mathlib.RingTheory.RamificationInertia.Basic
import Mathlib.RingTheory.RootsOfUnity.Basic
import Mathlib.RingTheory.SimpleModule.Basic
import Mathlib.RingTheory.Spectrum.Prime.Topology
import Mathlib.RingTheory.TensorProduct.Basic
import Mathlib.RingTheory.TensorProduct.Finite
import Mathlib.RingTheory.TensorProduct.Free
import Mathlib.RingTheory.TensorProduct.Maps
import Mathlib.RingTheory.TensorProduct.MvPolynomial
import Mathlib.RingTheory.TensorProduct.Quotient
import Mathlib.RingTheory.Trace.Basic
import Mathlib.RingTheory.Valuation.Discrete.Basic
import Mathlib.RingTheory.Valuation.Discrete.IsDiscreteValuationRing
import Mathlib.RingTheory.Valuation.Extension
import Mathlib.RingTheory.Valuation.Integral
import Mathlib.RingTheory.Valuation.LocalSubring
import Mathlib.RingTheory.Valuation.RamificationGroup
import Mathlib.RingTheory.Valuation.ValuationRing
import Mathlib.RingTheory.Valuation.ValuationSubring
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Tactic
import Mathlib.Topology.Algebra.Category.ProfiniteGrp.Basic
import Mathlib.Topology.Algebra.ClopenNhdofOne
import Mathlib.Topology.Algebra.ContinuousMonoidHom
import Mathlib.Topology.Algebra.Group.Basic
import Mathlib.Topology.Algebra.Group.ClosedSubgroup
import Mathlib.Topology.Algebra.Group.Quotient
import Mathlib.Topology.Algebra.Group.SubmonoidClosure
import Mathlib.Topology.Algebra.Group.TopologicalAbelianization
import Mathlib.Topology.Algebra.Group.Units
import Mathlib.Topology.Algebra.IsOpenUnits
import Mathlib.Topology.Algebra.IsUniformGroup.Basic
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.Topology.Algebra.OpenSubgroup
import Mathlib.Topology.Algebra.Ring.Basic
import Mathlib.Topology.Algebra.Ring.Compact
import Mathlib.Topology.Algebra.Valued.LocallyCompact
import Mathlib.Topology.Algebra.Valued.ValuativeRel
import Mathlib.Topology.Algebra.Valued.ValuedField
import Mathlib.Topology.Connected.Clopen
import Mathlib.Topology.Instances.Matrix
import Mathlib.Topology.Instances.Sign
import Mathlib.Topology.Instances.ZMod
import Mathlib.Topology.Maps.Basic
import Mathlib.Topology.Neighborhoods
import Mathlib.Topology.Sets.Opens
import Mathlib.Topology.UniformSpace.AbsoluteValue
import Definitions.Def_OAIQ244Duke025
import Definitions.Def_OAIQ244Duke026

section
-- module Solutions.OAIQ244_DUKE.AbstractClassFieldTheory_Reciprocity_Construction_FrobeniusField
attribute [-instance] _root_.ClassFormation.DegreeData.FiniteAmbientFrobeniusFixedFieldTower.ambientQuotientFinite _root_.ClassFormation.DegreeData.FiniteAmbientFrobeniusFixedFieldTower.ambientRepresentedQuotientFinite _root_.ClassFormation.DegreeData.FiniteTower.totalQuotientFinite _root_.ClassFormation.DegreeData.FrobeniusFixedFieldTower.baseAbsoluteFiniteInstance _root_.ClassFormation.DegreeData.FrobeniusFixedFieldTower.extensionFinite _root_.ClassFormation.DegreeData.FrobeniusFixedFieldTower.extensionNormal _root_.ClassFormation.DegreeData.FrobeniusFixedFieldTower.fieldAbsoluteFiniteInstance _root_.ClassFormation.DegreeData.FrobeniusPowerFixedFieldTower.baseRepresentedAbsoluteFinite _root_.ClassFormation.DegreeData.FrobeniusPowerFixedFieldTower.fieldRepresentedAbsoluteFinite _root_.ClassFormation.DegreeData.FrobeniusPowerFixedFieldTower.relativeRepresentedQuotientFinite _root_.ClassFormation.DegreeData.frobeniusElementsMul _root_.ClassFormation.DegreeData.maximalUnramifiedNormQuotientAddCommGroup _root_.ClassFormation.FiniteAbstractField.toFiniteResidueAbstractField_extensionFinite _root_.ClassFormation.FiniteAbstractField.toFiniteResidueAbstractField_extensionNormal _root_.ClassFormation.FiniteCyclicSubextension.instFiniteQuotientSubtypeMemSubgroupFieldExtensionSubgroupField _root_.ClassFormation.FiniteCyclicSubextension.instFintypeQuotientSubtypeMemSubgroupFieldExtensionSubgroupField _root_.ClassFormation.FiniteCyclicSubextension.instNormalSubtypeMemSubgroupFieldExtensionSubgroupField _root_.ClassFormation.FiniteGaloisSubextension.extensionSubgroup_normalInstance _root_.ClassFormation.FiniteGaloisSubextension.extensionSubgroup_over_intermediate_normalInstance _root_.ClassFormation.FiniteGaloisSubextension.intermediateField_normalInstance _root_.ClassFormation.FiniteIntermediateField.galoisRefinement_normal _root_.ClassFormation.FiniteUnramifiedCyclicExtension.instFiniteQuotientSubtypeMemSubgroupBaseFieldExtensionSubgroupField _root_.ClassFormation.FiniteUnramifiedCyclicExtension.instFiniteQuotientSubtypeMemSubgroupFieldExtensionSubgroupField _root_.ClassFormation.FiniteUnramifiedCyclicExtension.instFintypeQuotientSubtypeMemSubgroupFieldExtensionSubgroupField _root_.ClassFormation.FiniteUnramifiedCyclicExtension.instNormalSubtypeMemSubgroupFieldExtensionSubgroupField _root_.ClassFormation.conjugateExtension_normal _root_.ClassFormation.finiteNormQuotientAddCommGroup _root_.ClassFormation.instIsAddTorsionFreeZHat _root_.ClassFormation.instIsMulTorsionFreeMultiplicativeZHat _root_.OAI.PrimeDegreePackets.diagonalLogAction _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.RelativeIdeleGroup.relativeIdeleMulAction _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace
attribute [-simp] _root_.ClassFormation.DegreeData.chosenUnramifiedFrobeniusLift_exponent _root_.ClassFormation.DegreeData.extensionNormalizedDegree_frobenius_mul _root_.ClassFormation.DegreeData.finiteReciprocityCandidate_apply _root_.ClassFormation.DegreeData.finiteReciprocityCandidate_zero _root_.ClassFormation.DegreeData.frobeniusActionConjugate_coe _root_.ClassFormation.DegreeData.frobeniusExponent_actionConjugate _root_.ClassFormation.DegreeData.frobeniusExponent_chosenDegreeOneFrobeniusElement _root_.ClassFormation.DegreeData.frobeniusExponent_mul _root_.ClassFormation.DegreeData.frobeniusExponent_powerOfDegreeOne _root_.ClassFormation.DegreeData.frobeniusFixedFieldAction_coe _root_.ClassFormation.DegreeData.frobeniusLiftDifference_coe _root_.ClassFormation.DegreeData.frobeniusMul_coe _root_.ClassFormation.DegreeData.frobeniusPowerOfDegreeOne_coe _root_.ClassFormation.DegreeData.frobeniusPowerSum_coe _root_.ClassFormation.DegreeData.frobeniusQuotientAction_mk _root_.ClassFormation.DegreeData.frobeniusQuotientRepresentation_apply _root_.ClassFormation.DegreeData.frobeniusRestriction_chosenFiniteReciprocityFrobeniusLift _root_.ClassFormation.DegreeData.frobeniusRestriction_mul _root_.ClassFormation.DegreeData.maximalUnramifiedNormClass_eq_zero_iff _root_.ClassFormation.DegreeData.maximalUnramifiedNormQuotientInfiniteEquiv_maximalUnramifiedNormClass _root_.ClassFormation.DegreeData.maximalUnramifiedNormQuotientLift_maximalUnramifiedNormClass _root_.ClassFormation.DegreeData.maximalUnramifiedToFiniteNormQuotient_maximalUnramifiedNormClass _root_.ClassFormation.DegreeData.mem_maximalUnramifiedField_iff _root_.ClassFormation.DegreeData.mem_maximalUnramifiedNormSubgroup_iff _root_.ClassFormation.FiniteAbelianSubextension.extensionQuotientMk_apply _root_.ClassFormation.FiniteAbstractField.normToBase_index_eq_degree _root_.ClassFormation.FiniteGaloisSubextension.extensionQuotientMk_apply _root_.ClassFormation.FiniteGaloisSubextension.extensionQuotientMk_eq_one_iff _root_.ClassFormation.FiniteGaloisSubextension.toGaloisSubextension_isTotallyRamified_iff _root_.ClassFormation.FiniteGaloisSubextension.toGaloisSubextension_isUnramified_iff _root_.ClassFormation.ValuationData.canonicalUnramifiedNormQuotientValuation_finiteNormClass _root_.ClassFormation.ValuationData.canonicalValueQuotientHom_mk _root_.ClassFormation.ValuationData.canonicalValueReduction_one _root_.ClassFormation.ValuationData.mem_infiniteUnitAddSubgroup_iff _root_.ClassFormation.ValuationData.mem_infiniteUnitNormSubgroup_iff _root_.ClassFormation.ValuationData.mem_unitAddSubgroup_iff _root_.ClassFormation.ValuationData.oneValue_coe _root_.ClassFormation.ValuationData.unitRepresentation_quotient_mk_apply _root_.ClassFormation.ValuationData.unramifiedNormQuotientValuation_finiteNormClass _root_.ClassFormation.ValuationData.valuationAt_chosenPrimeElement _root_.ClassFormation.ValuationData.valuationAt_coe _root_.ClassFormation.ValuationData.valueModulo_apply _root_.ClassFormation.absoluteConjugateCosetEquiv_mk _root_.ClassFormation.canonicalValueQuotientMap_mk _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.ClassFormation.cyclicNormClassHom_apply _root_.ClassFormation.extensionFixedRepresentationEquiv_apply_coe _root_.ClassFormation.extensionFixedRepresentationEquiv_symm_apply_coe _root_.ClassFormation.finiteNormClass_add _root_.ClassFormation.finiteNormClass_eq_zero_iff _root_.ClassFormation.finiteNormClass_nsmul _root_.ClassFormation.finiteNormClass_sub _root_.ClassFormation.finiteNormClass_zero _root_.ClassFormation.finiteNormQuotientConcreteEquiv_finiteNormClass _root_.ClassFormation.finiteNormQuotientLift_finiteNormClass _root_.ClassFormation.finiteReciprocityNaturalityConjugation_mk _root_.ClassFormation.mem_nsmulImage_iff _root_.ClassFormation.normalExtensionAction_coe _root_.ClassFormation.nsmulImage_top _root_.ClassFormation.relativeConjugateCosetEquiv_mk _root_.ClassFormation.relativeCosetAction_mk _root_.ClassFormation.relativeCosetAction_zero _root_.ClassFormation.relativeNorm_apply_coe _root_.ClassFormation.relativeNorm_self _root_.ClassFormation.toZModPow_zHatToPadicInt _root_.ClassFormation.zHatReductionRingHom_apply _root_.ClassFormation.zHatRingEquivProfiniteIntegerPrimeProduct_apply _root_.ClassFormation.zHatToPadicInt_intCast _root_.ClassFormation.zHatToProfiniteIntegerPrimeProduct_apply _root_.ClassFormation.zHatToProfiniteIntegerPrimeProduct_intCast _root_.ClassFormation.zHatUnitsContinuousMulEquivPrimeProduct_coe_apply _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.KummerTheory.extensionFixedEndomorphism_apply_val _root_.KummerTheory.extensionFixedKernelElement_val _root_.KummerTheory.extensionFixedRepresentation_quotient_mk_apply_val _root_.KummerTheory.mem_extensionSubgroup_iff _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.LocalFieldTheory.residueField_algebraMap_residue _root_.OAI.PrimeDegreePackets.ThetaConstruction.schwartzCM_apply _root_.ClassFormation.DegreeData.inertiaConjugationCosetEquiv_mk
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

/-- The normalized-degree image of the actual subgroup `G_Σ ≤ G_K` is
the image already computed on the group-dual `Γ`. -/
theorem frobeniusFixedSubgroupWithin_normalizedDegree_image
    (D : DegreeData G) [IsTopologicalGroup G]
    (K : FiniteResidueAbstractField D) (L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.field.toSubgroup)
    [hLnormal : (extensionSubgroup K.field L hLK).Normal]
    (σ : D.FrobeniusElements K L hLK) :
    (D.frobeniusFixedSubgroupWithin K L hLK σ).map
        (D.normalizedDegree K).toMonoidHom =
      (D.frobeniusClosureDegree K L hLK σ).toMonoidHom.range := by
  ext z
  constructor
  · rintro ⟨k, hk, rfl⟩
    exact ⟨⟨QuotientGroup.mk k, hk⟩, rfl⟩
  · rintro ⟨a, rfl⟩
    obtain ⟨k, hk⟩ := QuotientGroup.mk'_surjective
      (D.extensionInertiaWithin K.field L hLK) a.1
    have hkS : k ∈ D.frobeniusFixedSubgroupWithin K L hLK σ := by
      change (QuotientGroup.mk' (D.extensionInertiaWithin K.field L hLK)) k ∈
        (D.frobeniusClosure K L hLK σ).toSubgroup
      exact hk.symm ▸ a.2
    refine ⟨k, hkS, ?_⟩
    calc
      D.normalizedDegree K k =
          D.extensionNormalizedDegree K L hLK
            ((QuotientGroup.mk' (D.extensionInertiaWithin K.field L hLK)) k) :=
        (D.extensionNormalizedDegree_mk K L hLK k).symm
      _ = D.extensionNormalizedDegree K L hLK a.1 :=
        congrArg (D.extensionNormalizedDegree K L hLK) hk

theorem frobeniusFixedField_mappedRelIndex (D : DegreeData G)
    [IsTopologicalGroup G] [CompactSpace G] [T2Space G]
    (K : FiniteResidueAbstractField D) (L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.field.toSubgroup)
    [hLnormal : (extensionSubgroup K.field L hLK).Normal]
    (σ : D.FrobeniusElements K L hLK) :
    ((D.frobeniusFixedField K L hLK σ).toSubgroup.map
        D.degree.toMonoidHom).relIndex
      (K.field.toSubgroup.map D.degree.toMonoidHom) =
      D.frobeniusExponent K L hLK σ := by
  let S : Subgroup K.field.toSubgroup :=
    D.frobeniusFixedSubgroupWithin K L hLK σ
  let dK : K.field.toSubgroup →* ZHatMul :=
    (D.normalizedDegree K).toMonoidHom
  let scale : ZHatMul →* ZHatMul :=
    (zHatPowNat (K.residueDegree : ℕ)).toMonoidHom
  have hraw : (D.restrictedDegree K.field).toMonoidHom = scale.comp dK := by
    apply MonoidHom.ext
    intro k
    apply Multiplicative.ext
    exact (D.residueDegree_nsmul_normalizedDegree K k).symm
  have hSigmaImage :
      (D.frobeniusFixedField K L hLK σ).toSubgroup.map
          D.degree.toMonoidHom =
        S.map (D.restrictedDegree K.field).toMonoidHom := by
    ext z
    constructor
    · rintro ⟨g, hg, rfl⟩
      obtain ⟨k, hk, hkg⟩ := hg
      refine ⟨k, hk, ?_⟩
      exact congrArg D.degree hkg
    · rintro ⟨k, hk, rfl⟩
      exact ⟨k.1, ⟨k, hk, rfl⟩, rfl⟩
  have hKimage :
      K.field.toSubgroup.map D.degree.toMonoidHom =
        (⊤ : Subgroup K.field.toSubgroup).map
          (D.restrictedDegree K.field).toMonoidHom := by
    ext z
    constructor
    · rintro ⟨g, hg, rfl⟩
      exact ⟨⟨g, hg⟩, trivial, rfl⟩
    · rintro ⟨k, _, rfl⟩
      exact ⟨k.1, k.2, rfl⟩
  have hscale : Function.Injective scale := by
    intro x y hxy
    apply Multiplicative.ext
    apply zHatMulNat_injective K.residueDegree.property
    exact congrArg Multiplicative.toAdd hxy
  have htop : (⊤ : Subgroup K.field.toSubgroup).map dK = ⊤ := by
    apply top_unique
    intro z _
    obtain ⟨k, hk⟩ := D.normalizedDegree_surjective K z
    exact ⟨k, trivial, hk⟩
  rw [hSigmaImage, hKimage, hraw]
  rw [← Subgroup.map_map, ← Subgroup.map_map]
  rw [Subgroup.relIndex_map_map_of_injective _ _ hscale]
  rw [show S.map dK =
      (D.frobeniusClosureDegree K L hLK σ).toMonoidHom.range by
        simpa [S, dK] using
          D.frobeniusFixedSubgroupWithin_normalizedDegree_image
            K L hLK σ]
  rw [htop, Subgroup.relIndex_top_right,
    D.frobeniusClosureDegree_range K L hLK σ,
    AddSubgroup.index_toSubgroup,
    zHatMulNat_range_index _
      (D.frobeniusExponent_pos K L hLK σ)]

/-- The actual relative residue quotient of the Frobenius fixed field over
`K` is finite.  Positivity of the computed mapped relative index gives an
honest finite-index witness before any natural-valued cardinality is formed. -/
theorem frobeniusFixedField_relativeResidueQuotientFinite
    (D : DegreeData G)
    [IsTopologicalGroup G] [CompactSpace G] [T2Space G]
    (K : FiniteResidueAbstractField D) (L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.field.toSubgroup)
    [hLnormal : (extensionSubgroup K.field L hLK).Normal]
    (σ : D.FrobeniusElements K L hLK) :
    Finite
      (↥(K.field.toSubgroup.map D.degree.toMonoidHom) ⧸
        ((D.frobeniusFixedField K L hLK σ).toSubgroup.map
            D.degree.toMonoidHom).subgroupOf
          (K.field.toSubgroup.map D.degree.toMonoidHom)) := by
  apply (Subgroup.index_ne_zero_iff_finite).mp
  change ((D.frobeniusFixedField K L hLK σ).toSubgroup.map
      D.degree.toMonoidHom).relIndex
        (K.field.toSubgroup.map D.degree.toMonoidHom) ≠ 0
  rw [D.frobeniusFixedField_mappedRelIndex K L hLK σ]
  exact (D.frobeniusExponent_pos K L hLK σ).ne'

/-- The Frobenius fixed field equipped with its actual finite absolute
residue quotient. -/
noncomputable def frobeniusFixedResidueField (D : DegreeData G)
    [IsTopologicalGroup G] [CompactSpace G] [T2Space G]
    (K : FiniteResidueAbstractField D) (L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.field.toSubgroup)
    [hLnormal : (extensionSubgroup K.field L hLK).Normal]
    (σ : D.FrobeniusElements K L hLK) :
    FiniteResidueAbstractField D := by
  letI := D.frobeniusFixedField_relativeResidueQuotientFinite K L hLK σ
  exact FiniteResidueAbstractField.ofRelativeInclusion D
    (D.frobeniusFixedField K L hLK σ) K
    (D.frobeniusFixedField_le K L hLK σ)

/-- Absolute residue-degree formula, now stated only through positive
natural invariants of honest finite quotient bundles. -/
theorem frobeniusFixedResidueField_residueDegree (D : DegreeData G)
    [IsTopologicalGroup G] [CompactSpace G] [T2Space G]
    (K : FiniteResidueAbstractField D) (L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.field.toSubgroup)
    [hLnormal : (extensionSubgroup K.field L hLK).Normal]
    (σ : D.FrobeniusElements K L hLK) :
    ((D.frobeniusFixedResidueField K L hLK σ).residueDegree : ℕ) =
      D.frobeniusExponent K L hLK σ * (K.residueDegree : ℕ) := by
  let Sigma := D.frobeniusFixedResidueField K L hLK σ
  let E : AbstractExtension G := {
    field := D.frobeniusFixedField K L hLK σ
    base := K.field
    below := D.frobeniusFixedField_le K L hLK σ
  }
  let := D.frobeniusFixedField_relativeResidueQuotientFinite K L hLK σ
  have hrelative :
      E.relativeResidueDegreeCardinal D =
        (D.frobeniusExponent K L hLK σ : Cardinal) := by
    rw [AbstractExtension.relativeResidueDegreeCardinal]
    change Cardinal.mk
        (↥(K.field.toSubgroup.map D.degree.toMonoidHom) ⧸
          ((D.frobeniusFixedField K L hLK σ).toSubgroup.map
              D.degree.toMonoidHom).subgroupOf
            (K.field.toSubgroup.map D.degree.toMonoidHom)) = _
    rw [← Nat.cast_card]
    exact_mod_cast D.frobeniusFixedField_mappedRelIndex K L hLK σ
  have hcard :=
    E.relativeResidueDegreeCardinal_mul_residueDegreeCardinal D
  change E.relativeResidueDegreeCardinal D *
      D.residueDegreeCardinal K.field =
    D.residueDegreeCardinal Sigma.field at hcard
  rw [hrelative, K.residueDegreeCardinal_eq_coe,
    Sigma.residueDegreeCardinal_eq_coe] at hcard
  exact_mod_cast hcard.symm

/-- The normalized degree constructed on `Γ` in the Frobenius fixed-field theorem is exactly
the intrinsic normalized degree of the actual field `Σ`. -/
theorem frobeniusFixedField_normalizedDegree_compatibility (D : DegreeData G)
    [IsTopologicalGroup G] [CompactSpace G] [T2Space G]
    (K : FiniteResidueAbstractField D) (L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.field.toSubgroup)
    [hLnormal : (extensionSubgroup K.field L hLK).Normal]
    (σ : D.FrobeniusElements K L hLK)
    (s : (D.frobeniusFixedField K L hLK σ).toSubgroup) :
    D.fixedFieldNormalizedDegree K L hLK σ
        (D.frobeniusFixedFieldToClosure K L hLK σ s) =
      D.normalizedDegree (D.frobeniusFixedResidueField K L hLK σ) s := by
  let Sigma := D.frobeniusFixedResidueField K L hLK σ
  let a : D.frobeniusClosure K L hLK σ :=
    D.frobeniusFixedFieldToClosure K L hLK σ s
  let k : K.field.toSubgroup :=
    Subgroup.inclusion (D.frobeniusFixedField_le K L hLK σ) s
  let n := D.frobeniusExponent K L hLK σ
  apply Multiplicative.ext
  apply zHatMulNat_injective Sigma.residueDegree.property
  change (Sigma.residueDegree : ℕ) •
      (D.fixedFieldNormalizedDegree K L hLK σ a).toAdd =
    (Sigma.residueDegree : ℕ) • (D.normalizedDegree Sigma s).toAdd
  calc
    (Sigma.residueDegree : ℕ) •
        (D.fixedFieldNormalizedDegree K L hLK σ a).toAdd =
      (K.residueDegree : ℕ) •
        (n • (D.fixedFieldNormalizedDegree K L hLK σ a).toAdd) := by
          rw [show (Sigma.residueDegree : ℕ) =
              n * (K.residueDegree : ℕ) by
            simpa [Sigma, n] using
              D.frobeniusFixedResidueField_residueDegree K L hLK σ]
          rw [smul_smul, Nat.mul_comm]
    _ = (K.residueDegree : ℕ) •
        (D.frobeniusClosureDegree K L hLK σ a).toAdd := by
          rw [D.frobeniusExponent_nsmul_fixedFieldNormalizedDegree]
    _ = (K.residueDegree : ℕ) • (D.normalizedDegree K k).toAdd := by
          rfl
    _ = (D.degree s.1).toAdd := by
          exact D.residueDegree_nsmul_normalizedDegree K k
    _ = (Sigma.residueDegree : ℕ) •
        (D.normalizedDegree Sigma s).toAdd := by
          exact (D.residueDegree_nsmul_normalizedDegree Sigma s).symm

end DegreeData

end
end ClassFormation
end

section
-- module Solutions.OAIQ244_DUKE.AbstractClassFieldTheory_Reciprocity_Construction_UniversalNormDescent
attribute [-instance] _root_.ClassFormation.DegreeData.FiniteAmbientFrobeniusFixedFieldTower.ambientQuotientFinite _root_.ClassFormation.DegreeData.FiniteAmbientFrobeniusFixedFieldTower.ambientRepresentedQuotientFinite _root_.ClassFormation.DegreeData.FrobeniusFixedFieldTower.baseAbsoluteFiniteInstance _root_.ClassFormation.DegreeData.FrobeniusFixedFieldTower.extensionFinite _root_.ClassFormation.DegreeData.FrobeniusFixedFieldTower.extensionNormal _root_.ClassFormation.DegreeData.FrobeniusFixedFieldTower.fieldAbsoluteFiniteInstance _root_.ClassFormation.DegreeData.FrobeniusPowerFixedFieldTower.baseRepresentedAbsoluteFinite _root_.ClassFormation.DegreeData.FrobeniusPowerFixedFieldTower.fieldRepresentedAbsoluteFinite _root_.ClassFormation.DegreeData.FrobeniusPowerFixedFieldTower.relativeRepresentedQuotientFinite _root_.ClassFormation.FiniteAbstractField.toFiniteResidueAbstractField_extensionFinite _root_.ClassFormation.FiniteAbstractField.toFiniteResidueAbstractField_extensionNormal _root_.ClassFormation.FiniteGaloisSubextension.extensionSubgroup_normalInstance _root_.ClassFormation.FiniteGaloisSubextension.extensionSubgroup_over_intermediate_normalInstance _root_.ClassFormation.FiniteGaloisSubextension.intermediateField_normalInstance _root_.ClassFormation.finiteNormQuotientAddCommGroup _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.maximalIdealPowSuccQuotModule _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace
attribute [-simp] _root_.ClassFormation.DegreeData.finiteReciprocityCandidate_apply _root_.ClassFormation.DegreeData.finiteReciprocityCandidate_zero _root_.ClassFormation.DegreeData.frobeniusFixedFieldAction_coe _root_.ClassFormation.DegreeData.frobeniusQuotientRepresentation_apply _root_.ClassFormation.DegreeData.maximalUnramifiedToFiniteNormQuotient_maximalUnramifiedNormClass _root_.ClassFormation.FiniteGaloisSubextension.classFieldCandidate_field _root_.ClassFormation.ValuationData.canonicalUnramifiedNormQuotientValuation_finiteNormClass _root_.ClassFormation.ValuationData.canonicalValueQuotientHom_mk _root_.ClassFormation.ValuationData.canonicalValueReduction_one _root_.ClassFormation.ValuationData.mem_infiniteUnitAddSubgroup_iff _root_.ClassFormation.ValuationData.mem_infiniteUnitNormSubgroup_iff _root_.ClassFormation.ValuationData.unramifiedNormQuotientValuation_finiteNormClass _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.ClassFormation.cyclicNormClassHom_apply _root_.ClassFormation.extensionFixedRepresentationEquiv_apply_coe _root_.ClassFormation.extensionFixedRepresentationEquiv_symm_apply_coe _root_.ClassFormation.finiteNormClass_add _root_.ClassFormation.finiteNormClass_eq_zero_iff _root_.ClassFormation.finiteNormClass_nsmul _root_.ClassFormation.finiteNormClass_sub _root_.ClassFormation.finiteNormClass_zero _root_.ClassFormation.finiteNormQuotientConcreteEquiv_finiteNormClass _root_.ClassFormation.finiteNormQuotientLift_finiteNormClass _root_.ClassFormation.mem_normFilterBasis_iff _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.LocalFieldTheory.residueField_algebraMap_residue _root_.OAI.PrimeDegreePackets.ThetaConstruction.schwartzCM_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

universe u v

namespace ClassFormation

open KummerTheory
open CyclicCohomology

/-!
# Universal norm descent

This module contains the representation-theoretic lifting and correction
calculation used by the abstract reciprocity construction, together with
the norm, action, and iterate identities it requires.
-/

noncomputable section

open CategoryTheory
open scoped BigOperators

theorem relativeNorm_transport_coe
    {R : IntegralRepGroupType} [Group R] [TopologicalSpace R]
    (B : Rep ℤ R)
    (F' E' F E : ClosedSubgroup R)
    (hF : F' = F) (hE : E' = E)
    (hE'F' : E'.toSubgroup ≤ F'.toSubgroup)
    (hEF : E.toSubgroup ≤ F.toSubgroup)
    [Finite (F'.toSubgroup ⧸ extensionSubgroup F' E' hE'F')]
    [Finite (F.toSubgroup ⧸ extensionSubgroup F E hEF)]
    (a : ambientFixedAddSubgroup B E') :
    ((relativeNorm B F E hEF (hE ▸ a) : ambientFixedAddSubgroup B F) : B.V) =
      ((relativeNorm B F' E' hE'F' a : ambientFixedAddSubgroup B F') : B.V) := by
  cases hF
  cases hE
  rfl

/-- Relative norm is equivariant for a conjugation stabilizing both
fields in the tower. -/
theorem relativeNorm_conjugateStableAction
    {R : IntegralRepGroupType} [Group R] [TopologicalSpace R] [ContinuousMul R]
    (B : Rep ℤ R) (F E : ClosedSubgroup R)
    (hEF : E.toSubgroup ≤ F.toSubgroup) (s : R)
    [Finite (F.toSubgroup ⧸ extensionSubgroup F E hEF)]
    (hF : conjugateClosedSubgroup F s = F)
    (hE : conjugateClosedSubgroup E s = E)
    (a : ambientFixedAddSubgroup B E) :
    relativeNorm B F E hEF (conjugateStableAction B E s hE a) =
      conjugateStableAction B F s hF (relativeNorm B F E hEF a) := by
  let hConj := conjugateClosedSubgroup_mono hEF s
  let : Finite ((conjugateClosedSubgroup F s).toSubgroup ⧸
      extensionSubgroup (conjugateClosedSubgroup F s)
        (conjugateClosedSubgroup E s) hConj) :=
    finite_conjugateExtension F E hEF s
  have hs := congrArg Subtype.val
    (relativeNorm_conjugate_apply B F E hEF s a)
  apply Subtype.ext
  calc
    ((relativeNorm B F E hEF (conjugateStableAction B E s hE a) :
        ambientFixedAddSubgroup B F) : B.V) =
        ((relativeNorm B (conjugateClosedSubgroup F s)
          (conjugateClosedSubgroup E s) hConj
          (conjugateFixedElement B E s a) :
            ambientFixedAddSubgroup B (conjugateClosedSubgroup F s)) : B.V) := by
      exact relativeNorm_transport_coe B
        (conjugateClosedSubgroup F s) (conjugateClosedSubgroup E s) F E
        hF hE hConj hEF (conjugateFixedElement B E s a)
    _ = ((conjugateFixedElement B F s (relativeNorm B F E hEF a) :
          ambientFixedAddSubgroup B (conjugateClosedSubgroup F s)) : B.V) := hs
    _ = ((conjugateStableAction B F s hF (relativeNorm B F E hEF a) :
          ambientFixedAddSubgroup B F) : B.V) :=
      (transport_fixed_coe B _ F hF _).symm

/-- Enumerate the norm of a finite cyclic representation by the first
n powers of a specified generator. -/
theorem rep_norm_eq_generatorPowerSum
    {Q : IntegralRepGroupType} [Group Q] [Fintype Q]
    (B : Rep ℤ Q) (g : Q) (hg : ∀ q, q ∈ Subgroup.zpowers g)
    (n : ℕ) (hcard : Fintype.card Q = n) (x : B.V) :
    B.norm.hom x = ∑ i : Fin n, B.ρ (g ^ i.1) x := by
  classical
  have horder : orderOf g = n := by
    calc
      orderOf g = Nat.card Q :=
        orderOf_eq_card_of_forall_mem_zpowers hg
      _ = Fintype.card Q := Nat.card_eq_fintype_card
      _ = n := hcard
  let e : Fin n ≃ Q := Equiv.ofBijective (fun i => g ^ i.1) (by
    constructor
    · intro i j hij
      apply Fin.ext
      have hmod : i.1 ≡ j.1 [MOD orderOf g] :=
        (pow_eq_pow_iff_modEq).mp hij
      rw [horder] at hmod
      exact hmod.eq_of_lt_of_lt i.2 j.2
    · intro q
      have himage :
          Finset.image (fun i => g ^ i) (Finset.range n) = Finset.univ := by
        rw [← horder]
        exact IsCyclic.image_range_orderOf hg
      have hq : q ∈ Finset.image (fun i => g ^ i) (Finset.range n) := by
        rw [himage]
        simp
      obtain ⟨i, hi, hiq⟩ := Finset.mem_image.mp hq
      exact ⟨⟨i, Finset.mem_range.mp hi⟩, hiq⟩)
  have hsum : (∑ q : Q, B.ρ q x) =
      ∑ i : Fin n, B.ρ (g ^ i.1) x :=
    (e.sum_comp (fun q : Q => B.ρ q x)).symm
  simpa [Rep.norm, Representation.norm] using hsum

/-- Replace the generator action in the preceding norm formula by a
pointwise equal endomorphism and enumerate its iterates. -/
theorem rep_norm_eq_generatorIterateSum
    {Q : IntegralRepGroupType} [Group Q] [Fintype Q]
    (B : Rep ℤ Q) (g : Q) (hg : ∀ q, q ∈ Subgroup.zpowers g)
    (n : ℕ) (hcard : Fintype.card Q = n)
    (f : B.V → B.V) (hf : ∀ z, B.ρ g z = f z) (x : B.V) :
    B.norm.hom x = ∑ i : Fin n, (f^[i.1]) x := by
  rw [rep_norm_eq_generatorPowerSum B g hg n hcard x]
  apply Finset.sum_congr rfl
  intro i _
  rw [rep_action_pow_eq_iterate]
  exact congrFun (congrArg (fun h : B.V → B.V => h^[i.1]) (funext hf)) x

/-- Every nonnegative power fixes an element fixed by the original group
element. -/
theorem rep_action_pow_fixed {R : IntegralRepGroupType} [Group R]
    (B : Rep ℤ R) (g : R) (x : B.V) (hx : B.ρ g x = x) (n : ℕ) :
    B.ρ (g ^ n) x = x := by
  rw [rep_action_pow_eq_iterate]
  exact Function.IsFixedPt.iterate hx n

end

end ClassFormation
end

section
-- module Solutions.OAIQ244_DUKE.AbstractClassFieldTheory_Reciprocity_Construction_FrobeniusFixedFieldAction
attribute [-instance] _root_.ClassFormation.DegreeData.FiniteAmbientFrobeniusFixedFieldTower.ambientQuotientFinite _root_.ClassFormation.DegreeData.FiniteAmbientFrobeniusFixedFieldTower.ambientRepresentedQuotientFinite _root_.ClassFormation.DegreeData.FrobeniusFixedFieldTower.baseAbsoluteFiniteInstance _root_.ClassFormation.DegreeData.FrobeniusFixedFieldTower.extensionFinite _root_.ClassFormation.DegreeData.FrobeniusFixedFieldTower.extensionNormal _root_.ClassFormation.DegreeData.FrobeniusFixedFieldTower.fieldAbsoluteFiniteInstance _root_.ClassFormation.DegreeData.FrobeniusPowerFixedFieldTower.baseRepresentedAbsoluteFinite _root_.ClassFormation.DegreeData.FrobeniusPowerFixedFieldTower.fieldRepresentedAbsoluteFinite _root_.ClassFormation.DegreeData.FrobeniusPowerFixedFieldTower.relativeRepresentedQuotientFinite _root_.ClassFormation.FiniteAbstractField.toFiniteResidueAbstractField_extensionFinite _root_.ClassFormation.FiniteAbstractField.toFiniteResidueAbstractField_extensionNormal _root_.ClassFormation.FiniteGaloisSubextension.extensionSubgroup_normalInstance _root_.ClassFormation.FiniteGaloisSubextension.extensionSubgroup_over_intermediate_normalInstance _root_.ClassFormation.FiniteGaloisSubextension.intermediateField_normalInstance _root_.ClassFormation.finiteNormQuotientAddCommGroup _root_.ClassFormation.instIsAddTorsionFreeZHat _root_.ClassFormation.instIsMulTorsionFreeMultiplicativeZHat _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.maximalIdealPowSuccQuotModule _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace
attribute [-simp] _root_.ClassFormation.DegreeData.chosenUnramifiedFrobeniusLift_exponent _root_.ClassFormation.DegreeData.finiteReciprocityCandidate_apply _root_.ClassFormation.DegreeData.finiteReciprocityCandidate_zero _root_.ClassFormation.DegreeData.frobeniusActionConjugate_coe _root_.ClassFormation.DegreeData.frobeniusExponent_actionConjugate _root_.ClassFormation.DegreeData.frobeniusExponent_chosenDegreeOneFrobeniusElement _root_.ClassFormation.DegreeData.frobeniusExponent_mul _root_.ClassFormation.DegreeData.frobeniusExponent_powerOfDegreeOne _root_.ClassFormation.DegreeData.frobeniusLiftDifference_coe _root_.ClassFormation.DegreeData.frobeniusPowerOfDegreeOne_coe _root_.ClassFormation.DegreeData.frobeniusQuotientRepresentation_apply _root_.ClassFormation.DegreeData.frobeniusRestriction_chosenFiniteReciprocityFrobeniusLift _root_.ClassFormation.DegreeData.frobeniusRestriction_mul _root_.ClassFormation.DegreeData.maximalUnramifiedToFiniteNormQuotient_maximalUnramifiedNormClass _root_.ClassFormation.FiniteAbelianSubextension.extensionQuotientMk_apply _root_.ClassFormation.FiniteGaloisSubextension.classFieldCandidate_field _root_.ClassFormation.FiniteGaloisSubextension.extensionQuotientMk_apply _root_.ClassFormation.FiniteGaloisSubextension.extensionQuotientMk_eq_one_iff _root_.ClassFormation.FiniteGaloisSubextension.toGaloisSubextension_isTotallyRamified_iff _root_.ClassFormation.FiniteGaloisSubextension.toGaloisSubextension_isUnramified_iff _root_.ClassFormation.ValuationData.canonicalUnramifiedNormQuotientValuation_finiteNormClass _root_.ClassFormation.ValuationData.canonicalValueQuotientHom_mk _root_.ClassFormation.ValuationData.canonicalValueReduction_one _root_.ClassFormation.ValuationData.mem_infiniteUnitAddSubgroup_iff _root_.ClassFormation.ValuationData.mem_infiniteUnitNormSubgroup_iff _root_.ClassFormation.ValuationData.unramifiedNormQuotientValuation_finiteNormClass _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.ClassFormation.cyclicNormClassHom_apply _root_.ClassFormation.extensionFixedRepresentationEquiv_apply_coe _root_.ClassFormation.extensionFixedRepresentationEquiv_symm_apply_coe _root_.ClassFormation.finiteNormClass_add _root_.ClassFormation.finiteNormClass_eq_zero_iff _root_.ClassFormation.finiteNormClass_nsmul _root_.ClassFormation.finiteNormClass_sub _root_.ClassFormation.finiteNormClass_zero _root_.ClassFormation.finiteNormQuotientConcreteEquiv_finiteNormClass _root_.ClassFormation.finiteNormQuotientLift_finiteNormClass _root_.ClassFormation.mem_normFilterBasis_iff _root_.ClassFormation.toZModPow_zHatToPadicInt _root_.ClassFormation.zHatReductionRingHom_apply _root_.ClassFormation.zHatRingEquivProfiniteIntegerPrimeProduct_apply _root_.ClassFormation.zHatToPadicInt_intCast _root_.ClassFormation.zHatToProfiniteIntegerPrimeProduct_apply _root_.ClassFormation.zHatToProfiniteIntegerPrimeProduct_intCast _root_.ClassFormation.zHatUnitsContinuousMulEquivPrimeProduct_coe_apply _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.LocalFieldTheory.residueField_algebraMap_residue _root_.OAI.PrimeDegreePackets.ThetaConstruction.schwartzCM_apply
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

/-!
# Actions on Frobenius fixed fields

This module defines the action induced on a Frobenius fixed field and proves
its compatibility with conjugate-stable actions, relative norms, inclusions,
and Frobenius power sums.
-/

noncomputable section

open CategoryTheory
open scoped BigOperators

section fixedFieldActions

/-!
Mathlib's `Rep ℤ G` requires its coefficient ring and acting group in the
same universe; `IntegralRepGroupType` names that shared boundary.
-/
variable {G : IntegralRepGroupType} [Group G] [TopologicalSpace G]

namespace DegreeData

/-- On a quotient representative, the fixed-field action coerces to the represented action. -/
theorem frobeniusFixedFieldAction_coe_of_mk (D : DegreeData G) (A : Rep ℤ G)
    [IsTopologicalGroup G] [CompactSpace G] [T2Space G]
    [TotallyDisconnectedSpace G]
    (K : FiniteResidueAbstractField D) (L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.field.toSubgroup)
    [hLnormal : (extensionSubgroup K.field L hLK).Normal]
    (σ : D.FrobeniusElements K L hLK)
    (q : K.field.toSubgroup ⧸ D.extensionInertiaWithin K.field L hLK)
    (hq : q * σ.1 = σ.1 * q)
    (k : K.field.toSubgroup) (hkq : QuotientGroup.mk k = q)
    (a : ambientFixedAddSubgroup A (D.frobeniusFixedField K L hLK σ)) :
    ((D.frobeniusFixedFieldAction A K L hLK σ q hq a :
      ambientFixedAddSubgroup A (D.frobeniusFixedField K L hLK σ)) : A.V) =
      A.ρ k.1 a.1 := by
  let t : K.field.toSubgroup := Quotient.out q
  have htq :
      (QuotientGroup.mk t :
        K.field.toSubgroup ⧸ D.extensionInertiaWithin K.field L hLK) = q :=
    Quotient.out_eq' q
  have hrel : t⁻¹ * k ∈ D.extensionInertiaWithin K.field L hLK :=
    QuotientGroup.eq.mp (htq.trans hkq.symm)
  have hrField : (t⁻¹ * k).1 ∈
      (D.frobeniusFixedField K L hLK σ).toSubgroup := by
    let rI : (D.fieldInertia L).toSubgroup :=
      ⟨(t⁻¹ * k).1, ⟨
        (mem_extensionSubgroup_iff K.field L hLK (t⁻¹ * k)).1 hrel.1,
        hrel.2⟩⟩
    exact D.fieldInertia_le_frobeniusFixedField K L hLK σ rI.2
  let r : (D.frobeniusFixedField K L hLK σ).toSubgroup :=
    ⟨(t⁻¹ * k).1, hrField⟩
  rw [D.frobeniusFixedFieldAction_coe]
  calc
    A.ρ t.1 a.1 = A.ρ t.1 (A.ρ r.1 a.1) := by rw [a.2 r]
    _ = A.ρ (t.1 * r.1) a.1 := by rw [map_mul]; rfl
    _ = A.ρ k.1 a.1 := by simp [r, t]

/-- The fixed-field action coincides with the conjugation-stable action. -/
theorem frobeniusFixedFieldAction_eq_conjugateStableAction
    (D : DegreeData G) (A : Rep ℤ G)
    [IsTopologicalGroup G] [CompactSpace G] [T2Space G]
    [TotallyDisconnectedSpace G]
    (K : FiniteResidueAbstractField D) (L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.field.toSubgroup)
    [hLnormal : (extensionSubgroup K.field L hLK).Normal]
    (σ : D.FrobeniusElements K L hLK)
    (q : K.field.toSubgroup ⧸ D.extensionInertiaWithin K.field L hLK)
    (hq : q * σ.1 = σ.1 * q)
    (a : ambientFixedAddSubgroup A (D.frobeniusFixedField K L hLK σ)) :
    let k : K.field.toSubgroup := Quotient.out q
    let hstable : conjugateClosedSubgroup
        (D.frobeniusFixedField K L hLK σ) k.1⁻¹ =
      D.frobeniusFixedField K L hLK σ :=
      D.conjugate_frobeniusFixedField_eq_of_commutes K L hLK σ q hq
    D.frobeniusFixedFieldAction A K L hLK σ q hq a =
      conjugateStableAction A (D.frobeniusFixedField K L hLK σ)
        k.1⁻¹ hstable a := by
  dsimp only
  apply Subtype.ext
  rw [D.frobeniusFixedFieldAction_coe, conjugateStableAction_coe]
  simp

/-- Relative norm in a power-fixed-field tower is equivariant for every
quotient element commuting with both defining powers. -/
theorem relativeNorm_frobeniusFixedFieldAction (D : DegreeData G) (A : Rep ℤ G)
    [IsTopologicalGroup G] [CompactSpace G] [T2Space G]
    [TotallyDisconnectedSpace G]
    (K : FiniteResidueAbstractField D) (L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.field.toSubgroup)
    [hLnormal : (extensionSubgroup K.field L hLK).Normal]
    (σ σ' : D.FrobeniusElements K L hLK)
    (hTS : (D.frobeniusFixedField K L hLK σ').toSubgroup ≤
      (D.frobeniusFixedField K L hLK σ).toSubgroup)
    [Finite ((D.frobeniusFixedField K L hLK σ).toSubgroup ⧸
      extensionSubgroup (D.frobeniusFixedField K L hLK σ)
        (D.frobeniusFixedField K L hLK σ') hTS)]
    (q : K.field.toSubgroup ⧸ D.extensionInertiaWithin K.field L hLK)
    (hq : q * σ.1 = σ.1 * q)
    (hq' : q * σ'.1 = σ'.1 * q)
    (a : ambientFixedAddSubgroup A
      (D.frobeniusFixedField K L hLK σ')) :
    relativeNorm A (D.frobeniusFixedField K L hLK σ)
        (D.frobeniusFixedField K L hLK σ') hTS
        (D.frobeniusFixedFieldAction A K L hLK σ' q hq' a) =
      D.frobeniusFixedFieldAction A K L hLK σ q hq
        (relativeNorm A (D.frobeniusFixedField K L hLK σ)
          (D.frobeniusFixedField K L hLK σ') hTS a) := by
  let k : K.field.toSubgroup := Quotient.out q
  let hSstable := D.conjugate_frobeniusFixedField_eq_of_commutes
    K L hLK σ q hq
  let hTstable := D.conjugate_frobeniusFixedField_eq_of_commutes
    K L hLK σ' q hq'
  rw [D.frobeniusFixedFieldAction_eq_conjugateStableAction
    A K L hLK σ' q hq' a]
  rw [relativeNorm_conjugateStableAction]
  rw [D.frobeniusFixedFieldAction_eq_conjugateStableAction
    A K L hLK σ q hq]

/-- A Frobenius power sum commutes with the relative norm in a fixed-field
tower whenever the quotient element stabilizes both fields. -/
theorem fixedFieldPowerSum_relativeNorm (D : DegreeData G) (A : Rep ℤ G)
    [IsTopologicalGroup G] [CompactSpace G] [T2Space G]
    [TotallyDisconnectedSpace G]
    (K : FiniteResidueAbstractField D) (L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.field.toSubgroup)
    [hLnormal : (extensionSubgroup K.field L hLK).Normal]
    (σ σ' : D.FrobeniusElements K L hLK)
    (hTS : (D.frobeniusFixedField K L hLK σ').toSubgroup ≤
      (D.frobeniusFixedField K L hLK σ).toSubgroup)
    [Finite ((D.frobeniusFixedField K L hLK σ).toSubgroup ⧸
      extensionSubgroup (D.frobeniusFixedField K L hLK σ)
        (D.frobeniusFixedField K L hLK σ') hTS)]
    (q : K.field.toSubgroup ⧸ D.extensionInertiaWithin K.field L hLK)
    (hq : q * σ.1 = σ.1 * q) (hq' : q * σ'.1 = σ'.1 * q)
    (n : ℕ)
    (a : ambientFixedAddSubgroup A
      (D.frobeniusFixedField K L hLK σ')) :
    relativeNorm A (D.frobeniusFixedField K L hLK σ)
        (D.frobeniusFixedField K L hLK σ') hTS
        (∑ i : Fin n,
          D.frobeniusFixedFieldAction A K L hLK σ'
            (q ^ i.1) (Commute.pow_left hq' i.1) a) =
      ∑ i : Fin n,
        D.frobeniusFixedFieldAction A K L hLK σ
          (q ^ i.1) (Commute.pow_left hq i.1)
          (relativeNorm A (D.frobeniusFixedField K L hLK σ)
            (D.frobeniusFixedField K L hLK σ') hTS a) := by
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro i _
  exact D.relativeNorm_frobeniusFixedFieldAction A K L hLK
    σ σ' hTS (q ^ i.1) (Commute.pow_left hq i.1)
      (Commute.pow_left hq' i.1) a

/-- The fixed-field power sum becomes the global Frobenius power sum after
inclusion into the maximal unramified field. -/
theorem fixedFieldPowerSum_inclusion (D : DegreeData G) (A : Rep ℤ G)
    [IsTopologicalGroup G] [CompactSpace G] [T2Space G]
    [TotallyDisconnectedSpace G]
    (K : FiniteResidueAbstractField D) (L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.field.toSubgroup)
    [hLnormal : (extensionSubgroup K.field L hLK).Normal]
    (σ : D.FrobeniusElements K L hLK)
    (q : K.field.toSubgroup ⧸ D.extensionInertiaWithin K.field L hLK)
    (hq : q * σ.1 = σ.1 * q) (n : ℕ)
    (a : ambientFixedAddSubgroup A
      (D.frobeniusFixedField K L hLK σ)) :
    fixedFieldInclusion A (D.frobeniusFixedField K L hLK σ)
        (D.maximalUnramifiedField L)
        (D.fieldInertia_le_frobeniusFixedField K L hLK σ)
        (∑ i : Fin n,
          D.frobeniusFixedFieldAction A K L hLK σ
            (q ^ i.1) (Commute.pow_left hq i.1) a) =
      D.frobeniusPowerSum A K.field L hLK q n
        (fixedFieldInclusion A (D.frobeniusFixedField K L hLK σ)
          (D.maximalUnramifiedField L)
          (D.fieldInertia_le_frobeniusFixedField K L hLK σ) a) := by
  apply Subtype.ext
  rw [D.frobeniusPowerSum_coe]
  change
    (AddSubgroup.subtype (ambientFixedAddSubgroup A
      (D.frobeniusFixedField K L hLK σ)))
        (∑ i : Fin n,
          D.frobeniusFixedFieldAction A K L hLK σ
            (q ^ i.1) (Commute.pow_left hq i.1) a) = _
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro i _
  exact congrArg Subtype.val
    (D.frobeniusFixedFieldAction_inclusion A K L hLK σ
      (q ^ i.1) (Commute.pow_left hq i.1) a)

end DegreeData

end fixedFieldActions

end

end ClassFormation
end

section
-- module Solutions.OAIQ244_DUKE.AbstractClassFieldTheory_Reciprocity_Construction_FiniteIntermediateFieldCompositum
attribute [-instance] _root_.ClassFormation.DegreeData.FiniteAmbientFrobeniusFixedFieldTower.ambientRepresentedQuotientFinite _root_.ClassFormation.DegreeData.FrobeniusFixedFieldTower.baseAbsoluteFiniteInstance _root_.ClassFormation.DegreeData.FrobeniusFixedFieldTower.extensionFinite _root_.ClassFormation.DegreeData.FrobeniusFixedFieldTower.extensionNormal _root_.ClassFormation.DegreeData.FrobeniusFixedFieldTower.fieldAbsoluteFiniteInstance _root_.ClassFormation.DegreeData.FrobeniusPowerFixedFieldTower.baseRepresentedAbsoluteFinite _root_.ClassFormation.DegreeData.FrobeniusPowerFixedFieldTower.fieldRepresentedAbsoluteFinite _root_.ClassFormation.DegreeData.FrobeniusPowerFixedFieldTower.relativeRepresentedQuotientFinite _root_.ClassFormation.FiniteAbstractField.toFiniteResidueAbstractField_extensionFinite _root_.ClassFormation.FiniteAbstractField.toFiniteResidueAbstractField_extensionNormal _root_.ClassFormation.FiniteGaloisSubextension.extensionSubgroup_normalInstance _root_.ClassFormation.FiniteGaloisSubextension.extensionSubgroup_over_intermediate_normalInstance _root_.ClassFormation.FiniteGaloisSubextension.intermediateField_normalInstance _root_.ClassFormation.finiteNormQuotientAddCommGroup _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace
attribute [-simp] _root_.ClassFormation.ValuationData.mem_infiniteUnitNormSubgroup_iff _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.LocalFieldTheory.residueField_algebraMap_residue _root_.OAI.PrimeDegreePackets.ThetaConstruction.schwartzCM_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

universe u v

namespace ClassFormation

open KummerTheory
open CyclicCohomology

/-!
# Finite intermediate-field composita

This module records the quotient cardinal and common-compositum facts for
finite intermediate fields used by the norm-descent tower.
-/

noncomputable section

open CategoryTheory
open scoped BigOperators

section finiteIntermediateFields

variable {G : Type u} [Group G] [TopologicalSpace G]

namespace FiniteIntermediateField

/-- Cardinality of the finite relative Galois quotient attached to a finite
intermediate field.  Recording the supplied `Finite` instance in the
definition lets later fixed-field constructions use the cardinality without
adding a second finiteness parameter. -/
noncomputable def quotientCard {E K : ClosedSubgroup G}
    (M : FiniteIntermediateField E K) : ℕ := by
  letI : Finite
      (K.toSubgroup ⧸ extensionSubgroup K M.field M.below) := M.finite
  exact Nat.card
    (K.toSubgroup ⧸ extensionSubgroup K M.field M.below)

/-- The finite quotient used in the descent construction has positive cardinality. -/
theorem quotientCard_pos {E K : ClosedSubgroup G}
    (M : FiniteIntermediateField E K) : 0 < M.quotientCard := by
  let : Finite
      (K.toSubgroup ⧸ extensionSubgroup K M.field M.below) := M.finite
  exact Nat.card_pos

/-- An initial finite stage and finitely many further stages have a common
finite overfield.  This existential form avoids choosing an artificial
ordering of the finite family. -/
theorem exists_common_compositum {E K : ClosedSubgroup G} {ι : Type v}
    (M : FiniteIntermediateField E K) (s : Finset ι)
    (F : ι → FiniteIntermediateField E K) :
    ∃ P : FiniteIntermediateField E K,
      P.field.toSubgroup ≤ M.field.toSubgroup ∧
        ∀ i ∈ s, P.field.toSubgroup ≤ (F i).field.toSubgroup := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      exact ⟨M, le_rfl, by simp⟩
  | @insert i s hi ih =>
      rcases ih with ⟨P, hPM, hPF⟩
      let Q := P.compositum (F i)
      refine ⟨Q, (P.compositum_le_left (F i)).trans hPM, ?_⟩
      intro j hj
      rw [Finset.mem_insert] at hj
      rcases hj with hji | hj
      · simpa [hji] using P.compositum_le_right (F i)
      · exact (P.compositum_le_left (F i)).trans (hPF j hj)

end FiniteIntermediateField

end finiteIntermediateFields

end

end ClassFormation
end

section
-- module Solutions.OAIQ244_DUKE.AbstractClassFieldTheory_Reciprocity_Construction_FrobeniusPowerFixedField
attribute [-instance] _root_.ClassFormation.DegreeData.FiniteAmbientFrobeniusFixedFieldTower.ambientQuotientFinite _root_.ClassFormation.DegreeData.FiniteAmbientFrobeniusFixedFieldTower.ambientRepresentedQuotientFinite _root_.ClassFormation.DegreeData.FrobeniusFixedFieldTower.baseAbsoluteFiniteInstance _root_.ClassFormation.DegreeData.FrobeniusFixedFieldTower.extensionFinite _root_.ClassFormation.DegreeData.FrobeniusFixedFieldTower.extensionNormal _root_.ClassFormation.DegreeData.FrobeniusFixedFieldTower.fieldAbsoluteFiniteInstance _root_.ClassFormation.DegreeData.FrobeniusPowerFixedFieldTower.baseRepresentedAbsoluteFinite _root_.ClassFormation.DegreeData.FrobeniusPowerFixedFieldTower.fieldRepresentedAbsoluteFinite _root_.ClassFormation.DegreeData.FrobeniusPowerFixedFieldTower.relativeRepresentedQuotientFinite _root_.ClassFormation.FiniteAbstractField.toFiniteResidueAbstractField_extensionFinite _root_.ClassFormation.FiniteAbstractField.toFiniteResidueAbstractField_extensionNormal _root_.ClassFormation.FiniteGaloisSubextension.extensionSubgroup_normalInstance _root_.ClassFormation.FiniteGaloisSubextension.extensionSubgroup_over_intermediate_normalInstance _root_.ClassFormation.FiniteGaloisSubextension.intermediateField_normalInstance _root_.ClassFormation.finiteNormQuotientAddCommGroup _root_.ClassFormation.instIsAddTorsionFreeZHat _root_.ClassFormation.instIsMulTorsionFreeMultiplicativeZHat _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.OAI.PrimeDegreePackets.xT2Space _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.CyclicCohomology.binaryCoefficientFamilyCommGroup _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace
attribute [-simp] _root_.ClassFormation.DegreeData.chosenUnramifiedFrobeniusLift_exponent _root_.ClassFormation.DegreeData.finiteReciprocityCandidate_apply _root_.ClassFormation.DegreeData.finiteReciprocityCandidate_zero _root_.ClassFormation.DegreeData.frobeniusActionConjugate_coe _root_.ClassFormation.DegreeData.frobeniusExponent_actionConjugate _root_.ClassFormation.DegreeData.frobeniusExponent_chosenDegreeOneFrobeniusElement _root_.ClassFormation.DegreeData.frobeniusExponent_mul _root_.ClassFormation.DegreeData.frobeniusFixedFieldAction_coe _root_.ClassFormation.DegreeData.frobeniusLiftDifference_coe _root_.ClassFormation.DegreeData.frobeniusQuotientRepresentation_apply _root_.ClassFormation.DegreeData.frobeniusRestriction_chosenFiniteReciprocityFrobeniusLift _root_.ClassFormation.DegreeData.frobeniusRestriction_mul _root_.ClassFormation.DegreeData.maximalUnramifiedToFiniteNormQuotient_maximalUnramifiedNormClass _root_.ClassFormation.FiniteAbelianSubextension.extensionQuotientMk_apply _root_.ClassFormation.FiniteGaloisSubextension.extensionQuotientMk_apply _root_.ClassFormation.FiniteGaloisSubextension.extensionQuotientMk_eq_one_iff _root_.ClassFormation.FiniteGaloisSubextension.toGaloisSubextension_isTotallyRamified_iff _root_.ClassFormation.FiniteGaloisSubextension.toGaloisSubextension_isUnramified_iff _root_.ClassFormation.ValuationData.canonicalUnramifiedNormQuotientValuation_finiteNormClass _root_.ClassFormation.ValuationData.canonicalValueQuotientHom_mk _root_.ClassFormation.ValuationData.canonicalValueReduction_one _root_.ClassFormation.ValuationData.mem_infiniteUnitAddSubgroup_iff _root_.ClassFormation.ValuationData.mem_infiniteUnitNormSubgroup_iff _root_.ClassFormation.ValuationData.unramifiedNormQuotientValuation_finiteNormClass _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.ClassFormation.cyclicNormClassHom_apply _root_.ClassFormation.extensionFixedRepresentationEquiv_apply_coe _root_.ClassFormation.extensionFixedRepresentationEquiv_symm_apply_coe _root_.ClassFormation.finiteNormClass_add _root_.ClassFormation.finiteNormClass_eq_zero_iff _root_.ClassFormation.finiteNormClass_nsmul _root_.ClassFormation.finiteNormClass_sub _root_.ClassFormation.finiteNormClass_zero _root_.ClassFormation.finiteNormQuotientConcreteEquiv_finiteNormClass _root_.ClassFormation.finiteNormQuotientLift_finiteNormClass _root_.ClassFormation.toZModPow_zHatToPadicInt _root_.ClassFormation.zHatReductionRingHom_apply _root_.ClassFormation.zHatRingEquivProfiniteIntegerPrimeProduct_apply _root_.ClassFormation.zHatToPadicInt_intCast _root_.ClassFormation.zHatToProfiniteIntegerPrimeProduct_apply _root_.ClassFormation.zHatToProfiniteIntegerPrimeProduct_intCast _root_.ClassFormation.zHatUnitsContinuousMulEquivPrimeProduct_coe_apply _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.LocalFieldTheory.residueField_algebraMap_residue _root_.OAI.PrimeDegreePackets.ThetaConstruction.schwartzCM_apply
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

/-!
# Frobenius power fixed fields

This module constructs the fixed fields of powers of a Frobenius element and
proves their inclusion, exponent, normality, unramifiedness, finiteness,
degree, quotient-cardinality, and generator properties.
-/

noncomputable section

open CategoryTheory
open scoped BigOperators

section degreeOnePowerFields

variable {G : Type u} [Group G] [TopologicalSpace G]

namespace DegreeData

/-- An element fixing `L` commutes modulo `G_{\widetilde L}` with every
degree-zero element of `G(\widetilde L/K)`.  Group-theoretically this is
`[G_L,I_K] ⊆ G_L ∩ I_K = G_{\widetilde L}`; it is the reason the
fields fixed by the powers of `φⁿ` in the universal norm-descent lemma are stable under the
elements `τᵢ` occurring in `(*)`. -/
theorem extensionInertia_commutes_of_mem_extensionSubgroup (D : DegreeData G)
    (K : FiniteResidueAbstractField D) (L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.field.toSubgroup)
    [hLnormal : (extensionSubgroup K.field L hLK).Normal]
    (k : K.field.toSubgroup) (hk : k ∈ extensionSubgroup K.field L hLK)
    (q : K.field.toSubgroup ⧸ D.extensionInertiaWithin K.field L hLK)
    (hq : D.extensionNormalizedDegree K L hLK q = 1) :
    (QuotientGroup.mk k :
        K.field.toSubgroup ⧸ D.extensionInertiaWithin K.field L hLK) * q =
      q * QuotientGroup.mk k := by
  revert hq
  refine Quotient.inductionOn' q ?_
  intro t hdt
  have htI : t ∈ D.fieldInertiaWithin K.field := by
    rw [← D.normalizedDegree_ker K]
    exact hdt
  change QuotientGroup.mk (k * t) = QuotientGroup.mk (t * k)
  apply QuotientGroup.eq.mpr
  constructor
  · change (k * t)⁻¹ * (t * k) ∈ extensionSubgroup K.field L hLK
    have hconj : t⁻¹ * k⁻¹ * t ∈ extensionSubgroup K.field L hLK := by
      simpa using hLnormal.conj_mem k⁻¹
        ((extensionSubgroup K.field L hLK).inv_mem hk) t⁻¹
    simpa [mul_assoc] using
      (extensionSubgroup K.field L hLK).mul_mem hconj hk
  · change (k * t)⁻¹ * (t * k) ∈ D.fieldInertiaWithin K.field
    have hconj : k⁻¹ * t * k ∈ D.fieldInertiaWithin K.field := by
      simpa using (inferInstance : (D.fieldInertiaWithin K.field).Normal).conj_mem
        t htI k⁻¹
    simp [mul_assoc]

/-- Let `P/K` be a finite Galois subextension of `\widetilde L/K`
containing `L`.  The `|G(P/K)|`-th power of every element of
`G(\widetilde L/K)` fixes `P`, hence commutes with the degree-zero kernel.
This is the precise finite-stage input behind the choice
`n = [M:K]`, `σ = φⁿ`. -/
theorem quotientPower_card_commutes_degreeZero (D : DegreeData G)
    (K : FiniteResidueAbstractField D) (L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.field.toSubgroup)
    [hLnormal : (extensionSubgroup K.field L hLK).Normal]
    (P : FiniteIntermediateField (D.maximalUnramifiedField L) K.field)
    (hPL : P.field.toSubgroup ≤ L.toSubgroup)
    [hPnormal : (extensionSubgroup K.field P.field P.below).Normal]
    (q τ : K.field.toSubgroup ⧸ D.extensionInertiaWithin K.field L hLK)
    (hτ : D.extensionNormalizedDegree K L hLK τ = 1) :
    let n := Nat.card
      (K.field.toSubgroup ⧸ extensionSubgroup K.field P.field P.below)
    q ^ n * τ = τ * q ^ n := by
  let R := K.field.toSubgroup ⧸ extensionSubgroup K.field P.field P.below
  let : Finite R := P.finite
  let n := Nat.card R
  let Q := K.field.toSubgroup ⧸ D.extensionInertiaWithin K.field L hLK
  let hIP : D.extensionInertiaWithin K.field L hLK ≤
      extensionSubgroup K.field P.field P.below := by
    intro x hx
    have hxE : x ∈ extensionSubgroup K.field (D.maximalUnramifiedField L)
        (D.maximalUnramifiedField_le_of_le hLK) := by
      rw [D.extensionSubgroup_maximalUnramifiedField K.field L hLK]
      exact hx
    apply (mem_extensionSubgroup_iff K.field P.field P.below x).2
    exact P.above
      ((mem_extensionSubgroup_iff K.field (D.maximalUnramifiedField L)
        (D.maximalUnramifiedField_le_of_le hLK) x).1 hxE)
  let rP : Q →* R :=
    QuotientGroup.map (D.extensionInertiaWithin K.field L hLK)
      (extensionSubgroup K.field P.field P.below)
      (MonoidHom.id K.field.toSubgroup) hIP
  let k : K.field.toSubgroup := Quotient.out (q ^ n)
  have hkq : (QuotientGroup.mk k : Q) = q ^ n :=
    Quotient.out_eq' (q ^ n)
  have hrPpow : rP (q ^ n) = 1 := by
    rw [map_pow]
    exact pow_card_eq_one'
  have hkP : k ∈ extensionSubgroup K.field P.field P.below := by
    apply (QuotientGroup.eq_one_iff k).1
    calc
      (QuotientGroup.mk k : R) = rP (QuotientGroup.mk k) := rfl
      _ = rP (q ^ n) := congrArg rP hkq
      _ = 1 := hrPpow
  have hkL : k ∈ extensionSubgroup K.field L hLK := by
    apply (mem_extensionSubgroup_iff K.field L hLK k).2
    exact hPL ((mem_extensionSubgroup_iff K.field P.field P.below k).1 hkP)
  have hcomm := D.extensionInertia_commutes_of_mem_extensionSubgroup
    K L hLK k hkL τ hτ
  simpa [Q, n, hkq] using hcomm

/-- If `P/K` is finite Galois and contained in `\widetilde L`, then `P`
is contained in the field fixed by `φⁿ`, where
`n = |G(P/K)|`.  Indeed `φⁿ` is trivial in `G(P/K)`, and the kernel
of the restriction map is closed, so it contains the whole procyclic
closure generated by `φⁿ`. -/
theorem frobeniusPowerFixedField_le_finiteField (D : DegreeData G)
    [IsTopologicalGroup G] [CompactSpace G] [T2Space G]
    (K : FiniteResidueAbstractField D) (L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.field.toSubgroup)
    [hLnormal : (extensionSubgroup K.field L hLK).Normal]
    (P : FiniteIntermediateField (D.maximalUnramifiedField L) K.field)
    [hPnormal : (extensionSubgroup K.field P.field P.below).Normal]
    (φ : D.FrobeniusElements K L hLK)
    (hφ : D.frobeniusExponent K L hLK φ = 1) :
    let n := P.quotientCard
    let hn : 0 < n := P.quotientCard_pos
    (D.frobeniusFixedField K L hLK
      (D.frobeniusPowerOfDegreeOne K L hLK φ hφ n hn)).toSubgroup ≤
      P.field.toSubgroup := by
  dsimp only
  let R := K.field.toSubgroup ⧸ extensionSubgroup K.field P.field P.below
  let n := P.quotientCard
  have hn : 0 < n := P.quotientCard_pos
  let Q := K.field.toSubgroup ⧸ D.extensionInertiaWithin K.field L hLK
  let hIP : D.extensionInertiaWithin K.field L hLK ≤
      extensionSubgroup K.field P.field P.below := by
    intro x hx
    have hxE : x ∈ extensionSubgroup K.field (D.maximalUnramifiedField L)
        (D.maximalUnramifiedField_le_of_le hLK) := by
      rw [D.extensionSubgroup_maximalUnramifiedField K.field L hLK]
      exact hx
    apply (mem_extensionSubgroup_iff K.field P.field P.below x).2
    exact P.above
      ((mem_extensionSubgroup_iff K.field (D.maximalUnramifiedField L)
        (D.maximalUnramifiedField_le_of_le hLK) x).1 hxE)
  let rP : Q →ₜ* R :=
    { toMonoidHom :=
        QuotientGroup.map
          (N := D.extensionInertiaWithin K.field L hLK)
          (M := extensionSubgroup K.field P.field P.below)
          (f := MonoidHom.id K.field.toSubgroup) hIP
      continuous_toFun := by
        refine (QuotientGroup.isQuotientMap_mk
          (G := K.field.toSubgroup)
          (N := D.extensionInertiaWithin K.field L hLK)).continuous_iff.2 ?_
        change Continuous
          (⇑(QuotientGroup.map
              (D.extensionInertiaWithin K.field L hLK)
              (extensionSubgroup K.field P.field P.below)
              (MonoidHom.id K.field.toSubgroup) hIP) ∘
            QuotientGroup.mk'
              (D.extensionInertiaWithin K.field L hLK))
        have hcomp :
            (⇑(QuotientGroup.map
                (D.extensionInertiaWithin K.field L hLK)
                (extensionSubgroup K.field P.field P.below)
                (MonoidHom.id K.field.toSubgroup) hIP) ∘
              QuotientGroup.mk'
                (D.extensionInertiaWithin K.field L hLK)) =
              QuotientGroup.mk'
                (extensionSubgroup K.field P.field P.below) := by
          funext k
          exact QuotientGroup.map_mk' _ _ _ _ k
        rw [hcomp]
        exact continuous_quotient_mk' }
  let : Finite R := P.finite
  let : IsClosed
      (extensionSubgroup K.field P.field P.below : Set K.field.toSubgroup) :=
    extensionSubgroup_isClosed K.field P.field P.below
  have hrPpow : rP (φ.1 ^ n) = 1 := by
    rw [map_pow]
    change (rP φ.1) ^ Nat.card R = 1
    exact pow_card_eq_one'
  let σ := D.frobeniusPowerOfDegreeOne K L hLK φ hφ n hn
  have hclosure :
      (D.frobeniusClosure K L hLK σ).toSubgroup ≤
        rP.toMonoidHom.ker := by
    apply Subgroup.topologicalClosure_minimal
    · rw [Subgroup.closure_le]
      intro z hz
      have hz' : z = φ.1 ^ n := by simpa [σ] using hz
      subst z
      exact hrPpow
    · change IsClosed {x : Q | rP x = 1}
      exact isClosed_eq rP.continuous continuous_const
  rintro g ⟨k, hk, rfl⟩
  apply (mem_extensionSubgroup_iff K.field P.field P.below k).1
  apply (QuotientGroup.eq_one_iff k).1
  have hk' := hclosure hk
  change QuotientGroup.mk' (extensionSubgroup K.field P.field P.below) k = 1 at hk'
  exact hk'

/-- The extension fixed by `φⁿᵐ` over the field fixed by `φⁿ` is
unramified. -/
theorem frobeniusPowerFixedField_isUnramified (D : DegreeData G)
    [IsTopologicalGroup G] [CompactSpace G] [T2Space G]
    [TotallyDisconnectedSpace G]
    (K : FiniteResidueAbstractField D) (L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.field.toSubgroup)
    [hLnormal : (extensionSubgroup K.field L hLK).Normal]
    (φ : D.FrobeniusElements K L hLK)
    (hφ : D.frobeniusExponent K L hLK φ = 1)
    (n m : ℕ) (hn : 0 < n) (hm : 0 < m) :
    let σ := D.frobeniusPowerOfDegreeOne K L hLK φ hφ n hn
    let σm := D.frobeniusPowerOfDegreeOne K L hLK φ hφ (n * m)
      (Nat.mul_pos hn hm)
    let S := D.frobeniusFixedField K L hLK σ
    let T := D.frobeniusFixedField K L hLK σm
    let hTS := D.frobeniusPowerFixedField_le K L hLK φ hφ n m hn hm
    (DegreeData.AbstractExtension.mk T S hTS).IsUnramified D := by
  dsimp only
  let σ := D.frobeniusPowerOfDegreeOne K L hLK φ hφ n hn
  let σm := D.frobeniusPowerOfDegreeOne K L hLK φ hφ (n * m)
    (Nat.mul_pos hn hm)
  let S := D.frobeniusFixedField K L hLK σ
  let T := D.frobeniusFixedField K L hLK σm
  let hTS := D.frobeniusPowerFixedField_le K L hLK φ hφ n m hn hm
  rw [(DegreeData.AbstractExtension.mk T S hTS).isUnramified_iff_inertia_le D]
  intro x hx
  have hxI : x ∈ D.fieldInertia S := ⟨hx.1, hx.2⟩
  have hSI : D.fieldInertia S = D.fieldInertia L :=
    D.frobeniusFixedField_fieldInertia K L hLK σ
  have hTI : D.fieldInertia T = D.fieldInertia L :=
    D.frobeniusFixedField_fieldInertia K L hLK σm
  rw [hSI, ← hTI] at hxI
  exact hxI.1

/-- Finiteness of the power-fixed-field tower. -/
theorem frobeniusPowerFixedField_finite (D : DegreeData G)
    [IsTopologicalGroup G] [CompactSpace G] [T2Space G]
    (K : FiniteResidueAbstractField D) (L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.field.toSubgroup)
    [hLnormal : (extensionSubgroup K.field L hLK).Normal]
    [hLfinite : Finite
      (K.field.toSubgroup ⧸ extensionSubgroup K.field L hLK)]
    (φ : D.FrobeniusElements K L hLK)
    (hφ : D.frobeniusExponent K L hLK φ = 1)
    (n m : ℕ) (hn : 0 < n) (hm : 0 < m) :
    let σ := D.frobeniusPowerOfDegreeOne K L hLK φ hφ n hn
    let σm := D.frobeniusPowerOfDegreeOne K L hLK φ hφ (n * m)
      (Nat.mul_pos hn hm)
    let S := D.frobeniusFixedField K L hLK σ
    let T := D.frobeniusFixedField K L hLK σm
    let hTS := D.frobeniusPowerFixedField_le K L hLK φ hφ n m hn hm
    Finite (S.toSubgroup ⧸ extensionSubgroup S T hTS) := by
  dsimp only
  let σ := D.frobeniusPowerOfDegreeOne K L hLK φ hφ n hn
  let σm := D.frobeniusPowerOfDegreeOne K L hLK φ hφ (n * m)
    (Nat.mul_pos hn hm)
  let S := D.frobeniusFixedField K L hLK σ
  let T := D.frobeniusFixedField K L hLK σm
  let hSK := D.frobeniusFixedField_le K L hLK σ
  let hTK := D.frobeniusFixedField_le K L hLK σm
  let hTS := D.frobeniusPowerFixedField_le K L hLK φ hφ n m hn hm
  let hTKfinite : Finite
      (K.field.toSubgroup ⧸ extensionSubgroup K.field T hTK) :=
    D.frobeniusFixedField_finite K L hLK σm
  exact FiniteIntermediateField.finite_extension_of_le hTK hSK hTS

/-- The relative degree of the tower fixed by φⁿᵐ over the field fixed
by φⁿ is exactly m. -/
theorem frobeniusPowerFixedField_relIndex (D : DegreeData G)
    [IsTopologicalGroup G] [CompactSpace G] [T2Space G]
    [TotallyDisconnectedSpace G]
    (K : FiniteResidueAbstractField D) (L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.field.toSubgroup)
    [hLnormal : (extensionSubgroup K.field L hLK).Normal]
    (φ : D.FrobeniusElements K L hLK)
    (hφ : D.frobeniusExponent K L hLK φ = 1)
    (n m : ℕ) (hn : 0 < n) (hm : 0 < m) :
    let σ := D.frobeniusPowerOfDegreeOne K L hLK φ hφ n hn
    let σm := D.frobeniusPowerOfDegreeOne K L hLK φ hφ
      (n * m) (Nat.mul_pos hn hm)
    let S := D.frobeniusFixedField K L hLK σ
    let T := D.frobeniusFixedField K L hLK σm
    T.toSubgroup.relIndex S.toSubgroup = m := by
  dsimp only
  let σ := D.frobeniusPowerOfDegreeOne K L hLK φ hφ n hn
  let σm := D.frobeniusPowerOfDegreeOne K L hLK φ hφ
    (n * m) (Nat.mul_pos hn hm)
  let S := D.frobeniusFixedField K L hLK σ
  let T := D.frobeniusFixedField K L hLK σm
  let hTS := D.frobeniusPowerFixedField_le
    K L hLK φ hφ n m hn hm
  have hTSunramified : (DegreeData.AbstractExtension.mk T S hTS).IsUnramified D :=
    D.frobeniusPowerFixedField_isUnramified
      K L hLK φ hφ n m hn hm
  have hTSramification :
      (T.toSubgroup ⊓ D.degree.toMonoidHom.ker).relIndex
          (S.toSubgroup ⊓ D.degree.toMonoidHom.ker) = 1 := by
    rw [Subgroup.relIndex_eq_one]
    intro x hx
    exact ⟨hTSunramified hx, hx.2⟩
  rw [relIndex_eq_map_relIndex_mul_inf_ker_relIndex
      D.degree.toMonoidHom hTS,
    hTSramification, Nat.mul_one]
  let SR := D.frobeniusFixedResidueField K L hLK σ
  let TR := D.frobeniusFixedResidueField K L hLK σm
  have hSindex : (D.fieldImage S).index = (SR.residueDegree : ℕ) := by
    have h := D.fieldImageAdd_index SR
    change (D.fieldImage S).index = (SR.residueDegree : ℕ) at h
    exact h
  have hTindex : (D.fieldImage T).index = (TR.residueDegree : ℕ) := by
    have h := D.fieldImageAdd_index TR
    change (D.fieldImage T).index = (TR.residueDegree : ℕ) at h
    exact h
  have hresidueMul :
      (T.toSubgroup.map D.degree.toMonoidHom).relIndex
          (S.toSubgroup.map D.degree.toMonoidHom) *
          (SR.residueDegree : ℕ) = (TR.residueDegree : ℕ) := by
    rw [← hSindex, ← hTindex, D.fieldImage_eq_map, D.fieldImage_eq_map]
    exact Subgroup.relIndex_mul_index (Subgroup.map_mono hTS)
  rw [D.frobeniusFixedResidueField_residueDegree K L hLK σ,
    D.frobeniusFixedResidueField_residueDegree K L hLK σm] at hresidueMul
  rw [show D.frobeniusExponent K L hLK σm = n * m by
      exact D.frobeniusExponent_powerOfDegreeOne
        K L hLK φ hφ (n * m) (Nat.mul_pos hn hm),
    show D.frobeniusExponent K L hLK σ = n by
      exact D.frobeniusExponent_powerOfDegreeOne
        K L hLK φ hφ n hn] at hresidueMul
  apply Nat.eq_of_mul_eq_mul_right (Nat.mul_pos hn K.residueDegree.property)
  calc
    (T.toSubgroup.map D.degree.toMonoidHom).relIndex
          (S.toSubgroup.map D.degree.toMonoidHom) *
        (n * (K.residueDegree : ℕ)) =
      (n * m) * (K.residueDegree : ℕ) := hresidueMul
    _ = m * (n * (K.residueDegree : ℕ)) := by ac_rfl

/-- The quotient between two successive Frobenius power fixed fields is
genuinely finite.  This is obtained from the computed finite relative index,
before taking its natural-valued cardinality. -/
theorem frobeniusPowerFixedField_quotientFinite (D : DegreeData G)
    [IsTopologicalGroup G] [CompactSpace G] [T2Space G]
    [TotallyDisconnectedSpace G]
    (K : FiniteResidueAbstractField D) (L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.field.toSubgroup)
    [hLnormal : (extensionSubgroup K.field L hLK).Normal]
    (φ : D.FrobeniusElements K L hLK)
    (hφ : D.frobeniusExponent K L hLK φ = 1)
    (n m : ℕ) (hn : 0 < n) (hm : 0 < m) :
    let σ := D.frobeniusPowerOfDegreeOne K L hLK φ hφ n hn
    let σm := D.frobeniusPowerOfDegreeOne K L hLK φ hφ
      (n * m) (Nat.mul_pos hn hm)
    let S := D.frobeniusFixedField K L hLK σ
    let T := D.frobeniusFixedField K L hLK σm
    let hTS := D.frobeniusPowerFixedField_le
      K L hLK φ hφ n m hn hm
    Finite (S.toSubgroup ⧸ extensionSubgroup S T hTS) := by
  dsimp only
  let σ := D.frobeniusPowerOfDegreeOne K L hLK φ hφ n hn
  let σm := D.frobeniusPowerOfDegreeOne K L hLK φ hφ
    (n * m) (Nat.mul_pos hn hm)
  let S := D.frobeniusFixedField K L hLK σ
  let T := D.frobeniusFixedField K L hLK σm
  let hTS := D.frobeniusPowerFixedField_le
    K L hLK φ hφ n m hn hm
  apply (Subgroup.index_ne_zero_iff_finite).mp
  change T.toSubgroup.relIndex S.toSubgroup ≠ 0
  rw [D.frobeniusPowerFixedField_relIndex
    K L hLK φ hφ n m hn hm]
  exact hm.ne'

/-- Cardinality form of the preceding relative-degree computation. -/
theorem frobeniusPowerFixedField_quotientCard (D : DegreeData G)
    [IsTopologicalGroup G] [CompactSpace G] [T2Space G]
    [TotallyDisconnectedSpace G]
    (K : FiniteResidueAbstractField D) (L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.field.toSubgroup)
    [hLnormal : (extensionSubgroup K.field L hLK).Normal]
    (φ : D.FrobeniusElements K L hLK)
    (hφ : D.frobeniusExponent K L hLK φ = 1)
    (n m : ℕ) (hn : 0 < n) (hm : 0 < m) :
    let σ := D.frobeniusPowerOfDegreeOne K L hLK φ hφ n hn
    let σm := D.frobeniusPowerOfDegreeOne K L hLK φ hφ
      (n * m) (Nat.mul_pos hn hm)
    let S := D.frobeniusFixedField K L hLK σ
    let T := D.frobeniusFixedField K L hLK σm
    let hTS := D.frobeniusPowerFixedField_le
      K L hLK φ hφ n m hn hm
    Nat.card (S.toSubgroup ⧸ extensionSubgroup S T hTS) = m := by
  dsimp only
  let σ := D.frobeniusPowerOfDegreeOne K L hLK φ hφ n hn
  let σm := D.frobeniusPowerOfDegreeOne K L hLK φ hφ
    (n * m) (Nat.mul_pos hn hm)
  let S := D.frobeniusFixedField K L hLK σ
  let T := D.frobeniusFixedField K L hLK σm
  let hTS := D.frobeniusPowerFixedField_le
    K L hLK φ hφ n m hn hm
  let : Finite (S.toSubgroup ⧸ extensionSubgroup S T hTS) :=
    D.frobeniusPowerFixedField_quotientFinite
      K L hLK φ hφ n m hn hm
  calc
    Nat.card (S.toSubgroup ⧸ extensionSubgroup S T hTS) =
        (extensionSubgroup S T hTS).index := rfl
    _ = T.toSubgroup.relIndex S.toSubgroup := by
      rfl
    _ = m :=
      D.frobeniusPowerFixedField_relIndex
        K L hLK φ hφ n m hn hm

/-- The restriction of the concrete element `φⁿ` is a degree-one
generator of `Gal(Σₘ/Σ)`.  This is the generator to which the unit-cohomology axiom
is applied; retaining the actual representative is essential for
the subsequent equation involving `σ = φⁿ`. -/
theorem frobeniusPowerFixedField_generator (D : DegreeData G)
    [IsTopologicalGroup G] [CompactSpace G] [T2Space G]
    [TotallyDisconnectedSpace G]
    (K : FiniteResidueAbstractField D) (L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.field.toSubgroup)
    [hLnormal : (extensionSubgroup K.field L hLK).Normal]
    [hLfinite : Finite
      (K.field.toSubgroup ⧸ extensionSubgroup K.field L hLK)]
    (φ : D.FrobeniusElements K L hLK)
    (hφ : D.frobeniusExponent K L hLK φ = 1)
    (n m : ℕ) (hn : 0 < n) (hm : 0 < m) :
    let σ := D.frobeniusPowerOfDegreeOne K L hLK φ hφ n hn
    let σm := D.frobeniusPowerOfDegreeOne K L hLK φ hφ (n * m)
      (Nat.mul_pos hn hm)
    let S := D.frobeniusFixedField K L hLK σ
    let T := D.frobeniusFixedField K L hLK σm
    let hTS := D.frobeniusPowerFixedField_le K L hLK φ hφ n m hn hm
    let hTSnormal : (extensionSubgroup S T hTS).Normal :=
      D.frobeniusPowerFixedField_normal K L hLK φ hφ n m hn hm
    letI := hTSnormal
    ∃ s : S.toSubgroup,
      D.frobeniusFixedFieldToClosure K L hLK σ s =
          D.frobeniusInClosure K L hLK σ ∧
      D.normalizedDegree (D.frobeniusFixedResidueField K L hLK σ) s =
        Multiplicative.ofAdd (1 : ZHat) ∧
      ∀ x : S.toSubgroup ⧸ extensionSubgroup S T hTS,
        x ∈ Subgroup.zpowers (QuotientGroup.mk s) := by
  dsimp only
  let σ := D.frobeniusPowerOfDegreeOne K L hLK φ hφ n hn
  let σm := D.frobeniusPowerOfDegreeOne K L hLK φ hφ (n * m)
    (Nat.mul_pos hn hm)
  let S := D.frobeniusFixedField K L hLK σ
  let T := D.frobeniusFixedField K L hLK σm
  let hTS := D.frobeniusPowerFixedField_le K L hLK φ hφ n m hn hm
  let hTSnormal : (extensionSubgroup S T hTS).Normal :=
    D.frobeniusPowerFixedField_normal K L hLK φ hφ n m hn hm
  let := hTSnormal
  let k : K.field.toSubgroup := Quotient.out σ.1
  have hkσ :
      (QuotientGroup.mk k :
        K.field.toSubgroup ⧸ D.extensionInertiaWithin K.field L hLK) = σ.1 :=
    Quotient.out_eq' σ.1
  have hkClosure : QuotientGroup.mk k ∈
      (D.frobeniusClosure K L hLK σ).toSubgroup := by
    rw [hkσ]
    exact (D.frobeniusInClosure K L hLK σ).2
  let s : S.toSubgroup := ⟨k.1, ⟨k, hkClosure, rfl⟩⟩
  have hsClosure :
      D.frobeniusFixedFieldToClosure K L hLK σ s =
        D.frobeniusInClosure K L hLK σ := by
    apply Subtype.ext
    exact hkσ
  have hsDegree :
      D.normalizedDegree (D.frobeniusFixedResidueField K L hLK σ) s =
        Multiplicative.ofAdd (1 : ZHat) := by
    rw [← D.frobeniusFixedField_normalizedDegree_compatibility
      K L hLK σ s, hsClosure]
    exact D.fixedFieldNormalizedDegree_generator K L hLK σ
  let hTSfinite : Finite
      (S.toSubgroup ⧸ extensionSubgroup S T hTS) :=
    D.frobeniusPowerFixedField_finite K L hLK φ hφ n m hn hm
  have hTSunramified : (DegreeData.AbstractExtension.mk T S hTS).IsUnramified D :=
    D.frobeniusPowerFixedField_isUnramified
      K L hLK φ hφ n m hn hm
  let SR := D.frobeniusFixedResidueField K L hLK σ
  let : (extensionSubgroup SR.field T hTS).Normal := by
    change (extensionSubgroup S T hTS).Normal
    exact hTSnormal
  let : Finite
      (SR.field.toSubgroup ⧸ extensionSubgroup SR.field T hTS) := by
    change Finite (S.toSubgroup ⧸ extensionSubgroup S T hTS)
    exact hTSfinite
  have hTSunramifiedR :
      (DegreeData.AbstractExtension.mk T SR.field hTS).IsUnramified D := by
    change (DegreeData.AbstractExtension.mk T S hTS).IsUnramified D
    exact hTSunramified
  refine ⟨s, hsClosure, hsDegree, ?_⟩
  exact D.quotient_generator_of_unramified_degree_one
    SR T hTS hTSunramifiedR s hsDegree

end DegreeData
end degreeOnePowerFields

end

end ClassFormation
end

section
-- module Solutions.OAIQ244_DUKE.AbstractClassFieldTheory_Reciprocity_Construction_FiniteFieldUnitMaps
attribute [-instance] _root_.ClassFormation.FiniteGaloisSubextension.extensionSubgroup_over_intermediate_normalInstance _root_.ClassFormation.FiniteGaloisSubextension.intermediateField_normalInstance _root_.ClassFormation.instIsAddTorsionFreeZHat _root_.ClassFormation.instIsMulTorsionFreeMultiplicativeZHat _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.maximalIdealPowSuccQuotModule _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace
attribute [-simp] _root_.ClassFormation.DegreeData.chosenUnramifiedFrobeniusLift_exponent _root_.ClassFormation.DegreeData.finiteReciprocityCandidate_apply _root_.ClassFormation.DegreeData.finiteReciprocityCandidate_zero _root_.ClassFormation.DegreeData.frobeniusActionConjugate_coe _root_.ClassFormation.DegreeData.frobeniusExponent_actionConjugate _root_.ClassFormation.DegreeData.frobeniusExponent_chosenDegreeOneFrobeniusElement _root_.ClassFormation.DegreeData.frobeniusExponent_mul _root_.ClassFormation.DegreeData.frobeniusLiftDifference_coe _root_.ClassFormation.DegreeData.frobeniusQuotientRepresentation_apply _root_.ClassFormation.DegreeData.frobeniusRestriction_chosenFiniteReciprocityFrobeniusLift _root_.ClassFormation.DegreeData.frobeniusRestriction_mul _root_.ClassFormation.FiniteAbelianSubextension.extensionQuotientMk_apply _root_.ClassFormation.FiniteGaloisSubextension.classFieldCandidate_field _root_.ClassFormation.ValuationData.canonicalUnramifiedNormQuotientValuation_finiteNormClass _root_.ClassFormation.ValuationData.canonicalValueQuotientHom_mk _root_.ClassFormation.ValuationData.canonicalValueReduction_one _root_.ClassFormation.ValuationData.mem_infiniteUnitAddSubgroup_iff _root_.ClassFormation.ValuationData.mem_infiniteUnitNormSubgroup_iff _root_.ClassFormation.ValuationData.unramifiedNormQuotientValuation_finiteNormClass _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.ClassFormation.cyclicNormClassHom_apply _root_.ClassFormation.extensionFixedRepresentationEquiv_apply_coe _root_.ClassFormation.extensionFixedRepresentationEquiv_symm_apply_coe _root_.ClassFormation.mem_normFilterBasis_iff _root_.ClassFormation.toZModPow_zHatToPadicInt _root_.ClassFormation.zHatReductionRingHom_apply _root_.ClassFormation.zHatRingEquivProfiniteIntegerPrimeProduct_apply _root_.ClassFormation.zHatToPadicInt_intCast _root_.ClassFormation.zHatToProfiniteIntegerPrimeProduct_apply _root_.ClassFormation.zHatToProfiniteIntegerPrimeProduct_intCast _root_.ClassFormation.zHatUnitsContinuousMulEquivPrimeProduct_coe_apply _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.LocalFieldTheory.residueField_algebraMap_residue _root_.OAI.PrimeDegreePackets.ThetaConstruction.schwartzCM_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

universe u v

namespace ClassFormation

open KummerTheory
open CyclicCohomology

/-!
# Finite-field unit maps

This module proves valuation invariance on Frobenius fixed fields and
constructs the induced actions, inclusions, and relative norms on the
corresponding finite unit groups.
-/

noncomputable section

open CategoryTheory
open scoped BigOperators

variable {G : IntegralRepGroupType} [Group G] [TopologicalSpace G]

namespace ValuationData

variable {D : DegreeData G} {A : Rep ℤ G}

theorem ambientFixedAddSubgroup_transport_coe
    (K L : FiniteAbstractField G) (h : K = L)
    (a : ambientFixedAddSubgroup A K.field) :
    (((h ▸ a : ambientFixedAddSubgroup A L.field) : A.V)) = a.1 := by
  cases h
  rfl

theorem valuationAt_transport
    (v : ValuationData D A) (K L : FiniteAbstractField G) (h : K = L)
    (a : ambientFixedAddSubgroup A K.field) :
    v.valuationAt L (h ▸ a) = v.valuationAt K a := by
  cases h
  rfl

/-- A quotient element stabilizing a Frobenius fixed field preserves its
normalized valuation. -/
theorem valuationAt_frobeniusFixedFieldAction
    (v : ValuationData D A)
    [IsTopologicalGroup G] [CompactSpace G] [T2Space G]
    [TotallyDisconnectedSpace G]
    (K : DegreeData.FiniteResidueAbstractField D) (L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.field.toSubgroup)
    [hLnormal : (extensionSubgroup K.field L hLK).Normal]
    (σ : D.FrobeniusElements K L hLK)
    (q : K.field.toSubgroup ⧸ D.extensionInertiaWithin K.field L hLK)
    (hq : q * σ.1 = σ.1 * q)
    [Finite ((baseField G).toSubgroup ⧸
      extensionSubgroup (baseField G)
        (D.frobeniusFixedField K L hLK σ)
        (le_baseField (D.frobeniusFixedField K L hLK σ)))]
    (a : ambientFixedAddSubgroup A
      (D.frobeniusFixedField K L hLK σ)) :
    v.valuationAt (D.frobeniusFixedAbstractField K L hLK σ)
        (D.frobeniusFixedFieldAction A K L hLK σ q hq a) =
      v.valuationAt (D.frobeniusFixedAbstractField K L hLK σ) a := by
  let TF := D.frobeniusFixedAbstractField K L hLK σ
  let k : K.field.toSubgroup := Quotient.out q
  let hstable : conjugateClosedSubgroup TF.field k.1⁻¹ = TF.field :=
    D.conjugate_frobeniusFixedField_eq_of_commutes K L hLK σ q hq
  let CF := TF.conjugate k.1⁻¹
  let C := CF.field
  have hconj := v.normalizedValuation_conjugate TF k.1⁻¹ a
  let bC : ambientFixedAddSubgroup A C :=
    conjugateFixedElement A TF.field k.1⁻¹ a
  have hCFTF : CF = TF := by
    exact FiniteAbstractField.eq_of_field_eq CF TF hstable
  let bT : ambientFixedAddSubgroup A TF.field := hCFTF ▸ bC
  have hbTcoe : bT.1 = bC.1 := by
    exact ambientFixedAddSubgroup_transport_coe CF TF hCFTF bC
  have hvaluationTransport : v.valuationAt TF bT = v.valuationAt CF bC := by
    exact v.valuationAt_transport CF TF hCFTF bC
  have hbT : bT = D.frobeniusFixedFieldAction
      A K L hLK σ q hq a := by
    apply Subtype.ext
    change bT.1 =
      (D.frobeniusFixedFieldAction A K L hLK σ q hq a).1
    calc
      bT.1 = bC.1 := hbTcoe
      _ = A.ρ k.1 a.1 :=
        (conjugateFixedElement_coe A TF.field k.1⁻¹ a).trans
          (congrArg (fun s : G => A.ρ s a.1) (inv_inv k.1))
      _ = (D.frobeniusFixedFieldAction A K L hLK σ q hq a).1 := by rfl
  calc
    v.valuationAt TF (D.frobeniusFixedFieldAction A K L hLK σ q hq a) =
        v.valuationAt TF bT := congrArg (v.valuationAt TF) hbT.symm
    _ = v.valuationAt CF bC := hvaluationTransport
    _ = v.valuationAt TF a := by simpa [CF, C, bC] using hconj

/-- The stabilizing action restricted to the unit group of a Frobenius
fixed field. -/
noncomputable def frobeniusFixedFieldUnitAction
    (v : ValuationData D A)
    [IsTopologicalGroup G] [CompactSpace G] [T2Space G]
    [TotallyDisconnectedSpace G]
    (K : DegreeData.FiniteResidueAbstractField D) (L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.field.toSubgroup)
    [hLnormal : (extensionSubgroup K.field L hLK).Normal]
    (σ : D.FrobeniusElements K L hLK)
    (q : K.field.toSubgroup ⧸ D.extensionInertiaWithin K.field L hLK)
    (hq : q * σ.1 = σ.1 * q)
    [Finite ((baseField G).toSubgroup ⧸
      extensionSubgroup (baseField G)
        (D.frobeniusFixedField K L hLK σ)
        (le_baseField (D.frobeniusFixedField K L hLK σ)))] :
    v.unitAddSubgroup (D.frobeniusFixedAbstractField K L hLK σ) →+
      v.unitAddSubgroup (D.frobeniusFixedAbstractField K L hLK σ) where
  toFun u := ⟨D.frobeniusFixedFieldAction A K L hLK σ q hq u.1, by
    exact (v.mem_unitAddSubgroup_iff
      (D.frobeniusFixedAbstractField K L hLK σ)
      (D.frobeniusFixedFieldAction A K L hLK σ q hq u.1)).2
        ((v.valuationAt_frobeniusFixedFieldAction K L hLK σ q hq u.1).trans u.2)⟩
  map_zero' := by apply Subtype.ext; exact map_zero _
  map_add' _ _ := by apply Subtype.ext; exact map_add _ _ _

/-- The norm of a unit through an arbitrary finite extension is a unit.
This is the valuation-theoretic step used when a finite Galois refinement
is pushed back down to the originally prescribed intermediate field. -/
theorem relativeNorm_mem_unitAddSubgroup
    (v : ValuationData D A) (E : FiniteAbstractFieldExtension G)
    (u : v.unitAddSubgroup E.field) :
    relativeNorm A E.base.field E.field.field E.below u.1 ∈
      v.unitAddSubgroup E.base := by
  rw [v.mem_unitAddSubgroup_iff]
  apply Subtype.ext
  have h := v.normalizedValuation_tower E u.1
  let ER := E.toFiniteResidueAbstractExtension D
  change (ER.residueDegree : ℕ) •
      ((v.valuationAt E.field u.1 : v.valueGroup) : ZHat) =
    ((v.valuationAt E.base
      (relativeNorm A E.base.field E.field.field E.below u.1) :
        v.valueGroup) : ZHat) at h
  have hu : v.valuationAt E.field u.1 = 0 := u.2
  simpa [hu] using h.symm

/-- Relative norm restricted to the finite unit groups. -/
def finiteUnitNorm
    (v : ValuationData D A) (E : FiniteAbstractFieldExtension G) :
    v.unitAddSubgroup E.field →+ v.unitAddSubgroup E.base where
  toFun u := ⟨relativeNorm A E.base.field E.field.field E.below u.1,
    v.relativeNorm_mem_unitAddSubgroup E u⟩
  map_zero' := by apply Subtype.ext; exact map_zero _
  map_add' _ _ := by apply Subtype.ext; exact map_add _ _ _

end ValuationData
end

end ClassFormation
end

section
-- module Solutions.OAIQ244_DUKE.AbstractClassFieldTheory_Reciprocity_Construction_FixedTowerUnitCorrection
attribute [-instance] _root_.ClassFormation.FiniteGaloisSubextension.extensionSubgroup_over_intermediate_normalInstance _root_.ClassFormation.FiniteGaloisSubextension.intermediateField_normalInstance _root_.ClassFormation.instIsAddTorsionFreeZHat _root_.ClassFormation.instIsMulTorsionFreeMultiplicativeZHat _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.maximalIdealPowSuccQuotModule _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace
attribute [-simp] _root_.ClassFormation.DegreeData.chosenUnramifiedFrobeniusLift_exponent _root_.ClassFormation.DegreeData.finiteReciprocityCandidate_apply _root_.ClassFormation.DegreeData.finiteReciprocityCandidate_zero _root_.ClassFormation.DegreeData.frobeniusActionConjugate_coe _root_.ClassFormation.DegreeData.frobeniusExponent_actionConjugate _root_.ClassFormation.DegreeData.frobeniusExponent_chosenDegreeOneFrobeniusElement _root_.ClassFormation.DegreeData.frobeniusExponent_mul _root_.ClassFormation.DegreeData.frobeniusLiftDifference_coe _root_.ClassFormation.DegreeData.frobeniusQuotientRepresentation_apply _root_.ClassFormation.DegreeData.frobeniusRestriction_chosenFiniteReciprocityFrobeniusLift _root_.ClassFormation.DegreeData.frobeniusRestriction_mul _root_.ClassFormation.FiniteAbelianSubextension.extensionQuotientMk_apply _root_.ClassFormation.FiniteGaloisSubextension.classFieldCandidate_field _root_.ClassFormation.ValuationData.canonicalUnramifiedNormQuotientValuation_finiteNormClass _root_.ClassFormation.ValuationData.canonicalValueQuotientHom_mk _root_.ClassFormation.ValuationData.canonicalValueReduction_one _root_.ClassFormation.ValuationData.mem_infiniteUnitAddSubgroup_iff _root_.ClassFormation.ValuationData.mem_infiniteUnitNormSubgroup_iff _root_.ClassFormation.ValuationData.unramifiedNormQuotientValuation_finiteNormClass _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.ClassFormation.cyclicNormClassHom_apply _root_.ClassFormation.extensionFixedRepresentationEquiv_apply_coe _root_.ClassFormation.extensionFixedRepresentationEquiv_symm_apply_coe _root_.ClassFormation.mem_normFilterBasis_iff _root_.ClassFormation.toZModPow_zHatToPadicInt _root_.ClassFormation.zHatReductionRingHom_apply _root_.ClassFormation.zHatRingEquivProfiniteIntegerPrimeProduct_apply _root_.ClassFormation.zHatToPadicInt_intCast _root_.ClassFormation.zHatToProfiniteIntegerPrimeProduct_apply _root_.ClassFormation.zHatToProfiniteIntegerPrimeProduct_intCast _root_.ClassFormation.zHatUnitsContinuousMulEquivPrimeProduct_coe_apply _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.LocalFieldTheory.residueField_algebraMap_residue _root_.OAI.PrimeDegreePackets.ThetaConstruction.schwartzCM_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

universe u v

namespace ClassFormation

open KummerTheory
open CyclicCohomology

/-!
# Fixed-tower unit correction

This module constructs the unit-valued correction term on a Frobenius
fixed-field tower and proves its coefficient and relative-norm identities.
-/

noncomputable section

open CategoryTheory
open scoped BigOperators

variable {G : IntegralRepGroupType} [Group G] [TopologicalSpace G]

namespace ValuationData

variable {D : DegreeData G} {A : Rep ℤ G}

/-- The unit-valued correction term on the upper Frobenius fixed field.
This is the additive form of the right-hand side of the corrected equation. -/
noncomputable def fixedTowerCorrection
    (v : ValuationData D A)
    [IsTopologicalGroup G] [CompactSpace G] [T2Space G]
    [TotallyDisconnectedSpace G]
    (K : DegreeData.FiniteResidueAbstractField D) (L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.field.toSubgroup)
    [hLnormal : (extensionSubgroup K.field L hLK).Normal]
    (σn : D.FrobeniusElements K L hLK)
    [Finite ((baseField G).toSubgroup ⧸
      extensionSubgroup (baseField G)
        (D.frobeniusFixedField K L hLK σn)
        (le_baseField (D.frobeniusFixedField K L hLK σn)))]
    {ι : Type v} (s : Finset ι)
    (φ : K.field.toSubgroup ⧸ D.extensionInertiaWithin K.field L hLK)
    (hφσn : φ * σn.1 = σn.1 * φ)
    (τ : ι → K.field.toSubgroup ⧸ D.extensionInertiaWithin K.field L hLK)
    (hτσn : ∀ i, τ i * σn.1 = σn.1 * τ i)
    (uBar :
      v.unitAddSubgroup (D.frobeniusFixedAbstractField K L hLK σn))
    (uBarᵢ : ι →
      v.unitAddSubgroup (D.frobeniusFixedAbstractField K L hLK σn)) :
    v.unitAddSubgroup (D.frobeniusFixedAbstractField K L hLK σn) :=
  v.frobeniusFixedFieldUnitAction K L hLK σn φ hφσn uBar -
    uBar -
    ∑ i ∈ s,
      (v.frobeniusFixedFieldUnitAction K L hLK σn
          (τ i) (hτσn i) (uBarᵢ i) - uBarᵢ i)

/--
The underlying fixed-tower correction is the Frobenius difference minus the prescribed finite sum
of correction terms.
-/
theorem fixedTowerCorrection_coe
    (v : ValuationData D A)
    [IsTopologicalGroup G] [CompactSpace G] [T2Space G]
    [TotallyDisconnectedSpace G]
    (K : DegreeData.FiniteResidueAbstractField D) (L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.field.toSubgroup)
    [hLnormal : (extensionSubgroup K.field L hLK).Normal]
    (σn : D.FrobeniusElements K L hLK)
    [Finite ((baseField G).toSubgroup ⧸
      extensionSubgroup (baseField G)
        (D.frobeniusFixedField K L hLK σn)
        (le_baseField (D.frobeniusFixedField K L hLK σn)))]
    {ι : Type v} (s : Finset ι)
    (φ : K.field.toSubgroup ⧸ D.extensionInertiaWithin K.field L hLK)
    (hφσn : φ * σn.1 = σn.1 * φ)
    (τ : ι → K.field.toSubgroup ⧸ D.extensionInertiaWithin K.field L hLK)
    (hτσn : ∀ i, τ i * σn.1 = σn.1 * τ i)
    (uBar :
      v.unitAddSubgroup (D.frobeniusFixedAbstractField K L hLK σn))
    (uBarᵢ : ι →
      v.unitAddSubgroup (D.frobeniusFixedAbstractField K L hLK σn)) :
    (v.fixedTowerCorrection K L hLK σn s φ hφσn
      τ hτσn uBar uBarᵢ).1 =
        (v.frobeniusFixedFieldUnitAction K L hLK σn
            φ hφσn uBar).1 -
          uBar.1 -
          ∑ i ∈ s,
            ((v.frobeniusFixedFieldUnitAction K L hLK σn
                (τ i) (hτσn i) (uBarᵢ i)).1 - (uBarᵢ i).1) := by
  let inclusion :=
    (v.unitAddSubgroup (D.frobeniusFixedAbstractField K L hLK σn)).subtype
  change inclusion (v.fixedTowerCorrection K L hLK σn s φ hφσn
    τ hτσn uBar uBarᵢ) =
      inclusion (v.frobeniusFixedFieldUnitAction K L hLK σn φ hφσn uBar) -
        inclusion uBar - ∑ i ∈ s,
          (inclusion (v.frobeniusFixedFieldUnitAction K L hLK σn
            (τ i) (hτσn i) (uBarᵢ i)) - inclusion (uBarᵢ i))
  simp only [fixedTowerCorrection, map_sub, map_sum]

/-- Applying the lower norm to the correction term gives zero.  This is
the norm calculation immediately before the use of H⁻¹ = 0. -/
theorem fixedTowerCorrection_relativeNorm_eq_zero
    (v : ValuationData D A)
    [IsTopologicalGroup G] [CompactSpace G] [T2Space G]
    [TotallyDisconnectedSpace G]
    (K : DegreeData.FiniteResidueAbstractField D) (L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.field.toSubgroup)
    [hLnormal : (extensionSubgroup K.field L hLK).Normal]
    (σ σn : D.FrobeniusElements K L hLK)
    (hTS : (D.frobeniusFixedField K L hLK σn).toSubgroup ≤
      (D.frobeniusFixedField K L hLK σ).toSubgroup)
    [Finite ((D.frobeniusFixedField K L hLK σ).toSubgroup ⧸
      extensionSubgroup (D.frobeniusFixedField K L hLK σ)
        (D.frobeniusFixedField K L hLK σn) hTS)]
    [Finite ((baseField G).toSubgroup ⧸
      extensionSubgroup (baseField G)
        (D.frobeniusFixedField K L hLK σ)
        (le_baseField (D.frobeniusFixedField K L hLK σ)))]
    [Finite ((baseField G).toSubgroup ⧸
      extensionSubgroup (baseField G)
        (D.frobeniusFixedField K L hLK σn)
        (le_baseField (D.frobeniusFixedField K L hLK σn)))]
    {ι : Type v} (s : Finset ι)
    (φ : K.field.toSubgroup ⧸ D.extensionInertiaWithin K.field L hLK)
    (hφσ : φ * σ.1 = σ.1 * φ)
    (hφσn : φ * σn.1 = σn.1 * φ)
    (τ : ι → K.field.toSubgroup ⧸ D.extensionInertiaWithin K.field L hLK)
    (hτσ : ∀ i, τ i * σ.1 = σ.1 * τ i)
    (hτσn : ∀ i, τ i * σn.1 = σn.1 * τ i)
    (u :
      v.unitAddSubgroup (D.frobeniusFixedAbstractField K L hLK σ))
    (uᵢ : ι →
      v.unitAddSubgroup (D.frobeniusFixedAbstractField K L hLK σ))
    (uBar :
      v.unitAddSubgroup (D.frobeniusFixedAbstractField K L hLK σn))
    (uBarᵢ : ι →
      v.unitAddSubgroup (D.frobeniusFixedAbstractField K L hLK σn))
    (huBar : relativeNorm A (D.frobeniusFixedField K L hLK σ)
      (D.frobeniusFixedField K L hLK σn) hTS uBar.1 = u.1)
    (huBarᵢ : ∀ i,
      relativeNorm A (D.frobeniusFixedField K L hLK σ)
        (D.frobeniusFixedField K L hLK σn) hTS
          (uBarᵢ i).1 = (uᵢ i).1)
    (hstar :
      A.ρ (Quotient.out φ).1 u.1.1 - u.1.1 =
        ∑ i ∈ s,
          (A.ρ (Quotient.out (τ i)).1 (uᵢ i).1.1 - (uᵢ i).1.1)) :
    relativeNorm A (D.frobeniusFixedField K L hLK σ)
      (D.frobeniusFixedField K L hLK σn) hTS
        (v.fixedTowerCorrection K L hLK σn s φ hφσn
          τ hτσn uBar uBarᵢ).1 = 0 := by
  dsimp only [DegreeData.frobeniusFixedAbstractField] at *
  let u' : ambientFixedAddSubgroup A
      (D.frobeniusFixedField K L hLK σ) :=
    ⟨u.1.1, u.1.2⟩
  let uᵢ' (i : ι) : ambientFixedAddSubgroup A
      (D.frobeniusFixedField K L hLK σ) :=
    ⟨(uᵢ i).1.1, (uᵢ i).1.2⟩
  let uBar' : ambientFixedAddSubgroup A
      (D.frobeniusFixedField K L hLK σn) :=
    ⟨uBar.1.1, uBar.1.2⟩
  let uBarᵢ' (i : ι) : ambientFixedAddSubgroup A
      (D.frobeniusFixedField K L hLK σn) :=
    ⟨(uBarᵢ i).1.1, (uBarᵢ i).1.2⟩
  have hsumBar (f : ι →
      v.unitAddSubgroup (D.frobeniusFixedAbstractField K L hLK σn)) :
      ((∑ i ∈ s, f i).1.1 : A.V) = ∑ i ∈ s, (f i).1.1 := by
    calc
      ((∑ i ∈ s, f i).1.1 : A.V) =
          (ambientFixedAddSubgroup A
            (D.frobeniusFixedField K L hLK σn)).subtype
              (∑ i ∈ s, (v.unitAddSubgroup
                (D.frobeniusFixedAbstractField K L hLK σn)).subtype (f i)) := by
        exact congrArg (ambientFixedAddSubgroup A
          (D.frobeniusFixedField K L hLK σn)).subtype
          (map_sum (v.unitAddSubgroup
            (D.frobeniusFixedAbstractField K L hLK σn)).subtype f s)
      _ = _ := map_sum
        (ambientFixedAddSubgroup A
          (D.frobeniusFixedField K L hLK σn)).subtype
        (fun i => (v.unitAddSubgroup
          (D.frobeniusFixedAbstractField K L hLK σn)).subtype (f i)) s
  have hsumBar' (f : ι → ambientFixedAddSubgroup A
      (D.frobeniusFixedField K L hLK σn)) :
      ((∑ i ∈ s, f i).1 : A.V) = ∑ i ∈ s, (f i).1 :=
    map_sum (ambientFixedAddSubgroup A
      (D.frobeniusFixedField K L hLK σn)).subtype f s
  have hφVal :
      ((D.frobeniusFixedFieldAction A K L hLK σn φ hφσn uBar').1 : A.V) =
        A.ρ (Quotient.out φ).1 uBar.1.1 := by
    simp [uBar']
  have hτVal (i : ι) :
      ((D.frobeniusFixedFieldAction A K L hLK σn
        (τ i) (hτσn i) (uBarᵢ' i)).1 : A.V) =
        A.ρ (Quotient.out (τ i)).1 (uBarᵢ i).1.1 := by
    simp [uBarᵢ']
  have hunitφVal :
      ((v.frobeniusFixedFieldUnitAction K L hLK σn
        φ hφσn uBar).1.1 : A.V) =
        A.ρ (Quotient.out φ).1 uBar.1.1 := by
    change ((D.frobeniusFixedFieldAction A K L hLK σn
      φ hφσn uBar.1).1 : A.V) = _
    exact hφVal
  have hunitτVal (i : ι) :
      ((v.frobeniusFixedFieldUnitAction K L hLK σn
        (τ i) (hτσn i) (uBarᵢ i)).1.1 : A.V) =
        A.ρ (Quotient.out (τ i)).1 (uBarᵢ i).1.1 := by
    change ((D.frobeniusFixedFieldAction A K L hLK σn
      (τ i) (hτσn i) (uBarᵢ i).1).1 : A.V) = _
    exact hτVal i
  have hsubAmbient (x y : ambientFixedAddSubgroup A
      (D.frobeniusFixedField K L hLK σn)) :
      ((x - y).1 : A.V) = x.1 - y.1 :=
    map_sub (ambientFixedAddSubgroup A
      (D.frobeniusFixedField K L hLK σn)).subtype x y
  have hsumAmbient (f : ι → ambientFixedAddSubgroup A
      (D.frobeniusFixedField K L hLK σn)) :
      ((∑ i ∈ s, f i).1 : A.V) = ∑ i ∈ s, (f i).1 :=
    map_sum (ambientFixedAddSubgroup A
      (D.frobeniusFixedField K L hLK σn)).subtype f s
  have hcorrection :
      (v.fixedTowerCorrection K L hLK σn s φ hφσn
          τ hτσn uBar uBarᵢ).1 =
        D.frobeniusFixedFieldAction A K L hLK σn
            φ hφσn uBar' -
          uBar' -
          ∑ i ∈ s,
            (D.frobeniusFixedFieldAction A K L hLK σn
                (τ i) (hτσn i) (uBarᵢ' i) - uBarᵢ' i) := by
    rw [v.fixedTowerCorrection_coe
      K L hLK σn s φ hφσn τ hτσn uBar uBarᵢ]
    rfl
  rw [hcorrection]
  simp only [map_sub, map_sum]
  have hφEquiv :
      relativeNorm A (D.frobeniusFixedField K L hLK σ)
          (D.frobeniusFixedField K L hLK σn) hTS
          (D.frobeniusFixedFieldAction A K L hLK σn
            φ hφσn uBar') =
        D.frobeniusFixedFieldAction A K L hLK σ
          φ hφσ
            (relativeNorm A (D.frobeniusFixedField K L hLK σ)
              (D.frobeniusFixedField K L hLK σn) hTS uBar') := by
    exact D.relativeNorm_frobeniusFixedFieldAction
      A K L hLK σ σn hTS φ hφσ hφσn uBar'
  rw [hφEquiv]
  have hτEquiv (i : ι) :
      relativeNorm A (D.frobeniusFixedField K L hLK σ)
          (D.frobeniusFixedField K L hLK σn) hTS
          (D.frobeniusFixedFieldAction A K L hLK σn
            (τ i) (hτσn i) (uBarᵢ' i)) =
        D.frobeniusFixedFieldAction A K L hLK σ
          (τ i) (hτσ i)
            (relativeNorm A (D.frobeniusFixedField K L hLK σ)
              (D.frobeniusFixedField K L hLK σn) hTS (uBarᵢ' i)) := by
    exact D.relativeNorm_frobeniusFixedFieldAction
      A K L hLK σ σn hTS (τ i) (hτσ i) (hτσn i) (uBarᵢ' i)
  simp_rw [hτEquiv]
  have huBar' :
      relativeNorm A (D.frobeniusFixedField K L hLK σ)
        (D.frobeniusFixedField K L hLK σn) hTS uBar' = u' := by
    exact huBar
  have huBarᵢ' (i : ι) :
      relativeNorm A (D.frobeniusFixedField K L hLK σ)
        (D.frobeniusFixedField K L hLK σn) hTS (uBarᵢ' i) = uᵢ' i := by
    exact huBarᵢ i
  rw [huBar']
  simp_rw [huBarᵢ']
  apply Subtype.ext
  have hsum : ((∑ i ∈ s, uᵢ i).1.1 : A.V) =
      ∑ i ∈ s, (uᵢ i).1.1 := by
    calc
      ((∑ i ∈ s, uᵢ i).1.1 : A.V) =
          (ambientFixedAddSubgroup A
            (D.frobeniusFixedField K L hLK σ)).subtype
              (∑ i ∈ s, (v.unitAddSubgroup
                (D.frobeniusFixedAbstractField K L hLK σ)).subtype (uᵢ i)) := by
        exact congrArg (ambientFixedAddSubgroup A
          (D.frobeniusFixedField K L hLK σ)).subtype
          (map_sum (v.unitAddSubgroup
            (D.frobeniusFixedAbstractField K L hLK σ)).subtype uᵢ s)
      _ = _ := map_sum
        (ambientFixedAddSubgroup A
          (D.frobeniusFixedField K L hLK σ)).subtype
        (fun i => (v.unitAddSubgroup
          (D.frobeniusFixedAbstractField K L hLK σ)).subtype (uᵢ i)) s
  have hsum' (f : ι → ambientFixedAddSubgroup A
      (D.frobeniusFixedField K L hLK σ)) :
      ((∑ i ∈ s, f i).1 : A.V) = ∑ i ∈ s, (f i).1 :=
    map_sum (ambientFixedAddSubgroup A
      (D.frobeniusFixedField K L hLK σ)).subtype f s
  simpa [u', uᵢ', D.frobeniusFixedFieldAction_coe,
    hsum, hsum', Finset.sum_sub_distrib] using
    sub_eq_zero.mpr hstar

end ValuationData
end

end ClassFormation
end

section
-- module Solutions.OAIQ244_DUKE.AbstractClassFieldTheory_Reciprocity_Construction_FrobeniusQuotientDescent
attribute [-instance] _root_.ClassFormation.DegreeData.FiniteAmbientFrobeniusFixedFieldTower.ambientQuotientFinite _root_.ClassFormation.DegreeData.FiniteAmbientFrobeniusFixedFieldTower.ambientRepresentedQuotientFinite _root_.ClassFormation.DegreeData.FrobeniusFixedFieldTower.baseAbsoluteFiniteInstance _root_.ClassFormation.DegreeData.FrobeniusFixedFieldTower.extensionFinite _root_.ClassFormation.DegreeData.FrobeniusFixedFieldTower.extensionNormal _root_.ClassFormation.DegreeData.FrobeniusFixedFieldTower.fieldAbsoluteFiniteInstance _root_.ClassFormation.DegreeData.FrobeniusPowerFixedFieldTower.baseRepresentedAbsoluteFinite _root_.ClassFormation.DegreeData.FrobeniusPowerFixedFieldTower.fieldRepresentedAbsoluteFinite _root_.ClassFormation.DegreeData.FrobeniusPowerFixedFieldTower.relativeRepresentedQuotientFinite _root_.ClassFormation.FiniteAbstractField.toFiniteResidueAbstractField_extensionFinite _root_.ClassFormation.FiniteAbstractField.toFiniteResidueAbstractField_extensionNormal _root_.ClassFormation.FiniteGaloisSubextension.extensionSubgroup_normalInstance _root_.ClassFormation.FiniteGaloisSubextension.extensionSubgroup_over_intermediate_normalInstance _root_.ClassFormation.FiniteGaloisSubextension.intermediateField_normalInstance _root_.ClassFormation.finiteNormQuotientAddCommGroup _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.maximalIdealPowSuccQuotModule _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace
attribute [-simp] _root_.ClassFormation.DegreeData.chosenUnramifiedFrobeniusLift_exponent _root_.ClassFormation.DegreeData.finiteReciprocityCandidate_apply _root_.ClassFormation.DegreeData.finiteReciprocityCandidate_zero _root_.ClassFormation.DegreeData.frobeniusActionConjugate_coe _root_.ClassFormation.DegreeData.frobeniusExponent_actionConjugate _root_.ClassFormation.DegreeData.frobeniusExponent_chosenDegreeOneFrobeniusElement _root_.ClassFormation.DegreeData.frobeniusExponent_mul _root_.ClassFormation.DegreeData.frobeniusExponent_powerOfDegreeOne _root_.ClassFormation.DegreeData.frobeniusFixedFieldAction_coe _root_.ClassFormation.DegreeData.frobeniusLiftDifference_coe _root_.ClassFormation.DegreeData.frobeniusPowerOfDegreeOne_coe _root_.ClassFormation.DegreeData.frobeniusRestriction_chosenFiniteReciprocityFrobeniusLift _root_.ClassFormation.DegreeData.frobeniusRestriction_mul _root_.ClassFormation.DegreeData.maximalUnramifiedToFiniteNormQuotient_maximalUnramifiedNormClass _root_.ClassFormation.FiniteAbelianSubextension.extensionQuotientMk_apply _root_.ClassFormation.FiniteGaloisSubextension.classFieldCandidate_field _root_.ClassFormation.FiniteGaloisSubextension.extensionQuotientMk_apply _root_.ClassFormation.FiniteGaloisSubextension.extensionQuotientMk_eq_one_iff _root_.ClassFormation.FiniteGaloisSubextension.toGaloisSubextension_isTotallyRamified_iff _root_.ClassFormation.FiniteGaloisSubextension.toGaloisSubextension_isUnramified_iff _root_.ClassFormation.ValuationData.canonicalUnramifiedNormQuotientValuation_finiteNormClass _root_.ClassFormation.ValuationData.canonicalValueQuotientHom_mk _root_.ClassFormation.ValuationData.canonicalValueReduction_one _root_.ClassFormation.ValuationData.mem_infiniteUnitAddSubgroup_iff _root_.ClassFormation.ValuationData.mem_infiniteUnitNormSubgroup_iff _root_.ClassFormation.ValuationData.unramifiedNormQuotientValuation_finiteNormClass _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.ClassFormation.cyclicNormClassHom_apply _root_.ClassFormation.extensionFixedRepresentationEquiv_apply_coe _root_.ClassFormation.extensionFixedRepresentationEquiv_symm_apply_coe _root_.ClassFormation.finiteNormClass_add _root_.ClassFormation.finiteNormClass_eq_zero_iff _root_.ClassFormation.finiteNormClass_nsmul _root_.ClassFormation.finiteNormClass_sub _root_.ClassFormation.finiteNormClass_zero _root_.ClassFormation.finiteNormQuotientConcreteEquiv_finiteNormClass _root_.ClassFormation.finiteNormQuotientLift_finiteNormClass _root_.ClassFormation.mem_normFilterBasis_iff _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.LocalFieldTheory.residueField_algebraMap_residue _root_.OAI.PrimeDegreePackets.ThetaConstruction.schwartzCM_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

universe u v

namespace ClassFormation

open KummerTheory
open CyclicCohomology

/-!
# Frobenius quotient descent

This module constructs the Frobenius quotient representation, identifies its
Birkhoff sums with Frobenius power sums, and proves the finite-support
descent from the maximal unramified field.
-/

noncomputable section

open CategoryTheory
open scoped BigOperators

section representationDescent

/-!
Mathlib's `Rep ℤ G` requires its coefficient ring and acting group in the
same universe; `IntegralRepGroupType` names that shared boundary.
-/
variable {G : IntegralRepGroupType} [Group G] [TopologicalSpace G]

namespace DegreeData

/-- Underlying coefficient of the actual quotient action, expressed through
the chosen quotient representative. -/
theorem frobeniusQuotientAction_coe_out (D : DegreeData G) (A : Rep ℤ G)
    (K L : ClosedSubgroup G) (hLK : L.toSubgroup ≤ K.toSubgroup)
    [hLnormal : (extensionSubgroup K L hLK).Normal]
    (q : K.toSubgroup ⧸ D.extensionInertiaWithin K L hLK)
    (a : ambientFixedAddSubgroup A (D.maximalUnramifiedField L)) :
    (D.frobeniusQuotientAction A K L hLK q a).1 =
      A.ρ (Quotient.out q).1 a.1 := by
  let k : K.toSubgroup := Quotient.out q
  have hkq : (QuotientGroup.mk k :
      K.toSubgroup ⧸ D.extensionInertiaWithin K L hLK) = q :=
    Quotient.out_eq' q
  calc
    (D.frobeniusQuotientAction A K L hLK q a).1 =
        (D.frobeniusQuotientAction A K L hLK (QuotientGroup.mk k) a).1 :=
      congrArg (fun z => (D.frobeniusQuotientAction A K L hLK z a).1) hkq.symm
    _ = A.ρ k.1 a.1 := rfl
    _ = A.ρ (Quotient.out q).1 a.1 := rfl

/-- An orbit sum of an element fixed by its first translate is scalar
multiplication by the orbit length. -/
theorem frobeniusPowerSum_eq_nsmul_of_fixed (D : DegreeData G) (A : Rep ℤ G)
    (K L : ClosedSubgroup G) (hLK : L.toSubgroup ≤ K.toSubgroup)
    [hLnormal : (extensionSubgroup K L hLK).Normal]
    (q : K.toSubgroup ⧸ D.extensionInertiaWithin K L hLK)
    (n : ℕ)
    (a : ambientFixedAddSubgroup A (D.maximalUnramifiedField L))
    (ha : D.frobeniusQuotientAction A K L hLK q a = a) :
    D.frobeniusPowerSum A K L hLK q n a = n • a := by
  let B := D.frobeniusQuotientRepresentation A K L hLK
  have hpow (i : ℕ) :
      D.frobeniusQuotientAction A K L hLK (q ^ i) a = a := by
    have haB : B.ρ q a = a := by
      change D.frobeniusQuotientAction A K L hLK q a = a
      exact ha
    have hi := rep_action_pow_fixed B q a haB i
    change D.frobeniusQuotientAction A K L hLK (q ^ i) a = a at hi
    exact hi
  unfold DegreeData.frobeniusPowerSum
  simp_rw [hpow]
  simp

end DegreeData

end representationDescent

end

end ClassFormation
end

section
-- module Solutions.OAIQ244_DUKE.AbstractClassFieldTheory_Reciprocity_Construction_FixedTowerUnitDescent
attribute [-instance] _root_.ClassFormation.FiniteGaloisSubextension.extensionSubgroup_over_intermediate_normalInstance _root_.ClassFormation.FiniteGaloisSubextension.intermediateField_normalInstance _root_.ClassFormation.FiniteGaloisSubextension.intermediateSubgroup_normalInstance _root_.ClassFormation.FiniteGaloisSubextension.upperQuotient_groupInstance _root_.ClassFormation.instIsAddTorsionFreeZHat _root_.ClassFormation.instIsMulTorsionFreeMultiplicativeZHat _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.maximalIdealPowSuccQuotModule _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace
attribute [-simp] _root_.ClassFormation.DegreeData.chosenUnramifiedFrobeniusLift_exponent _root_.ClassFormation.DegreeData.finiteReciprocityCandidate_apply _root_.ClassFormation.DegreeData.finiteReciprocityCandidate_zero _root_.ClassFormation.DegreeData.frobeniusActionConjugate_coe _root_.ClassFormation.DegreeData.frobeniusExponent_actionConjugate _root_.ClassFormation.DegreeData.frobeniusExponent_chosenDegreeOneFrobeniusElement _root_.ClassFormation.DegreeData.frobeniusExponent_mul _root_.ClassFormation.DegreeData.frobeniusLiftDifference_coe _root_.ClassFormation.DegreeData.frobeniusRestriction_chosenFiniteReciprocityFrobeniusLift _root_.ClassFormation.DegreeData.frobeniusRestriction_mul _root_.ClassFormation.FiniteAbelianSubextension.extensionQuotientMk_apply _root_.ClassFormation.FiniteGaloisSubextension.classFieldCandidate_field _root_.ClassFormation.FiniteGaloisSubextension.intermediateFiniteAbelianOfCommutatorLe_field _root_.ClassFormation.FiniteGaloisSubextension.lowerQuotientEquiv_mk _root_.ClassFormation.FiniteGaloisSubextension.lowerQuotientEquiv_mk_coe _root_.ClassFormation.FiniteGaloisSubextension.lowerRestrictionHom_apply_coe _root_.ClassFormation.FiniteGaloisSubextension.mem_intermediateSubgroup_iff _root_.ClassFormation.FiniteGaloisSubextension.upperQuotientEquiv_mk_mk _root_.ClassFormation.FiniteGaloisSubextension.upperQuotientMk_apply _root_.ClassFormation.ValuationData.canonicalUnramifiedNormQuotientValuation_finiteNormClass _root_.ClassFormation.ValuationData.canonicalValueQuotientHom_mk _root_.ClassFormation.ValuationData.canonicalValueReduction_one _root_.ClassFormation.ValuationData.mem_infiniteUnitAddSubgroup_iff _root_.ClassFormation.ValuationData.mem_infiniteUnitNormSubgroup_iff _root_.ClassFormation.ValuationData.unramifiedNormQuotientValuation_finiteNormClass _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.ClassFormation.cyclicNormClassHom_apply _root_.ClassFormation.extensionFixedRepresentationEquiv_apply_coe _root_.ClassFormation.extensionFixedRepresentationEquiv_symm_apply_coe _root_.ClassFormation.mem_normFilterBasis_iff _root_.ClassFormation.toZModPow_zHatToPadicInt _root_.ClassFormation.zHatReductionRingHom_apply _root_.ClassFormation.zHatRingEquivProfiniteIntegerPrimeProduct_apply _root_.ClassFormation.zHatToPadicInt_intCast _root_.ClassFormation.zHatToProfiniteIntegerPrimeProduct_apply _root_.ClassFormation.zHatToProfiniteIntegerPrimeProduct_intCast _root_.ClassFormation.zHatUnitsContinuousMulEquivPrimeProduct_coe_apply _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.LocalFieldTheory.residueField_algebraMap_residue _root_.OAI.PrimeDegreePackets.ThetaConstruction.schwartzCM_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

universe u v

namespace ClassFormation

open KummerTheory
open CyclicCohomology

/-!
# Unit descent on Frobenius fixed-field towers

This module packages the fixed-tower action and power correction, applies
the unit-cohomology axiom, and proves the corrected universal norm-descent
equation on finite fixed-field towers.
-/

noncomputable section

open CategoryTheory
open scoped BigOperators

variable {G : IntegralRepGroupType} [Group G] [TopologicalSpace G]

namespace ValuationData

variable {D : DegreeData G} {A : Rep ℤ G}

/-- The stabilizing action on the upper unit group, expressed directly on a
fixed-field tower.  This is the bundle-native boundary used by the descent
construction. -/
noncomputable def fixedTowerUnitAction
    (v : ValuationData D A)
    [IsTopologicalGroup G] [CompactSpace G] [T2Space G]
    [TotallyDisconnectedSpace G]
    (T : DegreeData.FrobeniusFixedFieldTower D)
    (q : T.ambientBase.field.toSubgroup ⧸
      D.extensionInertiaWithin T.ambientBase.field T.ambient.field
        T.ambient.below)
    (hq : q * T.fieldFrobenius.1 = T.fieldFrobenius.1 * q) :
    v.unitAddSubgroup
        (DegreeData.FrobeniusFixedFieldTower.field (G := G) (D := D) T) →+
      v.unitAddSubgroup
        (DegreeData.FrobeniusFixedFieldTower.field (G := G) (D := D) T) := by
  let TF :=
    D.frobeniusFixedAbstractField T.ambientBase T.ambient.field
      T.ambient.below T.fieldFrobenius
  have hTF : TF = T.field := by
    apply FiniteAbstractField.eq_of_field_eq
    rfl
  exact hTF ▸
    v.frobeniusFixedFieldUnitAction T.ambientBase T.ambient.field
      T.ambient.below T.fieldFrobenius q hq

/-- The corrected upper unit associated with a power-fixed-field tower.
All fixed fields and finiteness witnesses are obtained from `P`; callers no
longer have to align independently constructed unit-group types. -/
noncomputable def powerTowerCorrection
    (v : ValuationData D A)
    [IsTopologicalGroup G] [CompactSpace G] [T2Space G]
    [TotallyDisconnectedSpace G]
    (P : DegreeData.FrobeniusPowerFixedFieldTower D)
    {ι : Type v} (s : Finset ι)
    (τ : ι →
      (D.extensionNormalizedDegreeContinuous P.ambientBase P.ambient.field
        P.ambient.below).toMonoidHom.ker)
    (hτ : ∀ i, (τ i).1 * P.fieldFrobenius.1 =
      P.fieldFrobenius.1 * (τ i).1)
    (uBar : v.unitAddSubgroup
      (DegreeData.FrobeniusFixedFieldTower.field (G := G) (D := D)
        (DegreeData.FrobeniusPowerFixedFieldTower.toFrobeniusFixedFieldTower
          (G := G) (D := D) P)))
    (uBarᵢ : ι → v.unitAddSubgroup
      (DegreeData.FrobeniusFixedFieldTower.field (G := G) (D := D)
        (DegreeData.FrobeniusPowerFixedFieldTower.toFrobeniusFixedFieldTower
          (G := G) (D := D) P))) :
    v.unitAddSubgroup
      (DegreeData.FrobeniusFixedFieldTower.field (G := G) (D := D)
        (DegreeData.FrobeniusPowerFixedFieldTower.toFrobeniusFixedFieldTower
          (G := G) (D := D) P)) :=
  let T := DegreeData.FrobeniusPowerFixedFieldTower.toFrobeniusFixedFieldTower
    (G := G) (D := D) P
  v.fixedTowerUnitAction T P.frobenius.1 P.frobenius_commute_field uBar -
    uBar -
    ∑ i ∈ s,
      (v.fixedTowerUnitAction T (τ i).1 (hτ i) (uBarᵢ i) - uBarᵢ i)

/-- The cyclic generator selected on the lower fixed field acts on the
upper unit group as the concrete quotient element defining that field. -/
theorem unitRepresentation_generator_action_eq
    (v : ValuationData D A)
    [IsTopologicalGroup G] [CompactSpace G] [T2Space G]
    [TotallyDisconnectedSpace G]
    (T : DegreeData.FrobeniusFixedFieldTower D)
    (g : T.Representative)
    (y : v.unitAddSubgroup
      (DegreeData.FrobeniusFixedFieldTower.field (G := G) (D := D) T)) :
    v.fixedTowerUnitAction T T.baseFrobenius.1 T.commute y =
      ((v.unitRepresentation T.extension T.normal).ρ
          (QuotientGroup.mk g.element) y :
        v.unitAddSubgroup
          (DegreeData.FrobeniusFixedFieldTower.field (G := G) (D := D) T)) := by
  let gK : T.ambientBase.field.toSubgroup :=
    ⟨g.element.1, (D.frobeniusFixedField_le T.ambientBase T.ambient.field
      T.ambient.below T.baseFrobenius) g.element.2⟩
  have hgKσ :
      (QuotientGroup.mk gK :
        T.ambientBase.field.toSubgroup ⧸
          D.extensionInertiaWithin T.ambientBase.field T.ambient.field
            T.ambient.below) = T.baseFrobenius.1 := by
    exact congrArg Subtype.val g.mapsToFrobenius
  apply Subtype.ext
  apply Subtype.ext
  change A.ρ (Quotient.out T.baseFrobenius.1).1 y.1.1 =
    A.ρ g.element.1 y.1.1
  calc
    A.ρ (Quotient.out T.baseFrobenius.1).1 y.1.1 =
        A.ρ gK.1 y.1.1 := by
      calc
        A.ρ (Quotient.out T.baseFrobenius.1).1 y.1.1 =
            (D.frobeniusFixedFieldAction A T.ambientBase T.ambient.field
              T.ambient.below T.fieldFrobenius T.baseFrobenius.1
                T.commute y.1).1 := by
                exact (D.frobeniusFixedFieldAction_coe A T.ambientBase
                  T.ambient.field T.ambient.below T.fieldFrobenius
                  T.baseFrobenius.1 T.commute y.1).symm
        _ = A.ρ gK.1 y.1.1 := by
          exact D.frobeniusFixedFieldAction_coe_of_mk
            A T.ambientBase T.ambient.field T.ambient.below
              T.fieldFrobenius T.baseFrobenius.1 T.commute gK hgKσ y.1
    _ = A.ρ g.element.1 y.1.1 := rfl

/-- The unit-cohomology axiom supplies the barred unit lifts and the corrected upper unit in
the exact power-fixed-field tower used. -/
theorem universalNormDescent_fixedTower_solution
    (v : ValuationData D A)
    [IsTopologicalGroup G] [CompactSpace G] [T2Space G]
    [TotallyDisconnectedSpace G]
    (hAxiom : v.SatisfiesUnramifiedUnitCohomology)
    (P : DegreeData.FrobeniusPowerFixedFieldTower D)
    {ι : Type v} (s : Finset ι)
    (τ : ι →
      (D.extensionNormalizedDegreeContinuous P.ambientBase P.ambient.field
        P.ambient.below).toMonoidHom.ker)
    (hτσ : ∀ i, (τ i).1 * P.baseFrobenius.1 =
      P.baseFrobenius.1 * (τ i).1)
    (hτσn : ∀ i, (τ i).1 * P.fieldFrobenius.1 =
      P.fieldFrobenius.1 * (τ i).1)
    (u : v.unitAddSubgroup P.toFrobeniusFixedFieldTower.base)
    (uᵢ : ι → v.unitAddSubgroup P.toFrobeniusFixedFieldTower.base)
    (hstar :
      A.ρ (Quotient.out P.frobenius.1).1 u.1.1 - u.1.1 =
        ∑ i ∈ s,
          (A.ρ (Quotient.out (τ i).1).1 (uᵢ i).1.1 - (uᵢ i).1.1)) :
    let T : DegreeData.FrobeniusFixedFieldTower D :=
      DegreeData.FrobeniusPowerFixedFieldTower.toFrobeniusFixedFieldTower
        (G := G) (D := D) P
    ∃ (uBar : v.unitAddSubgroup
          (DegreeData.FrobeniusFixedFieldTower.field (G := G) (D := D) T))
        (uBarᵢ : ι → v.unitAddSubgroup
          (DegreeData.FrobeniusFixedFieldTower.field (G := G) (D := D) T))
        (yBar : v.unitAddSubgroup
          (DegreeData.FrobeniusFixedFieldTower.field (G := G) (D := D) T)),
      relativeNorm A T.extension.base.field T.extension.field.field
          T.extension.below uBar.1 = u.1 ∧
      (∀ i, relativeNorm A T.extension.base.field T.extension.field.field
        T.extension.below
        (uBarᵢ i).1 = (uᵢ i).1) ∧
      v.fixedTowerUnitAction T P.baseFrobenius.1 T.commute yBar - yBar =
        v.powerTowerCorrection P s τ hτσn uBar uBarᵢ := by
  dsimp only
  let K := P.ambientBase
  let L := P.ambient.field
  let hLK := P.ambient.below
  let φ := P.frobenius
  let hφ := P.exponent_one
  let n := P.n
  let hn := P.n_pos
  let σ := P.baseFrobenius
  let σn := P.fieldFrobenius
  let tower := P.toFrobeniusFixedFieldTower
  let S := tower.base.field
  let T := tower.field.field
  let SF := tower.base
  let TF := tower.field
  let hTS := tower.field_le_base
  let hTSnormal : (extensionSubgroup S T hTS).Normal := tower.normal
  let : Finite
      (K.field.toSubgroup ⧸ extensionSubgroup K.field L hLK) :=
    P.ambient.finite
  let : Finite
      (S.toSubgroup ⧸ extensionSubgroup S T hTS) :=
    tower.finiteQuotient
  let : (extensionSubgroup S T hTS).Normal := hTSnormal
  have hφσ : φ.1 * σ.1 = σ.1 * φ.1 :=
    P.frobenius_commute_base
  have hφσn : φ.1 * σn.1 = σn.1 * φ.1 :=
    P.frobenius_commute_field
  have hσσn : σ.1 * σn.1 = σn.1 * σ.1 :=
    tower.commute
  have hTSunramified : (DegreeData.AbstractExtension.mk T S hTS).IsUnramified D :=
    D.frobeniusPowerFixedField_isUnramified K L hLK φ hφ n n hn hn
  obtain ⟨gS, hgClosure, _hgDegree, hg⟩ :=
    D.frobeniusPowerFixedField_generator K L hLK φ hφ n n hn hn
  let generator : tower.CyclicGenerator :=
    { element := gS
      mapsToFrobenius := hgClosure
      generates := hg }
  let g : S.toSubgroup ⧸ extensionSubgroup S T hTS := QuotientGroup.mk gS
  let : Fintype (S.toSubgroup ⧸ extensionSubgroup S T hTS) :=
    Fintype.ofFinite _
  let Kuc : FiniteAbstractField G := SF
  let Euc : FiniteUnramifiedCyclicExtension D Kuc :=
    { field := T
      below := hTS
      normal := hTSnormal
      finite := tower.finiteQuotient
      generator := g
      generates := hg
      unramified := hTSunramified }
  let E : FiniteAbstractFieldExtension G := Euc.toFiniteAbstractFieldExtension
  have hEnormal :
      (extensionSubgroup E.base.field E.field.field E.below).Normal :=
    Euc.normal
  let : (extensionSubgroup E.base.field E.field.field E.below).Normal :=
    hEnormal
  let : Fintype
      (E.base.field.toSubgroup ⧸
        extensionSubgroup E.base.field E.field.field E.below) :=
    Fintype.ofFinite _
  have hEunramified : E.IsUnramified D := by
    exact Euc.toFiniteAbstractFieldExtension_isUnramified
  have hA :
      CategoryTheory.Limits.IsZero
          (tateCohomology (v.unitRepresentation E hEnormal) 0) ∧
        CategoryTheory.Limits.IsZero
          (tateCohomology (v.unitRepresentation E hEnormal) (-1)) := by
    simpa [E, hEnormal,
      FiniteUnramifiedCyclicExtension.unitRepresentation] using
        hAxiom Kuc Euc
  obtain ⟨uBar, huBar⟩ :=
    v.exists_unit_relativeNorm_eq_of_tateHZero_isZero
      E hEnormal hEunramified g hg hA.1 u
  have huBarᵢ_exists (i : ι) : ∃ z : v.unitAddSubgroup TF,
      relativeNorm A S T hTS z.1 = (uᵢ i).1 :=
    v.exists_unit_relativeNorm_eq_of_tateHZero_isZero
      E hEnormal hEunramified g hg hA.1 (uᵢ i)
  choose uBarᵢ huBarᵢ using huBarᵢ_exists
  let delta : v.unitAddSubgroup TF :=
    v.powerTowerCorrection P s τ hτσn uBar uBarᵢ
  have hfixedAction
      (q : K.field.toSubgroup ⧸ D.extensionInertiaWithin K.field L hLK)
      (hq : q * σn.1 = σn.1 * q)
      (z : v.unitAddSubgroup TF) :
      v.fixedTowerUnitAction tower q hq z =
        v.frobeniusFixedFieldUnitAction K L hLK σn q hq z := by
    apply Subtype.ext
    apply Subtype.ext
    change A.ρ (Quotient.out q).1 z.1.1 =
      A.ρ (Quotient.out q).1 z.1.1
    rfl
  have hdeltaRelativeNorm : relativeNorm A S T hTS delta.1 = 0 := by
    have hdeltaAmbient :
        delta.1 =
          (v.fixedTowerCorrection K L hLK σn s φ.1 hφσn
            (fun i => (τ i).1) hτσn uBar uBarᵢ).1 := by
      have hdeltaUnit :
          delta =
            v.fixedTowerCorrection K L hLK σn s φ.1 hφσn
              (fun i => (τ i).1) hτσn uBar uBarᵢ := by
        simp [delta, powerTowerCorrection,
          fixedTowerCorrection, tower, K, L, σn,
          hfixedAction]
        rfl
      exact congrArg Subtype.val hdeltaUnit
    rw [hdeltaAmbient]
    let : Finite ((baseField G).toSubgroup ⧸
        extensionSubgroup (baseField G) (D.frobeniusFixedField K L hLK σ)
          (le_baseField (D.frobeniusFixedField K L hLK σ))) :=
      tower.baseAbsoluteFinite
    exact
      v.fixedTowerCorrection_relativeNorm_eq_zero K L hLK σ σn hTS
        s φ.1 hφσ hφσn (fun i => (τ i).1) hτσ hτσn
        u uᵢ uBar uBarᵢ huBar huBarᵢ hstar
  let U := v.unitRepresentation E hEnormal
  have hdeltaNorm : U.norm.hom delta = 0 := by
    apply Subtype.ext
    apply Subtype.ext
    calc
      (((U.norm.hom delta).1 : ambientFixedAddSubgroup A T) : A.V) =
          ((relativeNorm A S T hTS delta.1 : ambientFixedAddSubgroup A S) : A.V) :=
        v.unitRepresentation_norm_coe E hEnormal delta
      _ = 0 := congrArg Subtype.val hdeltaRelativeNorm
      _ = (((0 : v.unitAddSubgroup TF).1 : ambientFixedAddSubgroup A T) : A.V) := rfl
  obtain ⟨yBar, hyBar⟩ :=
    v.exists_unit_sigma_sub_eq_of_tateHMinusOne_isZero
      E hEnormal g hg hA.2 delta hdeltaNorm
  have haction :=
    v.unitRepresentation_generator_action_eq
      tower generator.toRepresentative yBar
  have haction' :
      v.fixedTowerUnitAction tower σ.1 hσσn yBar = U.ρ g yBar := by
    apply Subtype.ext
    apply Subtype.ext
    calc
      (v.fixedTowerUnitAction tower σ.1 hσσn yBar).1.1 =
          (((v.unitRepresentation tower.extension tower.normal).ρ
            (QuotientGroup.mk generator.element) yBar).1.1 : A.V) :=
        congrArg (fun z : v.unitAddSubgroup TF => z.1.1) haction
      _ = (U.ρ g yBar).1.1 := by
        rfl
  refine ⟨uBar, uBarᵢ, yBar, huBar, huBarᵢ, ?_⟩
  rw [← haction'] at hyBar
  apply Subtype.ext
  apply Subtype.ext
  exact congrArg (fun z : v.unitAddSubgroup TF => z.1.1) hyBar

/-- The maximal-unramified norm of a relative norm in the power-fixed
tower is the corresponding orbit sum.  This is the actual norm-enumeration
step behind the factor `z^n`. -/
theorem maximalNorm_relativeNorm_fixedTower
    [IsTopologicalGroup G] [CompactSpace G] [T2Space G]
    [TotallyDisconnectedSpace G]
    (v : ValuationData D A)
    (FT : DegreeData.FiniteAmbientFrobeniusFixedFieldTower D)
    (generator : FT.toFrobeniusFixedFieldTower.CyclicGenerator)
    (n : ℕ)
    (hcard : (FT.extension.degree : ℕ) = n)
    (a : v.unitAddSubgroup
      (DegreeData.FrobeniusFixedFieldTower.field (G := G) (D := D)
        FT.toFrobeniusFixedFieldTower)) :
    letI : Finite
        ((D.maximalUnramifiedField FT.ambientBase.field).toSubgroup ⧸
          extensionSubgroup (D.maximalUnramifiedField FT.ambientBase.field)
            (D.maximalUnramifiedField FT.ambient.field)
            (D.maximalUnramifiedField_mono FT.ambient.below)) :=
      D.maximalUnramifiedExtension_finite FT.ambientBase.field
        FT.ambient.field FT.ambient.below
    let Ext := FT.extension
    let S := Ext.base.field
    let T := Ext.field.field
    let I := D.maximalUnramifiedField FT.ambientBase.field
    let E := D.maximalUnramifiedField FT.ambient.field
    let hTE : E.toSubgroup ≤ T.toSubgroup := by
      change (D.maximalUnramifiedField FT.ambient.field).toSubgroup ≤
        (D.frobeniusFixedField FT.ambientBase FT.ambient.field
          FT.ambient.below FT.fieldFrobenius).toSubgroup
      rw [D.maximalUnramifiedField_eq_fieldInertia]
      exact D.fieldInertia_le_frobeniusFixedField FT.ambientBase
        FT.ambient.field FT.ambient.below FT.fieldFrobenius
    let hSE : E.toSubgroup ≤ S.toSubgroup := by
      change (D.maximalUnramifiedField FT.ambient.field).toSubgroup ≤
        (D.frobeniusFixedField FT.ambientBase FT.ambient.field
          FT.ambient.below FT.baseFrobenius).toSubgroup
      rw [D.maximalUnramifiedField_eq_fieldInertia]
      exact D.fieldInertia_le_frobeniusFixedField FT.ambientBase
        FT.ambient.field FT.ambient.below FT.baseFrobenius
    let hEI := D.maximalUnramifiedField_mono FT.ambient.below
    let N := relativeNorm A I E hEI
    let J := fixedFieldInclusion A I E hEI
    J (N (fixedFieldInclusion A S E hSE
        (relativeNorm A S T Ext.below a.1))) =
      D.frobeniusPowerSum A FT.ambientBase.field FT.ambient.field
        FT.ambient.below FT.baseFrobenius.1 n
        (J (N (fixedFieldInclusion A T E hTE a.1))) := by
  dsimp only
  let tower := FT.toFrobeniusFixedFieldTower
  let K := FT.ambientBase
  let L := FT.ambient.field
  let hLK := FT.ambient.below
  let σ := FT.baseFrobenius
  let σ' := FT.fieldFrobenius
  let hTS := FT.field_le_base
  let hTSnormal : (extensionSubgroup FT.base.field FT.field.field hTS).Normal :=
    FT.normal
  let gS := generator.element
  let hgClosure := generator.mapsToFrobenius
  let hg := generator.generates
  let hσσ' := FT.commute
  let : Finite
      ((D.maximalUnramifiedField K.field).toSubgroup ⧸
        extensionSubgroup (D.maximalUnramifiedField K.field)
          (D.maximalUnramifiedField L)
          (D.maximalUnramifiedField_mono hLK)) :=
    D.maximalUnramifiedExtension_finite K.field L hLK
  let S := FT.base.field
  let T := FT.field.field
  let SF := FT.base
  let TF := FT.field
  let : Finite (S.toSubgroup ⧸ extensionSubgroup S T hTS) :=
    FT.finiteQuotient
  let : (extensionSubgroup S T hTS).Normal := hTSnormal
  let I := D.maximalUnramifiedField K.field
  let E := D.maximalUnramifiedField L
  let hTE : E.toSubgroup ≤ T.toSubgroup := by
    change (D.maximalUnramifiedField L).toSubgroup ≤
      (D.frobeniusFixedField K L hLK σ').toSubgroup
    rw [D.maximalUnramifiedField_eq_fieldInertia]
    exact D.fieldInertia_le_frobeniusFixedField K L hLK σ'
  let hSE : E.toSubgroup ≤ S.toSubgroup := by
    change (D.maximalUnramifiedField L).toSubgroup ≤
      (D.frobeniusFixedField K L hLK σ).toSubgroup
    rw [D.maximalUnramifiedField_eq_fieldInertia]
    exact D.fieldInertia_le_frobeniusFixedField K L hLK σ
  let hEI := D.maximalUnramifiedField_mono hLK
  let N := relativeNorm A I E hEI
  let J := fixedFieldInclusion A I E hEI
  let Ext : FiniteAbstractFieldExtension G := FT.extension
  have hExtNormal :
      (extensionSubgroup Ext.base.field Ext.field.field Ext.below).Normal :=
    FT.normal
  let : (extensionSubgroup Ext.base.field Ext.field.field Ext.below).Normal :=
    hExtNormal
  let U := v.unitRepresentation Ext hExtNormal
  let g : S.toSubgroup ⧸ extensionSubgroup S T hTS := QuotientGroup.mk gS
  let f : v.unitAddSubgroup TF → v.unitAddSubgroup TF :=
    v.frobeniusFixedFieldUnitAction K L hLK σ' σ.1 hσσ'
  let F : v.unitAddSubgroup TF →+ ambientFixedAddSubgroup A E :=
    (J.comp N).comp
      ((fixedFieldInclusion A T E hTE).comp (v.unitAddSubgroup TF).subtype)
  let act : ambientFixedAddSubgroup A E → ambientFixedAddSubgroup A E :=
    D.frobeniusQuotientAction A K.field L hLK σ.1
  have hsemiconj : Function.Semiconj F f act := by
    intro z
    have hIncl := D.frobeniusFixedFieldAction_inclusion A K L hLK
      σ' σ.1 hσσ' z.1
    have hNorm := D.maximalUnramifiedNorm_frobeniusQuotientAction
      A K.field L hLK σ.1 (fixedFieldInclusion A T E hTE z.1)
    calc
      F (f z) = J (N (D.frobeniusQuotientAction A K.field L hLK σ.1
          (fixedFieldInclusion A T E hTE z.1))) := by
        apply congrArg (J.comp N)
        exact hIncl
      _ = D.frobeniusQuotientAction A K.field L hLK σ.1
          (J (N (fixedFieldInclusion A T E hTE z.1))) := hNorm
      _ = act (F z) := rfl
  let : Fintype (S.toSubgroup ⧸ extensionSubgroup S T hTS) :=
    Fintype.ofFinite _
  let : Fintype
      (Ext.base.field.toSubgroup ⧸
        extensionSubgroup Ext.base.field Ext.field.field Ext.below) := by
    change Fintype (S.toSubgroup ⧸ extensionSubgroup S T hTS)
    infer_instance
  have hcard' : Fintype.card
      (S.toSubgroup ⧸ extensionSubgroup S T hTS) = n := by
    calc
      Fintype.card (S.toSubgroup ⧸ extensionSubgroup S T hTS) =
          Nat.card (S.toSubgroup ⧸ extensionSubgroup S T hTS) := by
        rw [Nat.card_eq_fintype_card]
      _ = (Ext.degree : ℕ) :=
        Ext.toFiniteAbstractExtension.degree_coe.symm
      _ = n := hcard
  have hgen (z : v.unitAddSubgroup TF) : U.ρ g z = f z :=
    (v.unitRepresentation_generator_action_eq
      tower generator.toRepresentative z).symm
  have hRep := rep_norm_eq_generatorIterateSum U g hg n hcard' f hgen a
  have hMapped : F (U.norm.hom a) =
      ∑ i : Fin n, F ((f^[i.1]) a) := by
    calc
      F (U.norm.hom a) = F (∑ i : Fin n, (f^[i.1]) a) :=
        congrArg F hRep
      _ = ∑ i : Fin n, F ((f^[i.1]) a) :=
        map_sum F (fun i : Fin n => (f^[i.1]) a) Finset.univ
  have hMapped' : F (U.norm.hom a) =
      ∑ i : Fin n, D.frobeniusQuotientAction A K.field L hLK
        (σ.1 ^ i.1) (F a) := by
    calc
      F (U.norm.hom a) = ∑ i : Fin n, F ((f^[i.1]) a) := hMapped
      _ = ∑ i : Fin n, (act^[i.1]) (F a) := by
        apply Finset.sum_congr rfl
        intro i _
        exact hsemiconj.iterate_right i.1 a
      _ = _ := by
        apply Finset.sum_congr rfl
        intro i _
        let B := D.frobeniusQuotientRepresentation A K.field L hLK
        have hpow :=
          (rep_action_pow_eq_iterate B σ.1 i.1 (F a)).symm
        change
          ((D.frobeniusQuotientAction A K.field L hLK σ.1)^[i.1]) (F a) =
            D.frobeniusQuotientAction A K.field L hLK
              (σ.1 ^ i.1) (F a) at hpow
        simpa only [act] using hpow
  have hLeft : F (U.norm.hom a) =
      J (N (fixedFieldInclusion A S E hSE
        (relativeNorm A S T hTS a.1))) := by
    apply congrArg (J.comp N)
    apply Subtype.ext
    exact v.unitRepresentation_norm_coe Ext hExtNormal a
  calc
    J (N (fixedFieldInclusion A S E hSE
        (relativeNorm A S T hTS a.1))) = F (U.norm.hom a) := hLeft.symm
    _ = ∑ i : Fin n, D.frobeniusQuotientAction A K.field L hLK
        (σ.1 ^ i.1) (F a) := hMapped'
    _ = D.frobeniusPowerSum A K.field L hLK σ.1 n
        (J (N (fixedFieldInclusion A T E hTE a.1))) := rfl

/-- The corrected barred unit satisfies the original coinvariant equation
after inclusion into the maximal unramified field. -/
theorem universalNormDescent_correctedEquation
    (v : ValuationData D A)
    [IsTopologicalGroup G] [CompactSpace G] [T2Space G]
    [TotallyDisconnectedSpace G]
    (K : DegreeData.FiniteResidueAbstractField D) (L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.field.toSubgroup)
    [hLnormal : (extensionSubgroup K.field L hLK).Normal]
    (σ σn : D.FrobeniusElements K L hLK)
    {ι : Type v} (s : Finset ι)
    (φ : K.field.toSubgroup ⧸ D.extensionInertiaWithin K.field L hLK)
    (hφσn : φ * σn.1 = σn.1 * φ)
    (τ : ι →
      K.field.toSubgroup ⧸ D.extensionInertiaWithin K.field L hLK)
    (hτσn : ∀ i, τ i * σn.1 = σn.1 * τ i)
    (hσσn : σ.1 * σn.1 = σn.1 * σ.1)
    [hTabsolute : Finite ((baseField G).toSubgroup ⧸
      extensionSubgroup (baseField G)
        (D.frobeniusFixedField K L hLK σn)
        (le_baseField (D.frobeniusFixedField K L hLK σn)))]
    (n : ℕ)
    (hσpow : σ.1 = φ ^ n)
    (uBar : v.unitAddSubgroup
      (D.frobeniusFixedAbstractField K L hLK σn))
    (uBarᵢ : ι → v.unitAddSubgroup
      (D.frobeniusFixedAbstractField K L hLK σn))
    (yBar : v.unitAddSubgroup
      (D.frobeniusFixedAbstractField K L hLK σn))
    (hyBar :
      v.frobeniusFixedFieldUnitAction K L hLK σn σ.1 hσσn yBar - yBar =
        v.fixedTowerCorrection K L hLK σn s φ hφσn
          τ hτσn uBar uBarᵢ) :
    let E := D.maximalUnramifiedField L
    let hTE := D.fieldInertia_le_frobeniusFixedField K L hLK σn
    let uBarE := fixedFieldInclusion A
      (D.frobeniusFixedField K L hLK σn) E hTE uBar.1
    let uBarᵢE := fun i => fixedFieldInclusion A
      (D.frobeniusFixedField K L hLK σn) E hTE (uBarᵢ i).1
    let yBarE := fixedFieldInclusion A
      (D.frobeniusFixedField K L hLK σn) E hTE yBar.1
    let w := uBarE - D.frobeniusPowerSum A K.field L hLK φ n yBarE
    D.frobeniusQuotientAction A K.field L hLK φ w - w =
      ∑ i ∈ s,
        (D.frobeniusQuotientAction A K.field L hLK (τ i) (uBarᵢE i) -
          uBarᵢE i) := by
  dsimp only
  let T := D.frobeniusFixedField K L hLK σn
  let TF := D.frobeniusFixedAbstractField K L hLK σn
  let E := D.maximalUnramifiedField L
  let hTE := D.fieldInertia_le_frobeniusFixedField K L hLK σn
  let uBarE := fixedFieldInclusion A T E hTE uBar.1
  let uBarᵢE := fun i => fixedFieldInclusion A T E hTE (uBarᵢ i).1
  let yBarE := fixedFieldInclusion A T E hTE yBar.1
  let φny := D.frobeniusPowerSum A K.field L hLK φ n yBarE
  let w := uBarE - φny
  have hdeltaCoe := v.fixedTowerCorrection_coe K L hLK σn
    s φ hφσn τ hτσn uBar uBarᵢ
  have hyVal := congrArg (fun z : v.unitAddSubgroup TF => z.1.1) hyBar
  have hdeltaVal := congrArg
    (fun z : ambientFixedAddSubgroup A TF.field => z.1) hdeltaCoe
  have hdeltaVal' :
      (v.fixedTowerCorrection K L hLK σn s φ hφσn
        τ hτσn uBar uBarᵢ).1.1 =
        A.ρ (Quotient.out φ).1 uBar.1.1 - uBar.1.1 -
          ∑ i ∈ s,
            (A.ρ (Quotient.out (τ i)).1 (uBarᵢ i).1.1 -
              (uBarᵢ i).1.1) := by
    change
      (v.fixedTowerCorrection K L hLK σn s φ hφσn
        τ hτσn uBar uBarᵢ).1.1 =
        (AddSubgroup.subtype (ambientFixedAddSubgroup A TF.field))
          ((v.frobeniusFixedFieldUnitAction K L hLK σn
              φ hφσn uBar).1 -
            uBar.1 - ∑ i ∈ s,
              ((v.frobeniusFixedFieldUnitAction K L hLK σn
                (τ i) (hτσn i) (uBarᵢ i)).1 - (uBarᵢ i).1)) at hdeltaVal
    rw [map_sub, map_sub, map_sum] at hdeltaVal
    simp only [ValuationData.frobeniusFixedFieldUnitAction] at hdeltaVal
    exact hdeltaVal
  have hraw :
      A.ρ (Quotient.out σ.1).1 yBar.1.1 - yBar.1.1 =
        A.ρ (Quotient.out φ).1 uBar.1.1 - uBar.1.1 -
          ∑ i ∈ s,
            (A.ρ (Quotient.out (τ i)).1 (uBarᵢ i).1.1 -
              (uBarᵢ i).1.1) :=
    hyVal.trans hdeltaVal'
  have hcorrE :
      D.frobeniusQuotientAction A K.field L hLK σ.1 yBarE - yBarE =
        D.frobeniusQuotientAction A K.field L hLK φ uBarE - uBarE -
          ∑ i ∈ s,
            (D.frobeniusQuotientAction A K.field L hLK (τ i) (uBarᵢE i) -
              uBarᵢE i) := by
    apply Subtype.ext
    change
      (AddSubgroup.subtype (ambientFixedAddSubgroup A E))
          (D.frobeniusQuotientAction A K.field L hLK σ.1 yBarE - yBarE) =
        (AddSubgroup.subtype (ambientFixedAddSubgroup A E))
          (D.frobeniusQuotientAction A K.field L hLK φ uBarE - uBarE -
            ∑ i ∈ s,
              (D.frobeniusQuotientAction A K.field L hLK (τ i) (uBarᵢE i) -
                uBarᵢE i))
    rw [map_sub, map_sub, map_sum]
    simp_rw [map_sub]
    change
      (D.frobeniusQuotientAction A K.field L hLK σ.1 yBarE).1 - yBarE.1 =
        (D.frobeniusQuotientAction A K.field L hLK φ uBarE).1 - uBarE.1 -
          ∑ i ∈ s,
            ((D.frobeniusQuotientAction A K.field L hLK (τ i) (uBarᵢE i)).1 -
              (uBarᵢE i).1)
    simp_rw [D.frobeniusQuotientAction_coe_out]
    exact hraw
  have htel := D.frobeniusPowerSum_action_sub A K.field L hLK φ n yBarE
  rw [← hσpow] at htel
  have hw :
      D.frobeniusQuotientAction A K.field L hLK φ w - w =
        (D.frobeniusQuotientAction A K.field L hLK φ uBarE - uBarE) -
          (D.frobeniusQuotientAction A K.field L hLK φ φny - φny) := by
    dsimp [w]
    apply Subtype.ext
    change
      (AddSubgroup.subtype (ambientFixedAddSubgroup A E))
          (D.frobeniusQuotientAction A K.field L hLK φ (uBarE - φny) -
            (uBarE - φny)) =
        (AddSubgroup.subtype (ambientFixedAddSubgroup A E))
          ((D.frobeniusQuotientAction A K.field L hLK φ uBarE - uBarE) -
            (D.frobeniusQuotientAction A K.field L hLK φ φny - φny))
    rw [map_sub, map_sub, map_sub, map_sub]
    change
      (D.frobeniusQuotientAction A K.field L hLK φ (uBarE - φny)).1 -
          (uBarE.1 - φny.1) =
        ((D.frobeniusQuotientAction A K.field L hLK φ uBarE).1 - uBarE.1) -
          ((D.frobeniusQuotientAction A K.field L hLK φ φny).1 - φny.1)
    simp_rw [D.frobeniusQuotientAction_coe_out]
    change
      A.ρ (Quotient.out φ).1 (uBarE.1 - φny.1) -
          (uBarE.1 - φny.1) =
        (A.ρ (Quotient.out φ).1 uBarE.1 - uBarE.1) -
          (A.ρ (Quotient.out φ).1 φny.1 - φny.1)
    rw [map_sub]
    abel
  rw [hw, htel, hcorrE]
  abel

end ValuationData
end

end ClassFormation
end

section
-- module Solutions.OAIQ244_DUKE.AbstractClassFieldTheory_Reciprocity_Construction_InfiniteUnitNormSubgroup
attribute [-instance] _root_.ClassFormation.FiniteGaloisSubextension.extensionSubgroup_over_intermediate_normalInstance _root_.ClassFormation.FiniteGaloisSubextension.intermediateField_normalInstance _root_.ClassFormation.instIsAddTorsionFreeZHat _root_.ClassFormation.instIsMulTorsionFreeMultiplicativeZHat _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace
attribute [-simp] _root_.ClassFormation.DegreeData.chosenUnramifiedFrobeniusLift_exponent _root_.ClassFormation.DegreeData.finiteReciprocityCandidate_apply _root_.ClassFormation.DegreeData.finiteReciprocityCandidate_zero _root_.ClassFormation.DegreeData.frobeniusActionConjugate_coe _root_.ClassFormation.DegreeData.frobeniusExponent_actionConjugate _root_.ClassFormation.DegreeData.frobeniusExponent_chosenDegreeOneFrobeniusElement _root_.ClassFormation.DegreeData.frobeniusExponent_mul _root_.ClassFormation.DegreeData.frobeniusLiftDifference_coe _root_.ClassFormation.DegreeData.frobeniusRestriction_chosenFiniteReciprocityFrobeniusLift _root_.ClassFormation.DegreeData.frobeniusRestriction_mul _root_.ClassFormation.FiniteAbelianSubextension.extensionQuotientMk_apply _root_.ClassFormation.FiniteGaloisSubextension.classFieldCandidate_field _root_.ClassFormation.ValuationData.canonicalUnramifiedNormQuotientValuation_finiteNormClass _root_.ClassFormation.ValuationData.canonicalValueQuotientHom_mk _root_.ClassFormation.ValuationData.canonicalValueReduction_one _root_.ClassFormation.ValuationData.unramifiedNormQuotientValuation_finiteNormClass _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.ClassFormation.cyclicNormClassHom_apply _root_.ClassFormation.extensionFixedRepresentationEquiv_apply_coe _root_.ClassFormation.extensionFixedRepresentationEquiv_symm_apply_coe _root_.ClassFormation.mem_normFilterBasis_iff _root_.ClassFormation.toZModPow_zHatToPadicInt _root_.ClassFormation.zHatReductionRingHom_apply _root_.ClassFormation.zHatRingEquivProfiniteIntegerPrimeProduct_apply _root_.ClassFormation.zHatToPadicInt_intCast _root_.ClassFormation.zHatToProfiniteIntegerPrimeProduct_apply _root_.ClassFormation.zHatToProfiniteIntegerPrimeProduct_intCast _root_.ClassFormation.zHatUnitsContinuousMulEquivPrimeProduct_coe_apply _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.LocalFieldTheory.residueField_algebraMap_residue _root_.OAI.PrimeDegreePackets.ThetaConstruction.schwartzCM_apply
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

/-!
# Infinite unit norm subgroups

This module defines the finite-level and infinite unit norm ranges, proves
their tower compatibility, and compares them with the ambient norm
subgroups.
-/

noncomputable section

open CategoryTheory
open scoped BigOperators

variable {G : IntegralRepGroupType} [Group G] [TopologicalSpace G]

namespace ValuationData

variable {D : DegreeData G} {A : Rep ℤ G}

/-- A unit norm obtained from a finite overfield of `M` already lies in the
unit norm range attached to `M`, by transitivity of the actual norm. -/
theorem mem_finiteIntermediateUnitNormRange_of_overfield
    (v : ValuationData D A) (E : ClosedSubgroup G)
    (K : FiniteAbstractField G)
    (M P : FiniteIntermediateField E K.field)
    (hPM : P.field.toSubgroup ≤ M.field.toSubgroup)
    [hPfinite : Finite
      (K.field.toSubgroup ⧸ extensionSubgroup K.field P.field P.below)]
    (uP : v.unitAddSubgroup (P.toFiniteAbstractField K))
    (aK : ambientFixedAddSubgroup A K.field)
    (haK : relativeNorm A K.field P.field P.below uP.1 = aK) :
    aK ∈ v.finiteIntermediateUnitNormRange E K M := by
  let hMfinite : Finite
      (K.field.toSubgroup ⧸ extensionSubgroup K.field M.field M.below) :=
    M.finite
  let hPMfinite : Finite
      (M.field.toSubgroup ⧸ extensionSubgroup M.field P.field hPM) :=
    FiniteIntermediateField.finite_extension_of_le P.below M.below hPM
  let : Finite
      ((M.toFiniteAbstractField K).field.toSubgroup ⧸
        extensionSubgroup (M.toFiniteAbstractField K).field P.field hPM) := by
    change Finite
      (M.field.toSubgroup ⧸ extensionSubgroup M.field P.field hPM)
    exact hPMfinite
  let EMP : FiniteAbstractFieldExtension G :=
    FiniteAbstractFieldExtension.ofInclusion
      P.field (M.toFiniteAbstractField K) hPM
  let uM : v.unitAddSubgroup (M.toFiniteAbstractField K) :=
    by
      simpa [EMP, FiniteAbstractFieldExtension.ofInclusion] using
        v.finiteUnitNorm EMP uP
  let T : DegreeData.FiniteTower G := {
    top := P.field
    middle := M.field
    base := K.field
    top_le_middle := hPM
    middle_le_base := M.below
    finiteTopQuotient := hPMfinite
    finiteBaseQuotient := hMfinite }
  simp only [finiteIntermediateUnitNormRange]
  change aK ∈ ((relativeNorm A K.field M.field M.below).comp
    (v.unitAddSubgroup (M.toFiniteAbstractField K)).subtype).range
  refine ⟨uM, ?_⟩
  change relativeNorm A K.field M.field M.below
      (relativeNorm A M.field P.field hPM uP.1) = aK
  calc
    _ = relativeNorm A K.field P.field (hPM.trans M.below) uP.1 :=
      T.norm_trans_apply A uP.1
    _ = relativeNorm A K.field P.field P.below uP.1 := by rfl
    _ = aK := haK

end ValuationData
end

end ClassFormation
end

section
-- module Solutions.OAIQ244_DUKE.AbstractClassFieldTheory_Reciprocity_Construction_Universal
attribute [-instance] _root_.ClassFormation.FiniteGaloisSubextension.extensionSubgroup_over_intermediate_normalInstance _root_.ClassFormation.FiniteGaloisSubextension.intermediateField_normalInstance _root_.ClassFormation.instIsAddTorsionFreeZHat _root_.ClassFormation.instIsMulTorsionFreeMultiplicativeZHat _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace
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

/-- The universal norm-descent lemma, first descent step: the maximal-unramified norm of `u`
is represented by a genuine unit over `K`. -/
theorem universalNormDescent_endpoint_descent
    (v : ValuationData D A) [IsTopologicalGroup G]
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
          (D.maximalUnramifiedField L) (D.maximalUnramifiedField_mono hLK) u.1 := by
  let : Finite
      ((D.maximalUnramifiedField K.field).toSubgroup ⧸
        extensionSubgroup (D.maximalUnramifiedField K.field)
          (D.maximalUnramifiedField L)
          (D.maximalUnramifiedField_mono hLK)) :=
    D.maximalUnramifiedExtension_finite K.field L hLK
  have hfixed := D.maximalUnramifiedNorm_fixed_of_hstar A
    (K.toFiniteResidueAbstractField D) L hLK
    s φ.1 τ u.1 (fun i => (uᵢ i).1) hstar
  exact v.descend_maximalUnramifiedNorm_unit K L hLK φ hφ u.1 u.2 hfixed

end ValuationData

end
end ClassFormation
end

section
-- module Solutions.OAIQ244_DUKE.AbstractClassFieldTheory_Reciprocity_Construction_MainMultiplicativity_CorrectionSum
attribute [-instance] _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.maximalIdealPowSuccQuotModule _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace
attribute [-simp] _root_.ClassFormation.DegreeData.finiteReciprocityCandidate_apply _root_.ClassFormation.DegreeData.finiteReciprocityCandidate_zero _root_.ClassFormation.FiniteGaloisSubextension.classFieldCandidate_field _root_.ClassFormation.ValuationData.canonicalUnramifiedNormQuotientValuation_finiteNormClass _root_.ClassFormation.ValuationData.canonicalValueQuotientHom_mk _root_.ClassFormation.ValuationData.canonicalValueReduction_one _root_.ClassFormation.ValuationData.unramifiedNormQuotientValuation_finiteNormClass _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.ClassFormation.cyclicNormClassHom_apply _root_.ClassFormation.extensionFixedRepresentationEquiv_apply_coe _root_.ClassFormation.extensionFixedRepresentationEquiv_symm_apply_coe _root_.ClassFormation.mem_normFilterBasis_iff _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.LocalFieldTheory.residueField_algebraMap_residue _root_.OAI.PrimeDegreePackets.ThetaConstruction.schwartzCM_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

/-!
# Correction sums for reciprocity multiplicativity

This file packages the three correction coefficients and action elements,
proves their degree-zero property, and identifies their action-difference sum.
-/

universe u

namespace ClassFormation

open KummerTheory
open CyclicCohomology

noncomputable section

open CategoryTheory
open scoped BigOperators

/-- Correction coefficients in the order produced by the left-action
translation of the Frobenius multiplicativity identity. -/
def frobeniusMultiplicativityCorrectionTerm
    {R : IntegralRepGroupType} [Group R]
    (B : Rep ℤ R) (τ₁ : R) (p₁ p₃ p₄ : B.V) : Fin 3 → B.V :=
  ![p₄ - p₃, p₁ - p₃, p₃ - B.ρ τ₁ p₃]

/-- Explicit left-action form of the group-ring identity, with the factor
order and the first two terms arranged as they occur in `(*)`. -/
theorem frobeniusMultiplicativity_actionDifference_eq_correctionSum
    {R : IntegralRepGroupType} [Group R] (B : Rep ℤ R)
    (τ₁ τ₄ : R) (p₁ p₃ p₄ : B.V) :
    (B.ρ τ₄ p₄ - p₄) + (B.ρ τ₁ p₁ - p₁) +
        (p₃ - B.ρ (τ₄ * τ₁) p₃) =
      ∑ i : Fin 3,
        (B.ρ (frobeniusMultiplicativityCorrectionAction τ₁ τ₄ i)
          (frobeniusMultiplicativityCorrectionTerm B τ₁ p₁ p₃ p₄ i) -
          frobeniusMultiplicativityCorrectionTerm B τ₁ p₁ p₃ p₄ i) := by
  have hmul : B.ρ (τ₄ * τ₁) p₃ = B.ρ τ₄ (B.ρ τ₁ p₃) := by
    rw [map_mul]
    rfl
  rw [hmul]
  simp [frobeniusMultiplicativityCorrectionAction,
    frobeniusMultiplicativityCorrectionTerm, Fin.sum_univ_succ, map_sub]
  abel

end

end ClassFormation
end

section
-- module Solutions.OAIQ244_DUKE.AbstractClassFieldTheory_Reciprocity_Construction_MainFiniteReciprocity
attribute [-instance] _root_.ClassFormation.FiniteGaloisSubextension.extensionSubgroup_over_intermediate_normalInstance _root_.ClassFormation.FiniteGaloisSubextension.intermediateField_normalInstance _root_.ClassFormation.instIsAddTorsionFreeZHat _root_.ClassFormation.instIsMulTorsionFreeMultiplicativeZHat _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace
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

section frobeniusLiftAlgebra

variable {G : Type u} [Group G] [TopologicalSpace G]

namespace DegreeData

/-- If the two lifts have the same restriction, their quotient restricts
trivially. -/
theorem frobeniusRestriction_frobeniusLiftDifference (D : DegreeData G)
    (K : FiniteResidueAbstractField D) (L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.field.toSubgroup)
    [hLnormal : (extensionSubgroup K.field L hLK).Normal]
    (σ τ : D.FrobeniusElements K L hLK)
    (hRestriction : D.frobeniusRestriction K L hLK σ =
      D.frobeniusRestriction K L hLK τ)
    (hdegree : D.frobeniusExponent K L hLK σ <
      D.frobeniusExponent K L hLK τ) :
    D.frobeniusRestriction K L hLK
      (D.frobeniusLiftDifference K L hLK σ τ hdegree) = 1 := by
  change D.extensionRestriction K.field L hLK
    (D.frobeniusLiftDifference K L hLK σ τ hdegree).1 = 1
  rw [D.frobeniusLiftDifference_coe K L hLK σ τ hdegree]
  rw [map_mul, map_inv]
  change (D.frobeniusRestriction K L hLK σ)⁻¹ *
      D.frobeniusRestriction K L hLK τ = 1
  rw [hRestriction, inv_mul_cancel]

end DegreeData

end frobeniusLiftAlgebra

/-!
# The abstract reciprocity construction, the unramified norm-quotient equivalence

This file proves the generator calculation in the unramified case: the finite reciprocity equivalence sends arithmetic Frobenius to the prime
class.  That class generates the finite norm quotient, so the resulting
reciprocity homomorphism is promoted to an additive equivalence.
-/

end

end ClassFormation
end

section
-- module Solutions.OAIQ244_DUKE.LocalField_NonarchimedeanLocalField_NormQuotient
attribute [-instance] _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.CyclicCohomology.binaryCoefficientFamilyCommGroup _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false
/-!
# Quotients by local norm subgroups

Constructs `Kˣ/N(Lˣ)`, its universal maps and comparison equivalences, and
relates its finite cardinality to the index of the norm subgroup.
-/

namespace LocalFieldTheory

noncomputable section

universe u v

/-- A base-field unit has trivial norm class exactly when it lies in the local norm subgroup. -/
theorem normClass_eq_one_iff (K L : Type u) [Field K] [Field L]
    [Algebra K L] (x : Kˣ) :
    normClass K L x = 1 ↔ ∃ y : Lˣ, normUnits K L y = x := by
  rw [← MonoidHom.mem_range]
  exact QuotientGroup.eq_one_iff x

/-! ### Surjectivity and equality refinements for norm quotients -/

end
end LocalFieldTheory
end

section
-- module Solutions.OAIQ244_DUKE.AlgebraicNumberTheory_Idele_NormApproximation_FinitePlaces
attribute [-instance] _root_.OAI.PrimeDegreePackets.diagonalLogAction _root_.OAI.PrimeDegreePackets.matrixSecondCountable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

/-!
# Weak approximation for actual local norm quotients

For a finite Galois extension `L / K` and a finite set `S` of finite
places of `K`, this file chooses an actual extension of every `v ∈ S`,
forms the corresponding algebraic localization `L_w / K_v`, and
transports its local norm subgroup to mathlib's concrete adic
completion.  These transported norm subgroups are open.  Multiplicative
weak approximation therefore gives a surjection

`Kˣ → ∏ v ∈ S, K_vˣ / N(L_wˣ)`.

All choices are made from the extension theorem for absolute values;
none of the local conclusions is included as input data.
-/

open scoped NumberField Classical NNReal
open NumberField IsDedekindDomain

noncomputable section

open LocalClassFieldTheory


open AlgebraicNumberTheory.Valuations
open LocalClassFieldTheory
open LocalFieldTheory

variable {K L : Type}
    [Field K] [NumberField K]
    [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]

/-- The chosen actual localization `L_w` above the finite place `v`. -/
abbrev ChosenFinitePlaceLocalizedCompletion
    (v : HeightOneSpectrum (𝓞 K)) :=
  LocalizedCompletion
    (NumberField.HeightOneSpectrum.adicAbv K v)
    (chosenFinitePlaceExtension (L := L) v)

/-- The concrete local norm subgroup at `v`.  It is first formed in the
absolute-value completion model and then transported to the adic
completion used by the idele library. -/
noncomputable def chosenFinitePlaceLocalNormSubgroup
    (v : HeightOneSpectrum (𝓞 K)) :
    Subgroup (v.adicCompletion K)ˣ := by
  let vK :=
    NumberField.HeightOneSpectrum.adicAbv K v
  let w := chosenFinitePlaceExtension (L := L) v
  letI hK :=
    AbsoluteValue.extensionCompletionAlgebra
      (K := K) w.1
  letI : SMul K w.1.Completion := hK.toSMul
  letI : Algebra vK.Completion w.1.Completion :=
    AbsoluteValue.completionAlgebra vK w.1 w.2
  let E := LocalizedCompletion vK w
  let e :
      vK.Completionˣ ≃ₜ* (v.adicCompletion K)ˣ :=
    finitePlaceCompletionUnitsContinuousMulEquiv v
  exact
    (localNormSubgroup vK.Completion E).map
      e.toMonoidHom

/-- The actual local norm quotient in the concrete finite-place
completion used by ideles. -/
abbrev ChosenFinitePlaceNormQuotient
    (v : HeightOneSpectrum (𝓞 K)) :=
  (v.adicCompletion K)ˣ ⧸
    chosenFinitePlaceLocalNormSubgroup
      (K := K) (L := L) v
end
end

section
-- module Solutions.OAIQ244_DUKE.AlgebraicNumberTheory_Adele_IntegralTensorSupport_LocalTensorDecomposition
attribute [-instance] _root_.OAI.PrimeDegreePackets.matrixSecondCountable
attribute [-simp] _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.OAI.PrimeDegreePackets.ThetaConstruction.schwartzCM_apply _root_.doubleCosetExtension_mk _root_.extendAbsoluteValueExtensionFromIntermediate_apply _root_.mem_finitePlaceDecompositionGroup_iff _root_.restrictAbsoluteValueExtensionToIntermediate_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

/-!
# Integral comparison for local tensor decompositions

This module identifies integrality and units in a finite-place tensor factor
with the corresponding componentwise conditions in the completions above that
place.
-/

open scoped NumberField TensorProduct NNReal
open NumberField IsDedekindDomain

noncomputable section

open AlgebraicNumberTheory.Valuations

universe u v

variable
    {K : Type u} {L : Type v}
    [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L]

section LocalTensorDecompositionIntegralComparison

/-- The component of the concrete finite tensor factor in a completion
above `w`, obtained from the canonical local tensor equivalence. -/
noncomputable def finitePlaceLocalTensorDecompositionComponent
    (w : HeightOneSpectrum (𝓞 K))
    (wL : AbsoluteValueExtension
      (NumberField.HeightOneSpectrum.adicAbv K w) L)
    (x : w.adicCompletion K ⊗[K] L) :
    wL.1.Completion := by
  let vK :=
    NumberField.HeightOneSpectrum.adicAbv K w
  let hvK : vK.IsNontrivial :=
    RayClass.adicAbv_isNontrivial w
  letI : ∀ u : AbsoluteValueExtension vK L,
      Algebra vK.Completion u.1.Completion :=
    fun u =>
      AbsoluteValue.completionAlgebra vK u.1 u.2
  exact
    completionTensorDecomposition_left
      (K := K) (L := L) vK hvK
      ((relativeFinitePlaceLocalTensorAlgEquiv
        (K := K) (L := L) w).symm x) wL

omit [NumberField L] in
/-- The local tensor-decomposition component of a pure tensor has the expected value. -/
@[simp]
theorem finitePlaceLocalTensorDecompositionComponent_tmul
    (w : HeightOneSpectrum (𝓞 K))
    (wL : AbsoluteValueExtension
      (NumberField.HeightOneSpectrum.adicAbv K w) L)
    (a : w.adicCompletion K) (b : L) :
    finitePlaceLocalTensorDecompositionComponent
        (K := K) (L := L) w wL (a ⊗ₜ[K] b) =
      AbsoluteValue.completionMap
          (NumberField.HeightOneSpectrum.adicAbv K w)
          wL.1 wL.2
          ((relativeFinitePlaceCompletionAlgEquiv w).symm a) *
        AbsoluteValue.toCompletion wL.1 b := by
  simp [finitePlaceLocalTensorDecompositionComponent,
    relativeFinitePlaceLocalTensorAlgEquiv,
    completionTensorDecomposition_left_tmul_apply,
    AbsoluteValue.toCompletionAlgHom]

end LocalTensorDecompositionIntegralComparison
end
end

section
-- module Solutions.OAIQ244_DUKE.AlgebraicNumberTheory_Adele_IntegralLocalFactor
attribute [-instance] _root_.OAI.PrimeDegreePackets.matrixSecondCountable
attribute [-simp] _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.OAI.PrimeDegreePackets.ThetaConstruction.schwartzCM_apply _root_.doubleCosetExtension_mk _root_.extendAbsoluteValueExtensionFromIntermediate_apply _root_.mem_finitePlaceDecompositionGroup_iff _root_.restrictAbsoluteValueExtensionToIntermediate_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

/-!
# Integral finite local factors of the relative idele group

For a finite place `w` of the base field, the canonical local tensor decomposition identifies
`K_w ⊗_K L` with the product of the completions of `L` above `w`.
This file packages each projection as an actual ring homomorphism and
defines the subgroup of tensor units whose value and inverse are integral
in every completion factor.  Thus the integrality predicate used for the
restricted product is closed under all group operations for structural,
rather than coordinate-dependent, reasons.
-/

open scoped NumberField TensorProduct
open NumberField IsDedekindDomain

noncomputable section


open AlgebraicNumberTheory.Valuations
open LocalClassFieldTheory

universe u v

variable
    {K : Type u} {L : Type v}
    [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L]

/-- The projection of the finite local tensor algebra to one completion
factor in the canonical local tensor decomposition, as a ring homomorphism. -/
noncomputable def finitePlaceLocalTensorDecompositionComponentRingHom
    (w : HeightOneSpectrum (𝓞 K))
    (wL : AbsoluteValueExtension
      (HeightOneSpectrum.adicAbv K w) L) :
    (w.adicCompletion K ⊗[K] L) →+* wL.1.Completion := by
  let vK := HeightOneSpectrum.adicAbv K w
  let hvK : vK.IsNontrivial :=
    RayClass.adicAbv_isNontrivial w
  letI : ∀ u : AbsoluteValueExtension vK L,
      Algebra vK.Completion u.1.Completion :=
    fun u =>
      AbsoluteValue.completionAlgebra vK u.1 u.2
  exact
    (Pi.evalRingHom
      (fun u : AbsoluteValueExtension vK L =>
        u.1.Completion) wL).comp
      ((completionTensorDecomposition_left
        (K := K) (L := L) vK hvK).toRingEquiv.toRingHom.comp
        (relativeFinitePlaceLocalTensorAlgEquiv
          (K := K) (L := L) w).symm.toRingEquiv.toRingHom)

omit [NumberField L] in
/-- The ring-homomorphism packaging evaluates to the original
relative-tensor component map. -/
@[simp]
theorem finitePlaceLocalTensorDecompositionComponentRingHom_apply
    (w : HeightOneSpectrum (𝓞 K))
    (wL : AbsoluteValueExtension
      (HeightOneSpectrum.adicAbv K w) L)
    (x : w.adicCompletion K ⊗[K] L) :
    finitePlaceLocalTensorDecompositionComponentRingHom
        (K := K) (L := L) w wL x =
      finitePlaceLocalTensorDecompositionComponent
        (K := K) (L := L) w wL x :=
  rfl

omit [NumberField L] in
/-- Every relative-tensor component map sends zero to zero. -/
@[simp]
theorem finitePlaceLocalTensorDecompositionComponent_zero
    (w : HeightOneSpectrum (𝓞 K))
    (wL : AbsoluteValueExtension
      (HeightOneSpectrum.adicAbv K w) L) :
    finitePlaceLocalTensorDecompositionComponent
        (K := K) (L := L) w wL 0 = 0 := by
  simpa only [finitePlaceLocalTensorDecompositionComponentRingHom_apply] using
    (finitePlaceLocalTensorDecompositionComponentRingHom
      (K := K) (L := L) w wL).map_zero

omit [NumberField L] in
/-- Relative-tensor component maps preserve addition. -/
@[simp]
theorem finitePlaceLocalTensorDecompositionComponent_add
    (w : HeightOneSpectrum (𝓞 K))
    (wL : AbsoluteValueExtension
      (HeightOneSpectrum.adicAbv K w) L)
    (x y : w.adicCompletion K ⊗[K] L) :
    finitePlaceLocalTensorDecompositionComponent
        (K := K) (L := L) w wL (x + y) =
      finitePlaceLocalTensorDecompositionComponent
          (K := K) (L := L) w wL x +
        finitePlaceLocalTensorDecompositionComponent
          (K := K) (L := L) w wL y := by
  simpa only [finitePlaceLocalTensorDecompositionComponentRingHom_apply] using
    (finitePlaceLocalTensorDecompositionComponentRingHom
      (K := K) (L := L) w wL).map_add x y

/-- The corresponding component homomorphism on units. -/
noncomputable def finitePlaceLocalTensorDecompositionUnitsComponent
    (w : HeightOneSpectrum (𝓞 K))
    (wL : AbsoluteValueExtension
      (HeightOneSpectrum.adicAbv K w) L) :
    (w.adicCompletion K ⊗[K] L)ˣ →*
      wL.1.Completionˣ :=
  Units.map
    (finitePlaceLocalTensorDecompositionComponentRingHom
      (K := K) (L := L) w wL)

/-- The canonical local tensor decomposition on the complete group of units of the finite local
tensor algebra. -/
noncomputable def finitePlaceLocalTensorDecompositionUnitsEquiv
    (w : HeightOneSpectrum (𝓞 K)) :
    (w.adicCompletion K ⊗[K] L)ˣ ≃*
      ∀ wL : AbsoluteValueExtension
          (HeightOneSpectrum.adicAbv K w) L,
        wL.1.Completionˣ := by
  let vK := HeightOneSpectrum.adicAbv K w
  let hvK : vK.IsNontrivial :=
    RayClass.adicAbv_isNontrivial w
  letI : ∀ u : AbsoluteValueExtension vK L,
      Algebra vK.Completion u.1.Completion :=
    fun u =>
      AbsoluteValue.completionAlgebra vK u.1 u.2
  exact
    (Units.mapEquiv
      (((relativeFinitePlaceLocalTensorAlgEquiv
            (K := K) (L := L) w).symm.toRingEquiv.trans
          (completionTensorDecomposition_left
            (K := K) (L := L) vK hvK).toRingEquiv).toMulEquiv)).trans
      MulEquiv.piUnits

omit [NumberField L] in
/-- The product equivalence on units evaluates componentwise through the
corresponding unit homomorphism. -/
@[simp]
theorem finitePlaceLocalTensorDecompositionUnitsEquiv_apply
    (w : HeightOneSpectrum (𝓞 K))
    (x : (w.adicCompletion K ⊗[K] L)ˣ)
    (wL : AbsoluteValueExtension
      (HeightOneSpectrum.adicAbv K w) L) :
    finitePlaceLocalTensorDecompositionUnitsEquiv
        (K := K) (L := L) w x wL =
      finitePlaceLocalTensorDecompositionUnitsComponent
        (K := K) (L := L) w wL x :=
  rfl

omit [NumberField L] in
/-- Coercing a unit component to the completion agrees with applying the
underlying tensor component map. -/
@[simp]
theorem finitePlaceLocalTensorDecompositionUnitsComponent_coe
    (w : HeightOneSpectrum (𝓞 K))
    (wL : AbsoluteValueExtension
      (HeightOneSpectrum.adicAbv K w) L)
    (x : (w.adicCompletion K ⊗[K] L)ˣ) :
    ((finitePlaceLocalTensorDecompositionUnitsComponent
        (K := K) (L := L) w wL x :
          wL.1.Completionˣ) :
        wL.1.Completion) =
      finitePlaceLocalTensorDecompositionComponent
        (K := K) (L := L) w wL
        (x : w.adicCompletion K ⊗[K] L) :=
  rfl

/-- The product of the actual valuation-ring unit groups in all
completion factors above a finite base place. -/
abbrev FinitePlaceLocalTensorDecompositionIntegralUnitProduct
    (w : HeightOneSpectrum (𝓞 K)) :=
  Subgroup.pi Set.univ fun
      wL : AbsoluteValueExtension
        (HeightOneSpectrum.adicAbv K w) L =>
    (absoluteValueCompletionIntegers wL.1
      (absoluteValueExtension_isNonarchimedean
        (HeightOneSpectrum.adicAbv K w)
        (HeightOneSpectrum.isNonarchimedean_adicAbv K w)
        wL)).units

/-- A product subgroup is the product of its component subgroup types. -/
@[implicit_reducible]
noncomputable def
    finitePlaceLocalTensorDecompositionIntegralUnitProductEquivPi
    (w : HeightOneSpectrum (𝓞 K)) :
    FinitePlaceLocalTensorDecompositionIntegralUnitProduct
        (K := K) (L := L) w ≃*
      ∀ wL : AbsoluteValueExtension
          (HeightOneSpectrum.adicAbv K w) L,
        (absoluteValueCompletionIntegers wL.1
          (absoluteValueExtension_isNonarchimedean
            (HeightOneSpectrum.adicAbv K w)
            (HeightOneSpectrum.isNonarchimedean_adicAbv K w)
            wL)).units where
  toFun x wL :=
    ⟨x.1 wL, x.2 wL (Set.mem_univ wL)⟩
  invFun x :=
    ⟨fun wL => x wL, by
      intro wL hwL
      exact (x wL).2⟩
  left_inv x := by
    apply Subtype.ext
    rfl
  right_inv x := by
    funext wL
    apply Subtype.ext
    rfl
  map_mul' x y := by
    funext wL
    apply Subtype.ext
    rfl
end
end

section
-- module Solutions.OAIQ244_DUKE.AlgebraicNumberTheory_Completion_LocalizedValuation
attribute [-instance] _root_.OAI.PrimeDegreePackets.diagonalLogAction _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.chosenFinitePlaceBaseValuationCompatible
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

/-!
# Valuation rings of algebraic localizations

This file equips nonarchimedean absolute-value completions and their algebraic
localizations with the norm-induced valuation structures. It identifies the
localized valuation ring with the integral closure of the base valuation ring.
-/

open scoped NumberField TensorProduct ValuativeRel NNReal
open NumberField IsDedekindDomain

noncomputable section

open AlgebraicNumberTheory.Valuations
open HilbertRamification
open LocalClassFieldTheory
open LocalFieldTheory

variable
    {K : Type} {L : Type}
    [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]

section LocalValuation

variable (vK : AbsoluteValue K ℝ) (hvK : vK.IsNontrivial)
    (w : AbsoluteValueExtension vK L)

omit [NumberField K] [NumberField L] [FiniteDimensional K L]
    [IsGalois K L] in
/-- A chosen localization above a nonarchimedean place inherits an
ultrametric distance. -/
theorem localizedCompletionIsUltrametricDist
    (hvKna : IsNonarchimedean (vK : K → ℝ)) :
    IsUltrametricDist (LocalizedCompletion vK w) := by
  let hw : IsNonarchimedean (w.1 : L → ℝ) :=
    absoluteValueExtension_isNonarchimedean
      vK hvKna w
  let : IsUltrametricDist w.1.Completion :=
    IsUltrametricDist.isUltrametricDist_of_isNonarchimedean_norm
      (AbsoluteValue.completionAbsoluteValue_isNonarchimedean
        w.1 hw)
  infer_instance

/-- The norm-induced valued-field structure on the chosen algebraic
localization. -/
@[reducible]
noncomputable def localizedCompletionFinitePlaceValued
    (hvKna : IsNonarchimedean (vK : K → ℝ)) :
    Valued (LocalizedCompletion vK w) ℝ≥0 :=
  letI : IsUltrametricDist (LocalizedCompletion vK w) :=
    localizedCompletionIsUltrametricDist vK w hvKna
  NormedField.toValued

/-- The valuation relation induced by the norm valuation on the chosen
algebraic localization. -/
@[reducible]
noncomputable def localizedCompletionFinitePlaceValuativeRel
    (hvKna : IsNonarchimedean (vK : K → ℝ)) :
    ValuativeRel (LocalizedCompletion vK w) := by
  letI : Valued (LocalizedCompletion vK w) ℝ≥0 :=
    localizedCompletionFinitePlaceValued vK w hvKna
  exact ValuativeRel.ofValuation
    (Valued.v : Valuation (LocalizedCompletion vK w) ℝ≥0)

omit [NumberField K] [NumberField L] [FiniteDimensional K L]
    [IsGalois K L] in
/-- Membership in the valuation ring of a chosen algebraic localization is
equivalent to the usual norm bound by one, for the canonical norm-induced
valuation used in this file. -/
theorem localizedCompletion_mem_integers_iff_norm_le_one
    (hvKna : IsNonarchimedean (vK : K → ℝ))
    (x : LocalizedCompletion vK w) :
    letI : Valued (LocalizedCompletion vK w) ℝ≥0 :=
      localizedCompletionFinitePlaceValued vK w hvKna
    letI : ValuativeRel (LocalizedCompletion vK w) :=
      localizedCompletionFinitePlaceValuativeRel vK w hvKna
    x ∈ 𝒪[LocalizedCompletion vK w] ↔ ‖x‖ ≤ 1 := by
  let : Valued (LocalizedCompletion vK w) ℝ≥0 :=
    localizedCompletionFinitePlaceValued vK w hvKna
  let ν : Valuation (LocalizedCompletion vK w) ℝ≥0 := Valued.v
  let : ValuativeRel (LocalizedCompletion vK w) :=
    localizedCompletionFinitePlaceValuativeRel vK w hvKna
  rw [Valuation.mem_integer_iff,
    ← map_one (ValuativeRel.valuation (LocalizedCompletion vK w)),
    ← Valuation.Compatible.vle_iff_le
      (v := ValuativeRel.valuation (LocalizedCompletion vK w))]
  change ν x ≤ ν 1 ↔ _
  simp only [map_one]
  change ‖x‖₊ ≤ 1 ↔ ‖x‖ ≤ 1
  exact NNReal.coe_le_coe

omit [NumberField K] [NumberField L] [IsGalois K L] in
/-- The norm-defined integer ring of the chosen localization is the
integral closure of the norm-defined integer ring of the completed base.
This is the concrete Henselian source of the local integer-ring action. -/
theorem localizedCompletion_integerRing_eq_integralClosure
    (hvK : vK.IsNontrivial)
    (hvKna : IsNonarchimedean (vK : K → ℝ)) :
    letI hK := AbsoluteValue.extensionCompletionAlgebra (K := K) w.1
    letI : SMul K w.1.Completion := hK.toSMul
    letI := AbsoluteValue.completionAlgebra vK w.1 w.2
    letI : Valued vK.Completion ℝ≥0 :=
      finitePlaceCompletionValued vK hvKna
    letI : ValuativeRel vK.Completion :=
      finitePlaceCompletionValuativeRel vK hvKna
    letI : Valued (LocalizedCompletion vK w) ℝ≥0 :=
      localizedCompletionFinitePlaceValued vK w hvKna
    letI : ValuativeRel (LocalizedCompletion vK w) :=
      localizedCompletionFinitePlaceValuativeRel vK w hvKna
    (ValuativeRel.valuation
        (LocalizedCompletion vK w)).integer =
      (integralClosure
        (ValuativeRel.valuation vK.Completion).integer
        (LocalizedCompletion vK w)).toSubring := by
  let hK := AbsoluteValue.extensionCompletionAlgebra (K := K) w.1
  let : SMul K w.1.Completion := hK.toSMul
  let := AbsoluteValue.completionAlgebra vK w.1 w.2
  let : Valued vK.Completion ℝ≥0 :=
    finitePlaceCompletionValued vK hvKna
  let : ValuativeRel vK.Completion :=
    finitePlaceCompletionValuativeRel vK hvKna
  let : Valued (LocalizedCompletion vK w) ℝ≥0 :=
    localizedCompletionFinitePlaceValued vK w hvKna
  let : ValuativeRel (LocalizedCompletion vK w) :=
    localizedCompletionFinitePlaceValuativeRel vK w hvKna
  let aC := AbsoluteValue.completionAbsoluteValue vK
  let bE :=
    AbsoluteValue.algebraicLocalizationAbsoluteValue
      vK w.1 w.2
  let haC :
      LubinTate.Valuations.NonarchimedeanAbsoluteValue aC :=
    (AbsoluteValue.isNonarchimedean_iff_bounded_nat aC).1
      (AbsoluteValue.completionAbsoluteValue_isNonarchimedean
        vK hvKna)
  let hbE :
      LubinTate.Valuations.NonarchimedeanAbsoluteValue bE :=
    (AbsoluteValue.isNonarchimedean_iff_bounded_nat bE).1
      (absoluteValueExtension_isNonarchimedean
        aC
        (AbsoluteValue.completionAbsoluteValue_isNonarchimedean
          vK hvKna)
        ⟨bE,
          AbsoluteValue.algebraicLocalizationAbsoluteValue_extends
            vK w.1 w.2⟩)
  let va := absoluteValueExponentialValuation aC haC
  let vb := absoluteValueExponentialValuation bE hbE
  let : Module.Finite vK.Completion
      (LocalizedCompletion vK w) :=
    localizedCompletionModuleFinite vK hvK w
  let : Algebra.IsAlgebraic vK.Completion
      (LocalizedCompletion vK w) :=
    Algebra.IsAlgebraic.of_finite
      vK.Completion (LocalizedCompletion vK w)
  have hVaAbs :
      LubinTate.Valuations.exponentialValuationSubringAsValuationSubring va =
        absoluteValueValuationSubring aC haC :=
    associatedAbsoluteValue_valuationSubring_eq
      va (Real.exp 1) aC haC
        (absoluteValueExponentialValuation_associated aC haC)
  have hVbAbs :
      LubinTate.Valuations.exponentialValuationSubringAsValuationSubring vb =
        absoluteValueValuationSubring bE hbE :=
    associatedAbsoluteValue_valuationSubring_eq
      vb (Real.exp 1) bE hbE
        (absoluteValueExponentialValuation_associated bE hbE)
  have hVa :
      (LubinTate.Valuations.exponentialValuationSubringAsValuationSubring
        va).toSubring =
        (ValuativeRel.valuation vK.Completion).integer := by
    rw [hVaAbs]
    ext x
    change
      x ∈ absoluteValueValuationSubring aC haC ↔
        x ∈ (ValuativeRel.valuation vK.Completion).integer
    rw [mem_absoluteValueValuationSubring_iff,
      finitePlaceCompletion_mem_integers_iff_norm_le_one]
    rfl
  have hVb :
      (LubinTate.Valuations.exponentialValuationSubringAsValuationSubring
        vb).toSubring =
        (ValuativeRel.valuation
          (LocalizedCompletion vK w)).integer := by
    rw [hVbAbs]
    ext x
    change
      x ∈ absoluteValueValuationSubring bE hbE ↔
        x ∈ (ValuativeRel.valuation
          (LocalizedCompletion vK w)).integer
    rw [mem_absoluteValueValuationSubring_iff,
      localizedCompletion_mem_integers_iff_norm_le_one]
    rfl
  have hhensAbs :
      ValuationTheory.DiscreteValuationField.HenselianValuationByFactorization
        (absoluteValueValuationSubring aC haC).valuation :=
    henselianValuation_of_complete aC
      ((absoluteValueCompleteness_completeSpace_withAbs_iff_complete aC).1
        (AbsoluteValue.completionAbsoluteValue_complete vK))
      haC
  have hhens :
      ValuationTheory.DiscreteValuationField.HenselianValuationByFactorization
        (LubinTate.Valuations.exponentialValuationSubringAsValuationSubring
          va).valuation := by
    rw [hVaAbs]
    exact hhensAbs
  have hExt : ∀ x : vK.Completion,
      vb (algebraMap vK.Completion
        (LocalizedCompletion vK w) x) = va x :=
    absoluteValueExponentialValuation_extends
      aC bE haC hbE
      (AbsoluteValue.algebraicLocalizationAbsoluteValue_extends
        vK w.1 w.2)
  let W :=
    LubinTate.Valuations.exponentialValuationSubringAsValuationSubring va
  let : Algebra W (LocalizedCompletion vK w) := inferInstance
  have hclosure :=
    exponentialValuationSubring_eq_integralClosure_of_henselian
      va vb hExt hhens
  let O := (ValuativeRel.valuation vK.Completion).integer
  have hWO : W.toSubring = O := by
    simpa only [W, O] using hVa
  let eWO : W ≃+* O :=
    { toFun := fun x =>
        ⟨x, by
          rw [← hWO]
          exact x.property⟩
      invFun := fun x =>
        ⟨x, by
          change (x : vK.Completion) ∈ W.toSubring
          rw [hWO]
          exact x.property⟩
      left_inv := fun x ↦ by
        apply Subtype.ext
        rfl
      right_inv := fun x ↦ by
        apply Subtype.ext
        rfl
      map_mul' := fun x y ↦ by
        apply Subtype.ext
        rfl
      map_add' := fun x y ↦ by
        apply Subtype.ext
        rfl }
  have heWO :
      (algebraMap O (LocalizedCompletion vK w)).comp
          eWO.toRingHom =
        algebraMap W (LocalizedCompletion vK w) := by
    ext x
    rw [RingHom.comp_apply,
      IsScalarTower.algebraMap_apply O vK.Completion,
      IsScalarTower.algebraMap_apply W vK.Completion]
    rfl
  ext x
  change
    x ∈ (ValuativeRel.valuation
      (LocalizedCompletion vK w)).integer ↔
      IsIntegral O x
  constructor
  · intro hx
    have hxv :
        x ∈
          (LubinTate.Valuations.exponentialValuationSubringAsValuationSubring
            vb).toSubring := by
      rw [hVb]
      exact hx
    rw [hclosure] at hxv
    have hxW : IsIntegral W x := hxv
    exact (eWO.isIntegral_iff heWO x).1 hxW
  · intro hx
    have hxW : IsIntegral W x :=
      (eWO.isIntegral_iff heWO x).2 hx
    have hxv :
        x ∈
          (LubinTate.Valuations.exponentialValuationSubringAsValuationSubring
            vb).toSubring := by
      rw [hclosure]
      exact hxW
    rw [← hVb]
    exact hxv

omit [NumberField K] [NumberField L] [FiniteDimensional K L]
    [IsGalois K L] in
/-- The intrinsic norm valuations on the completed base and on the
chosen localization form an extension pair. -/
theorem localizedCompletionValuationHasExtension
    (hvKna : IsNonarchimedean (vK : K → ℝ)) :
    letI hK := AbsoluteValue.extensionCompletionAlgebra (K := K) w.1
    letI : SMul K w.1.Completion := hK.toSMul
    letI := AbsoluteValue.completionAlgebra vK w.1 w.2
    letI : Valued vK.Completion ℝ≥0 :=
      finitePlaceCompletionValued vK hvKna
    letI : ValuativeRel vK.Completion :=
      finitePlaceCompletionValuativeRel vK hvKna
    letI : Valued (LocalizedCompletion vK w) ℝ≥0 :=
      localizedCompletionFinitePlaceValued vK w hvKna
    letI : ValuativeRel (LocalizedCompletion vK w) :=
      localizedCompletionFinitePlaceValuativeRel vK w hvKna
    Valuation.HasExtension
      (ValuativeRel.valuation vK.Completion)
      (ValuativeRel.valuation (LocalizedCompletion vK w)) := by
  let hK := AbsoluteValue.extensionCompletionAlgebra (K := K) w.1
  let : SMul K w.1.Completion := hK.toSMul
  let := AbsoluteValue.completionAlgebra vK w.1 w.2
  let : Valued vK.Completion ℝ≥0 :=
    finitePlaceCompletionValued vK hvKna
  let : ValuativeRel vK.Completion :=
    finitePlaceCompletionValuativeRel vK hvKna
  let : Valued (LocalizedCompletion vK w) ℝ≥0 :=
    localizedCompletionFinitePlaceValued vK w hvKna
  let : ValuativeRel (LocalizedCompletion vK w) :=
    localizedCompletionFinitePlaceValuativeRel vK w hvKna
  apply Valuation.HasExtension.ofComapInteger
  ext x
  rw [Subring.mem_comap,
    localizedCompletion_mem_integers_iff_norm_le_one,
    finitePlaceCompletion_mem_integers_iff_norm_le_one]
  have h :=
    AbsoluteValue.algebraicLocalizationAbsoluteValue_extends
      vK w.1 w.2 x
  change
    AbsoluteValue.algebraicLocalizationAbsoluteValue
          vK w.1 w.2
          (algebraMap vK.Completion
            (LocalizedCompletion vK w) x) ≤ 1 ↔
      AbsoluteValue.completionAbsoluteValue vK x ≤ 1
  rw [h]

omit [NumberField K] [NumberField L] [IsGalois K L] in
/-- The integral-closure certificate with the canonical algebra structure
on valuation rings supplied by `Valuation.HasExtension`. -/
theorem localizedCompletionIsIntegralClosureWithExtension
    (hvK : vK.IsNontrivial)
    (hvKna : IsNonarchimedean (vK : K → ℝ)) :
    letI hK := AbsoluteValue.extensionCompletionAlgebra (K := K) w.1
    letI : SMul K w.1.Completion := hK.toSMul
    letI := AbsoluteValue.completionAlgebra vK w.1 w.2
    letI : Valued vK.Completion ℝ≥0 :=
      finitePlaceCompletionValued vK hvKna
    letI : ValuativeRel vK.Completion :=
      finitePlaceCompletionValuativeRel vK hvKna
    letI : Valued (LocalizedCompletion vK w) ℝ≥0 :=
      localizedCompletionFinitePlaceValued vK w hvKna
    letI : ValuativeRel (LocalizedCompletion vK w) :=
      localizedCompletionFinitePlaceValuativeRel vK w hvKna
    letI : Algebra 𝒪[vK.Completion] (LocalizedCompletion vK w) :=
      Algebra.ofSubsemiring 𝒪[vK.Completion]
    letI := localizedCompletionValuationHasExtension vK w hvKna
    IsIntegralClosure
      𝒪[LocalizedCompletion vK w]
      𝒪[vK.Completion]
      (LocalizedCompletion vK w) := by
  let hK := AbsoluteValue.extensionCompletionAlgebra (K := K) w.1
  let : SMul K w.1.Completion := hK.toSMul
  let := AbsoluteValue.completionAlgebra vK w.1 w.2
  let : Valued vK.Completion ℝ≥0 :=
    finitePlaceCompletionValued vK hvKna
  let : ValuativeRel vK.Completion :=
    finitePlaceCompletionValuativeRel vK hvKna
  let : Valued (LocalizedCompletion vK w) ℝ≥0 :=
    localizedCompletionFinitePlaceValued vK w hvKna
  let : ValuativeRel (LocalizedCompletion vK w) :=
    localizedCompletionFinitePlaceValuativeRel vK w hvKna
  let : Algebra 𝒪[vK.Completion] (LocalizedCompletion vK w) :=
    Algebra.ofSubsemiring 𝒪[vK.Completion]
  let := localizedCompletionValuationHasExtension vK w hvKna
  let h :=
    localizedCompletion_integerRing_eq_integralClosure
      vK w hvK hvKna
  refine
    { algebraMap_injective :=
        (ValuativeRel.valuation
          (LocalizedCompletion vK w)).integer.subtype_injective
      isIntegral_iff := ?_ }
  intro x
  constructor
  · intro hx
    have hxO : x ∈ 𝒪[LocalizedCompletion vK w] := by
      rw [h]
      exact hx
    exact ⟨⟨x, hxO⟩, rfl⟩
  · rintro ⟨y, rfl⟩
    have hyO :
        algebraMap 𝒪[LocalizedCompletion vK w]
            (LocalizedCompletion vK w) y ∈
          𝒪[LocalizedCompletion vK w] := by
      change (y : LocalizedCompletion vK w) ∈
        𝒪[LocalizedCompletion vK w]
      exact y.property
    exact (SetLike.ext_iff.mp h _).1 hyO


end LocalValuation
end
end

section
-- module Solutions.OAIQ244_DUKE.AlgebraicNumberTheory_Completion_ChosenLocalization
attribute [-instance] _root_.OAI.PrimeDegreePackets.diagonalLogAction _root_.OAI.PrimeDegreePackets.matrixSecondCountable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

/-!
# The chosen localization at a finite place

This file equips the actual chosen localization of a finite number-field
extension with its canonical valued local-field structures. It also defines
unramifiedness for that actual completed extension.
-/

open scoped NumberField Classical ValuativeRel NNReal
open NumberField IsDedekindDomain

noncomputable section

open AlgebraicNumberTheory.Valuations
open LocalFieldTheory
open LocalFieldTheory.IsNonarchimedeanLocalField

variable
    {K L : Type}
    [Field K] [NumberField K]
    [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]

noncomputable instance chosenFinitePlaceCompletionAlgebra
    (w₀ : HeightOneSpectrum (𝓞 K)) :
    Algebra
      (ChosenFinitePlaceBaseCompletion (K := K) w₀)
      (chosenFinitePlaceExtension (L := L) w₀).1.Completion :=
  AbsoluteValue.completionAlgebra
    (HeightOneSpectrum.adicAbv K w₀)
    (chosenFinitePlaceExtension (L := L) w₀).1
    (chosenFinitePlaceExtension (L := L) w₀).2

noncomputable instance chosenFinitePlaceLocalizedValued
    (w₀ : HeightOneSpectrum (𝓞 K)) :
    Valued
      (ChosenFinitePlaceLocalizedCompletion
        (K := K) (L := L) w₀) ℝ≥0 :=
  localizedCompletionFinitePlaceValued
    (HeightOneSpectrum.adicAbv K w₀)
    (chosenFinitePlaceExtension (L := L) w₀)
    (HeightOneSpectrum.isNonarchimedean_adicAbv K w₀)

noncomputable instance chosenFinitePlaceLocalizedValuativeRel
    (w₀ : HeightOneSpectrum (𝓞 K)) :
    ValuativeRel
      (ChosenFinitePlaceLocalizedCompletion
        (K := K) (L := L) w₀) :=
  localizedCompletionFinitePlaceValuativeRel
    (HeightOneSpectrum.adicAbv K w₀)
    (chosenFinitePlaceExtension (L := L) w₀)
    (HeightOneSpectrum.isNonarchimedean_adicAbv K w₀)

noncomputable instance
    chosenFinitePlaceLocalizedValuationHasExtension
    (w₀ : HeightOneSpectrum (𝓞 K)) :
    Valuation.HasExtension
      (ValuativeRel.valuation
        (ChosenFinitePlaceBaseCompletion (K := K) w₀))
      (ValuativeRel.valuation
        (ChosenFinitePlaceLocalizedCompletion
          (K := K) (L := L) w₀)) :=
  localizedCompletionValuationHasExtension
    (HeightOneSpectrum.adicAbv K w₀)
    (chosenFinitePlaceExtension (L := L) w₀)
    (HeightOneSpectrum.isNonarchimedean_adicAbv K w₀)

noncomputable instance chosenFinitePlaceLocalizedIntegerAlgebra
    (w₀ : HeightOneSpectrum (𝓞 K)) :
    Algebra
      𝒪[ChosenFinitePlaceBaseCompletion (K := K) w₀]
      (ChosenFinitePlaceLocalizedCompletion
        (K := K) (L := L) w₀) :=
  Algebra.ofSubsemiring
    𝒪[ChosenFinitePlaceBaseCompletion (K := K) w₀]

noncomputable instance chosenFinitePlaceLocalizedIsIntegralClosure
    (w₀ : HeightOneSpectrum (𝓞 K)) :
    IsIntegralClosure
      𝒪[ChosenFinitePlaceLocalizedCompletion
        (K := K) (L := L) w₀]
      𝒪[ChosenFinitePlaceBaseCompletion (K := K) w₀]
      (ChosenFinitePlaceLocalizedCompletion
        (K := K) (L := L) w₀) :=
  localizedCompletionIsIntegralClosureWithExtension
    (HeightOneSpectrum.adicAbv K w₀)
    (chosenFinitePlaceExtension (L := L) w₀)
    (RayClass.adicAbv_isNontrivial w₀)
    (HeightOneSpectrum.isNonarchimedean_adicAbv K w₀)

noncomputable instance chosenFinitePlaceCompletionFiniteDimensional
    (w₀ : HeightOneSpectrum (𝓞 K)) :
    FiniteDimensional
      (ChosenFinitePlaceBaseCompletion (K := K) w₀)
      (chosenFinitePlaceExtension (L := L) w₀).1.Completion :=
  completionModuleFinite
    (HeightOneSpectrum.adicAbv K w₀)
    (RayClass.adicAbv_isNontrivial w₀)
    (chosenFinitePlaceExtension (L := L) w₀)

noncomputable instance chosenFinitePlaceCompletionContinuousSMul
    (w₀ : HeightOneSpectrum (𝓞 K)) :
    ContinuousSMul
      (ChosenFinitePlaceBaseCompletion (K := K) w₀)
      (chosenFinitePlaceExtension (L := L) w₀).1.Completion :=
  continuousSMul_of_algebraMap _ _
    (AbsoluteValue.completionMap_isometry
      (HeightOneSpectrum.adicAbv K w₀)
      (chosenFinitePlaceExtension (L := L) w₀).1
      (chosenFinitePlaceExtension (L := L) w₀).2).continuous

noncomputable instance chosenFinitePlaceCompletionLocallyCompactSpace
    (w₀ : HeightOneSpectrum (𝓞 K)) :
    LocallyCompactSpace
      (chosenFinitePlaceExtension (L := L) w₀).1.Completion :=
  LocallyCompactSpace.of_finiteDimensional_of_complete
    (ChosenFinitePlaceBaseCompletion (K := K) w₀)
    (chosenFinitePlaceExtension (L := L) w₀).1.Completion

noncomputable instance chosenFinitePlaceLocalizedFiniteDimensional
    (w₀ : HeightOneSpectrum (𝓞 K)) :
    FiniteDimensional
      (ChosenFinitePlaceBaseCompletion (K := K) w₀)
      (ChosenFinitePlaceLocalizedCompletion
        (K := K) (L := L) w₀) :=
  AlgebraicNumberTheory.Valuations.localizedCompletionModuleFinite
    (HeightOneSpectrum.adicAbv K w₀)
    (RayClass.adicAbv_isNontrivial w₀)
    (chosenFinitePlaceExtension (L := L) w₀)

noncomputable instance chosenFinitePlaceLocalizedIsGalois
    (w₀ : HeightOneSpectrum (𝓞 K)) :
    IsGalois
      (ChosenFinitePlaceBaseCompletion (K := K) w₀)
      (ChosenFinitePlaceLocalizedCompletion
        (K := K) (L := L) w₀) :=
  HilbertRamification.algebraicLocalization_isGalois
    (HeightOneSpectrum.adicAbv K w₀)
    (chosenFinitePlaceExtension (L := L) w₀)

noncomputable instance
    chosenFinitePlaceLocalizedLocallyCompactSpace
    (w₀ : HeightOneSpectrum (𝓞 K)) :
    LocallyCompactSpace
      (ChosenFinitePlaceLocalizedCompletion
        (K := K) (L := L) w₀) := by
  let e :
      ChosenFinitePlaceLocalizedCompletion
          (K := K) (L := L) w₀ ≃ᵢ
        (chosenFinitePlaceExtension (L := L) w₀).1.Completion :=
    { toEquiv :=
        (AlgebraicNumberTheory.Valuations.localizedCompletionEquivCompletion
          (HeightOneSpectrum.adicAbv K w₀)
          (RayClass.adicAbv_isNontrivial w₀)
          (chosenFinitePlaceExtension (L := L) w₀)).toEquiv
      isometry_toFun := Isometry.of_dist_eq fun _ _ => rfl }
  exact (e.toHomeomorph.locallyCompactSpace_iff).2 inferInstance

noncomputable instance chosenFinitePlaceLocalizedValuationCompatible
    (w₀ : HeightOneSpectrum (𝓞 K)) :
    (Valued.v :
      Valuation
        (ChosenFinitePlaceLocalizedCompletion
          (K := K) (L := L) w₀)
        ℝ≥0).Compatible :=
  Valuation.Compatible.ofValuation _

noncomputable instance
    chosenFinitePlaceLocalizedValuationIsNontrivial
    (w₀ : HeightOneSpectrum (𝓞 K)) :
    (ValuativeRel.valuation
      (ChosenFinitePlaceLocalizedCompletion
        (K := K) (L := L) w₀)).IsNontrivial :=
  Valuation.IsNontrivial.of_hasExtension
    (ValuativeRel.valuation
      (ChosenFinitePlaceBaseCompletion (K := K) w₀))
    (ValuativeRel.valuation
      (ChosenFinitePlaceLocalizedCompletion
        (K := K) (L := L) w₀))

noncomputable instance
    chosenFinitePlaceLocalizedValuativeRelIsNontrivial
    (w₀ : HeightOneSpectrum (𝓞 K)) :
    ValuativeRel.IsNontrivial
      (ChosenFinitePlaceLocalizedCompletion
        (K := K) (L := L) w₀) :=
  (ValuativeRel.isNontrivial_iff_isNontrivial
    (ValuativeRel.valuation
      (ChosenFinitePlaceLocalizedCompletion
        (K := K) (L := L) w₀))).2 inferInstance

noncomputable instance chosenFinitePlaceLocalizedIsValuativeTopology
    (w₀ : HeightOneSpectrum (𝓞 K)) :
    IsValuativeTopology
      (ChosenFinitePlaceLocalizedCompletion
        (K := K) (L := L) w₀) :=
  isValuativeTopology_of_valued_ofValuation
    (ChosenFinitePlaceLocalizedCompletion
      (K := K) (L := L) w₀) ℝ≥0

noncomputable instance
    chosenFinitePlaceLocalizedIsNonarchimedeanLocalField
    (w₀ : HeightOneSpectrum (𝓞 K)) :
    IsNonarchimedeanLocalField
      (ChosenFinitePlaceLocalizedCompletion
        (K := K) (L := L) w₀) :=
  { toIsValuativeTopology := inferInstance
    toLocallyCompactSpace := inferInstance
    toIsNontrivial := inferInstance }

noncomputable instance chosenFinitePlaceLocalizedIntegerModuleFinite
    (w₀ : HeightOneSpectrum (𝓞 K)) :
    Module.Finite
      𝒪[ChosenFinitePlaceBaseCompletion (K := K) w₀]
      𝒪[ChosenFinitePlaceLocalizedCompletion
        (K := K) (L := L) w₀] := by
  let : Algebra.IsSeparable
      (ChosenFinitePlaceBaseCompletion (K := K) w₀)
      (ChosenFinitePlaceLocalizedCompletion (K := K) (L := L) w₀) :=
    (chosenFinitePlaceLocalizedIsGalois (K := K) (L := L) w₀).to_isSeparable
  exact integerRing_moduleFinite_of_isIntegralClosure
    (ChosenFinitePlaceBaseCompletion (K := K) w₀)
    (ChosenFinitePlaceLocalizedCompletion
      (K := K) (L := L) w₀)

/-- The chosen extension of the completed field is unramified, expressed
using the intrinsic valuation on the algebraic localization.  The canonical local-field instances for the chosen completion are exported
from this module, so clients only supply the mathematical unramifiedness
hypothesis. -/
noncomputable def ChosenFinitePlaceIsUnramified
    (w₀ : HeightOneSpectrum (𝓞 K)) : Prop :=
  IsNonarchimedeanLocalField.IsUnramifiedValuedExtension
    (ChosenFinitePlaceBaseCompletion (K := K) w₀)
    (ChosenFinitePlaceLocalizedCompletion
      (K := K) (L := L) w₀)
end
end

section
-- module Solutions.OAIQ244_DUKE.AlgebraicNumberTheory_Idele_Cohomology_Decomposition
attribute [-instance] _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.CyclicCohomology.binaryCoefficientFamilyCommGroup _root_.adicCompletionProperSpace _root_.chosenFinitePlaceCompletionAlgebra _root_.chosenFinitePlaceCompletionContinuousSMul _root_.chosenFinitePlaceCompletionFiniteDimensional _root_.chosenFinitePlaceCompletionLocallyCompactSpace _root_.chosenFinitePlaceLocalizedFiniteDimensional _root_.chosenFinitePlaceLocalizedIntegerAlgebra _root_.chosenFinitePlaceLocalizedIntegerModuleFinite _root_.chosenFinitePlaceLocalizedIsGalois _root_.chosenFinitePlaceLocalizedIsIntegralClosure _root_.chosenFinitePlaceLocalizedIsNonarchimedeanLocalField _root_.chosenFinitePlaceLocalizedIsValuativeTopology _root_.chosenFinitePlaceLocalizedLocallyCompactSpace _root_.chosenFinitePlaceLocalizedValuationCompatible _root_.chosenFinitePlaceLocalizedValuationHasExtension _root_.chosenFinitePlaceLocalizedValuationIsNontrivial _root_.chosenFinitePlaceLocalizedValuativeRel _root_.chosenFinitePlaceLocalizedValuativeRelIsNontrivial _root_.chosenFinitePlaceLocalizedValued
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

/-!
# Finite-support decompositions of actual ideles

For a finite set `S` of finite places, this file identifies the actual
subgroup `I_K^S` with the product of all archimedean local groups, the
full multiplicative groups at places in `S`, and the local unit groups
away from `S`.  The construction is componentwise and uses the genuine
restricted-product membership condition.

For a finite family of base places in a Galois extension, it also
assembles the local tensor-algebra decomposition and proves its
equivariance for the full Galois action.  Finally, the concrete
unramified local class-field theorem is transported through Shapiro to
show that every unramified induced integer-unit block has trivial
`H⁰` and `H⁻¹`.
-/

open scoped NumberField RestrictedProduct ValuativeRel
open NumberField IsDedekindDomain

noncomputable section

open LocalClassFieldTheory

open AlgebraicNumberTheory.Valuations
open HilbertRamification
open LocalClassFieldTheory
open LocalFieldTheory
open CyclicCohomology.ProfiniteCohomology.Herbrand
open CyclicCohomology

universe u

variable {F : Type u} [Field F] [NumberField F]

section FiniteTensorFamily

universe uK uL uι

variable {K : Type uK} {L : Type uL}
    [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]

/-- The componentwise induced-module action on a local block family. -/
@[reducible]
noncomputable def localBlockFamilyAction {ι : Type uι}
    (d : ι → LocalPlaceDatum K L) :
    MulDistribMulAction (L ≃ₐ[K] L)
      (LocalBlockFamily d) := by
  letI : ∀ i, MulDistribMulAction
      (absoluteValueDecompositionGroup K (d i).extension.1)
      (LocalizedCompletion
        (d i).base (d i).extension)ˣ :=
    fun i ↦ decompositionGroupLocalUnitsAction
      (d i).base (d i).base_isNontrivial
      (d i).extension
  letI : ∀ i, MulDistribMulAction (L ≃ₐ[K] L)
      (LocalPlaceBlock
        (d i).base (d i).base_isNontrivial
        (d i).extension) :=
    fun i ↦ inducedMulDistribMulAction
      (absoluteValueDecompositionGroup K (d i).extension.1)
  exact piMulDistribMulAction (L ≃ₐ[K] L)
    (fun i ↦ LocalPlaceBlock
      (d i).base (d i).base_isNontrivial
      (d i).extension)

end FiniteTensorFamily
end
end

section
-- module Solutions.OAIQ244_DUKE.AlgebraicNumberTheory_Idele_Cohomology_SPlaces_OutsideIntegralInduced_LocalInduction_Spine
attribute [-instance] _root_.OAI.PrimeDegreePackets.diagonalLogAction _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.chosenFinitePlaceCompletionAlgebra _root_.chosenFinitePlaceCompletionContinuousSMul _root_.chosenFinitePlaceCompletionFiniteDimensional _root_.chosenFinitePlaceCompletionLocallyCompactSpace _root_.chosenFinitePlaceLocalizedFiniteDimensional _root_.chosenFinitePlaceLocalizedIntegerAlgebra _root_.chosenFinitePlaceLocalizedIntegerModuleFinite _root_.chosenFinitePlaceLocalizedIsGalois _root_.chosenFinitePlaceLocalizedIsIntegralClosure _root_.chosenFinitePlaceLocalizedIsNonarchimedeanLocalField _root_.chosenFinitePlaceLocalizedIsValuativeTopology _root_.chosenFinitePlaceLocalizedLocallyCompactSpace _root_.chosenFinitePlaceLocalizedValuationCompatible _root_.chosenFinitePlaceLocalizedValuationHasExtension _root_.chosenFinitePlaceLocalizedValuationIsNontrivial _root_.chosenFinitePlaceLocalizedValuativeRel _root_.chosenFinitePlaceLocalizedValuativeRelIsNontrivial _root_.chosenFinitePlaceLocalizedValued
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

/-!
# Shared completion spine for integral local induction

This file names the coherent algebra, valuation, and integral-closure
structures used by every integral local-induction leaf.
-/

open scoped NumberField TensorProduct ValuativeRel NNReal
open NumberField IsDedekindDomain

noncomputable section

open AlgebraicNumberTheory.Valuations
open HilbertRamification
open LocalClassFieldTheory
open LocalFieldTheory

variable
    {K : Type} {L : Type}
    [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]

namespace LocalInductionInternal

variable (vK : AbsoluteValue K ℝ)
    (w : AbsoluteValueExtension vK L)

/-- The base-field algebra structure on the chosen extension completion. -/
@[reducible]
noncomputable def extensionCompletionAlgebra :
    Algebra K w.1.Completion :=
  AbsoluteValue.extensionCompletionAlgebra (K := K) w.1

/-- The scalar action underlying `extensionCompletionAlgebra`. -/
@[reducible]
noncomputable def extensionCompletionSMul :
    SMul K w.1.Completion :=
  (extensionCompletionAlgebra vK w).toSMul

/-- The completed-base algebra structure on the chosen extension
completion. -/
@[reducible]
noncomputable def completionAlgebra :
    Algebra vK.Completion w.1.Completion :=
  AbsoluteValue.completionAlgebra vK w.1 w.2

/-- The canonical valued structure on the chosen localized completion. -/
@[reducible]
noncomputable def localizedValued
    (hvKna : IsNonarchimedean (vK : K → ℝ)) :
    Valued (LocalizedCompletion vK w) ℝ≥0 :=
  localizedCompletionFinitePlaceValued vK w hvKna

/-- The canonical valuative relation on the chosen localized completion. -/
@[reducible]
noncomputable def localizedValuativeRel
    (hvKna : IsNonarchimedean (vK : K → ℝ)) :
    letI : Valued (LocalizedCompletion vK w) ℝ≥0 :=
      localizedValued vK w hvKna
    ValuativeRel (LocalizedCompletion vK w) :=
  localizedCompletionFinitePlaceValuativeRel vK w hvKna

/-- The canonical algebra of the localized completion over the completed
base valuation ring. -/
@[reducible]
noncomputable def integerAlgebra
    (hvKna : IsNonarchimedean (vK : K → ℝ)) :
    letI := extensionCompletionAlgebra vK w
    letI : SMul K w.1.Completion := extensionCompletionSMul vK w
    letI := completionAlgebra vK w
    letI : Valued vK.Completion ℝ≥0 := baseValued vK hvKna
    letI : ValuativeRel vK.Completion := baseValuativeRel vK hvKna
    letI : Valued (LocalizedCompletion vK w) ℝ≥0 :=
      localizedValued vK w hvKna
    letI : ValuativeRel (LocalizedCompletion vK w) :=
      localizedValuativeRel vK w hvKna
    Algebra 𝒪[vK.Completion] (LocalizedCompletion vK w) := by
  letI := extensionCompletionAlgebra vK w
  letI : SMul K w.1.Completion := extensionCompletionSMul vK w
  letI := completionAlgebra vK w
  letI : Valued vK.Completion ℝ≥0 := baseValued vK hvKna
  letI : ValuativeRel vK.Completion := baseValuativeRel vK hvKna
  letI : Valued (LocalizedCompletion vK w) ℝ≥0 :=
    localizedValued vK w hvKna
  letI : ValuativeRel (LocalizedCompletion vK w) :=
    localizedValuativeRel vK w hvKna
  exact Algebra.ofSubsemiring 𝒪[vK.Completion]

omit [NumberField K] [NumberField L] [FiniteDimensional K L]
    [IsGalois K L] in
/-- The canonical valuation-extension certificate for the integral
local-induction completion pair. -/
theorem valuationHasExtension
    (hvKna : IsNonarchimedean (vK : K → ℝ)) :
    letI := extensionCompletionAlgebra vK w
    letI : SMul K w.1.Completion := extensionCompletionSMul vK w
    letI := completionAlgebra vK w
    letI : Valued vK.Completion ℝ≥0 := baseValued vK hvKna
    letI : ValuativeRel vK.Completion := baseValuativeRel vK hvKna
    letI : Valued (LocalizedCompletion vK w) ℝ≥0 :=
      localizedValued vK w hvKna
    letI : ValuativeRel (LocalizedCompletion vK w) :=
      localizedValuativeRel vK w hvKna
    Valuation.HasExtension
      (ValuativeRel.valuation vK.Completion)
      (ValuativeRel.valuation (LocalizedCompletion vK w)) :=
  localizedCompletionValuationHasExtension vK w hvKna

omit [NumberField K] [NumberField L] [IsGalois K L] in
/-- The canonical integral-closure certificate for the integral
local-induction completion pair. -/
theorem isIntegralClosure
    (hvK : vK.IsNontrivial)
    (hvKna : IsNonarchimedean (vK : K → ℝ)) :
    letI := extensionCompletionAlgebra vK w
    letI : SMul K w.1.Completion := extensionCompletionSMul vK w
    letI := completionAlgebra vK w
    letI : Valued vK.Completion ℝ≥0 := baseValued vK hvKna
    letI : ValuativeRel vK.Completion := baseValuativeRel vK hvKna
    letI : Valued (LocalizedCompletion vK w) ℝ≥0 :=
      localizedValued vK w hvKna
    letI : ValuativeRel (LocalizedCompletion vK w) :=
      localizedValuativeRel vK w hvKna
    letI : Algebra 𝒪[vK.Completion] (LocalizedCompletion vK w) :=
      integerAlgebra vK w hvKna
    letI := valuationHasExtension vK w hvKna
    IsIntegralClosure
      𝒪[LocalizedCompletion vK w]
      𝒪[vK.Completion]
      (LocalizedCompletion vK w) :=
  localizedCompletionIsIntegralClosureWithExtension
    vK w hvK hvKna

end LocalInductionInternal
end
end

section
-- module Solutions.OAIQ244_DUKE.AlgebraicNumberTheory_Idele_Cohomology_SPlaces_OutsideIntegralInduced_LocalInduction_Action
attribute [-instance] _root_.OAI.PrimeDegreePackets.diagonalLogAction _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.chosenFinitePlaceCompletionAlgebra _root_.chosenFinitePlaceCompletionContinuousSMul _root_.chosenFinitePlaceCompletionFiniteDimensional _root_.chosenFinitePlaceCompletionLocallyCompactSpace _root_.chosenFinitePlaceLocalizedFiniteDimensional _root_.chosenFinitePlaceLocalizedIntegerAlgebra _root_.chosenFinitePlaceLocalizedIntegerModuleFinite _root_.chosenFinitePlaceLocalizedIsGalois _root_.chosenFinitePlaceLocalizedIsIntegralClosure _root_.chosenFinitePlaceLocalizedIsNonarchimedeanLocalField _root_.chosenFinitePlaceLocalizedIsValuativeTopology _root_.chosenFinitePlaceLocalizedLocallyCompactSpace _root_.chosenFinitePlaceLocalizedValuationCompatible _root_.chosenFinitePlaceLocalizedValuationHasExtension _root_.chosenFinitePlaceLocalizedValuationIsNontrivial _root_.chosenFinitePlaceLocalizedValuativeRel _root_.chosenFinitePlaceLocalizedValuativeRelIsNontrivial _root_.chosenFinitePlaceLocalizedValued
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

/-!
# Integral local induced modules

This file identifies the product of valuation-ring unit groups over the
extensions of a finite place with the corresponding induced module.
-/

open scoped NumberField TensorProduct ValuativeRel NNReal
open NumberField IsDedekindDomain

noncomputable section

open AlgebraicNumberTheory.Valuations
open HilbertRamification
open LocalClassFieldTheory
open LocalFieldTheory

variable
    {K : Type} {L : Type}
    [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]

section IntegralInduction

variable (vK : AbsoluteValue K ℝ) (hvK : vK.IsNontrivial)
    (hvKna : IsNonarchimedean (vK : K → ℝ))
    (w : AbsoluteValueExtension vK L)

/-- The decomposition-group action on the units of the intrinsic integer
ring of the chosen localization. -/
@[reducible]
noncomputable def decompositionGroupLocalizedIntegerUnitsAction :
    letI := LocalInductionInternal.extensionCompletionAlgebra vK w
    letI : SMul K w.1.Completion :=
      LocalInductionInternal.extensionCompletionSMul vK w
    letI := LocalInductionInternal.completionAlgebra vK w
    letI : Valued vK.Completion ℝ≥0 :=
      LocalInductionInternal.baseValued vK hvKna
    letI : ValuativeRel vK.Completion :=
      LocalInductionInternal.baseValuativeRel vK hvKna
    letI : Valued (LocalizedCompletion vK w) ℝ≥0 :=
      LocalInductionInternal.localizedValued vK w hvKna
    letI : ValuativeRel (LocalizedCompletion vK w) :=
      LocalInductionInternal.localizedValuativeRel vK w hvKna
    letI : Algebra 𝒪[vK.Completion] (LocalizedCompletion vK w) :=
      LocalInductionInternal.integerAlgebra vK w hvKna
    letI := LocalInductionInternal.valuationHasExtension vK w hvKna
    letI := LocalInductionInternal.isIntegralClosure
      vK w hvK hvKna
    MulDistribMulAction
      (absoluteValueDecompositionGroup K w.1)
      𝒪[LocalizedCompletion vK w]ˣ := by
  letI := LocalInductionInternal.extensionCompletionAlgebra vK w
  letI : SMul K w.1.Completion :=
    LocalInductionInternal.extensionCompletionSMul vK w
  letI := LocalInductionInternal.completionAlgebra vK w
  letI : Valued vK.Completion ℝ≥0 :=
    LocalInductionInternal.baseValued vK hvKna
  letI : ValuativeRel vK.Completion :=
    LocalInductionInternal.baseValuativeRel vK hvKna
  letI : Valued (LocalizedCompletion vK w) ℝ≥0 :=
    LocalInductionInternal.localizedValued vK w hvKna
  letI : ValuativeRel (LocalizedCompletion vK w) :=
    LocalInductionInternal.localizedValuativeRel vK w hvKna
  letI : Algebra 𝒪[vK.Completion] (LocalizedCompletion vK w) :=
    LocalInductionInternal.integerAlgebra vK w hvKna
  letI := LocalInductionInternal.valuationHasExtension vK w hvKna
  letI := LocalInductionInternal.isIntegralClosure
    vK w hvK hvKna
  letI : MulDistribMulAction
      (Gal(LocalizedCompletion vK w / vK.Completion))
      𝒪[LocalizedCompletion vK w]ˣ :=
    galoisGroupIntegerUnitsMulDistribMulActionOfIsIntegralClosure
      vK.Completion (LocalizedCompletion vK w)
  exact
    MulDistribMulAction.compHom
      𝒪[LocalizedCompletion vK w]ˣ
      (decompositionGroupEquivAlgebraicLocalizationAut
        vK hvK w).toMonoidHom


end IntegralInduction
end
end

section
-- module Solutions.OAIQ244_DUKE.AlgebraicNumberTheory_Idele_Cohomology_SPlaces_OutsideIntegralInduced_ChosenPlaceAction
attribute [-instance] _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.CyclicCohomology.binaryCoefficientFamilyCommGroup
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

/-!
# The action at a chosen finite place

This file exposes the decomposition-group action and the direct local
cohomology endpoint used by the integral induced-block construction. Keeping
this localization boundary in a lower leaf prevents downstream transport
proofs from elaborating it together with the tensor-block API.
-/

open scoped NumberField ValuativeRel NNReal
open NumberField IsDedekindDomain

noncomputable section

open AlgebraicNumberTheory.Valuations
open HilbertRamification
open LocalClassFieldTheory
open LocalFieldTheory
open CyclicCohomology.ProfiniteCohomology.Herbrand
open CyclicCohomology

variable
    {K : Type} {L : Type}
    [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]

section ChosenFinitePlace

/-- The decomposition group at the chosen extension of a finite place. -/
abbrev ChosenFinitePlaceDecompositionGroup
    (w₀ : HeightOneSpectrum (𝓞 K)) :=
  absoluteValueDecompositionGroup K
    (chosenFinitePlaceExtension (L := L) w₀).1

/-- Integer units in the chosen localized completion. -/
abbrev ChosenFinitePlaceLocalizedIntegerUnits
    (w₀ : HeightOneSpectrum (𝓞 K)) :=
  𝒪[ChosenFinitePlaceLocalizedCompletion
    (K := K) (L := L) w₀]ˣ

/-- Field units in the chosen localized completion. -/
abbrev ChosenFinitePlaceLocalizedFieldUnits
    (w₀ : HeightOneSpectrum (𝓞 K)) :=
  (ChosenFinitePlaceLocalizedCompletion
    (K := K) (L := L) w₀)ˣ

/-- The decomposition-group action on the chosen local integer units.

The named action is the boundary at which dependent induced-module
declarations stop expanding the chosen-localization construction. -/
@[implicit_reducible]
noncomputable def
    chosenFinitePlaceDecompositionGroupIntegerUnitsAction
    (w₀ : HeightOneSpectrum (𝓞 K)) :
    MulDistribMulAction
      (ChosenFinitePlaceDecompositionGroup
        (K := K) (L := L) w₀)
      (ChosenFinitePlaceLocalizedIntegerUnits
        (K := K) (L := L) w₀) :=
  decompositionGroupLocalizedIntegerUnitsAction
    (vK := HeightOneSpectrum.adicAbv K w₀)
    (hvK := RayClass.adicAbv_isNontrivial w₀)
    (hvKna :=
      HeightOneSpectrum.isNonarchimedean_adicAbv K w₀)
    (w := chosenFinitePlaceExtension (L := L) w₀)

/-- The decomposition-group action on the chosen local field units. -/
@[implicit_reducible]
noncomputable def chosenFinitePlaceDecompositionGroupLocalUnitsAction
    (w₀ : HeightOneSpectrum (𝓞 K)) :
    MulDistribMulAction
      (ChosenFinitePlaceDecompositionGroup
        (K := K) (L := L) w₀)
      (ChosenFinitePlaceLocalizedFieldUnits
        (K := K) (L := L) w₀) :=
  decompositionGroupLocalUnitsAction
    (HeightOneSpectrum.adicAbv K w₀)
    (RayClass.adicAbv_isNontrivial w₀)
    (chosenFinitePlaceExtension (L := L) w₀)

/-- The induced module of integer units at the chosen finite place. -/
abbrev ChosenFinitePlaceInducedIntegerUnits
    (w₀ : HeightOneSpectrum (𝓞 K)) :=
  @InducedModule
    (G := L ≃ₐ[K] L)
    (B := ChosenFinitePlaceLocalizedIntegerUnits
      (K := K) (L := L) w₀)
    inferInstance
    (ChosenFinitePlaceDecompositionGroup
      (K := K) (L := L) w₀)
    inferInstance
    (chosenFinitePlaceDecompositionGroupIntegerUnitsAction
      (K := K) (L := L) w₀)

/-- The local multiplicative block attached to the chosen finite place. -/
abbrev ChosenFinitePlaceLocalPlaceBlock
    (w₀ : HeightOneSpectrum (𝓞 K)) :=
  LocalPlaceBlock
    (HeightOneSpectrum.adicAbv K w₀)
    (RayClass.adicAbv_isNontrivial w₀)
    (chosenFinitePlaceExtension (L := L) w₀)

end ChosenFinitePlace
end
end


