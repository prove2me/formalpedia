-- Prove2me | Definitions.Def_OAIQ244Duke053
-- name    : OAIQ244Duke053
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-13T07:04:34.435206+00:00
-- url     : https://prove2.me/theorems/c92583c9-32ca-4d2f-91bb-9dc9b7df96dc
-- title:
--   Definitions bundle OAIQ244Duke053 of the split of OpenAI, Equidistribution of Prime-Degree Torus Packets with Arbitrary Local Type
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.DukePrimeDegree.prime_degree_packet_measure_equidistribution_unconditional` and `OAI.DukePrimeDegree.prime_degree_packet_measures_tendsto_haar_unconditional`, carved from OpenAI's openai/math development (OpenAI, *Equidistribution of Prime-Degree Torus Packets with Arbitrary Local Type*, OpenAI Math Release, September 24, 2026, result family 15, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 165 declarations of OpenAI's Lean: 37 definitions, 4 instances and 124 theorems. The definitions and types are `ClassFormation.DegreeData.abstractReciprocityEquiv`, `ClassFormation.DegreeData.abstractReciprocityTotallyRamifiedFiniteGaloisExtension`, `ClassFormation.DegreeData.abstractReciprocityTotallyRamifiedFrobeniusInM`, `ClassFormation.DegreeData.abstractReciprocityTotallyRamifiedLowerGenerator`, `ClassFormation.DegreeData.abstractReciprocityTotallyRamifiedRestrictionEquiv`, `ClassFormation.DegreeData.chosenDegreeOneFrobeniusLiftOfFiniteTotallyRamified`, `ClassFormation.DegreeData.chosenDegreeOneFrobeniusLiftOfTotallyRamified`, `ClassFormation.DegreeData.finiteUnramifiedDegreeEquiv`, `ClassFormation.DegreeData.finiteUnramifiedDegreeHom`, `ClassFormation.DegreeData.finiteUnramifiedRestriction`, `ClassFormation.DegreeData.maximalUnramifiedExtensionRestriction`, `ClassFormation.DegreeData.maximalUnramifiedFrobeniusPower`, `ClassFormation.DegreeData.normResidueSymbol`, `ClassFormation.FiniteAbelianSubextension.NormOpenAddSubgroup`, `ClassFormation.FiniteAbelianSubextension.normSubgroupMap`, `ClassFormation.FiniteCyclicSubextension.galoisGenerator`, `ClassFormation.FiniteCyclicSubextension.toFiniteGaloisSubextension`, `ClassFormation.FiniteGaloisSubextension.abelianIntermediateField`, `ClassFormation.FiniteGaloisSubextension.abelianRestrictionHom`, `ClassFormation.FiniteGaloisSubextension.abstractReciprocityRestrictionCosetEquiv`, `ClassFormation.FiniteGaloisSubextension.abstractReciprocityRestrictionCosetMap`, `ClassFormation.FiniteGaloisSubextension.abstractReciprocityRestrictionMulEquiv`, `ClassFormation.FiniteGaloisSubextension.bundledRestrictionHom`, `ClassFormation.FiniteGaloisSubextension.inertiaImage`, `ClassFormation.FiniteGaloisSubextension.intermediateNormMap`, `ClassFormation.FiniteGaloisSubextension.intermediateNormQuotientInclusion`, `ClassFormation.FiniteGaloisSubextension.lowerInclusionHom`, `ClassFormation.FiniteGaloisSubextension.maximalUnramifiedSubextension`, `ClassFormation.FiniteGaloisSubextension.upperRestrictionHom`, `ClassFormation.ValuationData.maximalUnramifiedNormResidueSymbol`, `ClassFormation.abstractReciprocityInclusion`, `ClassFormation.abstractReciprocityNormMap`, `ClassFormation.abstractReciprocityNormProjection`, `ClassFormation.abstractReciprocityRestriction`, `ClassFormation.normResidueNaturalityAbelianizedConjugation`, `ClassFormation.normResidueNaturalityAbelianizedRestriction`, `ClassFormation.transferNormNaturalityNormQuotientInclusion`.
--
--   **Sources.** They come from these modules of lean/OAI/NumberTheory, in whole or in part: `AbstractClassFieldTheory_Reciprocity_Construction_MainNaturality`, `AbstractClassFieldTheory_Reciprocity_Construction_MainTransfer`, `AbstractClassFieldTheory_Reciprocity_Core`, `AbstractClassFieldTheory_Reciprocity_FiniteAbelianClassification`, `AbstractClassFieldTheory_Reciprocity_Main`, `AbstractClassFieldTheory_Reciprocity_MaximalUnramifiedSymbol`, `AbstractClassFieldTheory_Reciprocity_Reduction`, `AbstractClassFieldTheory_Reciprocity_Sylow`, `AbstractClassFieldTheory_Reciprocity_TotallyRamified`, `AbstractClassFieldTheory_Reciprocity_TotallyRamifiedCase_Conclusion`, `AbstractClassFieldTheory_Reciprocity_TotallyRamifiedCase_FixedSource`, `AbstractClassFieldTheory_Reciprocity_TotallyRamifiedCase_FrobeniusLift`, `AbstractClassFieldTheory_Reciprocity_TotallyRamifiedCase_FrobeniusNorms`, `AbstractClassFieldTheory_Reciprocity_TotallyRamifiedCase_RestrictionCosets`, `AbstractClassFieldTheory_Reciprocity_TotallyRamifiedCase_RestrictionEquiv`, `GlobalClassFieldTheory_ClassFieldAxiom_IdeleClassPowerLocalUnitQuotient_ArchimedeanPowerIndex`.
--
--   **Imports.** It imports the bundles `OAIQ244Duke045` and `OAIQ244Duke046` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ244Duke062`, `OAIQ244Duke063`, `OAIQ244Duke065` and `OAIQ244Duke066`.
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
import Mathlib.Algebra.Group.Equiv.Basic
import Mathlib.Algebra.Group.Hom.Basic
import Mathlib.Algebra.Group.Int.TypeTags
import Mathlib.Algebra.Group.Pi.Basic
import Mathlib.Algebra.Group.Pi.Units
import Mathlib.Algebra.Group.Subgroup.Basic
import Mathlib.Algebra.Group.Subgroup.Ker
import Mathlib.Algebra.Group.Subgroup.Map
import Mathlib.Algebra.Group.Subgroup.Pointwise
import Mathlib.Algebra.Group.TransferInstance
import Mathlib.Algebra.Group.Units.Equiv
import Mathlib.Algebra.Group.Units.Hom
import Mathlib.Algebra.Module.Equiv.Basic
import Mathlib.Algebra.Module.LinearMap.Polynomial
import Mathlib.Algebra.Module.PID
import Mathlib.Algebra.Module.Shrink
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
import Mathlib.FieldTheory.Galois.Abelian
import Mathlib.FieldTheory.Galois.Basic
import Mathlib.FieldTheory.Galois.Infinite
import Mathlib.FieldTheory.Galois.IsGaloisGroup
import Mathlib.FieldTheory.Galois.NormalBasis
import Mathlib.FieldTheory.Galois.Profinite
import Mathlib.FieldTheory.IntermediateField.Adjoin.Algebra
import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.FieldTheory.IsAlgClosed.Basic
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
import Mathlib.GroupTheory.FiniteAbelian.Duality
import Mathlib.GroupTheory.GroupAction.Basic
import Mathlib.GroupTheory.GroupAction.Defs
import Mathlib.GroupTheory.GroupAction.Quotient
import Mathlib.GroupTheory.Index
import Mathlib.GroupTheory.Nilpotent
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.GroupTheory.QuotientGroup.Basic
import Mathlib.GroupTheory.QuotientGroup.Finite
import Mathlib.GroupTheory.SpecificGroups.Cyclic
import Mathlib.GroupTheory.Sylow
import Mathlib.GroupTheory.Transfer
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.LinearAlgebra.Charpoly.BaseChange
import Mathlib.LinearAlgebra.Determinant
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Dimension.DivisionRing
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.LinearAlgebra.Dimension.Localization
import Mathlib.LinearAlgebra.Dimension.Torsion.Finite
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.FreeModule.IdealQuotient
import Mathlib.LinearAlgebra.Quotient.Pi
import Mathlib.LinearAlgebra.StdBasis
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
import Mathlib.NumberTheory.NumberField.Cyclotomic.Basic
import Mathlib.NumberTheory.NumberField.ProductFormula
import Mathlib.NumberTheory.NumberField.Units.DirichletTheorem
import Mathlib.NumberTheory.NumberField.Units.Regulator
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
import Mathlib.RingTheory.ClassGroup.Basic
import Mathlib.RingTheory.Complex
import Mathlib.RingTheory.DedekindDomain.Factorization
import Mathlib.RingTheory.DedekindDomain.IntegralClosure
import Mathlib.RingTheory.DedekindDomain.SInteger
import Mathlib.RingTheory.DiscreteValuationRing.Basic
import Mathlib.RingTheory.DiscreteValuationRing.TFAE
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
import Mathlib.Topology.Algebra.FilterBasis
import Mathlib.Topology.Algebra.Group.Basic
import Mathlib.Topology.Algebra.Group.ClosedSubgroup
import Mathlib.Topology.Algebra.Group.Pointwise
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
import Mathlib.Topology.Homeomorph.Defs
import Mathlib.Topology.Instances.Matrix
import Mathlib.Topology.Instances.Sign
import Mathlib.Topology.Instances.ZMod
import Mathlib.Topology.Maps.Basic
import Mathlib.Topology.Neighborhoods
import Mathlib.Topology.Order
import Mathlib.Topology.Sets.Opens
import Mathlib.Topology.UniformSpace.AbsoluteValue
import Mathlib.Topology.WithTopology
import Definitions.Def_OAIQ244Duke045
import Definitions.Def_OAIQ244Duke046

section
-- module Solutions.OAIQ244_DUKE.AbstractClassFieldTheory_Reciprocity_Construction_MainNaturality
attribute [-instance] _root_.ClassFormation.FiniteGaloisSubextension.extensionSubgroup_over_intermediate_normalInstance _root_.ClassFormation.FiniteGaloisSubextension.intermediateField_normalInstance _root_.ClassFormation.instIsAddTorsionFreeZHat _root_.ClassFormation.instIsMulTorsionFreeMultiplicativeZHat _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.DiscreteNthRootsSubgroup.instTopologicalSpaceSubtypeUnitsMemSubgroup _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.KummerTheory.finite_finsupp_nsmulQuotient _root_.LocalClassFieldTheory.baseFixingExtensionQuotient_finite _root_.LocalClassFieldTheory.extensionSubgroupBase_normal _root_.LocalClassFieldTheory.finiteGaloisExtensionSubgroupOfEmbedding_normal _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitQuotientCarrier_finite _root_.LocalFieldTheory.DiscreteValuationField.finite_padicInt_finPi_nsmulQuotient _root_.LocalFieldTheory.DiscreteValuationField.finite_padicInt_pi_nsmulQuotient_of_coprime _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_multiplicative_nthPowerQuotient _root_.LocalFieldTheory.finite_nsmulAddQuotient_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.LubinTate.compatibleGroupFamiliesGroup _root_.OAI.PrimeDegreePackets.boundedRealFields_finite _root_.OAI.PrimeDegreePackets.instNonemptyLeafTestSpace _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.RamificationTheory.HilbertRamification.ValuationSubring.inertiaGroup_normal _root_.RamificationTheory.HilbertRamification.ValuationSubring.ramificationGroupInInertiaAut_normal _root_.RayClass.approximationCompletionTopologicalSpace _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.LocalClassFieldTheory.normalizationIntegerRingIsIntegralClosure _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteIdeleGroupIsTopologicalGroup _root_.finiteLocalUnitsOpen _root_.ideleGroupIsTopologicalGroup
attribute [-simp] _root_.ClassFormation.DegreeData.transferNormNaturalityAbelianizedReciprocity_of _root_.ClassFormation.DegreeData.transferNormNaturalityFrobeniusIntermediateEquiv_mk _root_.ClassFormation.DegreeData.transferNormNaturalityIntermediateToFrobeniusSubgroup_apply _root_.ClassFormation.DegreeData.transferNormNaturalityTransferFrobeniusLift_coe _root_.ClassFormation.DegreeData.transferNormNaturalityTransferNormOrbitEquiv_mk _root_.ClassFormation.FiniteAbelianSubextension.extensionQuotientMk_apply _root_.ClassFormation.FiniteGaloisSubextension.classFieldCandidate_field _root_.ClassFormation.cyclicNormClassHom_apply _root_.ClassFormation.extensionFixedRepresentationEquiv_apply_coe _root_.ClassFormation.extensionFixedRepresentationEquiv_symm_apply_coe _root_.ClassFormation.mem_normFilterBasis_iff _root_.ClassFormation.orbitQuotientClosedCyclicEquiv_mk _root_.ClassFormation.toZModPow_zHatToPadicInt _root_.ClassFormation.transferNormNaturalityExtensionFixedEquiv_apply_coe _root_.ClassFormation.transferNormNaturalityExtensionFixedEquiv_symm_coe _root_.ClassFormation.transferNormNaturalityIntermediateAbsoluteEquiv_apply _root_.ClassFormation.transferNormNaturalityIntermediateInclusion_mk _root_.ClassFormation.transferNormNaturalityIntermediateQuotientEquiv_mk _root_.ClassFormation.zHatReductionRingHom_apply _root_.ClassFormation.zHatRingEquivProfiniteIntegerPrimeProduct_apply _root_.ClassFormation.zHatToPadicInt_intCast _root_.ClassFormation.zHatToProfiniteIntegerPrimeProduct_apply _root_.ClassFormation.zHatToProfiniteIntegerPrimeProduct_intCast _root_.ClassFormation.zHatUnitsContinuousMulEquivPrimeProduct_coe_apply _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.IsDiscreteValuationRing.addVal_ringEquiv _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.KummerTheory.torsionQuotientEquivOfZHatMulDecomposition_mk _root_.KummerTheory.zHatUnitsContinuousMulEquivPrimeProduct_rationalCyclotomicCharacter _root_.LocalClassFieldTheory.baseFixingExtensionQuotientEquivAmbient_mk _root_.LocalClassFieldTheory.baseUnitsEquivGaloisAmbientFixed_val _root_.LocalClassFieldTheory.embeddedFieldUnitsEquivGaloisFixed_coe _root_.LocalClassFieldTheory.finiteGaloisUnitsEquivAbstractFixedOfEmbedding_coe _root_.LocalClassFieldTheory.finiteGaloisUnitsEquivAbstractFixed_coe _root_.LocalClassFieldTheory.finiteResidueFrobeniusFromZHat_apply _root_.LocalClassFieldTheory.finiteResidueFrobeniusFromZHat_one _root_.LocalClassFieldTheory.intermediateFieldUnitsEquivGaloisFixed_coe _root_.LocalClassFieldTheory.intrinsicFiniteAbstractBase_eq_base _root_.LocalClassFieldTheory.residueAbsoluteDegreeIn_frobenius _root_.LocalClassFieldTheory.residueAbsoluteFrobenius_one _root_.LocalClassFieldTheory.residueFrobeniusToLimit_apply_component _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.LocalFieldTheory.residueField_algebraMap_residue _root_.OAI.PrimeDegreePackets.ThetaConstruction.schwartzCM_apply _root_.ClassFormation.transferNormNaturalityRightCosetProductEquiv_apply _root_.infinitePlace_mult_smul
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

namespace DegreeData

/-- The fixed field of a transported Frobenius lift contains the original
fixed field, i.e. `Σ' / Σ` is an intermediate extension. -/
theorem finiteReciprocityNaturalityFrobeniusFixedField_le
    (D : DegreeData G) [IsTopologicalGroup G]
    (E : DegreeData.FiniteResidueAbstractExtension D)
    (L L' : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ E.base.toSubgroup)
    (hL'K' : L'.toSubgroup ≤ E.field.toSubgroup)
    (hL'L : L'.toSubgroup ≤ L.toSubgroup)
    [hLnormal : (extensionSubgroup E.base.field L hLK).Normal]
    [hL'normal : (extensionSubgroup E.field.field L' hL'K').Normal]
    (σ : D.FrobeniusElements E.field L' hL'K') :
    (D.frobeniusFixedField E.field L' hL'K' σ).toSubgroup ≤
      (D.frobeniusFixedField E.base L hLK
        (D.finiteReciprocityNaturalityFrobeniusTowerLift
          E L L' hLK hL'K' hL'L σ)).toSubgroup := by
  rintro g ⟨k', hk', rfl⟩
  let k : E.base.field.toSubgroup := Subgroup.inclusion E.below k'
  refine ⟨k, ?_, rfl⟩
  change QuotientGroup.mk k ∈
    (D.frobeniusClosure E.base L hLK
      (D.finiteReciprocityNaturalityFrobeniusTowerLift
        E L L' hLK hL'K' hL'L σ)).toSubgroup
  change QuotientGroup.mk k' ∈
    (D.frobeniusClosure E.field L' hL'K' σ).toSubgroup at hk'
  have hmap := map_mem_closedSubgroupGenerated_singleton
    (D.finiteReciprocityNaturalityFrobeniusTowerMapContinuous
      E.base.field E.field.field L L' hLK hL'K' E.below hL'L) σ.1 (by
        simpa [DegreeData.frobeniusClosure] using hk')
  let f := D.finiteReciprocityNaturalityFrobeniusTowerMap
    E.base.field E.field.field L L' hLK hL'K' E.below hL'L
  change f (QuotientGroup.mk k') ∈
    (closedSubgroupGenerated ({f σ.1} : Set _) : Subgroup _) at hmap
  simp [DegreeData.frobeniusClosure]
  change f (QuotientGroup.mk k') ∈
    (closedSubgroupGenerated ({f σ.1} : Set _) : Subgroup _)
  exact hmap

/-- The intermediate extension `Σ' / Σ` attached to a transported
Frobenius lift is totally ramified. -/
theorem finiteReciprocityNaturalityFrobeniusFixedField_isTotallyRamified
    (D : DegreeData G) [IsTopologicalGroup G] [CompactSpace G] [T2Space G]
    (E : DegreeData.FiniteResidueAbstractExtension D)
    (L L' : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ E.base.toSubgroup)
    (hL'K' : L'.toSubgroup ≤ E.field.toSubgroup)
    (hL'L : L'.toSubgroup ≤ L.toSubgroup)
    [hLnormal : (extensionSubgroup E.base.field L hLK).Normal]
    [hL'normal : (extensionSubgroup E.field.field L' hL'K').Normal]
    [Finite
      (E.base.toSubgroup ⧸ extensionSubgroup E.base.field L hLK)]
    [hL'K'finite : Finite
      (E.field.toSubgroup ⧸ extensionSubgroup E.field.field L' hL'K')]
    (σ : D.FrobeniusElements E.field L' hL'K') :
    (DegreeData.AbstractExtension.mk
      (D.frobeniusFixedField E.field L' hL'K' σ)
      (D.frobeniusFixedField E.base L hLK
        (D.finiteReciprocityNaturalityFrobeniusTowerLift
          E L L' hLK hL'K' hL'L σ))
      (D.finiteReciprocityNaturalityFrobeniusFixedField_le
        E L L' hLK hL'K' hL'L σ)).IsTotallyRamified D := by
  let τ := D.finiteReciprocityNaturalityFrobeniusTowerLift
    E L L' hLK hL'K' hL'L σ
  let S' := D.frobeniusFixedField E.field L' hL'K' σ
  let S := D.frobeniusFixedField E.base L hLK τ
  let hS'S := D.finiteReciprocityNaturalityFrobeniusFixedField_le
    E L L' hLK hL'K' hL'L σ
  let FS := D.frobeniusFixedResidueField E.base L hLK τ
  let FS' := D.frobeniusFixedResidueField E.field L' hL'K' σ
  have hresidue : (FS.residueDegree : ℕ) = (FS'.residueDegree : ℕ) := by
    calc
      (FS.residueDegree : ℕ) =
          D.frobeniusExponent E.base L hLK τ *
            (E.base.residueDegree : ℕ) :=
        D.frobeniusFixedResidueField_residueDegree E.base L hLK τ
      _ = ((E.residueDegree : ℕ) *
            D.frobeniusExponent E.field L' hL'K' σ) *
          (E.base.residueDegree : ℕ) := by
        rw [D.finiteReciprocityNaturalityFrobeniusTowerLift_exponent]
      _ = D.frobeniusExponent E.field L' hL'K' σ *
          ((E.residueDegree : ℕ) * (E.base.residueDegree : ℕ)) := by
        ac_rfl
      _ = D.frobeniusExponent E.field L' hL'K' σ *
          (E.field.residueDegree : ℕ) := by
        rw [E.residueDegree_mul_absoluteResidueDegree D]
      _ = (FS'.residueDegree : ℕ) :=
        (D.frobeniusFixedResidueField_residueDegree E.field L' hL'K' σ).symm
  let hS'K' := D.frobeniusFixedField_le E.field L' hL'K' σ
  let hSK := D.frobeniusFixedField_le E.base L hLK τ
  let : Finite (E.field.toSubgroup ⧸
      extensionSubgroup E.field.field S' hS'K') :=
    D.frobeniusFixedField_finite E.field L' hL'K' σ
  let : Finite (E.base.toSubgroup ⧸
      extensionSubgroup E.base.field S hSK) :=
    D.frobeniusFixedField_finite E.base L hLK τ
  let : Finite (E.base.toSubgroup ⧸
      extensionSubgroup E.base.field S' (hS'K'.trans E.below)) :=
    relativeTowerQuotientFinite E.base.field E.field.field S' hS'K' E.below
  let hS'Sfinite : Finite
      (S.toSubgroup ⧸ extensionSubgroup S S' hS'S) :=
    FiniteIntermediateField.finite_extension_of_le
      (hS'S.trans hSK) hSK hS'S
  let ES'S : DegreeData.FiniteResidueAbstractExtension D :=
    { field := FS'
      base := FS
      below := hS'S
      finiteQuotient := hS'Sfinite }
  have hrelative : (ES'S.residueDegree : ℕ) = 1 := by
    change (ES'S.base.residueDegree : ℕ) =
      (ES'S.field.residueDegree : ℕ) at hresidue
    have hmul := ES'S.residueDegree_mul_absoluteResidueDegree D
    rw [← hresidue] at hmul
    have hpos : 0 < (ES'S.base.residueDegree : ℕ) :=
      ES'S.base.residueDegree.property
    nlinarith
  exact ES'S.toFiniteAbstractExtension.isTotallyRamified_of_residueDegree_eq_one
    D hrelative

end DegreeData

end GroupOnly

section Representation

/-! Mathlib's `Rep ℤ G` forces its representation-bearing group `G` to `Type 0`. -/
variable {G : IntegralRepGroupType} [Group G] [TopologicalSpace G]

/-- The norm identity used for the first diagram of norm--conjugation naturality,
already expressed in the target finite norm quotient.  Taking `S = Σ` and
`S' = Σ'` gives the calculation. -/
theorem finiteReciprocityNaturality_norm_tower_class
    (A : Rep ℤ G)
    (K K' L L' S S' : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.toSubgroup)
    (hL'K' : L'.toSubgroup ≤ K'.toSubgroup)
    (hK'K : K'.toSubgroup ≤ K.toSubgroup)
    (hL'L : L'.toSubgroup ≤ L.toSubgroup)
    (hSK : S.toSubgroup ≤ K.toSubgroup)
    (hS'K' : S'.toSubgroup ≤ K'.toSubgroup)
    (hS'S : S'.toSubgroup ≤ S.toSubgroup)
    [hLKfinite : Finite (K.toSubgroup ⧸ extensionSubgroup K L hLK)]
    [hL'K'finite : Finite (K'.toSubgroup ⧸ extensionSubgroup K' L' hL'K')]
    [hK'Kfinite : Finite (K.toSubgroup ⧸ extensionSubgroup K K' hK'K)]
    [hSKfinite : Finite (K.toSubgroup ⧸ extensionSubgroup K S hSK)]
    [hS'K'finite : Finite (K'.toSubgroup ⧸ extensionSubgroup K' S' hS'K')]
    [hS'Sfinite : Finite (S.toSubgroup ⧸ extensionSubgroup S S' hS'S)]
    (π : ambientFixedAddSubgroup A S') :
    finiteReciprocityNaturalityNormMap A K K' L L' hLK hL'K' hK'K hL'L
        (finiteNormClass A K' L' hL'K'
          (relativeNorm A K' S' hS'K' π)) =
      finiteNormClass A K L hLK
        (relativeNorm A K S hSK (relativeNorm A S S' hS'S π)) := by
  let hS'Kfinite : Finite (K.toSubgroup ⧸
      extensionSubgroup K S' (hS'K'.trans hK'K)) :=
    finiteReciprocityNaturality_tower_finite K K' S' hK'K hS'K'
  let TKK' : DegreeData.FiniteTower G :=
    { top := S'
      middle := K'
      base := K
      top_le_middle := hS'K'
      middle_le_base := hK'K
      finiteTopQuotient := hS'K'finite
      finiteBaseQuotient := hK'Kfinite }
  let TSS' : DegreeData.FiniteTower G :=
    { top := S'
      middle := S
      base := K
      top_le_middle := hS'S
      middle_le_base := hSK
      finiteTopQuotient := hS'Sfinite
      finiteBaseQuotient := hSKfinite }
  rw [finiteReciprocityNaturalityNormMap_finiteNormClass]
  apply congrArg (finiteNormClass A K L hLK)
  calc
    relativeNorm A K K' hK'K (relativeNorm A K' S' hS'K' π) =
        relativeNorm A K S' (hS'K'.trans hK'K) π :=
      TKK'.norm_trans_apply A π
    _ = relativeNorm A K S' (hS'S.trans hSK) π := by
      congr 2
    _ = relativeNorm A K S hSK (relativeNorm A S S' hS'S π) :=
      (TSS'.norm_trans_apply A π).symm

namespace DegreeData

/-- **norm--conjugation naturality, first diagram.** Restriction on finite Galois groups
corresponds under the finite reciprocity equivalence to the norm `N_{K'/K}` on finite norm
quotients. -/
theorem finiteReciprocityNaturality_restriction_norm_commutes
    (D : DegreeData G) (A : Rep ℤ G) (v : ValuationData D A)
    [IsTopologicalGroup G] [CompactSpace G] [T2Space G]
    [TotallyDisconnectedSpace G]
    (hAxiom : v.SatisfiesUnramifiedUnitCohomology D)
    (E : FiniteAbstractFieldExtension G)
    (L L' : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ E.base.field.toSubgroup)
    (hL'K' : L'.toSubgroup ≤ E.field.field.toSubgroup)
    (hL'L : L'.toSubgroup ≤ L.toSubgroup)
    [hLnormal : (extensionSubgroup E.base.field L hLK).Normal]
    [hL'normal : (extensionSubgroup E.field.field L' hL'K').Normal]
    [hLKfinite : Finite
      (E.base.field.toSubgroup ⧸ extensionSubgroup E.base.field L hLK)]
    [hL'K'finite : Finite
      (E.field.field.toSubgroup ⧸
        extensionSubgroup E.field.field L' hL'K')] :
    (finiteReciprocityNaturalityNormMap A E.base.field E.field.field L L'
      hLK hL'K' E.below hL'L).comp
        (D.finiteReciprocityHom A v hAxiom E.field L' hL'K') =
      (D.finiteReciprocityHom A v hAxiom E.base L hLK).comp
      (finiteReciprocityNaturalityRestriction
          E.base.field E.field.field L L'
          hLK hL'K' E.below hL'L).toAdditive := by
  let ER := E.toFiniteResidueAbstractExtension D
  let hL'K'finiteER : Finite
      (ER.field.field.toSubgroup ⧸
        extensionSubgroup ER.field.field L' hL'K') := by
    change Finite
      (ER.field.field.toSubgroup ⧸
        extensionSubgroup ER.field.field L' hL'K') at hL'K'finite
    exact hL'K'finite
  let hLKfiniteER : Finite
      (ER.base.field.toSubgroup ⧸
        extensionSubgroup ER.base.field L hLK) := by
    change Finite
      (ER.base.field.toSubgroup ⧸
        extensionSubgroup ER.base.field L hLK) at hLKfinite
    exact hLKfinite
  let hLnormalERbase :
      (extensionSubgroup ER.base.field L hLK).Normal := by
    change (extensionSubgroup ER.base.field L hLK).Normal at hLnormal
    exact hLnormal
  let hL'normalERfield :
      (extensionSubgroup ER.field.field L' hL'K').Normal := by
    change (extensionSubgroup ER.field.field L' hL'K').Normal at hL'normal
    exact hL'normal
  apply AddMonoidHom.ext
  intro q
  let σ := D.chosenFiniteReciprocityFrobeniusLift ER.field L' hL'K' q.toMul
  let τ := D.finiteReciprocityNaturalityFrobeniusTowerLift
    ER L L' hLK hL'K' hL'L σ
  have hσ : D.frobeniusRestriction ER.field L' hL'K' σ = q.toMul :=
    D.frobeniusRestriction_chosenFiniteReciprocityFrobeniusLift
      ER.field L' hL'K' q.toMul
  have hτ : D.frobeniusRestriction ER.base L hLK τ =
      ((finiteReciprocityNaturalityRestriction
        E.base.field E.field.field L L'
        hLK hL'K' E.below hL'L).toAdditive q).toMul := by
    rw [← D.finiteReciprocityNaturalityRestriction_frobeniusTowerLift
      ER L L' hLK hL'K' hL'L σ, hσ]
    rfl
  let S' := D.frobeniusFixedField ER.field L' hL'K' σ
  let S := D.frobeniusFixedField ER.base L hLK τ
  let hS'K' := D.frobeniusFixedField_le ER.field L' hL'K' σ
  let hSK := D.frobeniusFixedField_le ER.base L hLK τ
  let hS'S := D.finiteReciprocityNaturalityFrobeniusFixedField_le
    ER L L' hLK hL'K' hL'L σ
  let hS'K'finite : Finite
      (E.field.field.toSubgroup ⧸
        extensionSubgroup E.field.field S' hS'K') :=
    D.frobeniusFixedField_finite ER.field L' hL'K' σ
  let hSKfinite : Finite
      (E.base.field.toSubgroup ⧸
        extensionSubgroup E.base.field S hSK) :=
    D.frobeniusFixedField_finite ER.base L hLK τ
  let hS'Kfinite : Finite
      (E.base.field.toSubgroup ⧸
        extensionSubgroup E.base.field S' (hS'K'.trans E.below)) :=
    finiteReciprocityNaturality_tower_finite
      E.base.field E.field.field S' E.below hS'K'
  let hS'Sfinite : Finite
      (S.toSubgroup ⧸ extensionSubgroup S S' hS'S) :=
    FiniteIntermediateField.finite_extension_of_le
      (K := E.base.field) (hS'S.trans hSK) hSK hS'S
  let hSabsolute : Finite ((baseField G).toSubgroup ⧸
      extensionSubgroup (baseField G) S (le_baseField S)) :=
    D.frobeniusFixedField_absoluteFinite E.base L hLK τ
  let hS'absolute : Finite ((baseField G).toSubgroup ⧸
      extensionSubgroup (baseField G) S' (le_baseField S')) :=
    D.frobeniusFixedField_absoluteFinite E.field L' hL'K' σ
  let Sfinite : FiniteAbstractField G := ⟨S, hSabsolute⟩
  let S'finite : FiniteAbstractField G := ⟨S', hS'absolute⟩
  let ES'S : FiniteAbstractFieldExtension G :=
    { field := S'finite
      base := Sfinite
      below := hS'S
      finiteQuotient := hS'Sfinite }
  let π : ambientFixedAddSubgroup A S' := v.chosenPrimeElement S'finite
  have hπ : v.IsPrimeElement S'finite π := v.chosenPrimeElement_isPrime S'finite
  let πS : ambientFixedAddSubgroup A S := relativeNorm A S S' hS'S π
  have hTot : ES'S.IsTotallyRamified D := by
    have hTot' :=
      D.finiteReciprocityNaturalityFrobeniusFixedField_isTotallyRamified
        ER L L' hLK hL'K' hL'L σ
    change ES'S.IsTotallyRamified D at hTot'
    exact hTot'
  have hπS : v.IsPrimeElement Sfinite πS :=
    v.norm_prime_of_totallyRamified ES'S hTot π hπ
  change finiteReciprocityNaturalityNormMap
      A E.base.field E.field.field L L' hLK hL'K' E.below hL'L
      (D.finiteReciprocityHom A v hAxiom E.field L' hL'K' q) =
    D.finiteReciprocityHom A v hAxiom E.base L hLK
      ((finiteReciprocityNaturalityRestriction
        E.base.field E.field.field L L'
        hLK hL'K' E.below hL'L).toAdditive q)
  calc
    finiteReciprocityNaturalityNormMap
        A E.base.field E.field.field L L' hLK hL'K' E.below hL'L
        (D.finiteReciprocityHom A v hAxiom E.field L' hL'K' q) =
      finiteReciprocityNaturalityNormMap
        A E.base.field E.field.field L L' hLK hL'K' E.below hL'L
        (finiteNormClass A E.field.field L' hL'K'
          (relativeNorm A E.field.field S' hS'K' π)) := by
      apply congrArg (finiteReciprocityNaturalityNormMap
        A E.base.field E.field.field L L' hLK hL'K' E.below hL'L)
      have hprime :=
        D.finiteReciprocityHom_apply_eq_primeNormClass
          A v hAxiom E.field L' hL'K' q σ hσ π hπ
      change D.finiteReciprocityHom A v hAxiom E.field L' hL'K' q =
        finiteNormClass A E.field.field L' hL'K'
          (relativeNorm A E.field.field S' hS'K' π) at hprime
      exact hprime
    _ = finiteNormClass A E.base.field L hLK
        (relativeNorm A E.base.field S hSK πS) := by
      exact finiteReciprocityNaturality_norm_tower_class
        A E.base.field E.field.field L L' S S'
        hLK hL'K' E.below hL'L hSK hS'K' hS'S π
    _ = D.finiteReciprocityHom A v hAxiom E.base L hLK
        ((finiteReciprocityNaturalityRestriction
          E.base.field E.field.field L L'
          hLK hL'K' E.below hL'L).toAdditive q) := by
      symm
      have hprime :=
        D.finiteReciprocityHom_apply_eq_primeNormClass
          A v hAxiom E.base L hLK _ τ hτ πS hπS
      change D.finiteReciprocityHom A v hAxiom E.base L hLK _ =
        finiteNormClass A E.base.field L hLK
          (relativeNorm A E.base.field S hSK πS) at hprime
      exact hprime

end DegreeData

/-- The norm identity used for the second diagram of norm--conjugation naturality,
expressed in the conjugate finite norm quotient. -/
theorem finiteReciprocityNaturality_conjugation_norm_class
    [ContinuousMul G] (A : Rep ℤ G)
    (K L S : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.toSubgroup)
    (hSK : S.toSubgroup ≤ K.toSubgroup) (s : G)
    [Finite (K.toSubgroup ⧸ extensionSubgroup K L hLK)]
    [Finite (K.toSubgroup ⧸ extensionSubgroup K S hSK)]
    (π : ambientFixedAddSubgroup A S) :
    let hConjLK := conjugateClosedSubgroup_mono hLK s
    let hConjSK := conjugateClosedSubgroup_mono hSK s
    letI : Finite ((conjugateClosedSubgroup K s).toSubgroup ⧸
        extensionSubgroup (conjugateClosedSubgroup K s)
          (conjugateClosedSubgroup L s) hConjLK) :=
      finite_conjugateExtension K L hLK s
    letI : Finite ((conjugateClosedSubgroup K s).toSubgroup ⧸
        extensionSubgroup (conjugateClosedSubgroup K s)
          (conjugateClosedSubgroup S s) hConjSK) :=
      finite_conjugateExtension K S hSK s
    finiteReciprocityNaturalityConjugationNormMap A K L hLK s
        (finiteNormClass A K L hLK
          (relativeNorm A K S hSK π)) =
      finiteNormClass A (conjugateClosedSubgroup K s)
        (conjugateClosedSubgroup L s) hConjLK
        (relativeNorm A (conjugateClosedSubgroup K s)
          (conjugateClosedSubgroup S s) hConjSK
          (conjugateFixedElement A S s π)) := by
  dsimp only
  rw [finiteReciprocityNaturalityConjugationNormMap_finiteNormClass,
    relativeNorm_conjugate_apply]

end Representation

section GroupOnly

variable {G : Type u} [Group G] [TopologicalSpace G]

namespace DegreeData

section ConjugateFrobeniusQuotients

attribute [local instance] finiteReciprocityNaturalityConjugateInertia_normal


/-- The continuous conjugation equivalence identifies the two closed cyclic
subgroups generated by corresponding Frobenius lifts. -/
theorem finiteReciprocityNaturalityFrobeniusConjugationEquiv_mem_closure_iff
    (D : DegreeData G) [IsTopologicalGroup G]
    (K : FiniteResidueAbstractField D) (L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.field.toSubgroup) (s : G)
    [hLnormal : (extensionSubgroup K.field L hLK).Normal]
    (σ : D.FrobeniusElements K L hLK)
    (q : K.field.toSubgroup ⧸ D.extensionInertiaWithin K.field L hLK) :
    q ∈ (D.frobeniusClosure K L hLK σ).toSubgroup ↔
      D.finiteReciprocityNaturalityFrobeniusConjugationEquiv K.field L hLK s q ∈
        (D.frobeniusClosure
          (K.conjugate s : D.FiniteResidueAbstractField)
          (conjugateClosedSubgroup L s)
          (conjugateClosedSubgroup_mono hLK s)
          (D.finiteReciprocityNaturalityFrobeniusConjugationLift
            K L hLK s σ)).toSubgroup := by
  let e := D.finiteReciprocityNaturalityFrobeniusConjugationEquiv K.field L hLK s
  constructor
  · intro hq
    have hmap := map_mem_closedSubgroupGenerated_singleton
      (ContinuousMonoidHom.toContinuousMonoidHom e) σ.1 (by
        simpa [DegreeData.frobeniusClosure] using hq)
    unfold DegreeData.frobeniusClosure
    unfold DegreeData.FiniteResidueAbstractField.conjugate
    rw [D.finiteReciprocityNaturalityFrobeniusConjugationLift_coe]
    simpa [e] using hmap
  · intro hq
    have hq' : e q ∈ closedSubgroupGenerated {e σ.1} := by
      unfold DegreeData.frobeniusClosure at hq
      unfold DegreeData.FiniteResidueAbstractField.conjugate at hq
      rw [D.finiteReciprocityNaturalityFrobeniusConjugationLift_coe] at hq
      change e q ∈ (closedSubgroupGenerated {e σ.1}).toSubgroup
      simpa [e] using hq
    have hmap := map_mem_closedSubgroupGenerated_singleton
      (ContinuousMonoidHom.toContinuousMonoidHom e.symm)
      (D.finiteReciprocityNaturalityFrobeniusConjugationLift K L hLK s σ).1
      (by
        rw [D.finiteReciprocityNaturalityFrobeniusConjugationLift_coe]
        exact hq')
    simpa [DegreeData.frobeniusClosure,
      D.finiteReciprocityNaturalityFrobeniusConjugationLift_coe, e] using hmap

/-- The fixed field of the conjugated Frobenius lift is the conjugate of
the original fixed field. -/
theorem finiteReciprocityNaturalityFrobeniusFixedField_conjugate
    (D : DegreeData G) [IsTopologicalGroup G]
    (K : FiniteResidueAbstractField D) (L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.field.toSubgroup) (s : G)
    [hLnormal : (extensionSubgroup K.field L hLK).Normal]
    (σ : D.FrobeniusElements K L hLK) :
    conjugateClosedSubgroup (D.frobeniusFixedField K L hLK σ) s =
      D.frobeniusFixedField
        (K.conjugate s : D.FiniteResidueAbstractField)
        (conjugateClosedSubgroup L s)
        (conjugateClosedSubgroup_mono hLK s)
        (D.finiteReciprocityNaturalityFrobeniusConjugationLift K L hLK s σ) := by
  ext g
  change (g ∈ conjugateClosedSubgroup
      (D.frobeniusFixedField K L hLK σ) s) ↔
    g ∈ D.frobeniusFixedField
      (K.conjugate s : D.FiniteResidueAbstractField)
      (conjugateClosedSubgroup L s)
      (conjugateClosedSubgroup_mono hLK s)
      (D.finiteReciprocityNaturalityFrobeniusConjugationLift K L hLK s σ)
  rw [conjugateClosedSubgroup_mem]
  constructor
  · rintro ⟨k, hk, hkg⟩
    let ks : (K.conjugate s : D.FiniteResidueAbstractField).field.toSubgroup :=
      conjugateSubgroupEquiv K.field s k
    have hksg : ks.1 = g := by
      dsimp [ks]
      change (k : G) = s * g * s⁻¹ at hkg
      rw [hkg]
      simp [mul_assoc]
    have hkClosure : QuotientGroup.mk k ∈
        (D.frobeniusClosure K L hLK σ).toSubgroup :=
      (D.mem_frobeniusFixedSubgroupWithin_iff K L hLK σ k).1 hk
    have hksClosure : QuotientGroup.mk ks ∈
        (D.frobeniusClosure
          (K.conjugate s : D.FiniteResidueAbstractField)
          (conjugateClosedSubgroup L s)
          (conjugateClosedSubgroup_mono hLK s)
          (D.finiteReciprocityNaturalityFrobeniusConjugationLift
            K L hLK s σ)).toSubgroup := by
      have hmap :=
        (D.finiteReciprocityNaturalityFrobeniusConjugationEquiv_mem_closure_iff
          K L hLK s σ (QuotientGroup.mk k)).1 hkClosure
      have hmk :
          D.finiteReciprocityNaturalityFrobeniusConjugationEquiv
              K.field L hLK s (QuotientGroup.mk k) =
            QuotientGroup.mk ks := by
        apply QuotientGroup.eq_iff_div_mem.mpr
        simp [ks]
      rw [hmk] at hmap
      exact hmap
    refine ⟨ks, ?_, hksg⟩
    exact (D.mem_frobeniusFixedSubgroupWithin_iff
      (K.conjugate s : D.FiniteResidueAbstractField)
      (conjugateClosedSubgroup L s) (conjugateClosedSubgroup_mono hLK s)
      (D.finiteReciprocityNaturalityFrobeniusConjugationLift
        K L hLK s σ) ks).2 hksClosure
  · rintro ⟨ks, hks, hksg⟩
    let k : K.field.toSubgroup :=
      (conjugateSubgroupEquiv K.field s).symm ks
    have hkValue : k.1 = s * g * s⁻¹ := by
      dsimp [k]
      change (ks : G) = g at hksg
      change s * (ks : G) * s⁻¹ = s * g * s⁻¹
      rw [hksg]
    have hksClosure : QuotientGroup.mk ks ∈
        (D.frobeniusClosure
          (K.conjugate s : D.FiniteResidueAbstractField)
          (conjugateClosedSubgroup L s)
          (conjugateClosedSubgroup_mono hLK s)
          (D.finiteReciprocityNaturalityFrobeniusConjugationLift
            K L hLK s σ)).toSubgroup :=
      (D.mem_frobeniusFixedSubgroupWithin_iff
        (K.conjugate s : D.FiniteResidueAbstractField)
        (conjugateClosedSubgroup L s) (conjugateClosedSubgroup_mono hLK s)
        (D.finiteReciprocityNaturalityFrobeniusConjugationLift
          K L hLK s σ) ks).1 hks
    have hkClosure : QuotientGroup.mk k ∈
        (D.frobeniusClosure K L hLK σ).toSubgroup := by
      apply (D.finiteReciprocityNaturalityFrobeniusConjugationEquiv_mem_closure_iff
        K L hLK s σ (QuotientGroup.mk k)).2
      have hmk :
          D.finiteReciprocityNaturalityFrobeniusConjugationEquiv
              K.field L hLK s (QuotientGroup.mk k) =
            QuotientGroup.mk ks := by
        exact congrArg
          (QuotientGroup.mk' (D.extensionInertiaWithin
            (conjugateClosedSubgroup K.field s)
            (conjugateClosedSubgroup L s)
            (conjugateClosedSubgroup_mono hLK s)))
          ((conjugateSubgroupEquiv K.field s).apply_symm_apply ks)
      rw [hmk]
      exact hksClosure
    refine ⟨k, ?_, hkValue⟩
    exact (D.mem_frobeniusFixedSubgroupWithin_iff K L hLK σ k).2 hkClosure

end ConjugateFrobeniusQuotients

end DegreeData

end GroupOnly

section Representation

/-! Mathlib's `Rep ℤ G` forces its representation-bearing group `G` to `Type 0`. -/
variable {G : IntegralRepGroupType} [Group G] [TopologicalSpace G]

namespace DegreeData

/-- Normality of a conjugated finite abstract field is available without
unfolding the finite-field bundle. -/
instance finiteReciprocityNaturalityFiniteAbstractConjugate_normal
    [IsTopologicalGroup G]
    (K : FiniteAbstractField G) (L : ClosedSubgroup G)
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

theorem finiteReciprocityNaturality_isPrimeElement_transport
    (D : DegreeData G) {A : Rep ℤ G} (v : ValuationData D A)
    (S T : FiniteAbstractField G) (hST : S.field = T.field)
    (π : ambientFixedAddSubgroup A S.field) (hπ : v.IsPrimeElement S π) :
    v.IsPrimeElement T (hST ▸ π) := by
  cases S
  cases T
  cases hST
  simpa only using hπ

theorem finiteReciprocityNaturality_relativeNorm_right_transport
    (A : Rep ℤ G) (K S T : ClosedSubgroup G) (hST : S = T)
    (hSK : S.toSubgroup ≤ K.toSubgroup)
    (hTK : T.toSubgroup ≤ K.toSubgroup)
    [hKSfinite : Finite
      (K.toSubgroup ⧸ extensionSubgroup K S hSK)]
    [hKTfinite : Finite
      (K.toSubgroup ⧸ extensionSubgroup K T hTK)]
    (π : ambientFixedAddSubgroup A S) :
    relativeNorm A K S hSK π =
      relativeNorm A K T hTK (hST ▸ π) := by
  subst T
  rfl

section ConjugateFiniteNormQuotient

attribute [local instance] finiteReciprocityNaturalityConjugateNormAddZero


/-- **norm--conjugation naturality, second diagram.** Conjugation of finite Galois
groups corresponds under the finite reciprocity equivalence to conjugation of finite norm
classes. -/
theorem finiteReciprocityNaturality_conjugation_commutes
    (D : DegreeData G) (A : Rep ℤ G) (v : ValuationData D A)
    [IsTopologicalGroup G] [CompactSpace G] [T2Space G]
    [TotallyDisconnectedSpace G]
    (hAxiom : v.SatisfiesUnramifiedUnitCohomology D)
    (K : FiniteAbstractField G) (L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.field.toSubgroup) (s : G)
    [hLnormal : (extensionSubgroup K.field L hLK).Normal]
    [hLfinite : Finite
      (K.field.toSubgroup ⧸ extensionSubgroup K.field L hLK)] :
    let Ks : FiniteAbstractField G := K.conjugate s
    let Ls := conjugateClosedSubgroup L s
    let hLsKs := conjugateClosedSubgroup_mono hLK s
    letI : Finite
        (Ks.field.toSubgroup ⧸ extensionSubgroup Ks.field Ls hLsKs) :=
      finite_conjugateExtension K.field L hLK s
    (finiteReciprocityNaturalityConjugationNormMap A K.field L hLK s).comp
        (D.finiteReciprocityHom A v hAxiom K L hLK) =
      (D.finiteReciprocityHom A v hAxiom Ks Ls hLsKs).comp
        (finiteReciprocityNaturalityConjugation K.field L hLK s).toMonoidHom.toAdditive := by
  dsimp only
  let hLsfinite : Finite
      ((conjugateClosedSubgroup K.field s).toSubgroup ⧸
        extensionSubgroup (conjugateClosedSubgroup K.field s)
          (conjugateClosedSubgroup L s)
          (conjugateClosedSubgroup_mono hLK s)) :=
    finite_conjugateExtension K.field L hLK s
  let KR : D.FiniteResidueAbstractField :=
    K.toFiniteResidueAbstractField D
  let Ks : FiniteAbstractField G := K.conjugate s
  let KRs : D.FiniteResidueAbstractField :=
    Ks.toFiniteResidueAbstractField D
  have hKRs_conjugate : KR.conjugate s = KRs := by
    dsimp [KRs, Ks, KR]
    unfold FiniteAbstractField.toFiniteResidueAbstractField
    unfold FiniteAbstractField.conjugate
    unfold DegreeData.FiniteResidueAbstractField.conjugate
    rfl
  let hLsfiniteKs : Finite
      (Ks.field.toSubgroup ⧸
        extensionSubgroup Ks.field (conjugateClosedSubgroup L s)
          (conjugateClosedSubgroup_mono hLK s)) := by
    change Finite
      ((conjugateClosedSubgroup K.field s).toSubgroup ⧸
        extensionSubgroup (conjugateClosedSubgroup K.field s)
          (conjugateClosedSubgroup L s)
          (conjugateClosedSubgroup_mono hLK s))
    exact hLsfinite
  let hLsfiniteKRs : Finite
      (KRs.field.toSubgroup ⧸
        extensionSubgroup KRs.field (conjugateClosedSubgroup L s)
          (conjugateClosedSubgroup_mono hLK s)) := by
    simpa only [KRs, FiniteAbstractField.toFiniteResidueAbstractField] using
      hLsfiniteKs
  let hLnormalKR : (extensionSubgroup KR.field L hLK).Normal := by
    simpa only [KR, FiniteAbstractField.toFiniteResidueAbstractField] using
      hLnormal
  let hLsnormalKs :
      (extensionSubgroup Ks.field (conjugateClosedSubgroup L s)
        (conjugateClosedSubgroup_mono hLK s)).Normal := by
    change
      (extensionSubgroup (conjugateClosedSubgroup K.field s)
        (conjugateClosedSubgroup L s)
        (conjugateClosedSubgroup_mono hLK s)).Normal
    infer_instance
  let hLsnormalKRs :
      (extensionSubgroup KRs.field (conjugateClosedSubgroup L s)
        (conjugateClosedSubgroup_mono hLK s)).Normal := by
    simpa only [KRs, FiniteAbstractField.toFiniteResidueAbstractField] using
      hLsnormalKs
  apply AddMonoidHom.ext
  intro q
  let σ := D.chosenFiniteReciprocityFrobeniusLift KR L hLK q.toMul
  let σs : D.FrobeniusElements KRs
      (conjugateClosedSubgroup L s)
      (conjugateClosedSubgroup_mono hLK s) := by
    subst KRs
    exact D.finiteReciprocityNaturalityFrobeniusConjugationLift
      KR L hLK s σ
  have hσ : D.frobeniusRestriction KR L hLK σ = q.toMul :=
    D.frobeniusRestriction_chosenFiniteReciprocityFrobeniusLift
      KR L hLK q.toMul
  have hσs : D.frobeniusRestriction KRs
      (conjugateClosedSubgroup L s)
      (conjugateClosedSubgroup_mono hLK s) σs =
      ((finiteReciprocityNaturalityConjugation
        K.field L hLK s).toMonoidHom.toAdditive q).toMul := by
    change D.frobeniusRestriction KRs
        (conjugateClosedSubgroup L s)
        (conjugateClosedSubgroup_mono hLK s) σs =
      finiteReciprocityNaturalityConjugation K.field L hLK s q.toMul
    rw [← hσ]
    symm
    change finiteReciprocityNaturalityConjugation K.field L hLK s
        (D.extensionRestriction KR.field L hLK σ.1) =
      D.extensionRestriction KRs.field
        (conjugateClosedSubgroup L s)
        (conjugateClosedSubgroup_mono hLK s) σs.1
    unfold σs
    cases hKRs_conjugate
    dsimp only [id]
    rw [D.finiteReciprocityNaturalityFrobeniusConjugationLift_coe]
    refine Quotient.inductionOn' σ.1 ?_
    intro k
    rfl
  let S := D.frobeniusFixedField KR L hLK σ
  let Ss := D.frobeniusFixedField KRs
    (conjugateClosedSubgroup L s)
    (conjugateClosedSubgroup_mono hLK s) σs
  let hSK := D.frobeniusFixedField_le KR L hLK σ
  let hSsKs := D.frobeniusFixedField_le KRs
    (conjugateClosedSubgroup L s)
    (conjugateClosedSubgroup_mono hLK s) σs
  have hConjS : conjugateClosedSubgroup S s = Ss := by
    exact D.finiteReciprocityNaturalityFrobeniusFixedField_conjugate
      KR L hLK s σ
  let hSKfinite : Finite
      (K.field.toSubgroup ⧸ extensionSubgroup K.field S hSK) :=
    D.frobeniusFixedField_finite KR L hLK σ
  let hConjSKfinite : Finite
      (Ks.field.toSubgroup ⧸
        extensionSubgroup Ks.field
          (conjugateClosedSubgroup S s)
          (conjugateClosedSubgroup_mono hSK s)) :=
    by
      change Finite
        ((conjugateClosedSubgroup K.field s).toSubgroup ⧸
          extensionSubgroup (conjugateClosedSubgroup K.field s)
            (conjugateClosedSubgroup S s)
            (conjugateClosedSubgroup_mono hSK s))
      exact finite_conjugateExtension K.field S hSK s
  let hSsKsfinite : Finite
      (Ks.field.toSubgroup ⧸ extensionSubgroup Ks.field Ss hSsKs) :=
    D.frobeniusFixedField_finite KRs
      (conjugateClosedSubgroup L s)
      (conjugateClosedSubgroup_mono hLK s) σs
  let Sfinite : FiniteAbstractField G :=
    { field := S
      finite := D.frobeniusFixedField_absoluteFinite K L hLK σ }
  let Ssfinite : FiniteAbstractField G :=
    { field := Ss
      finite := D.frobeniusFixedField_absoluteFinite Ks
        (conjugateClosedSubgroup L s)
        (conjugateClosedSubgroup_mono hLK s) σs }
  let π : ambientFixedAddSubgroup A S := v.chosenPrimeElement Sfinite
  have hπ : v.IsPrimeElement Sfinite π := v.chosenPrimeElement_isPrime Sfinite
  let πs0 : ambientFixedAddSubgroup A (conjugateClosedSubgroup S s) :=
    conjugateFixedElement A S s π
  have hπs0 : v.IsPrimeElement (Sfinite.conjugate s) πs0 := by
    change v.valuationAt (Sfinite.conjugate s) πs0 = v.oneValue
    rw [show v.valuationAt (Sfinite.conjugate s) πs0 =
        v.valuationAt Sfinite π by
      simpa [Sfinite, πs0] using
        v.normalizedValuation_conjugate Sfinite s π]
    exact hπ
  let πs : ambientFixedAddSubgroup A Ss := hConjS ▸ πs0
  have hπs : v.IsPrimeElement Ssfinite πs := by
    have htransport :=
      D.finiteReciprocityNaturality_isPrimeElement_transport v
        (Sfinite.conjugate s) Ssfinite (by exact hConjS) πs0 hπs0
    unfold πs
    exact htransport
  change finiteReciprocityNaturalityConjugationNormMap A K.field L hLK s
      (D.finiteReciprocityHom A v hAxiom K L hLK q) =
    D.finiteReciprocityHom A v hAxiom Ks
      (conjugateClosedSubgroup L s)
      (conjugateClosedSubgroup_mono hLK s)
      ((finiteReciprocityNaturalityConjugation
        K.field L hLK s).toMonoidHom.toAdditive q)
  have hprimeNorm :
      finiteReciprocityNaturalityConjugationNormMap A K.field L hLK s
        (D.finiteReciprocityHom A v hAxiom K L hLK q) =
      finiteReciprocityNaturalityConjugationNormMap A K.field L hLK s
        (finiteNormClass A K.field L hLK
          (relativeNorm A K.field S hSK π)) := by
    rw [D.finiteReciprocityHom_apply_eq_primeNormClass
      A v hAxiom K L hLK q σ hσ π hπ]
  have hconjugateNorm :
      finiteReciprocityNaturalityConjugationNormMap A K.field L hLK s
        (finiteNormClass A K.field L hLK
          (relativeNorm A K.field S hSK π)) =
      finiteNormClass A Ks.field
        (conjugateClosedSubgroup L s)
        (conjugateClosedSubgroup_mono hLK s)
        (relativeNorm A Ks.field
          (conjugateClosedSubgroup S s)
          (conjugateClosedSubgroup_mono hSK s) πs0) := by
    exact finiteReciprocityNaturality_conjugation_norm_class
      A K.field L S hLK hSK s π
  have htransportNorm :
      finiteNormClass A Ks.field
        (conjugateClosedSubgroup L s)
        (conjugateClosedSubgroup_mono hLK s)
        (relativeNorm A Ks.field
          (conjugateClosedSubgroup S s)
          (conjugateClosedSubgroup_mono hSK s) πs0) =
      finiteNormClass A Ks.field
        (conjugateClosedSubgroup L s)
        (conjugateClosedSubgroup_mono hLK s)
        (relativeNorm A Ks.field Ss hSsKs πs) := by
    apply congrArg (finiteNormClass A Ks.field
      (conjugateClosedSubgroup L s)
      (conjugateClosedSubgroup_mono hLK s))
    have htransport :=
      finiteReciprocityNaturality_relativeNorm_right_transport A
        Ks.field (conjugateClosedSubgroup S s) Ss
        hConjS (conjugateClosedSubgroup_mono hSK s) hSsKs πs0
    simpa [πs] using htransport
  have hconjugatePrimeNorm :
      finiteNormClass A Ks.field
        (conjugateClosedSubgroup L s)
        (conjugateClosedSubgroup_mono hLK s)
        (relativeNorm A Ks.field Ss hSsKs πs) =
      D.finiteReciprocityHom A v hAxiom Ks
        (conjugateClosedSubgroup L s)
        (conjugateClosedSubgroup_mono hLK s)
        ((finiteReciprocityNaturalityConjugation
          K.field L hLK s).toMonoidHom.toAdditive q) := by
    rw [D.finiteReciprocityHom_apply_eq_primeNormClass
      A v hAxiom Ks
      (conjugateClosedSubgroup L s)
      (conjugateClosedSubgroup_mono hLK s)
      _ σs hσs πs hπs]
  exact hprimeNorm.trans (hconjugateNorm.trans (htransportNorm.trans hconjugatePrimeNorm))

end ConjugateFiniteNormQuotient

end DegreeData

end Representation

end

end ClassFormation
end

section
-- module Solutions.OAIQ244_DUKE.AbstractClassFieldTheory_Reciprocity_Construction_MainTransfer
attribute [-instance] _root_.ClassFormation.FiniteGaloisSubextension.extensionSubgroup_over_intermediate_normalInstance _root_.ClassFormation.FiniteGaloisSubextension.intermediateField_normalInstance _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalClassFieldTheory.baseFixingExtensionQuotient_finite _root_.LocalClassFieldTheory.extensionSubgroupBase_normal _root_.LocalClassFieldTheory.finiteGaloisExtensionSubgroupOfEmbedding_normal _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.LubinTate.compatibleGroupFamiliesGroup _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.LocalClassFieldTheory.normalizationIntegerRingIsIntegralClosure _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen
attribute [-simp] _root_.ClassFormation.FiniteAbelianSubextension.extensionQuotientMk_apply _root_.ClassFormation.FiniteGaloisSubextension.classFieldCandidate_field _root_.ClassFormation.cyclicNormClassHom_apply _root_.ClassFormation.extensionFixedRepresentationEquiv_apply_coe _root_.ClassFormation.extensionFixedRepresentationEquiv_symm_apply_coe _root_.ClassFormation.mem_normFilterBasis_iff _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.IsDiscreteValuationRing.addVal_ringEquiv _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.LocalClassFieldTheory.baseFixingExtensionQuotientEquivAmbient_mk _root_.LocalClassFieldTheory.baseUnitsEquivGaloisAmbientFixed_val _root_.LocalClassFieldTheory.embeddedFieldUnitsEquivGaloisFixed_coe _root_.LocalClassFieldTheory.finiteGaloisUnitsEquivAbstractFixedOfEmbedding_coe _root_.LocalClassFieldTheory.finiteGaloisUnitsEquivAbstractFixed_coe _root_.LocalClassFieldTheory.intermediateFieldUnitsEquivGaloisFixed_coe _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.LocalFieldTheory.residueField_algebraMap_residue _root_.OAI.PrimeDegreePackets.ThetaConstruction.schwartzCM_apply _root_.infinitePlace_mult_smul
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

section Representation

/-! Mathlib's `Rep ℤ G` forces its representation-bearing group `G` to `Type 0`. -/
variable {G : IntegralRepGroupType} [Group G] [TopologicalSpace G]

/-- The right vertical arrow of transfer--norm naturality: inclusion `A_K → A_{K'}`
descended to the actual finite norm quotients. -/
def transferNormNaturalityNormQuotientInclusion
    (A : Rep ℤ G) (K K' L : ClosedSubgroup G)
    (hLK' : L.toSubgroup ≤ K'.toSubgroup)
    (hK'K : K'.toSubgroup ≤ K.toSubgroup)
    [hLnormal : (extensionSubgroup K L (hLK'.trans hK'K)).Normal]
    [hL'normal : (extensionSubgroup K' L hLK').Normal]
    [Finite (K.toSubgroup ⧸
      extensionSubgroup K L (hLK'.trans hK'K))] :
    letI : Finite (K'.toSubgroup ⧸ extensionSubgroup K' L hLK') :=
      Finite.of_injective
        (transferNormNaturalityIntermediateInclusion K K' L hLK' hK'K)
        (transferNormNaturalityIntermediateInclusion_injective
          K K' L hLK' hK'K)
    FiniteNormQuotient A K L (hLK'.trans hK'K) →+
      FiniteNormQuotient A K' L hLK' := by
  letI hL'finite : Finite
      (K'.toSubgroup ⧸ extensionSubgroup K' L hLK') :=
    Finite.of_injective
      (transferNormNaturalityIntermediateInclusion K K' L hLK' hK'K)
      (transferNormNaturalityIntermediateInclusion_injective
        K K' L hLK' hK'K)
  let targetClass : ambientFixedAddSubgroup A K →+
      FiniteNormQuotient A K' L hLK' :=
    (finiteNormClassHom A K' L hLK').comp
      (fixedFieldInclusion A K K' hK'K)
  refine finiteNormQuotientLift A K L (hLK'.trans hK'K) targetClass ?_
  rintro _ ⟨a, rfl⟩
  apply (finiteNormClass_eq_zero_iff A K' L hLK' _).2
  refine ⟨transferNormNaturalityNormWitness A K K' L hLK' hK'K a, ?_⟩
  exact (transferNormNaturality_norm_doubleCoset_formula
    A K K' L hLK' hK'K a).symm

/-- The transfer-side map sends a finite norm class to the class of its fixed-field inclusion. -/
@[simp]
theorem transferNormNaturality_normQuotientInclusion_finiteNormClass
    (A : Rep ℤ G) (K K' L : ClosedSubgroup G)
    (hLK' : L.toSubgroup ≤ K'.toSubgroup)
    (hK'K : K'.toSubgroup ≤ K.toSubgroup)
    [hLnormal : (extensionSubgroup K L (hLK'.trans hK'K)).Normal]
    [Finite (K.toSubgroup ⧸
      extensionSubgroup K L (hLK'.trans hK'K))]
    (x : ambientFixedAddSubgroup A K) :
    letI : (extensionSubgroup K' L hLK').Normal :=
      transferNormNaturality_intermediateExtension_normal K K' L hLK' hK'K
    letI : Finite (K'.toSubgroup ⧸ extensionSubgroup K' L hLK') :=
      Finite.of_injective
        (transferNormNaturalityIntermediateInclusion K K' L hLK' hK'K)
        (transferNormNaturalityIntermediateInclusion_injective
          K K' L hLK' hK'K)
    transferNormNaturalityNormQuotientInclusion A K K' L hLK' hK'K
        (finiteNormClass A K L (hLK'.trans hK'K) x) =
      finiteNormClass A K' L hLK'
        (fixedFieldInclusion A K K' hK'K x) := by
  let hL'normal : (extensionSubgroup K' L hLK').Normal :=
    transferNormNaturality_intermediateExtension_normal K K' L hLK' hK'K
  let hL'finite : Finite
      (K'.toSubgroup ⧸ extensionSubgroup K' L hLK') :=
    Finite.of_injective
      (transferNormNaturalityIntermediateInclusion K K' L hLK' hK'K)
      (transferNormNaturalityIntermediateInclusion_injective
        K K' L hLK' hK'K)
  unfold transferNormNaturalityNormQuotientInclusion
  rw [finiteNormQuotientLift_finiteNormClass]
  rfl

end Representation

end

end ClassFormation
end

section
-- module Solutions.OAIQ244_DUKE.AbstractClassFieldTheory_Reciprocity_Core
attribute [-instance] _root_.ClassFormation.FiniteGaloisSubextension.extensionSubgroup_over_intermediate_normalInstance _root_.ClassFormation.FiniteGaloisSubextension.intermediateField_normalInstance _root_.ClassFormation.FiniteGaloisSubextension.intermediateSubgroup_normalInstance _root_.ClassFormation.FiniteGaloisSubextension.upperQuotient_groupInstance _root_.ClassFormation.instIsAddTorsionFreeZHat _root_.ClassFormation.instIsMulTorsionFreeMultiplicativeZHat _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.KummerTheory.finite_finsupp_nsmulQuotient _root_.LocalClassFieldTheory.baseFixingExtensionQuotient_finite _root_.LocalClassFieldTheory.extensionSubgroupBase_normal _root_.LocalClassFieldTheory.finiteGaloisExtensionSubgroupOfEmbedding_normal _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitQuotientCarrier_finite _root_.LocalFieldTheory.DiscreteValuationField.finite_padicInt_finPi_nsmulQuotient _root_.LocalFieldTheory.DiscreteValuationField.finite_padicInt_pi_nsmulQuotient_of_coprime _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_multiplicative_nthPowerQuotient _root_.LocalFieldTheory.finite_nsmulAddQuotient_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.LubinTate.compatibleGroupFamiliesGroup _root_.OAI.PrimeDegreePackets.boundedRealFields_finite _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.RayClass.approximationCompletionTopologicalSpace _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.maximalIdealPowSuccQuotModule _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.LocalClassFieldTheory.normalizationIntegerRingIsIntegralClosure _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen
attribute [-simp] _root_.ClassFormation.FiniteAbelianSubextension.extensionQuotientMk_apply _root_.ClassFormation.FiniteGaloisSubextension.classFieldCandidate_field _root_.ClassFormation.mem_normFilterBasis_iff _root_.ClassFormation.toZModPow_zHatToPadicInt _root_.ClassFormation.zHatReductionRingHom_apply _root_.ClassFormation.zHatRingEquivProfiniteIntegerPrimeProduct_apply _root_.ClassFormation.zHatToPadicInt_intCast _root_.ClassFormation.zHatToProfiniteIntegerPrimeProduct_apply _root_.ClassFormation.zHatToProfiniteIntegerPrimeProduct_intCast _root_.ClassFormation.zHatUnitsContinuousMulEquivPrimeProduct_coe_apply _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.IsDiscreteValuationRing.addVal_ringEquiv _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.KummerTheory.torsionQuotientEquivOfZHatMulDecomposition_mk _root_.KummerTheory.zHatUnitsContinuousMulEquivPrimeProduct_rationalCyclotomicCharacter _root_.LocalClassFieldTheory.baseFixingExtensionQuotientEquivAmbient_mk _root_.LocalClassFieldTheory.baseUnitsEquivGaloisAmbientFixed_val _root_.LocalClassFieldTheory.embeddedFieldUnitsEquivGaloisFixed_coe _root_.LocalClassFieldTheory.finiteGaloisUnitsEquivAbstractFixedOfEmbedding_coe _root_.LocalClassFieldTheory.finiteGaloisUnitsEquivAbstractFixed_coe _root_.LocalClassFieldTheory.finiteResidueFrobeniusFromZHat_apply _root_.LocalClassFieldTheory.finiteResidueFrobeniusFromZHat_one _root_.LocalClassFieldTheory.intermediateFieldUnitsEquivGaloisFixed_coe _root_.LocalClassFieldTheory.intrinsicFiniteAbstractBase_eq_base _root_.LocalClassFieldTheory.residueAbsoluteDegreeIn_frobenius _root_.LocalClassFieldTheory.residueAbsoluteFrobenius_one _root_.LocalClassFieldTheory.residueFrobeniusToLimit_apply_component _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.LocalFieldTheory.residueField_algebraMap_residue _root_.OAI.PrimeDegreePackets.ThetaConstruction.schwartzCM_apply _root_.infinitePlace_mult_smul
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

namespace ClassFormation

open KummerTheory

open CyclicCohomology

/-!
# Abstract reciprocity, the unramified cohomology consequence

The class field axiom implies the unit-cohomology axiom for every finite unramified
extension.  The proof follows: degree minus one is reduced to
the corresponding assertion for `A_L`, after correcting a primitive by an
element of `A_K` with the same valuation; in degree zero, valuation induces
a surjection from `A_K / N A_L` to `Z / [L : K] Z`, and equality of the two
orders makes this map injective.
-/

noncomputable section

open CategoryTheory

-- Mathlib's `Rep ℤ G` currently fixes the acting group to universe zero.
variable {G : IntegralRepGroupType} [Group G] [TopologicalSpace G]
variable {D : DegreeData G} {A : Rep ℤ G}

namespace ValuationData

theorem valueModulo_nsmul
    (v : ValuationData D A) (n : ℕ) (hn : 0 < n)
    (z : v.valueGroup) :
    v.valueModulo n hn (n • z) = 0 := by
  have hq :
      (QuotientAddGroup.mk' (nsmulWithin v.valueGroup n)) (n • z) = 0 := by
    apply (QuotientAddGroup.eq_zero_iff _).2
    exact ⟨z, rfl⟩
  change (v.cyclic_value_quotients n hn)
      ((QuotientAddGroup.mk' (nsmulWithin v.valueGroup n)) (n • z)) = 0
  rw [hq, map_zero]

theorem classFieldAxiom_unramifiedUnits_hMinusOne
    (v : ValuationData D A) (hcf : SatisfiesClassFieldAxiom A)
    (E : FiniteAbstractFieldExtension G)
    (hnormal : (extensionSubgroup E.base.field E.field.field E.below).Normal)
    (hUnramified : E.IsUnramified D)
    (g : E.base.field.toSubgroup ⧸
      extensionSubgroup E.base.field E.field.field E.below)
    (hg : ∀ x, x ∈ Subgroup.zpowers g) :
    letI := Fintype.ofFinite
      (E.base.field.toSubgroup ⧸
        extensionSubgroup E.base.field E.field.field E.below)
    Limits.IsZero
      (tateCohomology (v.unitRepresentation E hnormal) (-1)) := by
  let K := E.base.field
  let L := E.field.field
  let hLK := E.below
  let := hnormal
  let := Fintype.ofFinite
    (K.toSubgroup ⧸ extensionSubgroup K L hLK)
  let : IsCyclic (K.toSubgroup ⧸ extensionSubgroup K L hLK) :=
    isCyclic_of_generator g hg
  let : CommGroup (K.toSubgroup ⧸ extensionSubgroup K L hLK) :=
    IsCyclic.commGroup
  let U := v.unitRepresentation E hnormal
  let M := extensionFixedRepresentation A K L hLK hnormal
  let S := Rep.FiniteCyclicGroup.subCompNormHom U g
  let Kcf : FiniteAbstractField G := E.base
  let Ecf : FiniteCyclicSubextension Kcf :=
    { field := L
      below := hLK
      normal := hnormal
      finite := inferInstance
      generator := g
      generates := hg }
  have hMzero : Limits.IsZero (tateCohomology M (-1)) :=
    by
      simpa [Kcf, Ecf,
        FiniteCyclicSubextension.fixedRepresentation] using
          hcf.tateHMinusOne_isZero Kcf Ecf
  have hExact : S.Exact := by
    rw [S.moduleCat_exact_iff]
    intro u hu
    have huNorm : U.norm.hom u = 0 := by
      simpa [S] using hu
    let uM : M.V :=
      (extensionFixedRepresentationEquiv A K L hLK hnormal).symm u.1
    have huMNorm : M.norm.hom uM = 0 := by
      apply Subtype.ext
      calc
        (M.norm.hom uM).1 =
            ((relativeNorm A K L hLK
              (extensionFixedRepresentationEquiv A K L hLK hnormal uM) :
                ambientFixedAddSubgroup A K) : A.V) :=
          extensionFixedRepresentation_norm_coe A K L hLK hnormal uM
        _ = ((relativeNorm A K L hLK u.1 :
                ambientFixedAddSubgroup A K) : A.V) := by
          rfl
        _ = ((((U.norm.hom u).1 : ambientFixedAddSubgroup A L)) : A.V) :=
          (v.unitRepresentation_norm_coe E hnormal u).symm
        _ = 0 := by rw [huNorm]; rfl
    obtain ⟨a, ha⟩ :=
      CyclicCohomology.normKernel_le_sigmaMinusOneRange_of_tateHMinusOne_isZero
        M g hg hMzero uM huMNorm
    let aL : ambientFixedAddSubgroup A L :=
      extensionFixedRepresentationEquiv A K L hLK hnormal a
    obtain ⟨b, hb⟩ :=
      v.normalizedValuation_surjective E.base (v.valuationAt E.field aL)
    let bL : ambientFixedAddSubgroup A L :=
      fixedFieldInclusion A K L hLK b
    let eL : ambientFixedAddSubgroup A L := aL - bL
    have heL : v.valuationAt E.field eL = 0 := by
      change v.valuationAt E.field (aL - bL) = 0
      rw [map_sub,
        v.valuationAt_fixedFieldInclusion_of_unramified E hUnramified b,
        hb, sub_self]
    let e : U.V := ⟨eL, (v.mem_unitAddSubgroup_iff E.field eL).2 heL⟩
    refine ⟨e, ?_⟩
    have hactionSub :
        relativeCosetAction A K L hLK eL g =
          relativeCosetAction A K L hLK aL g -
            relativeCosetAction A K L hLK bL g := by
      refine Quotient.inductionOn' g ?_
      intro k
      rw [relativeCosetAction_mk, relativeCosetAction_mk,
        relativeCosetAction_mk]
      exact map_sub (A.ρ k.1) aL.1 bL.1
    have hactionB :
        relativeCosetAction A K L hLK bL g = bL.1 := by
      refine Quotient.inductionOn' g ?_
      intro k
      rw [relativeCosetAction_mk]
      exact b.2 k
    have hUaction :
        (((U.ρ g e).1 : ambientFixedAddSubgroup A L) : A.V) =
          relativeCosetAction A K L hLK eL g := by
      simpa [U] using
        v.unitRepresentation_action_coe E hnormal g e
    have hMaction :
        (M.ρ g a).1 = relativeCosetAction A K L hLK aL g := by
      simpa [M, aL] using
        extensionFixedRepresentation_action_coe A K L hLK hnormal g a
    apply Subtype.ext
    apply Subtype.ext
    calc
      ((((U.ρ g e - e).1 : ambientFixedAddSubgroup A L)) : A.V) =
          relativeCosetAction A K L hLK eL g - eL.1 := by
        change (((U.ρ g e).1 : ambientFixedAddSubgroup A L) : A.V) -
            ((e.1 : ambientFixedAddSubgroup A L) : A.V) = _
        rw [hUaction]
      _ = relativeCosetAction A K L hLK aL g - aL.1 := by
        rw [hactionSub, hactionB]
        change (_ - bL.1) - (aL.1 - bL.1) = _ - aL.1
        abel
      _ = (M.ρ g a - a).1 := by
        change _ = (M.ρ g a).1 - a.1
        rw [hMaction]
        rfl
      _ = uM.1 := congrArg Subtype.val ha
      _ = u.1.1 := rfl
  have hzeroS : Limits.IsZero S.homology :=
    (S.exact_iff_isZero_homology).1 hExact
  exact Limits.IsZero.of_iso hzeroS
    (TateCohomology.isoFiniteCyclicNegOne U g hg)

theorem classFieldAxiom_unramifiedUnits_hZero
    (v : ValuationData D A) (hcf : SatisfiesClassFieldAxiom A)
    (E : FiniteAbstractFieldExtension G)
    (hnormal : (extensionSubgroup E.base.field E.field.field E.below).Normal)
    (hUnramified : E.IsUnramified D)
    (g : E.base.field.toSubgroup ⧸
      extensionSubgroup E.base.field E.field.field E.below)
    (hg : ∀ x, x ∈ Subgroup.zpowers g) :
    letI := Fintype.ofFinite
      (E.base.field.toSubgroup ⧸
        extensionSubgroup E.base.field E.field.field E.below)
    Limits.IsZero
      (tateCohomology (v.unitRepresentation E hnormal) 0) := by
  let K := E.base.field
  let L := E.field.field
  let hLK := E.below
  let := hnormal
  let := Fintype.ofFinite
    (K.toSubgroup ⧸ extensionSubgroup K L hLK)
  let : IsCyclic (K.toSubgroup ⧸ extensionSubgroup K L hLK) :=
    isCyclic_of_generator g hg
  let : CommGroup (K.toSubgroup ⧸ extensionSubgroup K L hLK) :=
    IsCyclic.commGroup
  let n := (E.degree : ℕ)
  have hn : 0 < n := E.degree.property
  let M := extensionFixedRepresentation A K L hLK hnormal
  let instM : Module ℤ M.V := M.hV2
  let T := Rep.FiniteCyclicGroup.normHomCompSub M g
  let instTCycles : Module ℤ (LinearMap.ker T.g.hom) :=
    (LinearMap.ker T.g.hom).module
  let C := LinearMap.ker T.g.hom
  let cycleValAdd : C →+ ZMod n :=
    (v.valueModulo n hn).comp <|
      (v.valuationAt E.field).comp <|
        (extensionFixedRepresentationEquiv A K L hLK hnormal).toAddMonoidHom.comp
          C.subtype.toAddMonoidHom
  let cycleVal : C →ₗ[ℤ] ZMod n :=
    { toFun := cycleValAdd
      map_add' := cycleValAdd.map_add
      map_smul' := by
        intro m x
        simp only [RingHom.id_apply]
        convert! cycleValAdd.map_zsmul m x using 1
        all_goals try with_reducible_and_instances rfl
        exact congrArg cycleValAdd (int_smul_eq_zsmul ..) }
  have hcycleValNorm :
      LinearMap.range T.moduleCatToCycles ≤ LinearMap.ker cycleVal := by
    rintro x ⟨y, rfl⟩
    let yL : ambientFixedAddSubgroup A L :=
      extensionFixedRepresentationEquiv A K L hLK hnormal y
    let normK : ambientFixedAddSubgroup A K :=
      relativeNorm A K L hLK yL
    have hnormM :
        extensionFixedRepresentationEquiv A K L hLK hnormal (M.norm.hom y) =
          fixedFieldInclusion A K L hLK normK := by
      apply Subtype.ext
      exact extensionFixedRepresentation_norm_coe A K L hLK hnormal y
    have htower := v.normalizedValuation_tower E yL
    change (E.residueDegree D : ℕ) •
        ((v.valuationAt E.field yL : v.valueGroup) : ZHat) =
      ((v.valuationAt E.base
        (relativeNorm A E.base.field E.field.field E.below yL) :
          v.valueGroup) : ZHat) at htower
    rw [E.residueDegree_eq_degree_of_isUnramified D hUnramified] at htower
    have hvalNorm :
        v.valuationAt E.field
            (extensionFixedRepresentationEquiv A K L hLK hnormal
              (M.norm.hom y)) =
          n • v.valuationAt E.field yL := by
      rw [hnormM,
        v.valuationAt_fixedFieldInclusion_of_unramified E hUnramified normK]
      apply Subtype.ext
      exact htower.symm
    change v.valueModulo n hn
        (v.valuationAt E.field
          (extensionFixedRepresentationEquiv A K L hLK hnormal
            (M.norm.hom y))) = 0
    rw [hvalNorm]
    exact v.valueModulo_nsmul n hn (v.valuationAt E.field yL)
  let H := T.moduleCatLeftHomologyData.H
  let fieldVal : H →ₗ[ℤ] ZMod n :=
    (LinearMap.range T.moduleCatToCycles).liftQ cycleVal hcycleValNorm
  have hfieldValSurjective : Function.Surjective fieldVal := by
    intro z
    obtain ⟨c, hc⟩ := v.valueModulo_surjective n hn z
    obtain ⟨aK, haK⟩ := v.normalizedValuation_surjective E.base c
    let aL : ambientFixedAddSubgroup A L :=
      fixedFieldInclusion A K L hLK aK
    let aM : M.V :=
      (extensionFixedRepresentationEquiv A K L hLK hnormal).symm aL
    have haMfixed : M.ρ g aM = aM := by
      refine Quotient.inductionOn' g ?_
      intro k
      apply Subtype.ext
      change A.ρ k.1 aK.1 = aK.1
      exact aK.2 k
    have haMcycle : T.g aM = 0 := by
      change M.ρ g aM - aM = 0
      exact sub_eq_zero.mpr haMfixed
    let aCycle : C := ⟨aM, haMcycle⟩
    refine ⟨Submodule.mkQ (LinearMap.range T.moduleCatToCycles) aCycle, ?_⟩
    change v.valueModulo n hn (v.valuationAt E.field aL) = z
    rw [v.valuationAt_fixedFieldInclusion_of_unramified E hUnramified aK,
      haK]
    exact hc
  let homologyEquiv : H ≃ T.homology :=
    { toFun := fun x => T.moduleCatLeftHomologyData.homologyIso.inv x
      invFun := fun x => T.moduleCatLeftHomologyData.homologyIso.hom x
      left_inv := by intro x; simp
      right_inv := by intro x; simp }
  let eHTate : H ≃ tateCohomology M 0 :=
    homologyEquiv.trans
      (TateCohomology.isoFiniteCyclicZero M g hg).symm.toLinearEquiv.toEquiv
  let Kcf : FiniteAbstractField G := E.base
  let Ecf : FiniteCyclicSubextension Kcf :=
    { field := E.field.field
      below := E.below
      normal := hnormal
      finite := E.finiteQuotient
      generator := g
      generates := hg }
  let hEcfTateFinite :
      Finite (tateCohomology (Ecf.fixedRepresentation A) 0) :=
    (hcf Kcf Ecf).finiteTateHZero
  let hMTateFinite : Finite (tateCohomology M 0) := by
    simpa [M, K, L, hLK, Kcf, Ecf,
      FiniteCyclicSubextension.fixedRepresentation] using hEcfTateFinite
  let hHFinite : Finite H :=
    Finite.of_equiv (tateCohomology M 0) eHTate.symm
  have hcardT : Nat.card H = n := by
    calc
      Nat.card H = Nat.card (tateCohomology M 0) :=
        Nat.card_congr eHTate
      _ = n := by
        convert hcf.tateHZero_card Kcf Ecf using 1 <;>
          simp [n, M, K, L, Kcf, Ecf,
            FiniteCyclicSubextension.fixedRepresentation,
            FiniteCyclicSubextension.toFiniteAbstractExtension,
            FiniteAbstractFieldExtension.degree,
            FiniteAbstractFieldExtension.toFiniteAbstractExtension]
  have hfieldValInjective : Function.Injective fieldVal :=
    ((Nat.bijective_iff_surjective_and_card fieldVal).2
      ⟨hfieldValSurjective, hcardT.trans (Nat.card_zmod n).symm⟩).1
  let U := v.unitRepresentation E hnormal
  let S := Rep.FiniteCyclicGroup.normHomCompSub U g
  have hExact : S.Exact := by
    rw [S.moduleCat_exact_iff]
    intro u hu
    have huFixed : U.ρ g u = u := by
      apply sub_eq_zero.mp
      simpa [S, Rep.sub_hom, Rep.applyAsHom_apply] using hu
    let uM : M.V :=
      (extensionFixedRepresentationEquiv A K L hLK hnormal).symm u.1
    have huMFixed : M.ρ g uM = uM := by
      have hUaction :
          (((U.ρ g u).1 : ambientFixedAddSubgroup A L) : A.V) =
            relativeCosetAction A K L hLK u.1 g := by
        simpa [U] using
          v.unitRepresentation_action_coe E hnormal g u
      have hMaction :
          (M.ρ g uM).1 = relativeCosetAction A K L hLK u.1 g := by
        simpa [M, uM] using
          extensionFixedRepresentation_action_coe A K L hLK hnormal g uM
      apply Subtype.ext
      calc
        (M.ρ g uM).1 = relativeCosetAction A K L hLK u.1 g := hMaction
        _ = (((U.ρ g u).1 : ambientFixedAddSubgroup A L) : A.V) :=
          hUaction.symm
        _ = u.1.1 := by rw [huFixed]
        _ = uM.1 := rfl
    have huMcycle : T.g uM = 0 := by
      change M.ρ g uM - uM = 0
      exact sub_eq_zero.mpr huMFixed
    let uCycle : C := ⟨uM, huMcycle⟩
    have huClassVal :
        fieldVal (Submodule.mkQ (LinearMap.range T.moduleCatToCycles) uCycle) = 0 := by
      change v.valueModulo n hn (v.valuationAt E.field u.1) = 0
      rw [(v.mem_unitAddSubgroup_iff E.field u.1).1 u.2, map_zero]
    have huClass :
        Submodule.mkQ (LinearMap.range T.moduleCatToCycles) uCycle = 0 := by
      apply hfieldValInjective
      exact huClassVal.trans (map_zero fieldVal).symm
    have huCycleRange :
        uCycle ∈ LinearMap.range T.moduleCatToCycles := by
      exact (Submodule.Quotient.mk_eq_zero _).1 huClass
    obtain ⟨y, hy⟩ := huCycleRange
    have hyNorm : M.norm.hom y = uM := by
      exact congrArg Subtype.val hy
    let yL : ambientFixedAddSubgroup A L :=
      extensionFixedRepresentationEquiv A K L hLK hnormal y
    let normK : ambientFixedAddSubgroup A K :=
      relativeNorm A K L hLK yL
    have hnormInclusion :
        fixedFieldInclusion A K L hLK normK = u.1 := by
      apply Subtype.ext
      calc
        normK.1 = (M.norm.hom y).1 :=
          (extensionFixedRepresentation_norm_coe A K L hLK hnormal y).symm
        _ = uM.1 := congrArg Subtype.val hyNorm
        _ = u.1.1 := rfl
    have huVal : v.valuationAt E.field u.1 = 0 :=
      (v.mem_unitAddSubgroup_iff E.field u.1).1 u.2
    have htower := v.normalizedValuation_tower E yL
    change (E.residueDegree D : ℕ) •
        ((v.valuationAt E.field yL : v.valueGroup) : ZHat) =
      ((v.valuationAt E.base
        (relativeNorm A E.base.field E.field.field E.below yL) :
          v.valueGroup) : ZHat) at htower
    rw [E.residueDegree_eq_degree_of_isUnramified D hUnramified] at htower
    have hyVal : v.valuationAt E.field yL = 0 := by
      apply Subtype.ext
      apply zHatMulNat_injective hn
      calc
        n • ((v.valuationAt E.field yL : v.valueGroup) : ZHat) =
            ((v.valuationAt E.base normK : v.valueGroup) : ZHat) := htower
        _ = ((v.valuationAt E.field
              (fixedFieldInclusion A K L hLK normK) : v.valueGroup) : ZHat) := by
          rw [v.valuationAt_fixedFieldInclusion_of_unramified E hUnramified normK]
        _ = ((v.valuationAt E.field u.1 : v.valueGroup) : ZHat) := by
          rw [hnormInclusion]
        _ = 0 := congrArg Subtype.val huVal
        _ = n • (0 : ZHat) := (nsmul_zero n).symm
    let yU : U.V :=
      ⟨yL, (v.mem_unitAddSubgroup_iff E.field yL).2 hyVal⟩
    refine ⟨yU, ?_⟩
    apply Subtype.ext
    apply Subtype.ext
    calc
      ((((U.norm.hom yU).1 : ambientFixedAddSubgroup A L)) : A.V) =
          normK.1 := v.unitRepresentation_norm_coe E hnormal yU
      _ = (M.norm.hom y).1 :=
        (extensionFixedRepresentation_norm_coe A K L hLK hnormal y).symm
      _ = uM.1 := congrArg Subtype.val hyNorm
      _ = u.1.1 := rfl
  have hzeroS : Limits.IsZero S.homology :=
    (S.exact_iff_isZero_homology).1 hExact
  exact Limits.IsZero.of_iso hzeroS
    (TateCohomology.isoFiniteCyclicZero U g hg)

/-- **the unramified cohomology consequence.**  The class field axiom implies the unit-cohomology axiom: for every
finite unramified Galois extension `L / K`, both
`H⁰(G(L/K), U_L)` and `H⁻¹(G(L/K), U_L)` vanish. -/
theorem classFieldAxiom_implies_unramifiedUnitCohomology
    (v : ValuationData D A) (hcf : SatisfiesClassFieldAxiom A) :
    SatisfiesUnramifiedUnitCohomology D v := by
  intro K E
  constructor
  · simpa [FiniteUnramifiedCyclicExtension.unitRepresentation] using
      v.classFieldAxiom_unramifiedUnits_hZero hcf
        E.toFiniteAbstractFieldExtension E.normal
        E.toFiniteAbstractFieldExtension_isUnramified E.generator E.generates
  · simpa [FiniteUnramifiedCyclicExtension.unitRepresentation] using
      v.classFieldAxiom_unramifiedUnits_hMinusOne hcf
        E.toFiniteAbstractFieldExtension E.normal
        E.toFiniteAbstractFieldExtension_isUnramified E.generator E.generates

end ValuationData

/-!
# Abstract reciprocity, the abstract reciprocity theorem: the two exact rows

The proof of the abstract reciprocity theorem starts with a finite Galois tower
`L | M | K`.  This file constructs the two rows of that diagram on the
actual finite Galois groups and finite norm quotients:

`1 → G(L/M) → G(L/K) → G(M/K) → 1`,

`A_M / N_{L/M} A_L → A_K / N_{L/K} A_L
    → A_K / N_{M/K} A_M → 0`.

It also records the canonical factorization of an additive reciprocity map
through the abelianization.  No exactness or bijectivity statement is taken
as an input; both rows are proved directly from quotient membership and norm
transitivity.
-/

noncomputable section

-- Mathlib's `Rep ℤ G` currently fixes the acting group to universe zero.
variable {G : IntegralRepGroupType} [Group G] [TopologicalSpace G]

/-- The restriction `G(L/K) → G(M/K)` in the upper row. -/
def abstractReciprocityRestriction
    {G : Type*} [Group G] [TopologicalSpace G]
    (K M L : ClosedSubgroup G)
    (hLM : L.toSubgroup ≤ M.toSubgroup)
    (hMK : M.toSubgroup ≤ K.toSubgroup)
    [hLnormal :
      (extensionSubgroup K L (hLM.trans hMK)).Normal]
    [hMnormal : (extensionSubgroup K M hMK).Normal] :
    (K.toSubgroup ⧸ extensionSubgroup K L (hLM.trans hMK)) →*
      (K.toSubgroup ⧸ extensionSubgroup K M hMK) := by
  apply QuotientGroup.map
    (extensionSubgroup K L (hLM.trans hMK))
    (extensionSubgroup K M hMK)
    (MonoidHom.id K.toSubgroup)
  intro k hk
  exact hLM hk

/--
Establishes the identity `abstractReciprocityRestriction K M L hLM hMK (QuotientGroup.mk k) =
QuotientGroup.mk k`.
-/
@[simp]
theorem abstractReciprocityRestriction_mk
    {G : Type*} [Group G] [TopologicalSpace G]
    (K M L : ClosedSubgroup G)
    (hLM : L.toSubgroup ≤ M.toSubgroup)
    (hMK : M.toSubgroup ≤ K.toSubgroup)
    [hLnormal :
      (extensionSubgroup K L (hLM.trans hMK)).Normal]
    [hMnormal : (extensionSubgroup K M hMK).Normal]
    (k : K.toSubgroup) :
    abstractReciprocityRestriction K M L hLM hMK (QuotientGroup.mk k) =
      QuotientGroup.mk k :=
  rfl

/-- Restriction to the intermediate Galois extension is surjective. -/
theorem abstractReciprocityRestriction_surjective
    {G : Type*} [Group G] [TopologicalSpace G]
    (K M L : ClosedSubgroup G)
    (hLM : L.toSubgroup ≤ M.toSubgroup)
    (hMK : M.toSubgroup ≤ K.toSubgroup)
    [hLnormal :
      (extensionSubgroup K L (hLM.trans hMK)).Normal]
    [hMnormal : (extensionSubgroup K M hMK).Normal] :
    Function.Surjective (abstractReciprocityRestriction K M L hLM hMK) := by
  intro q
  refine QuotientGroup.induction_on q ?_
  intro k
  exact ⟨QuotientGroup.mk k, rfl⟩

/-- With equal base fields, norm--conjugation naturality's Galois-side restriction is
the restriction in the reciprocity reduction exact row's exact row. -/
theorem finiteReciprocityNaturalityRestriction_sameBase_eq_restriction
    {G : Type*} [Group G] [TopologicalSpace G]
    (K M L : ClosedSubgroup G)
    (hLM : L.toSubgroup ≤ M.toSubgroup)
    (hMK : M.toSubgroup ≤ K.toSubgroup)
    [hLnormal :
      (extensionSubgroup K L (hLM.trans hMK)).Normal]
    [hMnormal : (extensionSubgroup K M hMK).Normal] :
    finiteReciprocityNaturalityRestriction K K M L hMK (hLM.trans hMK) le_rfl hLM =
      abstractReciprocityRestriction K M L hLM hMK := by
  apply MonoidHom.ext
  intro q
  refine QuotientGroup.induction_on q ?_
  intro k
  rfl

/-- Finiteness of `L | K` implies finiteness of the quotient `G(M/K)`.
This is derived from the actual surjective restriction map. -/
theorem abstractReciprocity_intermediateQuotient_finite
    {G : Type*} [Group G] [TopologicalSpace G]
    (K M L : ClosedSubgroup G)
    (hLM : L.toSubgroup ≤ M.toSubgroup)
    (hMK : M.toSubgroup ≤ K.toSubgroup)
    [hLnormal :
      (extensionSubgroup K L (hLM.trans hMK)).Normal]
    [hMnormal : (extensionSubgroup K M hMK).Normal]
    [hLfinite : Finite
      (K.toSubgroup ⧸ extensionSubgroup K L (hLM.trans hMK))] :
    Finite (K.toSubgroup ⧸ extensionSubgroup K M hMK) :=
  Finite.of_surjective (abstractReciprocityRestriction K M L hLM hMK)
    (abstractReciprocityRestriction_surjective K M L hLM hMK)

/-- The inclusion `G(L/M) → G(L/K)` in the upper row.
Normality of `L | M` is derived from normality of `L | K`. -/
def abstractReciprocityInclusion
    {G : Type*} [Group G] [TopologicalSpace G]
    (K M L : ClosedSubgroup G)
    (hLM : L.toSubgroup ≤ M.toSubgroup)
    (hMK : M.toSubgroup ≤ K.toSubgroup)
    [hLnormal :
      (extensionSubgroup K L (hLM.trans hMK)).Normal] :
    letI : (extensionSubgroup M L hLM).Normal :=
      transferNormNaturality_intermediateExtension_normal K M L hLM hMK
    (M.toSubgroup ⧸ extensionSubgroup M L hLM) →*
      (K.toSubgroup ⧸ extensionSubgroup K L (hLM.trans hMK)) := by
  letI : (extensionSubgroup M L hLM).Normal :=
    transferNormNaturality_intermediateExtension_normal K M L hLM hMK
  exact transferNormNaturalityIntermediateInclusion K M L hLM hMK

/--
On quotient representatives, the abstract reciprocity inclusion is induced by inclusion of the
intermediate subgroup.
-/
@[simp]
theorem abstractReciprocityInclusion_mk
    {G : Type*} [Group G] [TopologicalSpace G]
    (K M L : ClosedSubgroup G)
    (hLM : L.toSubgroup ≤ M.toSubgroup)
    (hMK : M.toSubgroup ≤ K.toSubgroup)
    [hLnormal :
      (extensionSubgroup K L (hLM.trans hMK)).Normal]
    (m : M.toSubgroup) :
    letI : (extensionSubgroup M L hLM).Normal :=
      transferNormNaturality_intermediateExtension_normal K M L hLM hMK
    abstractReciprocityInclusion K M L hLM hMK (QuotientGroup.mk m) =
      QuotientGroup.mk (Subgroup.inclusion hMK m) := by
  let : (extensionSubgroup M L hLM).Normal :=
    transferNormNaturality_intermediateExtension_normal K M L hLM hMK
  rfl

/-- The upper row is exact at `G(L/K)`: the image of `G(L/M)` is exactly
the kernel of restriction to `G(M/K)`. -/
theorem abstractReciprocity_galois_exact
    {G : Type*} [Group G] [TopologicalSpace G]
    (K M L : ClosedSubgroup G)
    (hLM : L.toSubgroup ≤ M.toSubgroup)
    (hMK : M.toSubgroup ≤ K.toSubgroup)
    [hLnormal :
      (extensionSubgroup K L (hLM.trans hMK)).Normal]
    [hMnormal : (extensionSubgroup K M hMK).Normal] :
    letI : (extensionSubgroup M L hLM).Normal :=
      transferNormNaturality_intermediateExtension_normal K M L hLM hMK
    (abstractReciprocityRestriction K M L hLM hMK).ker =
      (abstractReciprocityInclusion K M L hLM hMK).range := by
  let : (extensionSubgroup M L hLM).Normal :=
    transferNormNaturality_intermediateExtension_normal K M L hLM hMK
  ext q
  refine QuotientGroup.induction_on q ?_
  intro k
  constructor
  · intro hk
    change abstractReciprocityRestriction K M L hLM hMK
      (QuotientGroup.mk k) = 1 at hk
    have hkM : k ∈ extensionSubgroup K M hMK :=
      (QuotientGroup.eq_one_iff k).1 hk
    let m : M.toSubgroup := ⟨k.1, hkM⟩
    refine ⟨QuotientGroup.mk m, ?_⟩
    exact congrArg
      (fun t : K.toSubgroup =>
        (QuotientGroup.mk t :
          K.toSubgroup ⧸ extensionSubgroup K L (hLM.trans hMK)))
      (Subtype.ext rfl)
  · rintro ⟨q, hq⟩
    rw [← hq]
    refine QuotientGroup.induction_on q ?_
    intro m
    change (QuotientGroup.mk (Subgroup.inclusion hMK m) :
      K.toSubgroup ⧸ extensionSubgroup K M hMK) = 1
    exact (QuotientGroup.eq_one_iff _).2 m.2

/-- Finiteness of `L | K` also implies finiteness of `L | M`. -/
theorem abstractReciprocity_lowerExtension_finite
    {G : Type*} [Group G] [TopologicalSpace G]
    (K M L : ClosedSubgroup G)
    (hLM : L.toSubgroup ≤ M.toSubgroup)
    (hMK : M.toSubgroup ≤ K.toSubgroup)
    [hLfinite : Finite
      (K.toSubgroup ⧸ extensionSubgroup K L (hLM.trans hMK))] :
    Finite (M.toSubgroup ⧸ extensionSubgroup M L hLM) := by
  let inclusion :
      (M.toSubgroup ⧸ extensionSubgroup M L hLM) →
        (K.toSubgroup ⧸ extensionSubgroup K L (hLM.trans hMK)) :=
    Quotient.map' (Subgroup.inclusion hMK) (by
      intro x y hxy
      rw [QuotientGroup.leftRel_apply] at hxy ⊢
      apply (mem_extensionSubgroup_iff K L (hLM.trans hMK) _).2
      simpa using (mem_extensionSubgroup_iff M L hLM _).1 hxy)
  apply Finite.of_injective inclusion
  intro x y
  refine QuotientGroup.induction_on x ?_
  intro m
  refine QuotientGroup.induction_on y ?_
  intro n h
  apply QuotientGroup.eq.mpr
  apply (mem_extensionSubgroup_iff M L hLM (m⁻¹ * n)).2
  have h' :
      (QuotientGroup.mk (Subgroup.inclusion hMK m) :
          K.toSubgroup ⧸ extensionSubgroup K L (hLM.trans hMK)) =
        QuotientGroup.mk (Subgroup.inclusion hMK n) := by
    simpa [inclusion] using h
  have hmem := QuotientGroup.eq.mp h'
  have hG := (mem_extensionSubgroup_iff K L (hLM.trans hMK)
    ((Subgroup.inclusion hMK m)⁻¹ * Subgroup.inclusion hMK n)).1 hmem
  simpa using hG

/-- Norm transitivity identifies the norm image from `L` with a subgroup
of the norm image from `M`. -/
theorem abstractReciprocity_finiteNormSubgroup_le
    (A : Rep ℤ G) (K M L : ClosedSubgroup G)
    (hLM : L.toSubgroup ≤ M.toSubgroup)
    (hMK : M.toSubgroup ≤ K.toSubgroup)
    [hKMfinite : Finite
      (K.toSubgroup ⧸ extensionSubgroup K M hMK)]
    [hMLfinite : Finite
      (M.toSubgroup ⧸ extensionSubgroup M L hLM)]
    [hKLfinite : Finite
      (K.toSubgroup ⧸ extensionSubgroup K L (hLM.trans hMK))] :
    finiteNormSubgroup A K L (hLM.trans hMK) ≤
      finiteNormSubgroup A K M hMK := by
  let T : DegreeData.FiniteTower G :=
    { top := L
      middle := M
      base := K
      top_le_middle := hLM
      middle_le_base := hMK
      finiteTopQuotient := hMLfinite
      finiteBaseQuotient := hKMfinite }
  rintro _ ⟨a, rfl⟩
  refine ⟨relativeNorm A M L hLM a, ?_⟩
  exact T.norm_trans_apply A a

/-- The first arrow in the lower row, induced by `N_{M/K}`. -/
def abstractReciprocityNormMap
    (A : Rep ℤ G) (K M L : ClosedSubgroup G)
    (hLM : L.toSubgroup ≤ M.toSubgroup)
    (hMK : M.toSubgroup ≤ K.toSubgroup)
    [hLnormal :
      (extensionSubgroup K L (hLM.trans hMK)).Normal]
    [hMnormal : (extensionSubgroup K M hMK).Normal]
    [hKLfinite : Finite
      (K.toSubgroup ⧸ extensionSubgroup K L (hLM.trans hMK))] :
    letI : Finite (M.toSubgroup ⧸ extensionSubgroup M L hLM) :=
      abstractReciprocity_lowerExtension_finite K M L hLM hMK
    letI : Finite (K.toSubgroup ⧸ extensionSubgroup K M hMK) :=
      abstractReciprocity_intermediateQuotient_finite K M L hLM hMK
    FiniteNormQuotient A M L hLM →+
      FiniteNormQuotient A K L (hLM.trans hMK) := by
  letI : Finite (M.toSubgroup ⧸ extensionSubgroup M L hLM) :=
    abstractReciprocity_lowerExtension_finite K M L hLM hMK
  letI : Finite (K.toSubgroup ⧸ extensionSubgroup K M hMK) :=
    abstractReciprocity_intermediateQuotient_finite K M L hLM hMK
  exact finiteReciprocityNaturalityNormMap A K M L L (hLM.trans hMK) hLM hMK le_rfl

/--
The abstract reciprocity norm map sends a finite norm class to the class of the corresponding
relative norm.
-/
@[simp]
theorem abstractReciprocityNormMap_finiteNormClass
    (A : Rep ℤ G) (K M L : ClosedSubgroup G)
    (hLM : L.toSubgroup ≤ M.toSubgroup)
    (hMK : M.toSubgroup ≤ K.toSubgroup)
    [hLnormal :
      (extensionSubgroup K L (hLM.trans hMK)).Normal]
    [hMnormal : (extensionSubgroup K M hMK).Normal]
    [hKLfinite : Finite
      (K.toSubgroup ⧸ extensionSubgroup K L (hLM.trans hMK))]
    (a : ambientFixedAddSubgroup A M) :
    letI : Finite (M.toSubgroup ⧸ extensionSubgroup M L hLM) :=
      abstractReciprocity_lowerExtension_finite K M L hLM hMK
    letI : Finite (K.toSubgroup ⧸ extensionSubgroup K M hMK) :=
      abstractReciprocity_intermediateQuotient_finite K M L hLM hMK
    abstractReciprocityNormMap A K M L hLM hMK
        (finiteNormClass A M L hLM a) =
      finiteNormClass A K L (hLM.trans hMK)
        (relativeNorm A K M hMK a) := by
  let : Finite (M.toSubgroup ⧸ extensionSubgroup M L hLM) :=
    abstractReciprocity_lowerExtension_finite K M L hLM hMK
  let : Finite (K.toSubgroup ⧸ extensionSubgroup K M hMK) :=
    abstractReciprocity_intermediateQuotient_finite K M L hLM hMK
  exact finiteReciprocityNaturalityNormMap_finiteNormClass A K M L L
    (hLM.trans hMK) hLM hMK le_rfl a

/-- The quotient projection
`A_K/N_{L/K}A_L → A_K/N_{M/K}A_M` in the lower row. -/
def abstractReciprocityNormProjection
    (A : Rep ℤ G) (K M L : ClosedSubgroup G)
    (hLM : L.toSubgroup ≤ M.toSubgroup)
    (hMK : M.toSubgroup ≤ K.toSubgroup)
    [hLnormal :
      (extensionSubgroup K L (hLM.trans hMK)).Normal]
    [hMnormal : (extensionSubgroup K M hMK).Normal]
    [hKLfinite : Finite
      (K.toSubgroup ⧸ extensionSubgroup K L (hLM.trans hMK))] :
    letI : Finite (M.toSubgroup ⧸ extensionSubgroup M L hLM) :=
      abstractReciprocity_lowerExtension_finite K M L hLM hMK
    letI : Finite (K.toSubgroup ⧸ extensionSubgroup K M hMK) :=
      abstractReciprocity_intermediateQuotient_finite K M L hLM hMK
    FiniteNormQuotient A K L (hLM.trans hMK) →+
      FiniteNormQuotient A K M hMK := by
  letI : Finite (M.toSubgroup ⧸ extensionSubgroup M L hLM) :=
    abstractReciprocity_lowerExtension_finite K M L hLM hMK
  letI : Finite (K.toSubgroup ⧸ extensionSubgroup K M hMK) :=
    abstractReciprocity_intermediateQuotient_finite K M L hLM hMK
  apply finiteNormQuotientLift A K L (hLM.trans hMK)
    (finiteNormClassHom A K M hMK)
  intro a ha
  exact (finiteNormClass_eq_zero_iff A K M hMK a).2
    (abstractReciprocity_finiteNormSubgroup_le A K M L hLM hMK ha)

/--
The abstract reciprocity norm projection preserves the representative while passing to the
intermediate norm quotient.
-/
@[simp]
theorem abstractReciprocityNormProjection_finiteNormClass
    (A : Rep ℤ G) (K M L : ClosedSubgroup G)
    (hLM : L.toSubgroup ≤ M.toSubgroup)
    (hMK : M.toSubgroup ≤ K.toSubgroup)
    [hLnormal :
      (extensionSubgroup K L (hLM.trans hMK)).Normal]
    [hMnormal : (extensionSubgroup K M hMK).Normal]
    [hKLfinite : Finite
      (K.toSubgroup ⧸ extensionSubgroup K L (hLM.trans hMK))]
    (a : ambientFixedAddSubgroup A K) :
    letI : Finite (M.toSubgroup ⧸ extensionSubgroup M L hLM) :=
      abstractReciprocity_lowerExtension_finite K M L hLM hMK
    letI : Finite (K.toSubgroup ⧸ extensionSubgroup K M hMK) :=
      abstractReciprocity_intermediateQuotient_finite K M L hLM hMK
    abstractReciprocityNormProjection A K M L hLM hMK
        (finiteNormClass A K L (hLM.trans hMK) a) =
      finiteNormClass A K M hMK a := by
  let : Finite (M.toSubgroup ⧸ extensionSubgroup M L hLM) :=
    abstractReciprocity_lowerExtension_finite K M L hLM hMK
  let : Finite (K.toSubgroup ⧸ extensionSubgroup K M hMK) :=
    abstractReciprocity_intermediateQuotient_finite K M L hLM hMK
  simp [abstractReciprocityNormProjection]
  rfl

/-- When the two base fields in norm--conjugation naturality coincide, its norm map is
the ordinary projection between the two actual finite norm quotients. -/
theorem finiteReciprocityNaturalityNormMap_sameBase_eq_normProjection
    (A : Rep ℤ G) (K M L : ClosedSubgroup G)
    (hLM : L.toSubgroup ≤ M.toSubgroup)
    (hMK : M.toSubgroup ≤ K.toSubgroup)
    [hLnormal :
      (extensionSubgroup K L (hLM.trans hMK)).Normal]
    [hMnormal : (extensionSubgroup K M hMK).Normal]
    [hKLfinite : Finite
      (K.toSubgroup ⧸ extensionSubgroup K L (hLM.trans hMK))] :
    letI : Finite (M.toSubgroup ⧸ extensionSubgroup M L hLM) :=
      abstractReciprocity_lowerExtension_finite K M L hLM hMK
    letI : Finite (K.toSubgroup ⧸ extensionSubgroup K M hMK) :=
      abstractReciprocity_intermediateQuotient_finite K M L hLM hMK
    letI : Finite (K.toSubgroup ⧸ extensionSubgroup K K le_rfl) :=
      (FiniteGaloisSubextension.refl K).finite
    finiteReciprocityNaturalityNormMap A K K M L hMK (hLM.trans hMK) le_rfl hLM =
      abstractReciprocityNormProjection A K M L hLM hMK := by
  let : Finite (M.toSubgroup ⧸ extensionSubgroup M L hLM) :=
    abstractReciprocity_lowerExtension_finite K M L hLM hMK
  let : Finite (K.toSubgroup ⧸ extensionSubgroup K M hMK) :=
    abstractReciprocity_intermediateQuotient_finite K M L hLM hMK
  let : Finite (K.toSubgroup ⧸ extensionSubgroup K K le_rfl) :=
    (FiniteGaloisSubextension.refl K).finite
  apply AddMonoidHom.ext
  intro q
  refine FiniteNormQuotient.induction_on A K L (hLM.trans hMK) q ?_
  intro a
  have hmap := finiteReciprocityNaturalityNormMap_finiteNormClass
    A K K M L hMK (hLM.trans hMK) le_rfl hLM a
  have hnorm := congrArg (finiteNormClass A K M hMK) (relativeNorm_self A K a)
  exact hmap.trans (hnorm.trans
    (abstractReciprocityNormProjection_finiteNormClass A K M L hLM hMK a).symm)

/-- The quotient projection in the lower row is surjective. -/
theorem abstractReciprocityNormProjection_surjective
    (A : Rep ℤ G) (K M L : ClosedSubgroup G)
    (hLM : L.toSubgroup ≤ M.toSubgroup)
    (hMK : M.toSubgroup ≤ K.toSubgroup)
    [hLnormal :
      (extensionSubgroup K L (hLM.trans hMK)).Normal]
    [hMnormal : (extensionSubgroup K M hMK).Normal]
    [hKLfinite : Finite
      (K.toSubgroup ⧸ extensionSubgroup K L (hLM.trans hMK))] :
    letI : Finite (M.toSubgroup ⧸ extensionSubgroup M L hLM) :=
      abstractReciprocity_lowerExtension_finite K M L hLM hMK
    letI : Finite (K.toSubgroup ⧸ extensionSubgroup K M hMK) :=
      abstractReciprocity_intermediateQuotient_finite K M L hLM hMK
    Function.Surjective (abstractReciprocityNormProjection A K M L hLM hMK) := by
  let : Finite (M.toSubgroup ⧸ extensionSubgroup M L hLM) :=
    abstractReciprocity_lowerExtension_finite K M L hLM hMK
  let : Finite (K.toSubgroup ⧸ extensionSubgroup K M hMK) :=
    abstractReciprocity_intermediateQuotient_finite K M L hLM hMK
  intro q
  refine FiniteNormQuotient.induction_on A K M hMK q ?_
  intro a
  exact ⟨finiteNormClass A K L (hLM.trans hMK) a, by
    rw [abstractReciprocityNormProjection_finiteNormClass]⟩

/-- The lower row is exact at `A_K/N_{L/K}A_L`. -/
theorem abstractReciprocity_normQuotient_exact
    (A : Rep ℤ G) (K M L : ClosedSubgroup G)
    (hLM : L.toSubgroup ≤ M.toSubgroup)
    (hMK : M.toSubgroup ≤ K.toSubgroup)
    [hLnormal :
      (extensionSubgroup K L (hLM.trans hMK)).Normal]
    [hMnormal : (extensionSubgroup K M hMK).Normal]
    [hKLfinite : Finite
      (K.toSubgroup ⧸ extensionSubgroup K L (hLM.trans hMK))] :
    letI : Finite (M.toSubgroup ⧸ extensionSubgroup M L hLM) :=
      abstractReciprocity_lowerExtension_finite K M L hLM hMK
    letI : Finite (K.toSubgroup ⧸ extensionSubgroup K M hMK) :=
      abstractReciprocity_intermediateQuotient_finite K M L hLM hMK
    Function.Exact (abstractReciprocityNormMap A K M L hLM hMK)
      (abstractReciprocityNormProjection A K M L hLM hMK) := by
  let : Finite (M.toSubgroup ⧸ extensionSubgroup M L hLM) :=
    abstractReciprocity_lowerExtension_finite K M L hLM hMK
  let : Finite (K.toSubgroup ⧸ extensionSubgroup K M hMK) :=
    abstractReciprocity_intermediateQuotient_finite K M L hLM hMK
  rw [AddMonoidHom.exact_iff]
  ext q
  refine FiniteNormQuotient.induction_on A K L (hLM.trans hMK) q ?_
  intro a
  constructor
  · intro ha
    change abstractReciprocityNormProjection A K M L hLM hMK
        (finiteNormClass A K L (hLM.trans hMK) a) = 0 at ha
    rw [abstractReciprocityNormProjection_finiteNormClass] at ha
    have haM : a ∈ finiteNormSubgroup A K M hMK :=
      (finiteNormClass_eq_zero_iff A K M hMK a).1 ha
    obtain ⟨b, rfl⟩ := haM
    exact ⟨finiteNormClass A M L hLM b, by
      rw [abstractReciprocityNormMap_finiteNormClass]⟩
  · rintro ⟨q, hq⟩
    rw [← hq]
    refine FiniteNormQuotient.induction_on A M L hLM q ?_
    intro b
    change abstractReciprocityNormProjection A K M L hLM hMK
        (abstractReciprocityNormMap A K M L hLM hMK
          (finiteNormClass A M L hLM b)) = 0
    rw [abstractReciprocityNormMap_finiteNormClass,
      abstractReciprocityNormProjection_finiteNormClass]
    exact (finiteNormClass_eq_zero_iff A K M hMK _).2 ⟨b, rfl⟩

/-- In a cyclic tower, the first norm map in the lower exact row is
injective.  This is the order calculation in the third reduction:
the three norm quotients have orders `[L:M]`, `[L:K]`, and `[M:K]`, and
the tower law cancels the last factor. -/
theorem abstractReciprocity_cyclicTower_normMap_injective
    (A : Rep ℤ G) (hcf : SatisfiesClassFieldAxiom A)
    (K M L : ClosedSubgroup G)
    (hLM : L.toSubgroup ≤ M.toSubgroup)
    (hMK : M.toSubgroup ≤ K.toSubgroup)
    [hKabsolute : Finite ((baseField G).toSubgroup ⧸
      extensionSubgroup (baseField G) K (le_baseField K))]
    [hLnormal :
      (extensionSubgroup K L (hLM.trans hMK)).Normal]
    [hMnormal : (extensionSubgroup K M hMK).Normal]
    [hKLfinite : Finite
      (K.toSubgroup ⧸ extensionSubgroup K L (hLM.trans hMK))]
    (gKL : K.toSubgroup ⧸
      extensionSubgroup K L (hLM.trans hMK))
    (hgKL : ∀ q, q ∈ Subgroup.zpowers gKL)
    (gML :
      letI : (extensionSubgroup M L hLM).Normal :=
        transferNormNaturality_intermediateExtension_normal K M L hLM hMK
      M.toSubgroup ⧸ extensionSubgroup M L hLM)
    (hgML :
      letI : (extensionSubgroup M L hLM).Normal :=
        transferNormNaturality_intermediateExtension_normal K M L hLM hMK
      ∀ q, q ∈ Subgroup.zpowers gML)
    (gKM : K.toSubgroup ⧸ extensionSubgroup K M hMK)
    (hgKM : ∀ q, q ∈ Subgroup.zpowers gKM) :
    letI : Finite (M.toSubgroup ⧸ extensionSubgroup M L hLM) :=
      abstractReciprocity_lowerExtension_finite K M L hLM hMK
    letI : Finite (K.toSubgroup ⧸ extensionSubgroup K M hMK) :=
      abstractReciprocity_intermediateQuotient_finite K M L hLM hMK
    Function.Injective (abstractReciprocityNormMap A K M L hLM hMK) := by
  let hMLnormal : (extensionSubgroup M L hLM).Normal :=
    transferNormNaturality_intermediateExtension_normal K M L hLM hMK
  let hMLfinite : Finite
      (M.toSubgroup ⧸ extensionSubgroup M L hLM) :=
    abstractReciprocity_lowerExtension_finite K M L hLM hMK
  let hKMfinite : Finite
      (K.toSubgroup ⧸ extensionSubgroup K M hMK) :=
    abstractReciprocity_intermediateQuotient_finite K M L hLM hMK
  let hMabsolute : Finite ((baseField G).toSubgroup ⧸
      extensionSubgroup (baseField G) M (le_baseField M)) :=
    relativeTowerQuotientFinite (baseField G) K M hMK (le_baseField K)
  let ELM : DegreeData.FiniteAbstractExtension G :=
    DegreeData.FiniteAbstractExtension.ofInclusion L M hLM
  let EMK : DegreeData.FiniteAbstractExtension G :=
    DegreeData.FiniteAbstractExtension.ofInclusion M K hMK
  let ELK : DegreeData.FiniteAbstractExtension G :=
    DegreeData.FiniteAbstractExtension.ofInclusion L K (hLM.trans hMK)
  let hELMbaseAbsolute : Finite ((baseField G).toSubgroup ⧸
      extensionSubgroup (baseField G) ELM.base (le_baseField ELM.base)) := by
    simpa [ELM, DegreeData.FiniteAbstractExtension.ofInclusion] using hMabsolute
  let hEMKbaseAbsolute : Finite ((baseField G).toSubgroup ⧸
      extensionSubgroup (baseField G) EMK.base (le_baseField EMK.base)) := by
    simpa [EMK, DegreeData.FiniteAbstractExtension.ofInclusion] using hKabsolute
  let hELKbaseAbsolute : Finite ((baseField G).toSubgroup ⧸
      extensionSubgroup (baseField G) ELK.base (le_baseField ELK.base)) := by
    simpa [ELK, DegreeData.FiniteAbstractExtension.ofInclusion] using hKabsolute
  let f := abstractReciprocityNormMap A K M L hLM hMK
  let p := abstractReciprocityNormProjection A K M L hLM hMK
  let : Finite (FiniteNormQuotient A M L hLM) :=
    finiteNormQuotient_finite_of_classFieldAxiom
      A hcf ELM hMLnormal gML hgML
  let : Finite (FiniteNormQuotient A K L (hLM.trans hMK)) :=
    finiteNormQuotient_finite_of_classFieldAxiom
      A hcf ELK hLnormal gKL hgKL
  let : Finite (FiniteNormQuotient A K M hMK) :=
    finiteNormQuotient_finite_of_classFieldAxiom
      A hcf EMK hMnormal gKM hgKM
  have hexact : p.ker = f.range :=
    (AddMonoidHom.exact_iff).1
      (abstractReciprocity_normQuotient_exact A K M L hLM hMK)
  have hpsurjective : Function.Surjective p :=
    abstractReciprocityNormProjection_surjective A K M L hLM hMK
  have hmiddle :
      Nat.card (FiniteNormQuotient A K L (hLM.trans hMK)) =
        Nat.card f.range *
          Nat.card (FiniteNormQuotient A K M hMK) := by
    calc
      Nat.card (FiniteNormQuotient A K L (hLM.trans hMK)) =
          Nat.card p.ker * p.ker.index :=
        (AddSubgroup.card_mul_index p.ker).symm
      _ = Nat.card f.range * Nat.card p.range := by
        rw [AddSubgroup.index_ker, hexact]
      _ = Nat.card f.range *
          Nat.card (FiniteNormQuotient A K M hMK) := by
        have hpRange : p.range = ⊤ :=
          (AddMonoidHom.range_eq_top).2 hpsurjective
        rw [hpRange]
        simp
  have hdegree :
      (ELM.degree : ℕ) * (EMK.degree : ℕ) = (ELK.degree : ℕ) := by
    rw [← ELM.relIndex_eq_degree, ← EMK.relIndex_eq_degree,
      ← ELK.relIndex_eq_degree]
    exact Subgroup.relIndex_mul_relIndex L.toSubgroup M.toSubgroup
      K.toSubgroup hLM hMK
  have hKMpositive : 0 < (EMK.degree : ℕ) := EMK.degree.property
  have hcardML :
      Nat.card (FiniteNormQuotient A M L hLM) =
        (ELM.degree : ℕ) := by
    simpa [ELM, DegreeData.FiniteAbstractExtension.ofInclusion] using
      finiteNormQuotient_card_of_classFieldAxiom
        A hcf ELM hMLnormal gML hgML
  have hcardKL :
      Nat.card (FiniteNormQuotient A K L (hLM.trans hMK)) =
        (ELK.degree : ℕ) := by
    simpa [ELK, DegreeData.FiniteAbstractExtension.ofInclusion] using
      finiteNormQuotient_card_of_classFieldAxiom
        A hcf ELK hLnormal gKL hgKL
  have hcardKM :
      Nat.card (FiniteNormQuotient A K M hMK) =
        (EMK.degree : ℕ) := by
    simpa [EMK, DegreeData.FiniteAbstractExtension.ofInclusion] using
      finiteNormQuotient_card_of_classFieldAxiom
        A hcf EMK hMnormal gKM hgKM
  have hcardRange :
      Nat.card (FiniteNormQuotient A M L hLM) =
        Nat.card f.range := by
    apply Nat.mul_right_cancel hKMpositive
    calc
      Nat.card (FiniteNormQuotient A M L hLM) *
          (EMK.degree : ℕ) =
          (ELM.degree : ℕ) * (EMK.degree : ℕ) := by
        rw [hcardML]
      _ = (ELK.degree : ℕ) := hdegree
      _ = Nat.card (FiniteNormQuotient A K L (hLM.trans hMK)) := by
        rw [hcardKL]
      _ = Nat.card f.range *
          Nat.card (FiniteNormQuotient A K M hMK) := hmiddle
      _ = Nat.card f.range * (EMK.degree : ℕ) := by
        rw [hcardKM]
  have hRangeBijective : Function.Bijective f.rangeRestrict :=
    (Nat.bijective_iff_surjective_and_card f.rangeRestrict).2
      ⟨AddMonoidHom.rangeRestrict_surjective f, hcardRange⟩
  intro x y hxy
  apply hRangeBijective.1
  exact Subtype.ext hxy

/-- An elementary profinite-integer step:
if `n z = k` in `ℤ̂`, with `0 ≤ k < n`, then `k = 0`. -/
theorem abstractReciprocity_zHat_nsmul_eq_natCast_forces_zero
    (n k : ℕ) (hn : 0 < n) (hk : k < n) (z : ZHat)
    (h : n • z =
      Int.castRingHom ZHat (k : ℤ)) :
    k = 0 := by
  have hkmod : (k : ZMod n) = 0 := by
    have hkmodInt : ((k : ℤ) : ZMod n) = 0 := by
      calc
        ((k : ℤ) : ZMod n) = zHatReduction n hn
          (Int.castRingHom ZHat (k : ℤ)) :=
              (zHatReduction_int n hn (k : ℤ)).symm
        _ =
          zHatReduction n hn (n • z) := congrArg (zHatReduction n hn) h.symm
        _ = n • zHatReduction n hn z := map_nsmul (zHatReduction n hn) n z
        _ = 0 := by simp
    simpa using hkmodInt
  exact Nat.eq_zero_of_dvd_of_lt
    ((ZMod.natCast_eq_zero_iff k n).1 hkmod) hk

/-- In a finite totally ramified extension, the normalized valuation of an
element from the lower field is multiplied by the extension degree after
inclusion into the upper field.  This is the valuation identity used for
`M/M⁰`. -/
theorem abstractReciprocity_valuationAt_fixedFieldInclusion_of_totallyRamified
    {D : DegreeData G} {A : Rep ℤ G} (v : ValuationData D A)
    (E : FiniteAbstractFieldExtension G)
    (hTot : E.IsTotallyRamified D)
    (x : ambientFixedAddSubgroup A E.base.field) :
    ((v.valuationAt E.field
      (fixedFieldInclusion A E.base.field E.field.field E.below x) :
      v.valueGroup) : ZHat) =
      (E.degree : ℕ) •
        ((v.valuationAt E.base x : v.valueGroup) : ZHat) := by
  let EF := E.toFiniteAbstractExtension
  let hEFfinite : Finite
      (E.base.field.toSubgroup ⧸
        extensionSubgroup E.base.field E.field.field E.below) :=
    EF.finiteQuotient
  have htower := v.normalizedValuation_tower E
    (fixedFieldInclusion A E.base.field E.field.field E.below x)
  have hresidue : (E.residueDegree D : ℕ) = 1 :=
    EF.residueDegree_eq_one_of_isTotallyRamified D hTot
  change (E.residueDegree D : ℕ) •
      ((v.valuationAt E.field
        (fixedFieldInclusion A E.base.field E.field.field E.below x) :
          v.valueGroup) : ZHat) =
    ((v.valuationAt E.base
      (relativeNorm A E.base.field E.field.field E.below
        (fixedFieldInclusion A E.base.field E.field.field E.below x)) :
          v.valueGroup) : ZHat) at htower
  rw [hresidue, one_nsmul] at htower
  have hbelow : E.below = EF.below := Subsingleton.elim _ _
  rw [hbelow] at htower
  change
    ((v.valuationAt E.field
      (fixedFieldInclusion A EF.base EF.field EF.below x) :
        v.valueGroup) : ZHat) =
      ((v.valuationAt E.base
        (relativeNorm A EF.base EF.field EF.below
          (fixedFieldInclusion A EF.base EF.field EF.below x)) :
            v.valueGroup) : ZHat) at htower
  rw [relativeNorm_fixedFieldInclusion A EF x] at htower
  have hfixedFieldInclusion :
      fixedFieldInclusion A EF.base EF.field EF.below x =
        fixedFieldInclusion A E.base.field E.field.field E.below x := by
    apply Subtype.ext
    rfl
  rw [hfixedFieldInclusion] at htower
  have htower' :
      ((v.valuationAt E.field
        (fixedFieldInclusion A E.base.field E.field.field E.below x) :
          v.valueGroup) : ZHat) =
        ((v.valuationAt E.base ((E.degree : ℕ) • x) :
          v.valueGroup) : ZHat) := by
    simpa [EF, FiniteAbstractFieldExtension.degree] using htower
  calc
    ((v.valuationAt E.field
      (fixedFieldInclusion A E.base.field E.field.field E.below x) :
        v.valueGroup) : ZHat) =
        ((v.valuationAt E.base ((E.degree : ℕ) • x) :
          v.valueGroup) : ZHat) := htower'
    _ = (E.degree : ℕ) •
        ((v.valuationAt E.base x : v.valueGroup) : ZHat) :=
      congrArg Subtype.val
        (map_nsmul (v.valuationAt E.base) (E.degree : ℕ) x)

/-- The exact `k = 0` valuation endpoint of the totally ramified argument.  Here `K = M⁰`, `L = M`, and `x` is the element constructed in
the fixed subgroup. -/
theorem abstractReciprocity_totallyRamified_valuation_forces_exponent_zero
    {D : DegreeData G} {A : Rep ℤ G} (v : ValuationData D A)
    (E : FiniteAbstractFieldExtension G)
    (hTot : E.IsTotallyRamified D)
    (k : ℕ) (hk : k < (E.degree : ℕ))
    (x : ambientFixedAddSubgroup A E.base.field)
    (hx :
      ((v.valuationAt E.field
        (fixedFieldInclusion A E.base.field E.field.field E.below x) :
        v.valueGroup) : ZHat) =
        Int.castRingHom ZHat (k : ℤ)) :
    k = 0 := by
  have hn : 0 < (E.degree : ℕ) := E.degree.property
  apply abstractReciprocity_zHat_nsmul_eq_natCast_forces_zero
    (E.degree : ℕ) k hn hk
    (((v.valuationAt E.base x : v.valueGroup) : ZHat))
  rw [← abstractReciprocity_valuationAt_fixedFieldInclusion_of_totallyRamified
    v E hTot]
  exact hx

end
end
end ClassFormation
end

section
-- module Solutions.OAIQ244_DUKE.AbstractClassFieldTheory_Reciprocity_Reduction
attribute [-instance] _root_.ClassFormation.instIsAddTorsionFreeZHat _root_.ClassFormation.instIsMulTorsionFreeMultiplicativeZHat _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.KummerTheory.finite_finsupp_nsmulQuotient _root_.LocalClassFieldTheory.baseFixingExtensionQuotient_finite _root_.LocalClassFieldTheory.extensionSubgroupBase_normal _root_.LocalClassFieldTheory.finiteGaloisExtensionSubgroupOfEmbedding_normal _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitQuotientCarrier_finite _root_.LocalFieldTheory.DiscreteValuationField.finite_padicInt_finPi_nsmulQuotient _root_.LocalFieldTheory.DiscreteValuationField.finite_padicInt_pi_nsmulQuotient_of_coprime _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_multiplicative_nthPowerQuotient _root_.LocalFieldTheory.finite_nsmulAddQuotient_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.LubinTate.compatibleGroupFamiliesGroup _root_.OAI.PrimeDegreePackets.boundedRealFields_finite _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.RamificationTheory.HilbertRamification.ValuationSubring.inertiaGroup_normal _root_.RamificationTheory.HilbertRamification.ValuationSubring.ramificationGroupInInertiaAut_normal _root_.RayClass.approximationCompletionTopologicalSpace _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.LocalClassFieldTheory.normalizationIntegerRingIsIntegralClosure _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen
attribute [-simp] _root_.ClassFormation.FiniteAbelianSubextension.extensionQuotientMk_apply _root_.ClassFormation.FiniteGaloisSubextension.classFieldCandidate_field _root_.ClassFormation.FiniteGaloisSubextension.intermediateFiniteAbelianOfCommutatorLe_field _root_.ClassFormation.mem_normFilterBasis_iff _root_.ClassFormation.toZModPow_zHatToPadicInt _root_.ClassFormation.zHatReductionRingHom_apply _root_.ClassFormation.zHatRingEquivProfiniteIntegerPrimeProduct_apply _root_.ClassFormation.zHatToPadicInt_intCast _root_.ClassFormation.zHatToProfiniteIntegerPrimeProduct_apply _root_.ClassFormation.zHatToProfiniteIntegerPrimeProduct_intCast _root_.ClassFormation.zHatUnitsContinuousMulEquivPrimeProduct_coe_apply _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.IsDiscreteValuationRing.addVal_ringEquiv _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.KummerTheory.torsionQuotientEquivOfZHatMulDecomposition_mk _root_.KummerTheory.zHatUnitsContinuousMulEquivPrimeProduct_rationalCyclotomicCharacter _root_.LocalClassFieldTheory.baseFixingExtensionQuotientEquivAmbient_mk _root_.LocalClassFieldTheory.baseUnitsEquivGaloisAmbientFixed_val _root_.LocalClassFieldTheory.embeddedFieldUnitsEquivGaloisFixed_coe _root_.LocalClassFieldTheory.finiteGaloisUnitsEquivAbstractFixedOfEmbedding_coe _root_.LocalClassFieldTheory.finiteGaloisUnitsEquivAbstractFixed_coe _root_.LocalClassFieldTheory.finiteResidueFrobeniusFromZHat_apply _root_.LocalClassFieldTheory.finiteResidueFrobeniusFromZHat_one _root_.LocalClassFieldTheory.intermediateFieldUnitsEquivGaloisFixed_coe _root_.LocalClassFieldTheory.residueAbsoluteDegreeIn_frobenius _root_.LocalClassFieldTheory.residueAbsoluteFrobenius_one _root_.LocalClassFieldTheory.residueFrobeniusToLimit_apply_component _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.LocalFieldTheory.residueField_algebraMap_residue _root_.OAI.PrimeDegreePackets.ThetaConstruction.schwartzCM_apply _root_.infinitePlace_mult_smul
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

namespace ClassFormation

open KummerTheory

open CyclicCohomology

/-!
# The abstract reciprocity theorem: actual reduction maps

This file isolates the field- and quotient-theoretic content of the three
reductions.  In particular, the Sylow reduction uses an
intermediate field which need not be normal over the base.  We therefore
construct its norm map without a normality assumption on the intermediate
extension.

The reciprocity homomorphisms themselves belong to the finite reciprocity equivalence.  The
lemmas below only construct the actual arrows and prove the algebraic diagram
chases which will be applied to those homomorphisms.
-/

noncomputable section

universe u

section Representation

-- Mathlib's `Rep ℤ G` currently fixes the acting group to universe zero.
variable {G : IntegralRepGroupType} [Group G] [TopologicalSpace G]
  [IsTopologicalGroup G]

namespace FiniteGaloisSubextension

variable {K : ClosedSubgroup G}

/-- The norm arrow
`A_M / N_{L/M} A_L → A_K / N_{L/K} A_L` for the actual intermediate
field cut out by `S ≤ G(L/K)`.  No normality of `M/K` is used. -/
def intermediateNormMap (A : Rep ℤ G) (L : FiniteGaloisSubextension K)
    (S : Subgroup L.extensionQuotient) :
    let M := L.intermediateField S
    let hLM := L.field_le_intermediateField S
    letI : Finite (M.toSubgroup ⧸ extensionSubgroup M L.field hLM) :=
      L.extension_over_intermediate_finite S
    letI : Finite (K.toSubgroup ⧸ extensionSubgroup K L.field L.below) :=
      L.finite
    FiniteNormQuotient A M L.field hLM →+
      FiniteNormQuotient A K L.field L.below := by
  let M := L.intermediateField S
  let hLM := L.field_le_intermediateField S
  let hMK := L.intermediateField_le_base S
  letI : Finite (K.toSubgroup ⧸
      extensionSubgroup K L.field L.below) := L.finite
  letI : Finite (M.toSubgroup ⧸
      extensionSubgroup M L.field hLM) :=
    L.extension_over_intermediate_finite S
  letI : Finite (K.toSubgroup ⧸ extensionSubgroup K M hMK) :=
    L.intermediateField_finite S
  exact finiteReciprocityNaturalityNormMap A K M L.field L.field
    L.below hLM hMK le_rfl

/-- Representative formula for the nonnormal-intermediate norm arrow. -/
@[simp]
theorem intermediateNormMap_finiteNormClass (A : Rep ℤ G)
    (L : FiniteGaloisSubextension K) (S : Subgroup L.extensionQuotient)
    (a : ambientFixedAddSubgroup A (L.intermediateField S)) :
    letI : Finite (K.toSubgroup ⧸
        extensionSubgroup K L.field L.below) := L.finite
    letI : Finite ((L.intermediateField S).toSubgroup ⧸
        extensionSubgroup (L.intermediateField S) L.field
          (L.field_le_intermediateField S)) :=
      L.extension_over_intermediate_finite S
    letI : Finite (K.toSubgroup ⧸ extensionSubgroup K
        (L.intermediateField S) (L.intermediateField_le_base S)) :=
      L.intermediateField_finite S
    L.intermediateNormMap A S
        (finiteNormClass A (L.intermediateField S) L.field
          (L.field_le_intermediateField S) a) =
      finiteNormClass A K L.field L.below
        (relativeNorm A K (L.intermediateField S)
          (L.intermediateField_le_base S) a) := by
  let : Finite (K.toSubgroup ⧸
      extensionSubgroup K L.field L.below) := L.finite
  let : Finite ((L.intermediateField S).toSubgroup ⧸
      extensionSubgroup (L.intermediateField S) L.field
        (L.field_le_intermediateField S)) :=
    L.extension_over_intermediate_finite S
  let : Finite (K.toSubgroup ⧸ extensionSubgroup K
      (L.intermediateField S) (L.intermediateField_le_base S)) :=
    L.intermediateField_finite S
  exact finiteReciprocityNaturalityNormMap_finiteNormClass A K
    (L.intermediateField S) L.field L.field L.below
    (L.field_le_intermediateField S) (L.intermediateField_le_base S) le_rfl a

/-- Inclusion of fixed elements, descended to the two actual norm
quotients.  This is the map `i` in the Sylow argument. -/
def intermediateNormQuotientInclusion (A : Rep ℤ G)
    (L : FiniteGaloisSubextension K) (S : Subgroup L.extensionQuotient) :
    letI : Finite (K.toSubgroup ⧸
        extensionSubgroup K L.field L.below) := L.finite
    letI : Finite ((L.intermediateField S).toSubgroup ⧸
        extensionSubgroup (L.intermediateField S) L.field
          (L.field_le_intermediateField S)) :=
      L.extension_over_intermediate_finite S
    FiniteNormQuotient A K L.field L.below →+
      FiniteNormQuotient A (L.intermediateField S) L.field
        (L.field_le_intermediateField S) := by
  letI : Finite (K.toSubgroup ⧸
      extensionSubgroup K L.field L.below) := L.finite
  letI : (extensionSubgroup K L.field L.below).Normal := L.normal
  letI : (extensionSubgroup (L.intermediateField S) L.field
      (L.field_le_intermediateField S)).Normal :=
    L.extensionSubgroup_over_intermediate_normal S
  letI : Finite ((L.intermediateField S).toSubgroup ⧸
      extensionSubgroup (L.intermediateField S) L.field
        (L.field_le_intermediateField S)) :=
    L.extension_over_intermediate_finite S
  exact transferNormNaturalityNormQuotientInclusion A K (L.intermediateField S)
    L.field (L.field_le_intermediateField S)
      (L.intermediateField_le_base S)

/-- Representative formula for the inclusion used in the Sylow
reduction. -/
@[simp]
theorem intermediateNormQuotientInclusion_finiteNormClass (A : Rep ℤ G)
    (L : FiniteGaloisSubextension K) (S : Subgroup L.extensionQuotient)
    (a : ambientFixedAddSubgroup A K) :
    letI : Finite (K.toSubgroup ⧸
        extensionSubgroup K L.field L.below) := L.finite
    letI : Finite ((L.intermediateField S).toSubgroup ⧸
        extensionSubgroup (L.intermediateField S) L.field
          (L.field_le_intermediateField S)) :=
      L.extension_over_intermediate_finite S
    L.intermediateNormQuotientInclusion A S
        (finiteNormClass A K L.field L.below a) =
      finiteNormClass A (L.intermediateField S) L.field
        (L.field_le_intermediateField S)
        (fixedFieldInclusion A K (L.intermediateField S)
          (L.intermediateField_le_base S) a) := by
  let : Finite (K.toSubgroup ⧸
      extensionSubgroup K L.field L.below) := L.finite
  let : (extensionSubgroup K L.field L.below).Normal := L.normal
  let : (extensionSubgroup (L.intermediateField S) L.field
      (L.field_le_intermediateField S)).Normal :=
    L.extensionSubgroup_over_intermediate_normal S
  let : Finite ((L.intermediateField S).toSubgroup ⧸
      extensionSubgroup (L.intermediateField S) L.field
        (L.field_le_intermediateField S)) :=
    L.extension_over_intermediate_finite S
  exact transferNormNaturality_normQuotientInclusion_finiteNormClass A K
    (L.intermediateField S) L.field (L.field_le_intermediateField S)
      (L.intermediateField_le_base S) a

/-- The exact identity `N_{M/K} ∘ i = [M:K]`, now for an
arbitrary (possibly nonnormal) intermediate field. -/
theorem intermediateNormMap_comp_inclusion (A : Rep ℤ G)
    (L : FiniteGaloisSubextension K) (S : Subgroup L.extensionQuotient) :
    letI : Finite (K.toSubgroup ⧸
        extensionSubgroup K L.field L.below) := L.finite
    ∀ q : FiniteNormQuotient A K L.field L.below,
    letI : Finite ((L.intermediateField S).toSubgroup ⧸
        extensionSubgroup (L.intermediateField S) L.field
          (L.field_le_intermediateField S)) :=
      L.extension_over_intermediate_finite S
    letI : Finite (K.toSubgroup ⧸ extensionSubgroup K
        (L.intermediateField S) (L.intermediateField_le_base S)) :=
      L.intermediateField_finite S
    L.intermediateNormMap A S
        (L.intermediateNormQuotientInclusion A S q) =
      ((L.intermediateFiniteAbstractExtension S).degree : ℕ) • q := by
  let : Finite (K.toSubgroup ⧸
      extensionSubgroup K L.field L.below) := L.finite
  intro q
  let : (extensionSubgroup K L.field L.below).Normal := L.normal
  let : (extensionSubgroup (L.intermediateField S) L.field
      (L.field_le_intermediateField S)).Normal :=
    L.extensionSubgroup_over_intermediate_normal S
  let : Finite ((L.intermediateField S).toSubgroup ⧸
      extensionSubgroup (L.intermediateField S) L.field
        (L.field_le_intermediateField S)) :=
    L.extension_over_intermediate_finite S
  let : Finite (K.toSubgroup ⧸ extensionSubgroup K
      (L.intermediateField S) (L.intermediateField_le_base S)) :=
    L.intermediateField_finite S
  refine FiniteNormQuotient.induction_on A K L.field L.below q ?_
  intro a
  rw [intermediateNormQuotientInclusion_finiteNormClass,
    intermediateNormMap_finiteNormClass]
  rw [show relativeNorm A K (L.intermediateField S)
      (L.intermediateField_le_base S)
        (fixedFieldInclusion A K (L.intermediateField S)
          (L.intermediateField_le_base S) a) =
      ((L.intermediateFiniteAbstractExtension S).degree : ℕ) • a by
    change relativeNorm A
        (L.intermediateFiniteAbstractExtension S).base
        (L.intermediateFiniteAbstractExtension S).field
        (L.intermediateFiniteAbstractExtension S).below
        (fixedFieldInclusion A
          (L.intermediateFiniteAbstractExtension S).base
          (L.intermediateFiniteAbstractExtension S).field
          (L.intermediateFiniteAbstractExtension S).below a) =
      ((L.intermediateFiniteAbstractExtension S).degree : ℕ) • a
    exact relativeNorm_fixedFieldInclusion A
      (L.intermediateFiniteAbstractExtension S) a]
  exact finiteNormClass_nsmul A K L.field L.below _ a

end FiniteGaloisSubextension

end Representation

section GroupOnly

variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

namespace FiniteGaloisSubextension

variable {K : ClosedSubgroup G}

/-- The inclusion `G(L/M) → G(L/K)` for the actual intermediate field,
obtained from `G(L/M) ≃ S` followed by the subgroup inclusion. -/
def lowerInclusionHom (L : FiniteGaloisSubextension K)
    (S : Subgroup L.extensionQuotient) :
    (L.intermediateField S).toSubgroup ⧸
        extensionSubgroup (L.intermediateField S) L.field
          (L.field_le_intermediateField S) →*
      L.extensionQuotient :=
  S.subtype.comp (L.lowerQuotientEquiv S).toMonoidHom

/-- Representative formula for the actual lower inclusion. -/
@[simp]
theorem lowerInclusionHom_mk (L : FiniteGaloisSubextension K)
    (S : Subgroup L.extensionQuotient)
    (m : (L.intermediateField S).toSubgroup) :
    L.lowerInclusionHom S (QuotientGroup.mk m) =
      (QuotientGroup.mk'
        (extensionSubgroup K L.field L.below))
          ⟨m.1, L.intermediateField_le_base S m.property⟩ := by
  exact L.lowerQuotientEquiv_mk_coe S m

/-- Every lower quotient of a cyclic extension is cyclic. -/
theorem lowerQuotient_isCyclic (L : FiniteGaloisSubextension K)
    (S : Subgroup L.extensionQuotient) [IsCyclic L.extensionQuotient] :
    IsCyclic
      ((L.intermediateField S).toSubgroup ⧸
        extensionSubgroup (L.intermediateField S) L.field
          (L.field_le_intermediateField S)) :=
  (L.lowerQuotientEquiv S).isCyclic.2 inferInstance

/-- The actual restriction arrow `G(L/K) → G(M/K)` attached to a normal
subgroup `S ◁ G(L/K)`, expressed through the third-isomorphism
identification constructed in `IntermediateExtension`. -/
def upperRestrictionHom (L : FiniteGaloisSubextension K)
    (S : Subgroup L.extensionQuotient) [S.Normal] :
    L.extensionQuotient →*
      K.toSubgroup ⧸ extensionSubgroup K (L.intermediateField S)
        (L.intermediateField_le_base S) :=
  (L.upperQuotientEquiv S).toMonoidHom.comp (QuotientGroup.mk' S)

/-- Representative formula for the actual upper restriction arrow. -/
@[simp]
theorem upperRestrictionHom_mk (L : FiniteGaloisSubextension K)
    (S : Subgroup L.extensionQuotient) [S.Normal] (k : K.toSubgroup) :
    L.upperRestrictionHom S
        (QuotientGroup.mk k : L.extensionQuotient) =
      QuotientGroup.mk k := by
  exact L.upperQuotientEquiv_mk_mk S k

/-- Every upper quotient of a cyclic extension is cyclic. -/
theorem upperQuotient_isCyclic (L : FiniteGaloisSubextension K)
    (S : Subgroup L.extensionQuotient) [S.Normal]
    [IsCyclic L.extensionQuotient] :
    IsCyclic
      (K.toSubgroup ⧸ extensionSubgroup K (L.intermediateField S)
        (L.intermediateField_le_base S)) := by
  have hsource : IsCyclic (L.extensionQuotient ⧸ S) :=
    isCyclic_of_surjective (QuotientGroup.mk' S)
      (QuotientGroup.mk'_surjective S)
  exact (L.upperQuotientEquiv S).isCyclic.1 hsource

/-- Its kernel is exactly the subgroup defining the intermediate field. -/
theorem upperRestrictionHom_eq_one_iff (L : FiniteGaloisSubextension K)
    (S : Subgroup L.extensionQuotient) [S.Normal]
    (q : L.extensionQuotient) :
    L.upperRestrictionHom S q = 1 ↔ q ∈ S := by
  change L.upperQuotientEquiv S
      (L.upperQuotientMk S q) = 1 ↔ q ∈ S
  constructor
  · intro h
    apply (QuotientGroup.eq_one_iff q).1
    change L.upperQuotientMk S q = 1
    apply (L.upperQuotientEquiv S).injective
    exact h.trans ((L.upperQuotientEquiv S).map_one).symm
  · intro h
    have hmk : L.upperQuotientMk S q = 1 := by
      change (QuotientGroup.mk' S) q = 1
      exact (QuotientGroup.eq_one_iff q).2 h
    exact (congrArg (L.upperQuotientEquiv S) hmk).trans
      (L.upperQuotientEquiv S).map_one

/-- The maximal abelian intermediate field in the first reduction is the
actual field cut out by the commutator subgroup of `G(L/K)`. -/
def abelianIntermediateField (L : FiniteGaloisSubextension K) :
    ClosedSubgroup G :=
  L.intermediateField (commutator L.extensionQuotient)

/-- Normality of the maximal abelian intermediate extension. -/
instance abelianIntermediateField_normalInstance
    (L : FiniteGaloisSubextension K) :
    (extensionSubgroup K L.abelianIntermediateField
      (L.intermediateField_le_base
        (commutator L.extensionQuotient))).Normal := by
  change (extensionSubgroup K
    (L.intermediateField (commutator L.extensionQuotient))
      (L.intermediateField_le_base
        (commutator L.extensionQuotient))).Normal
  exact L.intermediateField_normal
    (commutator L.extensionQuotient) inferInstance

/-- Restriction to the maximal abelian intermediate field. -/
def abelianRestrictionHom (L : FiniteGaloisSubextension K) :
    L.extensionQuotient →*
      K.toSubgroup ⧸ extensionSubgroup K L.abelianIntermediateField
        (L.intermediateField_le_base
          (commutator L.extensionQuotient)) :=
  L.upperRestrictionHom (commutator L.extensionQuotient)

/-- The first reduction's exact upper-row assertion: the kernel of
restriction to `L^ab` is the commutator subgroup. -/
theorem abelianRestrictionHom_eq_one_iff
    (L : FiniteGaloisSubextension K) (q : L.extensionQuotient) :
    L.abelianRestrictionHom q = 1 ↔
      q ∈ commutator L.extensionQuotient :=
  L.upperRestrictionHom_eq_one_iff (commutator L.extensionQuotient) q

/-- A jointly faithful family of quotient coordinates gives a jointly
faithful family of actual restriction maps to the corresponding
intermediate fields. -/
theorem upperRestrictionHom_jointlyFaithful
    (L : FiniteGaloisSubextension K)
    {I : Type*} {C : I → Type*} [∀ i, Group (C i)]
    (f : ∀ i, L.extensionQuotient →* C i)
    (hfaithful : (⨅ i, MonoidHom.ker (f i)) = ⊥)
    (q : L.extensionQuotient) :
    (∀ i, L.upperRestrictionHom (MonoidHom.ker (f i)) q = 1) ↔
      q = 1 := by
  constructor
  · intro hq
    have hmem : q ∈ ⨅ i, MonoidHom.ker (f i) := by
      rw [Subgroup.mem_iInf]
      intro i
      exact (L.upperRestrictionHom_eq_one_iff
        (MonoidHom.ker (f i)) q).1 (hq i)
    rw [hfaithful, Subgroup.mem_bot] at hmem
    exact hmem
  · rintro rfl
    intro i
    exact map_one _

/-- A finite abelian `G(L/K)` supplies the actual cyclic intermediate
extensions used in the second reduction.  The coordinate kernels have
trivial intersection, and the corresponding groups `G(Mᵢ/K)` are finite
cyclic. -/
theorem exists_cyclicIntermediateFields
    (L : FiniteGaloisSubextension K)
    [IsMulCommutative L.extensionQuotient] :
    ∃ (I : Type 0) (_ : Fintype I) (m : I → ℕ),
      (∀ i, 1 < m i) ∧
      ∃ f : ∀ i,
          L.extensionQuotient →* Multiplicative (ZMod (m i)),
        (∀ i, Function.Surjective (f i)) ∧
        (⨅ i, MonoidHom.ker (f i)) = ⊥ ∧
        (∀ i, IsCyclic
          (K.toSubgroup ⧸ extensionSubgroup K
            (L.intermediateField (MonoidHom.ker (f i)))
            (L.intermediateField_le_base (MonoidHom.ker (f i))))) ∧
        (∀ i, Finite
          (K.toSubgroup ⧸ extensionSubgroup K
            (L.intermediateField (MonoidHom.ker (f i)))
            (L.intermediateField_le_base (MonoidHom.ker (f i))))) := by
  let : CommGroup L.extensionQuotient :=
    open scoped IsMulCommutative in inferInstance
  obtain ⟨I, hI, m, hm, f, hf, hfaithful⟩ :=
    finiteCommGroup_exists_jointlyFaithful_cyclic_factors
      L.extensionQuotient
  let : Fintype I := hI
  refine ⟨I, hI, m, hm, f, hf, hfaithful, ?_, ?_⟩
  · intro i
    let e : L.extensionQuotient ⧸ MonoidHom.ker (f i) ≃*
        Multiplicative (ZMod (m i)) :=
      QuotientGroup.quotientKerEquivOfSurjective (f i) (hf i)
    have hsource : IsCyclic
        (L.extensionQuotient ⧸ MonoidHom.ker (f i)) :=
      e.isCyclic.2 inferInstance
    exact (L.upperQuotientEquiv (MonoidHom.ker (f i))).isCyclic.1 hsource
  · intro i
    exact L.intermediateField_finite (MonoidHom.ker (f i))

/-! ## The maximal unramified subextension in the third reduction -/

/-- The inertia subgroup of `G(L/K)`: the image of `I_K` in the actual
finite quotient.  Its fixed field is `L ∩ K̃` in the notation of. -/
def inertiaImage (D : DegreeData G) (L : FiniteGaloisSubextension K) :
    Subgroup L.extensionQuotient :=
  (D.fieldInertiaWithin K).map
    (QuotientGroup.mk' (extensionSubgroup K L.field L.below))

omit [IsTopologicalGroup G] in
/-- The inertia image is normal, since it is the image of the normal
inertia subgroup under a surjective quotient map. -/
theorem inertiaImage_normal (D : DegreeData G)
    (L : FiniteGaloisSubextension K) : (L.inertiaImage D).Normal := by
  exact (inferInstance : (D.fieldInertiaWithin K).Normal).map
    (QuotientGroup.mk' (extensionSubgroup K L.field L.below))
    (QuotientGroup.mk'_surjective
      (extensionSubgroup K L.field L.below))

/-- The inertia image in a finite Galois quotient is normal. -/
instance inertiaImage_normalInstance (D : DegreeData G)
    (L : FiniteGaloisSubextension K) : (L.inertiaImage D).Normal :=
  L.inertiaImage_normal D

/-- The actual maximal unramified subextension `M = L ∩ K̃`. -/
def maximalUnramifiedSubextension (D : DegreeData G)
    (L : FiniteGaloisSubextension K) : ClosedSubgroup G :=
  L.intermediateField (L.inertiaImage D)

/-- The constructed `M/K` is unramified. -/
theorem maximalUnramifiedSubextension_isUnramified
    (D : DegreeData G) (L : FiniteGaloisSubextension K) :
    (DegreeData.AbstractExtension.mk (L.maximalUnramifiedSubextension D) K
      (L.intermediateField_le_base (L.inertiaImage D))).IsUnramified D := by
  change (DegreeData.AbstractExtension.mk
    (L.intermediateField (L.inertiaImage D)) K
    (L.intermediateField_le_base (L.inertiaImage D))).IsUnramified D
  rw [(DegreeData.AbstractExtension.mk
    (L.intermediateField (L.inertiaImage D)) K
    (L.intermediateField_le_base (L.inertiaImage D))).isUnramified_iff_inertia_le D]
  intro x hx
  let k : K.toSubgroup := ⟨x, hx.1⟩
  have hkI : k ∈ D.fieldInertiaWithin K := by
    exact hx.2
  have hkS :
      (QuotientGroup.mk'
        (extensionSubgroup K L.field L.below)) k ∈ L.inertiaImage D :=
    ⟨k, hkI, rfl⟩
  have hkP : k ∈ L.intermediateSubgroup (L.inertiaImage D) := by
    change (QuotientGroup.mk'
      (extensionSubgroup K L.field L.below)) k ∈ L.inertiaImage D
    exact hkS
  exact ⟨k, hkP, rfl⟩

/-- The complementary extension `L/M` is totally ramified, i.e.
`f_{L/M}=1`. -/
theorem maximalUnramifiedSubextension_isTotallyRamified
    (D : DegreeData G) (L : FiniteGaloisSubextension K) :
    (DegreeData.AbstractExtension.mk L.field
      (L.maximalUnramifiedSubextension D)
      (L.field_le_intermediateField (L.inertiaImage D))).IsTotallyRamified D := by
  let S := L.inertiaImage D
  let M := L.maximalUnramifiedSubextension D
  let hLM := L.field_le_intermediateField S
  let hMK := L.intermediateField_le_base S
  change (DegreeData.AbstractExtension.mk L.field
    (L.intermediateField (L.inertiaImage D)) hLM).IsTotallyRamified D
  rw [(DegreeData.AbstractExtension.mk L.field
    (L.intermediateField (L.inertiaImage D)) hLM).isTotallyRamified_iff_image_le D]
  rintro z ⟨x, hxM, rfl⟩
  let xK : K.toSubgroup := ⟨x, hMK hxM⟩
  have hxP : xK ∈ L.intermediateSubgroup S := by
    rw [← L.extensionSubgroup_intermediateField_eq S]
    exact (mem_extensionSubgroup_iff K M hMK xK).2 hxM
  change (QuotientGroup.mk'
    (extensionSubgroup K L.field L.below)) xK ∈
      (D.fieldInertiaWithin K).map
        (QuotientGroup.mk'
          (extensionSubgroup K L.field L.below)) at hxP
  obtain ⟨i, hiI, hi⟩ := hxP
  have hiH : i⁻¹ * xK ∈ extensionSubgroup K L.field L.below :=
    QuotientGroup.eq.mp hi
  have hiL : i.1⁻¹ * x ∈ L.field.toSubgroup := by
    exact (mem_extensionSubgroup_iff K L.field L.below (i⁻¹ * xK)).1 hiH
  refine ⟨i.1⁻¹ * x, hiL, ?_⟩
  have hdegree : D.degree i.1 = 1 :=
    (D.mem_fieldInertiaWithin_iff K i).1 hiI
  simp [hdegree]

end FiniteGaloisSubextension

end GroupOnly

section Representation

-- Mathlib's `Rep ℤ G` currently fixes the acting group to universe zero.
variable {G : IntegralRepGroupType} [Group G] [TopologicalSpace G]
  [IsTopologicalGroup G]

namespace FiniteGaloisSubextension

variable {K : ClosedSubgroup G}

/-- In the cyclic case, the lower norm arrow for
`L / (L ∩ K̃) / K` is injective by the order calculation from.
This specializes the actual cardinality proof in the reciprocity reduction exact row to the
inertia-image intermediate field. -/
theorem maximalUnramified_normMap_injective
    (A : Rep ℤ G) (hcf : SatisfiesClassFieldAxiom A)
    (D : DegreeData G) (L : FiniteGaloisSubextension K)
    [Finite ((baseField G).toSubgroup ⧸
      extensionSubgroup (baseField G) K (le_baseField K))]
    [IsCyclic L.extensionQuotient] :
    let S := L.inertiaImage D
    let M := L.intermediateField S
    let hLM := L.field_le_intermediateField S
    let hMK := L.intermediateField_le_base S
    letI : Finite
        (M.toSubgroup ⧸ extensionSubgroup M L.field hLM) :=
      L.extension_over_intermediate_finite S
    letI : Finite
        (K.toSubgroup ⧸ extensionSubgroup K M hMK) :=
      L.intermediateField_finite S
    letI : Finite
        (K.toSubgroup ⧸ extensionSubgroup K L.field (hLM.trans hMK)) := by
      simpa only using L.finite
    Function.Injective
      (abstractReciprocityNormMap A K M L.field hLM hMK) := by
  dsimp only
  let S := L.inertiaImage D
  let M := L.intermediateField S
  let hLM := L.field_le_intermediateField S
  let hMK := L.intermediateField_le_base S
  let : (extensionSubgroup K L.field (hLM.trans hMK)).Normal := by
    simpa only using L.normal
  let : (extensionSubgroup K M hMK).Normal :=
    L.intermediateField_normal S inferInstance
  let : Finite
      (K.toSubgroup ⧸ extensionSubgroup K L.field (hLM.trans hMK)) := by
    simpa only using L.finite
  let : Finite
      (M.toSubgroup ⧸ extensionSubgroup M L.field hLM) :=
    L.extension_over_intermediate_finite S
  let : Finite
      (K.toSubgroup ⧸ extensionSubgroup K M hMK) :=
    L.intermediateField_finite S
  let : IsCyclic
      (M.toSubgroup ⧸ extensionSubgroup M L.field hLM) :=
    L.lowerQuotient_isCyclic S
  let : IsCyclic
      (K.toSubgroup ⧸ extensionSubgroup K M hMK) :=
    L.upperQuotient_isCyclic S
  obtain ⟨gKL, hgKL⟩ := IsCyclic.exists_generator
    (α := L.extensionQuotient)
  obtain ⟨gML, hgML⟩ := IsCyclic.exists_generator
    (α := M.toSubgroup ⧸ extensionSubgroup M L.field hLM)
  obtain ⟨gKM, hgKM⟩ := IsCyclic.exists_generator
    (α := K.toSubgroup ⧸ extensionSubgroup K M hMK)
  exact abstractReciprocity_cyclicTower_normMap_injective
    A hcf K M L.field hLM hMK gKL hgKL gML hgML gKM hgKM

end FiniteGaloisSubextension

/-- Exact remaining kernel calculation in the first reduction.  For the
actual maximal abelian intermediate field, commutativity of the right square
and injectivity of its reciprocity arrow identify the kernel of the middle
arrow with the commutator subgroup. -/
theorem abstractReciprocity_abelianReduction_kernel
    {K : ClosedSubgroup G} {B : Type*} {C : Type*}
    [AddCommGroup B] [AddCommGroup C]
    (L : FiniteGaloisSubextension K)
    (p : B →+ C)
    (r : Additive L.extensionQuotient →+ B)
    (rAb : Additive
        (K.toSubgroup ⧸ extensionSubgroup K L.abelianIntermediateField
          (L.intermediateField_le_base
            (commutator L.extensionQuotient))) →+ C)
    (hright : ∀ q,
      p (r (Additive.ofMul q)) =
        rAb (Additive.ofMul (L.abelianRestrictionHom q)))
    (hrAb : Function.Injective rAb)
    (q : L.extensionQuotient) :
    r (Additive.ofMul q) = 0 ↔
      q ∈ commutator L.extensionQuotient := by
  constructor
  · intro hq
    have hzero :
        rAb (Additive.ofMul (L.abelianRestrictionHom q)) = 0 := by
      rw [← hright q, hq, map_zero]
    have hresAdd :
        Additive.ofMul (L.abelianRestrictionHom q) = 0 := by
      apply hrAb
      simpa using hzero
    have hres : L.abelianRestrictionHom q = 1 := by
      exact Additive.ofMul.injective (by simpa using hresAdd)
    exact (L.abelianRestrictionHom_eq_one_iff q).1 hres
  · exact abstractReciprocity_commutator_mem_kernel r q

end Representation

end
end ClassFormation
end

section
-- module Solutions.OAIQ244_DUKE.AbstractClassFieldTheory_Reciprocity_Sylow
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalClassFieldTheory.baseFixingExtensionQuotient_finite _root_.LocalClassFieldTheory.extensionSubgroupBase_normal _root_.LocalClassFieldTheory.finiteGaloisExtensionSubgroupOfEmbedding_normal _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitQuotientCarrier_finite _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.LubinTate.compatibleGroupFamiliesGroup _root_.OAI.PrimeDegreePackets.boundedRealFields_finite _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.RamificationTheory.HilbertRamification.ValuationSubring.inertiaGroup_normal _root_.RamificationTheory.HilbertRamification.ValuationSubring.ramificationGroupInInertiaAut_normal _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.LocalClassFieldTheory.normalizationIntegerRingIsIntegralClosure _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

namespace ClassFormation

open KummerTheory

open CyclicCohomology

/-!
# The abstract reciprocity theorem: the Sylow step in the first reduction

This file formalizes the source-producing group-theoretic part of the
first reduction.  For a Sylow `p`-subgroup `P` of the actual
finite quotient `G(L/K)`, the already constructed fixed field `M = L^P`
is an actual (not necessarily Galois over `K`) intermediate field.  The
actual quotient `G(L/M)` is a `p`-group and hence solvable, while
`[M:K] = (G(L/K) : P)` is prime to `p`.

For an abelian group `B`, multiplication by `[M:K]` is therefore
surjective on every Sylow `p`-subgroup of `B`, without assuming that the
ambient group is finite.  Equivalently, that Sylow subgroup lies in the
image of the `[M:K]`-fold map.  In the abstract reciprocity theorem the ambient norm quotient is
only known at this point to have bounded exponent; its individual cyclic
subgroups are finite.  This avoids using the desired reciprocity
surjectivity to prove finiteness.  No reciprocity surjectivity or
the finite reciprocity equivalence comparison is assumed here.
-/

noncomputable section

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

namespace FiniteGaloisSubextension

variable {K : ClosedSubgroup G}

/-! ## The fixed field of a Sylow subgroup -/

/-- For `M = L^P`, the actual lower quotient `G(L/M)` is a `p`-group.
This is the identification `G(L/M) \cong P`, applied to an actual
Sylow subgroup of the actual finite quotient `G(L/K)`. -/
theorem abstractReciprocity_sylow_lowerQuotient_isPGroup
    (L : FiniteGaloisSubextension K) {p : ℕ}
    (P : Sylow p L.extensionQuotient) :
    IsPGroup p
      ((L.intermediateField (P : Subgroup L.extensionQuotient)).toSubgroup ⧸
        extensionSubgroup
          (L.intermediateField (P : Subgroup L.extensionQuotient)) L.field
          (L.field_le_intermediateField
            (P : Subgroup L.extensionQuotient))) := by
  exact P.isPGroup'.of_equiv
    (L.lowerQuotientEquiv (P : Subgroup L.extensionQuotient)).symm

section SylowSolvability

local notation "IsSolvable" => Group.IsSolvable

/-- Consequently, the actual extension `L/M` cut out by a Sylow subgroup
is solvable.  Mathlib proves this by the standard chain
finite `p`-group `\Rightarrow` nilpotent `\Rightarrow` solvable. -/
theorem abstractReciprocity_sylow_lowerQuotient_isSolvable
    (L : FiniteGaloisSubextension K) {p : ℕ} [Fact p.Prime]
    (P : Sylow p L.extensionQuotient) :
    IsSolvable
      ((L.intermediateField (P : Subgroup L.extensionQuotient)).toSubgroup ⧸
        extensionSubgroup
          (L.intermediateField (P : Subgroup L.extensionQuotient)) L.field
          (L.field_le_intermediateField
            (P : Subgroup L.extensionQuotient))) := by
  let : Finite
      ((L.intermediateField (P : Subgroup L.extensionQuotient)).toSubgroup ⧸
        extensionSubgroup
          (L.intermediateField (P : Subgroup L.extensionQuotient)) L.field
          (L.field_le_intermediateField
            (P : Subgroup L.extensionQuotient))) :=
    L.extension_over_intermediate_finite
      (P : Subgroup L.extensionQuotient)
  let : Group.IsNilpotent
      ((L.intermediateField (P : Subgroup L.extensionQuotient)).toSubgroup ⧸
        extensionSubgroup
          (L.intermediateField (P : Subgroup L.extensionQuotient)) L.field
          (L.field_le_intermediateField
            (P : Subgroup L.extensionQuotient))) :=
    (L.abstractReciprocity_sylow_lowerQuotient_isPGroup P).isNilpotent
  change Group.IsSolvable
    ((L.intermediateField (P : Subgroup L.extensionQuotient)).toSubgroup ⧸
      extensionSubgroup
        (L.intermediateField (P : Subgroup L.extensionQuotient)) L.field
        (L.field_le_intermediateField (P : Subgroup L.extensionQuotient)))
  infer_instance

end SylowSolvability

/-- The degree of the actual fixed field `M = L^P` over `K` is the index
of `P` in `G(L/K)`.  No normality of `P`, and hence none of `M/K`, is
used. -/
theorem abstractReciprocity_sylow_intermediateDegree_eq_index
    (L : FiniteGaloisSubextension K) {p : ℕ}
    (P : Sylow p L.extensionQuotient) :
    (L.intermediateFiniteAbstractExtension
      (P : Subgroup L.extensionQuotient)).degree =
      (P : Subgroup L.extensionQuotient).index := by
  rw [← (L.intermediateFiniteAbstractExtension
    (P : Subgroup L.extensionQuotient)).extensionSubgroup_index_eq_degree]
  change (extensionSubgroup K
    (L.intermediateField (P : Subgroup L.extensionQuotient))
      (L.intermediateField_le_base (P : Subgroup L.extensionQuotient))).index = _
  rw [L.extensionSubgroup_intermediateField_eq
    (P : Subgroup L.extensionQuotient)]
  exact (P : Subgroup L.extensionQuotient).index_comap_of_surjective
    (QuotientGroup.mk'_surjective
      (extensionSubgroup K L.field L.below))

/-- Hence the actual degree `[M:K]` is prime to the chosen Sylow prime
`p`, as asserted. -/
theorem abstractReciprocity_sylow_intermediateDegree_coprime
    (L : FiniteGaloisSubextension K) {p : ℕ} [Fact p.Prime]
    (P : Sylow p L.extensionQuotient) :
    Nat.Coprime
      (L.intermediateFiniteAbstractExtension
        (P : Subgroup L.extensionQuotient)).degree p := by
  rw [L.abstractReciprocity_sylow_intermediateDegree_eq_index P]
  rw [Nat.coprime_comm, Nat.Prime.coprime_iff_not_dvd Fact.out]
  exact P.not_dvd_index

/-! ## Sylow subgroups in a possibly infinite abelian target -/

/-- The exact specialization: for `M = L^P`, every Sylow
`p`-subgroup of an abelian group `B` lies in the image of the
`[M:K]`-fold map on `B`.  This is the group-theoretic input which the
identity `N_{M/K} ∘ i = [M:K]` later converts into norm-map containment. -/
theorem abstractReciprocity_sylowAddSubgroup_le_intermediateDegree_nsmul_range
    (L : FiniteGaloisSubextension K) {p : ℕ} [Fact p.Prime]
    (P : Sylow p L.extensionQuotient)
    {B : Type*} [AddCommGroup B]
    (S : Sylow p (Multiplicative B)) :
    Subgroup.toAddSubgroup'
        (S : Subgroup (Multiplicative B)) ≤
      (nsmulAddMonoidHom (α := B)
        (L.intermediateFiniteAbstractExtension
          (P : Subgroup L.extensionQuotient)).degree).range := by
  exact sylowAddSubgroup_le_nsmul_range_of_coprime S
    (L.abstractReciprocity_sylow_intermediateDegree_coprime P)

end FiniteGaloisSubextension

end
end ClassFormation
end

section
-- module Solutions.OAIQ244_DUKE.AbstractClassFieldTheory_Reciprocity_TotallyRamified
attribute [-instance] _root_.ClassFormation.FiniteGaloisSubextension.abelianIntermediateField_normalInstance _root_.ClassFormation.FiniteGaloisSubextension.extensionSubgroup_over_intermediate_normalInstance _root_.ClassFormation.FiniteGaloisSubextension.inertiaImage_normalInstance _root_.ClassFormation.FiniteGaloisSubextension.intermediateField_normalInstance _root_.ClassFormation.instIsAddTorsionFreeZHat _root_.ClassFormation.instIsMulTorsionFreeMultiplicativeZHat _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.KummerTheory.finite_finsupp_nsmulQuotient _root_.LocalClassFieldTheory.baseFixingExtensionQuotient_finite _root_.LocalClassFieldTheory.extensionSubgroupBase_normal _root_.LocalClassFieldTheory.finiteGaloisExtensionSubgroupOfEmbedding_normal _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitQuotientCarrier_finite _root_.LocalFieldTheory.DiscreteValuationField.finite_padicInt_finPi_nsmulQuotient _root_.LocalFieldTheory.DiscreteValuationField.finite_padicInt_pi_nsmulQuotient_of_coprime _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_multiplicative_nthPowerQuotient _root_.LocalFieldTheory.finite_nsmulAddQuotient_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.LubinTate.compatibleGroupFamiliesGroup _root_.OAI.PrimeDegreePackets.boundedRealFields_finite _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.maximalIdealPowSuccQuotModule _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.LocalClassFieldTheory.normalizationIntegerRingIsIntegralClosure _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen
attribute [-simp] _root_.ClassFormation.FiniteAbelianSubextension.extensionQuotientMk_apply _root_.ClassFormation.FiniteGaloisSubextension.classFieldCandidate_field _root_.ClassFormation.FiniteGaloisSubextension.intermediateNormMap_finiteNormClass _root_.ClassFormation.FiniteGaloisSubextension.intermediateNormQuotientInclusion_finiteNormClass _root_.ClassFormation.FiniteGaloisSubextension.lowerInclusionHom_mk _root_.ClassFormation.FiniteGaloisSubextension.upperRestrictionHom_mk _root_.ClassFormation.mem_normFilterBasis_iff _root_.ClassFormation.toZModPow_zHatToPadicInt _root_.ClassFormation.zHatReductionRingHom_apply _root_.ClassFormation.zHatRingEquivProfiniteIntegerPrimeProduct_apply _root_.ClassFormation.zHatToPadicInt_intCast _root_.ClassFormation.zHatToProfiniteIntegerPrimeProduct_apply _root_.ClassFormation.zHatToProfiniteIntegerPrimeProduct_intCast _root_.ClassFormation.zHatUnitsContinuousMulEquivPrimeProduct_coe_apply _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.IsDiscreteValuationRing.addVal_ringEquiv _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.KummerTheory.torsionQuotientEquivOfZHatMulDecomposition_mk _root_.KummerTheory.zHatUnitsContinuousMulEquivPrimeProduct_rationalCyclotomicCharacter _root_.LocalClassFieldTheory.baseFixingExtensionQuotientEquivAmbient_mk _root_.LocalClassFieldTheory.baseUnitsEquivGaloisAmbientFixed_val _root_.LocalClassFieldTheory.embeddedFieldUnitsEquivGaloisFixed_coe _root_.LocalClassFieldTheory.finiteGaloisUnitsEquivAbstractFixedOfEmbedding_coe _root_.LocalClassFieldTheory.finiteGaloisUnitsEquivAbstractFixed_coe _root_.LocalClassFieldTheory.finiteResidueFrobeniusFromZHat_apply _root_.LocalClassFieldTheory.finiteResidueFrobeniusFromZHat_one _root_.LocalClassFieldTheory.intermediateFieldUnitsEquivGaloisFixed_coe _root_.LocalClassFieldTheory.intrinsicFiniteAbstractBase_eq_base _root_.LocalClassFieldTheory.residueAbsoluteDegreeIn_frobenius _root_.LocalClassFieldTheory.residueAbsoluteFrobenius_one _root_.LocalClassFieldTheory.residueFrobeniusToLimit_apply_component _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.LocalFieldTheory.residueField_algebraMap_residue _root_.OAI.PrimeDegreePackets.ThetaConstruction.schwartzCM_apply _root_.infinitePlace_mult_smul
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

namespace ClassFormation

open KummerTheory

open CyclicCohomology

/-!
# The abstract reciprocity theorem: the totally ramified calculation

This file isolates the calculation.  The input from the finite reciprocity equivalence is an equality in an actual finite norm quotient.  Such an equality is
first turned into an equality of actual norms.  For the cyclic totally
ramified extension `M / M⁰`, the class-field axiom then supplies the element `a` with
`aᵒ-a = v-u`.  The element written in this construction as
`π_L^k v a^(1-σ̃)` is descended from `A_M` to the actual fixed group
`A_{M⁰}`, and its valuation is computed to be `k`.  The final invocation of
the valuation endpoint in the reciprocity reduction exact row therefore gives `k = 0`.

The only comparison not made in this file is the finite reciprocity equivalence
identification of a reciprocity value with the prime-norm class.  No
compatibility record or theorem-shaped certificate is introduced for that
comparison.
-/

noncomputable section

open CategoryTheory

-- Mathlib's `Rep ℤ G` currently fixes the acting group to universe zero.
variable {G : IntegralRepGroupType} [Group G] [TopologicalSpace G]

/-! ## The linear calculation behind the fixed element -/

namespace ValuationData

variable {D : DegreeData G} {A : Rep ℤ G}

/-- The representative extracted from a zero prime-norm class can be
written as `π_L^k v` with an actual unit `v ∈ U_L`.  This is the
prime/valuation calculation: both
`L / K` and the Frobenius fixed field `Σ / K` have relative residue
degree one. -/
theorem primeNormClass_eq_zero_exists_unit_norm_eq
    (v : ValuationData D A)
    (K L S : FiniteAbstractField G)
    (hLK : L.field.toSubgroup ≤ K.field.toSubgroup)
    (hSK : S.field.toSubgroup ≤ K.field.toSubgroup)
    (hTot : (DegreeData.AbstractExtension.mk
      L.field K.field hLK).IsTotallyRamified D)
    [hLKfinite : Finite
      (K.field.toSubgroup ⧸ extensionSubgroup K.field L.field hLK)]
    [hSKfinite : Finite
      (K.field.toSubgroup ⧸ extensionSubgroup K.field S.field hSK)]
    (hSigmaResidue :
      ((DegreeData.FiniteAbstractExtension.ofInclusion
        S.field K.field hSK).residueDegree D : ℕ) = 1)
    (k : ℕ)
    (piS : ambientFixedAddSubgroup A S.field)
    (piL : ambientFixedAddSubgroup A L.field)
    (hpiS : v.IsPrimeElement S piS)
    (hpiL : v.IsPrimeElement L piL)
    (hclass :
      finiteNormClass A K.field L.field hLK
          (relativeNorm A K.field S.field hSK (k • piS)) = 0) :
    ∃ w : v.unitAddSubgroup L,
      relativeNorm A K.field L.field hLK (k • piL + w.1) =
        relativeNorm A K.field S.field hSK (k • piS) := by
  obtain ⟨b, hb⟩ :=
    (finiteNormClass_eq_zero_iff
      A K.field L.field hLK _).1 hclass
  let EL : FiniteAbstractFieldExtension G :=
    { field := L
      base := K
      below := hLK
      finiteQuotient := hLKfinite }
  let ES : FiniteAbstractFieldExtension G :=
    FiniteAbstractFieldExtension.ofInclusion S.field K hSK
  have hvalB : v.valuationAt L b = k • v.oneValue := by
    apply Subtype.ext
    have hL := v.normalizedValuation_tower EL b
    have hS := v.normalizedValuation_tower ES (k • piS)
    have hTotEL : EL.IsTotallyRamified D := by
      simpa [EL, FiniteAbstractFieldExtension.IsTotallyRamified,
        FiniteAbstractFieldExtension.toFiniteAbstractExtension] using hTot
    have hresidue : (EL.residueDegree D : ℕ) = 1 :=
      EL.toFiniteAbstractExtension.residueDegree_eq_one_of_isTotallyRamified
        D hTotEL
    change (EL.residueDegree D : ℕ) •
        ((v.valuationAt L b : v.valueGroup) : ZHat) =
      ((v.valuationAt K (relativeNorm A K.field L.field hLK b) :
        v.valueGroup) : ZHat) at hL
    rw [hresidue, one_nsmul] at hL
    have hSigmaResidue' : (ES.residueDegree D : ℕ) = 1 := by
      let ES₀ :=
        DegreeData.FiniteAbstractExtension.ofInclusion S.field K.field hSK
      have hSigmaCard :
          ES₀.toAbstractExtension.relativeResidueDegreeCardinal D = 1 := by
        calc
          ES₀.toAbstractExtension.relativeResidueDegreeCardinal D =
              ((ES₀.residueDegree D : ℕ) : Cardinal) :=
            ES₀.relativeResidueDegreeCardinal_eq_coe D
          _ = 1 := by rw [hSigmaResidue]; simp
      apply Nat.cast_injective (R := Cardinal)
      unfold FiniteAbstractFieldExtension.residueDegree
      rw [← ES.toFiniteAbstractExtension.relativeResidueDegreeCardinal_eq_coe D]
      simpa [ES, ES₀, FiniteAbstractFieldExtension.toFiniteAbstractExtension,
        FiniteAbstractFieldExtension.ofInclusion,
        DegreeData.FiniteAbstractExtension.toAbstractExtension,
        DegreeData.FiniteAbstractExtension.ofInclusion] using hSigmaCard
    change (ES.residueDegree D : ℕ) •
        ((v.valuationAt S (k • piS) : v.valueGroup) : ZHat) =
      ((v.valuationAt K
        (relativeNorm A K.field S.field hSK (k • piS)) :
          v.valueGroup) : ZHat) at hS
    rw [hSigmaResidue', one_nsmul] at hS
    calc
      ((v.valuationAt L b : v.valueGroup) : ZHat) =
          ((v.valuationAt K (relativeNorm A K.field L.field hLK b) :
            v.valueGroup) : ZHat) := hL
      _ = ((v.valuationAt K
          (relativeNorm A K.field S.field hSK (k • piS)) :
            v.valueGroup) : ZHat) := by rw [hb]
      _ = ((v.valuationAt S (k • piS) : v.valueGroup) : ZHat) := hS.symm
      _ = ((k • v.oneValue : v.valueGroup) : ZHat) := by
        congr 1
        rw [map_nsmul, hpiS]
  let wL : ambientFixedAddSubgroup A L.field := b - k • piL
  have hw : v.valuationAt L wL = 0 := by
    change v.valuationAt L (b - k • piL) = 0
    rw [map_sub, map_nsmul, hvalB, hpiL, sub_self]
  let w : v.unitAddSubgroup L :=
    ⟨wL, (v.mem_unitAddSubgroup_iff L wL).2 hw⟩
  refine ⟨w, ?_⟩
  calc
    relativeNorm A K.field L.field hLK (k • piL + w.1) =
        relativeNorm A K.field L.field hLK b := by
      congr 1
      apply Subtype.ext
      dsimp [w, wL]
      abel
    _ = relativeNorm A K.field S.field hSK (k • piS) := hb

/-- Normalized valuation is invariant under the actual quotient action.
This is the quotient-representation form of the unit-cohomology axiom's
`valuationAt_normalExtensionAction`. -/
theorem valuationAt_extensionFixedRepresentation_action
    (v : ValuationData D A)
    (E : FiniteAbstractFieldExtension G)
    (hnormal : (extensionSubgroup
      E.base.field E.field.field E.below).Normal)
    (q : E.base.field.toSubgroup ⧸
      extensionSubgroup E.base.field E.field.field E.below)
    (a : (extensionFixedRepresentation A E.base.field E.field.field
      E.below hnormal).V) :
    v.valuationAt E.field
        (extensionFixedRepresentationEquiv A E.base.field E.field.field
          E.below hnormal
          ((extensionFixedRepresentation A E.base.field E.field.field
            E.below hnormal).ρ q a)) =
      v.valuationAt E.field
        (extensionFixedRepresentationEquiv A E.base.field E.field.field
          E.below hnormal a) := by
  let := hnormal
  refine Quotient.inductionOn' q ?_
  intro r
  let aL : ambientFixedAddSubgroup A E.field.field :=
    extensionFixedRepresentationEquiv A E.base.field E.field.field
      E.below hnormal a
  have heq :
      extensionFixedRepresentationEquiv A E.base.field E.field.field
          E.below hnormal
          ((extensionFixedRepresentation A E.base.field E.field.field
            E.below hnormal).ρ
            (QuotientGroup.mk r) a) =
        normalExtensionAction A E.base.field E.field.field E.below
          hnormal r aL := by
    apply Subtype.ext
    rfl
  rw [heq]
  exact v.valuationAt_normalExtensionAction E hnormal r aL

/-- The class-field axiom, in representative form: equality of two actual relative
norms yields the element `a` for which `a^σ-a = v-u`. -/
theorem abstractReciprocity_exists_hMinusOne_primitive
    (hcf : SatisfiesClassFieldAxiom A)
    (E : FiniteAbstractFieldExtension G)
    (hnormal : (extensionSubgroup
      E.base.field E.field.field E.below).Normal)
    (g : E.base.field.toSubgroup ⧸
      extensionSubgroup E.base.field E.field.field E.below)
    (hg : ∀ q, q ∈ Subgroup.zpowers g)
    (u w : ambientFixedAddSubgroup A E.field.field)
    (hnorm : relativeNorm A E.base.field E.field.field E.below w =
      relativeNorm A E.base.field E.field.field E.below u) :
    let M := extensionFixedRepresentation A E.base.field E.field.field
      E.below hnormal
    ∃ a : M.V,
      M.ρ g a - a =
        (extensionFixedRepresentationEquiv A E.base.field E.field.field
          E.below hnormal).symm
          (w - u) := by
  let := hnormal
  let := E.finiteQuotient
  let := Fintype.ofFinite
    (E.base.field.toSubgroup ⧸
      extensionSubgroup E.base.field E.field.field E.below)
  let M := extensionFixedRepresentation A E.base.field E.field.field
    E.below hnormal
  let z : M.V :=
    (extensionFixedRepresentationEquiv A E.base.field E.field.field
      E.below hnormal).symm (w - u)
  have hzNorm : M.norm.hom z = 0 := by
    apply Subtype.ext
    calc
      (M.norm.hom z).1 =
          ((relativeNorm A E.base.field E.field.field E.below (w - u) :
            ambientFixedAddSubgroup A E.base.field) : A.V) :=
        extensionFixedRepresentation_norm_coe A E.base.field E.field.field
          E.below hnormal z
      _ = ((relativeNorm A E.base.field E.field.field E.below w -
          relativeNorm A E.base.field E.field.field E.below u :
            ambientFixedAddSubgroup A E.base.field) : A.V) := by
        rw [map_sub]
      _ = 0 := by rw [hnorm, sub_self]; rfl
  let Ecf : FiniteCyclicSubextension E.base :=
    { field := E.field.field
      below := E.below
      normal := hnormal
      finite := E.finiteQuotient
      generator := g
      generates := hg }
  have hzero : Limits.IsZero (tateCohomology M (-1)) := by
    simpa [Ecf,
      FiniteCyclicSubextension.fixedRepresentation] using
        hcf.tateHMinusOne_isZero E.base Ecf
  obtain ⟨a, ha⟩ :=
    CyclicCohomology.normKernel_le_sigmaMinusOneRange_of_tateHMinusOne_isZero
      M g hg hzero z hzNorm
  exact ⟨a, ha⟩

end ValuationData

end
end ClassFormation
end

section
-- module Solutions.OAIQ244_DUKE.AbstractClassFieldTheory_Reciprocity_TotallyRamifiedCase_FrobeniusLift
attribute [-instance] _root_.ClassFormation.instIsAddTorsionFreeZHat _root_.ClassFormation.instIsMulTorsionFreeMultiplicativeZHat _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.DiscreteNthRootsSubgroup.instTopologicalSpaceSubtypeUnitsMemSubgroup _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalClassFieldTheory.baseFixingExtensionQuotient_finite _root_.LocalClassFieldTheory.extensionSubgroupBase_normal _root_.LocalClassFieldTheory.finiteGaloisExtensionSubgroupOfEmbedding_normal _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.LubinTate.compatibleGroupFamiliesGroup _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.RamificationTheory.HilbertRamification.ValuationSubring.inertiaGroup_normal _root_.RamificationTheory.HilbertRamification.ValuationSubring.ramificationGroupInInertiaAut_normal _root_.RayClass.approximationCompletionTopologicalSpace _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.LocalClassFieldTheory.normalizationIntegerRingIsIntegralClosure _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen
attribute [-simp] _root_.ClassFormation.FiniteAbelianSubextension.extensionQuotientMk_apply _root_.ClassFormation.FiniteGaloisSubextension.classFieldCandidate_field _root_.ClassFormation.FiniteGaloisSubextension.intermediateFiniteAbelianOfCommutatorLe_field _root_.ClassFormation.mem_normFilterBasis_iff _root_.ClassFormation.toZModPow_zHatToPadicInt _root_.ClassFormation.zHatReductionRingHom_apply _root_.ClassFormation.zHatRingEquivProfiniteIntegerPrimeProduct_apply _root_.ClassFormation.zHatToPadicInt_intCast _root_.ClassFormation.zHatToProfiniteIntegerPrimeProduct_apply _root_.ClassFormation.zHatToProfiniteIntegerPrimeProduct_intCast _root_.ClassFormation.zHatUnitsContinuousMulEquivPrimeProduct_coe_apply _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.IsDiscreteValuationRing.addVal_ringEquiv _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.KummerTheory.torsionQuotientEquivOfZHatMulDecomposition_mk _root_.KummerTheory.zHatUnitsContinuousMulEquivPrimeProduct_rationalCyclotomicCharacter _root_.LocalClassFieldTheory.baseFixingExtensionQuotientEquivAmbient_mk _root_.LocalClassFieldTheory.finiteResidueFrobeniusFromZHat_apply _root_.LocalClassFieldTheory.finiteResidueFrobeniusFromZHat_one _root_.LocalClassFieldTheory.residueAbsoluteDegreeIn_frobenius _root_.LocalClassFieldTheory.residueAbsoluteFrobenius_one _root_.LocalClassFieldTheory.residueFrobeniusToLimit_apply_component _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.LocalFieldTheory.residueField_algebraMap_residue _root_.OAI.PrimeDegreePackets.ThetaConstruction.schwartzCM_apply _root_.infinitePlace_mult_smul
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

/-!
# Frobenius lifts for totally ramified extensions

This file constructs degree-one Frobenius lifts and the finite auxiliary
Galois extension used in the totally ramified reciprocity argument.
-/

noncomputable section

namespace ClassFormation

open KummerTheory
open CyclicCohomology

-- Mathlib's `Rep ℤ G` currently fixes the acting group to universe zero.
variable {G : IntegralRepGroupType} [Group G] [TopologicalSpace G]

namespace DegreeData

/-- Every automorphism of a totally ramified Galois extension has a
Frobenius lift of exponent one. -/
theorem exists_degreeOneFrobeniusLiftOfTotallyRamified
    (D : DegreeData G)
    (K : FiniteResidueAbstractField D) (L : GaloisSubextension K.field)
    (hTot : L.IsTotallyRamified D)
    (q : L.extensionQuotient) :
    ∃ σ : D.FrobeniusElements K L.field L.below,
      D.frobeniusExponent K L.field L.below σ = 1 ∧
      L.extensionQuotientMulEquiv.symm
        (D.frobeniusRestriction K L.field L.below σ) = q := by
  let φ := D.chosenDegreeOneFrobeniusElement K L.field L.below
  let q₀ := D.frobeniusRestriction K L.field L.below φ
  let qRaw := L.extensionQuotientMulEquiv q
  obtain ⟨s, hs⟩ := QuotientGroup.mk'_surjective
    (extensionSubgroup K.field L.field L.below) (qRaw * q₀⁻¹)
  have hsDegree : D.degree s.1 ∈
      K.field.toSubgroup.map D.degree.toMonoidHom := ⟨s.1, s.2, rfl⟩
  have hImage :=
    (L.isTotallyRamified_iff_image_le D).1 hTot hsDegree
  obtain ⟨l, hlL, hlDegree⟩ := hImage
  let lL : L.field.toSubgroup := ⟨l, hlL⟩
  let lK : K.field.toSubgroup := Subgroup.inclusion L.below lL
  let i : K.field.toSubgroup := s * lK⁻¹
  let t : K.field.toSubgroup ⧸
      D.extensionInertiaWithin K.field L.field L.below :=
    QuotientGroup.mk i * φ.1
  have hiDegree : D.normalizedDegree K i = 1 := by
    change i ∈ (D.normalizedDegree K).toMonoidHom.ker
    rw [D.normalizedDegree_ker K]
    change D.degree i.1 = 1
    dsimp [i, lK, lL]
    rw [map_mul, map_inv]
    change D.degree s.1 * (D.degree l)⁻¹ = 1
    rw [← hlDegree]
    simp
  have htDegree : D.extensionNormalizedDegree K L.field L.below t =
      (Multiplicative.ofAdd (1 : ZHat) : ZHatMul) ^ (1 : ℕ) := by
    change D.extensionNormalizedDegree K L.field L.below
        (QuotientGroup.mk i * φ.1) = _
    rw [map_mul, D.extensionNormalizedDegree_mk, hiDegree, one_mul]
    calc
      D.extensionNormalizedDegree K L.field L.below φ.1 =
          (Multiplicative.ofAdd (1 : ZHat) : ZHatMul) ^
              D.frobeniusExponent K L.field L.below φ :=
        D.extensionNormalizedDegree_frobenius_eq_pow K L.field L.below φ
      _ = (Multiplicative.ofAdd (1 : ZHat) : ZHatMul) ^ (1 : ℕ) := by
        rw [D.frobeniusExponent_chosenDegreeOneFrobeniusElement]
  let σ : D.FrobeniusElements K L.field L.below :=
    ⟨t, 1, Nat.one_pos, htDegree⟩
  have hσExponent : D.frobeniusExponent K L.field L.below σ = 1 := by
    apply proCIntegerOne_pow_nat_injective
    calc
      (Multiplicative.ofAdd (1 : ZHat) : ZHatMul) ^
            D.frobeniusExponent K L.field L.below σ =
          D.extensionNormalizedDegree K L.field L.below σ.1 :=
        (D.extensionNormalizedDegree_frobenius_eq_pow
          K L.field L.below σ).symm
      _ = (Multiplicative.ofAdd (1 : ZHat) : ZHatMul) ^ (1 : ℕ) :=
        htDegree
  refine ⟨σ, hσExponent, ?_⟩
  refine L.extensionQuotientMulEquiv.symm_apply_eq.mpr ?_
  change D.extensionRestriction K.field L.field L.below
      (QuotientGroup.mk i * φ.1) = qRaw
  rw [map_mul, D.extensionRestriction_mk]
  have hiRestriction :
      (QuotientGroup.mk i :
        K.field.toSubgroup ⧸ extensionSubgroup K.field L.field L.below) =
        QuotientGroup.mk s := by
    dsimp [i]
    change (QuotientGroup.mk' (extensionSubgroup K.field L.field L.below))
        (s * lK⁻¹) =
      (QuotientGroup.mk' (extensionSubgroup K.field L.field L.below)) s
    rw [map_mul, map_inv]
    have hlOne :
        (QuotientGroup.mk' (extensionSubgroup K.field L.field L.below)) lK = 1 := by
      apply (QuotientGroup.eq_one_iff _).2
      exact lL.2
    rw [hlOne, inv_one, mul_one]
  rw [hiRestriction]
  change (QuotientGroup.mk' (extensionSubgroup K.field L.field L.below)) s * q₀ = qRaw
  rw [hs]
  simp [q₀]
/-- In a totally ramified finite Galois extension every finite automorphism
has a degree-one Frobenius lift.  This is the element denoted
`\tilde\sigma = \sigma\varphi_L`. -/
noncomputable def chosenDegreeOneFrobeniusLiftOfTotallyRamified
    (D : DegreeData G)
    (K : FiniteResidueAbstractField D) (L : GaloisSubextension K.field)
    (hTot : L.IsTotallyRamified D)
    (q : L.extensionQuotient) :
    D.FrobeniusElements K L.field L.below :=
  Classical.choose
    (D.exists_degreeOneFrobeniusLiftOfTotallyRamified
      K L hTot q)
/-- The chosen Frobenius lift for a totally ramified extension has exponent one. -/
@[simp]
theorem frobeniusExponent_chosenDegreeOneFrobeniusLiftOfTotallyRamified
    (D : DegreeData G)
    (K : FiniteResidueAbstractField D) (L : GaloisSubextension K.field)
    (hTot : L.IsTotallyRamified D)
    (q : L.extensionQuotient) :
    D.frobeniusExponent K L.field L.below
      (D.chosenDegreeOneFrobeniusLiftOfTotallyRamified
        K L hTot q) = 1 := by
  exact (Classical.choose_spec
    (D.exists_degreeOneFrobeniusLiftOfTotallyRamified
      K L hTot q)).1
/-- The chosen degree-one Frobenius lift restricts to the prescribed automorphism. -/
@[simp]
theorem frobeniusRestriction_chosenDegreeOneFrobeniusLiftOfTotallyRamified
    (D : DegreeData G)
    (K : FiniteResidueAbstractField D) (L : GaloisSubextension K.field)
    (hTot : L.IsTotallyRamified D)
    (q : L.extensionQuotient) :
    L.extensionQuotientMulEquiv.symm
        (D.frobeniusRestriction K L.field L.below
          (D.chosenDegreeOneFrobeniusLiftOfTotallyRamified
            K L hTot q)) = q := by
  exact (Classical.choose_spec
    (D.exists_degreeOneFrobeniusLiftOfTotallyRamified
      K L hTot q)).2
/-- Underlying quotient form of the Galois-bundle restriction theorem. -/
theorem frobeniusRestriction_chosenDegreeOneFrobeniusLiftOfTotallyRamified_underlying
    (D : DegreeData G)
    (K : FiniteResidueAbstractField D) (L : GaloisSubextension K.field)
    (hTot : L.IsTotallyRamified D)
    (q : L.extensionQuotient) :
    D.frobeniusRestriction K L.field L.below
        (D.chosenDegreeOneFrobeniusLiftOfTotallyRamified
          K L hTot q) =
      L.extensionQuotientMulEquiv q := by
  apply L.extensionQuotientMulEquiv.symm.injective
  exact
    D.frobeniusRestriction_chosenDegreeOneFrobeniusLiftOfTotallyRamified
      K L hTot q
/-- The degree-one lift specialized to a bundled finite Galois extension.
The conversion to the non-finite Galois boundary and the quotient comparison
are performed once in this definition. -/
noncomputable def chosenDegreeOneFrobeniusLiftOfFiniteTotallyRamified
    (D : DegreeData G)
    (K : FiniteResidueAbstractField D)
    (L : FiniteGaloisSubextension K.field)
    (hTot : L.IsTotallyRamified D)
    (q : L.extensionQuotient) :
    D.FrobeniusElements K L.field L.below :=
  D.chosenDegreeOneFrobeniusLiftOfTotallyRamified
    K L.toGaloisSubextension
      (L.isTotallyRamified_toGaloisSubextension D hTot)
      (L.toGaloisExtensionQuotientMulEquiv q)
/-- The finite totally ramified Frobenius lift has exponent one. -/
@[simp]
theorem frobeniusExponent_chosenDegreeOneFrobeniusLiftOfFiniteTotallyRamified
    (D : DegreeData G)
    (K : FiniteResidueAbstractField D)
    (L : FiniteGaloisSubextension K.field)
    (hTot : L.IsTotallyRamified D)
    (q : L.extensionQuotient) :
    D.frobeniusExponent K L.field L.below
      (D.chosenDegreeOneFrobeniusLiftOfFiniteTotallyRamified
        K L hTot q) = 1 := by
  exact D.frobeniusExponent_chosenDegreeOneFrobeniusLiftOfTotallyRamified
    K L.toGaloisSubextension
      (L.isTotallyRamified_toGaloisSubextension D hTot)
      (L.toGaloisExtensionQuotientMulEquiv q)
/-- The finite totally ramified Frobenius lift restricts to the chosen automorphism. -/
@[simp]
theorem frobeniusRestriction_chosenDegreeOneFrobeniusLiftOfFiniteTotallyRamified
    (D : DegreeData G)
    (K : FiniteResidueAbstractField D)
    (L : FiniteGaloisSubextension K.field)
    (hTot : L.IsTotallyRamified D)
    (q : L.extensionQuotient) :
    L.extensionQuotientMulEquiv.symm
        (D.frobeniusRestriction K L.field L.below
          (D.chosenDegreeOneFrobeniusLiftOfFiniteTotallyRamified
            K L hTot q)) = q := by
  refine L.extensionQuotientMulEquiv.symm_apply_eq.mpr ?_
  have h :=
    D.frobeniusRestriction_chosenDegreeOneFrobeniusLiftOfTotallyRamified_underlying
      K L.toGaloisSubextension
        (L.isTotallyRamified_toGaloisSubextension D hTot)
        (L.toGaloisExtensionQuotientMulEquiv q)
  change
    D.frobeniusRestriction K L.field L.below
        (D.chosenDegreeOneFrobeniusLiftOfTotallyRamified
          K L.toGaloisSubextension
            (L.isTotallyRamified_toGaloisSubextension D hTot)
            (L.toGaloisExtensionQuotientMulEquiv q)) =
      L.extensionQuotientMulEquiv q at h
  exact h
/-- Underlying quotient form of the preceding finite-bundle theorem. -/
theorem frobeniusRestriction_chosenDegreeOneFrobeniusLiftOfFiniteTotallyRamified_underlying
    (D : DegreeData G)
    (K : FiniteResidueAbstractField D)
    (L : FiniteGaloisSubextension K.field)
    (hTot : L.IsTotallyRamified D)
    (q : L.extensionQuotient) :
    D.frobeniusRestriction K L.field L.below
        (D.chosenDegreeOneFrobeniusLiftOfFiniteTotallyRamified
          K L hTot q) =
      L.extensionQuotientMulEquiv q := by
  apply L.extensionQuotientMulEquiv.symm.injective
  exact
    D.frobeniusRestriction_chosenDegreeOneFrobeniusLiftOfFiniteTotallyRamified
      K L hTot q
/-- The finite Galois extension `M / K` chosen.  It contains both
`L` and the degree-one Frobenius fixed field `Σ`, and is contained in the
maximal unramified extension of `L`. -/
noncomputable def abstractReciprocityTotallyRamifiedFiniteGaloisExtension
    (D : DegreeData G)
    [IsTopologicalGroup G] [CompactSpace G] [T2Space G]
    (K : FiniteResidueAbstractField D)
    (L : FiniteGaloisSubextension K.field)
    (hTot : L.IsTotallyRamified D)
    (q : L.extensionQuotient) :
    FiniteGaloisSubextension K.field := by
  let σ := D.chosenDegreeOneFrobeniusLiftOfFiniteTotallyRamified
    K L hTot q
  letI : Finite
      (K.field.toSubgroup ⧸ extensionSubgroup K.field L.field L.below) :=
    L.finite
  let SigmaI := D.frobeniusFixedIntermediateField K L.field L.below σ
  let LI := D.fieldAsMaximalUnramifiedIntermediate K.field L.field L.below
  let C := SigmaI.compositum LI
  letI : (extensionSubgroup K.field (D.maximalUnramifiedField L.field)
      (D.maximalUnramifiedField_le_of_le L.below)).Normal :=
    D.extensionSubgroup_maximalUnramifiedField_normal K.field L.field L.below
  let M := C.galoisRefinement
  exact
    { field := M.field
      below := M.below
      normal := by
        exact FiniteIntermediateField.galoisRefinement_normal C
      finite := M.finite }
/-- The auxiliary reciprocity extension lies below the given totally ramified extension. -/
theorem abstractReciprocityTotallyRamifiedFiniteGaloisExtension_le_L
    (D : DegreeData G)
    [IsTopologicalGroup G] [CompactSpace G] [T2Space G]
    (K : FiniteResidueAbstractField D)
    (L : FiniteGaloisSubextension K.field)
    (hTot : L.IsTotallyRamified D)
    (q : L.extensionQuotient) :
    (D.abstractReciprocityTotallyRamifiedFiniteGaloisExtension
      K L hTot q).field.toSubgroup ≤ L.field.toSubgroup := by
  let σ := D.chosenDegreeOneFrobeniusLiftOfFiniteTotallyRamified
    K L hTot q
  let : Finite
      (K.field.toSubgroup ⧸ extensionSubgroup K.field L.field L.below) :=
    L.finite
  let SigmaI := D.frobeniusFixedIntermediateField K L.field L.below σ
  let LI := D.fieldAsMaximalUnramifiedIntermediate K.field L.field L.below
  let C := SigmaI.compositum LI
  let : (extensionSubgroup K.field (D.maximalUnramifiedField L.field)
      (D.maximalUnramifiedField_le_of_le L.below)).Normal :=
    D.extensionSubgroup_maximalUnramifiedField_normal K.field L.field L.below
  change (C.galoisRefinement).field.toSubgroup ≤ L.field.toSubgroup
  exact C.galoisRefinement_le_field.trans
    (FiniteIntermediateField.compositum_le_right SigmaI LI)
/-- The auxiliary reciprocity extension is fixed by the selected automorphism. -/
theorem abstractReciprocityTotallyRamifiedFiniteGaloisExtension_le_sigma
    (D : DegreeData G)
    [IsTopologicalGroup G] [CompactSpace G] [T2Space G]
    (K : FiniteResidueAbstractField D)
    (L : FiniteGaloisSubextension K.field)
    (hTot : L.IsTotallyRamified D)
    (q : L.extensionQuotient) :
    (D.abstractReciprocityTotallyRamifiedFiniteGaloisExtension
      K L hTot q).field.toSubgroup ≤
      (D.frobeniusFixedField K L.field L.below
        (D.chosenDegreeOneFrobeniusLiftOfFiniteTotallyRamified
          K L hTot q)).toSubgroup := by
  let σ := D.chosenDegreeOneFrobeniusLiftOfFiniteTotallyRamified
    K L hTot q
  let : Finite
      (K.field.toSubgroup ⧸ extensionSubgroup K.field L.field L.below) :=
    L.finite
  let SigmaI := D.frobeniusFixedIntermediateField K L.field L.below σ
  let LI := D.fieldAsMaximalUnramifiedIntermediate K.field L.field L.below
  let C := SigmaI.compositum LI
  let : (extensionSubgroup K.field (D.maximalUnramifiedField L.field)
      (D.maximalUnramifiedField_le_of_le L.below)).Normal :=
    D.extensionSubgroup_maximalUnramifiedField_normal K.field L.field L.below
  change (C.galoisRefinement).field.toSubgroup ≤ SigmaI.field.toSubgroup
  exact C.galoisRefinement_le_field.trans
    (FiniteIntermediateField.compositum_le_left SigmaI LI)

/-- The maximal unramified field lies below the auxiliary totally ramified reciprocity field. -/
theorem maximalUnramifiedField_le_abstractReciprocityTotallyRamifiedFiniteGaloisExtension
    (D : DegreeData G)
    [IsTopologicalGroup G] [CompactSpace G] [T2Space G]
    (K : FiniteResidueAbstractField D)
    (L : FiniteGaloisSubextension K.field)
    (hTot : L.IsTotallyRamified D)
    (q : L.extensionQuotient) :
    (D.maximalUnramifiedField L.field).toSubgroup ≤
      (D.abstractReciprocityTotallyRamifiedFiniteGaloisExtension
        K L hTot q).field.toSubgroup := by
  let σ := D.chosenDegreeOneFrobeniusLiftOfFiniteTotallyRamified
    K L hTot q
  let : Finite
      (K.field.toSubgroup ⧸ extensionSubgroup K.field L.field L.below) :=
    L.finite
  let SigmaI := D.frobeniusFixedIntermediateField K L.field L.below σ
  let LI := D.fieldAsMaximalUnramifiedIntermediate K.field L.field L.below
  let C := SigmaI.compositum LI
  let : (extensionSubgroup K.field (D.maximalUnramifiedField L.field)
      (D.maximalUnramifiedField_le_of_le L.below)).Normal :=
    D.extensionSubgroup_maximalUnramifiedField_normal K.field L.field L.below
  change (D.maximalUnramifiedField L.field).toSubgroup ≤
    (C.galoisRefinement).field.toSubgroup
  exact (C.galoisRefinement).above

end DegreeData

end ClassFormation
end
end

section
-- module Solutions.OAIQ244_DUKE.AbstractClassFieldTheory_Reciprocity_TotallyRamifiedCase_RestrictionCosets
attribute [-instance] _root_.ClassFormation.instIsAddTorsionFreeZHat _root_.ClassFormation.instIsMulTorsionFreeMultiplicativeZHat _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.KummerTheory.finite_finsupp_nsmulQuotient _root_.LocalClassFieldTheory.baseFixingExtensionQuotient_finite _root_.LocalClassFieldTheory.extensionSubgroupBase_normal _root_.LocalClassFieldTheory.finiteGaloisExtensionSubgroupOfEmbedding_normal _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitQuotientCarrier_finite _root_.LocalFieldTheory.DiscreteValuationField.finite_padicInt_finPi_nsmulQuotient _root_.LocalFieldTheory.DiscreteValuationField.finite_padicInt_pi_nsmulQuotient_of_coprime _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_multiplicative_nthPowerQuotient _root_.LocalFieldTheory.finite_nsmulAddQuotient_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.LubinTate.compatibleGroupFamiliesGroup _root_.OAI.PrimeDegreePackets.boundedRealFields_finite _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.RamificationTheory.HilbertRamification.ValuationSubring.inertiaGroup_normal _root_.RamificationTheory.HilbertRamification.ValuationSubring.ramificationGroupInInertiaAut_normal _root_.RayClass.approximationCompletionTopologicalSpace _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.maximalIdealPowSuccQuotModule _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.LocalClassFieldTheory.normalizationIntegerRingIsIntegralClosure _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen
attribute [-simp] _root_.ClassFormation.DegreeData.frobeniusExponent_chosenDegreeOneFrobeniusLiftOfFiniteTotallyRamified _root_.ClassFormation.DegreeData.frobeniusExponent_chosenDegreeOneFrobeniusLiftOfTotallyRamified _root_.ClassFormation.DegreeData.frobeniusRestriction_chosenDegreeOneFrobeniusLiftOfFiniteTotallyRamified _root_.ClassFormation.DegreeData.frobeniusRestriction_chosenDegreeOneFrobeniusLiftOfTotallyRamified _root_.ClassFormation.FiniteAbelianSubextension.extensionQuotientMk_apply _root_.ClassFormation.FiniteGaloisSubextension.classFieldCandidate_field _root_.ClassFormation.FiniteGaloisSubextension.intermediateFiniteAbelianOfCommutatorLe_field _root_.ClassFormation.mem_normFilterBasis_iff _root_.ClassFormation.toZModPow_zHatToPadicInt _root_.ClassFormation.zHatReductionRingHom_apply _root_.ClassFormation.zHatRingEquivProfiniteIntegerPrimeProduct_apply _root_.ClassFormation.zHatToPadicInt_intCast _root_.ClassFormation.zHatToProfiniteIntegerPrimeProduct_apply _root_.ClassFormation.zHatToProfiniteIntegerPrimeProduct_intCast _root_.ClassFormation.zHatUnitsContinuousMulEquivPrimeProduct_coe_apply _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.IsDiscreteValuationRing.addVal_ringEquiv _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.KummerTheory.torsionQuotientEquivOfZHatMulDecomposition_mk _root_.KummerTheory.zHatUnitsContinuousMulEquivPrimeProduct_rationalCyclotomicCharacter _root_.LocalClassFieldTheory.baseFixingExtensionQuotientEquivAmbient_mk _root_.LocalClassFieldTheory.baseUnitsEquivGaloisAmbientFixed_val _root_.LocalClassFieldTheory.embeddedFieldUnitsEquivGaloisFixed_coe _root_.LocalClassFieldTheory.finiteGaloisUnitsEquivAbstractFixedOfEmbedding_coe _root_.LocalClassFieldTheory.finiteGaloisUnitsEquivAbstractFixed_coe _root_.LocalClassFieldTheory.finiteResidueFrobeniusFromZHat_apply _root_.LocalClassFieldTheory.finiteResidueFrobeniusFromZHat_one _root_.LocalClassFieldTheory.intermediateFieldUnitsEquivGaloisFixed_coe _root_.LocalClassFieldTheory.residueAbsoluteDegreeIn_frobenius _root_.LocalClassFieldTheory.residueAbsoluteFrobenius_one _root_.LocalClassFieldTheory.residueFrobeniusToLimit_apply_component _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.LocalFieldTheory.residueField_algebraMap_residue _root_.OAI.PrimeDegreePackets.ThetaConstruction.schwartzCM_apply _root_.infinitePlace_mult_smul
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

/-!
# Restriction transport for finite Galois subextensions

This file constructs quotient restriction maps, their coset equivalences,
and the compatible relative actions and norms used in ramified towers.
-/

noncomputable section

namespace ClassFormation

open KummerTheory
open CyclicCohomology

-- Mathlib's `Rep ℤ G` currently fixes the acting group to universe zero.
variable {G : IntegralRepGroupType} [Group G] [TopologicalSpace G]

namespace FiniteGaloisSubextension

/-- Restriction between the named finite Galois quotient boundaries. -/
def bundledRestrictionHom
    {K : ClosedSubgroup G}
    (M L : FiniteGaloisSubextension K)
    (hML : M.field.toSubgroup ≤ L.field.toSubgroup) :
    M.extensionQuotient →* L.extensionQuotient :=
  L.extensionQuotientMulEquiv.symm.toMonoidHom.comp
    ((abstractReciprocityRestriction
      K L.field M.field hML L.below).comp
        M.extensionQuotientMulEquiv.toMonoidHom)

/-- The coset map from the lower maximal-unramified quotient to a totally
ramified quotient. -/
noncomputable def abstractReciprocityRestrictionCosetMap
    (D : DegreeData G) [IsTopologicalGroup G]
    (E : DegreeData.AbstractExtension G)
    (M : FiniteGaloisSubextension E.base)
    (hME : M.field.toSubgroup ≤ E.field.toSubgroup) :
    let M₀ := M.maximalUnramifiedSubextension D
    let hMM₀ : M.field.toSubgroup ≤ M₀.toSubgroup :=
      M.field_le_intermediateField (M.inertiaImage D)
    (M₀.toSubgroup ⧸ extensionSubgroup M₀ M.field hMM₀) →
      (E.base.toSubgroup ⧸ E.subgroup) := by
  let S := M.inertiaImage D
  let M₀ := M.maximalUnramifiedSubextension D
  let hMM₀ : M.field.toSubgroup ≤ M₀.toSubgroup :=
    M.field_le_intermediateField S
  let hM₀K : M₀.toSubgroup ≤ E.base.toSubgroup :=
    M.intermediateField_le_base S
  exact Quotient.map'
    (fun x : M₀.toSubgroup =>
      (⟨x.1, hM₀K x.2⟩ : E.base.toSubgroup))
    (by
      intro x y hxy
      rw [QuotientGroup.leftRel_apply] at hxy ⊢
      exact hME hxy)

/-- The restriction coset map is bijective when the upper extension is
totally ramified and the auxiliary field contains the relevant inertia. -/
theorem abstractReciprocityRestrictionCosetMap_bijective
    (D : DegreeData G) [IsTopologicalGroup G]
    (E : DegreeData.AbstractExtension G)
    (M : FiniteGaloisSubextension E.base)
    (hME : M.field.toSubgroup ≤ E.field.toSubgroup)
    (hTot : E.IsTotallyRamified D)
    (hInertia : ∀ i : E.base.toSubgroup,
      i ∈ D.fieldInertiaWithin E.base →
      i.1 ∈ E.field.toSubgroup → i.1 ∈ M.field.toSubgroup) :
    Function.Bijective (M.abstractReciprocityRestrictionCosetMap D E hME) := by
  let S := M.inertiaImage D
  let M₀ := M.maximalUnramifiedSubextension D
  let hMM₀ : M.field.toSubgroup ≤ M₀.toSubgroup :=
    M.field_le_intermediateField S
  let hM₀K : M₀.toSubgroup ≤ E.base.toSubgroup :=
    M.intermediateField_le_base S
  constructor
  · intro x y hxy
    refine Quotient.inductionOn₂' x y ?_ hxy
    intro a b hab
    apply Quotient.sound'
    rw [QuotientGroup.leftRel_apply]
    let aK : E.base.toSubgroup := ⟨a.1, hM₀K a.2⟩
    let bK : E.base.toSubgroup := ⟨b.1, hM₀K b.2⟩
    let z : E.base.toSubgroup := aK⁻¹ * bK
    have habE : aK⁻¹ * bK ∈ E.subgroup := by
      exact QuotientGroup.leftRel_apply.mp (Quotient.exact' hab)
    have hzE : z.1 ∈ E.field.toSubgroup :=
      (mem_extensionSubgroup_iff E.base E.field E.below z).1 habE
    have haP : aK ∈ M.intermediateSubgroup S := by
      rw [← M.extensionSubgroup_intermediateField_eq S]
      exact (mem_extensionSubgroup_iff E.base M₀ hM₀K aK).2 a.2
    have hbP : bK ∈ M.intermediateSubgroup S := by
      rw [← M.extensionSubgroup_intermediateField_eq S]
      exact (mem_extensionSubgroup_iff E.base M₀ hM₀K bK).2 b.2
    have hzP : z ∈ M.intermediateSubgroup S :=
      (M.intermediateSubgroup S).mul_mem
        ((M.intermediateSubgroup S).inv_mem haP) hbP
    change (QuotientGroup.mk'
      (extensionSubgroup E.base M.field M.below)) z ∈
        (D.fieldInertiaWithin E.base).map
          (QuotientGroup.mk'
            (extensionSubgroup E.base M.field M.below)) at hzP
    obtain ⟨i, hiI, hi⟩ := hzP
    have hizM : i⁻¹ * z ∈ extensionSubgroup E.base M.field M.below :=
      QuotientGroup.eq.mp hi
    have hizM' : i.1⁻¹ * z.1 ∈ M.field.toSubgroup :=
      (mem_extensionSubgroup_iff E.base M.field M.below (i⁻¹ * z)).1 hizM
    have hiE : i.1 ∈ E.field.toSubgroup := by
      have hmul := E.field.toSubgroup.mul_mem hzE
        (E.field.toSubgroup.inv_mem (hME hizM'))
      simpa [mul_inv_rev, mul_assoc] using hmul
    have hiM : i.1 ∈ M.field.toSubgroup := hInertia i hiI hiE
    have hzM : z.1 ∈ M.field.toSubgroup := by
      have hmul := M.field.toSubgroup.mul_mem hiM hizM'
      simpa [mul_assoc] using hmul
    exact hzM
  · intro x
    refine Quotient.inductionOn' x ?_
    intro k
    have hkDegree : D.degree k.1 ∈
        E.base.toSubgroup.map D.degree.toMonoidHom := ⟨k.1, k.2, rfl⟩
    obtain ⟨e, heE, heDegree⟩ :=
      (E.isTotallyRamified_iff_image_le D).1 hTot hkDegree
    let eE : E.field.toSubgroup := ⟨e, heE⟩
    let eK : E.base.toSubgroup := Subgroup.inclusion E.below eE
    let i : E.base.toSubgroup := k * eK⁻¹
    have hiI : i ∈ D.fieldInertiaWithin E.base := by
      change D.degree i.1 = 1
      dsimp [i, eK, eE]
      rw [map_mul, map_inv]
      change D.degree k.1 * (D.degree e)⁻¹ = 1
      change D.degree e = D.degree k.1 at heDegree
      rw [heDegree]
      simp
    have hiS : (QuotientGroup.mk'
        (extensionSubgroup E.base M.field M.below)) i ∈ S :=
      ⟨i, hiI, rfl⟩
    have hiP : i ∈ M.intermediateSubgroup S := hiS
    let iM₀ : M₀.toSubgroup := ⟨i.1, ⟨i, hiP, rfl⟩⟩
    refine ⟨QuotientGroup.mk iM₀, ?_⟩
    apply Quotient.sound'
    rw [QuotientGroup.leftRel_apply]
    change (i⁻¹ * k).1 ∈ E.field.toSubgroup
    simpa [i, eK, eE, mul_inv_rev, mul_assoc] using eE.2

/-- The equivalence induced by the totally ramified restriction coset map. -/
noncomputable def abstractReciprocityRestrictionCosetEquiv
    (D : DegreeData G) [IsTopologicalGroup G]
    (E : DegreeData.AbstractExtension G)
    (M : FiniteGaloisSubextension E.base)
    (hME : M.field.toSubgroup ≤ E.field.toSubgroup)
    (hTot : E.IsTotallyRamified D)
    (hInertia : ∀ i : E.base.toSubgroup,
      i ∈ D.fieldInertiaWithin E.base →
      i.1 ∈ E.field.toSubgroup → i.1 ∈ M.field.toSubgroup) :
    let M₀ := M.maximalUnramifiedSubextension D
    let hMM₀ : M.field.toSubgroup ≤ M₀.toSubgroup :=
      M.field_le_intermediateField (M.inertiaImage D)
    (M₀.toSubgroup ⧸ extensionSubgroup M₀ M.field hMM₀) ≃
      E.quotient :=
  Equiv.ofBijective (M.abstractReciprocityRestrictionCosetMap D E hME)
    (M.abstractReciprocityRestrictionCosetMap_bijective
      D E hME hTot hInertia)

/-- The multiplicative restriction equivalence from the lower Galois group
to the original totally ramified quotient. -/
noncomputable def abstractReciprocityRestrictionMulEquiv
    (D : DegreeData G) [IsTopologicalGroup G]
    (E : DegreeData.AbstractExtension G)
    (M : FiniteGaloisSubextension E.base)
    (hME : M.field.toSubgroup ≤ E.field.toSubgroup)
    [hEnormal :
      (extensionSubgroup E.base E.field E.below).Normal]
    (hTot : E.IsTotallyRamified D)
    (hInertia : ∀ i : E.base.toSubgroup,
      i ∈ D.fieldInertiaWithin E.base →
      i.1 ∈ E.field.toSubgroup → i.1 ∈ M.field.toSubgroup) :
    let S := M.inertiaImage D
    let N := M.lowerFiniteGalois S
    letI : (extensionSubgroup
        (M.maximalUnramifiedSubextension D) M.field N.below).Normal :=
      N.normal
    letI : Group E.quotient := by
      change Group
        (E.base.toSubgroup ⧸ extensionSubgroup E.base E.field E.below)
      infer_instance
    N.extensionQuotient ≃*
      E.quotient := by
  let S := M.inertiaImage D
  let M₀ := M.maximalUnramifiedSubextension D
  let N := M.lowerFiniteGalois S
  let hM₀K : M₀.toSubgroup ≤ E.base.toSubgroup :=
    M.intermediateField_le_base S
  letI : (extensionSubgroup M₀ M.field N.below).Normal := N.normal
  letI : Group E.quotient := by
    change Group
      (E.base.toSubgroup ⧸ extensionSubgroup E.base E.field E.below)
    infer_instance
  let r : N.extensionQuotient →*
      E.quotient :=
    QuotientGroup.map
      (extensionSubgroup M₀ M.field N.below)
      (extensionSubgroup E.base E.field E.below)
      (Subgroup.inclusion hM₀K)
      (by
        intro m hm
        exact hME hm)
  apply MulEquiv.ofBijective r
  have hr : (r : N.extensionQuotient →
      E.quotient) =
      M.abstractReciprocityRestrictionCosetMap D E hME := by
    funext x
    refine Quotient.inductionOn' x ?_
    intro m
    rfl
  rw [hr]
  exact M.abstractReciprocityRestrictionCosetMap_bijective
    D E hME hTot hInertia

/-- Relative coset actions are transported by the restriction coset
equivalence. -/
theorem relativeCosetAction_abstractReciprocityRestrictionCosetEquiv
    (A : Rep ℤ G) (D : DegreeData G) [IsTopologicalGroup G]
    (E : DegreeData.AbstractExtension G)
    (M : FiniteGaloisSubextension E.base)
    (hME : M.field.toSubgroup ≤ E.field.toSubgroup)
    (hTot : E.IsTotallyRamified D)
    (hInertia : ∀ i : E.base.toSubgroup,
      i ∈ D.fieldInertiaWithin E.base →
      i.1 ∈ E.field.toSubgroup → i.1 ∈ M.field.toSubgroup)
    (a : ambientFixedAddSubgroup A E.field)
    (r : let M₀ := M.maximalUnramifiedSubextension D
      let hMM₀ : M.field.toSubgroup ≤ M₀.toSubgroup :=
        M.field_le_intermediateField (M.inertiaImage D)
      M₀.toSubgroup ⧸ extensionSubgroup M₀ M.field hMM₀) :
    let M₀ := M.maximalUnramifiedSubextension D
    let hMM₀ : M.field.toSubgroup ≤ M₀.toSubgroup :=
      M.field_le_intermediateField (M.inertiaImage D)
    relativeCosetAction A M₀ M.field hMM₀
        (fixedFieldInclusion A E.field M.field hME a) r =
      relativeCosetAction A E.base E.field E.below a
        (M.abstractReciprocityRestrictionCosetEquiv
          D E hME hTot hInertia r) := by
  let S := M.inertiaImage D
  let M₀ := M.maximalUnramifiedSubextension D
  let hMM₀ : M.field.toSubgroup ≤ M₀.toSubgroup :=
    M.field_le_intermediateField S
  let hM₀K : M₀.toSubgroup ≤ E.base.toSubgroup :=
    M.intermediateField_le_base S
  refine Quotient.inductionOn' r ?_
  intro x
  rfl

/-- Relative norm commutes with fixed-field inclusion along the totally
ramified restriction equivalence. -/
theorem abstractReciprocity_relativeNorm_fixedFieldInclusion
    (A : Rep ℤ G) (D : DegreeData G) [IsTopologicalGroup G]
    (E : DegreeData.FiniteAbstractExtension G)
    (M : FiniteGaloisSubextension E.base)
    (hME : M.field.toSubgroup ≤ E.field.toSubgroup)
    (hTot : E.IsTotallyRamified D)
    (hInertia : ∀ i : E.base.toSubgroup,
      i ∈ D.fieldInertiaWithin E.base →
      i.1 ∈ E.field.toSubgroup → i.1 ∈ M.field.toSubgroup)
    (a : ambientFixedAddSubgroup A E.field) :
    let M₀ := M.maximalUnramifiedSubextension D
    let hMM₀ : M.field.toSubgroup ≤ M₀.toSubgroup :=
      M.field_le_intermediateField (M.inertiaImage D)
    let hM₀K : M₀.toSubgroup ≤ E.base.toSubgroup :=
      M.intermediateField_le_base (M.inertiaImage D)
    letI : Finite
        (M₀.toSubgroup ⧸ extensionSubgroup M₀ M.field hMM₀) :=
      M.extension_over_intermediate_finite (M.inertiaImage D)
    relativeNorm A M₀ M.field hMM₀
        (fixedFieldInclusion A E.field M.field hME a) =
      fixedFieldInclusion A E.base M₀ hM₀K
        (relativeNorm A E.base E.field E.below a) := by
  let S := M.inertiaImage D
  let M₀ := M.maximalUnramifiedSubextension D
  let hMM₀ : M.field.toSubgroup ≤ M₀.toSubgroup :=
    M.field_le_intermediateField S
  let hM₀K : M₀.toSubgroup ≤ E.base.toSubgroup :=
    M.intermediateField_le_base S
  let hMfinite : Finite
      (M₀.toSubgroup ⧸ extensionSubgroup M₀ M.field hMM₀) :=
    M.extension_over_intermediate_finite S
  let : Finite
      (E.base.toSubgroup ⧸ extensionSubgroup E.base E.field E.below) :=
    E.finiteQuotient
  let e : (M₀.toSubgroup ⧸ extensionSubgroup M₀ M.field hMM₀) ≃
      (E.base.toSubgroup ⧸ extensionSubgroup E.base E.field E.below) :=
    M.abstractReciprocityRestrictionCosetEquiv
      D E.toAbstractExtension hME hTot hInertia
  apply Subtype.ext
  let : Fintype
      (M₀.toSubgroup ⧸ extensionSubgroup M₀ M.field hMM₀) :=
    Fintype.ofFinite _
  let : Fintype
      (E.base.toSubgroup ⧸ extensionSubgroup E.base E.field E.below) :=
    Fintype.ofFinite _
  change (∑ r, relativeCosetAction A M₀ M.field hMM₀
      (fixedFieldInclusion A E.field M.field hME a) r) =
    ∑ q, relativeCosetAction A E.base E.field E.below a q
  calc
    ∑ r, relativeCosetAction A M₀ M.field hMM₀
        (fixedFieldInclusion A E.field M.field hME a) r =
      ∑ r, relativeCosetAction A E.base E.field E.below a (e r) := by
        apply Fintype.sum_congr
        intro r
        exact M.relativeCosetAction_abstractReciprocityRestrictionCosetEquiv
          A D E.toAbstractExtension hME hTot hInertia a r
    _ = ∑ q, relativeCosetAction A E.base E.field E.below a q :=
      e.sum_comp (relativeCosetAction A E.base E.field E.below a)

/-- Two auxiliary quotient elements commute when they have the same
restriction and the auxiliary field contains the inertia subgroup. -/
theorem commute_of_same_restriction_of_inertia_le
    (D : DegreeData G) [IsTopologicalGroup G]
    (E : DegreeData.AbstractExtension G)
    (M : FiniteGaloisSubextension E.base)
    (hME : M.field.toSubgroup ≤ E.field.toSubgroup)
    (hIE : (D.fieldInertia E.field).toSubgroup ≤ M.field.toSubgroup)
    [hEnormal :
      (extensionSubgroup E.base E.field E.below).Normal]
    (g t : E.base.toSubgroup ⧸
      extensionSubgroup E.base M.field M.below)
    (hres : abstractReciprocityRestriction
        E.base E.field M.field hME E.below g =
      abstractReciprocityRestriction
        E.base E.field M.field hME E.below t) :
    Commute g t := by
  rw [Commute]
  let a : E.base.toSubgroup := Quotient.out g
  let b : E.base.toSubgroup := Quotient.out t
  have ha : (QuotientGroup.mk'
      (extensionSubgroup E.base M.field M.below)) a = g :=
    Quotient.out_eq' g
  have hb : (QuotientGroup.mk'
      (extensionSubgroup E.base M.field M.below)) b = t :=
    Quotient.out_eq' t
  have hcosetE :
      (QuotientGroup.mk'
        (extensionSubgroup E.base E.field E.below)) (a * b) =
      (QuotientGroup.mk'
        (extensionSubgroup E.base E.field E.below)) (b * a) := by
    rw [map_mul, map_mul]
    have haE : (QuotientGroup.mk'
        (extensionSubgroup E.base E.field E.below)) a =
        abstractReciprocityRestriction
          E.base E.field M.field hME E.below g := by
      calc
        (QuotientGroup.mk'
            (extensionSubgroup E.base E.field E.below)) a =
            abstractReciprocityRestriction E.base E.field M.field hME E.below
              ((QuotientGroup.mk'
                (extensionSubgroup E.base M.field M.below)) a) := rfl
        _ = abstractReciprocityRestriction
            E.base E.field M.field hME E.below g :=
          congrArg (abstractReciprocityRestriction
            E.base E.field M.field hME E.below) ha
    have hbE : (QuotientGroup.mk'
        (extensionSubgroup E.base E.field E.below)) b =
        abstractReciprocityRestriction
          E.base E.field M.field hME E.below t := by
      calc
        (QuotientGroup.mk'
            (extensionSubgroup E.base E.field E.below)) b =
            abstractReciprocityRestriction E.base E.field M.field hME E.below
              ((QuotientGroup.mk'
                (extensionSubgroup E.base M.field M.below)) b) := rfl
        _ = abstractReciprocityRestriction
            E.base E.field M.field hME E.below t :=
          congrArg (abstractReciprocityRestriction
            E.base E.field M.field hME E.below) hb
    rw [haE, hbE, hres]
  let z : E.base.toSubgroup := (a * b)⁻¹ * (b * a)
  have hzE : z ∈ extensionSubgroup E.base E.field E.below :=
    QuotientGroup.eq.mp hcosetE
  have hzE' : z.1 ∈ E.field.toSubgroup :=
    (mem_extensionSubgroup_iff E.base E.field E.below z).1 hzE
  have hzDegree : D.degree z.1 = 1 := by
    dsimp [z]
    rw [map_mul, map_inv, map_mul, map_mul]
    apply Multiplicative.ext
    change -((D.degree a.1).toAdd + (D.degree b.1).toAdd) +
        ((D.degree b.1).toAdd + (D.degree a.1).toAdd) = 0
    abel
  have hzM : z.1 ∈ M.field.toSubgroup :=
    hIE ⟨hzE', hzDegree⟩
  have hzH : z ∈ extensionSubgroup E.base M.field M.below :=
    (mem_extensionSubgroup_iff E.base M.field M.below z).2 hzM
  calc
    g * t = (QuotientGroup.mk'
        (extensionSubgroup E.base M.field M.below)) (a * b) := by
      rw [map_mul, ha, hb]
    _ = (QuotientGroup.mk'
        (extensionSubgroup E.base M.field M.below)) (b * a) :=
      QuotientGroup.eq.mpr hzH
    _ = t * g := by rw [map_mul, ha, hb]

/-- Equal restrictions induce equal relative coset actions on elements
fixed by the upper field. -/
theorem relativeCosetAction_eq_of_restriction_eq
    (A : Rep ℤ G) (E : DegreeData.AbstractExtension G)
    (M : FiniteGaloisSubextension E.base)
    (hME : M.field.toSubgroup ≤ E.field.toSubgroup)
    [hEnormal :
      (extensionSubgroup E.base E.field E.below).Normal]
    (a : ambientFixedAddSubgroup A E.field)
    (g t : E.base.toSubgroup ⧸
      extensionSubgroup E.base M.field M.below)
    (hres : abstractReciprocityRestriction
        E.base E.field M.field hME E.below g =
      abstractReciprocityRestriction
        E.base E.field M.field hME E.below t) :
    relativeCosetAction A E.base M.field M.below
        (fixedFieldInclusion A E.field M.field hME a) g =
      relativeCosetAction A E.base M.field M.below
        (fixedFieldInclusion A E.field M.field hME a) t := by
  refine Quotient.inductionOn₂' g t ?_ hres
  intro x y hxy
  simp only [relativeCosetAction_mk, fixedFieldInclusion_coe]
  have hxyE : x⁻¹ * y ∈ extensionSubgroup E.base E.field E.below :=
    QuotientGroup.eq.mp hxy
  let e : E.field.toSubgroup := ⟨(x⁻¹ * y).1, hxyE⟩
  have hy : y = x * Subgroup.inclusion E.below e := by
    apply Subtype.ext
    simp [e]
  rw [hy]
  change A.ρ x.1 a.1 = A.ρ (x.1 * e.1) a.1
  rw [map_mul]
  change A.ρ x.1 a.1 = A.ρ x.1 (A.ρ e.1 a.1)
  rw [a.2 e]

end FiniteGaloisSubextension

end ClassFormation
end
end

section
-- module Solutions.OAIQ244_DUKE.AbstractClassFieldTheory_Reciprocity_TotallyRamifiedCase_RestrictionEquiv
attribute [-instance] _root_.ClassFormation.instIsAddTorsionFreeZHat _root_.ClassFormation.instIsMulTorsionFreeMultiplicativeZHat _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalClassFieldTheory.baseFixingExtensionQuotient_finite _root_.LocalClassFieldTheory.extensionSubgroupBase_normal _root_.LocalClassFieldTheory.finiteGaloisExtensionSubgroupOfEmbedding_normal _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.LubinTate.compatibleGroupFamiliesGroup _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.RamificationTheory.HilbertRamification.ValuationSubring.inertiaGroup_normal _root_.RamificationTheory.HilbertRamification.ValuationSubring.ramificationGroupInInertiaAut_normal _root_.RayClass.approximationCompletionTopologicalSpace _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.LocalClassFieldTheory.normalizationIntegerRingIsIntegralClosure _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen
attribute [-simp] _root_.ClassFormation.FiniteGaloisSubextension.classFieldCandidate_field _root_.ClassFormation.FiniteGaloisSubextension.intermediateFiniteAbelianOfCommutatorLe_field _root_.ClassFormation.mem_normFilterBasis_iff _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.IsDiscreteValuationRing.addVal_ringEquiv _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.LocalFieldTheory.residueField_algebraMap_residue _root_.OAI.PrimeDegreePackets.ThetaConstruction.schwartzCM_apply _root_.infinitePlace_mult_smul
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

/-!
# The lower Galois group in the totally ramified auxiliary tower

This file identifies the lower Galois group with the original totally
ramified quotient and constructs its cyclic generator.
-/

noncomputable section

namespace ClassFormation

open KummerTheory
open CyclicCohomology

-- Mathlib's `Rep ℤ G` currently fixes the acting group to universe zero.
variable {G : IntegralRepGroupType} [Group G] [TopologicalSpace G]

namespace DegreeData

/-- Restriction identifies the actual lower Galois group `G(M/M⁰)` with
the original totally ramified group `G(L/K)`. -/
noncomputable def abstractReciprocityTotallyRamifiedRestrictionEquiv
    (D : DegreeData G)
    [IsTopologicalGroup G] [CompactSpace G] [T2Space G]
    (K : FiniteResidueAbstractField D)
    (L : FiniteGaloisSubextension K.field)
    (hTot : L.IsTotallyRamified D)
    (q : L.extensionQuotient) :
    let M := D.abstractReciprocityTotallyRamifiedFiniteGaloisExtension
      K L hTot q
    let S := M.inertiaImage D
    let N := M.lowerFiniteGalois S
    letI : (extensionSubgroup
        (M.maximalUnramifiedSubextension D) M.field N.below).Normal :=
      N.normal
    N.extensionQuotient ≃* L.extensionQuotient := by
  let M := D.abstractReciprocityTotallyRamifiedFiniteGaloisExtension
    K L hTot q
  let hML := D.abstractReciprocityTotallyRamifiedFiniteGaloisExtension_le_L
    K L hTot q
  have hInertia : ∀ i : K.field.toSubgroup,
      i ∈ D.fieldInertiaWithin K.field →
      i.1 ∈ L.field.toSubgroup → i.1 ∈ M.field.toSubgroup := by
    intro i hiI hiL
    apply D.maximalUnramifiedField_le_abstractReciprocityTotallyRamifiedFiniteGaloisExtension
      K L hTot q
    exact ⟨hiL, (D.mem_fieldInertiaWithin_iff K.field i).1 hiI⟩
  letI : (extensionSubgroup K.field L.field L.below).Normal := L.normal
  let EL := L.toFiniteAbstractExtension.toAbstractExtension
  letI : (extensionSubgroup EL.base EL.field EL.below).Normal := by
    change (extensionSubgroup K.field L.field L.below).Normal
    exact L.normal
  letI : Group EL.quotient := by
    change Group
      (K.field.toSubgroup ⧸ extensionSubgroup K.field L.field L.below)
    infer_instance
  exact (M.abstractReciprocityRestrictionMulEquiv
    D EL
      hML hTot hInertia).trans
      L.extensionQuotientMulEquiv.symm

/-- Restriction identifies the degree of the totally ramified lower
extension `M/M⁰` with the original cyclic degree `[L:K]`. -/
theorem abstractReciprocityTotallyRamifiedLowerDegree_eq
    (D : DegreeData G)
    [IsTopologicalGroup G] [CompactSpace G] [T2Space G]
    (K : FiniteResidueAbstractField D)
    (L : FiniteGaloisSubextension K.field)
    (hTot : L.IsTotallyRamified D)
    (q : L.extensionQuotient) :
  let M := D.abstractReciprocityTotallyRamifiedFiniteGaloisExtension
    K L hTot q
  let N := M.lowerFiniteGalois (M.inertiaImage D)
  (N.toFiniteAbstractExtension.degree : ℕ) =
    (L.toFiniteAbstractExtension.degree : ℕ) := by
  let M := D.abstractReciprocityTotallyRamifiedFiniteGaloisExtension
    K L hTot q
  let S := M.inertiaImage D
  let M₀ := M.maximalUnramifiedSubextension D
  let hMM₀ : M.field.toSubgroup ≤ M₀.toSubgroup :=
    M.field_le_intermediateField S
  let N := M.lowerFiniteGalois S
  let E := L.toFiniteAbstractExtension
  let e := D.abstractReciprocityTotallyRamifiedRestrictionEquiv
    K L hTot q
  calc
    (N.toFiniteAbstractExtension.degree : ℕ) =
        (extensionSubgroup M₀ M.field hMM₀).index :=
      N.toFiniteAbstractExtension.extensionSubgroup_index_eq_degree.symm
    _ = Nat.card N.extensionQuotient :=
      Subgroup.index_eq_card (extensionSubgroup M₀ M.field hMM₀)
    _ = Nat.card L.extensionQuotient :=
      Nat.card_congr e.toEquiv
    _ = (extensionSubgroup K.field L.field L.below).index :=
      (Subgroup.index_eq_card (extensionSubgroup K.field L.field L.below)).symm
    _ = (E.degree : ℕ) := by
      have h := E.extensionSubgroup_index_eq_degree
      change (extensionSubgroup K.field L.field L.below).index =
        (E.degree : ℕ) at h
      exact h

/-- The generator of `G(M/M⁰)` corresponding to the prescribed generator
of `G(L/K)`. -/
noncomputable def abstractReciprocityTotallyRamifiedLowerGenerator
    (D : DegreeData G)
    [IsTopologicalGroup G] [CompactSpace G] [T2Space G]
    (K : FiniteResidueAbstractField D)
    (L : FiniteGaloisSubextension K.field)
    (hTot : L.IsTotallyRamified D)
    (q : L.extensionQuotient) :
    let M := D.abstractReciprocityTotallyRamifiedFiniteGaloisExtension
      K L hTot q
    let S := M.inertiaImage D
    let N := M.lowerFiniteGalois S
    letI : (extensionSubgroup
        (M.maximalUnramifiedSubextension D) M.field N.below).Normal :=
      N.normal
    N.extensionQuotient := by
  exact (D.abstractReciprocityTotallyRamifiedRestrictionEquiv
    K L hTot q).symm q

/-- The restriction equivalence sends the constructed lower generator to the target generator. -/
@[simp]
theorem abstractReciprocityTotallyRamifiedRestrictionEquiv_lowerGenerator
    (D : DegreeData G)
    [IsTopologicalGroup G] [CompactSpace G] [T2Space G]
    (K : FiniteResidueAbstractField D)
    (L : FiniteGaloisSubextension K.field)
    (hTot : L.IsTotallyRamified D)
    (q : L.extensionQuotient) :
    D.abstractReciprocityTotallyRamifiedRestrictionEquiv K L hTot q
      (D.abstractReciprocityTotallyRamifiedLowerGenerator
        K L hTot q) = q := by
  exact MulEquiv.apply_symm_apply _ q

/-- The constructed lower automorphism generates the relevant cyclic quotient. -/
theorem abstractReciprocityTotallyRamifiedLowerGenerator_generates
    (D : DegreeData G)
    [IsTopologicalGroup G] [CompactSpace G] [T2Space G]
    (K : FiniteResidueAbstractField D)
    (L : FiniteGaloisSubextension K.field)
    (hTot : L.IsTotallyRamified D)
    (q : L.extensionQuotient)
    (hq : ∀ x, x ∈ Subgroup.zpowers q) :
    ∀ x, x ∈ Subgroup.zpowers
      (D.abstractReciprocityTotallyRamifiedLowerGenerator
        K L hTot q) := by
  let e := D.abstractReciprocityTotallyRamifiedRestrictionEquiv
    K L hTot q
  let g := D.abstractReciprocityTotallyRamifiedLowerGenerator
    K L hTot q
  intro x
  obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp (hq (e x))
  apply Subgroup.mem_zpowers_iff.mpr
  refine ⟨n, ?_⟩
  apply e.injective
  rw [map_zpow,
    D.abstractReciprocityTotallyRamifiedRestrictionEquiv_lowerGenerator, hn]

end DegreeData

end ClassFormation
end
end

section
-- module Solutions.OAIQ244_DUKE.AbstractClassFieldTheory_Reciprocity_TotallyRamifiedCase_FrobeniusNorms
attribute [-instance] _root_.ClassFormation.instIsAddTorsionFreeZHat _root_.ClassFormation.instIsMulTorsionFreeMultiplicativeZHat _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.DiscreteNthRootsSubgroup.instTopologicalSpaceSubtypeUnitsMemSubgroup _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalClassFieldTheory.baseFixingExtensionQuotient_finite _root_.LocalClassFieldTheory.extensionSubgroupBase_normal _root_.LocalClassFieldTheory.finiteGaloisExtensionSubgroupOfEmbedding_normal _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.LubinTate.compatibleGroupFamiliesGroup _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.RamificationTheory.HilbertRamification.ValuationSubring.inertiaGroup_normal _root_.RamificationTheory.HilbertRamification.ValuationSubring.ramificationGroupInInertiaAut_normal _root_.RayClass.approximationCompletionTopologicalSpace _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.maximalIdealPowSuccQuotModule _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.LocalClassFieldTheory.normalizationIntegerRingIsIntegralClosure _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen
attribute [-simp] _root_.ClassFormation.FiniteAbelianSubextension.extensionQuotientMk_apply _root_.ClassFormation.FiniteGaloisSubextension.classFieldCandidate_field _root_.ClassFormation.FiniteGaloisSubextension.intermediateFiniteAbelianOfCommutatorLe_field _root_.ClassFormation.mem_normFilterBasis_iff _root_.ClassFormation.toZModPow_zHatToPadicInt _root_.ClassFormation.zHatReductionRingHom_apply _root_.ClassFormation.zHatRingEquivProfiniteIntegerPrimeProduct_apply _root_.ClassFormation.zHatToPadicInt_intCast _root_.ClassFormation.zHatToProfiniteIntegerPrimeProduct_apply _root_.ClassFormation.zHatToProfiniteIntegerPrimeProduct_intCast _root_.ClassFormation.zHatUnitsContinuousMulEquivPrimeProduct_coe_apply _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.IsDiscreteValuationRing.addVal_ringEquiv _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.KummerTheory.torsionQuotientEquivOfZHatMulDecomposition_mk _root_.KummerTheory.zHatUnitsContinuousMulEquivPrimeProduct_rationalCyclotomicCharacter _root_.LocalClassFieldTheory.baseFixingExtensionQuotientEquivAmbient_mk _root_.LocalClassFieldTheory.baseUnitsEquivGaloisAmbientFixed_val _root_.LocalClassFieldTheory.embeddedFieldUnitsEquivGaloisFixed_coe _root_.LocalClassFieldTheory.finiteGaloisUnitsEquivAbstractFixedOfEmbedding_coe _root_.LocalClassFieldTheory.finiteGaloisUnitsEquivAbstractFixed_coe _root_.LocalClassFieldTheory.finiteResidueFrobeniusFromZHat_apply _root_.LocalClassFieldTheory.finiteResidueFrobeniusFromZHat_one _root_.LocalClassFieldTheory.intermediateFieldUnitsEquivGaloisFixed_coe _root_.LocalClassFieldTheory.residueAbsoluteDegreeIn_frobenius _root_.LocalClassFieldTheory.residueAbsoluteFrobenius_one _root_.LocalClassFieldTheory.residueFrobeniusToLimit_apply_component _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.LocalFieldTheory.residueField_algebraMap_residue _root_.OAI.PrimeDegreePackets.ThetaConstruction.schwartzCM_apply _root_.infinitePlace_mult_smul
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

/-!
# Frobenius actions and relative norms in a totally ramified tower

This file constructs the Frobenius element in the auxiliary extension and
proves its restriction, commutation, action, and relative-norm identities.
-/

noncomputable section

namespace ClassFormation

open KummerTheory
open CyclicCohomology

-- Mathlib's `Rep ℤ G` currently fixes the acting group to universe zero.
variable {G : IntegralRepGroupType} [Group G] [TopologicalSpace G]

namespace DegreeData

/-- The restriction `\tilde\sigma|_M`, an element of the actual upper
quotient `G(M/K)`. -/
noncomputable def abstractReciprocityTotallyRamifiedFrobeniusInM
    (D : DegreeData G)
    [IsTopologicalGroup G] [CompactSpace G] [T2Space G]
    (K : FiniteResidueAbstractField D)
    (L : FiniteGaloisSubextension K.field)
    (hTot : L.IsTotallyRamified D)
    (q : L.extensionQuotient) :
    (D.abstractReciprocityTotallyRamifiedFiniteGaloisExtension
      K L hTot q).extensionQuotient := by
  let σ := D.chosenDegreeOneFrobeniusLiftOfFiniteTotallyRamified
    K L hTot q
  let M := D.abstractReciprocityTotallyRamifiedFiniteGaloisExtension
    K L hTot q
  letI : (extensionSubgroup K.field M.field M.below).Normal := M.normal
  have hIM : D.extensionInertiaWithin K.field L.field L.below ≤
      extensionSubgroup K.field M.field M.below := by
    intro x hx
    apply (mem_extensionSubgroup_iff K.field M.field M.below x).2
    apply D.maximalUnramifiedField_le_abstractReciprocityTotallyRamifiedFiniteGaloisExtension
      K L hTot q
    exact ⟨(mem_extensionSubgroup_iff K.field L.field L.below x).1 hx.1,
      (D.mem_fieldInertiaWithin_iff K.field x).1 hx.2⟩
  let r : (K.field.toSubgroup ⧸
      D.extensionInertiaWithin K.field L.field L.below) →*
      (K.field.toSubgroup ⧸
        extensionSubgroup K.field M.field M.below) :=
    QuotientGroup.map
      (D.extensionInertiaWithin K.field L.field L.below)
      (extensionSubgroup K.field M.field M.below)
      (MonoidHom.id K.field.toSubgroup) hIM
  exact M.extensionQuotientMulEquiv.symm (r σ.1)

/-- The Frobenius chosen in the auxiliary field has the expected restriction. -/
@[simp]
theorem abstractReciprocityTotallyRamifiedFrobeniusInM_restriction
    (D : DegreeData G)
    [IsTopologicalGroup G] [CompactSpace G] [T2Space G]
    (K : FiniteResidueAbstractField D)
    (L : FiniteGaloisSubextension K.field)
    (hTot : L.IsTotallyRamified D)
    (q : L.extensionQuotient) :
    let M := D.abstractReciprocityTotallyRamifiedFiniteGaloisExtension
      K L hTot q
    let hML := D.abstractReciprocityTotallyRamifiedFiniteGaloisExtension_le_L
      K L hTot q
    M.bundledRestrictionHom L hML
      (D.abstractReciprocityTotallyRamifiedFrobeniusInM
        K L hTot q) = q := by
  let σ := D.chosenDegreeOneFrobeniusLiftOfFiniteTotallyRamified
    K L hTot q
  let M := D.abstractReciprocityTotallyRamifiedFiniteGaloisExtension
    K L hTot q
  let hML := D.abstractReciprocityTotallyRamifiedFiniteGaloisExtension_le_L
    K L hTot q
  let : (extensionSubgroup K.field M.field M.below).Normal := M.normal
  have hIM : D.extensionInertiaWithin K.field L.field L.below ≤
      extensionSubgroup K.field M.field M.below := by
    intro x hx
    apply (mem_extensionSubgroup_iff K.field M.field M.below x).2
    apply D.maximalUnramifiedField_le_abstractReciprocityTotallyRamifiedFiniteGaloisExtension
      K L hTot q
    exact ⟨(mem_extensionSubgroup_iff K.field L.field L.below x).1 hx.1,
      (D.mem_fieldInertiaWithin_iff K.field x).1 hx.2⟩
  let r : (K.field.toSubgroup ⧸
      D.extensionInertiaWithin K.field L.field L.below) →*
      (K.field.toSubgroup ⧸
        extensionSubgroup K.field M.field M.below) :=
    QuotientGroup.map
      (D.extensionInertiaWithin K.field L.field L.below)
      (extensionSubgroup K.field M.field M.below)
      (MonoidHom.id K.field.toSubgroup) hIM
  change L.extensionQuotientMulEquiv.symm
      (abstractReciprocityRestriction K.field L.field M.field hML L.below
        (r σ.1)) = q
  refine L.extensionQuotientMulEquiv.symm_apply_eq.mpr ?_
  have hcompat : ∀ z : K.field.toSubgroup ⧸
      D.extensionInertiaWithin K.field L.field L.below,
      abstractReciprocityRestriction K.field L.field M.field hML L.below (r z) =
        D.extensionRestriction K.field L.field L.below z := by
    intro z
    refine Quotient.inductionOn' z ?_
    intro x
    rfl
  exact (hcompat σ.1).trans
    (D.frobeniusRestriction_chosenDegreeOneFrobeniusLiftOfFiniteTotallyRamified_underlying
      K L hTot q)

/-- Including the lower generator and then restricting recovers its prescribed action. -/
@[simp]
theorem abstractReciprocityTotallyRamifiedLowerGenerator_inclusion_restriction
    (D : DegreeData G)
    [IsTopologicalGroup G] [CompactSpace G] [T2Space G]
    (K : FiniteResidueAbstractField D)
    (L : FiniteGaloisSubextension K.field)
    (hTot : L.IsTotallyRamified D)
    (q : L.extensionQuotient) :
    let M := D.abstractReciprocityTotallyRamifiedFiniteGaloisExtension
      K L hTot q
    let S := M.inertiaImage D
    let hML := D.abstractReciprocityTotallyRamifiedFiniteGaloisExtension_le_L
      K L hTot q
    M.bundledRestrictionHom L hML
      (M.lowerInclusionHom S
        (D.abstractReciprocityTotallyRamifiedLowerGenerator
          K L hTot q)) = q := by
  let M := D.abstractReciprocityTotallyRamifiedFiniteGaloisExtension
    K L hTot q
  let S := M.inertiaImage D
  let hML := D.abstractReciprocityTotallyRamifiedFiniteGaloisExtension_le_L
    K L hTot q
  let e := D.abstractReciprocityTotallyRamifiedRestrictionEquiv
    K L hTot q
  let g := D.abstractReciprocityTotallyRamifiedLowerGenerator
    K L hTot q
  change M.bundledRestrictionHom L hML
      (M.lowerInclusionHom S g) = q
  have hcompat : ∀ x,
      M.bundledRestrictionHom L hML
        (M.lowerInclusionHom S x) = e x := by
    intro x
    refine Quotient.inductionOn' x ?_
    intro m
    rw [M.lowerInclusionHom_mk S m]
    dsimp [e, abstractReciprocityTotallyRamifiedRestrictionEquiv]
    rfl
  exact (hcompat g).trans
    (D.abstractReciprocityTotallyRamifiedRestrictionEquiv_lowerGenerator K L hTot q)

/-- The lower cyclic generator commutes with the selected Frobenius element. -/
theorem abstractReciprocityTotallyRamified_generator_commutes_frobenius
    (D : DegreeData G)
    [IsTopologicalGroup G] [CompactSpace G] [T2Space G]
    (K : FiniteResidueAbstractField D)
    (L : FiniteGaloisSubextension K.field)
    (hTot : L.IsTotallyRamified D)
    (q : L.extensionQuotient) :
    let M := D.abstractReciprocityTotallyRamifiedFiniteGaloisExtension
      K L hTot q
    let S := M.inertiaImage D
    Commute
      (M.lowerInclusionHom S
        (D.abstractReciprocityTotallyRamifiedLowerGenerator
          K L hTot q))
      (D.abstractReciprocityTotallyRamifiedFrobeniusInM
        K L hTot q) := by
  let M := D.abstractReciprocityTotallyRamifiedFiniteGaloisExtension
    K L hTot q
  let S := M.inertiaImage D
  let hML := D.abstractReciprocityTotallyRamifiedFiniteGaloisExtension_le_L
    K L hTot q
  let g := D.abstractReciprocityTotallyRamifiedLowerGenerator
    K L hTot q
  let t := D.abstractReciprocityTotallyRamifiedFrobeniusInM
    K L hTot q
  let EL : DegreeData.AbstractExtension G := {
    field := L.field
    base := K.field
    below := L.below }
  let : (extensionSubgroup EL.base EL.field EL.below).Normal := by
    change (extensionSubgroup K.field L.field L.below).Normal
    exact L.normal
  have hresBundled :
      M.bundledRestrictionHom L hML (M.lowerInclusionHom S g) =
        M.bundledRestrictionHom L hML t := by
    rw [D.abstractReciprocityTotallyRamifiedLowerGenerator_inclusion_restriction,
      D.abstractReciprocityTotallyRamifiedFrobeniusInM_restriction]
  have hresRaw :
      abstractReciprocityRestriction K.field L.field M.field hML L.below
          (M.extensionQuotientMulEquiv (M.lowerInclusionHom S g)) =
        abstractReciprocityRestriction K.field L.field M.field hML L.below
          (M.extensionQuotientMulEquiv t) := by
    apply L.extensionQuotientMulEquiv.symm.injective
    simpa [FiniteGaloisSubextension.bundledRestrictionHom] using hresBundled
  have hcommRaw := M.commute_of_same_restriction_of_inertia_le
    D EL hML
    (D.maximalUnramifiedField_le_abstractReciprocityTotallyRamifiedFiniteGaloisExtension
      K L hTot q)
    (M.extensionQuotientMulEquiv (M.lowerInclusionHom S g))
    (M.extensionQuotientMulEquiv t) hresRaw
  rw [Commute]
  apply M.extensionQuotientMulEquiv.injective
  simpa only [map_mul] using hcommRaw.eq

/-- Frobenius fixes the automorphism used in the totally ramified construction. -/
theorem abstractReciprocityTotallyRamified_frobenius_fixes_sigma
    (D : DegreeData G) (A : Rep ℤ G)
    [IsTopologicalGroup G] [CompactSpace G] [T2Space G]
    (K : FiniteResidueAbstractField D)
    (L : FiniteGaloisSubextension K.field)
    (hTot : L.IsTotallyRamified D)
    (q : L.extensionQuotient)
    (a : ambientFixedAddSubgroup A
      (D.frobeniusFixedField K L.field L.below
        (D.chosenDegreeOneFrobeniusLiftOfFiniteTotallyRamified
          K L hTot q))) :
    let σ := D.chosenDegreeOneFrobeniusLiftOfFiniteTotallyRamified
      K L hTot q
    let Sigma := D.frobeniusFixedField K L.field L.below σ
    let M := D.abstractReciprocityTotallyRamifiedFiniteGaloisExtension
      K L hTot q
    let hMSigma :=
      D.abstractReciprocityTotallyRamifiedFiniteGaloisExtension_le_sigma
        K L hTot q
    relativeCosetAction A K.field M.field M.below
        (fixedFieldInclusion A Sigma M.field hMSigma a)
        (M.extensionQuotientMulEquiv
          (D.abstractReciprocityTotallyRamifiedFrobeniusInM
            K L hTot q)) =
      (fixedFieldInclusion A Sigma M.field hMSigma a).1 := by
  let σ := D.chosenDegreeOneFrobeniusLiftOfFiniteTotallyRamified
    K L hTot q
  let Sigma := D.frobeniusFixedField K L.field L.below σ
  let M := D.abstractReciprocityTotallyRamifiedFiniteGaloisExtension
    K L hTot q
  let hMSigma :=
    D.abstractReciprocityTotallyRamifiedFiniteGaloisExtension_le_sigma
      K L hTot q
  let : (extensionSubgroup K.field M.field M.below).Normal := M.normal
  have hIM : D.extensionInertiaWithin K.field L.field L.below ≤
      extensionSubgroup K.field M.field M.below := by
    intro x hx
    apply (mem_extensionSubgroup_iff K.field M.field M.below x).2
    apply D.maximalUnramifiedField_le_abstractReciprocityTotallyRamifiedFiniteGaloisExtension
      K L hTot q
    exact ⟨(mem_extensionSubgroup_iff K.field L.field L.below x).1 hx.1,
      (D.mem_fieldInertiaWithin_iff K.field x).1 hx.2⟩
  let r : (K.field.toSubgroup ⧸
      D.extensionInertiaWithin K.field L.field L.below) →*
      (K.field.toSubgroup ⧸
        extensionSubgroup K.field M.field M.below) :=
    QuotientGroup.map
      (D.extensionInertiaWithin K.field L.field L.below)
      (extensionSubgroup K.field M.field M.below)
      (MonoidHom.id K.field.toSubgroup) hIM
  change relativeCosetAction A K.field M.field M.below
      (fixedFieldInclusion A Sigma M.field hMSigma a) (r σ.1) = _
  let x : K.field.toSubgroup := Quotient.out σ.1
  have hx : (QuotientGroup.mk x :
      K.field.toSubgroup ⧸
        D.extensionInertiaWithin K.field L.field L.below) = σ.1 :=
    Quotient.out_eq' σ.1
  rw [← hx]
  change A.ρ x.1 a.1 = a.1
  have hxClosure : (QuotientGroup.mk x :
      K.field.toSubgroup ⧸
        D.extensionInertiaWithin K.field L.field L.below) ∈
      (D.frobeniusClosure K L.field L.below σ).toSubgroup := by
    rw [hx]
    exact (D.frobeniusInClosure K L.field L.below σ).2
  let xSigma : Sigma.toSubgroup :=
    ⟨x.1, ⟨x, hxClosure, rfl⟩⟩
  exact a.2 xSigma

/-- The two constructed automorphisms induce the same action on the extension field. -/
theorem abstractReciprocityTotallyRamified_actions_agree_on_L
    (D : DegreeData G) (A : Rep ℤ G)
    [IsTopologicalGroup G] [CompactSpace G] [T2Space G]
    (K : FiniteResidueAbstractField D)
    (L : FiniteGaloisSubextension K.field)
    (hTot : L.IsTotallyRamified D)
    (q : L.extensionQuotient)
    (a : ambientFixedAddSubgroup A L.field) :
    let M := D.abstractReciprocityTotallyRamifiedFiniteGaloisExtension
      K L hTot q
    let S := M.inertiaImage D
    let hML := D.abstractReciprocityTotallyRamifiedFiniteGaloisExtension_le_L
      K L hTot q
    relativeCosetAction A K.field M.field M.below
        (fixedFieldInclusion A L.field M.field hML a)
        (M.extensionQuotientMulEquiv
          (M.lowerInclusionHom S
            (D.abstractReciprocityTotallyRamifiedLowerGenerator
              K L hTot q))) =
      relativeCosetAction A K.field M.field M.below
        (fixedFieldInclusion A L.field M.field hML a)
        (M.extensionQuotientMulEquiv
          (D.abstractReciprocityTotallyRamifiedFrobeniusInM
            K L hTot q)) := by
  let M := D.abstractReciprocityTotallyRamifiedFiniteGaloisExtension
    K L hTot q
  let S := M.inertiaImage D
  let hML := D.abstractReciprocityTotallyRamifiedFiniteGaloisExtension_le_L
    K L hTot q
  let EL : DegreeData.AbstractExtension G := {
    field := L.field
    base := K.field
    below := L.below }
  let : (extensionSubgroup EL.base EL.field EL.below).Normal := by
    change (extensionSubgroup K.field L.field L.below).Normal
    exact L.normal
  apply M.relativeCosetAction_eq_of_restriction_eq A EL hML
  apply L.extensionQuotientMulEquiv.symm.injective
  simpa [FiniteGaloisSubextension.bundledRestrictionHom] using
    (show M.bundledRestrictionHom L hML
        (M.lowerInclusionHom S
          (D.abstractReciprocityTotallyRamifiedLowerGenerator
            K L hTot q)) =
      M.bundledRestrictionHom L hML
        (D.abstractReciprocityTotallyRamifiedFrobeniusInM
          K L hTot q) by
      rw [D.abstractReciprocityTotallyRamifiedLowerGenerator_inclusion_restriction,
        D.abstractReciprocityTotallyRamifiedFrobeniusInM_restriction])

/-- The first norm restriction used:
`N_{M/M⁰}|_{A_L}=N_{L/K}`, with both sides included in `A_{M⁰}`. -/
theorem abstractReciprocity_totallyRamified_relativeNorm_L
    (D : DegreeData G) (A : Rep ℤ G)
    [IsTopologicalGroup G] [CompactSpace G] [T2Space G]
    (K : FiniteResidueAbstractField D)
    (L : FiniteGaloisSubextension K.field)
    (hTot : L.IsTotallyRamified D)
    (q : L.extensionQuotient)
    (a : ambientFixedAddSubgroup A L.field) :
    let M := D.abstractReciprocityTotallyRamifiedFiniteGaloisExtension
      K L hTot q
    let M₀ := M.maximalUnramifiedSubextension D
    let hML := D.abstractReciprocityTotallyRamifiedFiniteGaloisExtension_le_L
      K L hTot q
    let hMM₀ : M.field.toSubgroup ≤ M₀.toSubgroup :=
      M.field_le_intermediateField (M.inertiaImage D)
    let hM₀K : M₀.toSubgroup ≤ K.field.toSubgroup :=
      M.intermediateField_le_base (M.inertiaImage D)
    letI : Finite
        (K.field.toSubgroup ⧸ extensionSubgroup K.field L.field L.below) :=
      L.finite
    letI : Finite
        (M₀.toSubgroup ⧸ extensionSubgroup M₀ M.field hMM₀) :=
      M.extension_over_intermediate_finite (M.inertiaImage D)
    relativeNorm A M₀ M.field hMM₀
        (fixedFieldInclusion A L.field M.field hML a) =
      fixedFieldInclusion A K.field M₀ hM₀K
        (relativeNorm A K.field L.field L.below a) := by
  let M := D.abstractReciprocityTotallyRamifiedFiniteGaloisExtension
    K L hTot q
  let hML := D.abstractReciprocityTotallyRamifiedFiniteGaloisExtension_le_L
    K L hTot q
  let : Finite
      (K.field.toSubgroup ⧸ extensionSubgroup K.field L.field L.below) :=
    L.finite
  have hInertia : ∀ i : K.field.toSubgroup,
      i ∈ D.fieldInertiaWithin K.field →
      i.1 ∈ L.field.toSubgroup → i.1 ∈ M.field.toSubgroup := by
    intro i hiI hiL
    apply D.maximalUnramifiedField_le_abstractReciprocityTotallyRamifiedFiniteGaloisExtension
      K L hTot q
    exact ⟨hiL, (D.mem_fieldInertiaWithin_iff K.field i).1 hiI⟩
  exact M.abstractReciprocity_relativeNorm_fixedFieldInclusion
    A D L.toFiniteAbstractExtension hML hTot hInertia a

/-- The second norm restriction used:
`N_{M/M⁰}|_{A_Σ}=N_{Σ/K}`, again in the actual fixed group
`A_{M⁰}`. -/
theorem abstractReciprocity_totallyRamified_relativeNorm_sigma
    (D : DegreeData G) (A : Rep ℤ G)
    [IsTopologicalGroup G] [CompactSpace G] [T2Space G]
    [TotallyDisconnectedSpace G]
    (K : FiniteResidueAbstractField D)
    (L : FiniteGaloisSubextension K.field)
    (hTot : L.IsTotallyRamified D)
    (q : L.extensionQuotient)
    (a : ambientFixedAddSubgroup A
      (D.frobeniusFixedField K L.field L.below
        (D.chosenDegreeOneFrobeniusLiftOfFiniteTotallyRamified
          K L hTot q))) :
    letI : Finite
        (K.field.toSubgroup ⧸ extensionSubgroup K.field L.field L.below) :=
      L.finite
    let σ := D.chosenDegreeOneFrobeniusLiftOfFiniteTotallyRamified
      K L hTot q
    let Sigma := D.frobeniusFixedField K L.field L.below σ
    let hSigmaK := D.frobeniusFixedField_le K L.field L.below σ
    letI : Finite
        (K.field.toSubgroup ⧸ extensionSubgroup K.field Sigma hSigmaK) :=
      D.frobeniusFixedField_finite K L.field L.below σ
    let M := D.abstractReciprocityTotallyRamifiedFiniteGaloisExtension
      K L hTot q
    let M₀ := M.maximalUnramifiedSubextension D
    let hMSigma :=
      D.abstractReciprocityTotallyRamifiedFiniteGaloisExtension_le_sigma
        K L hTot q
    let hMM₀ : M.field.toSubgroup ≤ M₀.toSubgroup :=
      M.field_le_intermediateField (M.inertiaImage D)
    let hM₀K : M₀.toSubgroup ≤ K.field.toSubgroup :=
      M.intermediateField_le_base (M.inertiaImage D)
    letI : Finite
        (M₀.toSubgroup ⧸ extensionSubgroup M₀ M.field hMM₀) :=
      M.extension_over_intermediate_finite (M.inertiaImage D)
    relativeNorm A M₀ M.field hMM₀
        (fixedFieldInclusion A Sigma M.field hMSigma a) =
      fixedFieldInclusion A K.field M₀ hM₀K
        (relativeNorm A K.field Sigma hSigmaK a) := by
  let : Finite
      (K.field.toSubgroup ⧸ extensionSubgroup K.field L.field L.below) :=
    L.finite
  let σ := D.chosenDegreeOneFrobeniusLiftOfFiniteTotallyRamified
    K L hTot q
  let Sigma := D.frobeniusFixedField K L.field L.below σ
  let hSigmaK := D.frobeniusFixedField_le K L.field L.below σ
  let hSigmaFinite : Finite
      (K.field.toSubgroup ⧸ extensionSubgroup K.field Sigma hSigmaK) :=
    D.frobeniusFixedField_finite K L.field L.below σ
  let ESigma : DegreeData.FiniteAbstractExtension G :=
    DegreeData.FiniteAbstractExtension.ofInclusion Sigma K.field hSigmaK
  let M := D.abstractReciprocityTotallyRamifiedFiniteGaloisExtension
    K L hTot q
  let hMSigma :=
    D.abstractReciprocityTotallyRamifiedFiniteGaloisExtension_le_sigma
      K L hTot q
  have hSigmaTot : ESigma.IsTotallyRamified D := by
    have hrelative : (ESigma.residueDegree D : ℕ) = 1 := by
      calc
        (ESigma.residueDegree D : ℕ) =
            D.frobeniusExponent K L.field L.below σ :=
          D.frobeniusFixedField_residueDegreeOverBase K L.field L.below σ
        _ = 1 :=
          D.frobeniusExponent_chosenDegreeOneFrobeniusLiftOfFiniteTotallyRamified
            K L hTot q
    exact ESigma.isTotallyRamified_of_residueDegree_eq_one D hrelative
  have hInertia : ∀ i : K.field.toSubgroup,
      i ∈ D.fieldInertiaWithin K.field →
      i.1 ∈ Sigma.toSubgroup → i.1 ∈ M.field.toSubgroup := by
    intro i hiI hiSigma
    apply D.maximalUnramifiedField_le_abstractReciprocityTotallyRamifiedFiniteGaloisExtension
      K L hTot q
    have hiSigmaInertia :
        i.1 ∈ (D.fieldInertia Sigma).toSubgroup :=
      ⟨hiSigma, (D.mem_fieldInertiaWithin_iff K.field i).1 hiI⟩
    rw [D.frobeniusFixedField_fieldInertia
      K L.field L.below σ] at hiSigmaInertia
    exact hiSigmaInertia
  exact M.abstractReciprocity_relativeNorm_fixedFieldInclusion
    A D ESigma hMSigma hSigmaTot hInertia a

end DegreeData

end ClassFormation
end
end

section
-- module Solutions.OAIQ244_DUKE.AbstractClassFieldTheory_Reciprocity_TotallyRamifiedCase_FixedSource
attribute [-instance] _root_.ClassFormation.instIsAddTorsionFreeZHat _root_.ClassFormation.instIsMulTorsionFreeMultiplicativeZHat _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.KummerTheory.finite_finsupp_nsmulQuotient _root_.LocalClassFieldTheory.baseFixingExtensionQuotient_finite _root_.LocalClassFieldTheory.extensionSubgroupBase_normal _root_.LocalClassFieldTheory.finiteGaloisExtensionSubgroupOfEmbedding_normal _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitQuotientCarrier_finite _root_.LocalFieldTheory.DiscreteValuationField.finite_padicInt_finPi_nsmulQuotient _root_.LocalFieldTheory.DiscreteValuationField.finite_padicInt_pi_nsmulQuotient_of_coprime _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_multiplicative_nthPowerQuotient _root_.LocalFieldTheory.finite_nsmulAddQuotient_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.LubinTate.compatibleGroupFamiliesGroup _root_.OAI.PrimeDegreePackets.boundedRealFields_finite _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.RamificationTheory.HilbertRamification.ValuationSubring.inertiaGroup_normal _root_.RamificationTheory.HilbertRamification.ValuationSubring.ramificationGroupInInertiaAut_normal _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.maximalIdealPowSuccQuotModule _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.LocalClassFieldTheory.normalizationIntegerRingIsIntegralClosure _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen
attribute [-simp] _root_.ClassFormation.FiniteAbelianSubextension.extensionQuotientMk_apply _root_.ClassFormation.FiniteGaloisSubextension.classFieldCandidate_field _root_.ClassFormation.FiniteGaloisSubextension.intermediateFiniteAbelianOfCommutatorLe_field _root_.ClassFormation.mem_normFilterBasis_iff _root_.ClassFormation.toZModPow_zHatToPadicInt _root_.ClassFormation.zHatReductionRingHom_apply _root_.ClassFormation.zHatRingEquivProfiniteIntegerPrimeProduct_apply _root_.ClassFormation.zHatToPadicInt_intCast _root_.ClassFormation.zHatToProfiniteIntegerPrimeProduct_apply _root_.ClassFormation.zHatToProfiniteIntegerPrimeProduct_intCast _root_.ClassFormation.zHatUnitsContinuousMulEquivPrimeProduct_coe_apply _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.IsDiscreteValuationRing.addVal_ringEquiv _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.KummerTheory.torsionQuotientEquivOfZHatMulDecomposition_mk _root_.KummerTheory.zHatUnitsContinuousMulEquivPrimeProduct_rationalCyclotomicCharacter _root_.LocalClassFieldTheory.baseFixingExtensionQuotientEquivAmbient_mk _root_.LocalClassFieldTheory.baseUnitsEquivGaloisAmbientFixed_val _root_.LocalClassFieldTheory.embeddedFieldUnitsEquivGaloisFixed_coe _root_.LocalClassFieldTheory.finiteGaloisUnitsEquivAbstractFixedOfEmbedding_coe _root_.LocalClassFieldTheory.finiteGaloisUnitsEquivAbstractFixed_coe _root_.LocalClassFieldTheory.finiteResidueFrobeniusFromZHat_apply _root_.LocalClassFieldTheory.finiteResidueFrobeniusFromZHat_one _root_.LocalClassFieldTheory.intermediateFieldUnitsEquivGaloisFixed_coe _root_.LocalClassFieldTheory.intrinsicFiniteAbstractBase_eq_base _root_.LocalClassFieldTheory.residueAbsoluteDegreeIn_frobenius _root_.LocalClassFieldTheory.residueAbsoluteFrobenius_one _root_.LocalClassFieldTheory.residueFrobeniusToLimit_apply_component _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.LocalFieldTheory.residueField_algebraMap_residue _root_.OAI.PrimeDegreePackets.ThetaConstruction.schwartzCM_apply _root_.infinitePlace_mult_smul
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

/-!
# The fixed source in the totally ramified reciprocity argument

This file converts a finite cyclic extension to the canonical finite Galois
boundary and carries out the source-producing fixed-element calculation.
-/

noncomputable section

namespace ClassFormation

open KummerTheory
open CyclicCohomology

-- Mathlib's `Rep ℤ G` currently fixes the acting group to universe zero.
variable {G : IntegralRepGroupType} [Group G] [TopologicalSpace G]

/-- If two commuting group elements act compatibly on a coboundary, the
standard corrected combination is fixed by the first element. -/
theorem abstractReciprocity_fixedCombination_of_commute
    {Q : IntegralRepGroupType} [Group Q] (B : Rep ℤ Q)
    (g t : Q) (hcomm : Commute g t) (c b a : B.V)
    (htc : B.ρ t c = c)
    (hgb : B.ρ g b = B.ρ t b)
    (hbc : b - c = B.ρ g a - a) :
    B.ρ g (b + a - B.ρ t a) = b + a - B.ρ t a := by
  have hcommAction : B.ρ g (B.ρ t a) = B.ρ t (B.ρ g a) := by
    calc
      B.ρ g (B.ρ t a) = B.ρ (g * t) a := by
        rw [map_mul]
        rfl
      _ = B.ρ (t * g) a := by rw [hcomm.eq]
      _ = B.ρ t (B.ρ g a) := by
        rw [map_mul]
        rfl
  have hb : b = c + B.ρ g a - a := by
    calc
      b = (b - c) + c := by abel
      _ = (B.ρ g a - a) + c := by rw [hbc]
      _ = c + B.ρ g a - a := by abel
  have htbc := congrArg (fun z : B.V ↦ B.ρ t z) hbc
  have htbc' : B.ρ t b - c = B.ρ t (B.ρ g a) - B.ρ t a := by
    simpa only [map_sub, htc] using htbc
  have htb : B.ρ t b = c + B.ρ t (B.ρ g a) - B.ρ t a := by
    calc
      B.ρ t b = (B.ρ t b - c) + c := by abel
      _ = (B.ρ t (B.ρ g a) - B.ρ t a) + c := by rw [htbc']
      _ = c + B.ρ t (B.ρ g a) - B.ρ t a := by abel
  calc
    B.ρ g (b + a - B.ρ t a) =
        B.ρ g b + B.ρ g a - B.ρ g (B.ρ t a) := by
      simp only [map_add, map_sub]
    _ = B.ρ t b + B.ρ g a - B.ρ t (B.ρ g a) := by
      rw [hgb, hcommAction]
    _ = c + B.ρ g a - B.ρ t a := by rw [htb]; abel
    _ = b + a - B.ρ t a := by rw [hb]; abel

namespace FiniteGaloisSubextension
/-- The lower inclusion homomorphism preserves the relative coset action. -/
theorem relativeCosetAction_lowerInclusionHom
    (A : Rep ℤ G) [IsTopologicalGroup G] {K : ClosedSubgroup G}
    (M : FiniteGaloisSubextension K) (S : Subgroup M.extensionQuotient)
    (a : ambientFixedAddSubgroup A M.field)
    (g : (M.intermediateField S).toSubgroup ⧸
      extensionSubgroup (M.intermediateField S) M.field
        (M.field_le_intermediateField S)) :
    relativeCosetAction A (M.intermediateField S) M.field
        (M.field_le_intermediateField S) a g =
      relativeCosetAction A K M.field M.below a
        (M.lowerInclusionHom S g) := by
  refine Quotient.inductionOn' g ?_
  intro m
  rfl
end FiniteGaloisSubextension

namespace FiniteCyclicSubextension
variable {K : FiniteAbstractField G}
/-- Forget only the chosen cyclic generator.  The resulting finite Galois
bundle is the canonical input to the finite reciprocity construction. -/
def toFiniteGaloisSubextension (E : FiniteCyclicSubextension K) :
    FiniteGaloisSubextension K.field where
  field := E.field
  below := E.below
  normal := E.normal
  finite := E.finite
/-- The cyclic generator transported across the finite Galois quotient
boundary. -/
def galoisGenerator (E : FiniteCyclicSubextension K) :
    E.toFiniteGaloisSubextension.extensionQuotient :=
  E.toFiniteGaloisSubextension.extensionQuotientMulEquiv.symm E.generator
/-- The transported generator still generates the whole finite Galois
quotient. -/
theorem galoisGenerator_generates (E : FiniteCyclicSubextension K) :
    ∀ x, x ∈ Subgroup.zpowers E.galoisGenerator := by
  intro x
  let e := E.toFiniteGaloisSubextension.extensionQuotientMulEquiv
  obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp (E.generates (e x))
  apply Subgroup.mem_zpowers_iff.mpr
  refine ⟨n, ?_⟩
  apply e.injective
  change e (e.symm E.generator ^ n) = e x
  exact (map_zpow e _ n).trans
    ((congrArg (fun y => y ^ n) (e.apply_symm_apply E.generator)).trans hn)

end FiniteCyclicSubextension

namespace ValuationData

variable {D : DegreeData G} {A : Rep ℤ G}

-- The two fixed-field presentations have the same canonical addition.
-- Fix its homogeneous type before elaborating the bundled second operand.
local infixl:65 (priority := high) " + " =>
  (fun {α : Type _} [Add α] (a b : α) => HAdd.hAdd a b)

/-- The complete source-producing calculation in the cyclic totally
ramified case of the abstract reciprocity theorem. All fields, restriction
maps, norm identities, and action identities are constructed from the
original data; none is exposed as a hypothesis. -/
theorem abstractReciprocity_cyclicTotallyRamified_fixedSource
    (v : ValuationData D A) (hcf : SatisfiesClassFieldAxiom A)
    [IsTopologicalGroup G] [CompactSpace G] [T2Space G]
    [TotallyDisconnectedSpace G]
    (K : FiniteAbstractField G)
    (E : FiniteCyclicSubextension K)
    (hTot : E.IsTotallyRamified D)
    (k : ℕ)
    (piSigma : ambientFixedAddSubgroup A
      (D.frobeniusFixedField (K.toFiniteResidueAbstractField D)
        E.field E.below
        (D.chosenDegreeOneFrobeniusLiftOfFiniteTotallyRamified
          (K.toFiniteResidueAbstractField D)
          E.toFiniteGaloisSubextension
          hTot
          E.galoisGenerator)))
    (piL : ambientFixedAddSubgroup A E.field) :
    let L := E.toFiniteAbstractFieldExtension.field
    let KR := K.toFiniteResidueAbstractField D
    letI : Finite
        ((baseField G).toSubgroup ⧸
          extensionSubgroup (baseField G) KR.field
            (le_baseField KR.field)) := by
      change Finite
        ((baseField G).toSubgroup ⧸
          extensionSubgroup (baseField G) K.field
            (le_baseField K.field))
      exact K.finite
    let LG := E.toFiniteGaloisSubextension
    letI : Finite
        (KR.field.toSubgroup ⧸
          extensionSubgroup KR.field LG.field LG.below) :=
      LG.finite
    let q := E.galoisGenerator
    let hLGTot := hTot
    let σ := D.chosenDegreeOneFrobeniusLiftOfFiniteTotallyRamified
      KR LG hLGTot q
    let Sigma := D.frobeniusFixedField KR LG.field LG.below σ
    let hSigmaK := D.frobeniusFixedField_le KR LG.field LG.below σ
    letI : Finite
        (K.field.toSubgroup ⧸ extensionSubgroup K.field Sigma hSigmaK) :=
      D.frobeniusFixedField_finite KR LG.field LG.below σ
    ∀ (w : v.unitAddSubgroup L)
      (_hpiL : v.IsPrimeElement L piL)
      (_hnorm :
        relativeNorm A K.field E.field E.below (k • piL + w.1) =
          relativeNorm A K.field Sigma hSigmaK (k • piSigma)),
    let M := D.abstractReciprocityTotallyRamifiedFiniteGaloisExtension
      KR LG hLGTot q
    letI : Finite
        (KR.field.toSubgroup ⧸
          extensionSubgroup KR.field M.field M.below) :=
      M.finite
    letI : Finite ((baseField G).toSubgroup ⧸
        extensionSubgroup (baseField G) M.field
          (le_baseField M.field)) :=
      FiniteGaloisSubextension.finite_extension_trans M.below (le_baseField K.field)
    let MF : FiniteAbstractField G := ⟨M.field, inferInstance⟩
    let S := M.inertiaImage D
    let M₀ := M.maximalUnramifiedSubextension D
    let hMM₀ : M.field.toSubgroup ≤ M₀.toSubgroup :=
      M.field_le_intermediateField S
    ∃ x : ambientFixedAddSubgroup A M₀,
      ((v.valuationAt MF
        (fixedFieldInclusion A M₀ M.field hMM₀ x) :
          v.valueGroup) : ZHat) =
        Int.castRingHom ZHat (k : ℤ) := by
  dsimp only
  let L := E.toFiniteAbstractFieldExtension.field
  let KR := K.toFiniteResidueAbstractField D
  let LG := E.toFiniteGaloisSubextension
  let hLGfinite : Finite
      (KR.field.toSubgroup ⧸
        extensionSubgroup KR.field LG.field LG.below) :=
    LG.finite
  let hLGfiniteOverK : Finite
      (K.field.toSubgroup ⧸
        extensionSubgroup K.field LG.field LG.below) := by
    have h := hLGfinite
    change Finite
      (K.field.toSubgroup ⧸
        extensionSubgroup K.field LG.field LG.below) at h
    exact h
  let q := E.galoisGenerator
  let hq := E.galoisGenerator_generates
  let hLGTot := hTot
  let hKRabsolute : Finite ((baseField G).toSubgroup ⧸
      extensionSubgroup (baseField G) KR.field (le_baseField KR.field)) := by
    change Finite
      ((baseField G).toSubgroup ⧸
        extensionSubgroup (baseField G) K.field
          (le_baseField K.field))
    exact K.finite
  let σ := D.chosenDegreeOneFrobeniusLiftOfFiniteTotallyRamified
    KR LG hLGTot q
  let Sigma := D.frobeniusFixedField KR LG.field LG.below σ
  let hSigmaK := D.frobeniusFixedField_le KR LG.field LG.below σ
  let hSigmaFinite : Finite
      (K.field.toSubgroup ⧸ extensionSubgroup K.field Sigma hSigmaK) :=
    D.frobeniusFixedField_finite KR LG.field LG.below σ
  intro w hpiL hnorm
  let M := D.abstractReciprocityTotallyRamifiedFiniteGaloisExtension
    KR LG hLGTot q
  let hMfinite : Finite
      (KR.field.toSubgroup ⧸
        extensionSubgroup KR.field M.field M.below) :=
    M.finite
  let hMabsolute : Finite ((baseField G).toSubgroup ⧸
      extensionSubgroup (baseField G) M.field (le_baseField M.field)) :=
    FiniteGaloisSubextension.finite_extension_trans M.below (le_baseField K.field)
  let MF : FiniteAbstractField G := ⟨M.field, hMabsolute⟩
  let S := M.inertiaImage D
  let M₀ := M.maximalUnramifiedSubextension D
  let hML := D.abstractReciprocityTotallyRamifiedFiniteGaloisExtension_le_L
    KR LG hLGTot q
  let hMSigma :=
    D.abstractReciprocityTotallyRamifiedFiniteGaloisExtension_le_sigma
      KR LG hLGTot q
  let hMM₀ : M.field.toSubgroup ≤ M₀.toSubgroup :=
    M.field_le_intermediateField S
  let hM₀K : M₀.toSubgroup ≤ K.field.toSubgroup :=
    M.intermediateField_le_base S
  let N := M.lowerFiniteGalois S
  let hMnormal : (extensionSubgroup K.field M.field M.below).Normal := M.normal
  let hNnormal : (extensionSubgroup M₀ M.field hMM₀).Normal := N.normal
  let hNfinite : Finite
      (M₀.toSubgroup ⧸ extensionSubgroup M₀ M.field hMM₀) :=
    N.finite
  let hMLfinite : Finite
      (E.field.toSubgroup ⧸ extensionSubgroup E.field M.field hML) :=
    FiniteGaloisSubextension.finite_extension_over_intermediate
      M.below E.below hML
  let hM₀finite : Finite
      (K.field.toSubgroup ⧸ extensionSubgroup K.field M₀ hM₀K) :=
    M.intermediateField_finite S
  let hM₀absolute : Finite ((baseField G).toSubgroup ⧸
      extensionSubgroup (baseField G) M₀ (le_baseField M₀)) :=
    FiniteGaloisSubextension.finite_extension_trans hM₀K (le_baseField K.field)
  let M₀F : FiniteAbstractField G := ⟨M₀, hM₀absolute⟩
  let EN : FiniteAbstractFieldExtension G :=
    { field := MF
      base := M₀F
      below := hMM₀
      finiteQuotient := hNfinite }
  let EM : FiniteAbstractFieldExtension G :=
    { field := MF
      base := K
      below := M.below
      finiteQuotient := M.finite }
  let EML : FiniteAbstractFieldExtension G :=
    { field := MF
      base := L
      below := hML
      finiteQuotient := hMLfinite }
  have hUnramifiedML :
      EML.IsUnramified D := by
    change EML.toFiniteAbstractExtension.IsUnramified D
    rw [EML.toFiniteAbstractExtension.isUnramified_iff_inertia_le D]
    intro x hx
    apply D.maximalUnramifiedField_le_abstractReciprocityTotallyRamifiedFiniteGaloisExtension
      KR LG hLGTot q
    exact hx
  let piSigmaM : ambientFixedAddSubgroup A M.field :=
    fixedFieldInclusion A Sigma M.field hMSigma piSigma
  let piLM : ambientFixedAddSubgroup A M.field :=
    fixedFieldInclusion A E.field M.field hML piL
  let wUnitM : v.unitAddSubgroup MF :=
    v.unitInclusion EML hUnramifiedML w
  let wM : ambientFixedAddSubgroup A M.field := wUnitM.1
  have hpiLM : v.IsPrimeElement MF piLM := by
    exact v.prime_of_unramified EML hUnramifiedML piL hpiL
  let cM : ambientFixedAddSubgroup A M.field := k • piSigmaM
  let bM : ambientFixedAddSubgroup A M.field := k • piLM + wM
  let uM : ambientFixedAddSubgroup A M.field := cM - k • piLM
  have hbM :
      bM = fixedFieldInclusion A E.field M.field hML (k • piL + w.1) := by
    apply Subtype.ext
    rfl
  have hcM :
      cM = fixedFieldInclusion A Sigma M.field hMSigma (k • piSigma) := by
    apply Subtype.ext
    rfl
  have hNormL :
      relativeNorm A M₀ M.field hMM₀
          (fixedFieldInclusion A E.field M.field hML (k • piL + w.1)) =
        fixedFieldInclusion A K.field M₀ hM₀K
          (relativeNorm A K.field E.field E.below (k • piL + w.1)) := by
    have h :=
      D.abstractReciprocity_totallyRamified_relativeNorm_L
        A KR LG hLGTot q (k • piL + w.1)
    change
      relativeNorm A M₀ M.field hMM₀
          (fixedFieldInclusion A E.field M.field hML (k • piL + w.1)) =
        fixedFieldInclusion A K.field M₀ hM₀K
          (relativeNorm A K.field E.field E.below (k • piL + w.1)) at h
    exact h
  have hNormSigma :
      relativeNorm A M₀ M.field hMM₀
          (fixedFieldInclusion A Sigma M.field hMSigma (k • piSigma)) =
        fixedFieldInclusion A K.field M₀ hM₀K
          (relativeNorm A K.field Sigma hSigmaK (k • piSigma)) := by
    have h :=
      D.abstractReciprocity_totallyRamified_relativeNorm_sigma
        A KR LG hLGTot q (k • piSigma)
    change
      relativeNorm A M₀ M.field hMM₀
          (fixedFieldInclusion A Sigma M.field hMSigma (k • piSigma)) =
        fixedFieldInclusion A K.field M₀ hM₀K
          (relativeNorm A K.field Sigma hSigmaK (k • piSigma)) at h
    exact h
  have hNormBC : relativeNorm A M₀ M.field hMM₀ bM =
      relativeNorm A M₀ M.field hMM₀ cM := by
    calc
      relativeNorm A M₀ M.field hMM₀ bM =
          relativeNorm A M₀ M.field hMM₀
            (fixedFieldInclusion A E.field M.field hML
              (k • piL + w.1)) := congrArg _ hbM
      _ =
          fixedFieldInclusion A K.field M₀ hM₀K
            (relativeNorm A K.field E.field E.below (k • piL + w.1)) :=
        hNormL
      _ = fixedFieldInclusion A K.field M₀ hM₀K
          (relativeNorm A K.field Sigma hSigmaK (k • piSigma)) := by
        exact congrArg
          (fixedFieldInclusion A K.field M₀ hM₀K) hnorm
      _ = relativeNorm A M₀ M.field hMM₀
          (fixedFieldInclusion A Sigma M.field hMSigma (k • piSigma)) :=
        hNormSigma.symm
      _ = relativeNorm A M₀ M.field hMM₀ cM :=
        congrArg _ hcM.symm
  have hnormWU : relativeNorm A M₀ M.field hMM₀ wM =
      relativeNorm A M₀ M.field hMM₀ uM := by
    dsimp only [bM, cM, uM] at hNormBC ⊢
    rw [map_add, map_nsmul, map_nsmul] at hNormBC
    rw [map_sub, map_nsmul, map_nsmul]
    exact eq_sub_of_add_eq' hNormBC
  let g := D.abstractReciprocityTotallyRamifiedLowerGenerator
    KR LG hLGTot q
  have hg : ∀ x, x ∈ Subgroup.zpowers g :=
    D.abstractReciprocityTotallyRamifiedLowerGenerator_generates
      KR LG hLGTot q hq
  let hNFintype : Fintype N.extensionQuotient := Fintype.ofFinite _
  let hNCyclic : IsCyclic N.extensionQuotient := by
    rw [isCyclic_iff_exists_zpowers_eq_top]
    refine ⟨g, ?_⟩
    ext x
    constructor
    · intro _
      exact Subgroup.mem_top x
    · intro _
      exact hg x
  let hNcomm : CommGroup N.extensionQuotient := IsCyclic.commGroup
  obtain ⟨aN, haN⟩ :=
    abstractReciprocity_exists_hMinusOne_primitive hcf
      EN N.normal g hg uM wM hnormWU
  let B := extensionFixedRepresentation A K.field M.field M.below M.normal
  let B₀ := extensionFixedRepresentation A M₀ M.field hMM₀ N.normal
  let eB := extensionFixedRepresentationEquiv A K.field M.field M.below M.normal
  let eB₀ := extensionFixedRepresentationEquiv A M₀ M.field hMM₀ N.normal
  let gB := M.extensionQuotientMulEquiv (M.lowerInclusionHom S g)
  let tB := M.extensionQuotientMulEquiv
    (D.abstractReciprocityTotallyRamifiedFrobeniusInM
      KR LG hLGTot q)
  let aB : B.V := eB.symm (eB₀ aN)
  let bB : B.V := eB.symm bM
  let cB : B.V := eB.symm cM
  have haNLocal :
      B₀.ρ g aN - aN = eB₀.symm (wM - uM) := by
    have h := haN
    change B₀.ρ g aN - aN = eB₀.symm (wM - uM) at h
    exact h
  have hActionPrimitive : eB (B.ρ gB aB) = eB₀ (B₀.ρ g aN) := by
    apply Subtype.ext
    calc
      (eB (B.ρ gB aB)).1 =
          relativeCosetAction A K.field M.field M.below (eB aB) gB :=
        extensionFixedRepresentation_action_coe
          A K.field M.field M.below M.normal gB aB
      _ = relativeCosetAction A M₀ M.field hMM₀ (eB₀ aN) g := by
        exact (M.relativeCosetAction_lowerInclusionHom A S (eB₀ aN) g).symm
      _ = (eB₀ (B₀.ρ g aN)).1 := by
        exact (extensionFixedRepresentation_action_coe
          A M₀ M.field hMM₀ N.normal g aN).symm
  have hprimitiveB : B.ρ gB aB - aB = eB.symm (wM - uM) := by
    apply eB.injective
    calc
      eB (B.ρ gB aB - aB) =
          eB₀ (B₀.ρ g aN) - eB₀ aN := by
        rw [map_sub, hActionPrimitive]
        simp [aB]
      _ = eB₀ (B₀.ρ g aN - aN) := by
        rw [map_sub]
      _ = eB₀ (eB₀.symm (wM - uM)) :=
        congrArg eB₀ haNLocal
      _ = wM - uM := eB₀.apply_symm_apply _
      _ = eB (eB.symm (wM - uM)) :=
        (eB.apply_symm_apply _).symm
  have hbc : bB - cB = B.ρ gB aB - aB := by
    rw [hprimitiveB]
    apply eB.injective
    dsimp only [bB, cB]
    simp only [map_sub, AddEquiv.apply_symm_apply]
    dsimp only [bM, cM, uM]
    abel
  have htc : B.ρ tB cB = cB := by
    apply eB.injective
    apply Subtype.ext
    calc
      (eB (B.ρ tB cB)).1 =
          relativeCosetAction A K.field M.field M.below cM tB :=
        extensionFixedRepresentation_action_coe
          A K.field M.field M.below M.normal tB cB
      _ = cM.1 := by
        dsimp only [cM]
        have hActionNsmul :
            relativeCosetAction A K.field M.field M.below
                (k • piSigmaM) tB =
              k • relativeCosetAction A K.field M.field M.below
                piSigmaM tB := by
          refine Quotient.inductionOn' tB ?_
          intro t
          simp only [relativeCosetAction_mk]
          exact map_nsmul (A.ρ t.1) k piSigmaM.1
        rw [hActionNsmul]
        congr 1
        have h :=
          D.abstractReciprocityTotallyRamified_frobenius_fixes_sigma
            A KR LG hLGTot q piSigma
        change
          relativeCosetAction A K.field M.field M.below
              (fixedFieldInclusion A Sigma M.field hMSigma piSigma) tB =
            (fixedFieldInclusion A Sigma M.field hMSigma piSigma).1 at h
        simpa [piSigmaM] using h
      _ = (eB cB).1 := rfl
  have hgb : B.ρ gB bB = B.ρ tB bB := by
    apply eB.injective
    apply Subtype.ext
    calc
      (eB (B.ρ gB bB)).1 =
          relativeCosetAction A K.field M.field M.below bM gB :=
        extensionFixedRepresentation_action_coe
          A K.field M.field M.below M.normal gB bB
      _ = relativeCosetAction A K.field M.field M.below bM tB := by
        have h :=
          D.abstractReciprocityTotallyRamified_actions_agree_on_L
            A KR LG hLGTot q (k • piL + w.1)
        change
          relativeCosetAction A K.field M.field M.below
              (fixedFieldInclusion A E.field M.field hML (k • piL + w.1)) gB =
            relativeCosetAction A K.field M.field M.below
              (fixedFieldInclusion A E.field M.field hML (k • piL + w.1)) tB at h
        rw [hbM]
        exact h
      _ = (eB (B.ρ tB bB)).1 := by
        exact (extensionFixedRepresentation_action_coe
          A K.field M.field M.below M.normal tB bB).symm
  have hcomm : Commute gB tB :=
    (D.abstractReciprocityTotallyRamified_generator_commutes_frobenius
      KR LG hLGTot q).map M.extensionQuotientMulEquiv.toMonoidHom
  let xB : B.V := bB + aB - B.ρ tB aB
  have hxB : B.ρ gB xB = xB :=
    abstractReciprocity_fixedCombination_of_commute
      B gB tB hcomm cB bB aB htc hgb hbc
  let xB₀ : B₀.V := eB₀.symm (eB xB)
  have hActionX : eB₀ (B₀.ρ g xB₀) = eB (B.ρ gB xB) := by
    apply Subtype.ext
    calc
      (eB₀ (B₀.ρ g xB₀)).1 =
          relativeCosetAction A M₀ M.field hMM₀ (eB₀ xB₀) g :=
        extensionFixedRepresentation_action_coe
          A M₀ M.field hMM₀ N.normal g xB₀
      _ = relativeCosetAction A K.field M.field M.below (eB xB) gB :=
        M.relativeCosetAction_lowerInclusionHom A S (eB xB) g
      _ = (eB (B.ρ gB xB)).1 := by
        exact (extensionFixedRepresentation_action_coe
          A K.field M.field M.below M.normal gB xB).symm
  have hxB₀ : B₀.ρ g xB₀ = xB₀ := by
    apply eB₀.injective
    rw [hActionX, hxB]
    rfl
  let T := Rep.FiniteCyclicGroup.normHomCompSub B₀ g
  let xCycle : T.moduleCatLeftHomologyData.K := ⟨xB₀, by
    change B₀.ρ g xB₀ - xB₀ = 0
    exact sub_eq_zero.mpr hxB₀⟩
  let x : ambientFixedAddSubgroup A M₀ :=
    (cyclicFixedCycleEquiv A M₀ M.field hMM₀
      N.normal N.finite g hg).symm xCycle
  refine ⟨x, ?_⟩
  have hxFormula : fixedFieldInclusion A M₀ M.field hMM₀ x = eB xB := by
    apply Subtype.ext
    rfl
  have hActionVal :=
    v.valuationAt_extensionFixedRepresentation_action
      EM M.normal tB aB
  have hval : v.valuationAt MF
      (fixedFieldInclusion A M₀ M.field hMM₀ x) =
      k • v.oneValue := by
    rw [hxFormula]
    have hxBFormula : eB xB = bM + eB aB - eB (B.ρ tB aB) := by
      apply Subtype.ext
      rfl
    rw [hxBFormula]
    dsimp only [bM]
    rw [map_sub, map_add, map_add, map_nsmul, hpiLM,
      wUnitM.2, hActionVal]
    abel
  calc
    ((v.valuationAt MF
        (fixedFieldInclusion A M₀ M.field hMM₀ x) :
          v.valueGroup) : ZHat) =
        ((k • v.oneValue : v.valueGroup) : ZHat) :=
      congrArg Subtype.val hval
    _ = k • (1 : ZHat) := rfl
    _ = Int.castRingHom ZHat (k : ℤ) := by
      simp

end ValuationData

end ClassFormation
end
end

section
-- module Solutions.OAIQ244_DUKE.AbstractClassFieldTheory_Reciprocity_TotallyRamifiedCase_Conclusion
attribute [-instance] _root_.ClassFormation.instIsAddTorsionFreeZHat _root_.ClassFormation.instIsMulTorsionFreeMultiplicativeZHat _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.KummerTheory.finite_finsupp_nsmulQuotient _root_.LocalClassFieldTheory.baseFixingExtensionQuotient_finite _root_.LocalClassFieldTheory.extensionSubgroupBase_normal _root_.LocalClassFieldTheory.finiteGaloisExtensionSubgroupOfEmbedding_normal _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitQuotientCarrier_finite _root_.LocalFieldTheory.DiscreteValuationField.finite_padicInt_finPi_nsmulQuotient _root_.LocalFieldTheory.DiscreteValuationField.finite_padicInt_pi_nsmulQuotient_of_coprime _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_multiplicative_nthPowerQuotient _root_.LocalFieldTheory.finite_nsmulAddQuotient_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.LubinTate.compatibleGroupFamiliesGroup _root_.OAI.PrimeDegreePackets.boundedRealFields_finite _root_.OAI.PrimeDegreePackets.instNonemptyLeafTestSpace _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.RamificationTheory.HilbertRamification.ValuationSubring.inertiaGroup_normal _root_.RamificationTheory.HilbertRamification.ValuationSubring.ramificationGroupInInertiaAut_normal _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.LocalClassFieldTheory.normalizationIntegerRingIsIntegralClosure _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen
attribute [-simp] _root_.ClassFormation.FiniteAbelianSubextension.extensionQuotientMk_apply _root_.ClassFormation.FiniteGaloisSubextension.classFieldCandidate_field _root_.ClassFormation.FiniteGaloisSubextension.intermediateFiniteAbelianOfCommutatorLe_field _root_.ClassFormation.mem_normFilterBasis_iff _root_.ClassFormation.toZModPow_zHatToPadicInt _root_.ClassFormation.zHatReductionRingHom_apply _root_.ClassFormation.zHatRingEquivProfiniteIntegerPrimeProduct_apply _root_.ClassFormation.zHatToPadicInt_intCast _root_.ClassFormation.zHatToProfiniteIntegerPrimeProduct_apply _root_.ClassFormation.zHatToProfiniteIntegerPrimeProduct_intCast _root_.ClassFormation.zHatUnitsContinuousMulEquivPrimeProduct_coe_apply _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.IsDiscreteValuationRing.addVal_ringEquiv _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.KummerTheory.torsionQuotientEquivOfZHatMulDecomposition_mk _root_.KummerTheory.zHatUnitsContinuousMulEquivPrimeProduct_rationalCyclotomicCharacter _root_.LocalClassFieldTheory.baseFixingExtensionQuotientEquivAmbient_mk _root_.LocalClassFieldTheory.baseUnitsEquivGaloisAmbientFixed_val _root_.LocalClassFieldTheory.embeddedFieldUnitsEquivGaloisFixed_coe _root_.LocalClassFieldTheory.finiteGaloisUnitsEquivAbstractFixedOfEmbedding_coe _root_.LocalClassFieldTheory.finiteGaloisUnitsEquivAbstractFixed_coe _root_.LocalClassFieldTheory.finiteResidueFrobeniusFromZHat_apply _root_.LocalClassFieldTheory.finiteResidueFrobeniusFromZHat_one _root_.LocalClassFieldTheory.intermediateFieldUnitsEquivGaloisFixed_coe _root_.LocalClassFieldTheory.intrinsicFiniteAbstractBase_eq_base _root_.LocalClassFieldTheory.residueAbsoluteDegreeIn_frobenius _root_.LocalClassFieldTheory.residueAbsoluteFrobenius_one _root_.LocalClassFieldTheory.residueFrobeniusToLimit_apply_component _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.LocalFieldTheory.residueField_algebraMap_residue _root_.OAI.PrimeDegreePackets.ThetaConstruction.schwartzCM_apply _root_.infinitePlace_mult_smul
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

/-!
# Totally ramified reciprocity

This file derives exponent vanishing, injectivity, and finally bijectivity of
finite reciprocity from the constructed fixed source.
-/

noncomputable section

namespace ClassFormation

open KummerTheory
open CyclicCohomology

-- Mathlib's `Rep ℤ G` currently fixes the acting group to universe zero.
variable {G : IntegralRepGroupType} [Group G] [TopologicalSpace G]

namespace ValuationData

variable {D : DegreeData G} {A : Rep ℤ G}

-- The two fixed-field presentations have the same canonical addition.
-- Fix its homogeneous type before elaborating the bundled second operand.
local infixl:65 (priority := high) " + " =>
  (fun {α : Type _} [Add α] (a b : α) => HAdd.hAdd a b)

/-- The exponent in the chosen cyclic decomposition is zero. -/
theorem abstractReciprocity_cyclicTotallyRamified_exponent_eq_zero
    (v : ValuationData D A) (hcf : SatisfiesClassFieldAxiom A)
    [IsTopologicalGroup G] [CompactSpace G] [T2Space G]
    [TotallyDisconnectedSpace G]
    (K : FiniteAbstractField G)
    (E : FiniteCyclicSubextension K)
    (hTot : E.IsTotallyRamified D)
    (k : ℕ)
    (hk : k < (E.toFiniteAbstractExtension.degree : ℕ))
    (piSigma : ambientFixedAddSubgroup A
      (D.frobeniusFixedField (K.toFiniteResidueAbstractField D)
        E.field E.below
        (D.chosenDegreeOneFrobeniusLiftOfFiniteTotallyRamified
          (K.toFiniteResidueAbstractField D)
          E.toFiniteGaloisSubextension
          hTot
          E.galoisGenerator)))
    (piL : ambientFixedAddSubgroup A E.field) :
    let L := E.toFiniteAbstractFieldExtension.field
    let KR := K.toFiniteResidueAbstractField D
    letI : Finite
        ((baseField G).toSubgroup ⧸
          extensionSubgroup (baseField G) KR.field
            (le_baseField KR.field)) := by
      change Finite
        ((baseField G).toSubgroup ⧸
          extensionSubgroup (baseField G) K.field
            (le_baseField K.field))
      exact K.finite
    let LG := E.toFiniteGaloisSubextension
    letI : Finite
        (KR.field.toSubgroup ⧸
          extensionSubgroup KR.field LG.field LG.below) :=
      LG.finite
    let q := E.galoisGenerator
    let hLGTot := hTot
    let σ := D.chosenDegreeOneFrobeniusLiftOfFiniteTotallyRamified
      KR LG hLGTot q
    let Sigma := D.frobeniusFixedField KR LG.field LG.below σ
    let hSigmaK := D.frobeniusFixedField_le KR LG.field LG.below σ
    letI : Finite
        (K.field.toSubgroup ⧸ extensionSubgroup K.field Sigma hSigmaK) :=
      D.frobeniusFixedField_finite KR LG.field LG.below σ
    ∀ (w : v.unitAddSubgroup L)
      (_hpiL : v.IsPrimeElement L piL)
      (_hnorm :
        relativeNorm A K.field E.field E.below (k • piL + w.1) =
          relativeNorm A K.field Sigma hSigmaK (k • piSigma)),
      k = 0 := by
  dsimp only
  let L := E.toFiniteAbstractFieldExtension.field
  let KR := K.toFiniteResidueAbstractField D
  let LG := E.toFiniteGaloisSubextension
  let hLGfinite : Finite
      (KR.field.toSubgroup ⧸
        extensionSubgroup KR.field LG.field LG.below) :=
    LG.finite
  let hLGfiniteOverK : Finite
      (K.field.toSubgroup ⧸
        extensionSubgroup K.field LG.field LG.below) := by
    have h := hLGfinite
    change Finite
      (K.field.toSubgroup ⧸
        extensionSubgroup K.field LG.field LG.below) at h
    exact h
  let q := E.galoisGenerator
  let hLGTot := hTot
  let hKRabsolute : Finite ((baseField G).toSubgroup ⧸
      extensionSubgroup (baseField G) KR.field (le_baseField KR.field)) := by
    change Finite ((baseField G).toSubgroup ⧸
      extensionSubgroup (baseField G) K.field (le_baseField K.field))
    exact K.finite
  let σ := D.chosenDegreeOneFrobeniusLiftOfFiniteTotallyRamified
    KR LG hLGTot q
  let Sigma := D.frobeniusFixedField KR LG.field LG.below σ
  let hSigmaK := D.frobeniusFixedField_le KR LG.field LG.below σ
  let hSigmaFinite : Finite
      (K.field.toSubgroup ⧸ extensionSubgroup K.field Sigma hSigmaK) :=
    D.frobeniusFixedField_finite KR LG.field LG.below σ
  intro w hpiL hnorm
  let M := D.abstractReciprocityTotallyRamifiedFiniteGaloisExtension
    KR LG hLGTot q
  let hMfinite : Finite
      (KR.field.toSubgroup ⧸
        extensionSubgroup KR.field M.field M.below) :=
    M.finite
  let S := M.inertiaImage D
  let M₀ := M.maximalUnramifiedSubextension D
  let hMM₀ : M.field.toSubgroup ≤ M₀.toSubgroup :=
    M.field_le_intermediateField S
  let hM₀K : M₀.toSubgroup ≤ K.field.toSubgroup :=
    M.intermediateField_le_base S
  let N := M.lowerFiniteGalois S
  let hNnormal : (extensionSubgroup M₀ M.field hMM₀).Normal := N.normal
  let hNfinite : Finite
      (M₀.toSubgroup ⧸ extensionSubgroup M₀ M.field hMM₀) :=
    N.finite
  let hM₀finite : Finite
      (K.field.toSubgroup ⧸ extensionSubgroup K.field M₀ hM₀K) :=
    M.intermediateField_finite S
  let hM₀absolute : Finite ((baseField G).toSubgroup ⧸
      extensionSubgroup (baseField G) M₀ (le_baseField M₀)) :=
    FiniteGaloisSubextension.finite_extension_trans hM₀K (le_baseField K.field)
  let hMabsolute : Finite ((baseField G).toSubgroup ⧸
      extensionSubgroup (baseField G) M.field (le_baseField M.field)) :=
    FiniteGaloisSubextension.finite_extension_trans M.below (le_baseField K.field)
  let MF : FiniteAbstractField G := ⟨M.field, hMabsolute⟩
  let M₀F : FiniteAbstractField G := ⟨M₀, hM₀absolute⟩
  let EN : FiniteAbstractFieldExtension G :=
    { field := MF
      base := M₀F
      below := hMM₀
      finiteQuotient := hNfinite }
  obtain ⟨x, hx⟩ :=
    v.abstractReciprocity_cyclicTotallyRamified_fixedSource hcf
      K E hTot k piSigma piL w hpiL hnorm
  have hkLower : k < (N.toFiniteAbstractExtension.degree : ℕ) := by
    rw [D.abstractReciprocityTotallyRamifiedLowerDegree_eq
      KR LG hLGTot q]
    exact hk
  exact abstractReciprocity_totallyRamified_valuation_forces_exponent_zero
    v EN (by
      simpa [EN, FiniteAbstractFieldExtension.IsTotallyRamified,
        FiniteAbstractFieldExtension.toFiniteAbstractExtension] using
          M.maximalUnramifiedSubextension_isTotallyRamified D)
      k hkLower x hx

/-- In the cyclic totally ramified case, the reciprocity homomorphism of
the finite reciprocity equivalence has trivial kernel.  This is the final kernel calculation. -/
theorem abstractReciprocity_cyclicTotallyRamified_finiteReciprocityHom_injective
    (v : ValuationData D A) (hcf : SatisfiesClassFieldAxiom A)
    [IsTopologicalGroup G] [CompactSpace G] [T2Space G]
    [TotallyDisconnectedSpace G]
    (hAxiom : v.SatisfiesUnramifiedUnitCohomology D)
    (K : FiniteAbstractField G)
    (E : FiniteCyclicSubextension K)
    (hTot : E.IsTotallyRamified D) :
    Function.Injective
      (D.finiteReciprocityHom A v hAxiom K E.field E.below) := by
  let L := E.toFiniteAbstractFieldExtension.field
  let KR := K.toFiniteResidueAbstractField D
  let LG := E.toFiniteGaloisSubextension
  let hLGfinite : Finite
      (KR.field.toSubgroup ⧸
        extensionSubgroup KR.field LG.field LG.below) :=
    LG.finite
  let hLGfiniteOverK : Finite
      (K.field.toSubgroup ⧸
        extensionSubgroup K.field LG.field LG.below) := by
    have h := hLGfinite
    change Finite
      (K.field.toSubgroup ⧸
        extensionSubgroup K.field LG.field LG.below) at h
    exact h
  let q := E.galoisGenerator
  let qRaw := E.generator
  let hLGTot := hTot
  let hKRabsolute : Finite ((baseField G).toSubgroup ⧸
      extensionSubgroup (baseField G) KR.field (le_baseField KR.field)) := by
    change Finite ((baseField G).toSubgroup ⧸
      extensionSubgroup (baseField G) K.field (le_baseField K.field))
    exact K.finite
  let Q := K.field.toSubgroup ⧸
    extensionSubgroup K.field E.field E.below
  let EF := E.toFiniteAbstractExtension
  let hQFintype : Fintype Q := Fintype.ofFinite _
  let σ := D.chosenDegreeOneFrobeniusLiftOfFiniteTotallyRamified
    KR LG hLGTot q
  let Sigma := D.frobeniusFixedField KR LG.field LG.below σ
  let hSigmaK := D.frobeniusFixedField_le KR LG.field LG.below σ
  let hSigmaFinite : Finite
      (K.field.toSubgroup ⧸ extensionSubgroup K.field Sigma hSigmaK) :=
    D.frobeniusFixedField_finite KR LG.field LG.below σ
  let hSigmaAbsolute : Finite ((baseField G).toSubgroup ⧸
      extensionSubgroup (baseField G) Sigma (le_baseField Sigma)) :=
    D.frobeniusFixedField_absoluteFinite K LG.field LG.below σ
  let SigmaF : FiniteAbstractField G := ⟨Sigma, hSigmaAbsolute⟩
  let piSigma : ambientFixedAddSubgroup A Sigma := v.chosenPrimeElement SigmaF
  let piL : ambientFixedAddSubgroup A E.field := v.chosenPrimeElement L
  rw [injective_iff_map_eq_zero]
  intro x hx
  obtain ⟨i, hi, _⟩ :=
    IsCyclic.unique_zpow_zmod (a := qRaw) E.generates x.toMul
  let k : ℕ := i.val
  have hcard : Fintype.card Q = (EF.degree : ℕ) := by
    calc
      Fintype.card Q = Nat.card Q := by
        rw [Nat.card_eq_fintype_card]
      _ = (extensionSubgroup K.field E.field E.below).index :=
        (Subgroup.index_eq_card
          (extensionSubgroup K.field E.field E.below)).symm
      _ = (EF.degree : ℕ) :=
        EF.extensionSubgroup_index_eq_degree
  have hk : k < (EF.degree : ℕ) := by
    rw [← hcard]
    exact i.val_lt
  have hxrepr : x = k • Additive.ofMul qRaw := by
    apply Additive.toMul.injective
    change x.toMul = qRaw ^ k
    exact hi
  rw [hxrepr, map_nsmul,
    D.finiteReciprocityHom_apply_eq_primeNormClass
      A v hAxiom K E.field E.below (Additive.ofMul qRaw) σ
      (by
        change D.frobeniusRestriction KR LG.field LG.below σ = qRaw
        exact
          (D.frobeniusRestriction_chosenDegreeOneFrobeniusLiftOfFiniteTotallyRamified_underlying
            KR LG hLGTot q).trans
            (E.toFiniteGaloisSubextension.extensionQuotientMulEquiv.apply_symm_apply
              E.generator))
      piSigma (v.chosenPrimeElement_isPrime SigmaF)] at hx
  have hclass :
      finiteNormClass A K.field E.field E.below
          (relativeNorm A K.field Sigma hSigmaK (k • piSigma)) = 0 := by
    have hx' := hx
    change k • finiteNormClass A K.field E.field E.below
        (relativeNorm A K.field Sigma hSigmaK piSigma) = 0 at hx'
    rw [map_nsmul, finiteNormClass_nsmul]
    exact hx'
  have hSigmaResidue :
      ((DegreeData.FiniteAbstractExtension.ofInclusion
        Sigma K.field hSigmaK).residueDegree D : ℕ) = 1 := by
    calc
      ((DegreeData.FiniteAbstractExtension.ofInclusion
          Sigma K.field hSigmaK).residueDegree D : ℕ) =
          D.frobeniusExponent KR LG.field LG.below σ :=
        D.frobeniusFixedField_residueDegreeOverBase KR LG.field LG.below σ
      _ = 1 :=
        D.frobeniusExponent_chosenDegreeOneFrobeniusLiftOfFiniteTotallyRamified
          KR LG hLGTot q
  let : Finite
      (K.field.toSubgroup ⧸ extensionSubgroup K.field L.field E.below) := E.finite
  obtain ⟨w, hnorm⟩ :=
    v.primeNormClass_eq_zero_exists_unit_norm_eq
      K L SigmaF E.below hSigmaK hTot hSigmaResidue
      k piSigma piL (v.chosenPrimeElement_isPrime SigmaF)
      (v.chosenPrimeElement_isPrime L) hclass
  have hkzero := v.abstractReciprocity_cyclicTotallyRamified_exponent_eq_zero
    hcf K E hTot k hk piSigma piL
      w (v.chosenPrimeElement_isPrime L) hnorm
  rw [hxrepr, hkzero, zero_nsmul]

/-- The cyclic totally ramified instance of the abstract reciprocity theorem. -/
theorem abstractReciprocity_cyclicTotallyRamified_finiteReciprocityHom_bijective
    (v : ValuationData D A) (hcf : SatisfiesClassFieldAxiom A)
    [IsTopologicalGroup G] [CompactSpace G] [T2Space G]
    [TotallyDisconnectedSpace G]
    (hAxiom : v.SatisfiesUnramifiedUnitCohomology D)
    (K : FiniteAbstractField G)
    (E : FiniteCyclicSubextension K)
    (hTot : E.IsTotallyRamified D) :
    Function.Bijective
      (D.finiteReciprocityHom A v hAxiom K E.field E.below) := by
  let EF := E.toFiniteAbstractExtension
  let hEbaseAbsolute : Finite ((baseField G).toSubgroup ⧸
      extensionSubgroup (baseField G) EF.base (le_baseField EF.base)) := by
    simpa [EF, FiniteCyclicSubextension.toFiniteAbstractExtension] using K.finite
  let : Finite (FiniteNormQuotient A K.field E.field E.below) :=
    finiteNormQuotient_finite_of_classFieldAxiom
      A hcf EF E.normal E.generator E.generates
  apply (Nat.bijective_iff_injective_and_card
    (D.finiteReciprocityHom A v hAxiom K E.field E.below)).2
  exact ⟨v.abstractReciprocity_cyclicTotallyRamified_finiteReciprocityHom_injective
      hcf hAxiom K E hTot,
    cyclicReciprocity_card_equality
      A hcf EF E.normal E.generator E.generates⟩

end ValuationData

end ClassFormation
end
end

section
-- module Solutions.OAIQ244_DUKE.AbstractClassFieldTheory_Reciprocity_Main
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.KummerTheory.finite_finsupp_nsmulQuotient _root_.LocalClassFieldTheory.baseFixingExtensionQuotient_finite _root_.LocalClassFieldTheory.extensionSubgroupBase_normal _root_.LocalClassFieldTheory.finiteGaloisExtensionSubgroupOfEmbedding_normal _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitQuotientCarrier_finite _root_.LocalFieldTheory.DiscreteValuationField.finite_padicInt_finPi_nsmulQuotient _root_.LocalFieldTheory.DiscreteValuationField.finite_padicInt_pi_nsmulQuotient_of_coprime _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_multiplicative_nthPowerQuotient _root_.LocalFieldTheory.finite_nsmulAddQuotient_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.LubinTate.compatibleGroupFamiliesGroup _root_.OAI.PrimeDegreePackets.boundedRealFields_finite _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.RamificationTheory.HilbertRamification.ValuationSubring.inertiaGroup_normal _root_.RamificationTheory.HilbertRamification.ValuationSubring.ramificationGroupInInertiaAut_normal _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.CyclicCohomology.binaryCoefficientFamilyCommGroup _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.LocalClassFieldTheory.normalizationIntegerRingIsIntegralClosure _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen
attribute [-simp] _root_.ClassFormation.FiniteAbelianSubextension.extensionQuotientMk_apply _root_.ClassFormation.FiniteGaloisSubextension.classFieldCandidate_field _root_.ClassFormation.FiniteGaloisSubextension.intermediateFiniteAbelianOfCommutatorLe_field _root_.ClassFormation.mem_normFilterBasis_iff _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.IsDiscreteValuationRing.addVal_ringEquiv _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.LocalClassFieldTheory.baseFixingExtensionQuotientEquivAmbient_mk _root_.LocalClassFieldTheory.intrinsicFiniteAbstractBase_eq_base _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.LocalFieldTheory.residueField_algebraMap_residue _root_.OAI.PrimeDegreePackets.ThetaConstruction.schwartzCM_apply _root_.infinitePlace_mult_smul
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

namespace ClassFormation

open KummerTheory

open CyclicCohomology

/-!
# The abstract reciprocity theorem

This file assembles the three reductions.  The terminal
cyclic totally ramified calculation is proved in
`AbstractClassFieldTheory.Reciprocity.TotallyRamifiedCase`.
-/

noncomputable section

-- Mathlib's `Rep ℤ G` currently fixes the acting group to universe zero.
variable {G : IntegralRepGroupType} [Group G] [TopologicalSpace G]

/-- Additive exactness of the finite Galois row attached to an intermediate
Galois field. -/
theorem abstractReciprocity_galois_functionExact
    (K M L : ClosedSubgroup G)
    (hLM : L.toSubgroup ≤ M.toSubgroup)
    (hMK : M.toSubgroup ≤ K.toSubgroup)
    [hLnormal :
      (extensionSubgroup K L (hLM.trans hMK)).Normal]
    [hMnormal : (extensionSubgroup K M hMK).Normal] :
    letI : (extensionSubgroup M L hLM).Normal :=
      transferNormNaturality_intermediateExtension_normal K M L hLM hMK
    Function.Exact
      (MonoidHom.toAdditive (abstractReciprocityInclusion K M L hLM hMK))
      (MonoidHom.toAdditive (abstractReciprocityRestriction K M L hLM hMK)) := by
  let : (extensionSubgroup M L hLM).Normal :=
    transferNormNaturality_intermediateExtension_normal K M L hLM hMK
  intro q
  constructor
  · intro hq
    have hmul : abstractReciprocityRestriction K M L hLM hMK q.toMul = 1 := by
      exact Additive.ofMul.injective (by simpa using hq)
    have hmem : q.toMul ∈
        (abstractReciprocityRestriction K M L hLM hMK).ker := hmul
    rw [abstractReciprocity_galois_exact K M L hLM hMK] at hmem
    obtain ⟨x, hx⟩ := hmem
    refine ⟨Additive.ofMul x, ?_⟩
    exact Additive.toMul.injective hx
  · rintro ⟨x, rfl⟩
    have hmem : abstractReciprocityInclusion K M L hLM hMK x.toMul ∈
        (abstractReciprocityInclusion K M L hLM hMK).range :=
      ⟨x.toMul, rfl⟩
    rw [← abstractReciprocity_galois_exact K M L hLM hMK] at hmem
    exact Additive.ofMul.injective (by simpa using hmem)

namespace ValuationData

variable {D : DegreeData G} {A : Rep ℤ G}

/-- The common reciprocity square used by the cyclic and intermediate-field
reductions in the abstract reciprocity theorem. -/
theorem abstractReciprocity_finiteReciprocityHom_diagram
    (v : ValuationData D A)
    [IsTopologicalGroup G] [CompactSpace G] [T2Space G]
    [TotallyDisconnectedSpace G]
    (hAxiom : v.SatisfiesUnramifiedUnitCohomology D)
    (K M : FiniteAbstractField G) (L : ClosedSubgroup G)
    (hLM : L.toSubgroup ≤ M.field.toSubgroup)
    (hMK : M.field.toSubgroup ≤ K.field.toSubgroup)
    [hLnormal : (extensionSubgroup K.field L (hLM.trans hMK)).Normal]
    [hLfinite : Finite
      (K.field.toSubgroup ⧸ extensionSubgroup K.field L (hLM.trans hMK))]
    [hMnormal : (extensionSubgroup K.field M.field hMK).Normal]
    [hMfinite : Finite
      (K.field.toSubgroup ⧸ extensionSubgroup K.field M.field hMK)]
    [hLMnormal : (extensionSubgroup M.field L hLM).Normal]
    [hLMfinite : Finite
      (M.field.toSubgroup ⧸ extensionSubgroup M.field L hLM)] :
    let r₀ := D.finiteReciprocityHom A v hAxiom M L hLM
    let r := D.finiteReciprocityHom A v hAxiom K L (hLM.trans hMK)
    let r₁ := D.finiteReciprocityHom A v hAxiom K M.field hMK
    let i := MonoidHom.toAdditive
      (abstractReciprocityInclusion K.field M.field L hLM hMK)
    let q := MonoidHom.toAdditive
      (abstractReciprocityRestriction K.field M.field L hLM hMK)
    let n := abstractReciprocityNormMap A K.field M.field L hLM hMK
    let p := abstractReciprocityNormProjection A K.field M.field L hLM hMK
    Function.Surjective q ∧
      (∀ x, r (i x) = n (r₀ x)) ∧
      (∀ x, p (r x) = r₁ (q x)) := by
  dsimp only
  let EMK : FiniteAbstractFieldExtension G :=
    { field := M
      base := K
      below := hMK
      finiteQuotient := hMfinite }
  let EKK : FiniteAbstractFieldExtension G :=
    { field := K
      base := K
      below := le_rfl
      finiteQuotient := (FiniteGaloisSubextension.refl K.field).finite }
  let r₀ := D.finiteReciprocityHom A v hAxiom M L hLM
  let r := D.finiteReciprocityHom A v hAxiom K L (hLM.trans hMK)
  let r₁ := D.finiteReciprocityHom A v hAxiom K M.field hMK
  let i := MonoidHom.toAdditive
    (abstractReciprocityInclusion K.field M.field L hLM hMK)
  let q := MonoidHom.toAdditive
    (abstractReciprocityRestriction K.field M.field L hLM hMK)
  let n := abstractReciprocityNormMap A K.field M.field L hLM hMK
  let p := abstractReciprocityNormProjection A K.field M.field L hLM hMK
  have hq : Function.Surjective q := by
    intro y
    obtain ⟨x, hx⟩ := abstractReciprocityRestriction_surjective
      K.field M.field L hLM hMK y.toMul
    refine ⟨Additive.ofMul x, ?_⟩
    exact Additive.toMul.injective hx
  have hleft : ∀ x, r (i x) = n (r₀ x) := by
    intro x
    have hcomm := D.finiteReciprocityNaturality_restriction_norm_commutes
      A v hAxiom EMK L L (hLM.trans hMK) hLM le_rfl
    simpa only [r, r₀, n, i, abstractReciprocityNormMap,
      abstractReciprocityInclusion, transferNormNaturalityIntermediateInclusion,
      AddMonoidHom.comp_apply] using
        (congrArg (fun f => f x) hcomm).symm
  have hright : ∀ x, p (r x) = r₁ (q x) := by
    intro x
    have hcomm := D.finiteReciprocityNaturality_restriction_norm_commutes
      A v hAxiom EKK M.field L hMK (hLM.trans hMK) hLM
    rw [finiteReciprocityNaturalityNormMap_sameBase_eq_normProjection,
      finiteReciprocityNaturalityRestriction_sameBase_eq_restriction] at hcomm
    simpa only [r, r₁, p, q, AddMonoidHom.comp_apply] using
      congrArg (fun f => f x) hcomm
  exact ⟨hq, hleft, hright⟩

/-- The third reduction: the reciprocity homomorphism is
bijective for every cyclic finite Galois extension, by splitting it into
its maximal unramified and totally ramified parts. -/
theorem abstractReciprocity_cyclic_finiteReciprocityHom_bijective
    (v : ValuationData D A) (hcf : SatisfiesClassFieldAxiom A)
    [IsTopologicalGroup G] [CompactSpace G] [T2Space G]
    [TotallyDisconnectedSpace G]
    (hAxiom : v.SatisfiesUnramifiedUnitCohomology D)
    (K : FiniteAbstractField G) (L : FiniteGaloisSubextension K.field)
    [hCyclic : IsCyclic L.extensionQuotient] :
    letI : Finite
        (K.field.toSubgroup ⧸
          extensionSubgroup K.field L.field L.below) := L.finite
    Function.Bijective
      (D.finiteReciprocityHom A v hAxiom K L.field L.below) := by
  let : Finite
      (K.field.toSubgroup ⧸
        extensionSubgroup K.field L.field L.below) := L.finite
  let S := L.inertiaImage D
  let M := L.maximalUnramifiedSubextension D
  let hLM : L.field.toSubgroup ≤ M.toSubgroup :=
    L.field_le_intermediateField S
  let hMK : M.toSubgroup ≤ K.field.toSubgroup :=
    L.intermediateField_le_base S
  let hLnormal :
      (extensionSubgroup K.field L.field (hLM.trans hMK)).Normal := by
    simpa only using L.normal
  let hLfinite : Finite
      (K.field.toSubgroup ⧸
        extensionSubgroup K.field L.field (hLM.trans hMK)) := by
    simpa only using L.finite
  let hMnormal : (extensionSubgroup K.field M hMK).Normal :=
    L.intermediateField_normal S inferInstance
  let hMfinite : Finite
      (K.field.toSubgroup ⧸ extensionSubgroup K.field M hMK) :=
    L.intermediateField_finite S
  let hLMnormal : (extensionSubgroup M L.field hLM).Normal :=
    L.extensionSubgroup_over_intermediate_normal S
  let hLMfinite : Finite
      (M.toSubgroup ⧸ extensionSubgroup M L.field hLM) :=
    L.extension_over_intermediate_finite S
  let hMabsolute : Finite ((baseField G).toSubgroup ⧸
      extensionSubgroup (baseField G) M (le_baseField M)) :=
    FiniteGaloisSubextension.finite_extension_trans hMK (le_baseField K.field)
  let MF : FiniteAbstractField G := ⟨M, hMabsolute⟩
  let hLowerCyclic : IsCyclic
      (M.toSubgroup ⧸ extensionSubgroup M L.field hLM) :=
    L.lowerQuotient_isCyclic S
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator
    (α := M.toSubgroup ⧸ extensionSubgroup M L.field hLM)
  let Ecyc : FiniteCyclicSubextension MF :=
    { field := L.field
      below := hLM
      normal := hLMnormal
      finite := hLMfinite
      generator := g
      generates := hg }
  let r₀ := D.finiteReciprocityHom A v hAxiom MF L.field hLM
  let r := D.finiteReciprocityHom A v hAxiom K L.field (hLM.trans hMK)
  let r₁ := D.finiteReciprocityHom A v hAxiom K M hMK
  have hr₀ : Function.Bijective r₀ :=
    v.abstractReciprocity_cyclicTotallyRamified_finiteReciprocityHom_bijective
      hcf hAxiom MF Ecyc
        (L.maximalUnramifiedSubextension_isTotallyRamified D)
  have hr₁ : Function.Bijective r₁ :=
    (v.unramifiedReciprocityEquiv hAxiom K M hMK
      (L.maximalUnramifiedSubextension_isUnramified D)).bijective
  obtain ⟨hpQ, hleft, hright⟩ :=
    abstractReciprocity_finiteReciprocityHom_diagram
      v hAxiom K MF L.field hLM hMK
  exact abstractReciprocity_bijective_of_exact_diagram
    (MonoidHom.toAdditive
      (abstractReciprocityInclusion K.field M L.field hLM hMK))
    (MonoidHom.toAdditive
      (abstractReciprocityRestriction K.field M L.field hLM hMK))
    (abstractReciprocityNormMap A K.field M L.field hLM hMK)
    (abstractReciprocityNormProjection A K.field M L.field hLM hMK)
    r₀ r r₁
    (abstractReciprocity_galois_functionExact K.field M L.field hLM hMK)
    (abstractReciprocity_normQuotient_exact A K.field M L.field hLM hMK)
    hpQ (L.maximalUnramified_normMap_injective A hcf D)
    hleft hright hr₀ hr₁

/-- Surjectivity ascends through a normal intermediate field.  This is the
diagram chase used in the degree induction of the first reduction. -/
theorem abstractReciprocity_finiteReciprocityHom_surjective_of_intermediate
    (v : ValuationData D A)
    [IsTopologicalGroup G] [CompactSpace G] [T2Space G]
    [TotallyDisconnectedSpace G]
    (hAxiom : v.SatisfiesUnramifiedUnitCohomology D)
    (K : FiniteAbstractField G) (L : FiniteGaloisSubextension K.field)
    (S : Subgroup L.extensionQuotient) [hSnormal : S.Normal] :
    let M := L.intermediateField S
    let hLM := L.field_le_intermediateField S
    let hMK := L.intermediateField_le_base S
    letI : (extensionSubgroup K.field M hMK).Normal :=
      L.intermediateField_normal S hSnormal
    letI : Finite
        (K.field.toSubgroup ⧸ extensionSubgroup K.field M hMK) :=
      L.intermediateField_finite S
    letI : (extensionSubgroup M L.field hLM).Normal :=
      L.extensionSubgroup_over_intermediate_normal S
    letI : Finite
        (M.toSubgroup ⧸ extensionSubgroup M L.field hLM) :=
      L.extension_over_intermediate_finite S
    letI : Finite ((baseField G).toSubgroup ⧸
        extensionSubgroup (baseField G) M (le_baseField M)) :=
      FiniteGaloisSubextension.finite_extension_trans hMK (le_baseField K.field)
    let MF : FiniteAbstractField G := ⟨M, inferInstance⟩
    Function.Surjective
        (D.finiteReciprocityHom A v hAxiom MF L.field hLM) →
      Function.Surjective
        (D.finiteReciprocityHom A v hAxiom K M hMK) →
      letI : Finite
          (K.field.toSubgroup ⧸
            extensionSubgroup K.field L.field L.below) := L.finite
      Function.Surjective
        (D.finiteReciprocityHom A v hAxiom K L.field L.below) := by
  dsimp only
  let : Finite
      (K.field.toSubgroup ⧸
        extensionSubgroup K.field L.field L.below) := L.finite
  let M := L.intermediateField S
  let hLM := L.field_le_intermediateField S
  let hMK := L.intermediateField_le_base S
  let hLnormal :
      (extensionSubgroup K.field L.field (hLM.trans hMK)).Normal := by
    simpa only using L.normal
  let hLfinite : Finite
      (K.field.toSubgroup ⧸
        extensionSubgroup K.field L.field (hLM.trans hMK)) := by
    simpa only using L.finite
  let hMnormal : (extensionSubgroup K.field M hMK).Normal :=
    L.intermediateField_normal S hSnormal
  let hMfinite : Finite
      (K.field.toSubgroup ⧸ extensionSubgroup K.field M hMK) :=
    L.intermediateField_finite S
  let hLMnormal : (extensionSubgroup M L.field hLM).Normal :=
    L.extensionSubgroup_over_intermediate_normal S
  let hLMfinite : Finite
      (M.toSubgroup ⧸ extensionSubgroup M L.field hLM) :=
    L.extension_over_intermediate_finite S
  let hMabsolute : Finite ((baseField G).toSubgroup ⧸
      extensionSubgroup (baseField G) M (le_baseField M)) :=
    FiniteGaloisSubextension.finite_extension_trans hMK (le_baseField K.field)
  let MF : FiniteAbstractField G := ⟨M, hMabsolute⟩
  intro hr₀ hr₁
  let r₀ := D.finiteReciprocityHom A v hAxiom MF L.field hLM
  let r := D.finiteReciprocityHom A v hAxiom K L.field (hLM.trans hMK)
  let r₁ := D.finiteReciprocityHom A v hAxiom K M hMK
  obtain ⟨hpQ, hleft, hright⟩ :=
    abstractReciprocity_finiteReciprocityHom_diagram
      v hAxiom K MF L.field hLM hMK
  exact abstractReciprocity_surjective_of_exact_diagram
    (MonoidHom.toAdditive
      (abstractReciprocityInclusion K.field M L.field hLM hMK))
    (MonoidHom.toAdditive
      (abstractReciprocityRestriction K.field M L.field hLM hMK))
    (abstractReciprocityNormMap A K.field M L.field hLM hMK)
    (abstractReciprocityNormProjection A K.field M L.field hLM hMK)
    r₀ r r₁
    (abstractReciprocity_normQuotient_exact A K.field M L.field hLM hMK)
    hpQ hleft hright hr₀ hr₁

section SolvableReciprocity

local notation "IsSolvable" => Group.IsSolvable

/-- The degree induction in the first reduction for solvable
Galois groups.  In the abelian noncyclic case one cuts out one of the
faithful cyclic coordinates; in the nonabelian case one cuts out the
commutator subgroup. -/
theorem abstractReciprocity_solvable_finiteReciprocityHom_surjective
    (v : ValuationData D A) (hcf : SatisfiesClassFieldAxiom A)
    [IsTopologicalGroup G] [CompactSpace G] [T2Space G]
    [TotallyDisconnectedSpace G]
    (hAxiom : v.SatisfiesUnramifiedUnitCohomology D)
    (K : FiniteAbstractField G) (L : FiniteGaloisSubextension K.field)
    [hsolvable : IsSolvable L.extensionQuotient] :
    letI : Finite
        (K.field.toSubgroup ⧸
          extensionSubgroup K.field L.field L.below) := L.finite
    Function.Surjective
      (D.finiteReciprocityHom A v hAxiom K L.field L.below) := by
  classical
  let : Finite
      (K.field.toSubgroup ⧸
        extensionSubgroup K.field L.field L.below) := L.finite
  let Q := L.extensionQuotient
  by_cases hcyclic : IsCyclic Q
  · let : IsCyclic Q := hcyclic
    exact (v.abstractReciprocity_cyclic_finiteReciprocityHom_bijective
      hcf hAxiom K L).2
  have hQnotSubsingleton : ¬ Subsingleton Q := by
    intro hQ
    let : Subsingleton Q := hQ
    exact hcyclic inferInstance
  let hQnontrivial : Nontrivial Q :=
    not_subsingleton_iff_nontrivial.mp hQnotSubsingleton
  by_cases hcommutative : IsMulCommutative Q
  · let : IsMulCommutative Q := hcommutative
    obtain ⟨I, hIfinite, _, _, f, _, hfaithful, hfactorCyclic,
        _⟩ := L.exists_cyclicIntermediateFields
    let : Fintype I := hIfinite
    obtain ⟨q, hq⟩ := exists_ne (1 : Q)
    have hnotAll : ¬ ∀ i, f i q = 1 := by
      intro hall
      have hmem : q ∈ ⨅ i, MonoidHom.ker (f i) := by
        rw [Subgroup.mem_iInf]
        intro i
        exact (MonoidHom.mem_ker).2 (hall i)
      rw [hfaithful, Subgroup.mem_bot] at hmem
      exact hq hmem
    push Not at hnotAll
    obtain ⟨i, hi⟩ := hnotAll
    let S := MonoidHom.ker (f i)
    let hSnormal : S.Normal := inferInstance
    have hSneTop : S ≠ ⊤ := by
      intro htop
      have hmem : q ∈ S := by rw [htop]; trivial
      exact hi ((MonoidHom.mem_ker).1 hmem)
    let M := L.intermediateField S
    let N := L.lowerFiniteGalois S
    let U := L.intermediateFiniteGalois S hSnormal
    let hMabsolute : Finite ((baseField G).toSubgroup ⧸
        extensionSubgroup (baseField G) M (le_baseField M)) :=
      FiniteGaloisSubextension.finite_extension_trans
        (L.intermediateField_le_base S) (le_baseField K.field)
    let MF : FiniteAbstractField G := ⟨M, hMabsolute⟩
    let hNsolvable : Group.IsSolvable N.extensionQuotient :=
      Group.isSolvable_of_isSolvable_injective
        (f := (L.lowerQuotientEquiv S).toMonoidHom)
        (L.lowerQuotientEquiv S).injective
    let hUcyclic : IsCyclic U.extensionQuotient := hfactorCyclic i
    let : Finite
        (MF.field.toSubgroup ⧸
          extensionSubgroup MF.field N.field N.below) := N.finite
    let : Finite
        (K.field.toSubgroup ⧸
          extensionSubgroup K.field U.field U.below) := U.finite
    have hNcard : Nat.card N.extensionQuotient < Nat.card Q := by
      calc
        Nat.card N.extensionQuotient = Nat.card S :=
          Nat.card_congr (L.lowerQuotientEquiv S).toEquiv
        _ < Nat.card Q :=
          abstractReciprocity_subgroup_card_lt_of_ne_top S hSneTop
    have hrN : Function.Surjective
        (D.finiteReciprocityHom A v hAxiom MF N.field N.below) :=
      abstractReciprocity_solvable_finiteReciprocityHom_surjective
        v hcf hAxiom MF N
    have hrU : Function.Surjective
        (D.finiteReciprocityHom A v hAxiom K U.field U.below) :=
      (v.abstractReciprocity_cyclic_finiteReciprocityHom_bijective
        hcf hAxiom K U).2
    exact abstractReciprocity_finiteReciprocityHom_surjective_of_intermediate
      v hAxiom K L S hrN hrU
  · let S := commutator Q
    let hSnormal : S.Normal := inferInstance
    have hSneBot : S ≠ ⊥ := by
      intro hbot
      apply hcommutative
      have hcenter : Subgroup.center Q = ⊤ :=
        (commutator_eq_bot_iff_center_eq_top Q).1 hbot
      let hcommGroup : CommGroup Q :=
        Group.commGroupOfCenterEqTop hcenter
      exact ⟨⟨fun x y => hcommGroup.mul_comm x y⟩⟩
    have hSlt : S < ⊤ :=
      Group.IsSolvable.commutator_lt_top_of_nontrivial Q
    let M := L.intermediateField S
    let N := L.lowerFiniteGalois S
    let U := L.intermediateFiniteGalois S hSnormal
    let hMfinite : Finite
        (K.field.toSubgroup ⧸ extensionSubgroup K.field M
          (L.intermediateField_le_base S)) :=
      L.intermediateField_finite S
    let hMabsolute : Finite ((baseField G).toSubgroup ⧸
        extensionSubgroup (baseField G) M (le_baseField M)) :=
      FiniteGaloisSubextension.finite_extension_trans
        (L.intermediateField_le_base S) (le_baseField K.field)
    let MF : FiniteAbstractField G := ⟨M, hMabsolute⟩
    let hNsolvable : Group.IsSolvable N.extensionQuotient :=
      Group.isSolvable_of_isSolvable_injective
        (f := (L.lowerQuotientEquiv S).toMonoidHom)
        (L.lowerQuotientEquiv S).injective
    let hUpperSolvable : Group.IsSolvable (L.upperQuotient S) := by
      change Group.IsSolvable (Q ⧸ S)
      infer_instance
    let hUsolvable : Group.IsSolvable U.extensionQuotient :=
      Group.isSolvable_of_isSolvable_injective
        (f := (L.upperQuotientEquiv S).symm.toMonoidHom)
        (L.upperQuotientEquiv S).symm.injective
    let : Finite
        (MF.field.toSubgroup ⧸
          extensionSubgroup MF.field N.field N.below) := N.finite
    let : Finite
        (K.field.toSubgroup ⧸
          extensionSubgroup K.field U.field U.below) := U.finite
    have hNcard : Nat.card N.extensionQuotient < Nat.card Q := by
      calc
        Nat.card N.extensionQuotient = Nat.card S :=
          Nat.card_congr (L.lowerQuotientEquiv S).toEquiv
        _ < Nat.card Q :=
          abstractReciprocity_subgroup_card_lt_of_ne_top S hSlt.ne
    have hUcard : Nat.card U.extensionQuotient < Nat.card Q := by
      calc
        Nat.card U.extensionQuotient = Nat.card (Q ⧸ S) :=
          Nat.card_congr (L.upperQuotientEquiv S).symm.toEquiv
        _ < Nat.card Q :=
          abstractReciprocity_quotient_card_lt_of_ne_bot S hSneBot
    have hrN : Function.Surjective
        (D.finiteReciprocityHom A v hAxiom MF N.field N.below) :=
      abstractReciprocity_solvable_finiteReciprocityHom_surjective
        v hcf hAxiom MF N
    have hrU : Function.Surjective
        (D.finiteReciprocityHom A v hAxiom K U.field U.below) :=
      abstractReciprocity_solvable_finiteReciprocityHom_surjective
        v hcf hAxiom K U
    exact abstractReciprocity_finiteReciprocityHom_surjective_of_intermediate
      v hAxiom K L S hrN hrU
termination_by Nat.card L.extensionQuotient
decreasing_by all_goals assumption

end SolvableReciprocity

/-- The Sylow step in the first reduction.  The norm quotient
need not be known finite here: the unramified cohomology consequence kills every element by the
extension degree, so the Sylow argument is performed inside the finite
cyclic subgroup generated by that element. -/
theorem abstractReciprocity_finiteReciprocityHom_surjective
    (v : ValuationData D A) (hcf : SatisfiesClassFieldAxiom A)
    [IsTopologicalGroup G] [CompactSpace G] [T2Space G]
    [TotallyDisconnectedSpace G]
    (hAxiom : v.SatisfiesUnramifiedUnitCohomology D)
    (K : FiniteAbstractField G) (L : FiniteGaloisSubextension K.field) :
    letI : Finite
        (K.field.toSubgroup ⧸
          extensionSubgroup K.field L.field L.below) := L.finite
    Function.Surjective
      (D.finiteReciprocityHom A v hAxiom K L.field L.below) := by
  classical
  let : Finite
      (K.field.toSubgroup ⧸
        extensionSubgroup K.field L.field L.below) := L.finite
  let r := D.finiteReciprocityHom A v hAxiom K L.field L.below
  apply (AddMonoidHom.range_eq_top (f := r)).1
  have hdegreePos : 0 < (L.toFiniteAbstractExtension.degree : ℕ) :=
    L.toFiniteAbstractExtension.degree.property
  apply abstractReciprocity_addSubgroup_eq_top_of_exponent_and_sylow_le
    (L.toFiniteAbstractExtension.degree : ℕ) hdegreePos
    (finiteNormQuotient_degree_nsmul_eq_zero
      A L.toFiniteAbstractExtension) r.range
  intro p _ Ptarget x hx
  let Psource : Sylow p L.extensionQuotient := default
  let S : Subgroup L.extensionQuotient :=
    (Psource : Subgroup L.extensionQuotient)
  let M := L.intermediateField S
  let hLM := L.field_le_intermediateField S
  let hMK := L.intermediateField_le_base S
  let N := L.lowerFiniteGalois S
  let hMfinite : Finite
      (K.field.toSubgroup ⧸ extensionSubgroup K.field M hMK) :=
    L.intermediateField_finite S
  let hLMnormal : (extensionSubgroup M L.field hLM).Normal :=
    L.extensionSubgroup_over_intermediate_normal S
  let hLMfinite : Finite
      (M.toSubgroup ⧸ extensionSubgroup M L.field hLM) :=
    L.extension_over_intermediate_finite S
  let hMabsolute : Finite ((baseField G).toSubgroup ⧸
      extensionSubgroup (baseField G) M (le_baseField M)) :=
    FiniteGaloisSubextension.finite_extension_trans hMK (le_baseField K.field)
  let MF : FiniteAbstractField G := ⟨M, hMabsolute⟩
  let EMK : FiniteAbstractFieldExtension G :=
    { field := MF
      base := K
      below := hMK
      finiteQuotient := hMfinite }
  let hNsolvable : Group.IsSolvable N.extensionQuotient :=
    L.abstractReciprocity_sylow_lowerQuotient_isSolvable Psource
  let rLower := D.finiteReciprocityHom A v hAxiom MF L.field hLM
  have hrLower : Function.Surjective rLower :=
    abstractReciprocity_solvable_finiteReciprocityHom_surjective
      v hcf hAxiom MF N
  have hxNsmul :=
    L.abstractReciprocity_sylowAddSubgroup_le_intermediateDegree_nsmul_range
      Psource Ptarget hx
  obtain ⟨y, hy⟩ := hxNsmul
  obtain ⟨g, hg⟩ := hrLower
    (L.intermediateNormQuotientInclusion A S y)
  refine ⟨MonoidHom.toAdditive
    (finiteReciprocityNaturalityRestriction K.field M L.field L.field
      L.below hLM hMK le_rfl) g, ?_⟩
  have hcomm := D.finiteReciprocityNaturality_restriction_norm_commutes
    A v hAxiom EMK L.field L.field
      L.below hLM le_rfl
  have hrecip : r (MonoidHom.toAdditive
        (finiteReciprocityNaturalityRestriction K.field M L.field L.field
          L.below hLM hMK le_rfl) g) =
      L.intermediateNormMap A S (rLower g) := by
    change r (MonoidHom.toAdditive
        (finiteReciprocityNaturalityRestriction K.field M L.field L.field
          L.below hLM hMK le_rfl) g) =
      finiteReciprocityNaturalityNormMap A K.field M L.field L.field
        L.below hLM hMK le_rfl (rLower g)
    simpa only [r, rLower, AddMonoidHom.comp_apply] using
      (congrArg (fun f => f g) hcomm).symm
  exact hrecip.trans ((congrArg (L.intermediateNormMap A S) hg).trans
    ((L.intermediateNormMap_comp_inclusion A S y).trans hy))

/-- The second reduction: for an abelian Galois group, the
cyclic quotient coordinates are jointly faithful, hence the reciprocity
homomorphism is injective. -/
theorem abstractReciprocity_abelian_finiteReciprocityHom_injective
    (v : ValuationData D A) (hcf : SatisfiesClassFieldAxiom A)
    [IsTopologicalGroup G] [CompactSpace G] [T2Space G]
    [TotallyDisconnectedSpace G]
    (hAxiom : v.SatisfiesUnramifiedUnitCohomology D)
    (K : FiniteAbstractField G) (L : FiniteGaloisSubextension K.field)
    [hcommutative : IsMulCommutative L.extensionQuotient] :
    letI : Finite
        (K.field.toSubgroup ⧸
          extensionSubgroup K.field L.field L.below) := L.finite
    Function.Injective
      (D.finiteReciprocityHom A v hAxiom K L.field L.below) := by
  classical
  let : Finite
      (K.field.toSubgroup ⧸
        extensionSubgroup K.field L.field L.below) := L.finite
  let EKK : FiniteAbstractFieldExtension G :=
    { field := K
      base := K
      below := le_rfl
      finiteQuotient := (FiniteGaloisSubextension.refl K.field).finite }
  obtain ⟨I, hIfinite, _, _, f, _, hfaithful, hfactorCyclic,
      _⟩ := L.exists_cyclicIntermediateFields
  let : Fintype I := hIfinite
  rw [injective_iff_map_eq_zero]
  intro q hq
  have hrestriction (i : I) :
      L.upperRestrictionHom (MonoidHom.ker (f i)) q.toMul = 1 := by
    let S := MonoidHom.ker (f i)
    let hSnormal : S.Normal := inferInstance
    let M := L.intermediateField S
    let hLM := L.field_le_intermediateField S
    let hMK := L.intermediateField_le_base S
    let U := L.intermediateFiniteGalois S hSnormal
    let hMnormal : (extensionSubgroup K.field M hMK).Normal :=
      L.intermediateField_normal S hSnormal
    let hMfinite : Finite
        (K.field.toSubgroup ⧸ extensionSubgroup K.field M hMK) :=
      L.intermediateField_finite S
    let hUcyclic : IsCyclic U.extensionQuotient := hfactorCyclic i
    let rFactor := D.finiteReciprocityHom A v hAxiom K M hMK
    have hrFactor : Function.Injective rFactor :=
      (v.abstractReciprocity_cyclic_finiteReciprocityHom_bijective
        hcf hAxiom K U).1
    have hcomm := D.finiteReciprocityNaturality_restriction_norm_commutes
      A v hAxiom EKK M L.field hMK L.below hLM
    rw [finiteReciprocityNaturalityNormMap_sameBase_eq_normProjection,
      finiteReciprocityNaturalityRestriction_sameBase_eq_restriction] at hcomm
    have hzero : rFactor (MonoidHom.toAdditive
        (abstractReciprocityRestriction K.field M L.field hLM hMK) q) = 0 := by
      calc
        rFactor (MonoidHom.toAdditive
            (abstractReciprocityRestriction K.field M L.field hLM hMK) q) =
            abstractReciprocityNormProjection A K.field M L.field hLM hMK
              (D.finiteReciprocityHom A v hAxiom
                K L.field L.below q) := by
                  simpa only [rFactor, AddMonoidHom.comp_apply] using
                    (congrArg (fun h => h q) hcomm).symm
        _ = 0 := by rw [hq, map_zero]
    have hadd : MonoidHom.toAdditive
        (abstractReciprocityRestriction K.field M L.field hLM hMK) q = 0 := by
      apply hrFactor
      simpa only [map_zero] using hzero
    have hbridge (z : L.extensionQuotient) :
        L.upperRestrictionHom S z =
          abstractReciprocityRestriction K.field M L.field hLM hMK z := by
      refine QuotientGroup.induction_on z ?_
      intro k
      rw [L.upperRestrictionHom_mk,
        abstractReciprocityRestriction_mk]
    have hmul :
        abstractReciprocityRestriction K.field M L.field hLM hMK q.toMul = 1 :=
      congrArg Additive.toMul hadd
    exact (hbridge (show L.extensionQuotient from q.toMul)).trans hmul
  have hqone : q.toMul = 1 :=
    (L.upperRestrictionHom_jointlyFaithful f hfaithful q.toMul).1
      hrestriction
  exact Additive.toMul.injective (by simpa using hqone)

/-- The first reduction: the factor of the finite reciprocity equivalence
through the maximal abelian quotient is bijective. -/
theorem abstractReciprocity_abelianizedReciprocity_bijective
    (v : ValuationData D A) (hcf : SatisfiesClassFieldAxiom A)
    [IsTopologicalGroup G] [CompactSpace G] [T2Space G]
    [TotallyDisconnectedSpace G]
    (hAxiom : v.SatisfiesUnramifiedUnitCohomology D)
    (K : FiniteAbstractField G) (L : FiniteGaloisSubextension K.field) :
    letI : Finite
        (K.field.toSubgroup ⧸
          extensionSubgroup K.field L.field L.below) := L.finite
    Function.Bijective
      (D.transferNormNaturalityAbelianizedReciprocity
        A v hAxiom K L.field L.below) := by
  classical
  let : Finite
      (K.field.toSubgroup ⧸
        extensionSubgroup K.field L.field L.below) := L.finite
  let Q := L.extensionQuotient
  let S := commutator Q
  let hSnormal : S.Normal := inferInstance
  let M := L.intermediateField S
  let hLM := L.field_le_intermediateField S
  let hMK := L.intermediateField_le_base S
  let U := L.intermediateFiniteGalois S hSnormal
  let hMnormal : (extensionSubgroup K.field M hMK).Normal :=
    L.intermediateField_normal S hSnormal
  let hMfinite : Finite
      (K.field.toSubgroup ⧸ extensionSubgroup K.field M hMK) :=
    L.intermediateField_finite S
  let EKK : FiniteAbstractFieldExtension G :=
    { field := K
      base := K
      below := le_rfl
      finiteQuotient := (FiniteGaloisSubextension.refl K.field).finite }
  let upperEquiv := L.upperQuotientEquiv S
  let hUpperCommutative : IsMulCommutative (Q ⧸ S) := by
    dsimp only [S]
    exact
      (Subgroup.Normal.quotient_commutative_iff_commutator_le).2 le_rfl
  let hUcommutative : IsMulCommutative U.extensionQuotient :=
    ⟨⟨fun x y => by
      obtain ⟨x', rfl⟩ := upperEquiv.surjective x
      obtain ⟨y', rfl⟩ := upperEquiv.surjective y
      calc
        upperEquiv x' * upperEquiv y' =
            upperEquiv (x' * y') := (map_mul upperEquiv x' y').symm
        _ = upperEquiv (y' * x') := congrArg upperEquiv
          (Std.Commutative.comm
            (op := fun a b : Q ⧸ S => a * b) x' y')
        _ = upperEquiv y' * upperEquiv x' := map_mul upperEquiv y' x'⟩⟩
  let factor := D.transferNormNaturalityAbelianizedReciprocity
    A v hAxiom K L.field L.below
  let r := D.finiteReciprocityHom A v hAxiom K L.field L.below
  let p := abstractReciprocityNormProjection A K.field M L.field hLM hMK
  let rAb := D.finiteReciprocityHom A v hAxiom K M hMK
  have hrAb : Function.Injective rAb :=
    v.abstractReciprocity_abelian_finiteReciprocityHom_injective
      hcf hAxiom K U
  have hrestrictionEq (q : Q) :
      abstractReciprocityRestriction K.field M L.field hLM hMK q =
        L.abelianRestrictionHom q := by
    refine QuotientGroup.induction_on q ?_
    intro k
    rw [abstractReciprocityRestriction_mk]
    rfl
  have hright (q : Q) :
      p (r (Additive.ofMul q)) =
        rAb (Additive.ofMul (L.abelianRestrictionHom q)) := by
    have hcomm := D.finiteReciprocityNaturality_restriction_norm_commutes
      A v hAxiom EKK M L.field hMK L.below hLM
    rw [finiteReciprocityNaturalityNormMap_sameBase_eq_normProjection,
      finiteReciprocityNaturalityRestriction_sameBase_eq_restriction] at hcomm
    have hq := congrArg (fun h => h (Additive.ofMul q)) hcomm
    calc
      p (r (Additive.ofMul q)) =
          rAb (Additive.ofMul
            (abstractReciprocityRestriction K.field M L.field hLM hMK q)) := by
        change
          p (r (Additive.ofMul q)) =
            rAb (Additive.ofMul
              (abstractReciprocityRestriction K.field M L.field hLM hMK q)) at hq
        exact hq
      _ = rAb (Additive.ofMul (L.abelianRestrictionHom q)) := by
        rw [hrestrictionEq]
  constructor
  · rw [injective_iff_map_eq_zero]
    intro z hz
    change factor (Additive.ofMul z.toMul) = 0 at hz
    change Additive.ofMul z.toMul = 0
    revert hz
    refine QuotientGroup.induction_on z.toMul ?_
    intro q hz
    have hrq : r (Additive.ofMul q) = 0 := by
      calc
        r (Additive.ofMul q) =
            factor (Additive.ofMul (Abelianization.of q)) :=
          (D.transferNormNaturalityAbelianizedReciprocity_of
            A v hAxiom K L.field L.below q).symm
        _ = 0 := by
          change factor (Additive.ofMul (Abelianization.of q)) = 0 at hz
          exact hz
    have hcommutator : q ∈ commutator Q :=
      (abstractReciprocity_abelianReduction_kernel
        L p r rAb hright hrAb q).1 hrq
    have hof : Abelianization.of q = 1 :=
      (QuotientGroup.eq_one_iff q).2 hcommutator
    change Additive.ofMul (Abelianization.of q) = Additive.ofMul 1
    exact congrArg Additive.ofMul hof
  · intro b
    obtain ⟨q, hq⟩ :=
      v.abstractReciprocity_finiteReciprocityHom_surjective
        hcf hAxiom K L b
    refine ⟨Additive.ofMul (Abelianization.of q.toMul), ?_⟩
    calc
      factor (Additive.ofMul (Abelianization.of q.toMul)) =
          r (Additive.ofMul q.toMul) :=
        D.transferNormNaturalityAbelianizedReciprocity_of
          A v hAxiom K L.field L.below q.toMul
      _ = r q := by rw [ofMul_toMul]
      _ = b := hq

end ValuationData

namespace DegreeData

/-- **the abstract reciprocity theorem (reciprocity isomorphism).**  For a finite Galois
extension `L/K`, the reciprocity homomorphism identifies the abelianized
Galois group with the finite norm quotient. -/
noncomputable def abstractReciprocityEquiv
    (D : DegreeData G) (A : Rep ℤ G) (v : ValuationData D A)
    (hcf : SatisfiesClassFieldAxiom A)
    [IsTopologicalGroup G] [CompactSpace G] [T2Space G]
    [TotallyDisconnectedSpace G]
    (K : FiniteAbstractField G) (L : FiniteGaloisSubextension K.field) :
    letI : Finite
        (K.field.toSubgroup ⧸
          extensionSubgroup K.field L.field L.below) := L.finite
    Additive (Abelianization L.extensionQuotient) ≃+
      FiniteNormQuotient A K.field L.field L.below := by
  letI : Finite
      (K.field.toSubgroup ⧸
        extensionSubgroup K.field L.field L.below) := L.finite
  let hAxiom := v.classFieldAxiom_implies_unramifiedUnitCohomology hcf
  exact AddEquiv.ofBijective
    (D.transferNormNaturalityAbelianizedReciprocity
      A v hAxiom K L.field L.below)
    (v.abstractReciprocity_abelianizedReciprocity_bijective
      hcf hAxiom K L)

/-- On a Galois element, the abstract reciprocity theorem is the reciprocity homomorphism of
the finite reciprocity equivalence. -/
@[simp]
theorem abstractReciprocityEquiv_apply_of
    (D : DegreeData G) (A : Rep ℤ G) (v : ValuationData D A)
    (hcf : SatisfiesClassFieldAxiom A)
    [IsTopologicalGroup G] [CompactSpace G] [T2Space G]
    [TotallyDisconnectedSpace G]
    (K : FiniteAbstractField G) (L : FiniteGaloisSubextension K.field)
    (q : L.extensionQuotient) :
    letI : Finite
        (K.field.toSubgroup ⧸
          extensionSubgroup K.field L.field L.below) := L.finite
    D.abstractReciprocityEquiv A v hcf K L
        (Additive.ofMul (Abelianization.of q)) =
      D.finiteReciprocityHom A v (v.classFieldAxiom_implies_unramifiedUnitCohomology hcf)
        K L.field L.below
        (Additive.ofMul q) := by
  let : Finite
      (K.field.toSubgroup ⧸
        extensionSubgroup K.field L.field L.below) := L.finite
  exact D.transferNormNaturalityAbelianizedReciprocity_of
    A v (v.classFieldAxiom_implies_unramifiedUnitCohomology hcf) K L.field L.below
      q

/-- The norm-residue symbol `(·, L/K)`, defined in this construction as the inverse
of the reciprocity isomorphism in the abstract reciprocity theorem. -/
noncomputable def normResidueSymbol
    (D : DegreeData G) (A : Rep ℤ G) (v : ValuationData D A)
    (hcf : SatisfiesClassFieldAxiom A)
    [IsTopologicalGroup G] [CompactSpace G] [T2Space G]
    [TotallyDisconnectedSpace G]
    (K : FiniteAbstractField G) (L : FiniteGaloisSubextension K.field) :
    letI : Finite
        (K.field.toSubgroup ⧸
          extensionSubgroup K.field L.field L.below) := L.finite
    FiniteNormQuotient A K.field L.field L.below ≃+
      Additive (Abelianization L.extensionQuotient) := by
  letI : Finite
      (K.field.toSubgroup ⧸
        extensionSubgroup K.field L.field L.below) := L.finite
  exact (D.abstractReciprocityEquiv A v hcf K L).symm

/-- The norm-residue symbol sends the reciprocity class of a Galois
element back to its class in the abelianization. -/
@[simp]
theorem normResidueSymbol_finiteReciprocityHom
    (D : DegreeData G) (A : Rep ℤ G) (v : ValuationData D A)
    (hcf : SatisfiesClassFieldAxiom A)
    [IsTopologicalGroup G] [CompactSpace G] [T2Space G]
    [TotallyDisconnectedSpace G]
    (K : FiniteAbstractField G) (L : FiniteGaloisSubextension K.field)
    (q : L.extensionQuotient) :
    letI : Finite
        (K.field.toSubgroup ⧸
          extensionSubgroup K.field L.field L.below) := L.finite
    D.normResidueSymbol A v hcf K L
        (D.finiteReciprocityHom A v (v.classFieldAxiom_implies_unramifiedUnitCohomology hcf)
          K L.field L.below
          (Additive.ofMul q)) =
      Additive.ofMul (Abelianization.of q) := by
  let : Finite
      (K.field.toSubgroup ⧸
        extensionSubgroup K.field L.field L.below) := L.finite
  rw [← D.abstractReciprocityEquiv_apply_of A v hcf K L q]
  exact (D.abstractReciprocityEquiv A v hcf K L).symm_apply_apply _

/-- Reciprocity followed by the norm-residue symbol inverse is the
identity on the finite norm quotient. -/
@[simp]
theorem abstractReciprocity_normResidueSymbol
    (D : DegreeData G) (A : Rep ℤ G) (v : ValuationData D A)
    (hcf : SatisfiesClassFieldAxiom A)
    [IsTopologicalGroup G] [CompactSpace G] [T2Space G]
    [TotallyDisconnectedSpace G]
    (K : FiniteAbstractField G) (L : FiniteGaloisSubextension K.field) :
    letI : Finite
        (K.field.toSubgroup ⧸
          extensionSubgroup K.field L.field L.below) := L.finite
    ∀ a : FiniteNormQuotient A K.field L.field L.below,
    D.abstractReciprocityEquiv A v hcf K L
        (D.normResidueSymbol A v hcf K L a) = a := by
  let : Finite
      (K.field.toSubgroup ⧸
        extensionSubgroup K.field L.field L.below) := L.finite
  intro a
  exact (D.abstractReciprocityEquiv A v hcf K L).apply_symm_apply a

end DegreeData

/-!
# Abstract reciprocity, reciprocity naturality: the three naturality diagrams

Reciprocity naturality states three diagrams for the norm residue
symbol.  Before taking the inverse of reciprocity, their vertical arrows are
exactly the maps already constructed in norm--conjugation and transfer--norm naturality:

* restriction on Galois groups together with the relative norm;
* conjugation on both sides;
* transfer together with inclusion of fixed elements.

This file applies abelianization to the Galois arrows and combines each pair
of vertical arrows into one map between the products
`Additive G(L/K)ᵃᵇ × A_K/N_{L/K}A_L`.  The formulas on quotient
representatives are proved from the actual maps.  Finally, the abstract reciprocity theorem and
norm--conjugation and transfer--norm naturality turn those reciprocity squares into the three printed
commutative diagrams for the inverse norm-residue symbol.
-/

noncomputable section

-- Mathlib's `Rep ℤ G` currently fixes the acting group to universe zero.
variable {G : IntegralRepGroupType} [Group G] [TopologicalSpace G]

/-! ## The norm/restriction diagram -/

/-- Restriction in the first diagram of reciprocity naturality, after applying
abelianization. -/
def normResidueNaturalityAbelianizedRestriction
    {G : Type*} [Group G] [TopologicalSpace G]
    (K K' L L' : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.toSubgroup)
    (hL'K' : L'.toSubgroup ≤ K'.toSubgroup)
    (hK'K : K'.toSubgroup ≤ K.toSubgroup)
    (hL'L : L'.toSubgroup ≤ L.toSubgroup)
    [hLnormal : (extensionSubgroup K L hLK).Normal]
    [hL'normal : (extensionSubgroup K' L' hL'K').Normal] :
    Abelianization
        (K'.toSubgroup ⧸ extensionSubgroup K' L' hL'K') →*
      Abelianization (K.toSubgroup ⧸ extensionSubgroup K L hLK) :=
  Abelianization.map
    (finiteReciprocityNaturalityRestriction K K' L L' hLK hL'K' hK'K hL'L)

/--
Establishes the identity `normResidueNaturalityAbelianizedRestriction K K' L L' hLK hL'K' hK'K
hL'L (Abelianization.of (QuotientGroup.mk k')) = Abelianization.of (QuotientGroup.mk
(Subgroup.inclusion hK'K k'))`.
-/
@[simp]
theorem normResidueNaturalityAbelianizedRestriction_of_mk
    {G : Type*} [Group G] [TopologicalSpace G]
    (K K' L L' : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.toSubgroup)
    (hL'K' : L'.toSubgroup ≤ K'.toSubgroup)
    (hK'K : K'.toSubgroup ≤ K.toSubgroup)
    (hL'L : L'.toSubgroup ≤ L.toSubgroup)
    [hLnormal : (extensionSubgroup K L hLK).Normal]
    [hL'normal : (extensionSubgroup K' L' hL'K').Normal]
    (k' : K'.toSubgroup) :
    normResidueNaturalityAbelianizedRestriction K K' L L'
        hLK hL'K' hK'K hL'L
        (Abelianization.of (QuotientGroup.mk k')) =
      Abelianization.of
        (QuotientGroup.mk (Subgroup.inclusion hK'K k')) := by
  change
    (Abelianization.lift
      (Abelianization.of.comp
        (finiteReciprocityNaturalityRestriction K K' L L'
          hLK hL'K' hK'K hL'L)))
        (Abelianization.of (QuotientGroup.mk k')) = _
  rw [Abelianization.lift_apply_of]
  rfl

/-! ## The conjugation diagram -/

/-- The right vertical isomorphism `σ*` in the second diagram of
reciprocity naturality, obtained by abelianizing the actual conjugation isomorphism
from norm--conjugation naturality. -/
noncomputable def normResidueNaturalityAbelianizedConjugation
    {G : Type*} [Group G] [TopologicalSpace G] [ContinuousMul G]
    (K L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.toSubgroup) (s : G)
    [hLnormal : (extensionSubgroup K L hLK).Normal] :
    Abelianization (K.toSubgroup ⧸ extensionSubgroup K L hLK) ≃*
      Abelianization
        ((conjugateClosedSubgroup K s).toSubgroup ⧸
          extensionSubgroup (conjugateClosedSubgroup K s)
            (conjugateClosedSubgroup L s)
            (conjugateClosedSubgroup_mono hLK s)) :=
  (finiteReciprocityNaturalityConjugation K L hLK s).abelianizationCongr

/--
Establishes the identity `normResidueNaturalityAbelianizedConjugation K L hLK s (Abelianization.of
(QuotientGroup.mk k)) = Abelianization.of (QuotientGroup.mk (conjugateSubgroupEquiv K s k))`.
-/
@[simp]
theorem normResidueNaturalityAbelianizedConjugation_of_mk
    {G : Type*} [Group G] [TopologicalSpace G] [ContinuousMul G]
    (K L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.toSubgroup) (s : G)
    [hLnormal : (extensionSubgroup K L hLK).Normal]
    (k : K.toSubgroup) :
    normResidueNaturalityAbelianizedConjugation K L hLK s
        (Abelianization.of (QuotientGroup.mk k)) =
      Abelianization.of
        (QuotientGroup.mk (conjugateSubgroupEquiv K s k)) := by
  calc
    normResidueNaturalityAbelianizedConjugation K L hLK s
        (Abelianization.of (QuotientGroup.mk k)) =
      Abelianization.of
        (finiteReciprocityNaturalityConjugation K L hLK s (QuotientGroup.mk k)) :=
      abelianizationCongr_of (finiteReciprocityNaturalityConjugation K L hLK s)
        (QuotientGroup.mk k)
    _ = Abelianization.of
        (QuotientGroup.mk (conjugateSubgroupEquiv K s k)) := by
      rw [finiteReciprocityNaturalityConjugation_mk]

/-! ## The inclusion/transfer diagram -/

/-! ## The three norm-residue diagrams -/

namespace DegreeData

/-- **Reciprocity naturality, first diagram.**  The norm-residue symbol
commutes with restriction on Galois groups and the relative norm on norm
quotients. -/
theorem normResidueNaturality_norm_restriction
    (D : DegreeData G) (A : Rep ℤ G) (v : ValuationData D A)
    (hcf : SatisfiesClassFieldAxiom A)
    [IsTopologicalGroup G] [CompactSpace G] [T2Space G]
    [TotallyDisconnectedSpace G]
    (T : FiniteAbstractFieldExtension G) (L L' : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ T.base.field.toSubgroup)
    (hL'K' : L'.toSubgroup ≤ T.field.field.toSubgroup)
    (hL'L : L'.toSubgroup ≤ L.toSubgroup)
    [hLnormal : (extensionSubgroup T.base.field L hLK).Normal]
    [hL'normal : (extensionSubgroup T.field.field L' hL'K').Normal]
    [hLKfinite : Finite
      (T.base.field.toSubgroup ⧸ extensionSubgroup T.base.field L hLK)]
    [hL'K'finite : Finite
      (T.field.field.toSubgroup ⧸
        extensionSubgroup T.field.field L' hL'K')] :
    let E : FiniteGaloisSubextension T.base.field :=
      ⟨L, hLK, hLnormal, hLKfinite⟩
    let E' : FiniteGaloisSubextension T.field.field :=
      ⟨L', hL'K', hL'normal, hL'K'finite⟩
    (MonoidHom.toAdditive
        (normResidueNaturalityAbelianizedRestriction
          T.base.field T.field.field L L'
          hLK hL'K' T.below hL'L)).comp
      (D.normResidueSymbol A v hcf T.field E').toAddMonoidHom =
      (D.normResidueSymbol A v hcf T.base E).toAddMonoidHom.comp
        (finiteReciprocityNaturalityNormMap A
          T.base.field T.field.field L L'
          hLK hL'K' T.below hL'L) := by
  dsimp only
  let E : FiniteGaloisSubextension T.base.field :=
    ⟨L, hLK, hLnormal, hLKfinite⟩
  let E' : FiniteGaloisSubextension T.field.field :=
    ⟨L', hL'K', hL'normal, hL'K'finite⟩
  let q := MonoidHom.toAdditive
    (normResidueNaturalityAbelianizedRestriction
      T.base.field T.field.field L L'
      hLK hL'K' T.below hL'L)
  let b := finiteReciprocityNaturalityNormMap A
    T.base.field T.field.field L L' hLK hL'K' T.below hL'L
  have hRec :
      b.comp (D.abstractReciprocityEquiv A v hcf T.field E').toAddMonoidHom =
        (D.abstractReciprocityEquiv A v hcf T.base E).toAddMonoidHom.comp q := by
    apply AddMonoidHom.ext
    intro x
    change b (D.abstractReciprocityEquiv A v hcf T.field E'
        (Additive.ofMul x.toMul)) =
      D.abstractReciprocityEquiv A v hcf T.base E
        (q (Additive.ofMul x.toMul))
    refine QuotientGroup.induction_on x.toMul ?_
    intro z
    change b (D.abstractReciprocityEquiv A v hcf T.field E'
        (Additive.ofMul (Abelianization.of z))) =
      D.abstractReciprocityEquiv A v hcf T.base E
        (Additive.ofMul (Abelianization.of
          (finiteReciprocityNaturalityRestriction
            T.base.field T.field.field L L'
            hLK hL'K' T.below hL'L z)))
    rw [D.abstractReciprocityEquiv_apply_of A v hcf T.field E' z]
    rw [D.abstractReciprocityEquiv_apply_of A v hcf T.base E
      (finiteReciprocityNaturalityRestriction
        T.base.field T.field.field L L'
        hLK hL'K' T.below hL'L z)]
    have h := D.finiteReciprocityNaturality_restriction_norm_commutes
      A v (v.classFieldAxiom_implies_unramifiedUnitCohomology hcf)
      T L L' hLK hL'K' hL'L
    exact DFunLike.congr_fun h (Additive.ofMul z)
  exact normResidueNaturality_symm_naturality
    (D.abstractReciprocityEquiv A v hcf T.field E')
    (D.abstractReciprocityEquiv A v hcf T.base E) q b hRec

/-- **Reciprocity naturality, second diagram.**  The norm-residue symbol
commutes with conjugation of the extension and of norm classes. -/
theorem normResidueNaturality_conjugation
    (D : DegreeData G) (A : Rep ℤ G) (v : ValuationData D A)
    (hcf : SatisfiesClassFieldAxiom A)
    [IsTopologicalGroup G] [CompactSpace G] [T2Space G]
    [TotallyDisconnectedSpace G]
    (K : FiniteAbstractField G) (L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.field.toSubgroup) (s : G)
    [hLnormal : (extensionSubgroup K.field L hLK).Normal]
    [hLfinite : Finite
      (K.field.toSubgroup ⧸ extensionSubgroup K.field L hLK)] :
    let Ks := K.conjugate s
    let Ls := conjugateClosedSubgroup L s
    let hLsKs := conjugateClosedSubgroup_mono hLK s
    letI : Finite (Ks.field.toSubgroup ⧸
        extensionSubgroup Ks.field Ls hLsKs) :=
      finite_conjugateExtension K.field L hLK s
    let E : FiniteGaloisSubextension K.field :=
      ⟨L, hLK, hLnormal, hLfinite⟩
    let Es : FiniteGaloisSubextension Ks.field :=
      ⟨Ls, hLsKs, inferInstance, inferInstance⟩
    (MonoidHom.toAdditive
        (normResidueNaturalityAbelianizedConjugation
          K.field L hLK s).toMonoidHom).comp
      (D.normResidueSymbol A v hcf K E).toAddMonoidHom =
      (D.normResidueSymbol A v hcf Ks Es).toAddMonoidHom.comp
        (finiteReciprocityNaturalityConjugationNormMap A K.field L hLK s) := by
  dsimp only
  let hLsfinite : Finite
      ((conjugateClosedSubgroup K.field s).toSubgroup ⧸
        extensionSubgroup (conjugateClosedSubgroup K.field s)
          (conjugateClosedSubgroup L s)
          (conjugateClosedSubgroup_mono hLK s)) :=
    finite_conjugateExtension K.field L hLK s
  let Ks := K.conjugate s
  let E : FiniteGaloisSubextension K.field :=
    ⟨L, hLK, hLnormal, hLfinite⟩
  let Es : FiniteGaloisSubextension Ks.field :=
    ⟨conjugateClosedSubgroup L s, conjugateClosedSubgroup_mono hLK s,
      inferInstance, hLsfinite⟩
  let q := MonoidHom.toAdditive
    (normResidueNaturalityAbelianizedConjugation K.field L hLK s).toMonoidHom
  let b := finiteReciprocityNaturalityConjugationNormMap A K.field L hLK s
  have hRec :
      b.comp (D.abstractReciprocityEquiv A v hcf K E).toAddMonoidHom =
        (D.abstractReciprocityEquiv A v hcf Ks Es).toAddMonoidHom.comp q := by
    apply AddMonoidHom.ext
    intro x
    change b (D.abstractReciprocityEquiv A v hcf K E
        (Additive.ofMul x.toMul)) =
      D.abstractReciprocityEquiv A v hcf Ks Es
        (q (Additive.ofMul x.toMul))
    refine QuotientGroup.induction_on x.toMul ?_
    intro z
    change b (D.abstractReciprocityEquiv A v hcf K E
        (Additive.ofMul (Abelianization.of z))) =
      D.abstractReciprocityEquiv A v hcf Ks Es
        (Additive.ofMul (Abelianization.of
          (finiteReciprocityNaturalityConjugation K.field L hLK s z)))
    rw [D.abstractReciprocityEquiv_apply_of A v hcf K E z]
    rw [D.abstractReciprocityEquiv_apply_of A v hcf
      Ks Es
      (finiteReciprocityNaturalityConjugation K.field L hLK s z)]
    have h := D.finiteReciprocityNaturality_conjugation_commutes
      A v (v.classFieldAxiom_implies_unramifiedUnitCohomology hcf) K L hLK s
    exact DFunLike.congr_fun h (Additive.ofMul z)
  exact normResidueNaturality_symm_naturality
    (D.abstractReciprocityEquiv A v hcf K E)
    (D.abstractReciprocityEquiv A v hcf Ks Es) q b hRec

end DegreeData

end
end
end ClassFormation
end

section
-- module Solutions.OAIQ244_DUKE.AbstractClassFieldTheory_Reciprocity_FiniteAbelianClassification
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.KummerTheory.finite_finsupp_nsmulQuotient _root_.LocalClassFieldTheory.baseFixingExtensionQuotient_finite _root_.LocalClassFieldTheory.extensionSubgroupBase_normal _root_.LocalClassFieldTheory.finiteGaloisExtensionSubgroupOfEmbedding_normal _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitQuotientCarrier_finite _root_.LocalFieldTheory.DiscreteValuationField.finite_padicInt_finPi_nsmulQuotient _root_.LocalFieldTheory.DiscreteValuationField.finite_padicInt_pi_nsmulQuotient_of_coprime _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_multiplicative_nthPowerQuotient _root_.LocalFieldTheory.finite_nsmulAddQuotient_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.LubinTate.compatibleGroupFamiliesGroup _root_.OAI.PrimeDegreePackets.boundedRealFields_finite _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.RamificationTheory.HilbertRamification.ValuationSubring.inertiaGroup_normal _root_.RamificationTheory.HilbertRamification.ValuationSubring.ramificationGroupInInertiaAut_normal _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.CyclicCohomology.binaryCoefficientFamilyCommGroup _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.LocalClassFieldTheory.normalizationIntegerRingIsIntegralClosure _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen
attribute [-simp] _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.IsDiscreteValuationRing.addVal_ringEquiv _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.LocalClassFieldTheory.baseUnitsEquivGaloisAmbientFixed_val _root_.LocalClassFieldTheory.embeddedFieldUnitsEquivGaloisFixed_coe _root_.LocalClassFieldTheory.finiteGaloisUnitsEquivAbstractFixedOfEmbedding_coe _root_.LocalClassFieldTheory.finiteGaloisUnitsEquivAbstractFixed_coe _root_.LocalClassFieldTheory.intermediateFieldUnitsEquivGaloisFixed_coe _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.LocalFieldTheory.residueField_algebraMap_residue _root_.OAI.PrimeDegreePackets.ThetaConstruction.schwartzCM_apply _root_.infinitePlace_mult_smul
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

/-!
# Finite abelian classification by norm subgroups

The first paragraph of the finite classification proof uses the two restriction maps
from the Galois group of a compositum.  This file constructs those maps on
the actual finite quotients and proves that they are jointly injective.
This is the group-theoretic source of the implication that a reciprocity
class which restricts trivially to both subextensions is already trivial on
their compositum.
-/

noncomputable section

namespace ClassFormation

open CyclicCohomology KummerTheory

-- Mathlib's `Rep ℤ G` currently fixes the acting group to universe zero.
variable {G : IntegralRepGroupType} [Group G] [TopologicalSpace G]

namespace FiniteAbelianSubextension

variable {K : ClosedSubgroup G}

local instance extensionQuotient_normal_r2b18ec_1
    {G : Type*} [Group G] [TopologicalSpace G] {K : ClosedSubgroup G}
    (L : FiniteAbelianSubextension K) :
    (extensionSubgroup K L.field L.below).Normal :=
  L.normal
local instance representedQuotient_finite_r2b18ec_1
    {G : Type*} [Group G] [TopologicalSpace G] {K : ClosedSubgroup G}
    (L : FiniteAbelianSubextension K) :
    Finite (K.toSubgroup ⧸ extensionSubgroup K L.field L.below) :=
  L.finite
/-- Additive subgroups which are open for the explicitly declared norm
topology.  The topology is part of the predicate, so no ambient topology
instance is changed outside the finite abelian classification theorem. -/
def NormOpenAddSubgroup (A : Rep ℤ G) (K : ClosedSubgroup G) :=
  {H : AddSubgroup (ambientFixedAddSubgroup A K) //
    IsNormOpen A K (H : Set (ambientFixedAddSubgroup A K))}

/-- Norm-open subgroups inherit the literal inclusion order of their
underlying additive subgroups.  This instance is stated explicitly because
`NormOpenAddSubgroup` is an opaque boundary type, not a transparent alias. -/
instance normOpenAddSubgroupPartialOrder (A : Rep ℤ G)
    (K : ClosedSubgroup G) : PartialOrder (NormOpenAddSubgroup A K) :=
  PartialOrder.lift (fun H => H.1) (fun _ _ h => Subtype.ext h)

/-- The actual map in the finite abelian classification theorem, `L ↦ N_{L/K} A_L`, with openness
carried by the codomain rather than assumed. -/
def normSubgroupMap (A : Rep ℤ G)
    (L : FiniteAbelianSubextension K) : NormOpenAddSubgroup A K := by
  refine ⟨L.normSubgroup A, ?_⟩
  simpa [FiniteAbelianSubextension.normSubgroup,
    FiniteGaloisSubextension.normSubgroup] using
    ClassFormation.normSubgroup_isOpen A K
      L.toFiniteGaloisExtension

/-- Establishes the identity `(L.normSubgroupMap A).1 = L.normSubgroup A`. -/
@[simp]
theorem normSubgroupMap_val
    (A : Rep ℤ G) (L : FiniteAbelianSubextension K) :
    (L.normSubgroupMap A).1 = L.normSubgroup A :=
  rfl

/-! ## Recovering a field from the order of its finite quotient -/

end FiniteAbelianSubextension

namespace FiniteGaloisSubextension

variable {K : ClosedSubgroup G} [IsTopologicalGroup G]

local instance classification_extensionQuotient_finite
    (E : FiniteGaloisSubextension K) :
    Finite (K.toSubgroup ⧸ extensionSubgroup K E.field E.below) :=
  E.finite

local instance classification_abelianExtension_normal
    (M : FiniteAbelianSubextension K) :
    (extensionSubgroup K M.field M.below).Normal :=
  M.normal

local instance classification_abelianExtension_finite
    (M : FiniteAbelianSubextension K) :
    Finite (K.toSubgroup ⧸ extensionSubgroup K M.field M.below) :=
  M.finite

/-- The original finite Galois field lies below the abelian class-field
candidate cut out inside it. -/
theorem classFieldCandidate_field_le
    (E : FiniteGaloisSubextension K) (A : Rep ℤ G)
    (H : AddSubgroup (ambientFixedAddSubgroup A K))
    (rE : FiniteNormQuotient A K E.field E.below ≃+
      Additive (Abelianization E.extensionQuotient)) :
    E.field.toSubgroup ≤
      (ClassFormation.FiniteGaloisSubextension.classFieldCandidate A E H rE).field.toSubgroup := by
  rw [classFieldCandidate_field A E H rE]
  exact E.field_le_intermediateField
    (reciprocityPreimageSubgroup A E H rE)

/-- Restriction from `E/K` to its class-field candidate is trivial exactly
on the pulled-back subgroup used to define that candidate. -/
theorem classFieldCandidate_restriction_eq_one_iff
    (E : FiniteGaloisSubextension K) (A : Rep ℤ G)
    (H : AddSubgroup (ambientFixedAddSubgroup A K))
    (rE : FiniteNormQuotient A K E.field E.below ≃+
      Additive (Abelianization E.extensionQuotient))
    (q : E.extensionQuotient) :
    abstractReciprocityRestriction K
        (ClassFormation.FiniteGaloisSubextension.classFieldCandidate A E H rE).field E.field
        (classFieldCandidate_field_le E A H rE)
        (ClassFormation.FiniteGaloisSubextension.classFieldCandidate A E H rE).below q = 1 ↔
      q ∈ reciprocityPreimageSubgroup A E H rE := by
  let S := reciprocityPreimageSubgroup A E H rE
  let M := ClassFormation.FiniteGaloisSubextension.classFieldCandidate A E H rE
  let hEM := classFieldCandidate_field_le E A H rE
  let k : K.toSubgroup := Quotient.out q
  rw [← Quotient.out_eq' q]
  constructor
  · intro hk
    have hkM : k ∈ extensionSubgroup K M.field M.below :=
      (QuotientGroup.eq_one_iff k).1 hk
    have hkMfield : k.1 ∈ M.field.toSubgroup :=
      (mem_extensionSubgroup_iff K M.field M.below k).1 hkM
    have hkIntermediate : k.1 ∈ (E.intermediateField S).toSubgroup := by
      rw [← classFieldCandidate_field A E H rE]
      exact hkMfield
    have hkIntermediateSubgroup :
        k ∈ extensionSubgroup K (E.intermediateField S)
          (E.intermediateField_le_base S) :=
      (mem_extensionSubgroup_iff K (E.intermediateField S)
        (E.intermediateField_le_base S) k).2 hkIntermediate
    rw [E.extensionSubgroup_intermediateField_eq S] at hkIntermediateSubgroup
    exact hkIntermediateSubgroup
  · intro hkS
    have hkIntermediateSubgroup : k ∈ E.intermediateSubgroup S := hkS
    rw [← E.extensionSubgroup_intermediateField_eq S] at hkIntermediateSubgroup
    have hkIntermediate : k.1 ∈ (E.intermediateField S).toSubgroup :=
      (mem_extensionSubgroup_iff K (E.intermediateField S)
        (E.intermediateField_le_base S) k).1 hkIntermediateSubgroup
    have hkMfield : k.1 ∈ M.field.toSubgroup := by
      rw [classFieldCandidate_field A E H rE]
      exact hkIntermediate
    apply (QuotientGroup.eq_one_iff k).2
    exact (mem_extensionSubgroup_iff K M.field M.below k).2 hkMfield

/-- The finite classification surjectivity diagram chase.  The final public theorem feeds
`rE` and its compatibility from finite reciprocity, so neither appears as an
assumption of the classification endpoint. -/
theorem classFieldCandidate_normSubgroup_eq_of_reciprocity
    [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]
    (D : DegreeData G) (A : Rep ℤ G) (v : ValuationData D A)
    (hAxiom : v.SatisfiesUnramifiedUnitCohomology D)
    (K : FiniteAbstractField G)
    (E : FiniteGaloisSubextension K.field)
    (H : AddSubgroup (ambientFixedAddSubgroup A K.field))
    (hEH : ClassFormation.FiniteGaloisSubextension.normSubgroup A E ≤ H)
    (rE : FiniteNormQuotient A K.field E.field E.below ≃+
      Additive (Abelianization E.extensionQuotient))
    (hcompatE : ∀ q : E.extensionQuotient,
      rE.symm (Additive.ofMul (Abelianization.of q)) =
        D.finiteReciprocityHom A v hAxiom K E.field E.below
          (Additive.ofMul q))
    (hbijM : Function.Bijective
      (D.finiteReciprocityHom A v hAxiom K
        (ClassFormation.FiniteGaloisSubextension.classFieldCandidate A E H rE).field
        (ClassFormation.FiniteGaloisSubextension.classFieldCandidate A E H rE).below)) :
    (ClassFormation.FiniteGaloisSubextension.classFieldCandidate A E H rE).normSubgroup A = H := by
  let S := reciprocityPreimageSubgroup A E H rE
  let M := ClassFormation.FiniteGaloisSubextension.classFieldCandidate A E H rE
  let hEM := classFieldCandidate_field_le E A H rE
  let EKK : FiniteAbstractFieldExtension G :=
    { field := K
      base := K
      below := le_rfl
      finiteQuotient := (FiniteGaloisSubextension.refl K.field).finite }
  let : Finite
      (K.field.toSubgroup ⧸ extensionSubgroup K.field K.field le_rfl) :=
    (FiniteGaloisSubextension.refl K.field).finite
  have hnat := D.finiteReciprocityNaturality_restriction_norm_commutes
    A v hAxiom EKK M.field E.field M.below E.below hEM
  rw [finiteReciprocityNaturalityNormMap_sameBase_eq_normProjection,
    finiteReciprocityNaturalityRestriction_sameBase_eq_restriction]
      at hnat
  ext a
  have haClass :=
    reciprocityClass_mem_preimageSubgroup_iff A E H hEH rE a
  let zE : FiniteNormQuotient A K.field E.field E.below :=
    finiteNormClass A K.field E.field E.below a
  let ab : Additive (Abelianization E.extensionQuotient) := rE zE
  let q : E.extensionQuotient := Quotient.out ab.toMul
  let zM : FiniteNormQuotient A K.field M.field M.below :=
    finiteNormClass A K.field M.field M.below a
  have hab : Additive.ofMul (Abelianization.of q) = ab := by
    apply Additive.ext
    exact Quotient.out_eq' ab.toMul
  have hrecE :
      D.finiteReciprocityHom A v hAxiom K E.field E.below
          (Additive.ofMul q) = zE := by
    rw [← hcompatE q, hab, AddEquiv.symm_apply_apply]
  have hcomm :
      D.finiteReciprocityHom A v hAxiom K M.field M.below
          ((abstractReciprocityRestriction K.field M.field E.field hEM M.below).toAdditive
            (Additive.ofMul q)) = zM := by
    calc
      D.finiteReciprocityHom A v hAxiom K M.field M.below
          ((abstractReciprocityRestriction K.field M.field E.field hEM M.below).toAdditive
            (Additive.ofMul q)) =
        abstractReciprocityNormProjection A K.field M.field E.field hEM M.below
          (D.finiteReciprocityHom A v hAxiom K E.field E.below
            (Additive.ofMul q)) := by
              exact (DFunLike.congr_fun hnat (Additive.ofMul q)).symm
      _ = abstractReciprocityNormProjection A K.field M.field E.field hEM M.below zE :=
        congrArg _ hrecE
      _ = zM := by
        rw [abstractReciprocityNormProjection_finiteNormClass]
  change a ∈ finiteNormSubgroup A K.field M.field M.below ↔ a ∈ H
  constructor
  · intro haM
    have hzM : zM = 0 :=
      (finiteNormClass_eq_zero_iff A K.field M.field M.below a).2 haM
    have hresZero :
        (abstractReciprocityRestriction K.field M.field E.field hEM M.below).toAdditive
            (Additive.ofMul q) = 0 := by
      apply hbijM.1
      calc
        D.finiteReciprocityHom A v hAxiom K M.field M.below
            ((abstractReciprocityRestriction K.field M.field E.field hEM M.below).toAdditive
              (Additive.ofMul q)) = zM := hcomm
        _ = 0 := hzM
        _ = D.finiteReciprocityHom A v hAxiom K M.field M.below 0 :=
          (map_zero _).symm
    have hresOne :
        abstractReciprocityRestriction K.field M.field E.field hEM M.below q = 1 := by
      exact congrArg Additive.toMul hresZero
    apply haClass.1
    have hqS :=
      (classFieldCandidate_restriction_eq_one_iff E A H rE q).1
        hresOne
    convert hqS using 1; rfl
  · intro haH
    have hqS : q ∈ S := by
      apply haClass.2 at haH
      convert haH using 1; rfl
    have hresOne :
        abstractReciprocityRestriction K.field M.field E.field hEM M.below q = 1 :=
      (classFieldCandidate_restriction_eq_one_iff E A H rE q).2 hqS
    have hresZero :
        (abstractReciprocityRestriction K.field M.field E.field hEM M.below).toAdditive
            (Additive.ofMul q) = 0 := by
      exact congrArg Additive.ofMul hresOne
    have hzM : zM = 0 := by
      calc
        zM = D.finiteReciprocityHom A v hAxiom K M.field M.below
            ((abstractReciprocityRestriction K.field M.field E.field hEM M.below).toAdditive
              (Additive.ofMul q)) := hcomm.symm
        _ = D.finiteReciprocityHom A v hAxiom K M.field M.below 0 :=
          congrArg _ hresZero
        _ = 0 := map_zero _
    exact (finiteNormClass_eq_zero_iff A K.field M.field M.below a).1 hzM

end FiniteGaloisSubextension
end ClassFormation

namespace ClassFormation

open CyclicCohomology KummerTheory

-- Mathlib's `Rep ℤ G` currently fixes the acting group to universe zero.
variable {G : IntegralRepGroupType} [Group G] [TopologicalSpace G]

namespace FiniteAbelianSubextension

variable {D : DegreeData G} {A : Rep ℤ G}

/-- finite reciprocity specialized to an actual finite abelian extension.
The two halves are supplied by the general Sylow surjectivity argument and
the cyclic-coordinate injectivity argument; no bijectivity premise is
exposed by the finite abelian classification theorem. -/
theorem reciprocityEquiv_bijective
    (v : ValuationData D A) (hcf : SatisfiesClassFieldAxiom A)
    [IsTopologicalGroup G] [CompactSpace G] [T2Space G]
    [TotallyDisconnectedSpace G]
    (hAxiom : v.SatisfiesUnramifiedUnitCohomology D)
    (K : FiniteAbstractField G)
    (L : FiniteAbelianSubextension K.field) :
    letI : Finite
        (K.field.toSubgroup ⧸
          extensionSubgroup K.field L.field L.below) := L.finite
    Function.Bijective
      (D.finiteReciprocityHom A v hAxiom K L.field L.below) := by
  let : (extensionSubgroup K.field L.field L.below).Normal := L.normal
  let : Finite
      (K.field.toSubgroup ⧸ extensionSubgroup K.field L.field L.below) := L.finite
  let : IsMulCommutative L.toFiniteGaloisExtension.extensionQuotient :=
    L.commutative
  exact ⟨
    v.abstractReciprocity_abelian_finiteReciprocityHom_injective
      hcf hAxiom K L.toFiniteGaloisExtension,
    v.abstractReciprocity_finiteReciprocityHom_surjective
      hcf hAxiom K L.toFiniteGaloisExtension⟩

/-- The kernel equality in the surjectivity surjectivity step.  Starting
from `N_E ≤ H`, pull `H / N_E` back through the actual norm-residue symbol
of finite reciprocity and take its fixed field.  The norm subgroup of that concrete
finite abelian candidate is exactly `H`. -/
theorem classFieldCandidate_normSubgroup_eq
    (v : ValuationData D A) (hcf : SatisfiesClassFieldAxiom A)
    [IsTopologicalGroup G] [CompactSpace G] [T2Space G]
    [TotallyDisconnectedSpace G]
    (K : FiniteAbstractField G)
    (E : FiniteGaloisSubextension K.field)
    (H : AddSubgroup (ambientFixedAddSubgroup A K.field))
    (hEH : ClassFormation.FiniteGaloisSubextension.normSubgroup A E ≤ H) :
    let rE := D.normResidueSymbol A v hcf K E
    (ClassFormation.FiniteGaloisSubextension.classFieldCandidate A E H rE).normSubgroup A = H := by
  dsimp only
  let : (extensionSubgroup K.field E.field E.below).Normal := E.normal
  let : Finite
      (K.field.toSubgroup ⧸ extensionSubgroup K.field E.field E.below) := E.finite
  let hAxiom := v.classFieldAxiom_implies_unramifiedUnitCohomology hcf
  let rE := D.normResidueSymbol A v hcf K E
  let M := ClassFormation.FiniteGaloisSubextension.classFieldCandidate A E H rE
  have hcompatE (q : E.extensionQuotient) :
      rE.symm (Additive.ofMul (Abelianization.of q)) =
        D.finiteReciprocityHom A v hAxiom K E.field E.below
          (Additive.ofMul q) := by
    simpa only [rE, DegreeData.normResidueSymbol, AddEquiv.symm_symm] using
      D.abstractReciprocityEquiv_apply_of A v hcf K E q
  exact
    FiniteGaloisSubextension.classFieldCandidate_normSubgroup_eq_of_reciprocity
      D A v hAxiom K E H hEH rE hcompatE
        (reciprocityEquiv_bijective
          v hcf hAxiom K M)

/-- Every open subgroup in the norm topology is the norm subgroup of an
actual finite abelian extension.  The extension is the fixed field of the
literal preimage of `H / N_E` under the norm-residue symbol of finite reciprocity.
-/
theorem normSubgroupMap_surjective
    (v : ValuationData D A) (hcf : SatisfiesClassFieldAxiom A)
    [IsTopologicalGroup G] [CompactSpace G] [T2Space G]
    [TotallyDisconnectedSpace G]
    (K : FiniteAbstractField G) :
    Function.Surjective (normSubgroupMap A :
      FiniteAbelianSubextension K.field → NormOpenAddSubgroup A K.field) := by
  intro H
  obtain ⟨E, hEH⟩ := normOpenAddSubgroup_contains_finiteNormSubgroup
    A K.field H.1 H.2
  let : (extensionSubgroup K.field E.field E.below).Normal := E.normal
  let : Finite
      (K.field.toSubgroup ⧸ extensionSubgroup K.field E.field E.below) := E.finite
  let rE := D.normResidueSymbol A v hcf K E
  let M := ClassFormation.FiniteGaloisSubextension.classFieldCandidate A E H.1 rE
  have hM : M.normSubgroup A = H.1 := by
    simpa only [rE, M] using
      classFieldCandidate_normSubgroup_eq
        v hcf K E H.1 hEH
  refine ⟨M, ?_⟩
  apply Subtype.ext
  exact hM

end FiniteAbelianSubextension
end ClassFormation
end
end

section
-- module Solutions.OAIQ244_DUKE.AbstractClassFieldTheory_Reciprocity_MaximalUnramifiedSymbol
attribute [-instance] _root_.ClassFormation.FiniteAbelianSubextension.normOpenAddSubgroupPartialOrder _root_.ClassFormation.FiniteGaloisSubextension.abelianIntermediateField_normalInstance _root_.ClassFormation.FiniteGaloisSubextension.extensionSubgroup_over_intermediate_normalInstance _root_.ClassFormation.FiniteGaloisSubextension.inertiaImage_normalInstance _root_.ClassFormation.FiniteGaloisSubextension.intermediateField_normalInstance _root_.ClassFormation.FiniteGaloisSubextension.intermediateSubgroup_normalInstance _root_.ClassFormation.FiniteGaloisSubextension.upperQuotient_groupInstance _root_.ClassFormation.instIsAddTorsionFreeZHat _root_.ClassFormation.instIsMulTorsionFreeMultiplicativeZHat _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.DiscreteNthRootsSubgroup.instTopologicalSpaceSubtypeUnitsMemSubgroup _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalClassFieldTheory.baseFixingExtensionQuotient_finite _root_.LocalClassFieldTheory.extensionSubgroupBase_normal _root_.LocalClassFieldTheory.finiteGaloisExtensionSubgroupOfEmbedding_normal _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitQuotientCarrier_finite _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.LubinTate.compatibleGroupFamiliesGroup _root_.OAI.PrimeDegreePackets.boundedRealFields_finite _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.RamificationTheory.HilbertRamification.ValuationSubring.inertiaGroup_normal _root_.RamificationTheory.HilbertRamification.ValuationSubring.ramificationGroupInInertiaAut_normal _root_.RayClass.approximationCompletionTopologicalSpace _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.maximalIdealPowSuccQuotModule _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.LocalClassFieldTheory.normalizationIntegerRingIsIntegralClosure _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen
attribute [-simp] _root_.ClassFormation.DegreeData.abstractReciprocityEquiv_apply_of _root_.ClassFormation.DegreeData.abstractReciprocityTotallyRamifiedFrobeniusInM_restriction _root_.ClassFormation.DegreeData.abstractReciprocityTotallyRamifiedLowerGenerator_inclusion_restriction _root_.ClassFormation.DegreeData.abstractReciprocityTotallyRamifiedRestrictionEquiv_lowerGenerator _root_.ClassFormation.DegreeData.abstractReciprocity_normResidueSymbol _root_.ClassFormation.DegreeData.frobeniusExponent_chosenDegreeOneFrobeniusLiftOfFiniteTotallyRamified _root_.ClassFormation.DegreeData.frobeniusExponent_chosenDegreeOneFrobeniusLiftOfTotallyRamified _root_.ClassFormation.DegreeData.frobeniusRestriction_chosenDegreeOneFrobeniusLiftOfFiniteTotallyRamified _root_.ClassFormation.DegreeData.frobeniusRestriction_chosenDegreeOneFrobeniusLiftOfTotallyRamified _root_.ClassFormation.DegreeData.normResidueSymbol_finiteReciprocityHom _root_.ClassFormation.FiniteAbelianSubextension.extensionQuotientMk_apply _root_.ClassFormation.FiniteGaloisSubextension.classFieldCandidate_field _root_.ClassFormation.FiniteGaloisSubextension.intermediateFiniteAbelianOfCommutatorLe_field _root_.ClassFormation.FiniteGaloisSubextension.intermediateNormMap_finiteNormClass _root_.ClassFormation.FiniteGaloisSubextension.intermediateNormQuotientInclusion_finiteNormClass _root_.ClassFormation.FiniteGaloisSubextension.lowerInclusionHom_mk _root_.ClassFormation.FiniteGaloisSubextension.lowerQuotientEquiv_mk _root_.ClassFormation.FiniteGaloisSubextension.lowerQuotientEquiv_mk_coe _root_.ClassFormation.FiniteGaloisSubextension.lowerRestrictionHom_apply_coe _root_.ClassFormation.FiniteGaloisSubextension.mem_intermediateSubgroup_iff _root_.ClassFormation.FiniteGaloisSubextension.upperQuotientEquiv_mk_mk _root_.ClassFormation.FiniteGaloisSubextension.upperQuotientMk_apply _root_.ClassFormation.FiniteGaloisSubextension.upperRestrictionHom_mk _root_.ClassFormation.abstractReciprocityInclusion_mk _root_.ClassFormation.abstractReciprocityNormMap_finiteNormClass _root_.ClassFormation.abstractReciprocityNormProjection_finiteNormClass _root_.ClassFormation.abstractReciprocityRestriction_mk _root_.ClassFormation.cyclicNormClassHom_apply _root_.ClassFormation.extensionFixedRepresentationEquiv_apply_coe _root_.ClassFormation.extensionFixedRepresentationEquiv_symm_apply_coe _root_.ClassFormation.mem_normFilterBasis_iff _root_.ClassFormation.normResidueNaturalityAbelianizedConjugation_of_mk _root_.ClassFormation.normResidueNaturalityAbelianizedRestriction_of_mk _root_.ClassFormation.toZModPow_zHatToPadicInt _root_.ClassFormation.zHatReductionRingHom_apply _root_.ClassFormation.zHatRingEquivProfiniteIntegerPrimeProduct_apply _root_.ClassFormation.zHatToPadicInt_intCast _root_.ClassFormation.zHatToProfiniteIntegerPrimeProduct_apply _root_.ClassFormation.zHatToProfiniteIntegerPrimeProduct_intCast _root_.ClassFormation.zHatUnitsContinuousMulEquivPrimeProduct_coe_apply _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.IsDiscreteValuationRing.addVal_ringEquiv _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.KummerTheory.torsionQuotientEquivOfZHatMulDecomposition_mk _root_.KummerTheory.zHatUnitsContinuousMulEquivPrimeProduct_rationalCyclotomicCharacter _root_.LocalClassFieldTheory.baseFixingExtensionQuotientEquivAmbient_mk _root_.LocalClassFieldTheory.finiteResidueFrobeniusFromZHat_apply _root_.LocalClassFieldTheory.finiteResidueFrobeniusFromZHat_one _root_.LocalClassFieldTheory.residueAbsoluteDegreeIn_frobenius _root_.LocalClassFieldTheory.residueAbsoluteFrobenius_one _root_.LocalClassFieldTheory.residueFrobeniusToLimit_apply_component _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.LocalFieldTheory.residueField_algebraMap_residue _root_.OAI.PrimeDegreePackets.ThetaConstruction.schwartzCM_apply _root_.infinitePlace_mult_smul
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

/-!
# Abstract reciprocity: the maximal-unramified symbol

This file constructs the source maps used in maximal-unramified reciprocity.  In
particular, the maximal unramified quotient is projected to every finite
unramified Galois quotient, and its Frobenius is sent to the finite
arithmetic Frobenius.  The valuation--Frobenius map below is kept as a
candidate until its compatibility with the finite norm-residue symbols has
been proved from the unramified norm-quotient equivalence.
-/

noncomputable section

namespace ClassFormation

open ClassFormation CyclicCohomology KummerTheory

universe u

section DegreeOnly

variable {G : Type u} [Group G] [TopologicalSpace G]

namespace DegreeData

/-- Restriction from the maximal unramified Galois group over `K` to the
actual quotient of an unramified Galois extension `L / K`.  This construction
does not require the quotient to be finite. -/
def maximalUnramifiedExtensionRestriction
    (D : DegreeData G) (K : FiniteResidueAbstractField D)
    (L : GaloisSubextension K.field)
    (hUnramified : L.IsUnramified D) :
    (K.field.toSubgroup ⧸ D.fieldInertiaWithin K.field) →*
      L.extensionQuotient :=
  L.extensionQuotientMulEquiv.symm.toMonoidHom.comp
    (QuotientGroup.map (D.fieldInertiaWithin K.field)
      (extensionSubgroup K.field L.field L.below)
      (MonoidHom.id K.field.toSubgroup) (by
        intro k hk
        apply (mem_extensionSubgroup_iff K.field L.field L.below k).2
        exact (L.isUnramified_iff_inertia_le D).1 hUnramified ⟨k.2, hk⟩))

/--
Establishes the identity `maximalUnramifiedExtensionRestriction D K L hUnramified
(QuotientGroup.mk k) = L.extensionQuotientMk k`.
-/
@[simp]
theorem maximalUnramifiedExtensionRestriction_mk
    (D : DegreeData G) (K : FiniteResidueAbstractField D)
    (L : GaloisSubextension K.field)
    (hUnramified : L.IsUnramified D)
    (k : K.field.toSubgroup) :
    maximalUnramifiedExtensionRestriction D K L hUnramified
        (QuotientGroup.mk k) =
      L.extensionQuotientMk k := by
  exact
    L.extensionQuotientMulEquiv.symm_apply_eq.mpr
      (L.extensionQuotientMk_apply k).symm

/-- Restriction sends the maximal-unramified Frobenius to the arithmetic
Frobenius of every finite unramified quotient. -/
@[simp]
theorem maximalUnramifiedRestriction_frobenius
    (D : DegreeData G) (K : FiniteResidueAbstractField D)
    (L : GaloisSubextension K.field)
    (hUnramified : L.IsUnramified D) :
    maximalUnramifiedExtensionRestriction D K L hUnramified
        (D.frobenius K) =
      L.extensionQuotientMulEquiv.symm
        (D.unramifiedFrobenius K L.field L.below) := by
  let φ : K.field.toSubgroup := Classical.choose
    (D.normalizedDegree_surjective K
      (Multiplicative.ofAdd (1 : ZHat)))
  have hφ : D.normalizedDegree K φ =
      Multiplicative.ofAdd (1 : ZHat) :=
    Classical.choose_spec
      (D.normalizedDegree_surjective K
        (Multiplicative.ofAdd (1 : ZHat)))
  have hmk : (QuotientGroup.mk φ :
      K.field.toSubgroup ⧸ D.fieldInertiaWithin K.field) = D.frobenius K := by
    apply (D.maximalUnramifiedDegreeEquiv K).injective
    rw [D.maximalUnramifiedDegreeEquiv_mk, hφ,
      D.maximalUnramifiedDegreeEquiv_frobenius]
  rw [← hmk, maximalUnramifiedExtensionRestriction_mk D]
  symm
  exact
    L.extensionQuotientMulEquiv.symm_apply_eq.mpr
      (L.extensionQuotientMk_apply φ).symm

/-- Restriction to a bundled finite Galois extension.  The named comparison
between the finite and non-finite Galois quotient boundaries is applied here,
once, rather than left to definitional unfolding in every consumer. -/
def finiteUnramifiedRestriction
    (D : DegreeData G) (K : FiniteResidueAbstractField D)
    (L : FiniteGaloisSubextension K.field)
    (hUnramified : L.IsUnramified D) :
    (K.field.toSubgroup ⧸ D.fieldInertiaWithin K.field) →*
      L.extensionQuotient :=
  L.toGaloisExtensionQuotientMulEquiv.symm.toMonoidHom.comp
    (D.maximalUnramifiedExtensionRestriction K L.toGaloisSubextension
      (L.isUnramified_toGaloisSubextension D hUnramified))

/--
Establishes the identity `finiteUnramifiedRestriction D K L hUnramified (QuotientGroup.mk k) =
L.extensionQuotientMk k`.
-/
@[simp]
theorem finiteUnramifiedRestriction_mk
    (D : DegreeData G) (K : FiniteResidueAbstractField D)
    (L : FiniteGaloisSubextension K.field)
    (hUnramified : L.IsUnramified D) (k : K.field.toSubgroup) :
    finiteUnramifiedRestriction D K L hUnramified (QuotientGroup.mk k) =
      L.extensionQuotientMk k := by
  apply L.extensionQuotientMulEquiv.injective
  simp [finiteUnramifiedRestriction,
    maximalUnramifiedExtensionRestriction_mk,
    FiniteGaloisSubextension.toGaloisExtensionQuotientMulEquiv]
  exact L.toGaloisSubextension.extensionQuotientMk_apply k

/--
Establishes the identity `finiteUnramifiedRestriction D K L hUnramified (D.frobenius K) =
L.extensionQuotientMulEquiv.symm (D.unramifiedFrobenius K L.field L.below)`.
-/
@[simp]
theorem finiteUnramifiedRestriction_frobenius
    (D : DegreeData G) (K : FiniteResidueAbstractField D)
    (L : FiniteGaloisSubextension K.field)
    (hUnramified : L.IsUnramified D) :
    finiteUnramifiedRestriction D K L hUnramified (D.frobenius K) =
      L.extensionQuotientMulEquiv.symm
        (D.unramifiedFrobenius K L.field L.below) := by
  rw [finiteUnramifiedRestriction, MonoidHom.comp_apply,
    maximalUnramifiedRestriction_frobenius]
  apply L.extensionQuotientMulEquiv.injective
  simp [FiniteGaloisSubextension.toGaloisExtensionQuotientMulEquiv]
  exact
    L.toGaloisSubextension.extensionQuotientMulEquiv.apply_symm_apply
      (D.unramifiedFrobenius K L.field L.below)

theorem finiteUnramifiedDegreeHom_killsExtension
    (D : DegreeData G) (K : FiniteResidueAbstractField D)
    (L : FiniteGaloisSubextension K.field)
    (hUnramified : L.IsUnramified D) :
    extensionSubgroup K.field L.field L.below ≤
      (((zHatReductionMul
        (L.toFiniteAbstractExtension.degree : ℕ)
        L.toFiniteAbstractExtension.degree.property).comp
        (D.normalizedDegree K)).toMonoidHom).ker := by
  let : Finite
      (K.field.toSubgroup ⧸
        extensionSubgroup K.field L.field L.below) :=
    L.finite
  intro k hk
  let E := L.toFiniteAbstractExtension
  let ER : FiniteResidueAbstractExtension D :=
    FiniteResidueAbstractExtension.ofInclusion D L.field K L.below
  let n := (E.degree : ℕ)
  let hn : 0 < n := E.degree.property
  have hkL : k.1 ∈ L.field.toSubgroup :=
    (mem_extensionSubgroup_iff K.field L.field L.below k).1 hk
  let l : ER.field.field.toSubgroup :=
    ⟨k.1, by
      simpa [ER, FiniteResidueAbstractExtension.ofInclusion] using hkL⟩
  have hkl : Subgroup.inclusion ER.below l = k := Subtype.ext rfl
  have hd := D.frobeniusRestrictionNaturality_normalizedDegree ER l
  have hERUnramified : ER.toFiniteAbstractExtension.IsUnramified D := by
    simpa [ER, FiniteResidueAbstractExtension.ofInclusion,
      FiniteResidueAbstractExtension.toFiniteAbstractExtension,
      FiniteGaloisSubextension.IsUnramified,
      FiniteGaloisSubextension.toFiniteAbstractExtension] using hUnramified
  have hdegree :
      (ER.toFiniteAbstractExtension.degree : ℕ) = n := by
    change Nat.card ER.toFiniteAbstractExtension.quotient =
      Nat.card E.quotient
    apply Nat.card_congr
    change
      (K.field.toSubgroup ⧸
          extensionSubgroup K.field L.field L.below) ≃
        (K.field.toSubgroup ⧸
          extensionSubgroup K.field L.field L.below)
    exact Equiv.refl _
  have hresidueDegree : (ER.residueDegree : ℕ) = n := by
    exact
      (ER.toFiniteAbstractExtension.residueDegree_eq_degree_of_isUnramified
        D hERUnramified).trans hdegree
  rw [hresidueDegree] at hd
  have hd' :
      (D.normalizedDegree K (Subgroup.inclusion ER.below l)).toAdd =
        n • (D.normalizedDegree ER.field l).toAdd := by
    change
      (D.normalizedDegree ER.base
        (Subgroup.inclusion ER.below l)).toAdd =
        n • (D.normalizedDegree ER.field l).toAdd
    exact hd
  change zHatReductionMul n hn (D.normalizedDegree K k) = 1
  apply Multiplicative.ext
  change zHatReduction n hn (D.normalizedDegree K k).toAdd = 0
  rw [← hkl, hd', map_nsmul]
  exact ZModModule.char_nsmul_eq_zero n _

/-- Normalized degree modulo `[L : K]` on a finite unramified Galois
quotient. -/
def finiteUnramifiedDegreeHom
    (D : DegreeData G) (K : FiniteResidueAbstractField D)
    (L : FiniteGaloisSubextension K.field)
    (hUnramified : L.IsUnramified D) :
    L.extensionQuotient →*
      Multiplicative
        (ZMod (L.toFiniteAbstractExtension.degree : ℕ)) :=
  (QuotientGroup.lift (extensionSubgroup K.field L.field L.below)
      (((zHatReductionMul
        (L.toFiniteAbstractExtension.degree : ℕ)
        L.toFiniteAbstractExtension.degree.property).comp
        (D.normalizedDegree K)).toMonoidHom)
      (finiteUnramifiedDegreeHom_killsExtension D K L hUnramified)).comp
    L.extensionQuotientMulEquiv.toMonoidHom

/--
Establishes the identity `finiteUnramifiedDegreeHom D K L hUnramified (L.extensionQuotientMk k) =
zHatReductionMul (L.toFiniteAbstractExtension.degree : ℕ)
L.toFiniteAbstractExtension.degree.property (D.normalizedDegree K k)`.
-/
@[simp]
theorem finiteUnramifiedDegreeHom_mk
    (D : DegreeData G) (K : FiniteResidueAbstractField D)
    (L : FiniteGaloisSubextension K.field)
    (hUnramified : L.IsUnramified D)
    (k : K.field.toSubgroup) :
    finiteUnramifiedDegreeHom D K L hUnramified
        (L.extensionQuotientMk k) =
      zHatReductionMul
        (L.toFiniteAbstractExtension.degree : ℕ)
        L.toFiniteAbstractExtension.degree.property
        (D.normalizedDegree K k) := by
  exact QuotientGroup.lift_mk' (extensionSubgroup K.field L.field L.below)
    (finiteUnramifiedDegreeHom_killsExtension D K L hUnramified) k

/--
The specified map is surjective: `Function.Surjective (finiteUnramifiedDegreeHom D K L
hUnramified)`.
-/
theorem finiteUnramifiedDegreeHom_surjective
    (D : DegreeData G) (K : FiniteResidueAbstractField D)
    (L : FiniteGaloisSubextension K.field)
    (hUnramified : L.IsUnramified D) :
    Function.Surjective
      (finiteUnramifiedDegreeHom D K L hUnramified) := by
  intro z
  let E := L.toFiniteAbstractExtension
  let n := (E.degree : ℕ)
  let hn : 0 < n := E.degree.property
  obtain ⟨w, hw⟩ := zHatReduction_surjective n hn z.toAdd
  obtain ⟨k, hk⟩ :=
    D.normalizedDegree_surjective K (Multiplicative.ofAdd w)
  refine ⟨L.extensionQuotientMk k, ?_⟩
  rw [finiteUnramifiedDegreeHom_mk D]
  apply Multiplicative.ext
  change zHatReduction n hn (D.normalizedDegree K k).toAdd = z.toAdd
  rw [hk]
  exact hw

/-- For an unramified finite extension, normalized degree modulo the
extension degree is an isomorphism. -/
def finiteUnramifiedDegreeEquiv
    (D : DegreeData G) (K : FiniteResidueAbstractField D)
    (L : FiniteGaloisSubextension K.field)
    (hUnramified : L.IsUnramified D) :
    L.extensionQuotient ≃*
      Multiplicative (ZMod (L.toFiniteAbstractExtension.degree : ℕ)) := by
  let E := L.toFiniteAbstractExtension
  let n := (E.degree : ℕ)
  let hn : 0 < n := E.degree.property
  letI : NeZero n := ⟨hn.ne'⟩
  letI : Finite
      (K.field.toSubgroup ⧸
        extensionSubgroup K.field L.field L.below) :=
    L.finite
  apply MulEquiv.ofBijective
    (finiteUnramifiedDegreeHom D K L hUnramified)
  apply (Nat.bijective_iff_surjective_and_card _).2
  refine ⟨finiteUnramifiedDegreeHom_surjective D
    K L hUnramified, ?_⟩
  calc
    Nat.card L.extensionQuotient =
        Nat.card
          (K.field.toSubgroup ⧸
            extensionSubgroup K.field L.field L.below) :=
      Nat.card_congr L.extensionQuotientMulEquiv.toEquiv
    _ =
        (extensionSubgroup K.field L.field L.below).index :=
      (Subgroup.index_eq_card _).symm
    _ = n := by
      change
        (extensionSubgroup E.base E.field E.below).index =
          (E.degree : ℕ)
      exact E.extensionSubgroup_index_eq_degree
    _ = Nat.card (ZMod n) := (Nat.card_zmod n).symm
    _ = Nat.card (Multiplicative (ZMod n)) :=
      (Nat.card_congr Multiplicative.toAdd).symm

/-- The maximal and finite normalized-degree isomorphisms commute with
restriction and reduction modulo `[L : K]`. -/
theorem finiteUnramifiedDegreeEquiv_restriction
    (D : DegreeData G) (K : FiniteResidueAbstractField D)
    (L : FiniteGaloisSubextension K.field)
    (hUnramified : L.IsUnramified D)
    (x : K.field.toSubgroup ⧸ D.fieldInertiaWithin K.field) :
    finiteUnramifiedDegreeEquiv D K L hUnramified
        (finiteUnramifiedRestriction D K L hUnramified x) =
      zHatReductionMul
        (L.toFiniteAbstractExtension.degree : ℕ)
        L.toFiniteAbstractExtension.degree.property
        (D.maximalUnramifiedDegreeEquiv K x) := by
  refine Quotient.inductionOn' x ?_
  intro k
  change finiteUnramifiedDegreeHom D K L hUnramified
      (L.extensionQuotientMk k) = _
  rw [finiteUnramifiedDegreeHom_mk D,
    D.maximalUnramifiedDegreeEquiv_mk]

/-- The arithmetic Frobenius has finite normalized degree one. -/
@[simp]
theorem finiteUnramifiedDegreeEquiv_unramifiedFrobenius
    (D : DegreeData G) (K : FiniteResidueAbstractField D)
    (L : FiniteGaloisSubextension K.field)
    (hUnramified : L.IsUnramified D) :
    finiteUnramifiedDegreeEquiv D K L hUnramified
        (L.extensionQuotientMulEquiv.symm
          (D.unramifiedFrobenius K L.field L.below)) =
      Multiplicative.ofAdd
        (1 : ZMod (L.toFiniteAbstractExtension.degree : ℕ)) := by
  rw [← finiteUnramifiedRestriction_frobenius D K L hUnramified,
    finiteUnramifiedDegreeEquiv_restriction D]
  rw [D.maximalUnramifiedDegreeEquiv_frobenius]
  apply Multiplicative.ext
  rfl

/-- Profinite exponentiation of the maximal-unramified Frobenius, expressed
through the canonical degree isomorphism with `ℤ̂`. -/
def maximalUnramifiedFrobeniusPower
    (D : DegreeData G) (K : FiniteResidueAbstractField D) (z : ZHat) :
    Additive (K.field.toSubgroup ⧸ D.fieldInertiaWithin K.field) :=
  (D.maximalUnramifiedDegreeEquiv K).toAdditive.symm z

/--
Establishes the identity `maximalUnramifiedFrobeniusPower D K 1 = Additive.ofMul (D.frobenius K)`.
-/
@[simp]
theorem maximalUnramifiedFrobeniusPower_one
    (D : DegreeData G) (K : FiniteResidueAbstractField D) :
    maximalUnramifiedFrobeniusPower D K 1 =
      Additive.ofMul (D.frobenius K) := by
  rfl

end DegreeData

end DegreeOnly

section Representation

-- Mathlib's `Rep ℤ G` currently fixes the acting group to universe zero.
variable {G : IntegralRepGroupType} [Group G] [TopologicalSpace G]
variable {D : DegreeData G} {A : Rep ℤ G}

open DegreeData

namespace ValuationData

/-- The maximal-unramified norm-residue symbol, given by the
valuation--Frobenius homomorphism. -/
def maximalUnramifiedNormResidueSymbol
    (v : ValuationData D A)
    (K : FiniteAbstractField G) :
    ambientFixedAddSubgroup A K.field →+
      Additive (K.field.toSubgroup ⧸ D.fieldInertiaWithin K.field) :=
  (D.maximalUnramifiedDegreeEquiv
    (K.toFiniteResidueAbstractField D)).toAdditive.symm.toAddMonoidHom.comp
    ((v.valueGroup).subtype.comp (v.valuationAt K))

end ValuationData

end Representation

end ClassFormation
end
end

section
-- module Solutions.OAIQ244_DUKE.GlobalClassFieldTheory_ClassFieldAxiom_IdeleClassPowerLocalUnitQuotient_ArchimedeanPowerIndex
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.residueFieldZModAlgebra _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.CyclicCohomology.binaryCoefficientFamilyCommGroup _root_.LocalClassFieldTheory.normalizationIntegerRingIsIntegralClosure _root_.chosenFinitePlaceCompletionAlgebra
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

/-!
# Archimedean power indices in idele class quotients

This file defines the concrete idele-class subgroup attached to local power
conditions and computes its archimedean local indices.
-/

open scoped NumberField Classical NNReal ValuativeRel TensorProduct
open NumberField IsDedekindDomain
open KummerTheory

noncomputable section

namespace GlobalClassFieldTheory.ClassFieldAxiom

variable {K : Type} [Field K] [NumberField K]

/-- Elementwise form of `C_K(S,T)=h(S,T)Kˣ/Kˣ`. -/
theorem mem_ideleClassPowerLocalUnitSubgroup_iff
    (n : ℕ+)
    (S T : Finset (HeightOneSpectrum (𝓞 K)))
    (c : IdeleClassGroup K) :
    c ∈ ideleClassPowerLocalUnitSubgroup (K := K) n S T ↔
      ∃ a : IdeleGroup K,
        a ∈ idelePowerLocalUnitSubgroup (K := K) n S T ∧
          QuotientGroup.mk' (IdeleGroup.principalSubgroup K) a = c := by
  rfl


end GlobalClassFieldTheory.ClassFieldAxiom
end
end


