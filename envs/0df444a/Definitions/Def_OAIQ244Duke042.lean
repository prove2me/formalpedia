-- Prove2me | Definitions.Def_OAIQ244Duke042
-- name    : OAIQ244Duke042
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-13T06:39:35.657208+00:00
-- url     : https://prove2.me/theorems/0408811a-db0f-4c17-a68f-4819cd4e8913
-- title:
--   Definitions bundle OAIQ244Duke042 of the split of OpenAI, Equidistribution of Prime-Degree Torus Packets with Arbitrary Local Type
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.DukePrimeDegree.prime_degree_packet_measure_equidistribution_unconditional` and `OAI.DukePrimeDegree.prime_degree_packet_measures_tendsto_haar_unconditional`, carved from OpenAI's openai/math development (OpenAI, *Equidistribution of Prime-Degree Torus Packets with Arbitrary Local Type*, OpenAI Math Release, September 24, 2026, result family 15, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 109 declarations of OpenAI's Lean: 37 definitions, 6 instances and 66 theorems. The definitions and types are `GlobalClassFieldTheory.GlobalClassFields.ConductorialSubgroup`, `GlobalClassFieldTheory.GlobalClassFields.ConductorialSubgroup.chosenDefiningModulus`, `GlobalClassFieldTheory.GlobalClassFields.ConductorialSubgroup.narrowFiniteConductor`, `GlobalClassFieldTheory.GlobalClassFields.ConductorialSubgroup.narrowFiniteConductorBoundingModulus`, `GlobalClassFieldTheory.GlobalClassFields.ConductorialSubgroup.narrowFiniteConductorExponent`, `GlobalClassFieldTheory.GlobalClassFields.IsDefiningModulus`, `IdeleGroup.ordinaryIdealClassSubgroup`, `IdeleGroup.quotientIdealClassKernelEquiv`, `IdeleGroup.quotientIntegralSupPrincipalEquiv`, `LocalClassFieldTheory.localBlockFamilyHerbrandH0Equiv`, `LocalClassFieldTheory.localBlockFamilyHerbrandHMinusOneEquiv`, `LocalClassFieldTheory.localPlaceBlockHerbrandH0Equiv`, `LocalClassFieldTheory.localPlaceBlockHerbrandHMinusOneEquiv`, `LocalClassFieldTheory.localTensorOrbitHom`, `LocalClassFieldTheory.localizedCompletionGaloisGenerator`, `LocalClassFieldTheory.towerAbsoluteUnits`, `LocalClassFieldTheory.towerAbstractBase`, `RamificationTheory.DiscreteValuationField.ValuedExtension.differentIdealOfFiniteSeparable`, `RayClass.Modulus.congruenceSubgroup`, `RayClass.RayClassGroup`, `RayClass.infiniteSign`, `RayClass.integralIdeleEquiv`, `RayClass.rayClassGroupEquivIdeleQuotient`, `absoluteValueExtensionEquivOfAlgEquiv`, `absoluteValueExtensionOverIntermediate`, `doubleCosetExtensionEquiv`, `extendedFullLogLattice`, `extendedFullLogLatticeEquivProdInt`, `extendedFullLogLatticeMulEquivProdInt`, `fullLogLatticeProdIntIncl`, `fullLogLatticeProdIntProj`, `fullLogLatticeProdIntToExtended`, `fullLogSpaceContinuousEquivHyperplaneProd`, `fullLogSpaceEquivHyperplaneProd`, `fullLogSpaceSplit`, `sUnitFullLogMulHom`, `towerCompositeClassNormQuotientEquiv`.
--
--   **Sources.** They come from these modules of lean/OAI/NumberTheory, in whole or in part: `AlgebraicNumberTheory_Galois_CyclicPrimeSubextension`, `AlgebraicNumberTheory_Idele_ClassGroup_Core`, `AlgebraicNumberTheory_Idele_ClassGroup_Tower`, `AlgebraicNumberTheory_Idele_IdealMap`, `AlgebraicNumberTheory_Ramification_Splitting_NormalClosure`, `AlgebraicNumberTheory_RayClass_FullModulus`, `AlgebraicNumberTheory_RayClass_Topology`, `AlgebraicNumberTheory_SUnit_GaloisAction`, `AlgebraicNumberTheory_SUnit_Herbrand`, `AlgebraicNumberTheory_SUnit_LogLattice`, `GlobalClassFieldTheory_GlobalClassFields_Conductor`, `Kummer_Concrete_LocalUnitKummerUnramified`, `LocalClassFieldTheory_ClassFormation_ArchimedeanNormQuotient`, `LocalClassFieldTheory_ClassFormation_LocalBlocks_Family_H0`, `LocalClassFieldTheory_ClassFormation_LocalBlocks_Family_HMinusOne`, `LocalClassFieldTheory_ClassFormation_LocalBlocks_Induced`, `LocalClassFieldTheory_ClassFormation_LocalBlocks_Tensor`, `LocalClassFieldTheory_ClassFormation_LocalizedCompletionCohomology_Algebra`, `LocalClassFieldTheory_ClassFormation_LocalizedCompletionCohomology_Generator`, `LocalClassFieldTheory_Finite_LocalReciprocity_GeneralTowerNaturality`, `LocalField_NonarchimedeanLocalField_FiniteExtensionCompleteDVF`, `LocalField_NonarchimedeanLocalField_NormQuotient`, `LocalField_NonarchimedeanLocalField_UnramifiedFrobenius`, `LubinTate_FormalModule_RecursiveCorrection`, `Ramification_Different`, `Valuation_DiscreteValuationField_Basic`, `Valuation_DiscreteValuationField_FiniteExtension_Uniqueness`.
--
--   **Imports.** It imports the bundles `OAIQ244Duke025`, `OAIQ244Duke026`, `OAIQ244Duke027`, `OAIQ244Duke028`, `OAIQ244Duke030`, `OAIQ244Duke031` and `OAIQ244Duke033` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ244Duke049`, `OAIQ244Duke050`, `OAIQ244Duke051` and `OAIQ244Duke052`; the statement `OAI.DukePrimeDegree.idealCharacter_kernelLaw_of_even_modulus`.
-- source:
--   OpenAI, Equidistribution of Prime-Degree Torus Packets with Arbitrary Local Type, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 15; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Equidistribution-of-Prime-Degree-Torus-Packets-with-Arbitrary-Local-Type-September-24-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/NumberTheory at commit 7ef5c0c

import Mathlib
import Mathlib.Algebra.Algebra.Basic
import Mathlib.Algebra.Algebra.Pi
import Mathlib.Algebra.Algebra.Tower
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Category.ModuleCat.Basic
import Mathlib.Algebra.CharP.Algebra
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
import Mathlib.Data.Rat.Cast.CharZero
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
import Mathlib.FieldTheory.Normal.Closure
import Mathlib.FieldTheory.Perfect
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
import Mathlib.LinearAlgebra.FreeModule.Finite.Quotient
import Mathlib.LinearAlgebra.FreeModule.IdealQuotient
import Mathlib.LinearAlgebra.Matrix.Gershgorin
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
import Mathlib.NumberTheory.NumberField.Completion.LiesOverInstances
import Mathlib.NumberTheory.NumberField.Completion.Ramification
import Mathlib.NumberTheory.NumberField.InfinitePlace.Ramification
import Mathlib.NumberTheory.NumberField.ProductFormula
import Mathlib.NumberTheory.NumberField.Units.DirichletTheorem
import Mathlib.NumberTheory.NumberField.Units.Regulator
import Mathlib.NumberTheory.Ostrowski
import Mathlib.NumberTheory.Padics.PadicNumbers
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
import Mathlib.RingTheory.DedekindDomain.Different
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
import Mathlib.RingTheory.MvPowerSeries.Expand
import Mathlib.RingTheory.MvPowerSeries.Order
import Mathlib.RingTheory.MvPowerSeries.Substitution
import Mathlib.RingTheory.Nakayama
import Mathlib.RingTheory.Norm.Basic
import Mathlib.RingTheory.Norm.Defs
import Mathlib.RingTheory.Norm.Transitivity
import Mathlib.RingTheory.Polynomial.ContentIdeal
import Mathlib.RingTheory.Polynomial.GaussLemma
import Mathlib.RingTheory.Polynomial.Vieta
import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.RingTheory.PowerSeries.Substitution
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
import Definitions.Def_OAIQ244Duke027
import Definitions.Def_OAIQ244Duke028
import Definitions.Def_OAIQ244Duke030
import Definitions.Def_OAIQ244Duke031
import Definitions.Def_OAIQ244Duke033

section
-- module Solutions.OAIQ244_DUKE.AlgebraicNumberTheory_Idele_ClassGroup_Tower
attribute [-instance] _root_.ClassFormation.DegreeData.FrobeniusFixedFieldTower.extensionNormal _root_.ClassFormation.DegreeData.GaloisSubextension.extensionSubgroup_normalInstance _root_.ClassFormation.FiniteAbstractField.toFiniteResidueAbstractField_extensionNormal _root_.ClassFormation.FiniteCyclicSubextension.instNormalSubtypeMemSubgroupFieldExtensionSubgroupField _root_.ClassFormation.FiniteGaloisSubextension.extensionSubgroup_normalInstance _root_.ClassFormation.FiniteGaloisSubextension.extensionSubgroup_over_intermediate_normalInstance _root_.ClassFormation.FiniteGaloisSubextension.intermediateField_normalInstance _root_.ClassFormation.FiniteIntermediateField.galoisRefinement_normal _root_.ClassFormation.FiniteUnramifiedCyclicExtension.instNormalSubtypeMemSubgroupFieldExtensionSubgroupField _root_.ClassFormation.conjugateExtension_normal _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.KummerTheory.primeCyclotomicBaseFiniteDimensional _root_.LocalClassFieldTheory.extensionSubgroupBase_normal _root_.LocalClassFieldTheory.finiteGaloisExtensionSubgroupOfEmbedding_normal _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionResidueField.instField _root_.RamificationTheory.HilbertRamification.ValuationSubring.inertiaGroup_normal _root_.RamificationTheory.HilbertRamification.ValuationSubring.ramificationGroupInInertiaAut_normal _root_.RamificationTheory.HilbertRamification.ValuationSubring.selectedResidueField.instAlgebra _root_.RelativeIdeleGroup.principalQuotientAction _root_.ValuationTheory.DiscreteValuationField.DVF.residueField.field _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.CyclicCohomology.binaryCoefficientFamilyCommGroup _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteIdeleGroupIsTopologicalGroup _root_.finiteLocalUnitsOpen _root_.ideleGroupIsTopologicalGroup
attribute [-simp] _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.FiniteIdeleGroup.absoluteNorm_apply _root_.FiniteIdeleGroup.mem_integralSubgroup_iff _root_.FiniteIdeleGroup.mem_supportedAt_iff _root_.FiniteIdeleGroup.valuationVectorAdd_apply _root_.FiniteIdeleGroup.valuationVector_apply _root_.FiniteIdeleGroup.valuationVector_valuationVectorSection _root_.IdeleClassGroup.absoluteNorm_mk _root_.IdeleClassGroup.mk_mem_normOneSubgroup_iff _root_.IdeleGroup.absoluteNorm_apply _root_.IdeleGroup.absoluteNorm_principalIdele _root_.IdeleGroup.finiteComponentContinuous_apply _root_.IdeleGroup.fractionalIdeal_principalIdele _root_.IdeleGroup.idealClass_principalIdele _root_.IdeleGroup.infiniteComponentContinuous_apply _root_.IdeleGroup.mem_supportedAt_iff _root_.InfiniteIdeleGroup.archimedeanNorm_apply _root_.InfiniteIdeleGroup.logNorm_mul _root_.IsDiscreteValuationRing.addVal_ringEquiv _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.LocalFieldTheory.residueField_algebraMap_residue _root_.OAI.PrimeDegreePackets.ThetaConstruction.schwartzCM_apply _root_.RayClass.Modulus.mem_ideleCongruenceSubgroup_iff _root_.RayClass.Modulus.mem_infiniteCongruenceSubgroup_iff _root_.RayClass.Modulus.mem_infiniteCongruenceSubgroup_iff_local _root_.RayClass.mem_finiteCongruenceSubgroup_iff _root_.RayClass.mem_narrowInfiniteCongruenceSubgroup_iff _root_.RayClass.quotientRaySubgroupEquivIdealRayClassGroup_mk _root_.RelativeIdeleGroup.Cohomology.baseIdeleClassEquivFixed_coe _root_.RelativeIdeleGroup.Cohomology.baseIdeleClassToFixed_coe _root_.RelativeIdeleGroup.Cohomology.ideleClassNorm_mk _root_.RelativeIdeleGroup.Cohomology.ideleClass_smul_mk _root_.RelativeIdeleGroup.Cohomology.relativeIdele_smul_def _root_.RelativeIdeleGroup.finiteComponent_coe _root_.RelativeIdeleGroup.finiteComponent_inclusion _root_.RelativeIdeleGroup.finiteComponent_norm _root_.RelativeIdeleGroup.finiteComponent_principalIdele _root_.RelativeIdeleGroup.infiniteComponent_coe _root_.RelativeIdeleGroup.infiniteComponent_inclusion _root_.RelativeIdeleGroup.infiniteComponent_norm _root_.RelativeIdeleGroup.infiniteComponent_principalIdele _root_.RelativeIdeleGroup.scalarConjugation_baseAdele_apply _root_.RelativeIdeleGroup.smul_class_mk _root_.finiteIdeleOfSPlaceFactors_apply_mem _root_.finiteIdeleOfSPlaceFactors_apply_notMem _root_.ideleSupportedAtEquivSPlaceFactors_infinite _root_.ideleSupportedAtEquivSPlaceFactors_inside _root_.ideleSupportedAtEquivSPlaceFactors_outside_coe _root_.infinitePlace_mult_smul _root_.mem_relativeAdeleCoefficientSupport_iff _root_.mem_relativeIdeleCoefficientSupport_iff _root_.pushoutNormQuotientMap_mk _root_.pushoutNormQuotientNormBack_mk _root_.pushoutTowerAdeleInclusion_tmul _root_.pushoutTowerClassInclusion_mk _root_.pushoutTowerIdeleInclusion_principalIdele _root_.relativeAdeleFiniteComponent_tmul _root_.relativeAdeleInfiniteComponent_tmul
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

/-!
# Idele-class norms in a field tower

For a tower `K ⊂ M ⊂ L`, keep the bottom field `K` fixed and write

`𝔸_M = 𝔸_K ⊗[K] M`,
`𝔸_L = (𝔸_K ⊗[K] M) ⊗[M] L`.

This gives an actual norm `C_L → C_M` whose composite with
`C_M → C_K` is the tower norm.  The resulting three concrete norm
quotients form a natural right-exact sequence.
-/

open scoped NumberField TensorProduct
open NumberField

noncomputable section

universe u

variable
    (K M L : Type u)
    [Field K] [NumberField K]
    [Field M] [NumberField M]
    [Field L] [NumberField L]
    [Algebra K M] [Algebra M L] [Algebra K L]
    [IsScalarTower K M L]
    [FiniteDimensional K M] [FiniteDimensional M L]

section NormQuotientSequence

attribute [local instance] instIsMulCommutativeTowerRelativeIdeleGroup
attribute [local instance] instIsMulCommutativeClassGroup
attribute [local instance] instIsMulCommutativeIdeleClassGroup
omit [NumberField M] in
/-- The tower composite norm and the ordinary one-step norm have the
same subgroup of norms in `C_K`. -/
theorem towerCompositeClassNorm_range_eq :
    (towerCompositeClassNorm K M L).range =
      (RelativeIdeleGroup.classNorm K L).range := by
  ext c
  constructor
  · rintro ⟨d, rfl⟩
    exact
      ⟨TowerRelativeIdeleGroup.classGroupEquiv K M L d,
        (towerCompositeClassNorm_eq_ideleClassNorm
          K M L d).symm⟩
  · rintro ⟨d, rfl⟩
    refine
      ⟨(TowerRelativeIdeleGroup.classGroupEquiv K M L).symm d,
        ?_⟩
    rw [towerCompositeClassNorm_eq_ideleClassNorm,
      MulEquiv.apply_symm_apply]

/-- Canonical identification of the tower composite norm quotient with
the existing one-step norm quotient `C_K / N_{L/K}C_L`. -/
def towerCompositeClassNormQuotientEquiv :
    TowerCompositeClassNormQuotient K M L ≃*
      RelativeIdeleGroup.ClassNormQuotient K L :=
  QuotientGroup.congr
    (towerCompositeClassNorm K M L).range
    (RelativeIdeleGroup.classNorm K L).range
    (MulEquiv.refl (IdeleClassGroup K))
    (by
      simpa using towerCompositeClassNorm_range_eq K M L)

omit [NumberField M] in
/-- The tower cardinal bound in the standard one-step presentation:

`#(C_K / N_{L/K}C_L) ≤
  #(C_M / N_{L/M}C_L) · #(C_K / N_{M/K}C_M)`.
-/
theorem ideleClassNormQuotient_card_le_mul
    [Finite (IntermediateClassNormQuotient K M L)]
    [Finite (RelativeIdeleGroup.ClassNormQuotient K M)] :
    Nat.card (RelativeIdeleGroup.ClassNormQuotient K L) ≤
      Nat.card (IntermediateClassNormQuotient K M L) *
        Nat.card (RelativeIdeleGroup.ClassNormQuotient K M) := by
  calc
    Nat.card (RelativeIdeleGroup.ClassNormQuotient K L) =
        Nat.card (TowerCompositeClassNormQuotient K M L) :=
      Nat.card_congr
        (towerCompositeClassNormQuotientEquiv K M L).symm.toEquiv
    _ ≤ Nat.card (IntermediateClassNormQuotient K M L) *
          Nat.card (RelativeIdeleGroup.ClassNormQuotient K M) :=
      towerCompositeClassNormQuotient_card_le_mul K M L

end NormQuotientSequence
end
end

section
-- module Solutions.OAIQ244_DUKE.AlgebraicNumberTheory_Idele_IdealMap
attribute [-instance] _root_.ClassFormation.DegreeData.FrobeniusFixedFieldTower.extensionNormal _root_.ClassFormation.DegreeData.GaloisSubextension.extensionSubgroup_normalInstance _root_.ClassFormation.FiniteAbstractField.toFiniteResidueAbstractField_extensionNormal _root_.ClassFormation.FiniteCyclicSubextension.instNormalSubtypeMemSubgroupFieldExtensionSubgroupField _root_.ClassFormation.FiniteGaloisSubextension.extensionSubgroup_normalInstance _root_.ClassFormation.FiniteGaloisSubextension.extensionSubgroup_over_intermediate_normalInstance _root_.ClassFormation.FiniteGaloisSubextension.intermediateField_normalInstance _root_.ClassFormation.FiniteIntermediateField.galoisRefinement_normal _root_.ClassFormation.FiniteUnramifiedCyclicExtension.instNormalSubtypeMemSubgroupFieldExtensionSubgroupField _root_.ClassFormation.conjugateExtension_normal _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalClassFieldTheory.extensionSubgroupBase_normal _root_.LocalClassFieldTheory.finiteGaloisExtensionSubgroupOfEmbedding_normal _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionResidueField.instField _root_.RamificationTheory.HilbertRamification.ValuationSubring.inertiaGroup_normal _root_.RamificationTheory.HilbertRamification.ValuationSubring.ramificationGroupInInertiaAut_normal _root_.RamificationTheory.HilbertRamification.ValuationSubring.selectedResidueField.instAlgebra _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.residueField.field _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.isDomain _root_.CyclicCohomology.binaryCoefficientFamilyCommGroup _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteIdeleGroupIsTopologicalGroup _root_.finiteLocalUnitsOpen _root_.ideleGroupIsTopologicalGroup _root_.relativeAdeleRingIntermediateAlgebra _root_.relativeAdeleRingTopIntermediateAlgebra
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

/-!
# The ideal attached to an idele

This file formalizes the ideal map from ideles. Its construction
is explicit: local discrete valuations form a finitely supported integer
vector, and unique factorization of fractional ideals identifies that vector
with a nonzero fractional ideal.  We prove both stages surjective and identify
the kernel with the ideles integral at every finite place.
-/

open scoped NumberField RestrictedProduct WithZero
open NumberField IsDedekindDomain

noncomputable section


variable {K : Type*} [Field K] [NumberField K]

namespace IdeleGroup

/-- A quotient form of the ideal-class map. The following results identify
this kernel with `I_K^{S∞} Kˣ`. -/
def quotientIdealClassKernelEquiv :
    IdeleGroup K ⧸ (idealClass (K := K)).ker ≃*
      ClassGroup (𝓞 K) :=
  QuotientGroup.quotientKerEquivOfSurjective
    idealClass idealClass_surjective

end IdeleGroup
end
end

section
-- module Solutions.OAIQ244_DUKE.AlgebraicNumberTheory_Idele_ClassGroup_Core
attribute [-instance] _root_.ClassFormation.DegreeData.FrobeniusFixedFieldTower.extensionNormal _root_.ClassFormation.DegreeData.GaloisSubextension.extensionSubgroup_normalInstance _root_.ClassFormation.FiniteAbstractField.toFiniteResidueAbstractField_extensionNormal _root_.ClassFormation.FiniteCyclicSubextension.instNormalSubtypeMemSubgroupFieldExtensionSubgroupField _root_.ClassFormation.FiniteGaloisSubextension.extensionSubgroup_normalInstance _root_.ClassFormation.FiniteGaloisSubextension.extensionSubgroup_over_intermediate_normalInstance _root_.ClassFormation.FiniteGaloisSubextension.intermediateField_normalInstance _root_.ClassFormation.FiniteIntermediateField.galoisRefinement_normal _root_.ClassFormation.FiniteUnramifiedCyclicExtension.instNormalSubtypeMemSubgroupFieldExtensionSubgroupField _root_.ClassFormation.conjugateExtension_normal _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalClassFieldTheory.extensionSubgroupBase_normal _root_.LocalClassFieldTheory.finiteGaloisExtensionSubgroupOfEmbedding_normal _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionResidueField.instField _root_.RamificationTheory.HilbertRamification.ValuationSubring.inertiaGroup_normal _root_.RamificationTheory.HilbertRamification.ValuationSubring.ramificationGroupInInertiaAut_normal _root_.RamificationTheory.HilbertRamification.ValuationSubring.selectedResidueField.instAlgebra _root_.ValuationTheory.DiscreteValuationField.DVF.residueField.field _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.isDomain _root_.CyclicCohomology.binaryCoefficientFamilyCommGroup _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteIdeleGroupIsTopologicalGroup _root_.finiteLocalUnitsOpen _root_.ideleGroupIsTopologicalGroup
attribute [-simp] _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.FiniteIdeleGroup.absoluteNorm_apply _root_.FiniteIdeleGroup.mem_supportedAt_iff _root_.FractionalIdealGroup.absoluteNorm_prime _root_.IdeleClassGroup.absoluteNorm_mk _root_.IdeleClassGroup.mk_mem_normOneSubgroup_iff _root_.IdeleGroup.absoluteNorm_apply _root_.IdeleGroup.absoluteNorm_principalIdele _root_.IdeleGroup.finiteComponentContinuous_apply _root_.IdeleGroup.infiniteComponentContinuous_apply _root_.IdeleGroup.mem_supportedAt_iff _root_.InfiniteIdeleGroup.archimedeanNorm_apply _root_.InfiniteIdeleGroup.logNorm_mul _root_.IsDiscreteValuationRing.addVal_ringEquiv _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.OAI.PrimeDegreePackets.ThetaConstruction.schwartzCM_apply _root_.RayClass.Modulus.mem_ideleCongruenceSubgroup_iff _root_.RayClass.Modulus.mem_infiniteCongruenceSubgroup_iff _root_.RayClass.Modulus.mem_infiniteCongruenceSubgroup_iff_local _root_.RayClass.mem_finiteCongruenceSubgroup_iff _root_.RayClass.mem_narrowInfiniteCongruenceSubgroup_iff _root_.RayClass.mem_primeToModulusIdeals_iff _root_.RayClass.primeToModulusIdeal_coe _root_.RayClass.quotientRaySubgroupEquivIdealRayClassGroup_mk _root_.finiteIdeleOfSPlaceFactors_apply_mem _root_.finiteIdeleOfSPlaceFactors_apply_notMem _root_.ideleSupportedAtEquivSPlaceFactors_infinite _root_.ideleSupportedAtEquivSPlaceFactors_inside _root_.ideleSupportedAtEquivSPlaceFactors_outside_coe _root_.infinitePlace_mult_smul
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

/-!
# The ordinary ideal class group as an idele quotient

This file proves that quotienting the idele group by the
ideles integral at every finite place and by the principal ideles gives the
ordinary ideal class group.
-/

open scoped NumberField RestrictedProduct WithZero
open NumberField IsDedekindDomain

noncomputable section


variable {K : Type*} [Field K] [NumberField K]

namespace IdeleGroup

/-- The subgroup `I_K^{S∞} Kˣ` defining the ordinary ideal class quotient. -/
def ordinaryIdealClassSubgroup : Subgroup (IdeleGroup K) :=
  integralAtFinitePlaces (K := K) ⊔ principalSubgroup K

/-- The kernel of the map from ideles to the ordinary ideal class group is
exactly `I_K^{S∞} Kˣ`. -/
theorem ordinaryIdealClassSubgroup_eq_ker :
    ordinaryIdealClassSubgroup (K := K) =
      (idealClass (K := K)).ker := by
  ext a
  constructor
  · intro ha
    rw [ordinaryIdealClassSubgroup, Subgroup.mem_sup] at ha
    obtain ⟨u, hu, p, hp, rfl⟩ := ha
    obtain ⟨x, rfl⟩ := hp
    have hu' : fractionalIdeal u = 1 := by
      rw [← MonoidHom.mem_ker,
        fractionalIdeal_ker]
      exact hu
    change idealClass (u * principalIdele K x) = 1
    rw [map_mul, idealClass_principalIdele, mul_one]
    change ClassGroup.mk K (fractionalIdeal u) = 1
    rw [hu', map_one]
  · intro ha
    change ClassGroup.mk K (fractionalIdeal a) = 1 at ha
    rw [classGroup_mk_eq_one_iff] at ha
    obtain ⟨x, hx⟩ := ha
    let u : IdeleGroup K := a * (principalIdele K x)⁻¹
    have hu : u ∈ integralAtFinitePlaces (K := K) := by
      rw [← fractionalIdeal_ker, MonoidHom.mem_ker]
      change fractionalIdeal
          (a * (principalIdele K x)⁻¹) = 1
      rw [map_mul, map_inv, fractionalIdeal_principalIdele,
        ← hx, mul_inv_cancel]
    rw [ordinaryIdealClassSubgroup, Subgroup.mem_sup]
    refine ⟨u, hu, principalIdele K x, ⟨x, rfl⟩, ?_⟩
    dsimp [u]
    group

/-- The ordinary ideal class group is the quotient of
the ideles by the ideles integral at all finite places and the principal
ideles. -/
def quotientIntegralSupPrincipalEquiv :
    IdeleGroup K ⧸
        (integralAtFinitePlaces (K := K) ⊔ principalSubgroup K) ≃*
      ClassGroup (𝓞 K) := by
  let h : integralAtFinitePlaces (K := K) ⊔ principalSubgroup K =
      (idealClass (K := K)).ker := by
    simpa [ordinaryIdealClassSubgroup] using
      ordinaryIdealClassSubgroup_eq_ker (K := K)
  exact
    (QuotientGroup.congr
      (integralAtFinitePlaces (K := K) ⊔ principalSubgroup K)
      (idealClass (K := K)).ker (MulEquiv.refl (IdeleGroup K))
      (by simpa using h)).trans
        (quotientIdealClassKernelEquiv (K := K))

end IdeleGroup
end
end

section
-- module Solutions.OAIQ244_DUKE.AlgebraicNumberTheory_RayClass_FullModulus
attribute [-instance] _root_.ClassFormation.DegreeData.FrobeniusFixedFieldTower.extensionNormal _root_.ClassFormation.DegreeData.GaloisSubextension.extensionSubgroup_normalInstance _root_.ClassFormation.FiniteAbstractField.toFiniteResidueAbstractField_extensionNormal _root_.ClassFormation.FiniteCyclicSubextension.instNormalSubtypeMemSubgroupFieldExtensionSubgroupField _root_.ClassFormation.FiniteGaloisSubextension.extensionSubgroup_normalInstance _root_.ClassFormation.FiniteGaloisSubextension.extensionSubgroup_over_intermediate_normalInstance _root_.ClassFormation.FiniteGaloisSubextension.intermediateField_normalInstance _root_.ClassFormation.FiniteIntermediateField.galoisRefinement_normal _root_.ClassFormation.FiniteUnramifiedCyclicExtension.instNormalSubtypeMemSubgroupFieldExtensionSubgroupField _root_.ClassFormation.conjugateExtension_normal _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalClassFieldTheory.extensionSubgroupBase_normal _root_.LocalClassFieldTheory.finiteGaloisExtensionSubgroupOfEmbedding_normal _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionResidueField.instField _root_.RamificationTheory.HilbertRamification.ValuationSubring.inertiaGroup_normal _root_.RamificationTheory.HilbertRamification.ValuationSubring.ramificationGroupInInertiaAut_normal _root_.RamificationTheory.HilbertRamification.ValuationSubring.selectedResidueField.instAlgebra _root_.ValuationTheory.DiscreteValuationField.DVF.residueField.field _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.CyclicCohomology.binaryCoefficientFamilyCommGroup _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

/-!
# Ray moduli with selected real places

A ray modulus consists of a finite modulus together with the real places at
which positivity is imposed.  This file defines the corresponding idèle and
idèle-class congruence subgroups without fixing an archimedean convention.
-/

open scoped Classical NumberField
open NumberField IsDedekindDomain

noncomputable section

variable {K : Type*} [Field K] [NumberField K]

namespace RayClass

namespace Modulus

/-- Selecting every real place recovers the narrow infinite congruence
subgroup. -/
theorem infiniteCongruenceSubgroup_narrowOfFinite (f : FiniteModulus K) :
    (narrowOfFinite f).infiniteCongruenceSubgroup =
      narrowInfiniteCongruenceSubgroup (K := K) := by
  ext a
  rw [mem_infiniteCongruenceSubgroup_iff,
    mem_narrowInfiniteCongruenceSubgroup_iff]
  simp only [infinitePart_narrowOfFinite, Finset.mem_univ, true_implies]
  constructor
  · intro ha w
    by_cases hw : w.IsReal
    · exact ha ⟨w, hw⟩
    · rw [mem_infinitePositiveSubgroup_iff]
      exact fun hreal => (hw hreal).elim
  · intro ha v
    exact ha v.1

/-- Selecting every real place recovers the narrow idèle congruence subgroup. -/
theorem ideleCongruenceSubgroup_narrowOfFinite (f : FiniteModulus K) :
    (narrowOfFinite f).ideleCongruenceSubgroup =
      (narrowInfiniteCongruenceSubgroup (K := K)).prod
        (finiteCongruenceSubgroup f) := by
  simp only [ideleCongruenceSubgroup, finitePart_narrowOfFinite]
  rw [infiniteCongruenceSubgroup_narrowOfFinite]

/-- The ray congruence subgroup of the idèle class group attached to a full
modulus. -/
def congruenceSubgroup (m : Modulus K) :
    Subgroup (IdeleClassGroup K) :=
  Subgroup.map
    (QuotientGroup.mk' (IdeleGroup.principalSubgroup K))
    (m.ideleCongruenceSubgroup ⊔ IdeleGroup.principalSubgroup K)

/-- The full ray congruence subgroup is normal in the idèle class group. -/
instance congruenceSubgroup_normal (m : Modulus K) :
    m.congruenceSubgroup.Normal := by
  let : IsMulCommutative (IdeleClassGroup K) := ⟨⟨fun a b => mul_comm a b⟩⟩
  exact Subgroup.normal_of_isMulCommutative _

end Modulus

/-- The ray class group attached to a full modulus. -/
abbrev RayClassGroup (m : Modulus K) :=
  IdeleClassGroup K ⧸ m.congruenceSubgroup

/-- The ray class group is equivalently the idèle group modulo the product
of its congruence subgroup with the principal idèles. -/
def rayClassGroupEquivIdeleQuotient (m : Modulus K) :
    RayClassGroup m ≃*
      IdeleGroup K ⧸
        (m.ideleCongruenceSubgroup ⊔ IdeleGroup.principalSubgroup K) :=
  QuotientGroup.quotientQuotientEquivQuotient
    (IdeleGroup.principalSubgroup K)
    (m.ideleCongruenceSubgroup ⊔ IdeleGroup.principalSubgroup K)
    le_sup_right

end RayClass
end
end

section
-- module Solutions.OAIQ244_DUKE.AlgebraicNumberTheory_RayClass_Topology
attribute [-instance] _root_.ClassFormation.DegreeData.FrobeniusFixedFieldTower.extensionNormal _root_.ClassFormation.DegreeData.GaloisSubextension.extensionSubgroup_normalInstance _root_.ClassFormation.FiniteAbstractField.toFiniteResidueAbstractField_extensionNormal _root_.ClassFormation.FiniteCyclicSubextension.instNormalSubtypeMemSubgroupFieldExtensionSubgroupField _root_.ClassFormation.FiniteGaloisSubextension.extensionSubgroup_normalInstance _root_.ClassFormation.FiniteGaloisSubextension.extensionSubgroup_over_intermediate_normalInstance _root_.ClassFormation.FiniteGaloisSubextension.intermediateField_normalInstance _root_.ClassFormation.FiniteIntermediateField.galoisRefinement_normal _root_.ClassFormation.FiniteUnramifiedCyclicExtension.instNormalSubtypeMemSubgroupFieldExtensionSubgroupField _root_.ClassFormation.conjugateExtension_normal _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalClassFieldTheory.extensionSubgroupBase_normal _root_.LocalClassFieldTheory.finiteGaloisExtensionSubgroupOfEmbedding_normal _root_.LocalFieldTheory.DiscreteValuationField.finite_nsmulAddKernel_padicInt_pi _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_multiplicative_nthPowerKernel _root_.LocalFieldTheory.finite_nsmulAddKernel_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.LubinTate.Valuations.exponentialValuationSubringIsLocalRing _root_.LubinTate.compatibleGroupFamiliesGroup _root_.OAI.PrimeDegreePackets.boundedRealFields_finite _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionFixedSubring.instIsLocalRing _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionResidueField.instField _root_.RamificationTheory.HilbertRamification.ValuationSubring.inertiaGroup_normal _root_.RamificationTheory.HilbertRamification.ValuationSubring.ramificationGroupInInertiaAut_normal _root_.RamificationTheory.HilbertRamification.ValuationSubring.selectedResidueField.instAlgebra _root_.ValuationTheory.DiscreteValuationField.DVF.maximalIdealPowSuccQuotModule _root_.ValuationTheory.DiscreteValuationField.DVF.residueField.field _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.isDomain _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.isLocalRing _root_.CyclicCohomology.binaryCoefficientFamilyCommGroup _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

/-!
# The congruence topology on the idele class group

The local higher-unit groups are open,
the ray congruence subgroups are open (and hence closed) of finite index, and
the congruence subgroups are cofinal among the closed finite-index subgroups
of the idele class group.
-/

open scoped Classical NumberField RestrictedProduct WithZero
open NumberField IsDedekindDomain
open Topology

noncomputable section


variable {K : Type*} [Field K] [NumberField K]

namespace RayClass

/-- Local higher-unit groups are contravariant in their depth. -/
theorem localHigherUnitGroup_antitone
    (v : HeightOneSpectrum (𝓞 K))
    {m n : ℕ} (hmn : m ≤ n) :
    localHigherUnitGroup v n ≤ localHigherUnitGroup v m := by
  intro x hx
  rw [mem_localHigherUnitGroup_iff] at hx ⊢
  obtain ⟨y, rfl, hy⟩ := hx
  refine ⟨y, rfl, ?_⟩
  rw [localHigherUnitMap_eq_one_iff] at hy ⊢
  exact Ideal.pow_le_pow_right hmn hy

/-- The local higher-unit group lies in the local integral-unit group. -/
theorem localHigherUnitGroup_le_finiteLocalUnits
    (v : HeightOneSpectrum (𝓞 K)) (n : ℕ) :
    localHigherUnitGroup v n ≤
      (v.adicCompletionIntegers K).units := by
  intro x hx
  rw [mem_localHigherUnitGroup_iff] at hx
  obtain ⟨y, rfl, _⟩ := hx
  exact y.property

/-- The tuple of signs of an infinite idele at all real places. -/
def infiniteSign :
    InfiniteIdeleGroup K →*
      ((v : {w : InfinitePlace K // w.IsReal}) → SignTypeˣ) :=
  MonoidHom.pi fun v ↦
    (realPlaceSign v).comp (InfiniteIdeleGroup.component v.1)

omit [NumberField K] in
/-- Positivity at all real places is exactly the kernel of the infinite sign
map. -/
theorem infiniteSign_ker_eq_narrowInfiniteCongruenceSubgroup :
    (infiniteSign (K := K)).ker =
      narrowInfiniteCongruenceSubgroup (K := K) := by
  ext a
  constructor
  · intro ha
    have ha' : infiniteSign (K := K) a = 1 :=
      MonoidHom.mem_ker.mp ha
    apply (mem_narrowInfiniteCongruenceSubgroup_iff a).2
    intro v
    apply (mem_infinitePositiveSubgroup_iff v
      (ContinuousMulEquiv.piUnits a v)).2
    intro hv
    have hsign :=
      congrArg Units.val (congrFun ha' ⟨v, hv⟩)
    change
      SignType.sign
          (InfinitePlace.Completion.extensionEmbeddingOfIsReal hv
            ((InfiniteIdeleGroup.component v a :
              v.Completionˣ) : v.Completion)) =
        1 at hsign
    exact sign_eq_one_iff.mp hsign
  · intro ha
    apply MonoidHom.mem_ker.mpr
    funext v
    apply Units.ext
    change
      SignType.sign
          (InfinitePlace.Completion.extensionEmbeddingOfIsReal v.2
            ((InfiniteIdeleGroup.component v.1 a :
              v.1.Completionˣ) : v.1.Completion)) =
        1
    rw [sign_eq_one_iff]
    exact
      ((mem_narrowInfiniteCongruenceSubgroup_iff a).1 ha v.1) v.2

/-- The infinite positivity subgroup has finite index (its quotient is
detected by the finitely many real signs). -/
instance narrowInfiniteCongruenceSubgroupFiniteIndex :
    (narrowInfiniteCongruenceSubgroup (K := K)).FiniteIndex := by
  rw [← infiniteSign_ker_eq_narrowInfiniteCongruenceSubgroup (K := K)]
  exact Subgroup.finiteIndex_ker (infiniteSign (K := K))

/-- Every selected-real-place congruence subgroup has finite index, because
it contains the narrow positivity subgroup. -/
instance Modulus.infiniteCongruenceSubgroupFiniteIndex
    (m : Modulus K) :
    m.infiniteCongruenceSubgroup.FiniteIndex := by
  apply Subgroup.finiteIndex_of_le
    (H := narrowInfiniteCongruenceSubgroup (K := K))
    (K := m.infiniteCongruenceSubgroup)
  intro a ha
  rw [Modulus.mem_infiniteCongruenceSubgroup_iff]
  intro v _
  exact (mem_narrowInfiniteCongruenceSubgroup_iff a).1 ha v.1

/-- The finite idele congruence subgroup lies in the everywhere-integral
finite ideles. -/
theorem finiteCongruenceSubgroup_le_integralSubgroup
    (m : FiniteModulus K) :
    finiteCongruenceSubgroup m ≤
      FiniteIdeleGroup.integralSubgroup (K := K) := by
  intro a ha v
  exact localHigherUnitGroup_le_finiteLocalUnits v (m v) (ha v)

/-- Ideles integral at all finite places split as the infinite ideles times
the compact group of integral finite ideles. -/
def integralIdeleEquiv :
    IdeleGroup.integralAtFinitePlaces (K := K) ≃*
      InfiniteIdeleGroup K ×
        FiniteIdeleGroup.integralSubgroup (K := K) where
  toFun a := (a.1.1, ⟨a.1.2, a.2⟩)
  invFun a := ⟨(a.1, a.2.1), a.2.2⟩
  left_inv a := by
    apply Subtype.ext
    rfl
  right_inv a := rfl
  map_mul' a b := rfl

/-- Under `integralIdeleEquiv`, the idele congruence subgroup maps to the
product of its infinite and finite congruence factors. -/
theorem map_ideleCongruenceSubgroup_subgroupOf_integral (m : Modulus K) :
    ((m.ideleCongruenceSubgroup).subgroupOf
      (IdeleGroup.integralAtFinitePlaces (K := K))).map
        (integralIdeleEquiv (K := K)).toMonoidHom =
      m.infiniteCongruenceSubgroup.prod
        ((finiteCongruenceSubgroup m.finitePart).subgroupOf
          (FiniteIdeleGroup.integralSubgroup (K := K))) := by
  ext a
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨hx.1, hx.2⟩
  · rintro ⟨ha, hb⟩
    refine ⟨⟨(a.1, a.2.1), a.2.2⟩, ⟨ha, hb⟩, rfl⟩

/-- The subgroup defining the ordinary ideal class group has finite index. -/
instance ordinaryIdealClassSubgroupFiniteIndex :
    (IdeleGroup.integralAtFinitePlaces (K := K) ⊔
      IdeleGroup.principalSubgroup K).FiniteIndex := by
  let : Finite
      (IdeleGroup K ⧸
        (IdeleGroup.integralAtFinitePlaces (K := K) ⊔
          IdeleGroup.principalSubgroup K)) :=
    Finite.of_equiv (ClassGroup (𝓞 K))
    (IdeleGroup.quotientIntegralSupPrincipalEquiv
      (K := K)).symm.toEquiv
  exact Subgroup.finiteIndex_of_finite_quotient

end RayClass
end
end

section
-- module Solutions.OAIQ244_DUKE.LocalField_NonarchimedeanLocalField_NormQuotient
attribute [-instance] _root_.ClassFormation.DegreeData.FrobeniusFixedFieldTower.extensionNormal _root_.ClassFormation.DegreeData.GaloisSubextension.extensionSubgroup_normalInstance _root_.ClassFormation.FiniteAbstractField.toFiniteResidueAbstractField_extensionNormal _root_.ClassFormation.FiniteCyclicSubextension.instNormalSubtypeMemSubgroupFieldExtensionSubgroupField _root_.ClassFormation.FiniteGaloisSubextension.extensionSubgroup_normalInstance _root_.ClassFormation.FiniteGaloisSubextension.extensionSubgroup_over_intermediate_normalInstance _root_.ClassFormation.FiniteGaloisSubextension.intermediateField_normalInstance _root_.ClassFormation.FiniteIntermediateField.galoisRefinement_normal _root_.ClassFormation.FiniteUnramifiedCyclicExtension.instNormalSubtypeMemSubgroupFieldExtensionSubgroupField _root_.ClassFormation.conjugateExtension_normal _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalClassFieldTheory.extensionSubgroupBase_normal _root_.LocalClassFieldTheory.finiteGaloisExtensionSubgroupOfEmbedding_normal _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.RamificationTheory.HilbertRamification.ValuationSubring.inertiaGroup_normal _root_.RamificationTheory.HilbertRamification.ValuationSubring.ramificationGroupInInertiaAut_normal _root_.RayClass.Modulus.congruenceSubgroup_normal _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.CyclicCohomology.binaryCoefficientFamilyCommGroup _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen
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

/-- Eliminate a norm-quotient class through the canonical quotient map,
without exposing the quotient representation to clients. -/
protected theorem NormQuotient.inductionOn {K L : Type u} [Field K] [Field L]
    [Algebra K L] {motive : NormQuotient K L → Prop}
    (q : NormQuotient K L)
    (h : ∀ x : Kˣ, motive (normClass K L x)) : motive q := by
  change motive (show Kˣ ⧸ localNormSubgroup K L from q)
  refine QuotientGroup.induction_on q ?_
  intro x
  exact h x

/-- The quotient class of any extension-unit norm is the identity norm class. -/
theorem mk_normUnits_eq_one (K L : Type u) [Field K] [Field L] [Algebra K L] (x : Lˣ) :
    normClass K L (normUnits K L x) = 1 := by
  exact (QuotientGroup.eq_one_iff (normUnits K L x)).2 ⟨x, rfl⟩

/-- Two units have the same norm class exactly when their quotient is a local norm. -/
theorem normClass_eq_iff_div_mem (K L : Type u) [Field K] [Field L]
    [Algebra K L] (x y : Kˣ) :
    normClass K L x = normClass K L y ↔
      x / y ∈ localNormSubgroup K L :=
  by
    let N := localNormSubgroup K L
    exact QuotientGroup.eq_iff_div_mem (N := N)

/-- Two norm classes agree exactly when their representatives differ by a unit norm. -/
theorem normClass_eq_iff_exists_norm_div (K L : Type u)
    [Field K] [Field L] [Algebra K L] (x y : Kˣ) :
    normClass K L x = normClass K L y ↔
      ∃ z : Lˣ, x / y = normUnits K L z := by
  rw [normClass_eq_iff_div_mem K L x y]
  change x / y ∈ (normUnits K L).range ↔ _
  rw [MonoidHom.mem_range]
  constructor
  · rintro ⟨z, hz⟩
    exact ⟨z, hz.symm⟩
  · rintro ⟨z, hz⟩
    exact ⟨z, hz.symm⟩

/-! ### Surjectivity and equality refinements for norm quotients -/

end
end LocalFieldTheory
end

section
-- module Solutions.OAIQ244_DUKE.Valuation_DiscreteValuationField_Basic
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.DiscreteValuationField.Examples.Qp.padicDVRValuation_isRankOneDiscrete _root_.LocalFieldTheory.DiscreteValuationField.LocalField.residueField_charP_residueCharacteristic _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.RamificationTheory.HilbertRamification.Higher.lowerRamificationGroup.instNormal _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionFixedMaximalIdeal.instIsMaximal _root_.RamificationTheory.HilbertRamification.ValuationSubring.selectedResidueField.instAlgebra _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.RamificationTheory.HilbertRamification.CompleteDVF.decompositionGroupMulSemiringAction _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen _root_.relativeAdeleRingIntermediateAlgebra _root_.relativeAdeleRingTopIntermediateAlgebra
attribute [-simp] _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.IsDiscreteValuationRing.addVal_ringEquiv _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.coe_valuationSubringUnitsToFieldUnits_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.multiplicativeIntegerValuationOfUniformizer_val _root_.LocalFieldTheory.localIntegerValuationSubringEquiv_apply_coe _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.LocalFieldTheory.residueField_algebraMap_residue _root_.LubinTate.SameUniformizer.constantCoeff_inVariable _root_.OAI.PrimeDegreePackets.ThetaConstruction.schwartzCM_apply _root_.RamificationTheory.HilbertRamification.Higher.dvfValuationSubringUnitAut_apply _root_.RamificationTheory.HilbertRamification.Higher.lowerRamificationGroup_neg_one _root_.RamificationTheory.HilbertRamification.Higher.mem_dvfHigherPrincipalUnitGroup_iff _root_.RamificationTheory.HilbertRamification.Higher.mem_lowerRamificationGroup_iff _root_.RamificationTheory.HilbertRamification.Higher.mem_valuationSubringDisplacementSubalgebraOfUniqueExtension_iff _root_.RamificationTheory.HilbertRamification.Higher.realRamificationIdeal_nat _root_.RamificationTheory.HilbertRamification.Higher.realRamificationIdeal_neg_one _root_.RamificationTheory.HilbertRamification.Higher.valuationSubringAutOfUniqueExtension_apply_coe _root_.RamificationTheory.HilbertRamification.Higher.valuationSubringAutOfUniqueExtension_apply_inv_apply _root_.RamificationTheory.HilbertRamification.Higher.valuationSubringAutOfUniqueExtension_mul_apply _root_.RamificationTheory.HilbertRamification.Higher.valuationSubringAutOfUniqueExtension_one_apply _root_.ValuationTheory.DiscreteValuationField.ValuedExtension.Henselian.integralClosureValuationSubringIntegerMapOfMemOrInv_apply _root_.ValuationTheory.DiscreteValuationField.ValuedExtension.degree_eq_finrank _root_.ValuationTheory.DiscreteValuationField.ValuedExtension.integerMap_apply _root_.ValuationTheory.DiscreteValuationField.ValuedExtension.integralClosureRingEquivTargetValuationSubringOfModuleFinite_apply _root_.ValuationTheory.DiscreteValuationField.ValuedExtension.integralClosureToTargetValuationSubringOfHasExtension_apply _root_.ValuationTheory.DiscreteValuationField.ValuedExtension.integralClosureValuationSubringIntegerMapOfMemOrInv_apply _root_.ValuationTheory.DiscreteValuationField.ValuedExtension.residueFieldEquivOfSurjective_apply _root_.ValuationTheory.DiscreteValuationField.ValuedExtension.residueFieldEquivOfSurjective_apply_residue _root_.ValuationTheory.DiscreteValuationField.ValuedExtension.residueFieldEquivOfSurjective_symm_apply_residueMap _root_.ValuationTheory.DiscreteValuationField.ValuedExtension.residueFieldEquivOfSurjective_symm_apply_target_residue _root_.ValuationTheory.DiscreteValuationField.ValuedExtension.residueMap_residue _root_.ValuationTheory.DiscreteValuationField.ValuedExtension.residueMap_residueFieldEquivOfSurjective_symm_apply _root_.ValuationTheory.DiscreteValuationField.ValuedExtension.residueUnitsEquivOfResidueMapSurjective_apply _root_.ValuationTheory.DiscreteValuationField.ValuedExtension.targetValuationSubringToIntegralClosureOfModuleFinite_apply _root_.ValuationTheory.DiscreteValuationField.ValuedExtension.unitMap_apply _root_.infinitePlace_mult_smul
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

namespace ValuationTheory

/-!
# Discretely valued fields

This is the basic one-dimensional API for fields equipped with a chosen
rank-one discrete valuation.
-/

noncomputable section

universe u v

namespace DiscreteValuationField

namespace DVF

variable {K : Type u} [Field K]

/-- An element of the valuation ring lying in the maximal ideal but not in its
square is a uniformizer. -/
theorem isUniformizer_of_mem_maximalIdeal_of_not_mem_maximalIdeal_sq
    (F : DVF.{u, v} K) {x : F.valuationSubring}
    (hx : x ∈ F.maximalIdeal) (hx_sq : x ∉ F.maximalIdeal ^ 2) :
    F.valuation.IsUniformizer (x : K) := by
  have hx_ne : x ≠ 0 := by
    intro hzero
    exact hx_sq (by simp [hzero])
  have hspan_ne : Ideal.span ({x} : Set F.valuationSubring) ≠ ⊥ := by
    intro hspan
    have hx_bot : x ∈ (⊥ : Ideal F.valuationSubring) := by
      rw [← hspan]
      exact Ideal.mem_span_singleton_self x
    exact hx_ne (by simpa using hx_bot)
  rcases F.nonzero_ideal_eq_maximalIdeal_pow
      (Ideal.span ({x} : Set F.valuationSubring)) hspan_ne with
    ⟨n, hn⟩
  have hspan_le_max :
      Ideal.span ({x} : Set F.valuationSubring) ≤ F.maximalIdeal := by
    rw [Ideal.span_le]
    intro y hy
    have hyx : y = x := by simpa using hy
    simpa [hyx] using hx
  have hn_ne_zero : n ≠ 0 := by
    intro hn_zero
    have hone : (1 : F.valuationSubring) ∈ F.maximalIdeal := by
      have htop_le :
          (⊤ : Ideal F.valuationSubring) ≤ F.maximalIdeal := by
        simpa [hn, hn_zero] using hspan_le_max
      exact htop_le trivial
    exact
      (IsLocalRing.maximalIdeal.isMaximal F.valuationSubring).isPrime.one_notMem
        hone
  have hn_lt_two : n < 2 := by
    by_contra hnot
    have htwo_le : 2 ≤ n := Nat.le_of_not_lt hnot
    have hx_span : x ∈ Ideal.span ({x} : Set F.valuationSubring) :=
      Ideal.mem_span_singleton_self x
    have hx_pow : x ∈ F.maximalIdeal ^ n := by
      simpa [hn] using hx_span
    exact hx_sq (Ideal.pow_le_pow_right htwo_le hx_pow)
  have hn_eq_one : n = 1 := by
    cases n with
    | zero => exact (hn_ne_zero rfl).elim
    | succ n =>
        cases n with
        | zero => rfl
        | succ n =>
            exact
              ((not_lt_of_ge
                (Nat.succ_le_succ (Nat.succ_le_succ (Nat.zero_le n))))
                hn_lt_two).elim
  have hmax :
      F.maximalIdeal = Ideal.span ({x} : Set F.valuationSubring) := by
    simpa [hn_eq_one] using hn.symm
  exact Valuation.isUniformizer_of_maximalIdeal_eq_span (v := F.valuation) hmax

/-! ### Successive quotients of powers of the maximal ideal -/

end DVF
end DiscreteValuationField

end

end ValuationTheory
end

section
-- module Solutions.OAIQ244_DUKE.Valuation_DiscreteValuationField_FiniteExtension_Uniqueness
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_isCompleteDiscrete _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.DiscreteValuationField.Examples.Qp.padicDVRValuation_isRankOneDiscrete _root_.LocalFieldTheory.DiscreteValuationField.LocalField.residueField_charP_residueCharacteristic _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.RamificationTheory.HilbertRamification.Higher.lowerRamificationGroup.instNormal _root_.RamificationTheory.HilbertRamification.ValuationSubring.selectedResidueField.instAlgebra _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.RamificationTheory.HilbertRamification.CompleteDVF.decompositionGroupMulSemiringAction _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.chosenFinitePlaceBaseValuationIsNontrivial _root_.finiteLocalUnitsOpen _root_.relativeAdeleRingIntermediateAlgebra _root_.relativeAdeleRingTopIntermediateAlgebra
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false
/-! Provides the public declarations in the `ValuationTheory.DiscreteValuationField.FiniteExtension.Uniqueness` Lean module. -/

namespace ValuationTheory

noncomputable section

universe u v w x y

namespace DiscreteValuationField
namespace ValuedExtension

variable {K : Type u} {L : Type w} [Field K] [Field L]
variable [Algebra K L] [FiniteDimensional K L]
variable (base : CompleteDVF.{u, v} K) (target : CompleteDVF.{w, x} L)
variable [base.valuation.HasExtension target.valuation]

/-- Module-finiteness of the target valuation ring in a finite separable
extension, with no separate integral-closure certificate. -/
theorem moduleFinite_target_valuationSubring_of_finite_separable

    [Algebra.IsSeparable K L]
    [IsScalarTower base.valuationSubring target.valuationSubring L] :
    Module.Finite base.valuationSubring target.valuationSubring := by
  let : IsIntegralClosure target.valuationSubring base.valuationSubring L :=
    (target_valuationSubring_isIntegralClosure_of_finite_separable base target)
  exact moduleFinite_target_valuationSubring_of_isIntegralClosure
    (K := K) (L := L) base target

/-- Torsion-freeness of the target valuation ring over the base valuation ring
in a finite separable extension, with no separate integral-closure
certificate. -/
theorem moduleIsTorsionFree_target_valuationSubring_of_finite_separable

    [Algebra.IsSeparable K L]
    [IsScalarTower base.valuationSubring target.valuationSubring L] :
    Module.IsTorsionFree base.valuationSubring target.valuationSubring := by
  let : IsIntegralClosure target.valuationSubring base.valuationSubring L :=
    (target_valuationSubring_isIntegralClosure_of_finite_separable base target)
  let : IsFractionRing base.valuationSubring K :=
    base_valuationSubring_isFractionRing (K := K) base
  let : FaithfulSMul base.valuationSubring L :=
    FaithfulSMul.of_field_isFractionRing base.valuationSubring L K L
  let : Module.IsTorsionFree base.valuationSubring L := inferInstance
  exact IsIntegralClosure.isTorsionFree base.valuationSubring L

end ValuedExtension
end DiscreteValuationField

end

end ValuationTheory
end

section
-- module Solutions.OAIQ244_DUKE.LocalClassFieldTheory_ClassFormation_LocalBlocks_Induced
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.HilbertRamification.decompositionField_decompositionField_integerMap_isLocalHom _root_.KummerTheory.DiscreteNthRootsSubgroup.instCommGroupSubtypeUnitsMemSubgroup _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.DiscreteValuationField.finite_nsmulAddKernel_padicInt_pi _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_multiplicative_nthPowerKernel _root_.LocalFieldTheory.finite_nsmulAddKernel_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.LubinTate.compatibleGroupFamiliesCommGroup _root_.LubinTate.compatibleGroupFamiliesGroup _root_.OAI.PrimeDegreePackets.boundedRealFields_finite _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionResidueField.instField _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.CyclicCohomology.binaryCoefficientFamilyCommGroup _root_.CyclicCohomology.instMulDistribMulActionBinaryCoefficientFamily _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

/-!
# Local blocks of the idele group

For a place `w` of a Galois extension above a base absolute value `v`, its
decomposition group acts on the local multiplicative group.  The product of
all conjugate local factors is therefore the induced module from that
decomposition group. This is the algebraic content of the induced local block.

The local field is expressed as the canonical algebraic localization.
For finite extensions this is the entire metric completion by
`absoluteValueExtension_finiteLocalization_eq_top`.
-/

open scoped TensorProduct

noncomputable section

namespace LocalClassFieldTheory

open AlgebraicNumberTheory.Valuations
open HilbertRamification
open CyclicCohomology.ProfiniteCohomology.Herbrand
open CyclicCohomology

universe u v

variable {K : Type u} {L : Type v}
    [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L]
    [IsGalois K L]

/-- Degree-zero cohomology for one local block. -/
noncomputable def localPlaceBlockHerbrandH0Equiv
    (vK : AbsoluteValue K ℝ) (hvK : vK.IsNontrivial)
    (w : AbsoluteValueExtension vK L)
    (σ : L ≃ₐ[K] L)
    (hgen : ∀ τ : L ≃ₐ[K] L,
      τ ∈ Subgroup.zpowers σ) :
    letI :=
      decompositionGroupLocalUnitsAction vK hvK w
    letI : Fintype (absoluteValueDecompositionGroup K w.1) :=
      Fintype.ofFinite _
    HerbrandH0 (L ≃ₐ[K] L)
        (LocalPlaceBlock vK hvK w) ≃*
      HerbrandH0 (absoluteValueDecompositionGroup K w.1)
        (LocalizedCompletion vK w)ˣ :=
  by
    letI :=
      decompositionGroupLocalUnitsAction vK hvK w
    letI : Fintype (absoluteValueDecompositionGroup K w.1) :=
      Fintype.ofFinite _
    exact inducedHerbrandH0EquivOfFiniteCyclic
      (absoluteValueDecompositionGroup K w.1) σ hgen

/-- Degree-minus-one cohomology for one local block. -/
noncomputable def localPlaceBlockHerbrandHMinusOneEquiv
    (vK : AbsoluteValue K ℝ) (hvK : vK.IsNontrivial)
    (w : AbsoluteValueExtension vK L)
    (σ : L ≃ₐ[K] L)
    (hgen : ∀ τ : L ≃ₐ[K] L,
      τ ∈ Subgroup.zpowers σ) :
    letI :=
      decompositionGroupLocalUnitsAction vK hvK w
    letI : Fintype (absoluteValueDecompositionGroup K w.1) :=
      Fintype.ofFinite _
    HerbrandHMinusOne (L ≃ₐ[K] L)
        (LocalPlaceBlock vK hvK w) σ ≃*
      HerbrandHMinusOne
        (absoluteValueDecompositionGroup K w.1)
        (LocalizedCompletion vK w)ˣ
        (subgroupGeneratorOfGenerator
          (absoluteValueDecompositionGroup K w.1) σ hgen) :=
  by
    letI :=
      decompositionGroupLocalUnitsAction vK hvK w
    letI : Fintype (absoluteValueDecompositionGroup K w.1) :=
      Fintype.ofFinite _
    exact inducedHerbrandHMinusOneEquivOfFiniteCyclic
      (absoluteValueDecompositionGroup K w.1) σ hgen

end LocalClassFieldTheory
end
end

section
-- module Solutions.OAIQ244_DUKE.LocalClassFieldTheory_ClassFormation_LocalizedCompletionCohomology_Algebra
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionResidueField.instField _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

/-!
# Algebra for localized completion cohomology

This file provides named algebra, finite-dimensional, Galois, scalar-tower, and
global-to-local embedding providers for localized completions.
-/

open AlgebraicNumberTheory.Valuations
open HilbertRamification
open LocalClassFieldTheory
open LocalFieldTheory
open CyclicCohomology
open CyclicCohomology.ProfiniteCohomology.Herbrand
open scoped TensorProduct

noncomputable section

namespace LocalClassFieldTheory

universe u v

variable {K : Type u} {L : Type v}
    [Field K] [Field L] [Algebra K L]

/-- The named finite-dimensional certificate for an algebraic localization
of a finite global extension. -/
theorem localizedCompletionFiniteDimensional
    [FiniteDimensional K L]
    (vK : AbsoluteValue K ℝ) (hvK : vK.IsNontrivial)
    (w : AbsoluteValueExtension vK L) :
    letI : Algebra vK.Completion (LocalizedCompletion vK w) :=
      localizedCompletionBaseAlgebra vK w
    FiniteDimensional vK.Completion (LocalizedCompletion vK w) := by
  let _ := localizedCompletionBaseAlgebra vK w
  exact localizedCompletionModuleFinite vK hvK w

/-- The named Galois certificate for the algebraic localization of a Galois
extension. -/
theorem localizedCompletionIsGalois
    [IsGalois K L]
    (vK : AbsoluteValue K ℝ)
    (w : AbsoluteValueExtension vK L) :
    letI : Algebra vK.Completion (LocalizedCompletion vK w) :=
      localizedCompletionBaseAlgebra vK w
    IsGalois vK.Completion (LocalizedCompletion vK w) := by
  let _ := localizedCompletionBaseAlgebra vK w
  exact HilbertRamification.algebraicLocalization_isGalois vK w


end LocalClassFieldTheory
end
end

section
-- module Solutions.OAIQ244_DUKE.LocalClassFieldTheory_ClassFormation_LocalizedCompletionCohomology_Generator
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.LubinTate.compatibleGroupFamiliesGroup _root_.OAI.PrimeDegreePackets.diagonalLogAction _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionResidueField.instField _root_.RamificationTheory.HilbertRamification.ValuationSubring.selectedResidueField.instAlgebra _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.RelativeIdeleGroup.relativeIdeleMulAction _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen _root_.relativeAdeleRingIntermediateAlgebra _root_.relativeAdeleRingTopIntermediateAlgebra
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

/-!
# A generator of a localized finite Galois group
-/

open AlgebraicNumberTheory.Valuations
open HilbertRamification
open LocalClassFieldTheory
open LocalFieldTheory
open CyclicCohomology
open CyclicCohomology.ProfiniteCohomology.Herbrand
open scoped TensorProduct

noncomputable section

namespace LocalClassFieldTheory

universe u v

variable {K : Type u} {L : Type v}
    [Field K] [Field L] [Algebra K L]
    [IsGalois K L] [FiniteDimensional K L]

/-- A generator of the localized Galois group induced by a chosen generator
of the global cyclic Galois group. -/
noncomputable def localizedCompletionGaloisGenerator
    (vK : AbsoluteValue K ℝ) (hvK : vK.IsNontrivial)
    (w : AbsoluteValueExtension vK L)
    (σ : L ≃ₐ[K] L)
    (hgen : ∀ τ : L ≃ₐ[K] L,
      τ ∈ Subgroup.zpowers σ) :
    letI hK := AbsoluteValue.extensionCompletionAlgebra (K := K) w.1
    letI : SMul K w.1.Completion := hK.toSMul
    letI : Algebra vK.Completion w.1.Completion :=
      AbsoluteValue.completionAlgebra vK w.1 w.2
    LocalizedCompletion vK w ≃ₐ[vK.Completion]
      LocalizedCompletion vK w :=
  (decompositionGroupEquivAlgebraicLocalizationAut
    vK hvK w)
      (subgroupGeneratorOfGenerator
        (absoluteValueDecompositionGroup K w.1) σ hgen)

theorem localizedCompletionGaloisGenerator_generates
    (vK : AbsoluteValue K ℝ) (hvK : vK.IsNontrivial)
    (w : AbsoluteValueExtension vK L)
    (σ : L ≃ₐ[K] L)
    (hgen : ∀ τ : L ≃ₐ[K] L,
      τ ∈ Subgroup.zpowers σ) :
    letI hK := AbsoluteValue.extensionCompletionAlgebra (K := K) w.1
    letI : SMul K w.1.Completion := hK.toSMul
    letI : Algebra vK.Completion w.1.Completion :=
      AbsoluteValue.completionAlgebra vK w.1 w.2
    ∀ τ : LocalizedCompletion vK w ≃ₐ[vK.Completion]
        LocalizedCompletion vK w,
      τ ∈ Subgroup.zpowers
        (localizedCompletionGaloisGenerator
          vK hvK w σ hgen) := by
  let := localizedCompletionBaseAlgebra vK w
  let H := absoluteValueDecompositionGroup K w.1
  let e :=
    decompositionGroupEquivAlgebraicLocalizationAut
      vK hvK w
  let δ :=
    subgroupGeneratorOfGenerator H σ hgen
  intro τ
  rw [show localizedCompletionGaloisGenerator
      vK hvK w σ hgen = e δ from rfl]
  change τ ∈ Subgroup.zpowers (e.toMonoidHom δ)
  rw [← MonoidHom.map_zpowers e.toMonoidHom δ]
  refine ⟨e.symm τ, ?_, e.apply_symm_apply τ⟩
  exact subgroupGeneratorOfGenerator_generates
    H σ hgen (e.symm τ)

end LocalClassFieldTheory
end
end

section
-- module Solutions.OAIQ244_DUKE.LocalField_NonarchimedeanLocalField_FiniteExtensionCompleteDVF
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.PrimeDegreePackets.diagonalLogAction _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.RamificationTheory.HilbertRamification.ValuationSubring.selectedResidueField.instAlgebra _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.RelativeIdeleGroup.relativeIdeleMulAction _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen _root_.relativeAdeleRingIntermediateAlgebra _root_.relativeAdeleRingTopIntermediateAlgebra
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

/-!
# Complete-DVF packages for local fields and their finite extensions

The canonical complete discrete valuation on a nonarchimedean local field,
and an integral-closure valuation chosen on each finite separable extension.
-/

noncomputable section

namespace LocalFieldTheory

open ValuationTheory.DiscreteValuationField
open ValuationTheory.DiscreteValuationField.ValuedExtension
open scoped ValuativeRel

universe u v y

/-! ## The canonical complete discrete valuation -/

/-- The valuation integer ring of a finite separable local extension is a
finite module over the base valuation integer ring. -/
theorem localCompleteDVF_integerRing_moduleFinite
    (K : Type u) (L : Type v) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [Algebra.IsSeparable K L]
    [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
    [Valuation.HasExtension (ValuativeRel.valuation K)
      (ValuativeRel.valuation L)] :
    Module.Finite 𝒪[K] 𝒪[L] := by
  let : IsIntegralClosure 𝒪[L] 𝒪[K] L :=
    localCompleteDVF_integerRing_isIntegralClosure K L
  exact IsIntegralClosure.finite 𝒪[K] K L 𝒪[L]

/-! ## Chosen ramification data for an arbitrary finite local extension -/

end LocalFieldTheory
end
end

section
-- module Solutions.OAIQ244_DUKE.AlgebraicNumberTheory_Galois_CyclicPrimeSubextension
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.PrimeDegreePackets.diagonalLogAction _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.CyclicCohomology.binaryCoefficientFamilyCommGroup
attribute [-simp] _root_.IsDiscreteValuationRing.addVal_ringEquiv _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.LocalClassFieldTheory.completionProductUnitsEquivRightCosets_apply_coe _root_.LocalClassFieldTheory.conjugateExtensionCompletionRingEquiv_toCompletion _root_.LocalClassFieldTheory.localTensorEvaluation_tmul _root_.LocalClassFieldTheory.mem_decompositionRightCosetsFinset _root_.LocalClassFieldTheory.rightCosetCompletionUnitsEquiv_apply_coe _root_.LocalClassFieldTheory.rightCosetExtensionEquiv_apply _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.OAI.PrimeDegreePackets.ThetaConstruction.schwartzCM_apply _root_.doubleCosetExtension_mk _root_.extendAbsoluteValueExtensionFromIntermediate_apply _root_.infinitePlace_mult_smul
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

/-!
# The prime-degree subextension of a cyclic prime-power extension

This file constructs a prime-degree intermediate field.
For a nontrivial cyclic Galois extension whose group has order
`p ^ exponent`, the index-`p` subgroup constructed in
`SplittingGroupTheory` is sent through the finite Galois
correspondence.  Its fixed field is an actual cyclic Galois extension
of the base of degree `p`.

The finite-place decomposition group in that subextension is obtained
by restricting the decomposition group of `L / K`.  Thus complete
splitting descends to the prime-degree subextension, and nonsplitting
there ascends to `L`.
-/

open scoped NumberField Classical IsMulCommutative
open NumberField IsDedekindDomain

noncomputable section

open AlgebraicNumberTheory.Valuations
open HilbertRamification

section ValuationRestriction

variable {F E : Type}
    [Field F] [Field E] [Algebra F E]

/-- Regard the original extension as an extension of its restriction
to an intermediate field. -/
def absoluteValueExtensionOverIntermediate
    (vF : AbsoluteValue F ℝ)
    (w : AbsoluteValueExtension vF E)
    (M : IntermediateField F E) :
    AbsoluteValueExtension
      (restrictAbsoluteValueExtensionToIntermediate
        vF w M).1 E where
  val := w.1
  property _ := rfl

end ValuationRestriction

section DecompositionGroupChoice

variable {F L : Type*}
    [Field F] [Field L] [Algebra F L]

/-- Decomposition groups depend only on the valuation class. -/
theorem absoluteValueDecompositionGroup_eq_of_absoluteValue_isEquiv
    (w w' : AbsoluteValue L ℝ)
    (hww' : w.IsEquiv w') :
    absoluteValueDecompositionGroup F w =
      absoluteValueDecompositionGroup F w' := by
  have hlt : ∀ x : L, w x < 1 ↔ w' x < 1 :=
    AbsoluteValue.isEquiv_iff_lt_one_iff.mp hww'
  ext σ
  simp only [mem_absoluteValueDecompositionGroup_iff]
  constructor
  · intro hσ x
    exact
      (hlt (σ x)).symm.trans
        ((hσ x).trans (hlt x))
  · intro hσ x
    exact
      (hlt (σ x)).trans
        ((hσ x).trans (hlt x).symm)

/-- In an abelian Galois extension, conjugating an exact extension does
not change its decomposition subgroup. -/
theorem absoluteValueDecompositionGroup_conjugate_eq_of_isMulCommutative
    [IsMulCommutative (L ≃ₐ[F] L)]
    (vF : AbsoluteValue F ℝ)
    (w : AbsoluteValueExtension vF L)
    (ρ : L ≃ₐ[F] L) :
    absoluteValueDecompositionGroup F
        (absoluteValueExtensionConjugate
          vF w ρ).1 =
      absoluteValueDecompositionGroup F w.1 := by
  ext τ
  change
    (∀ x : L,
      w.1 (ρ (τ x)) < 1 ↔ w.1 (ρ x) < 1) ↔
      ∀ x : L, w.1 (τ x) < 1 ↔ w.1 x < 1
  constructor
  · intro hτ x
    have hx := hτ (ρ⁻¹ x)
    have hleft :
        ρ (τ (ρ⁻¹ x)) = τ x := by
      calc
        ρ (τ (ρ⁻¹ x)) =
            τ (ρ (ρ⁻¹ x)) := by
          change
            (ρ * τ) (ρ⁻¹ x) =
              (τ * ρ) (ρ⁻¹ x)
          rw [mul_comm]
        _ = τ x := by simp
    have hright : ρ (ρ⁻¹ x) = x := by simp
    rwa [hleft, hright] at hx
  · intro hτ x
    have hx := hτ (ρ x)
    have hcomm :
        ρ (τ x) = τ (ρ x) := by
      change (ρ * τ) x = (τ * ρ) x
      rw [mul_comm]
    rwa [hcomm]

/-- In an abelian Galois extension the decomposition subgroup is
independent of the exact extension above the base place. -/
theorem absoluteValueDecompositionGroup_eq_of_exactExtensions_of_isMulCommutative
    [IsGalois F L]
    [IsMulCommutative (L ≃ₐ[F] L)]
    (vF : AbsoluteValue F ℝ)
    (hvF : vF.IsNontrivial)
    (w w' : AbsoluteValueExtension vF L) :
    absoluteValueDecompositionGroup F w.1 =
      absoluteValueDecompositionGroup F w'.1 := by
  obtain ⟨ρ, hρ⟩ :=
    absoluteValueConjugacy vF hvF w w'
  rw [hρ,
    absoluteValueDecompositionGroup_conjugate_eq_of_isMulCommutative
      (F := F) vF w ρ]

end DecompositionGroupChoice
end
end

section
-- module Solutions.OAIQ244_DUKE.AlgebraicNumberTheory_Ramification_Splitting_NormalClosure
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.KummerTheory.primeCyclotomicBaseIsGalois _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.PrimeDegreePackets.boundedRealFields_finite _root_.OAI.PrimeDegreePackets.diagonalLogAction _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.cyclicPrimeDegreeIntermediate_top_isGalois _root_.primeOrderFixedField_isGalois
attribute [-simp] _root_.IsDiscreteValuationRing.addVal_ringEquiv _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.LocalClassFieldTheory.completionProductUnitsEquivRightCosets_apply_coe _root_.LocalClassFieldTheory.conjugateExtensionCompletionRingEquiv_toCompletion _root_.LocalClassFieldTheory.localTensorEvaluation_tmul _root_.LocalClassFieldTheory.mem_decompositionRightCosetsFinset _root_.LocalClassFieldTheory.rightCosetCompletionUnitsEquiv_apply_coe _root_.LocalClassFieldTheory.rightCosetExtensionEquiv_apply _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.OAI.PrimeDegreePackets.ThetaConstruction.schwartzCM_apply _root_.infinitePlace_mult_smul
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

/-!
# Complete splitting and normal closures

This file formalizes the normal-closure reduction for complete splitting.
For a finite Galois extension `M / K`, an intermediate field `L`, a
nontrivial absolute value `v` of `K`, and an extension `w` to `M`, put

* `G = Gal(M / K)`,
* `H = Gal(M / L)`, and
* `D = D(w / v)`.

Restriction of the conjugates of `w` gives an equivalence

`H \ G / D ≃ { extensions of v to L }`.

Thus the intrinsic complete-splitting condition for the possibly
non-Galois extension `L / K` is exactly the equality between the number
of double cosets and the number of left cosets.  If `M` is generated by
the `K`-conjugates of `L`, then `H` has trivial normal core.
`SplittingGroupTheory` consequently forces `D = 1`, so the place splits
completely already in `M`.
-/

open scoped NumberField Classical
open NumberField IsDedekindDomain

noncomputable section

open AlgebraicNumberTheory.Valuations
open HilbertRamification

section AbsoluteValueExtensions

variable {K M : Type}
    [Field K] [Field M] [Algebra K M]

variable (vK : AbsoluteValue K ℝ)
    (hvK : vK.IsNontrivial)
    (w : AbsoluteValueExtension vK M)
    (L : IntermediateField K M)

local notation "G" => M ≃ₐ[K] M
local notation "H" => L.fixingSubgroup
local notation "D" => absoluteValueDecompositionGroup K w.val

/-- Every extension of `v` to the intermediate field occurs by
restricting a conjugate of `w`. -/
theorem doubleCosetExtension_surjective
    [FiniteDimensional K M] [IsGalois K M] :
    Function.Surjective
      (doubleCosetExtension vK hvK w L) := by
  intro u
  let w' : AbsoluteValueExtension vK M :=
    extendAbsoluteValueExtensionFromIntermediate
      vK hvK L u
  obtain ⟨g : G, hg⟩ :=
    absoluteValueConjugacy vK hvK w w'
  refine
    ⟨DoubleCoset.mk H D g⁻¹, ?_⟩
  rw [doubleCosetExtension_mk]
  apply Subtype.ext
  ext x
  change w.1 (g (x : M)) = u.1 x
  have hvalue :=
    congrArg
      (fun z : AbsoluteValueExtension vK M ↦
        z.1 (x : M))
      hg
  change w'.1 (x : M) = w.1 (g (x : M))
    at hvalue
  rw [← hvalue]
  exact
    extendAbsoluteValueExtensionFromIntermediate_apply
      vK hvK L u x

/-- Equality after restriction to `L` is precisely equality of the
corresponding double cosets. The proof applies valuation-extension counting over
`L` and then reads the resulting `L`-automorphism as an element of
`H = Gal(M / L)`. -/
theorem doubleCosetExtension_injective
    [IsGalois K M] :
    Function.Injective
      (doubleCosetExtension vK hvK w L) := by
  intro q r hqr
  let g : G := q.out
  let s : G := r.out
  have hrestr :
      restrictAbsoluteValueExtensionToIntermediate
          vK
          (absoluteValueExtensionConjugate
            vK w g⁻¹)
          L =
        restrictAbsoluteValueExtensionToIntermediate
          vK
          (absoluteValueExtensionConjugate
            vK w s⁻¹)
          L := by
    calc
      _ = doubleCosetExtension vK hvK w L q := by
        rw [← DoubleCoset.out_eq' _ _ q]
        exact
          (doubleCosetExtension_mk
            vK hvK w L g).symm
      _ = doubleCosetExtension vK hvK w L r :=
        hqr
      _ = _ := by
        rw [← DoubleCoset.out_eq' _ _ r]
        exact
          doubleCosetExtension_mk
            vK hvK w L s
  let u :
      AbsoluteValueExtension vK L :=
    restrictAbsoluteValueExtensionToIntermediate
      vK
      (absoluteValueExtensionConjugate
        vK w g⁻¹)
      L
  let wG : AbsoluteValueExtension u.1 M :=
    absoluteValueExtensionOverIntermediate
      vK
      (absoluteValueExtensionConjugate
        vK w g⁻¹)
      L
  let wS : AbsoluteValueExtension u.1 M :=
    { val :=
        (absoluteValueExtensionConjugate
          vK w s⁻¹).1
      property := by
        intro x
        have hx :=
          congrArg
            (fun z : AbsoluteValueExtension vK L ↦
              z.1 x)
            hrestr
        change
          w.1 (s⁻¹ (x : M)) =
            w.1 (g⁻¹ (x : M))
        exact hx.symm }
  let hu : u.1.IsNontrivial :=
    u.isNontrivial hvK
  obtain ⟨η : M ≃ₐ[L] M, hη⟩ :=
    absoluteValueConjugacy u.1 hu wG wS
  let h : G :=
    η.restrictScalars K
  have hh : h ∈ H := by
    intro x
    exact η.commutes x
  let d : G :=
    s⁻¹ * h⁻¹ * g
  have hdEq :
      absoluteValueExtensionConjugate
          vK w d = w := by
    apply Subtype.ext
    ext x
    have hx :=
      congrArg
        (fun z : AbsoluteValueExtension u.1 M ↦
          z.1 (η⁻¹ (g x)))
        hη
    change
      w.1 (s⁻¹ (η⁻¹ (g x))) =
        w.1 (g⁻¹ (η (η⁻¹ (g x))))
      at hx
    change
      w.1 (s⁻¹ (η⁻¹ (g x))) = w.1 x
    simpa using hx
  have hd : d ∈ D :=
    (mem_absoluteValueDecompositionGroup_iff_extensionConjugate_eq
      vK hvK w d).mpr hdEq
  rw [← DoubleCoset.out_eq' _ _ q,
    ← DoubleCoset.out_eq' _ _ r,
    DoubleCoset.eq]
  refine
    ⟨h⁻¹, L.fixingSubgroup.inv_mem hh,
      d⁻¹,
      (absoluteValueDecompositionGroup K w.val).inv_mem hd,
      ?_⟩
  simp [d, g, s, mul_assoc]

/-- The place-counting equivalence in the orientation needed for the
normal-closure reduction. -/
noncomputable def doubleCosetExtensionEquiv
    [FiniteDimensional K M] [IsGalois K M] :
    DoubleCoset.Quotient (H : Set G) D ≃
      AbsoluteValueExtension vK L :=
  Equiv.ofBijective
    (doubleCosetExtension vK hvK w L)
    ⟨doubleCosetExtension_injective
        vK hvK w L,
      doubleCosetExtension_surjective
        vK hvK w L⟩

end AbsoluteValueExtensions

section DoubleCosetCount

variable {K M : Type}
    [Field K] [Field M] [Algebra K M]
    [IsGalois K M]

local notation "G" => M ≃ₐ[K] M

variable [FiniteDimensional K M]

variable (vK : AbsoluteValue K ℝ)
    (w : AbsoluteValueExtension vK M)
    (L : IntermediateField K M)

/-- Place counting plus the definition of complete
splitting: `v` splits completely in `L` exactly when the double-coset
count equals the left-coset count. -/
theorem absoluteValueSplitsCompletelyInExtension_iff_doubleCoset_card_eq
    (hvK : vK.IsNontrivial) :
    AbsoluteValueSplitsCompletelyInExtension
        (E := L) vK ↔
      Nat.card
          (DoubleCoset.Quotient
            (L.fixingSubgroup : Set G)
            (absoluteValueDecompositionGroup K w.1)) =
        Nat.card
          (DoubleCoset.Quotient
            (L.fixingSubgroup : Set G)
            (⊥ : Subgroup G)) := by
  unfold AbsoluteValueSplitsCompletelyInExtension
  rw [Nat.card_congr
      (doubleCosetExtensionEquiv
        vK hvK w L),
    leftCosetDoubleCoset_card_eq_finrank]

/-- The actual decomposition group is trivial as soon as an
intermediate field with core-free fixing subgroup is completely split.
This is the reusable source-producing form of the normal-closure
normal-closure splitting argument. -/
theorem absoluteValueDecompositionGroup_eq_bot_of_splitsCompletelyInIntermediate
    (hvK : vK.IsNontrivial)
    (hcore :
      L.fixingSubgroup.normalCore = ⊥)
    (hsplit :
      AbsoluteValueSplitsCompletelyInExtension
        (E := L) vK) :
    absoluteValueDecompositionGroup K w.1 = ⊥ := by
  have hcard :=
    (absoluteValueSplitsCompletelyInExtension_iff_doubleCoset_card_eq
      vK w L hvK).mp hsplit
  exact
    (doubleCoset_card_eq_leftCoset_iff_of_normalCore_eq_bot
      L.fixingSubgroup
      (absoluteValueDecompositionGroup K w.1)
      hcore).mp hcard

end DoubleCosetCount

section SplittingTransport

variable
    {K E E' : Type}
    [Field K]
    [Field E] [Algebra K E]
    [Field E'] [Algebra K E']

/-- Transport extensions of an absolute value through an algebra
equivalence of finite extensions. -/
noncomputable def absoluteValueExtensionEquivOfAlgEquiv
    (v : AbsoluteValue K ℝ)
    (e : E ≃ₐ[K] E') :
    AbsoluteValueExtension v E ≃
      AbsoluteValueExtension v E' where
  toFun w :=
    { val :=
        w.1.comp (f := e.symm.toRingHom)
          e.symm.injective
      property := by
        intro x
        change w.1 (e.symm (algebraMap K E' x)) = v x
        rw [e.symm.commutes]
        exact w.2 x }
  invFun w :=
    { val :=
        w.1.comp (f := e.toRingHom)
          e.injective
      property := by
        intro x
        change w.1 (e (algebraMap K E x)) = v x
        rw [e.commutes]
        exact w.2 x }
  left_inv w := by
    apply Subtype.ext
    ext x
    change w.1 (e.symm (e x)) = w.1 x
    rw [e.symm_apply_apply]
  right_inv w := by
    apply Subtype.ext
    ext x
    change w.1 (e (e.symm x)) = w.1 x
    rw [e.apply_symm_apply]

variable [FiniteDimensional K E]
    [FiniteDimensional K E']

omit [FiniteDimensional K E] [FiniteDimensional K E'] in
/-- Intrinsic complete splitting is invariant under replacing the
extension by an isomorphic `K`-algebra. -/
theorem absoluteValueSplitsCompletelyInExtension_algEquiv
    (v : AbsoluteValue K ℝ)
    (e : E ≃ₐ[K] E') :
    AbsoluteValueSplitsCompletelyInExtension
        (E := E) v ↔
      AbsoluteValueSplitsCompletelyInExtension
        (E := E') v := by
  unfold AbsoluteValueSplitsCompletelyInExtension
  rw [Nat.card_congr
      (absoluteValueExtensionEquivOfAlgEquiv v e),
    e.toLinearEquiv.finrank_eq]

end SplittingTransport
end
end

section
-- module Solutions.OAIQ244_DUKE.AlgebraicNumberTheory_SUnit_LogLattice
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.DiscreteNthRootsSubgroup.instCommGroupSubtypeUnitsMemSubgroup _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.KummerTheory.finite_sUnit_nthPowerQuotient _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.LubinTate.compatibleGroupFamiliesCommGroup _root_.LubinTate.compatibleGroupFamiliesGroup _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.maximalIdealPowSuccQuotModule _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.CyclicCohomology.binaryCoefficientFamilyCommGroup _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace
attribute [-simp] _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.IsDiscreteValuationRing.addVal_ringEquiv _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.KummerTheory.mem_sUnitFiniteKummerRadical_iff _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.LocalFieldTheory.residueField_algebraMap_residue _root_.OAI.PrimeDegreePackets.ThetaConstruction.schwartzCM_apply _root_.coordinateSum_normalizedLogDiagonal _root_.fullLogSpace_smul_apply _root_.infinitePlace_mult_smul _root_.logPlacePermutationHom_apply _root_.sUnit_smul_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

/-!
# The logarithmic lattice of `S`-units

This file develops the logarithmic lattice of `S`-units. The
finite set `S` consists of the finite places; all infinite places are
understood to belong to the set of places used in the theorem.

The first construction uses the usual reduced archimedean logarithmic
space (one infinite coordinate is omitted) together with the integral
principal-divisor coordinates at `S`.  Its image is proved directly to
be a complete `ℤ`-lattice.  The normalized, all-place logarithmic map
and its coordinate-sum-zero hyperplane are constructed below from this
lattice.
-/

noncomputable section

open IsDedekindDomain Module
open scoped Classical NumberField nonZeroDivisors


variable {K : Type*} [Field K] [NumberField K]

namespace SUnitGroup

variable (S : Finset (HeightOneSpectrum (𝓞 K)))

section FullLogarithmicSpace

/-- The kernel of the normalized all-place logarithm is the group of
roots of unity. -/
theorem fullLog_eq_zero_iff
    (x : Additive (SUnitGroup (K := K) S)) :
    fullLog (K := K) S x = 0 ↔
      x ∈ AddCommGroup.torsion
        (Additive (SUnitGroup (K := K) S)) := by
  rw [← reducedLog_eq_zero_iff (K := K) S]
  constructor
  · intro hx
    have := congrArg
      (logHyperplaneEquivReduced (K := K) S) hx
    simpa [logHyperplaneEquivReduced_fullLog] using this
  · intro hx
    apply (logHyperplaneEquivReduced (K := K) S).injective
    rw [logHyperplaneEquivReduced_fullLog, hx, map_zero]

end FullLogarithmicSpace

end SUnitGroup
end
end

section
-- module Solutions.OAIQ244_DUKE.AlgebraicNumberTheory_SUnit_GaloisAction
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.DiscreteNthRootsSubgroup.instTopologicalSpaceSubtypeUnitsMemSubgroup _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.KummerTheory.finite_sUnit_nthPowerQuotient _root_.KummerTheory.nthRootsSubgroupFintype _root_.KummerTheory.primeCyclotomicBaseFiniteDimensional _root_.LocalFieldTheory.DiscreteValuationField.finite_nsmulAddKernel_padicInt_pi _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_multiplicative_nthPowerKernel _root_.LocalFieldTheory.finite_nsmulAddKernel_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.PrimeDegreePackets.ThetaConstruction.coordinateLattice_discrete _root_.OAI.PrimeDegreePackets.boundedRealFields_finite _root_.OAI.PrimeDegreePackets.diagonalLogAction _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.integralGroup_discrete _root_.OAI.PrimeDegreePackets.logSubgroup_discrete _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.OAI.PrimeDegreePackets.orderedLogSubgroup_discrete _root_.OAI.PrimeDegreePackets.xT2Space _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionResidueField.instField _root_.RamificationTheory.HilbertRamification.ValuationSubring.selectedResidueField.instAlgebra _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.RelativeIdeleGroup.relativeIdeleMulAction _root_.ValuationTheory.DiscreteValuationField.DVF.maximalIdealPowSuccQuotModule _root_.ValuationTheory.DiscreteValuationField.DVF.residueField.field _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.isDomain _root_.CyclicCohomology.binaryCoefficientFamilyCommGroup _root_.LocalClassFieldTheory.intrinsicAbsoluteGaloisT2 _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.chosenFinitePlaceBaseNontriviallyNormedField _root_.relativeAdeleRingIntermediateAlgebra _root_.relativeAdeleRingTopIntermediateAlgebra
attribute [-simp] _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.IsDiscreteValuationRing.addVal_ringEquiv _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.LocalFieldTheory.residueField_algebraMap_residue _root_.OAI.PrimeDegreePackets.ThetaConstruction.schwartzCM_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

/-!
# Galois actions on `S`-units and their logarithmic lattice

This file supplies the equivariant input for the `S`-unit calculation. A Galois
automorphism acts on finite places through its restriction to the ring of
integers, on infinite places by precomposition, and on field units in the
usual way.  For a stable finite set of finite places these actions restrict
to the actual `S`-unit group.
-/

open scoped BigOperators Classical NumberField nonZeroDivisors
open IsDedekindDomain Module
open CyclicCohomology.ProfiniteCohomology.Herbrand
open CyclicCohomology

noncomputable section

variable
    (K L : Type*) [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]

section FinitePlaceAction

/-- Splitting of the full coordinate space into the sum-zero
hyperplane and its coordinate sum. -/
noncomputable def fullLogSpaceSplit
    (S : Finset (HeightOneSpectrum (𝓞 L))) :
    SUnitGroup.FullLogSpace (K := L) S →ₗ[ℝ]
      (SUnitGroup.LogHyperplane (K := L) S × ℝ) where
  toFun z :=
    (⟨z -
        SUnitGroup.coordinateSum (K := L) S z •
          normalizedLogDiagonal L S, by
      apply LinearMap.mem_ker.mpr
      rw [map_sub, map_smul,
        coordinateSum_normalizedLogDiagonal]
      simp⟩,
      SUnitGroup.coordinateSum (K := L) S z)
  map_add' z z' := by
    apply Prod.ext
    · ext p
      simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, map_add,
        Prod.fst_add, Submodule.coe_add]
      module
    · exact map_add
        (SUnitGroup.coordinateSum (K := L) S) z z'
  map_smul' c z := by
    apply Prod.ext
    · ext p
      simp only [Pi.smul_apply, Pi.sub_apply, map_smul,
        Prod.smul_fst, RingHom.id_apply, Submodule.coe_smul]
      module
    · exact map_smul
        (SUnitGroup.coordinateSum (K := L) S) c z

theorem fullLogSpaceSplit_injective
    (S : Finset (HeightOneSpectrum (𝓞 L))) :
    Function.Injective (fullLogSpaceSplit L S) := by
  intro z z' h
  have hfirst :
      z -
          SUnitGroup.coordinateSum (K := L) S z •
            normalizedLogDiagonal L S =
        z' -
          SUnitGroup.coordinateSum (K := L) S z' •
            normalizedLogDiagonal L S :=
    congrArg
      (fun q =>
        ((q.1 :
          SUnitGroup.LogHyperplane (K := L) S) :
            SUnitGroup.FullLogSpace (K := L) S)) h
  have hsecond :
      SUnitGroup.coordinateSum (K := L) S z =
        SUnitGroup.coordinateSum (K := L) S z' :=
    congrArg Prod.snd h
  calc
    z =
        (z -
            SUnitGroup.coordinateSum (K := L) S z •
              normalizedLogDiagonal L S) +
          SUnitGroup.coordinateSum (K := L) S z •
            normalizedLogDiagonal L S := by
              symm
              exact sub_add_cancel _ _
    _ =
        (z' -
            SUnitGroup.coordinateSum (K := L) S z' •
              normalizedLogDiagonal L S) +
          SUnitGroup.coordinateSum (K := L) S z' •
            normalizedLogDiagonal L S := by
              rw [hfirst, hsecond]
    _ = z' := sub_add_cancel _ _

theorem fullLogSpaceSplit_surjective
    (S : Finset (HeightOneSpectrum (𝓞 L))) :
    Function.Surjective (fullLogSpaceSplit L S) := by
  intro q
  let z : SUnitGroup.FullLogSpace (K := L) S :=
    (q.1 : SUnitGroup.FullLogSpace (K := L) S) +
      q.2 • normalizedLogDiagonal L S
  refine ⟨z, ?_⟩
  apply Prod.ext
  · apply Subtype.ext
    change
      z -
          SUnitGroup.coordinateSum (K := L) S z •
            normalizedLogDiagonal L S =
        (q.1 : SUnitGroup.FullLogSpace (K := L) S)
    have hq :
        SUnitGroup.coordinateSum (K := L) S
            (q.1 : SUnitGroup.FullLogSpace (K := L) S) = 0 :=
      LinearMap.mem_ker.mp q.1.property
    simp [z, hq, coordinateSum_normalizedLogDiagonal]
  · change
      SUnitGroup.coordinateSum (K := L) S z = q.2
    have hq :
        SUnitGroup.coordinateSum (K := L) S
            (q.1 : SUnitGroup.FullLogSpace (K := L) S) = 0 :=
      LinearMap.mem_ker.mp q.1.property
    simp [z, hq, coordinateSum_normalizedLogDiagonal]

/-- Linear coordinate splitting used to adjoin one invariant diagonal
direction to the logarithmic lattice. -/
noncomputable def fullLogSpaceEquivHyperplaneProd
    (S : Finset (HeightOneSpectrum (𝓞 L))) :
    SUnitGroup.FullLogSpace (K := L) S ≃ₗ[ℝ]
      (SUnitGroup.LogHyperplane (K := L) S × ℝ) :=
  LinearEquiv.ofBijective
    (fullLogSpaceSplit L S)
    ⟨fullLogSpaceSplit_injective L S,
      fullLogSpaceSplit_surjective L S⟩

/-- The coordinate splitting as a continuous linear equivalence. -/
noncomputable def fullLogSpaceContinuousEquivHyperplaneProd
    (S : Finset (HeightOneSpectrum (𝓞 L))) :
    SUnitGroup.FullLogSpace (K := L) S ≃L[ℝ]
      (SUnitGroup.LogHyperplane (K := L) S × ℝ) :=
  (fullLogSpaceEquivHyperplaneProd L S).toContinuousLinearEquiv

/-- The complete lattice in the full logarithmic coordinate space
obtained by adjoining an integral invariant diagonal direction. -/
noncomputable def extendedFullLogLattice
    (S : Finset (HeightOneSpectrum (𝓞 L))) :
    Submodule ℤ (SUnitGroup.FullLogSpace (K := L) S) :=
  ZLattice.comap ℝ
    (fullLogHyperplaneDiagonalLattice L S)
    (fullLogSpaceContinuousEquivHyperplaneProd L S).toLinearMap

instance instDiscreteTopology_extendedFullLogLattice
    (S : Finset (HeightOneSpectrum (𝓞 L))) :
    DiscreteTopology (extendedFullLogLattice L S) := by
  let : Module.Finite ℤ
      (SUnitGroup.fullLogLattice (K := L) S) :=
    ZLattice.module_finite ℝ
      (SUnitGroup.fullLogLattice (K := L) S)
  let : Module.Free ℤ
      (SUnitGroup.fullLogLattice (K := L) S) :=
    ZLattice.module_free ℝ
      (SUnitGroup.fullLogLattice (K := L) S)
  let :
      DiscreteTopology
        (fullLogHyperplaneDiagonalLattice L S) := by
    unfold fullLogHyperplaneDiagonalLattice
    infer_instance
  let e := fullLogSpaceContinuousEquivHyperplaneProd L S
  change
    DiscreteTopology
      (ZLattice.comap ℝ
        (fullLogHyperplaneDiagonalLattice L S)
        e.toLinearMap)
  exact
    ZLattice.comap_discreteTopology ℝ
      (fullLogHyperplaneDiagonalLattice L S)
      e.continuous e.injective

instance instIsZLattice_extendedFullLogLattice
    (S : Finset (HeightOneSpectrum (𝓞 L))) :
    IsZLattice ℝ (extendedFullLogLattice L S) := by
  let : Module.Finite ℤ
      (SUnitGroup.fullLogLattice (K := L) S) :=
    ZLattice.module_finite ℝ
      (SUnitGroup.fullLogLattice (K := L) S)
  let : Module.Free ℤ
      (SUnitGroup.fullLogLattice (K := L) S) :=
    ZLattice.module_free ℝ
      (SUnitGroup.fullLogLattice (K := L) S)
  let :
      DiscreteTopology
        (fullLogHyperplaneDiagonalLattice L S) := by
    unfold fullLogHyperplaneDiagonalLattice
    infer_instance
  let :
      IsZLattice ℝ
        (fullLogHyperplaneDiagonalLattice L S) := by
    unfold fullLogHyperplaneDiagonalLattice
    infer_instance
  let e := fullLogSpaceContinuousEquivHyperplaneProd L S
  change
    IsZLattice ℝ
      (ZLattice.comap ℝ
        (fullLogHyperplaneDiagonalLattice L S)
        e.toLinearMap)
  exact inferInstance

omit [NumberField K] in
/-- Under the coordinate splitting, the hyperplane component transforms
by the restricted Galois action. -/
theorem fullLogSpaceSplit_fst_smul
    {S : Finset (HeightOneSpectrum (𝓞 L))}
    (hS : IsGaloisStableFinitePlaces K L S)
    (σ : L ≃ₐ[K] L)
    (z : SUnitGroup.FullLogSpace (K := L) S) :
    letI := logPlaceMulAction K L S hS
    letI := fullLogSpaceDistribMulAction K L S hS
    letI := logHyperplaneDistribMulAction K L S hS
    (fullLogSpaceSplit L S (σ • z)).1 =
      σ • (fullLogSpaceSplit L S z).1 := by
  let := logPlaceMulAction K L S hS
  let := fullLogSpaceDistribMulAction K L S hS
  let := logHyperplaneDistribMulAction K L S hS
  apply Subtype.ext
  change
    σ • z -
        SUnitGroup.coordinateSum (K := L) S (σ • z) •
          normalizedLogDiagonal L S =
      σ •
        (z -
          SUnitGroup.coordinateSum (K := L) S z •
            normalizedLogDiagonal L S)
  rw [coordinateSum_smul K L hS]
  ext p
  rfl

omit [NumberField K] in
/-- Under the coordinate splitting, the diagonal coordinate is
Galois-invariant. -/
theorem fullLogSpaceSplit_snd_smul
    {S : Finset (HeightOneSpectrum (𝓞 L))}
    (hS : IsGaloisStableFinitePlaces K L S)
    (σ : L ≃ₐ[K] L)
    (z : SUnitGroup.FullLogSpace (K := L) S) :
    letI := logPlaceMulAction K L S hS
    letI := fullLogSpaceDistribMulAction K L S hS
    (fullLogSpaceSplit L S (σ • z)).2 =
      (fullLogSpaceSplit L S z).2 := by
  let := logPlaceMulAction K L S hS
  let := fullLogSpaceDistribMulAction K L S hS
  exact coordinateSum_smul K L hS σ z

omit [NumberField K] in
/-- The full logarithmic lattice with its adjoined diagonal direction is
stable under the place-permutation representation. -/
theorem extendedFullLogLattice_permutation_stable
    {S : Finset (HeightOneSpectrum (𝓞 L))}
    (hS : IsGaloisStableFinitePlaces K L S) :
    ∀ (σ : L ≃ₐ[K] L)
      (z : SUnitGroup.FullLogSpace (K := L) S),
      z ∈ extendedFullLogLattice L S →
        permutationRepresentation
            (logPlacePermutationHom K L S hS) σ z ∈
          extendedFullLogLattice L S := by
  let := sUnitMulDistribMulAction K L S hS
  let := additiveSUnitDistribMulAction K L S hS
  let := logPlaceMulAction K L S hS
  let := fullLogSpaceDistribMulAction K L S hS
  let := logHyperplaneDistribMulAction K L S hS
  intro σ z hz
  rw [permutationRepresentation_logPlace K L hS]
  change
    fullLogSpaceSplit L S z ∈
      fullLogHyperplaneDiagonalLattice L S at hz
  change
    fullLogSpaceSplit L S (σ • z) ∈
      fullLogHyperplaneDiagonalLattice L S
  let b :=
    fullLogHyperplaneDiagonalBasis L S
  have hzrepr :
      ∀ i, b.repr (fullLogSpaceSplit L S z) i ∈
        Set.range (algebraMap ℤ ℝ) := by
    apply (b.mem_span_iff_repr_mem ℤ _).mp
    exact hz
  apply (b.mem_span_iff_repr_mem ℤ _).mpr
  intro i
  cases i with
  | inl j =>
      have hzfirst :
          (fullLogSpaceSplit L S z).1 ∈
            SUnitGroup.fullLogLattice (K := L) S := by
        rw [←
          (Module.Free.chooseBasis ℤ
            (SUnitGroup.fullLogLattice
              (K := L) S)).ofZLatticeBasis_span ℝ]
        apply
          ((fullLogLatticeRealBasis L S).mem_span_iff_repr_mem
            ℤ _).mpr
        intro k
        simpa only [b, fullLogHyperplaneDiagonalBasis,
          Basis.prod_repr_inl] using hzrepr (Sum.inl k)
      have hstable :=
        fullLogLattice_smul_mem K L hS σ
          (fullLogSpaceSplit L S z).1 hzfirst
      have hspanstable :
          σ • (fullLogSpaceSplit L S z).1 ∈
            Submodule.span ℤ
              (Set.range (fullLogLatticeRealBasis L S)) := by
        simpa only [fullLogLatticeRealBasis,
          (Module.Free.chooseBasis ℤ
            (SUnitGroup.fullLogLattice
              (K := L) S)).ofZLatticeBasis_span ℝ] using hstable
      have hcoord :=
        ((fullLogLatticeRealBasis L S).mem_span_iff_repr_mem
          ℤ _).mp hspanstable j
      simpa only [b, fullLogHyperplaneDiagonalBasis,
        Basis.prod_repr_inl,
        fullLogSpaceSplit_fst_smul K L hS] using hcoord
  | inr j =>
      simpa only [b, fullLogHyperplaneDiagonalBasis,
        Basis.prod_repr_inr,
        fullLogSpaceSplit_snd_smul K L hS] using
        hzrepr (Sum.inr j)

attribute [local instance] instMulActionAlgEquivHeightOneSpectrumRingOfIntegers_solutions
/-- For the actual full logarithmic `S`-unit
lattice.  The Herbrand quotient is the product of the orders of the
stabilizers of the Galois orbits of logarithmic places. -/
theorem
    extendedFullLogLattice_herbrandQuotient_eq_stabilizerProduct
    (K L : Type) [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    {S : Finset (HeightOneSpectrum (𝓞 L))}
    (hS : IsGaloisStableFinitePlaces K L S)
    (σ : L ≃ₐ[K] L)
    (hgen : ∀ τ : L ≃ₐ[K] L,
      τ ∈ Subgroup.zpowers σ) :
    let ρ :=
      logPlacePermutationHom K L S hS
    letI _indexAction :
        MulAction (L ≃ₐ[K] L)
          (SUnitGroup.LogPlace (K := L) S) :=
      permutationMulAction ρ
    letI _ambientAction :
        DistribMulAction (L ≃ₐ[K] L)
          (extendedFullLogLattice L S) :=
      completePermutationLatticeDistribMulAction
        ρ (extendedFullLogLattice L S)
        (extendedFullLogLattice_permutation_stable
          K L hS)
    letI _ambientMultiplicativeAction :
        MulDistribMulAction (L ≃ₐ[K] L)
          (Multiplicative
            (extendedFullLogLattice L S)) :=
      multiplicativeDistribMulAction
    letI _orbitFintype :
        Fintype
          (MulAction.orbitRel.Quotient
            (L ≃ₐ[K] L)
            (SUnitGroup.LogPlace (K := L) S)) :=
      Fintype.ofFinite _
    letI _stabilizerFintype :
        ∀ ω :
            MulAction.orbitRel.Quotient
              (L ≃ₐ[K] L)
              (SUnitGroup.LogPlace (K := L) S),
          Fintype (permutationOrbitStabilizer ω) :=
      fun _ => Fintype.ofFinite _
    ∃ h :
        HerbrandQuotientDefined
          (L ≃ₐ[K] L)
          (Multiplicative
            (extendedFullLogLattice L S)) σ,
      @herbrandQuotient
          (L ≃ₐ[K] L)
          (Multiplicative
            (extendedFullLogLattice L S))
          _ _ _ _ σ h.1 h.2 =
        ∏ ω :
            MulAction.orbitRel.Quotient
              (L ≃ₐ[K] L)
              (SUnitGroup.LogPlace (K := L) S),
          (Fintype.card
            (permutationOrbitStabilizer ω) : ℚ) := by
  let ρ :=
    logPlacePermutationHom K L S hS
  exact
    completePermutationLattice_herbrandQuotient_eq_stabilizerProduct
      (G := L ≃ₐ[K] L)
      (ι := SUnitGroup.LogPlace (K := L) S)
      ρ (extendedFullLogLattice L S)
      (extendedFullLogLattice_permutation_stable
        K L hS) σ hgen

end FinitePlaceAction
end
end

section
-- module Solutions.OAIQ244_DUKE.AlgebraicNumberTheory_SUnit_Herbrand
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.DiscreteNthRootsSubgroup.instCommGroupSubtypeUnitsMemSubgroup _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.KummerTheory.finite_sUnit_nthPowerQuotient _root_.KummerTheory.nthRootsSubgroupFintype _root_.KummerTheory.primeCyclotomicBaseFiniteDimensional _root_.LocalFieldTheory.DiscreteValuationField.finite_nsmulAddKernel_padicInt_pi _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_multiplicative_nthPowerKernel _root_.LocalFieldTheory.finite_nsmulAddKernel_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.LubinTate.compatibleGroupFamiliesCommGroup _root_.LubinTate.compatibleGroupFamiliesGroup _root_.OAI.PrimeDegreePackets.ThetaConstruction.coordinateLattice_discrete _root_.OAI.PrimeDegreePackets.boundedRealFields_finite _root_.OAI.PrimeDegreePackets.diagonalLogAction _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.integralGroup_discrete _root_.OAI.PrimeDegreePackets.logSubgroup_discrete _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.OAI.PrimeDegreePackets.orderedLogSubgroup_discrete _root_.CyclicCohomology.binaryCoefficientFamilyCommGroup
attribute [-simp] _root_.IsDiscreteValuationRing.addVal_ringEquiv _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.OAI.PrimeDegreePackets.ThetaConstruction.schwartzCM_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

/-!
# The Herbrand quotient of the global S-unit group

This file computes the Herbrand quotient of the global `S`-unit group. It connects the actual
`S`-unit group to its logarithmic lattice, adds the invariant diagonal
integer direction, and combines the resulting exact sequences with the
permutation-lattice calculation.
-/

open scoped BigOperators Classical NumberField nonZeroDivisors Pointwise
open IsDedekindDomain Module

noncomputable section

open CyclicCohomology.ProfiniteCohomology.Herbrand
open CyclicCohomology

variable
    (K L : Type*) [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]

section LogarithmicQuotient

/-- The full logarithm as a surjective multiplicative homomorphism
from `S`-units onto the multiplicative logarithmic lattice. -/
noncomputable def sUnitFullLogMulHom
    (S : Finset (HeightOneSpectrum (𝓞 L))) :
    SUnitGroup (K := L) S →*
      Multiplicative
        (SUnitGroup.fullLogLattice (K := L) S) where
  toFun x :=
    Multiplicative.ofAdd
      ⟨SUnitGroup.fullLog (K := L) S
          (Additive.ofMul x), by
        rw [SUnitGroup.fullLogLattice_eq_range]
        exact ⟨Additive.ofMul x, rfl⟩⟩
  map_one' := by
    apply Multiplicative.toAdd.injective
    apply Subtype.ext
    exact map_zero
      (SUnitGroup.fullLog (K := L) S)
  map_mul' x y := by
    apply Multiplicative.toAdd.injective
    apply Subtype.ext
    exact map_add
      (SUnitGroup.fullLog (K := L) S)
      (Additive.ofMul x) (Additive.ofMul y)

/-- The multiplicative full logarithm is onto its defining lattice. -/
theorem sUnitFullLogMulHom_surjective
    (S : Finset (HeightOneSpectrum (𝓞 L))) :
    Function.Surjective
      (sUnitFullLogMulHom L S) := by
  intro z
  have hz :
      (Multiplicative.toAdd z :
          SUnitGroup.fullLogLattice (K := L) S).1 ∈
        LinearMap.range
          (SUnitGroup.fullLog (K := L) S).toIntLinearMap := by
    rw [← SUnitGroup.fullLogLattice_eq_range]
    exact
      (Multiplicative.toAdd z :
        SUnitGroup.fullLogLattice (K := L) S).2
  obtain ⟨x, hx⟩ := hz
  refine ⟨Additive.toMul x, ?_⟩
  apply Multiplicative.toAdd.injective
  apply Subtype.ext
  change
    SUnitGroup.fullLog (K := L) S x =
      (Multiplicative.toAdd z :
        SUnitGroup.fullLogLattice (K := L) S).1
  exact hx

/-- The kernel of the multiplicative full logarithm is exactly the
torsion subgroup of the `S`-unit group. -/
theorem sUnitFullLogMulHom_ker
    (S : Finset (HeightOneSpectrum (𝓞 L))) :
    (sUnitFullLogMulHom L S).ker =
      CommGroup.torsion
        (SUnitGroup (K := L) S) := by
  ext x
  rw [MonoidHom.mem_ker]
  constructor
  · intro hx
    have hxlog :
        SUnitGroup.fullLog (K := L) S
            (Additive.ofMul x) = 0 := by
      have hx' :=
        congrArg
          (fun z :
              Multiplicative
                (SUnitGroup.fullLogLattice
                  (K := L) S) =>
            ((Multiplicative.toAdd z :
                SUnitGroup.fullLogLattice
                  (K := L) S) :
              SUnitGroup.LogHyperplane (K := L) S))
          hx
      exact hx'
    have hxt :=
      (SUnitGroup.fullLog_eq_zero_iff
        (K := L) S (Additive.ofMul x)).mp hxlog
    change IsOfFinOrder x
    exact isOfFinAddOrder_ofMul_iff.mp hxt
  · intro hxt
    apply Multiplicative.toAdd.injective
    apply Subtype.ext
    apply
      (SUnitGroup.fullLog_eq_zero_iff
        (K := L) S (Additive.ofMul x)).mpr
    change IsOfFinAddOrder (Additive.ofMul x)
    exact isOfFinAddOrder_ofMul_iff.mpr hxt

omit [NumberField K] in
/-- The multiplicative full logarithm is equivariant for the actual
Galois actions. -/
theorem sUnitFullLogMulHom_equivariant
    {S : Finset (HeightOneSpectrum (𝓞 L))}
    (hS : IsGaloisStableFinitePlaces K L S) :
    letI _sUnitAction :=
      sUnitMulDistribMulAction K L S hS
    letI _latticeAction :=
      fullLogLatticeDistribMulAction K L S hS
    letI _multiplicativeLatticeAction :
        MulDistribMulAction (L ≃ₐ[K] L)
          (Multiplicative
            (SUnitGroup.fullLogLattice (K := L) S)) :=
      multiplicativeDistribMulAction
    ∀ (σ : L ≃ₐ[K] L)
      (x : SUnitGroup (K := L) S),
      sUnitFullLogMulHom L S (σ • x) =
        σ • sUnitFullLogMulHom L S x := by
  let sUnitAction :=
    sUnitMulDistribMulAction K L S hS
  let additiveSUnitAction :=
    additiveSUnitDistribMulAction K L S hS
  let logPlaceAction :=
    logPlaceMulAction K L S hS
  let fullLogSpaceAction :=
    fullLogSpaceDistribMulAction K L S hS
  let logHyperplaneAction :=
    logHyperplaneDistribMulAction K L S hS
  let latticeAction :=
    fullLogLatticeDistribMulAction K L S hS
  let multiplicativeLatticeAction :
      MulDistribMulAction (L ≃ₐ[K] L)
        (Multiplicative
          (SUnitGroup.fullLogLattice (K := L) S)) :=
    multiplicativeDistribMulAction
  intro σ x
  apply Multiplicative.toAdd.injective
  apply Subtype.ext
  exact fullLog_smul K L hS σ (Additive.ofMul x)

omit [NumberField K] in
/-- The torsion subgroup is stable under Galois automorphisms. -/
theorem sUnitTorsion_stable
    {S : Finset (HeightOneSpectrum (𝓞 L))}
    (hS : IsGaloisStableFinitePlaces K L S) :
    letI _sUnitAction :=
      sUnitMulDistribMulAction K L S hS
    ∀ (σ : L ≃ₐ[K] L)
      (x : SUnitGroup (K := L) S),
      x ∈ CommGroup.torsion
          (SUnitGroup (K := L) S) →
        σ • x ∈ CommGroup.torsion
          (SUnitGroup (K := L) S) := by
  let sUnitAction :=
    sUnitMulDistribMulAction K L S hS
  intro σ x hx
  exact
    CommGroup.le_comap_torsion
      (MulDistribMulAction.toMonoidHom
        (SUnitGroup (K := L) S) σ) hx

/-- Exactness of torsion inclusion followed by the full logarithm. -/
theorem sUnitTorsion_fullLog_exact
    (S : Finset (HeightOneSpectrum (𝓞 L))) :
    ∀ x : SUnitGroup (K := L) S,
      sUnitFullLogMulHom L S x = 1 ↔
        ∃ t :
            CommGroup.torsion
              (SUnitGroup (K := L) S),
          (CommGroup.torsion
            (SUnitGroup (K := L) S)).subtype t = x := by
  intro x
  constructor
  · intro hx
    have hxt :
        x ∈ CommGroup.torsion
          (SUnitGroup (K := L) S) := by
      rw [← sUnitFullLogMulHom_ker L S]
      exact hx
    exact ⟨⟨x, hxt⟩, rfl⟩
  · rintro ⟨t, rfl⟩
    have ht :
        ((t :
            CommGroup.torsion
              (SUnitGroup (K := L) S)) :
          SUnitGroup (K := L) S) ∈
            (sUnitFullLogMulHom L S).ker := by
      rw [sUnitFullLogMulHom_ker L S]
      exact t.2
    exact ht

end LogarithmicQuotient

section DiagonalExtension

/-- Membership in the product lattice is exactly integrality in the
logarithmic lattice and in the diagonal coordinate. -/
theorem mem_fullLogHyperplaneDiagonalLattice_iff
    (S : Finset (HeightOneSpectrum (𝓞 L)))
    (z :
      SUnitGroup.LogHyperplane (K := L) S × ℝ) :
    z ∈ fullLogHyperplaneDiagonalLattice L S ↔
      z.1 ∈ SUnitGroup.fullLogLattice (K := L) S ∧
        ∃ n : ℤ, (n : ℝ) = z.2 := by
  let b :=
    fullLogHyperplaneDiagonalBasis L S
  constructor
  · intro hz
    have hzrepr :
        ∀ i, b.repr z i ∈
          Set.range (algebraMap ℤ ℝ) :=
      (b.mem_span_iff_repr_mem ℤ _).mp hz
    have hzfirst :
        z.1 ∈
          SUnitGroup.fullLogLattice (K := L) S := by
      rw [←
        (Module.Free.chooseBasis ℤ
          (SUnitGroup.fullLogLattice
            (K := L) S)).ofZLatticeBasis_span ℝ]
      apply
        ((fullLogLatticeRealBasis L S).mem_span_iff_repr_mem
          ℤ _).mpr
      intro j
      simpa only [b, fullLogHyperplaneDiagonalBasis,
        Basis.prod_repr_inl] using hzrepr (Sum.inl j)
    have hzsecond :=
      hzrepr (Sum.inr ())
    simp only [b, fullLogHyperplaneDiagonalBasis,
      Basis.prod_repr_inr, Basis.singleton_repr] at hzsecond
    exact ⟨hzfirst, hzsecond⟩
  · rintro ⟨hzfirst, ⟨n, hn⟩⟩
    apply (b.mem_span_iff_repr_mem ℤ _).mpr
    intro i
    cases i with
    | inl j =>
        have hzspan :
            z.1 ∈
              Submodule.span ℤ
                (Set.range (fullLogLatticeRealBasis L S)) := by
          simpa only [fullLogLatticeRealBasis,
            (Module.Free.chooseBasis ℤ
              (SUnitGroup.fullLogLattice
                (K := L) S)).ofZLatticeBasis_span ℝ] using
            hzfirst
        have hzcoord :=
          ((fullLogLatticeRealBasis L S).mem_span_iff_repr_mem
            ℤ _).mp hzspan j
        simpa only [b, fullLogHyperplaneDiagonalBasis,
          Basis.prod_repr_inl] using hzcoord
    | inr j =>
        refine ⟨n, ?_⟩
        simpa [b, fullLogHyperplaneDiagonalBasis,
          Basis.prod_repr_inr, Basis.singleton_repr,
          RingHom.id_apply] using hn

/-- The natural integral-linear map from the logarithmic lattice and
one diagonal integer coordinate to the extended full logarithmic
lattice. -/
noncomputable def fullLogLatticeProdIntToExtended
    (S : Finset (HeightOneSpectrum (𝓞 L))) :
    (SUnitGroup.fullLogLattice (K := L) S × ℤ) →ₗ[ℤ]
      extendedFullLogLattice L S := by
  let e :=
    fullLogSpaceEquivHyperplaneProd L S
  refine
    { toFun := fun z =>
        ⟨e.symm
            (((z.1 :
                SUnitGroup.fullLogLattice
                  (K := L) S) :
              SUnitGroup.LogHyperplane (K := L) S),
              (z.2 : ℝ)), ?_⟩
      map_add' := ?_
      map_smul' := ?_ }
  · change
      fullLogSpaceSplit L S
          (e.symm
            (((z.1 :
                SUnitGroup.fullLogLattice
                  (K := L) S) :
              SUnitGroup.LogHyperplane (K := L) S),
              (z.2 : ℝ))) ∈
        fullLogHyperplaneDiagonalLattice L S
    rw [show
      fullLogSpaceSplit L S
          (e.symm
            (((z.1 :
                SUnitGroup.fullLogLattice
                  (K := L) S) :
              SUnitGroup.LogHyperplane (K := L) S),
              (z.2 : ℝ))) =
        (((z.1 :
            SUnitGroup.fullLogLattice
              (K := L) S) :
          SUnitGroup.LogHyperplane (K := L) S),
          (z.2 : ℝ)) by
      exact e.apply_symm_apply _]
    exact
      (mem_fullLogHyperplaneDiagonalLattice_iff
        L S _).mpr ⟨z.1.2, ⟨z.2, rfl⟩⟩
  · intro x y
    apply Subtype.ext
    change
      e.symm
          (((((x + y).1 :
              SUnitGroup.fullLogLattice
                (K := L) S) :
            SUnitGroup.LogHyperplane (K := L) S)),
            (((x + y).2 : ℤ) : ℝ)) =
        e.symm
            ((((x.1 :
                SUnitGroup.fullLogLattice
                  (K := L) S) :
              SUnitGroup.LogHyperplane (K := L) S),
              (x.2 : ℝ))) +
          e.symm
            ((((y.1 :
                SUnitGroup.fullLogLattice
                  (K := L) S) :
              SUnitGroup.LogHyperplane (K := L) S),
              (y.2 : ℝ)))
    rw [← e.symm.map_add]
    congr 1
    ext <;> simp
  · intro n x
    apply Subtype.ext
    change
      e.symm
          (((((n • x).1 :
              SUnitGroup.fullLogLattice
                (K := L) S) :
            SUnitGroup.LogHyperplane (K := L) S)),
            ((((n • x).2 : ℤ) : ℝ))) =
        n •
          e.symm
            ((((x.1 :
                SUnitGroup.fullLogLattice
                  (K := L) S) :
              SUnitGroup.LogHyperplane (K := L) S),
              (x.2 : ℝ)))
    rw [← map_zsmul]
    congr 1
    ext <;> simp

/-- The preceding map is bijective. -/
theorem fullLogLatticeProdIntToExtended_bijective
    (S : Finset (HeightOneSpectrum (𝓞 L))) :
    Function.Bijective
      (fullLogLatticeProdIntToExtended L S) := by
  let e :=
    fullLogSpaceEquivHyperplaneProd L S
  constructor
  · intro x y hxy
    have hxy' :=
      congrArg
        (fun z : extendedFullLogLattice L S =>
          e (z :
            SUnitGroup.FullLogSpace (K := L) S))
        hxy
    have hpairs :
        (((x.1 :
              SUnitGroup.fullLogLattice
                (K := L) S) :
            SUnitGroup.LogHyperplane (K := L) S),
            (x.2 : ℝ)) =
          (((y.1 :
              SUnitGroup.fullLogLattice
                (K := L) S) :
            SUnitGroup.LogHyperplane (K := L) S),
            (y.2 : ℝ)) := by
      change
        e (e.symm
            (((x.1 :
                SUnitGroup.fullLogLattice
                  (K := L) S) :
              SUnitGroup.LogHyperplane (K := L) S),
              (x.2 : ℝ))) =
          e (e.symm
            (((y.1 :
                SUnitGroup.fullLogLattice
                  (K := L) S) :
              SUnitGroup.LogHyperplane (K := L) S),
              (y.2 : ℝ))) at hxy'
      simpa only [e, LinearEquiv.apply_symm_apply] using hxy'
    apply Prod.ext
    · apply Subtype.ext
      exact congrArg Prod.fst hpairs
    · have hs :
          (x.2 : ℝ) = (y.2 : ℝ) :=
        congrArg Prod.snd hpairs
      exact Int.cast_injective hs
  · intro y
    have hy :
        fullLogSpaceSplit L S
            (y :
              SUnitGroup.FullLogSpace (K := L) S) ∈
          fullLogHyperplaneDiagonalLattice L S :=
      y.2
    obtain ⟨hyfirst, n, hn⟩ :=
      (mem_fullLogHyperplaneDiagonalLattice_iff
        L S _).mp hy
    let x :
        SUnitGroup.fullLogLattice (K := L) S × ℤ :=
      (⟨(fullLogSpaceSplit L S
          (y :
            SUnitGroup.FullLogSpace (K := L) S)).1,
        hyfirst⟩, n)
    refine ⟨x, ?_⟩
    apply Subtype.ext
    apply e.injective
    change
      e (e.symm
          (((x.1 :
              SUnitGroup.fullLogLattice
                (K := L) S) :
            SUnitGroup.LogHyperplane (K := L) S),
            (x.2 : ℝ))) =
        e (y :
          SUnitGroup.FullLogSpace (K := L) S)
    rw [e.apply_symm_apply]
    change
      ((fullLogSpaceSplit L S
          (y :
            SUnitGroup.FullLogSpace (K := L) S)).1,
        (n : ℝ)) =
      fullLogSpaceSplit L S
        (y :
          SUnitGroup.FullLogSpace (K := L) S)
    exact Prod.ext rfl hn

/-- Integral-linear decomposition of the extended lattice into the
logarithmic lattice and one integer diagonal direction. -/
noncomputable def extendedFullLogLatticeEquivProdInt
    (S : Finset (HeightOneSpectrum (𝓞 L))) :
    extendedFullLogLattice L S ≃ₗ[ℤ]
      (SUnitGroup.fullLogLattice (K := L) S × ℤ) :=
  (LinearEquiv.ofBijective
    (fullLogLatticeProdIntToExtended L S)
    (fullLogLatticeProdIntToExtended_bijective L S)).symm

omit [NumberField K] in
/-- The map from logarithmic-plus-diagonal coordinates into the
extended lattice is equivariant. -/
theorem fullLogLatticeProdIntToExtended_equivariant
    {S : Finset (HeightOneSpectrum (𝓞 L))}
    (hS : IsGaloisStableFinitePlaces K L S) :
    let ρ :=
      logPlacePermutationHom K L S hS
    letI _indexAction :
        MulAction (L ≃ₐ[K] L)
          (SUnitGroup.LogPlace (K := L) S) :=
      permutationMulAction ρ
    letI _extendedAction :
        DistribMulAction (L ≃ₐ[K] L)
          (extendedFullLogLattice L S) :=
      completePermutationLatticeDistribMulAction
        ρ (extendedFullLogLattice L S)
        (extendedFullLogLattice_permutation_stable
          K L hS)
    letI _productAction :
        DistribMulAction (L ≃ₐ[K] L)
          (SUnitGroup.fullLogLattice (K := L) S × ℤ) :=
      fullLogLatticeProdIntDistribMulAction K L S hS
    ∀ (σ : L ≃ₐ[K] L)
      (z :
        SUnitGroup.fullLogLattice (K := L) S × ℤ),
      fullLogLatticeProdIntToExtended L S
          (_productAction.toMulAction.toSemigroupAction.toSMul.smul
            σ z) =
        _extendedAction.toMulAction.toSemigroupAction.toSMul.smul
          σ (fullLogLatticeProdIntToExtended L S z) := by
  dsimp only
  let ρ :=
    logPlacePermutationHom K L S hS
  let indexAction :
      MulAction (L ≃ₐ[K] L)
        (SUnitGroup.LogPlace (K := L) S) :=
    permutationMulAction ρ
  let sUnitAction :=
    sUnitMulDistribMulAction K L S hS
  let additiveSUnitAction :=
    additiveSUnitDistribMulAction K L S hS
  let logPlaceAction :=
    logPlaceMulAction K L S hS
  let fullLogSpaceAction :=
    fullLogSpaceDistribMulAction K L S hS
  let logHyperplaneAction :=
    logHyperplaneDistribMulAction K L S hS
  let fullLogLatticeAction :=
    fullLogLatticeDistribMulAction K L S hS
  let extendedAction :
      DistribMulAction (L ≃ₐ[K] L)
        (extendedFullLogLattice L S) :=
    completePermutationLatticeDistribMulAction
      ρ (extendedFullLogLattice L S)
      (extendedFullLogLattice_permutation_stable
        K L hS)
  let productAction :
      DistribMulAction (L ≃ₐ[K] L)
        (SUnitGroup.fullLogLattice (K := L) S × ℤ) :=
    fullLogLatticeProdIntDistribMulAction K L S hS
  intro σ z
  apply Subtype.ext
  apply fullLogSpaceSplit_injective L S
  apply Prod.ext
  · change
      (fullLogSpaceSplit L S
        ((fullLogSpaceEquivHyperplaneProd L S).symm
          (((σ • z.1 :
                SUnitGroup.fullLogLattice
                  (K := L) S) :
              SUnitGroup.LogHyperplane (K := L) S),
              (z.2 : ℝ)))).1 =
        (fullLogSpaceSplit L S
          (permutationRepresentation ρ σ
            ((fullLogSpaceEquivHyperplaneProd L S).symm
              (((z.1 :
                  SUnitGroup.fullLogLattice
                    (K := L) S) :
                SUnitGroup.LogHyperplane (K := L) S),
                (z.2 : ℝ))))).1
    rw [permutationRepresentation_logPlace K L hS,
      fullLogSpaceSplit_fst_smul K L hS]
    rw [show
      fullLogSpaceSplit L S
          ((fullLogSpaceEquivHyperplaneProd L S).symm
            (((σ • z.1 :
                  SUnitGroup.fullLogLattice
                    (K := L) S) :
                SUnitGroup.LogHyperplane (K := L) S),
              (z.2 : ℝ))) =
        (((σ • z.1 :
              SUnitGroup.fullLogLattice
                (K := L) S) :
            SUnitGroup.LogHyperplane (K := L) S),
          (z.2 : ℝ)) by
      exact
        (fullLogSpaceEquivHyperplaneProd L S).apply_symm_apply _]
    rw [show
      fullLogSpaceSplit L S
          ((fullLogSpaceEquivHyperplaneProd L S).symm
            (((z.1 :
                  SUnitGroup.fullLogLattice
                    (K := L) S) :
                SUnitGroup.LogHyperplane (K := L) S),
              (z.2 : ℝ))) =
        (((z.1 :
              SUnitGroup.fullLogLattice
                (K := L) S) :
            SUnitGroup.LogHyperplane (K := L) S),
          (z.2 : ℝ)) by
      exact
        (fullLogSpaceEquivHyperplaneProd L S).apply_symm_apply _]
    change
      σ • (z.1 :
          SUnitGroup.LogHyperplane (K := L) S) =
        σ • (z.1 :
          SUnitGroup.LogHyperplane (K := L) S)
    rfl
  · change
      (fullLogSpaceSplit L S
        ((fullLogSpaceEquivHyperplaneProd L S).symm
          (((σ • z.1 :
                SUnitGroup.fullLogLattice
                  (K := L) S) :
              SUnitGroup.LogHyperplane (K := L) S),
              (z.2 : ℝ)))).2 =
        (fullLogSpaceSplit L S
          (permutationRepresentation ρ σ
            ((fullLogSpaceEquivHyperplaneProd L S).symm
              (((z.1 :
                  SUnitGroup.fullLogLattice
                    (K := L) S) :
                SUnitGroup.LogHyperplane (K := L) S),
                (z.2 : ℝ))))).2
    rw [permutationRepresentation_logPlace K L hS,
      fullLogSpaceSplit_snd_smul K L hS]
    rw [show
      fullLogSpaceSplit L S
          ((fullLogSpaceEquivHyperplaneProd L S).symm
            (((σ • z.1 :
                  SUnitGroup.fullLogLattice
                    (K := L) S) :
                SUnitGroup.LogHyperplane (K := L) S),
              (z.2 : ℝ))) =
        (((σ • z.1 :
              SUnitGroup.fullLogLattice
                (K := L) S) :
            SUnitGroup.LogHyperplane (K := L) S),
          (z.2 : ℝ)) by
      exact
        (fullLogSpaceEquivHyperplaneProd L S).apply_symm_apply _]
    rw [show
      fullLogSpaceSplit L S
          ((fullLogSpaceEquivHyperplaneProd L S).symm
            (((z.1 :
                  SUnitGroup.fullLogLattice
                    (K := L) S) :
                SUnitGroup.LogHyperplane (K := L) S),
              (z.2 : ℝ))) =
        (((z.1 :
              SUnitGroup.fullLogLattice
                (K := L) S) :
            SUnitGroup.LogHyperplane (K := L) S),
          (z.2 : ℝ)) by
      exact
        (fullLogSpaceEquivHyperplaneProd L S).apply_symm_apply _]

omit [NumberField K] in
/-- The integral decomposition of the extended lattice is equivariant. -/
theorem extendedFullLogLatticeEquivProdInt_equivariant
    {S : Finset (HeightOneSpectrum (𝓞 L))}
    (hS : IsGaloisStableFinitePlaces K L S) :
    let ρ :=
      logPlacePermutationHom K L S hS
    letI _indexAction :
        MulAction (L ≃ₐ[K] L)
          (SUnitGroup.LogPlace (K := L) S) :=
      permutationMulAction ρ
    letI _extendedAction :
        DistribMulAction (L ≃ₐ[K] L)
          (extendedFullLogLattice L S) :=
      completePermutationLatticeDistribMulAction
        ρ (extendedFullLogLattice L S)
        (extendedFullLogLattice_permutation_stable
          K L hS)
    letI _productAction :
        DistribMulAction (L ≃ₐ[K] L)
          (SUnitGroup.fullLogLattice (K := L) S × ℤ) :=
      fullLogLatticeProdIntDistribMulAction K L S hS
    ∀ (σ : L ≃ₐ[K] L)
      (x : extendedFullLogLattice L S),
      extendedFullLogLatticeEquivProdInt L S
          (_extendedAction.toMulAction.toSemigroupAction.toSMul.smul
            σ x) =
        _productAction.toMulAction.toSemigroupAction.toSMul.smul
          σ (extendedFullLogLatticeEquivProdInt L S x) := by
  dsimp only
  let ρ :=
    logPlacePermutationHom K L S hS
  let indexAction :
      MulAction (L ≃ₐ[K] L)
        (SUnitGroup.LogPlace (K := L) S) :=
    permutationMulAction ρ
  let sUnitAction :=
    sUnitMulDistribMulAction K L S hS
  let additiveSUnitAction :=
    additiveSUnitDistribMulAction K L S hS
  let logPlaceAction :=
    logPlaceMulAction K L S hS
  let fullLogSpaceAction :=
    fullLogSpaceDistribMulAction K L S hS
  let logHyperplaneAction :=
    logHyperplaneDistribMulAction K L S hS
  let fullLogLatticeAction :=
    fullLogLatticeDistribMulAction K L S hS
  let extendedAction :
      DistribMulAction (L ≃ₐ[K] L)
        (extendedFullLogLattice L S) :=
    completePermutationLatticeDistribMulAction
      ρ (extendedFullLogLattice L S)
      (extendedFullLogLattice_permutation_stable
        K L hS)
  let productAction :
      DistribMulAction (L ≃ₐ[K] L)
        (SUnitGroup.fullLogLattice (K := L) S × ℤ) :=
    fullLogLatticeProdIntDistribMulAction K L S hS
  intro σ x
  let e :=
    extendedFullLogLatticeEquivProdInt L S
  apply e.symm.injective
  have hmap :=
    fullLogLatticeProdIntToExtended_equivariant
      K L hS σ (e x)
  change
    e.symm
        (productAction.toMulAction.toSemigroupAction.toSMul.smul
          σ (e x)) =
      extendedAction.toMulAction.toSemigroupAction.toSMul.smul
        σ (e.symm (e x)) at hmap
  rw [e.symm_apply_apply, hmap,
    e.symm_apply_apply]

end DiagonalExtension

section LogLatticeHerbrand

/-- Inclusion of the logarithmic lattice as the first factor of the
logarithmic-plus-diagonal lattice, in multiplicative notation. -/
def fullLogLatticeProdIntIncl
    (S : Finset (HeightOneSpectrum (𝓞 L))) :
    Multiplicative
        (SUnitGroup.fullLogLattice (K := L) S) →*
      Multiplicative
        (SUnitGroup.fullLogLattice (K := L) S × ℤ) where
  toFun z :=
    Multiplicative.ofAdd
      (Multiplicative.toAdd z, 0)
  map_one' := rfl
  map_mul' _ _ := rfl

/-- Projection from the logarithmic-plus-diagonal lattice to its
integer diagonal coordinate, in multiplicative notation. -/
def fullLogLatticeProdIntProj
    (S : Finset (HeightOneSpectrum (𝓞 L))) :
    Multiplicative
        (SUnitGroup.fullLogLattice (K := L) S × ℤ) →*
      Multiplicative ℤ where
  toFun z :=
    Multiplicative.ofAdd
      (Multiplicative.toAdd z).2
  map_one' := rfl
  map_mul' _ _ := rfl

/-- The multiplicative equivalence induced by the integral
decomposition of the extended lattice. -/
noncomputable def extendedFullLogLatticeMulEquivProdInt
    (S : Finset (HeightOneSpectrum (𝓞 L))) :
    Multiplicative (extendedFullLogLattice L S) ≃*
      Multiplicative
        (SUnitGroup.fullLogLattice (K := L) S × ℤ) :=
  (extendedFullLogLatticeEquivProdInt L S).toAddEquiv.toMultiplicative

omit [NumberField K] in
/-- The multiplicative form of the integral decomposition is
Galois-equivariant. -/
theorem extendedFullLogLatticeMulEquivProdInt_equivariant
    {S : Finset (HeightOneSpectrum (𝓞 L))}
    (hS : IsGaloisStableFinitePlaces K L S) :
    let ρ :=
      logPlacePermutationHom K L S hS
    letI _indexAction :
        MulAction (L ≃ₐ[K] L)
          (SUnitGroup.LogPlace (K := L) S) :=
      permutationMulAction ρ
    letI _extendedAction :
        DistribMulAction (L ≃ₐ[K] L)
          (extendedFullLogLattice L S) :=
      completePermutationLatticeDistribMulAction
        ρ (extendedFullLogLattice L S)
        (extendedFullLogLattice_permutation_stable
          K L hS)
    letI _extendedMultiplicativeAction :
        MulDistribMulAction (L ≃ₐ[K] L)
          (Multiplicative
            (extendedFullLogLattice L S)) :=
      multiplicativeDistribMulAction
    letI _productAction :
        DistribMulAction (L ≃ₐ[K] L)
          (SUnitGroup.fullLogLattice (K := L) S × ℤ) :=
      fullLogLatticeProdIntDistribMulAction K L S hS
    letI _productMultiplicativeAction :
        MulDistribMulAction (L ≃ₐ[K] L)
          (Multiplicative
            (SUnitGroup.fullLogLattice (K := L) S × ℤ)) :=
      multiplicativeDistribMulAction
    ∀ (σ : L ≃ₐ[K] L)
      (x : Multiplicative (extendedFullLogLattice L S)),
      extendedFullLogLatticeMulEquivProdInt L S
          (_extendedMultiplicativeAction.toMulAction.toSemigroupAction.toSMul.smul
            σ x) =
        _productMultiplicativeAction.toMulAction.toSemigroupAction.toSMul.smul
          σ (extendedFullLogLatticeMulEquivProdInt L S x) := by
  dsimp only
  let ρ :=
    logPlacePermutationHom K L S hS
  let indexAction :
      MulAction (L ≃ₐ[K] L)
        (SUnitGroup.LogPlace (K := L) S) :=
    permutationMulAction ρ
  let sUnitAction :=
    sUnitMulDistribMulAction K L S hS
  let additiveSUnitAction :=
    additiveSUnitDistribMulAction K L S hS
  let logPlaceAction :=
    logPlaceMulAction K L S hS
  let fullLogSpaceAction :=
    fullLogSpaceDistribMulAction K L S hS
  let logHyperplaneAction :=
    logHyperplaneDistribMulAction K L S hS
  let fullLogLatticeAction :=
    fullLogLatticeDistribMulAction K L S hS
  let extendedAction :
      DistribMulAction (L ≃ₐ[K] L)
        (extendedFullLogLattice L S) :=
    completePermutationLatticeDistribMulAction
      ρ (extendedFullLogLattice L S)
      (extendedFullLogLattice_permutation_stable
        K L hS)
  let extendedMultiplicativeAction :
      MulDistribMulAction (L ≃ₐ[K] L)
        (Multiplicative
          (extendedFullLogLattice L S)) :=
    multiplicativeDistribMulAction
  let productAction :
      DistribMulAction (L ≃ₐ[K] L)
        (SUnitGroup.fullLogLattice (K := L) S × ℤ) :=
    fullLogLatticeProdIntDistribMulAction K L S hS
  let productMultiplicativeAction :
      MulDistribMulAction (L ≃ₐ[K] L)
        (Multiplicative
          (SUnitGroup.fullLogLattice (K := L) S × ℤ)) :=
    multiplicativeDistribMulAction
  intro σ x
  apply Multiplicative.toAdd.injective
  change
    extendedFullLogLatticeEquivProdInt L S
        (extendedAction.toMulAction.toSemigroupAction.toSMul.smul
          σ (Multiplicative.toAdd x)) =
      productAction.toMulAction.toSemigroupAction.toSMul.smul
        σ
        (extendedFullLogLatticeEquivProdInt L S
          (Multiplicative.toAdd x))
  exact
    extendedFullLogLatticeEquivProdInt_equivariant
      K L hS σ (Multiplicative.toAdd x)

omit [NumberField K] in
/-- The first-factor inclusion is Galois-equivariant. -/
theorem fullLogLatticeProdIntIncl_equivariant
    {S : Finset (HeightOneSpectrum (𝓞 L))}
    (hS : IsGaloisStableFinitePlaces K L S) :
    letI _latticeAction :
        DistribMulAction (L ≃ₐ[K] L)
          (SUnitGroup.fullLogLattice (K := L) S) :=
      fullLogLatticeDistribMulAction K L S hS
    letI _latticeMultiplicativeAction :
        MulDistribMulAction (L ≃ₐ[K] L)
          (Multiplicative
            (SUnitGroup.fullLogLattice (K := L) S)) :=
      multiplicativeDistribMulAction
    letI _productAction :
        DistribMulAction (L ≃ₐ[K] L)
          (SUnitGroup.fullLogLattice (K := L) S × ℤ) :=
      fullLogLatticeProdIntDistribMulAction K L S hS
    letI _productMultiplicativeAction :
        MulDistribMulAction (L ≃ₐ[K] L)
          (Multiplicative
            (SUnitGroup.fullLogLattice (K := L) S × ℤ)) :=
      multiplicativeDistribMulAction
    ∀ (σ : L ≃ₐ[K] L)
      (z :
        Multiplicative
          (SUnitGroup.fullLogLattice (K := L) S)),
      fullLogLatticeProdIntIncl L S (σ • z) =
        σ • fullLogLatticeProdIntIncl L S z := by
  let latticeAction :=
    fullLogLatticeDistribMulAction K L S hS
  let latticeMultiplicativeAction :
      MulDistribMulAction (L ≃ₐ[K] L)
        (Multiplicative
          (SUnitGroup.fullLogLattice (K := L) S)) :=
    multiplicativeDistribMulAction
  let productAction :
      DistribMulAction (L ≃ₐ[K] L)
        (SUnitGroup.fullLogLattice (K := L) S × ℤ) :=
    fullLogLatticeProdIntDistribMulAction K L S hS
  let productMultiplicativeAction :
      MulDistribMulAction (L ≃ₐ[K] L)
        (Multiplicative
          (SUnitGroup.fullLogLattice (K := L) S × ℤ)) :=
    multiplicativeDistribMulAction
  intro σ z
  rfl

omit [NumberField K] in
/-- The diagonal projection is Galois-equivariant for the trivial
action on its integer target. -/
theorem fullLogLatticeProdIntProj_equivariant
    {S : Finset (HeightOneSpectrum (𝓞 L))}
    (hS : IsGaloisStableFinitePlaces K L S) :
    letI _latticeAction :
        DistribMulAction (L ≃ₐ[K] L)
          (SUnitGroup.fullLogLattice (K := L) S) :=
      fullLogLatticeDistribMulAction K L S hS
    letI _productAction :
        DistribMulAction (L ≃ₐ[K] L)
          (SUnitGroup.fullLogLattice (K := L) S × ℤ) :=
      fullLogLatticeProdIntDistribMulAction K L S hS
    letI _productMultiplicativeAction :
        MulDistribMulAction (L ≃ₐ[K] L)
          (Multiplicative
            (SUnitGroup.fullLogLattice (K := L) S × ℤ)) :=
      multiplicativeDistribMulAction
    letI _integerAction :
        MulDistribMulAction (L ≃ₐ[K] L)
          (Multiplicative ℤ) :=
      trivialIntMulDistribMulAction (L ≃ₐ[K] L)
    ∀ (σ : L ≃ₐ[K] L)
      (z :
        Multiplicative
          (SUnitGroup.fullLogLattice (K := L) S × ℤ)),
      fullLogLatticeProdIntProj L S (σ • z) =
        σ • fullLogLatticeProdIntProj L S z := by
  let latticeAction :=
    fullLogLatticeDistribMulAction K L S hS
  let productAction :
      DistribMulAction (L ≃ₐ[K] L)
        (SUnitGroup.fullLogLattice (K := L) S × ℤ) :=
    fullLogLatticeProdIntDistribMulAction K L S hS
  let productMultiplicativeAction :
      MulDistribMulAction (L ≃ₐ[K] L)
        (Multiplicative
          (SUnitGroup.fullLogLattice (K := L) S × ℤ)) :=
    multiplicativeDistribMulAction
  let integerAction :
      MulDistribMulAction (L ≃ₐ[K] L)
        (Multiplicative ℤ) :=
    trivialIntMulDistribMulAction (L ≃ₐ[K] L)
  intro σ z
  rfl

/-- Exactness of the first-factor inclusion followed by the diagonal
projection. -/
theorem fullLogLatticeProdInt_exact
    (S : Finset (HeightOneSpectrum (𝓞 L))) :
    ∀ z :
        Multiplicative
          (SUnitGroup.fullLogLattice (K := L) S × ℤ),
      fullLogLatticeProdIntProj L S z = 1 ↔
        ∃ x :
            Multiplicative
              (SUnitGroup.fullLogLattice (K := L) S),
          fullLogLatticeProdIntIncl L S x = z := by
  intro z
  constructor
  · intro hz
    refine
      ⟨Multiplicative.ofAdd
          (Multiplicative.toAdd z).1, ?_⟩
    apply Multiplicative.toAdd.injective
    apply Prod.ext
    · rfl
    · exact (congrArg Multiplicative.toAdd hz).symm
  · rintro ⟨x, rfl⟩
    rfl

/-- The first-factor inclusion is injective. -/
theorem fullLogLatticeProdIntIncl_injective
    (S : Finset (HeightOneSpectrum (𝓞 L))) :
    Function.Injective
      (fullLogLatticeProdIntIncl L S) := by
  intro x y hxy
  apply Multiplicative.toAdd.injective
  exact
    congrArg
      (fun z :
          Multiplicative
            (SUnitGroup.fullLogLattice (K := L) S × ℤ) =>
        (Multiplicative.toAdd z).1) hxy

/-- The diagonal projection is surjective. -/
theorem fullLogLatticeProdIntProj_surjective
    (S : Finset (HeightOneSpectrum (𝓞 L))) :
    Function.Surjective
      (fullLogLatticeProdIntProj L S) := by
  intro z
  exact
    ⟨Multiplicative.ofAdd
        (0, Multiplicative.toAdd z), rfl⟩

end LogLatticeHerbrand
end
end

section
-- module Solutions.OAIQ244_DUKE.GlobalClassFieldTheory_GlobalClassFields_Conductor
attribute [-instance] _root_.ClassFormation.DegreeData.FrobeniusFixedFieldTower.extensionNormal _root_.ClassFormation.DegreeData.GaloisSubextension.extensionSubgroup_normalInstance _root_.ClassFormation.FiniteAbstractField.toFiniteResidueAbstractField_extensionNormal _root_.ClassFormation.FiniteCyclicSubextension.instNormalSubtypeMemSubgroupFieldExtensionSubgroupField _root_.ClassFormation.FiniteGaloisSubextension.extensionSubgroup_normalInstance _root_.ClassFormation.FiniteGaloisSubextension.extensionSubgroup_over_intermediate_normalInstance _root_.ClassFormation.FiniteGaloisSubextension.intermediateField_normalInstance _root_.ClassFormation.FiniteIntermediateField.galoisRefinement_normal _root_.ClassFormation.FiniteUnramifiedCyclicExtension.instNormalSubtypeMemSubgroupFieldExtensionSubgroupField _root_.ClassFormation.conjugateExtension_normal _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalClassFieldTheory.extensionSubgroupBase_normal _root_.LocalClassFieldTheory.finiteGaloisExtensionSubgroupOfEmbedding_normal _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionResidueField.instField _root_.RamificationTheory.HilbertRamification.ValuationSubring.inertiaGroup_normal _root_.RamificationTheory.HilbertRamification.ValuationSubring.ramificationGroupInInertiaAut_normal _root_.RamificationTheory.HilbertRamification.ValuationSubring.selectedResidueField.instAlgebra _root_.ValuationTheory.DiscreteValuationField.DVF.residueField.field _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.CyclicCohomology.binaryCoefficientFamilyCommGroup _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic
attribute [-simp] _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.IsDiscreteValuationRing.addVal_ringEquiv _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.OAI.PrimeDegreePackets.ThetaConstruction.schwartzCM_apply _root_.infinitePlace_mult_smul
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

/-!
# Narrow finite conductors

This file constructs the finite part of the conductor in the convention
where every real place has the positive ray condition.  It is therefore a
*narrow finite conductor*, not yet the full global conductor of an
arbitrary modulus with an archimedean component.

The narrow finite conductor is the gcd of all finite moduli whose ray
class fields contain the given class field.  On norm subgroups, those are
exactly the moduli `m` for which `C_K^m ≤ H`.

We construct the gcd rather than postulating it.  At each finite prime its
exponent is the least exponent occurring among all defining moduli.  A
single defining modulus bounds the support, so these pointwise minima
assemble into a genuine finitely supported modulus.
-/

open scoped NumberField Classical

noncomputable section

namespace GlobalClassFieldTheory
namespace GlobalClassFields

open NumberField IsDedekindDomain

variable {K : Type*} [Field K] [NumberField K]

/-- A modulus defines a ray class field containing the class field
corresponding to `H` exactly when its congruence subgroup lies in `H`. -/
def IsDefiningModulus
    (H : Subgroup (IdeleClassGroup K))
    (m : RayClass.Modulus K) : Prop :=
  m.congruenceSubgroup ≤ H

/-- An idèle-class subgroup for which a finite ray-class defining modulus
exists.  This is precisely the domain on which the narrow finite conductor
is defined. -/
abbrev ConductorialSubgroup
    (K : Type*) [Field K] [NumberField K] :=
  {H : Subgroup (IdeleClassGroup K) //
    ∃ m : RayClass.Modulus K, IsDefiningModulus H m}

/-- At every finite place, some defining full modulus supplies a finite
defining exponent.  This is the nonemptiness input for the pointwise finite
conductor minimum. -/
theorem exists_definingFiniteExponent
    (H : Subgroup (IdeleClassGroup K))
    (h : ∃ m, IsDefiningModulus H m)
    (v : HeightOneSpectrum (𝓞 K)) :
    ∃ n : ℕ, ∃ m : RayClass.Modulus K,
      IsDefiningModulus H m ∧ m.finitePart v = n := by
  let m := Classical.choose h
  exact ⟨m.finitePart v, m, Classical.choose_spec h, rfl⟩

namespace ConductorialSubgroup

/-- A chosen full modulus defining a conductorial subgroup. -/
noncomputable def chosenDefiningModulus
    (H : ConductorialSubgroup K) :
    RayClass.Modulus K :=
  Classical.choose H.2

/-- The chosen full defining modulus has the advertised defining property. -/
theorem chosenDefiningModulus_spec
    (H : ConductorialSubgroup K) :
    IsDefiningModulus H.1 H.chosenDefiningModulus :=
  Classical.choose_spec H.2

/-- The finite part of one chosen defining modulus, used to bound the
support of the narrow finite conductor. -/
noncomputable def narrowFiniteConductorBoundingModulus
    (H : ConductorialSubgroup K) :
    RayClass.FiniteModulus K :=
  H.chosenDefiningModulus.finitePart

/-- The least narrow finite conductor exponent at `v` among all defining
moduli. -/
noncomputable def narrowFiniteConductorExponent
  (H : ConductorialSubgroup K)
    (v : HeightOneSpectrum (𝓞 K)) : ℕ :=
  Nat.find (exists_definingFiniteExponent H.1 H.2 v)

/-- The least narrow finite conductor exponent is attained by an actual
defining modulus. -/
theorem narrowFiniteConductorExponent_spec
    (H : ConductorialSubgroup K)
    (v : HeightOneSpectrum (𝓞 K)) :
    ∃ m : RayClass.Modulus K,
      IsDefiningModulus H.1 m ∧
        m.finitePart v = H.narrowFiniteConductorExponent v :=
  Nat.find_spec (exists_definingFiniteExponent H.1 H.2 v)

/-- The narrow finite conductor exponent is no larger than the exponent in
any defining modulus. -/
theorem narrowFiniteConductorExponent_le
    (H : ConductorialSubgroup K)
    {m : RayClass.Modulus K}
    (hm : IsDefiningModulus H.1 m)
    (v : HeightOneSpectrum (𝓞 K)) :
    H.narrowFiniteConductorExponent v ≤ m.finitePart v := by
  exact Nat.find_min'
    (exists_definingFiniteExponent H.1 H.2 v)
    ⟨m, hm, rfl⟩

/-- The finite part of the conductor in the all-real-positive (narrow)
convention. -/
noncomputable def narrowFiniteConductor
    (H : ConductorialSubgroup K) :
    RayClass.FiniteModulus K where
  toFun := H.narrowFiniteConductorExponent
  support :=
    H.narrowFiniteConductorBoundingModulus.support.filter
      (fun v => H.narrowFiniteConductorExponent v ≠ 0)
  mem_support_toFun := by
    intro v
    simp only [Finset.mem_filter, Finsupp.mem_support_iff]
    constructor
    · exact fun hv => hv.2
    · intro hv
      refine ⟨?_, hv⟩
      intro hbound
      have hle :
          H.narrowFiniteConductorExponent v ≤
            H.narrowFiniteConductorBoundingModulus v := by
        simpa only [narrowFiniteConductorBoundingModulus] using
        H.narrowFiniteConductorExponent_le
          H.chosenDefiningModulus_spec v
      rw [hbound] at hle
      exact hv (Nat.eq_zero_of_le_zero hle)

/-- Evaluating the narrow finite conductor returns its finite local
conductor exponent. -/
@[simp]
theorem narrowFiniteConductor_apply
    (H : ConductorialSubgroup K)
    (v : HeightOneSpectrum (𝓞 K)) :
    H.narrowFiniteConductor v = H.narrowFiniteConductorExponent v :=
  rfl

/-- The narrow finite conductor divides every defining modulus
(equivalently, its exponents are pointwise no larger). -/
theorem narrowFiniteConductor_le
    (H : ConductorialSubgroup K)
    {m : RayClass.Modulus K}
    (hm : IsDefiningModulus H.1 m) :
    H.narrowFiniteConductor ≤ m.finitePart := by
  intro v
  exact H.narrowFiniteConductorExponent_le hm v

end ConductorialSubgroup

end GlobalClassFields
end GlobalClassFieldTheory
end
end

section
-- module Solutions.OAIQ244_DUKE.Ramification_Different
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_isCompleteDiscrete _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.HilbertRamification.Dedekind.basePrime_isPrime _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.DiscreteValuationField.Examples.Qp.padicDVRValuation_isRankOneDiscrete _root_.LocalFieldTheory.DiscreteValuationField.LocalField.residueField_charP_residueCharacteristic _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.RamificationTheory.HilbertRamification.Higher.lowerRamificationGroup.instNormal _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionFixedMaximalIdeal.instIsMaximal _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionResidueField.instField _root_.RamificationTheory.HilbertRamification.ValuationSubring.selectedResidueField.instAlgebra _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.RamificationTheory.HilbertRamification.CompleteDVF.decompositionGroupMulSemiringAction _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.chosenFinitePlaceBaseValuationIsNontrivial _root_.finiteLocalUnitsOpen _root_.relativeAdeleRingIntermediateAlgebra _root_.relativeAdeleRingTopIntermediateAlgebra
attribute [-simp] _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.IsDiscreteValuationRing.addVal_ringEquiv _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.coe_valuationSubringUnitsToFieldUnits_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.fieldUnitValueUnit_mul _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.fieldUnitValueUnit_one _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.mrangeRestrict_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.multiplicativeIntegerValuationOfUniformizer_val _root_.LocalFieldTheory.localIntegerValuationSubringEquiv_apply_coe _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.LocalFieldTheory.residueField_algebraMap_residue _root_.LubinTate.SameUniformizer.constantCoeff_inVariable _root_.OAI.PrimeDegreePackets.ThetaConstruction.schwartzCM_apply _root_.RamificationTheory.HilbertRamification.Higher.dvfValuationSubringUnitAut_apply _root_.RamificationTheory.HilbertRamification.Higher.lowerRamificationGroup_neg_one _root_.RamificationTheory.HilbertRamification.Higher.mem_dvfHigherPrincipalUnitGroup_iff _root_.RamificationTheory.HilbertRamification.Higher.mem_lowerRamificationGroup_iff _root_.RamificationTheory.HilbertRamification.Higher.mem_valuationSubringDisplacementSubalgebraOfUniqueExtension_iff _root_.RamificationTheory.HilbertRamification.Higher.realRamificationIdeal_nat _root_.RamificationTheory.HilbertRamification.Higher.realRamificationIdeal_neg_one _root_.RamificationTheory.HilbertRamification.Higher.valuationSubringAutOfUniqueExtension_apply_coe _root_.RamificationTheory.HilbertRamification.Higher.valuationSubringAutOfUniqueExtension_apply_inv_apply _root_.RamificationTheory.HilbertRamification.Higher.valuationSubringAutOfUniqueExtension_mul_apply _root_.RamificationTheory.HilbertRamification.Higher.valuationSubringAutOfUniqueExtension_one_apply _root_.infinitePlace_mult_smul
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

/-!
# Different and codifferent for valued finite extensions

This file specializes mathlib's Dedekind-domain different ideal to complete
DVF valuation rings.  The ideal itself remains mathlib's `differentIdeal`; the
extra API here connects it to the chosen valuation rings, the codifferent, and
the local unramified criterion.
-/

noncomputable section

universe u v w x

attribute [local instance] FractionRing.liftAlgebra FractionRing.isScalarTower_liftAlgebra

namespace RamificationTheory
namespace DiscreteValuationField

open ValuationTheory.DiscreteValuationField
open ValuationTheory.DiscreteValuationField.ValuedExtension

namespace ValuedExtension

variable {K : Type u} {L : Type w} [Field K] [Field L]
variable [Algebra K L] [FiniteDimensional K L]
variable (base : CompleteDVF.{u, v} K) (target : CompleteDVF.{w, x} L)
variable [base.valuation.HasExtension target.valuation]

/-- The different ideal with the torsion-free certificate supplied by finite
separability of complete-DVF extensions. -/
noncomputable def differentIdealOfFiniteSeparable
    [Algebra.IsSeparable K L]
    [IsScalarTower base.valuationSubring target.valuationSubring L] :
    Ideal target.valuationSubring :=
  @differentIdeal base.valuationSubring target.valuationSubring
    inferInstance inferInstance inferInstance inferInstance inferInstance
    (moduleIsTorsionFree_target_valuationSubring_of_finite_separable
      (K := K) (L := L) (base := base) (target := target))

/-- Finite-separable version of the top/different criterion for
unramifiedness. -/
theorem differentIdealOfFiniteSeparable_eq_top_iff_isUnramifiedAt
    [Algebra.IsSeparable K L]
    [IsScalarTower base.valuationSubring target.valuationSubring L] :
    (RamificationTheory.DiscreteValuationField.ValuedExtension.differentIdealOfFiniteSeparable base target) = ⊤ ↔
      Algebra.IsUnramifiedAt base.valuationSubring target.maximalIdeal := by
  unfold differentIdealOfFiniteSeparable
  let : IsIntegralClosure target.valuationSubring base.valuationSubring L :=
    target_valuationSubring_isIntegralClosure_of_finite_separable base target
  let : Module.Finite base.valuationSubring target.valuationSubring :=
    moduleFinite_target_valuationSubring_of_finite_separable base target
  let : Module.IsTorsionFree base.valuationSubring target.valuationSubring :=
    moduleIsTorsionFree_target_valuationSubring_of_finite_separable base target
  let : Algebra (FractionRing base.valuationSubring)
      (FractionRing target.valuationSubring) := FractionRing.liftAlgebra _ _
  let : Algebra.IsSeparable (FractionRing base.valuationSubring)
      (FractionRing target.valuationSubring) :=
    (RamificationTheory.DiscreteValuationField.ValuedExtension.fractionRing_isSeparable_of_finite_separable base target)
  exact (RamificationTheory.DiscreteValuationField.ValuedExtension.differentIdeal_eq_top_iff_isUnramifiedAt base target)

/-- In a monogenic finite separable complete-DVF extension, the derivative of
the minimal polynomial belongs to the finite-separable different ideal. -/
theorem aeval_derivative_mem_differentIdealOfFiniteSeparable
    [Algebra.IsSeparable K L]
    [IsScalarTower base.valuationSubring target.valuationSubring L]
    (z : target.valuationSubring)
    (hz : Algebra.adjoin K {(algebraMap target.valuationSubring L) z} = ⊤) :
    Polynomial.aeval z
        (Polynomial.derivative (minpoly base.valuationSubring z)) ∈
      (RamificationTheory.DiscreteValuationField.ValuedExtension.differentIdealOfFiniteSeparable base target) := by
  unfold differentIdealOfFiniteSeparable
  let : IsIntegralClosure target.valuationSubring base.valuationSubring L :=
    target_valuationSubring_isIntegralClosure_of_finite_separable base target
  let : Module.IsTorsionFree base.valuationSubring target.valuationSubring :=
    moduleIsTorsionFree_target_valuationSubring_of_finite_separable
      (K := K) (L := L) (base := base) (target := target)
  exact (RamificationTheory.DiscreteValuationField.ValuedExtension.aeval_derivative_mem_differentIdeal base target) z hz

/-- A monogenic finite separable complete-DVF extension is unramified when
an integral equation for its generator has unit derivative.  The equation
need not be the minimal polynomial: integrally closed divisibility transfers
the unit condition to the derivative of the minimal polynomial, which then
generates the different. -/
theorem isUnramifiedAt_of_aeval_derivative_isUnit
    [Algebra.IsSeparable K L]
    [IsScalarTower base.valuationSubring target.valuationSubring L]
    (z : target.valuationSubring)
    (hz : Algebra.adjoin K {(algebraMap target.valuationSubring L) z} = ⊤)
    (P : Polynomial base.valuationSubring)
    (hP : Polynomial.aeval z P = 0)
    (hPderiv :
      IsUnit (Polynomial.aeval z (Polynomial.derivative P))) :
    Algebra.IsUnramifiedAt base.valuationSubring target.maximalIdeal := by
  let : IsIntegralClosure target.valuationSubring
      base.valuationSubring L :=
    target_valuationSubring_isIntegralClosure_of_finite_separable
      base target
  let : Module.IsTorsionFree base.valuationSubring
      target.valuationSubring :=
    moduleIsTorsionFree_target_valuationSubring_of_finite_separable
      (K := K) (L := L) (base := base) (target := target)
  obtain ⟨Q, hQ⟩ :=
    minpoly.isIntegrallyClosed_dvd
      (IsIntegralClosure.isIntegral base.valuationSubring L z) hP
  have hderiv :
      Polynomial.aeval z (Polynomial.derivative P) =
        Polynomial.aeval z
            (Polynomial.derivative
              (minpoly base.valuationSubring z)) *
          Polynomial.aeval z Q := by
    rw [hQ, Polynomial.derivative_mul]
    simp
  have hminpolyDeriv :
      IsUnit
        (Polynomial.aeval z
          (Polynomial.derivative
            (minpoly base.valuationSubring z))) := by
    apply isUnit_of_mul_isUnit_left
    rw [← hderiv]
    exact hPderiv
  apply
    (differentIdealOfFiniteSeparable_eq_top_iff_isUnramifiedAt
      base target).1
  apply
    (differentIdealOfFiniteSeparable base target).eq_top_of_isUnit_mem
      (aeval_derivative_mem_differentIdealOfFiniteSeparable
        base target z hz)
  exact hminpolyDeriv

end ValuedExtension
end DiscreteValuationField
end RamificationTheory

end
end

section
-- module Solutions.OAIQ244_DUKE.Kummer_Concrete_LocalUnitKummerUnramified
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.HilbertRamification.Dedekind.basePrime_isPrime _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.DiscreteValuationField.LocalField.residueField_charP_residueCharacteristic _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.LubinTate.Valuations.exponentialValuationSubringIsLocalRing _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.RamificationTheory.HilbertRamification.Higher.lowerRamificationGroup.instNormal _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionFixedMaximalIdeal.instIsMaximal _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionFixedSubring.instIsLocalRing _root_.RamificationTheory.HilbertRamification.ValuationSubring.selectedResidueField.instAlgebra _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.RamificationTheory.HilbertRamification.CompleteDVF.decompositionGroupMulSemiringAction _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen _root_.relativeAdeleRingIntermediateAlgebra _root_.relativeAdeleRingTopIntermediateAlgebra
attribute [-simp] _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.IsDiscreteValuationRing.addVal_ringEquiv _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.coe_valuationSubringUnitsToFieldUnits_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.fieldUnitValueUnit_mul _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.fieldUnitValueUnit_one _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.mrangeRestrict_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.multiplicativeIntegerValuationOfUniformizer_val _root_.LocalFieldTheory.galoisGroupEquivResidueAlgEquivOfUnramifiedValuationOfIsIntegralClosure_arithmeticFrobenius _root_.LocalFieldTheory.galoisGroupEquivZModOfUnramifiedValuationNormalized_arithmeticFrobenius _root_.LocalFieldTheory.galoisGroupEquivZModOfUnramifiedValuationNormalized_arithmeticFrobenius_zpow _root_.LocalFieldTheory.galoisGroupResidueAlgEquivOfIsIntegralClosure_arithmeticFrobenius _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.LubinTate.SameUniformizer.constantCoeff_inVariable _root_.OAI.PrimeDegreePackets.ThetaConstruction.schwartzCM_apply _root_.RamificationTheory.HilbertRamification.Higher.dvfValuationSubringUnitAut_apply _root_.RamificationTheory.HilbertRamification.Higher.lowerRamificationGroup_neg_one _root_.RamificationTheory.HilbertRamification.Higher.mem_dvfHigherPrincipalUnitGroup_iff _root_.RamificationTheory.HilbertRamification.Higher.mem_lowerRamificationGroup_iff _root_.RamificationTheory.HilbertRamification.Higher.mem_valuationSubringDisplacementSubalgebraOfUniqueExtension_iff _root_.RamificationTheory.HilbertRamification.Higher.realRamificationIdeal_nat _root_.RamificationTheory.HilbertRamification.Higher.realRamificationIdeal_neg_one _root_.RamificationTheory.HilbertRamification.Higher.valuationSubringAutOfUniqueExtension_apply_coe _root_.RamificationTheory.HilbertRamification.Higher.valuationSubringAutOfUniqueExtension_apply_inv_apply _root_.RamificationTheory.HilbertRamification.Higher.valuationSubringAutOfUniqueExtension_mul_apply _root_.RamificationTheory.HilbertRamification.Higher.valuationSubringAutOfUniqueExtension_one_apply _root_.infinitePlace_mult_smul
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

/-!
# Unramified local unit Kummer generators

This file packages the complete-DVF derivative criterion for a field extension
generated by an `n`-th root of a unit, with `n` itself a unit in the base field.
The statement is independent of the global Kummer construction so it can be
reused by local reciprocity arguments.
-/

open scoped ValuativeRel
open LocalFieldTheory

noncomputable section

namespace KummerTheory

/-- A finite separable extension generated by an `n`-th root of a unit is
unramified when `n` is a unit in the base field. -/
theorem isUnramifiedValuedExtension_of_unit_kummer_generator
    {C F : Type}
    [Field C] [Field F] [Algebra C F]
    [FiniteDimensional C F]
    [Algebra.IsSeparable C F]
    [ValuativeRel C] [ValuativeRel F]
    [TopologicalSpace C] [TopologicalSpace F]
    [IsNonarchimedeanLocalField C]
    [IsNonarchimedeanLocalField F]
    [Valuation.HasExtension
      (ValuativeRel.valuation C) (ValuativeRel.valuation F)]
    [Algebra 𝒪[C] F]
    [Module.Finite 𝒪[C] 𝒪[F]]
    (n : ℕ+)
    (b : C)
    (beta : F)
    (hb : ValuativeRel.valuation C b = 1)
    (hn : ValuativeRel.valuation C ((n : ℕ) : C) = 1)
    (hbeta : ValuativeRel.valuation F beta = 1)
    (hpow : beta ^ (n : ℕ) = algebraMap C F b)
    (hgen : Algebra.adjoin C {beta} = ⊤) :
    LocalFieldTheory.IsNonarchimedeanLocalField.IsUnramifiedValuedExtension C F := by
  let vC := ValuativeRel.valuation C
  let vF := ValuativeRel.valuation F
  let base := LocalFieldTheory.localCompleteDVF C
  let target := LocalFieldTheory.localCompleteDVF F
  let : base.valuation.HasExtension target.valuation := by
    apply Valuation.HasExtension.ofComapInteger
    ext x
    change vF (algebraMap C F x) ≤ 1 ↔ vC x ≤ 1
    exact Valuation.HasExtension.val_map_le_one_iff vC vF x
  let : IsScalarTower base.valuationSubring
      target.valuationSubring F :=
    ValuationTheory.DiscreteValuationField.Valuation.valuationSubring_isScalarTower_of_hasExtension
      base.valuation target.valuation
  let bBase : base.valuationSubring := by
    refine ⟨b, ?_⟩
    change base.valuation b ≤ 1
    rw [LocalFieldTheory.localCompleteDVF_valuation_eq]
    exact hb.le
  let z : target.valuationSubring := by
    refine ⟨beta, ?_⟩
    change target.valuation beta ≤ 1
    rw [LocalFieldTheory.localCompleteDVF_valuation_eq]
    exact hbeta.le
  have hnBaseUnit :
      IsUnit ((n : ℕ) : base.valuationSubring) := by
    apply
      (Valuation.integer.integers base.valuation).isUnit_iff_valuation_eq_one.mpr
    change base.valuation ((n : ℕ) : C) = 1
    rw [LocalFieldTheory.localCompleteDVF_valuation_eq]
    exact hn
  have hzpow :
      z ^ (n : ℕ) =
        algebraMap base.valuationSubring target.valuationSubring bBase := by
    apply Subtype.ext
    change beta ^ (n : ℕ) = algebraMap C F b
    exact hpow
  have hzUnit : IsUnit z := by
    apply
      (Valuation.integer.integers target.valuation).isUnit_iff_valuation_eq_one.mpr
    change target.valuation beta = 1
    rw [LocalFieldTheory.localCompleteDVF_valuation_eq]
    exact hbeta
  let P : Polynomial base.valuationSubring :=
    Polynomial.X ^ (n : ℕ) - Polynomial.C bBase
  have hP : Polynomial.aeval z P = 0 := by
    simp [P, hzpow]
  have hPderiv :
      IsUnit (Polynomial.aeval z (Polynomial.derivative P)) := by
    have hderivative :
        Polynomial.derivative P =
          Polynomial.C ((n : ℕ) : base.valuationSubring) *
            Polynomial.X ^ ((n : ℕ) - 1) := by
      simp [P, Polynomial.derivative_X_pow]
    have hCUnit :
        IsUnit
          (Polynomial.aeval z
            (Polynomial.C ((n : ℕ) : base.valuationSubring))) :=
      hnBaseUnit.map
        ((Polynomial.aeval z).toRingHom.comp Polynomial.C)
    have hXUnit :
        IsUnit
          (Polynomial.aeval z
            ((Polynomial.X : Polynomial base.valuationSubring) ^
              ((n : ℕ) - 1))) := by
      simpa only [map_pow, Polynomial.aeval_X] using
        hzUnit.pow ((n : ℕ) - 1)
    rw [hderivative, map_mul]
    exact hCUnit.mul hXUnit
  have hzgen :
      Algebra.adjoin C {(algebraMap target.valuationSubring F) z} = ⊤ := by
    change Algebra.adjoin C {beta} = ⊤
    exact hgen
  have hunramifiedAt :
      Algebra.IsUnramifiedAt
        base.valuationSubring target.maximalIdeal :=
    RamificationTheory.DiscreteValuationField.ValuedExtension.isUnramifiedAt_of_aeval_derivative_isUnit
      base target z hzgen P hP hPderiv
  refine ⟨?_⟩
  change target.maximalIdeal.ramificationIdx base.valuationSubring = 1
  let : Module.Finite
      base.valuationSubring target.valuationSubring := by
    change Module.Finite 𝒪[C] 𝒪[F]
    infer_instance
  let : Algebra.IsUnramifiedAt
      base.valuationSubring target.maximalIdeal := hunramifiedAt
  exact Ideal.ramificationIdx_eq_one_of_isUnramifiedAt

end KummerTheory
end
end

section
-- module Solutions.OAIQ244_DUKE.LocalClassFieldTheory_ClassFormation_LocalBlocks_Tensor
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.HilbertRamification.decompositionField_decompositionField_integerMap_isLocalHom _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.LubinTate.compatibleGroupFamiliesGroup _root_.OAI.PrimeDegreePackets.diagonalLogAction _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionResidueField.instField _root_.RamificationTheory.HilbertRamification.ValuationSubring.selectedResidueField.instAlgebra _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.RelativeIdeleGroup.relativeIdeleMulAction _root_.CyclicCohomology.binaryCoefficientFamilyCommGroup _root_.CyclicCohomology.instMulDistribMulActionBinaryCoefficientFamily _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen _root_.relativeAdeleRingIntermediateAlgebra _root_.relativeAdeleRingTopIntermediateAlgebra
attribute [-simp] _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.HilbertRamification.decompositionField_decompositionField_integerMap_apply _root_.HilbertRamification.decompositionField_decompositionField_residueFieldEquiv_apply _root_.HilbertRamification.mem_absoluteValueDecompositionField_iff _root_.IsDiscreteValuationRing.addVal_ringEquiv _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.LocalClassFieldTheory.mem_decompositionRightCosetsFinset _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.LocalFieldTheory.residueField_algebraMap_residue _root_.OAI.PrimeDegreePackets.ThetaConstruction.schwartzCM_apply _root_.doubleCosetExtension_mk _root_.extendAbsoluteValueExtensionFromIntermediate_apply _root_.infinitePlace_mult_smul _root_.mem_finitePlaceDecompositionGroup_iff _root_.restrictAbsoluteValueExtensionToIntermediate_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

/-!
# The tensor-product realization of a local induced block

This file connects the induced module in `LocalBlock` with the actual local
factor of the scalar-extended adele algebra.  The natural Galois action on
`K_v ⊗[K] L` is conjugation on the second tensor factor. The completion tensor-product theorem
identifies this algebra with the product of the completions above `v`.

The first part records the natural tensor action and the canonical
identifications between completions at conjugate absolute values.  These
identifications are the concrete source of the induced-module covariance in
the induced local-block calculation.
-/

open scoped TensorProduct

noncomputable section

namespace LocalClassFieldTheory

open AlgebraicNumberTheory.Valuations
open HilbertRamification
open CyclicCohomology

universe u v

variable {K : Type u} {L : Type v}
    [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L]
    [IsGalois K L]

/-- Evaluation at the chosen extension is covariant for left
multiplication by the decomposition group.  This is the defining
covariance relation of the induced module, obtained directly from
the localization Galois-group equivalence. -/
theorem localTensorEvaluation_conjugation_decomposition
    (vK : AbsoluteValue K ℝ) (hvK : vK.IsNontrivial)
    (w : AbsoluteValueExtension vK L)
    (h : absoluteValueDecompositionGroup K w.1)
    (g : L ≃ₐ[K] L)
    (z : LocalTensorAlgebra (L := L) vK) :
    letI hK := AbsoluteValue.extensionCompletionAlgebra (K := K) w.1
    letI : SMul K w.1.Completion := hK.toSMul
    letI := AbsoluteValue.completionAlgebra vK w.1 w.2
    localTensorEvaluation vK hvK w
        (localTensorConjugation vK (h.1 * g) z) =
      decompositionGroupEquivAlgebraicLocalizationAut
        vK hvK w h
        (localTensorEvaluation vK hvK w
          (localTensorConjugation vK g z)) := by
  let hK := AbsoluteValue.extensionCompletionAlgebra (K := K) w.1
  let _ : SMul K w.1.Completion := hK.toSMul
  let _ := AbsoluteValue.completionAlgebra vK w.1 w.2
  induction z using OAI.tensorInductionOn with
  | add x y hx hy =>
      simpa only [map_add] using congrArg₂ (· + ·) hx hy
  | tmul b x =>
      rw [localTensorConjugation_tmul,
        localTensorConjugation_tmul,
        localTensorEvaluation_tmul,
        localTensorEvaluation_tmul,
        map_mul,
        (decompositionGroupEquivAlgebraicLocalizationAut
          vK hvK w h).commutes,
        localizationRamificationGroups_decompositionGroupEquiv_toLocalization]
      rfl

/-- The canonical orbit-evaluation map from local tensor units to the
induced local block.  Its covariance is exactly
`localTensorEvaluation_conjugation_decomposition`. -/
noncomputable def localTensorOrbitHom
    (vK : AbsoluteValue K ℝ) (hvK : vK.IsNontrivial)
    (w : AbsoluteValueExtension vK L) :
    letI :=
      decompositionGroupLocalUnitsAction vK hvK w
    letI hK := AbsoluteValue.extensionCompletionAlgebra (K := K) w.1
    letI : SMul K w.1.Completion := hK.toSMul
    letI := AbsoluteValue.completionAlgebra vK w.1 w.2
    (LocalTensorAlgebra (L := L) vK)ˣ →*
      LocalPlaceBlock vK hvK w := by
  letI :=
    decompositionGroupLocalUnitsAction vK hvK w
  letI hK := AbsoluteValue.extensionCompletionAlgebra (K := K) w.1
  letI : SMul K w.1.Completion := hK.toSMul
  letI := AbsoluteValue.completionAlgebra vK w.1 w.2
  exact
    { toFun := fun z =>
        ⟨fun g =>
          Units.map
            (localTensorEvaluation vK hvK w).toMonoidHom
            (Units.map
              (localTensorConjugation vK g).toMonoidHom z),
          by
            intro h g
            apply Units.ext
            change
              localTensorEvaluation vK hvK w
                    (localTensorConjugation vK (h.1 * g)
                      (z : LocalTensorAlgebra (L := L) vK)) =
                decompositionGroupEquivAlgebraicLocalizationAut
                  vK hvK w h
                  (localTensorEvaluation vK hvK w
                    (localTensorConjugation vK g
                      (z : LocalTensorAlgebra (L := L) vK)))
            exact
              localTensorEvaluation_conjugation_decomposition
                vK hvK w h g z⟩
      map_one' := by
        apply Subtype.ext
        funext g
        apply Units.ext
        simp
      map_mul' := by
        intro x y
        apply Subtype.ext
        funext g
        apply Units.ext
        simp }

/-- Orbit evaluation intertwines natural conjugation on the tensor
factor with right translation on the induced module. -/
theorem localTensorOrbitHom_smul
    (vK : AbsoluteValue K ℝ) (hvK : vK.IsNontrivial)
    (w : AbsoluteValueExtension vK L)
    (τ : L ≃ₐ[K] L)
    (z : (LocalTensorAlgebra (L := L) vK)ˣ) :
    letI :=
      decompositionGroupLocalUnitsAction vK hvK w
    letI hK := AbsoluteValue.extensionCompletionAlgebra (K := K) w.1
    letI : SMul K w.1.Completion := hK.toSMul
    letI := AbsoluteValue.completionAlgebra vK w.1 w.2
    letI := localTensorUnitsAction (K := K) (L := L) vK
    localTensorOrbitHom vK hvK w (τ • z) =
      τ • localTensorOrbitHom vK hvK w z := by
  let _ :=
    decompositionGroupLocalUnitsAction vK hvK w
  let hK := AbsoluteValue.extensionCompletionAlgebra (K := K) w.1
  let _ : SMul K w.1.Completion := hK.toSMul
  let _ := AbsoluteValue.completionAlgebra vK w.1 w.2
  let _ := localTensorUnitsAction (K := K) (L := L) vK
  apply Subtype.ext
  funext g
  apply Units.ext
  change
    localTensorEvaluation vK hvK w
        (localTensorConjugation vK g
          (localTensorConjugation vK τ
            (z : LocalTensorAlgebra (L := L) vK))) =
      localTensorEvaluation vK hvK w
        (localTensorConjugation vK (g * τ)
          (z : LocalTensorAlgebra (L := L) vK))
  rw [localTensorConjugation_mul]

end LocalClassFieldTheory
end
end

section
-- module Solutions.OAIQ244_DUKE.LocalClassFieldTheory_ClassFormation_ArchimedeanNormQuotient
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.PrimeDegreePackets.diagonalLogAction _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen
attribute [-simp] _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.IsDiscreteValuationRing.addVal_ringEquiv _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.LocalClassFieldTheory.mem_decompositionRightCosetsFinset _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.OAI.PrimeDegreePackets.ThetaConstruction.schwartzCM_apply _root_.doubleCosetExtension_mk _root_.infinitePlace_mult_smul
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

/-!
# The real/complex norm quotient

At a ramified infinite place the local extension is `ℂ/ℝ`.  Its norm
subgroup consists exactly of the positive real units, so the sign map
identifies the norm quotient with `ℤˣ`, a group of order two.
-/

open LocalFieldTheory
open CyclicCohomology.ProfiniteCohomology.Herbrand
open CyclicCohomology

noncomputable section

namespace LocalClassFieldTheory

universe u v w z

open AlgebraicNumberTheory.Valuations
open HilbertRamification
open NumberField
open scoped Classical NumberField.LiesOver

variable
    {K L : Type}
    [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]

omit [NumberField K] [NumberField L] [FiniteDimensional K L]
    [IsGalois K L] in
/-- For an infinite place, the absolute-value decomposition
group is the ordinary Galois stabilizer of that place. -/
theorem absoluteValueDecompositionGroup_eq_infinitePlaceStabilizer
    (w : InfinitePlace L) :
    absoluteValueDecompositionGroup K w.1 =
      MulAction.stabilizer (L ≃ₐ[K] L) w := by
  ext σ
  constructor
  · intro hσ
    have hσi :
        σ⁻¹ ∈ absoluteValueDecompositionGroup K w.1 :=
      (absoluteValueDecompositionGroup K w.1).inv_mem hσ
    rw [mem_absoluteValueDecompositionGroup_iff_equivalent,
      LubinTate.Valuations.equivalentAbsoluteValues_iff_isEquiv] at hσi
    rw [MulAction.mem_stabilizer_iff]
    apply
      (InfinitePlace.eq_iff_isEquiv
        (w := σ • w) (v := w)).2
    exact hσi
  · intro hσ
    rw [MulAction.mem_stabilizer_iff] at hσ
    have hσi :
        σ⁻¹ ∈ absoluteValueDecompositionGroup K w.1 := by
      rw [mem_absoluteValueDecompositionGroup_iff_equivalent,
        LubinTate.Valuations.equivalentAbsoluteValues_iff_isEquiv]
      exact
        (InfinitePlace.eq_iff_isEquiv
          (w := σ • w) (v := w)).1 hσ
    simpa using
      (absoluteValueDecompositionGroup K w.1).inv_mem hσi

end LocalClassFieldTheory
end
end

section
-- module Solutions.OAIQ244_DUKE.LocalClassFieldTheory_ClassFormation_LocalBlocks_Family_H0
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.HilbertRamification.decompositionField_decompositionField_integerMap_isLocalHom _root_.KummerTheory.DiscreteNthRootsSubgroup.instCommGroupSubtypeUnitsMemSubgroup _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.DiscreteValuationField.finite_nsmulAddKernel_padicInt_pi _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_multiplicative_nthPowerKernel _root_.LocalFieldTheory.finite_nsmulAddKernel_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.LubinTate.compatibleGroupFamiliesCommGroup _root_.LubinTate.compatibleGroupFamiliesGroup _root_.OAI.PrimeDegreePackets.boundedRealFields_finite _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionResidueField.instField _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.CyclicCohomology.binaryCoefficientFamilyCommGroup _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

/-!
# Degree-zero cohomology of finite local-block families
-/

noncomputable section

namespace LocalClassFieldTheory

open AlgebraicNumberTheory.Valuations
open HilbertRamification
open CyclicCohomology.ProfiniteCohomology.Herbrand
open CyclicCohomology

universe u v w

variable {K : Type u} {L : Type v}
    [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]

/-- Degree-zero cohomology for a finite family of local blocks. -/
noncomputable def localBlockFamilyHerbrandH0Equiv
    {ι : Type w} [Fintype ι]
    (d : ι → LocalPlaceDatum K L)
    (σ : L ≃ₐ[K] L)
    (hgen : ∀ τ : L ≃ₐ[K] L,
      τ ∈ Subgroup.zpowers σ) :
    letI _localAction : ∀ i,
        MulDistribMulAction
          (absoluteValueDecompositionGroup K (d i).extension.1)
          (LocalizedCompletion
            (d i).base (d i).extension)ˣ :=
      fun i ↦ decompositionGroupLocalUnitsAction
        (d i).base (d i).base_isNontrivial
        (d i).extension
    letI _blockAction : ∀ i,
        MulDistribMulAction (L ≃ₐ[K] L)
          (LocalPlaceBlock
            (d i).base (d i).base_isNontrivial
            (d i).extension) :=
      fun i ↦ inducedMulDistribMulAction
        (absoluteValueDecompositionGroup K (d i).extension.1)
    letI _familyAction :
        MulDistribMulAction (L ≃ₐ[K] L)
          (LocalBlockFamily d) :=
      piMulDistribMulAction (L ≃ₐ[K] L)
        (fun i ↦ LocalPlaceBlock
          (d i).base (d i).base_isNontrivial
          (d i).extension)
    letI _decompositionFintype : ∀ i,
        Fintype
          (absoluteValueDecompositionGroup K
            (d i).extension.1) :=
      fun _ ↦ Fintype.ofFinite _
    HerbrandH0 (L ≃ₐ[K] L)
        (LocalBlockFamily d) ≃*
      ∀ i,
        HerbrandH0
          (absoluteValueDecompositionGroup K
            (d i).extension.1)
          (LocalizedCompletion
            (d i).base (d i).extension)ˣ := by
  letI localAction := localBlockFamilyLocalAction d
  letI blockAction := localBlockFamilyBlockAction d
  letI familyAction := localBlockFamilyCohomologyAction d
  letI decompositionFintype :=
    localBlockFamilyDecompositionFintype d
  exact
    (herbrandH0PiEquiv
      (G := L ≃ₐ[K] L)
      (fun i ↦ LocalPlaceBlock
        (d i).base (d i).base_isNontrivial
        (d i).extension)).trans
      (MulEquiv.piCongrRight fun i ↦
        localPlaceBlockHerbrandH0Equiv
          (d i).base (d i).base_isNontrivial
          (d i).extension σ hgen)

end LocalClassFieldTheory
end
end

section
-- module Solutions.OAIQ244_DUKE.LocalClassFieldTheory_ClassFormation_LocalBlocks_Family_HMinusOne
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.HilbertRamification.decompositionField_decompositionField_integerMap_isLocalHom _root_.KummerTheory.DiscreteNthRootsSubgroup.instCommGroupSubtypeUnitsMemSubgroup _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.DiscreteValuationField.finite_nsmulAddKernel_padicInt_pi _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_multiplicative_nthPowerKernel _root_.LocalFieldTheory.finite_nsmulAddKernel_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.LubinTate.compatibleGroupFamiliesCommGroup _root_.LubinTate.compatibleGroupFamiliesGroup _root_.OAI.PrimeDegreePackets.boundedRealFields_finite _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionResidueField.instField _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.CyclicCohomology.binaryCoefficientFamilyCommGroup _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

/-!
# Degree-minus-one cohomology of finite local-block families
-/

noncomputable section

namespace LocalClassFieldTheory

open AlgebraicNumberTheory.Valuations
open HilbertRamification
open CyclicCohomology.ProfiniteCohomology.Herbrand
open CyclicCohomology

universe u v w

variable {K : Type u} {L : Type v}
    [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]

/-- Degree-minus-one cohomology for a finite family of local blocks. -/
noncomputable def localBlockFamilyHerbrandHMinusOneEquiv
    {ι : Type w} [Fintype ι]
    (d : ι → LocalPlaceDatum K L)
    (σ : L ≃ₐ[K] L)
    (hgen : ∀ τ : L ≃ₐ[K] L,
      τ ∈ Subgroup.zpowers σ) :
    letI _localAction : ∀ i,
        MulDistribMulAction
          (absoluteValueDecompositionGroup K (d i).extension.1)
          (LocalizedCompletion
            (d i).base (d i).extension)ˣ :=
      fun i ↦ decompositionGroupLocalUnitsAction
        (d i).base (d i).base_isNontrivial
        (d i).extension
    letI _blockAction : ∀ i,
        MulDistribMulAction (L ≃ₐ[K] L)
          (LocalPlaceBlock
            (d i).base (d i).base_isNontrivial
            (d i).extension) :=
      fun i ↦ inducedMulDistribMulAction
        (absoluteValueDecompositionGroup K (d i).extension.1)
    letI _familyAction :
        MulDistribMulAction (L ≃ₐ[K] L)
          (LocalBlockFamily d) :=
      piMulDistribMulAction (L ≃ₐ[K] L)
        (fun i ↦ LocalPlaceBlock
          (d i).base (d i).base_isNontrivial
          (d i).extension)
    letI _decompositionFintype : ∀ i,
        Fintype
          (absoluteValueDecompositionGroup K
            (d i).extension.1) :=
      fun _ ↦ Fintype.ofFinite _
    HerbrandHMinusOne (L ≃ₐ[K] L)
        (LocalBlockFamily d) σ ≃*
      ∀ i,
        HerbrandHMinusOne
          (absoluteValueDecompositionGroup K
            (d i).extension.1)
          (LocalizedCompletion
            (d i).base (d i).extension)ˣ
          (subgroupGeneratorOfGenerator
            (absoluteValueDecompositionGroup K
              (d i).extension.1)
            σ hgen) := by
  letI localAction := localBlockFamilyLocalAction d
  letI blockAction := localBlockFamilyBlockAction d
  letI familyAction := localBlockFamilyCohomologyAction d
  letI decompositionFintype :=
    localBlockFamilyDecompositionFintype d
  exact
    (herbrandHMinusOnePiEquiv
      (G := L ≃ₐ[K] L)
      (fun i ↦ LocalPlaceBlock
        (d i).base (d i).base_isNontrivial
        (d i).extension) σ).trans
      (MulEquiv.piCongrRight fun i ↦
        localPlaceBlockHerbrandHMinusOneEquiv
          (d i).base (d i).base_isNontrivial
          (d i).extension σ hgen)

end LocalClassFieldTheory
end
end

section
-- module Solutions.OAIQ244_DUKE.LocalClassFieldTheory_Finite_LocalReciprocity_GeneralTowerNaturality
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen _root_.relativeAdeleRingIntermediateAlgebra _root_.relativeAdeleRingTopIntermediateAlgebra
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

/-!
# Restriction naturality in an arbitrary finite abelian tower

The fixed-separable-closure form of finite local reciprocity naturality is
transported here to an arbitrary tower `K ⊂ E ⊂ L`.  The two extensions are
realized compatibly in the chosen separable closure by first embedding `L`
and then restricting that embedding to `E`.  Abstract norm--residue
naturality then becomes the actual restriction homomorphism
`Gal(L/K) → Gal(E/K)`.
-/

noncomputable section

namespace LocalClassFieldTheory

open LocalFieldTheory RamificationTheory CyclicCohomology KummerTheory
open ClassFormation LocalClassFieldTheory
open scoped IsMulCommutative

abbrev towerAbsoluteUnits (K : Type) [Field K] :
    Rep ℤ (towerAbsoluteGalois K) :=
  intrinsicAbsoluteUnits K

abbrev towerAbstractBase (K : Type) [Field K] :
    ClosedSubgroup (towerAbsoluteGalois K) :=
  intrinsicAbstractBase K

end LocalClassFieldTheory
end
end

section
-- module Solutions.OAIQ244_DUKE.LocalField_NonarchimedeanLocalField_UnramifiedFrobenius
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.RamificationTheory.HilbertRamification.ValuationSubring.selectedResidueField.instAlgebra _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen _root_.relativeAdeleRingIntermediateAlgebra _root_.relativeAdeleRingTopIntermediateAlgebra
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

namespace LocalFieldTheory

/-!
# Actual unramified Frobenius

The arithmetic Frobenius is first defined as finite-field Frobenius on the
residue extension, then lifted to `Gal(L / K)` through the canonical
residue-action isomorphism for a finite unramified extension.
-/

noncomputable section

universe u

open scoped ValuativeRel
open _root_.LocalFieldTheory.IsNonarchimedeanLocalField

/-- The Galois group of a finite unramified extension is cyclic. -/
theorem isCyclic_galoisGroup_of_unramifiedValuation
    (K L : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] [Field L] [ValuativeRel L]
    [TopologicalSpace L] [IsNonarchimedeanLocalField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]
    [IsIntegralClosure 𝒪[L] 𝒪[K] L] [Module.Finite 𝒪[K] 𝒪[L]]
    [LocalFieldTheory.IsNonarchimedeanLocalField.IsUnramifiedValuedExtension K L] :
    IsCyclic Gal(L / K) := by
  rw [isCyclic_iff_exists_zpowers_eq_top]
  exact ⟨arithmeticFrobeniusOfUnramifiedValuation K L,
    arithmeticFrobeniusOfUnramifiedValuation_zpowers_eq_top K L⟩

end
end LocalFieldTheory
end

section
-- module Solutions.OAIQ244_DUKE.LubinTate_FormalModule_RecursiveCorrection
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.PrimeDegreePackets.boundedRealFields_finite _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.RamificationTheory.HilbertRamification.Higher.lowerRamificationGroup.instNormal _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.RamificationTheory.HilbertRamification.CompleteDVF.decompositionGroupMulSemiringAction _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

/-!
# Recursive monomial corrections for Lubin--Tate intertwiners

The coefficient selected in `RecursiveCoefficient` is inserted as a single
monomial.  This file proves that the insertion preserves the prescribed linear
term and cancels the defect coefficient in precisely that total degree.
-/

noncomputable section

open scoped BigOperators

universe u v w

namespace LubinTate
namespace SameUniformizer

open LocalFieldTheory.DiscreteValuationField

variable {K : Type u} [Field K]
variable {F : LocalField.{u, v} K} {π : F.valuationSubring}
variable {σ : Type w} [Fintype σ]

theorem linearInVariable_hasSubst
    (π : F.valuationSubring) :
    MvPowerSeries.HasSubst (linearInVariable (σ := σ) π) :=
  MvPowerSeries.hasSubst_of_constantCoeff_zero
    (linearInVariable_constantCoeff π)

end SameUniformizer
end LubinTate

end
end


