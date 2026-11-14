-- Prove2me | Definitions.Def_OAIQ244Duke119
-- name    : OAIQ244Duke119
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-14T02:23:03.842962+00:00
-- url     : https://prove2.me/theorems/8fda25f3-5bf7-42c7-82c9-da4d04446716
-- title:
--   Definitions bundle OAIQ244Duke119 of the split of OpenAI, Equidistribution of Prime-Degree Torus Packets with Arbitrary Local Type
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.DukePrimeDegree.prime_degree_packet_measure_equidistribution_unconditional` and `OAI.DukePrimeDegree.prime_degree_packet_measures_tendsto_haar_unconditional`, carved from OpenAI's openai/math development (OpenAI, *Equidistribution of Prime-Degree Torus Packets with Arbitrary Local Type*, OpenAI Math Release, September 24, 2026, result family 15, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 20 declarations of OpenAI's Lean: 11 definitions, 1 instance and 8 theorems. The definitions and types are `GlobalClassFieldTheory.Reciprocity.numberFieldTowerAbstractBaseFieldEquiv`, `GlobalClassFieldTheory.Reciprocity.numberFieldTowerAbstractTopFieldEquiv`, `GlobalClassFieldTheory.Reciprocity.numberFieldTowerBaseField`, `GlobalClassFieldTheory.Reciprocity.numberFieldTowerBaseSubgroup`, `GlobalClassFieldTheory.Reciprocity.numberFieldTowerFiniteAbstractField`, `GlobalClassFieldTheory.Reciprocity.numberFieldTowerLowerEmbedding`, `GlobalClassFieldTheory.Reciprocity.numberFieldTowerSeparableClosureBaseAlgebra`, `GlobalClassFieldTheory.Reciprocity.numberFieldTowerSeparableClosureEquivBaseSubgroup`, `GlobalClassFieldTheory.Reciprocity.numberFieldTowerSeparableClosureToBaseSubgroup`, `GlobalClassFieldTheory.Reciprocity.numberFieldTowerTopSubgroup`, `GlobalClassFieldTheory.Reciprocity.rationalFiniteNormQuotientEquivIdeleClassNormQuotient`.
--
--   **Sources.** They come from these modules of lean/OAI/NumberTheory, in whole or in part: `GlobalClassFieldTheory_Reciprocity_FiniteGaloisRealizationCore`, `GlobalClassFieldTheory_Reciprocity_FiniteGaloisRealizationNormQuotient`, `GlobalClassFieldTheory_Reciprocity_FiniteGaloisRealizationSubextension`, `GlobalClassFieldTheory_Reciprocity_IdeleClassDirectLimitNormQuotient`.
--
--   **Imports.** It imports the bundles `OAIQ244Duke091` and `OAIQ244Duke096` of this split.
--
--   **Imported by** (directly, in this split): the bundle `OAIQ244Duke098`.
-- source:
--   OpenAI, Equidistribution of Prime-Degree Torus Packets with Arbitrary Local Type, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 15; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Equidistribution-of-Prime-Degree-Torus-Packets-with-Arbitrary-Local-Type-September-24-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/NumberTheory at commit 7ef5c0c

import Mathlib
import Mathlib.Algebra.Algebra.Basic
import Mathlib.Algebra.Algebra.Pi
import Mathlib.Algebra.Algebra.Tower
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Category.ModuleCat.Basic
import Mathlib.Algebra.CharP.Algebra
import Mathlib.Algebra.CharP.Lemmas
import Mathlib.Algebra.CharP.Subring
import Mathlib.Algebra.Colimit.DirectLimit
import Mathlib.Algebra.EuclideanDomain.Basic
import Mathlib.Algebra.Exact.Basic
import Mathlib.Algebra.Group.Action.Basic
import Mathlib.Algebra.Group.Hom.Basic
import Mathlib.Algebra.Group.Int.TypeTags
import Mathlib.Algebra.Group.Pi.Basic
import Mathlib.Algebra.Group.Pi.Units
import Mathlib.Algebra.Group.Subgroup.Basic
import Mathlib.Algebra.Group.Subgroup.Ker
import Mathlib.Algebra.Group.Subgroup.Map
import Mathlib.Algebra.Group.Subgroup.Pointwise
import Mathlib.Algebra.Group.Submonoid.Units
import Mathlib.Algebra.Group.TransferInstance
import Mathlib.Algebra.Group.Units.Equiv
import Mathlib.Algebra.Group.Units.Hom
import Mathlib.Algebra.Module.Equiv.Basic
import Mathlib.Algebra.Module.LinearMap.Polynomial
import Mathlib.Algebra.Module.MinimalAxioms
import Mathlib.Algebra.Module.PID
import Mathlib.Algebra.Module.Shrink
import Mathlib.Algebra.Module.Torsion.Basic
import Mathlib.Algebra.Module.ZLattice.Basic
import Mathlib.Algebra.Module.ZMod
import Mathlib.Algebra.Order.Field.Power
import Mathlib.Algebra.Order.Group.Cyclic
import Mathlib.Algebra.Order.Hom.Units
import Mathlib.Algebra.Order.Ring.IsNonarchimedean
import Mathlib.Algebra.Order.WithTop.Untop0
import Mathlib.Algebra.Polynomial.Div
import Mathlib.Algebra.Polynomial.FieldDivision
import Mathlib.Algebra.Polynomial.Lifts
import Mathlib.Algebra.Ring.Pi
import Mathlib.Algebra.Ring.Subring.Basic
import Mathlib.Algebra.Ring.TransferInstance
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
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Finsupp
import Mathlib.Data.Int.ModEq
import Mathlib.Data.Int.WithZero
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Rat.Cast.CharZero
import Mathlib.Data.Rat.Lemmas
import Mathlib.Data.Set.Finite.Range
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.ZMod.QuotientGroup
import Mathlib.Data.ZMod.QuotientRing
import Mathlib.Dynamics.BirkhoffSum.Basic
import Mathlib.FieldTheory.AbsoluteGaloisGroup
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.FieldTheory.Finite.Extension
import Mathlib.FieldTheory.Finite.GaloisField
import Mathlib.FieldTheory.Galois.Abelian
import Mathlib.FieldTheory.Galois.Basic
import Mathlib.FieldTheory.Galois.GaloisClosure
import Mathlib.FieldTheory.Galois.Infinite
import Mathlib.FieldTheory.Galois.IsGaloisGroup
import Mathlib.FieldTheory.Galois.NormalBasis
import Mathlib.FieldTheory.Galois.Notation
import Mathlib.FieldTheory.Galois.Profinite
import Mathlib.FieldTheory.IntermediateField.Adjoin.Algebra
import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
import Mathlib.FieldTheory.IntermediateField.Algebraic
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.FieldTheory.IsSepClosed
import Mathlib.FieldTheory.KrullTopology
import Mathlib.FieldTheory.Minpoly.IsConjRoot
import Mathlib.FieldTheory.Minpoly.IsIntegrallyClosed
import Mathlib.FieldTheory.Normal.Basic
import Mathlib.FieldTheory.Normal.Closure
import Mathlib.FieldTheory.Perfect
import Mathlib.FieldTheory.PrimeField
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
import Mathlib.GroupTheory.QuotientGroup.Defs
import Mathlib.GroupTheory.QuotientGroup.Finite
import Mathlib.GroupTheory.SpecificGroups.Cyclic
import Mathlib.GroupTheory.Torsion
import Mathlib.GroupTheory.Transfer
import Mathlib.LinearAlgebra.Basis.SMul
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.LinearAlgebra.Charpoly.BaseChange
import Mathlib.LinearAlgebra.Determinant
import Mathlib.LinearAlgebra.Dimension.Basic
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Dimension.DivisionRing
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.LinearAlgebra.Dimension.Localization
import Mathlib.LinearAlgebra.Dimension.Torsion.Finite
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import Mathlib.LinearAlgebra.Finsupp.VectorSpace
import Mathlib.LinearAlgebra.FreeModule.Finite.Quotient
import Mathlib.LinearAlgebra.FreeModule.IdealQuotient
import Mathlib.LinearAlgebra.Isomorphisms
import Mathlib.LinearAlgebra.Matrix.Gershgorin
import Mathlib.LinearAlgebra.Pi
import Mathlib.LinearAlgebra.Quotient.Pi
import Mathlib.LinearAlgebra.StdBasis
import Mathlib.LinearAlgebra.TensorProduct.Basis
import Mathlib.LinearAlgebra.TensorProduct.RightExactness
import Mathlib.LinearAlgebra.Trace
import Mathlib.Logic.Equiv.Fin.Rotate
import Mathlib.NumberTheory.Cyclotomic.Basic
import Mathlib.NumberTheory.Cyclotomic.CyclotomicCharacter
import Mathlib.NumberTheory.LocalField.Basic
import Mathlib.NumberTheory.NumberField.AdeleRing
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.NumberTheory.NumberField.ClassNumber
import Mathlib.NumberTheory.NumberField.Completion.FinitePlace
import Mathlib.NumberTheory.NumberField.Completion.InfinitePlace
import Mathlib.NumberTheory.NumberField.Completion.LiesOverInstances
import Mathlib.NumberTheory.NumberField.Cyclotomic.Galois
import Mathlib.NumberTheory.NumberField.InfinitePlace.Ramification
import Mathlib.NumberTheory.NumberField.ProductFormula
import Mathlib.NumberTheory.NumberField.Units.DirichletTheorem
import Mathlib.NumberTheory.NumberField.Units.Regulator
import Mathlib.NumberTheory.Ostrowski
import Mathlib.NumberTheory.Padics.PadicNumbers
import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Mathlib.NumberTheory.Padics.ProperSpace
import Mathlib.NumberTheory.Padics.RingHoms
import Mathlib.NumberTheory.Padics.ValuativeRel
import Mathlib.NumberTheory.Padics.WithVal
import Mathlib.NumberTheory.RamificationInertia.Galois
import Mathlib.NumberTheory.RamificationInertia.Inertia
import Mathlib.NumberTheory.RamificationInertia.Ramification
import Mathlib.NumberTheory.RamificationInertia.Valuation
import Mathlib.Order.Filter.AtTopBot.Tendsto
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
import Mathlib.RingTheory.ClassGroup.ExtendedHom
import Mathlib.RingTheory.Complex
import Mathlib.RingTheory.DedekindDomain.Factorization
import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
import Mathlib.RingTheory.DedekindDomain.IntegralClosure
import Mathlib.RingTheory.DedekindDomain.SInteger
import Mathlib.RingTheory.DiscreteValuationRing.Basic
import Mathlib.RingTheory.DiscreteValuationRing.TFAE
import Mathlib.RingTheory.Discriminant
import Mathlib.RingTheory.Filtration
import Mathlib.RingTheory.Finiteness.Finsupp
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
import Mathlib.RingTheory.LaurentSeries
import Mathlib.RingTheory.LocalRing.Basic
import Mathlib.RingTheory.LocalRing.ResidueField.Basic
import Mathlib.RingTheory.Localization.Away.Basic
import Mathlib.RingTheory.Localization.Finiteness
import Mathlib.RingTheory.Nakayama
import Mathlib.RingTheory.Norm.Basic
import Mathlib.RingTheory.Norm.Defs
import Mathlib.RingTheory.Norm.Transitivity
import Mathlib.RingTheory.Polynomial.ContentIdeal
import Mathlib.RingTheory.Polynomial.Cyclotomic.Roots
import Mathlib.RingTheory.Polynomial.GaussLemma
import Mathlib.RingTheory.Polynomial.Vieta
import Mathlib.RingTheory.PowerSeries.Evaluation
import Mathlib.RingTheory.PowerSeries.Log
import Mathlib.RingTheory.PowerSeries.WellKnown
import Mathlib.RingTheory.QuasiFinite.Basic
import Mathlib.RingTheory.RamificationInertia.Basic
import Mathlib.RingTheory.RootsOfUnity.Basic
import Mathlib.RingTheory.SimpleModule.Basic
import Mathlib.RingTheory.SimpleRing.Basic
import Mathlib.RingTheory.Spectrum.Prime.Topology
import Mathlib.RingTheory.TensorProduct.Basic
import Mathlib.RingTheory.TensorProduct.Finite
import Mathlib.RingTheory.TensorProduct.Free
import Mathlib.RingTheory.TensorProduct.Maps
import Mathlib.RingTheory.TensorProduct.MvPolynomial
import Mathlib.RingTheory.TensorProduct.Quotient
import Mathlib.RingTheory.Trace.Basic
import Mathlib.RingTheory.Valuation.Archimedean
import Mathlib.RingTheory.Valuation.Discrete.Basic
import Mathlib.RingTheory.Valuation.Discrete.IsDiscreteValuationRing
import Mathlib.RingTheory.Valuation.Extension
import Mathlib.RingTheory.Valuation.Integral
import Mathlib.RingTheory.Valuation.LocalSubring
import Mathlib.RingTheory.Valuation.RamificationGroup
import Mathlib.RingTheory.Valuation.RankOne
import Mathlib.RingTheory.Valuation.ValuationRing
import Mathlib.RingTheory.Valuation.ValuationSubring
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Tactic
import Mathlib.Topology.Algebra.Category.ProfiniteGrp.Basic
import Mathlib.Topology.Algebra.ClopenNhdofOne
import Mathlib.Topology.Algebra.ContinuousMonoidHom
import Mathlib.Topology.Algebra.Field
import Mathlib.Topology.Algebra.Group.Basic
import Mathlib.Topology.Algebra.Group.ClosedSubgroup
import Mathlib.Topology.Algebra.Group.Pointwise
import Mathlib.Topology.Algebra.Group.Quotient
import Mathlib.Topology.Algebra.Group.SubmonoidClosure
import Mathlib.Topology.Algebra.Group.TopologicalAbelianization
import Mathlib.Topology.Algebra.Group.Units
import Mathlib.Topology.Algebra.InfiniteSum.Nonarchimedean
import Mathlib.Topology.Algebra.IsOpenUnits
import Mathlib.Topology.Algebra.IsUniformGroup.Basic
import Mathlib.Topology.Algebra.LinearTopology
import Mathlib.Topology.Algebra.Module.Basic
import Mathlib.Topology.Algebra.Module.Compact
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.Topology.Algebra.Nonarchimedean.AdicTopology
import Mathlib.Topology.Algebra.OpenSubgroup
import Mathlib.Topology.Algebra.Order.Field
import Mathlib.Topology.Algebra.Ring.Basic
import Mathlib.Topology.Algebra.Ring.Compact
import Mathlib.Topology.Algebra.UniformRing
import Mathlib.Topology.Algebra.Valued.LocallyCompact
import Mathlib.Topology.Algebra.Valued.NormedValued
import Mathlib.Topology.Algebra.Valued.ValuativeRel
import Mathlib.Topology.Algebra.Valued.ValuedField
import Mathlib.Topology.Algebra.Valued.WithZeroMulInt
import Mathlib.Topology.Connected.Clopen
import Mathlib.Topology.Homeomorph.Defs
import Mathlib.Topology.Homeomorph.Lemmas
import Mathlib.Topology.Homeomorph.TransferInstance
import Mathlib.Topology.Instances.Matrix
import Mathlib.Topology.Instances.Sign
import Mathlib.Topology.Instances.ZMod
import Mathlib.Topology.Maps.Basic
import Mathlib.Topology.MetricSpace.Ultra.Basic
import Mathlib.Topology.Neighborhoods
import Mathlib.Topology.Order
import Mathlib.Topology.Sets.Opens
import Mathlib.Topology.UniformSpace.AbsoluteValue
import Mathlib.Topology.WithTopology
import Definitions.Def_OAIQ244Duke091
import Definitions.Def_OAIQ244Duke096

section
-- module Solutions.OAIQ244_DUKE.GlobalClassFieldTheory_Reciprocity_IdeleClassDirectLimitNormQuotient
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.GlobalClassFields.ConductorialSubgroup.finiteIndex _root_.GlobalClassFieldTheory.GlobalClassFields.bigHilbertClassFieldNormSubgroup_normal _root_.GlobalClassFieldTheory.GlobalClassFields.finiteAbelianSubextensionAbstractRelativeFixedFieldFiniteDimensional _root_.GlobalClassFieldTheory.GlobalClassFields.finiteAbelianSubextensionAbstractRelativeFixedFieldIsAbelianGalois _root_.GlobalClassFieldTheory.GlobalClassFields.ideleClassNorm_rangeFiniteIndex _root_.GlobalClassFieldTheory.GlobalClassFields.smallHilbertClassFieldNormSubgroupFiniteIndex _root_.GlobalClassFieldTheory.Reciprocity.complexFourthRootField_numberField _root_.GlobalClassFieldTheory.Reciprocity.infinitePlaceComplexificationOverfield_baseSmul _root_.GlobalClassFieldTheory.Reciprocity.infinitePlaceComplexificationOverfield_numberField _root_.GlobalClassFieldTheory.Reciprocity.infinitePlaceComplexificationOverfield_smul _root_.GlobalClassFieldTheory.Reciprocity.numberFieldCyclotomicZHatFiniteCompositum_numberField _root_.GlobalClassFieldTheory.Reciprocity.numberFieldCyclotomicZHatFiniteLayerInCompositum_numberField _root_.GlobalClassFieldTheory.Reciprocity.numberFieldCyclotomicZHatIntersection_numberField _root_.GlobalClassFieldTheory.Reciprocity.ramifiedInfinitePlaceRealFixedField_numberField _root_.GlobalClassFieldTheory.Reciprocity.rationalCyclotomicZHatCompositum_algebra _root_.GlobalClassFieldTheory.Reciprocity.rationalCyclotomicZHatFiniteLayerCompositum_algebra _root_.GlobalClassFieldTheory.Reciprocity.rationalCyclotomicZHatFiniteLayerCompositum_smul _root_.GlobalClassFieldTheory.Reciprocity.rationalCyclotomicZHatFiniteLayerInCompositum_algebra _root_.GlobalClassFieldTheory.Reciprocity.rationalCyclotomicZHatFiniteLayerInCompositum_smul _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.KummerTheory.primeCyclotomicBaseIsGalois _root_.KummerTheory.primeCyclotomicBaseNumberField _root_.KummerTheory.rationalCyclotomicLevel_numberField _root_.LocalClassFieldTheory.finiteGaloisLocalField_integerRing_moduleFinite _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.residueFieldZModAlgebra _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedIntegralAlgebraContextValuationSubringAlgebra _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedIntegralAlgebraContextValuationSubringTower _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedQPadicContextValuationSubringTower _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.LubinTate.compatibleGroupFamiliesGroup _root_.LubinTate.padicCompletedLevelField_algebra _root_.LubinTate.padicCompletedLevelField_isGalois _root_.LubinTate.padicCompletedLevelField_padicScalarTower _root_.LubinTate.padicCompletedUnramifiedFieldAlgebra _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.boundedRealFields_numberField _root_.OAI.PrimeDegreePackets.instTopologicalSpaceLocalAlgebra _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.CyclicCohomology.binaryCoefficientFamilyCommGroup _root_.GlobalClassFieldTheory.GlobalClassFields.bigHilbertNormQuotient_finite _root_.GlobalClassFieldTheory.GlobalClassFields.bigHilbertNormSubgroup_finiteIndex _root_.LocalClassFieldTheory.comparisonIntegerRingIsIntegralClosure _root_.LocalClassFieldTheory.normalizationIntegerRingIsIntegralClosure _root_.chosenFinitePlaceCompletionAlgebra _root_.chosenFinitePlaceLocalizedIntegerAlgebra _root_.chosenFinitePlaceLocalizedIsGalois _root_.cyclicPrimeDegreeIntermediate_isGalois _root_.cyclicPrimeSubextension_isGalois _root_.relativeUnrestrictedSPlaceFactorCommGroup
attribute [-simp] _root_.ClassFormation.DegreeData.finiteUnramifiedDegreeEquiv_unramifiedFrobenius _root_.ClassFormation.DegreeData.finiteUnramifiedRestriction_frobenius _root_.ClassFormation.DegreeData.maximalUnramifiedRestriction_frobenius _root_.ClassFormation.FiniteAbelianSubextension.extensionQuotientMk_apply _root_.ClassFormation.FiniteAbelianSubextension.normSubgroupMap_val _root_.ClassFormation.FiniteGaloisSubextension.classFieldCandidate_field _root_.ClassFormation.ValuationData.maximalUnramifiedNormResidue_degree _root_.ClassFormation.mem_normFilterBasis_iff _root_.GlobalClassFieldTheory.ClassFieldAxiom.actualPushoutNormQuotientMap_mk _root_.GlobalClassFieldTheory.ClassFieldAxiom.hasseNormDiagonal_mk _root_.GlobalClassFieldTheory.ClassFieldAxiom.sUnitEquivSupportedPrincipalIdeleSubgroup_coe _root_.GlobalClassFieldTheory.GlobalClassFields.ConductorialSubgroup.ideleClassQuotientEquivOfNarrowFiniteConductorsEqOfRayClassGroupCardsEqQuotientCards_mk _root_.GlobalClassFieldTheory.GlobalClassFields.ConductorialSubgroup.mem_fullConductorInfinitePart_iff _root_.GlobalClassFieldTheory.GlobalClassFields.ConductorialSubgroup.narrowFiniteConductorRayClassGroupEquivQuotientOfCardEq_mk _root_.GlobalClassFieldTheory.GlobalClassFields.ConductorialSubgroup.narrowFiniteConductorRayClassGroupToQuotient_mk _root_.GlobalClassFieldTheory.GlobalClassFields.bigHilbertClassFieldQuotientCongr_mk _root_.GlobalClassFieldTheory.GlobalClassFields.bigHilbertClassFieldQuotientEquivNarrowClassGroup_mk _root_.GlobalClassFieldTheory.GlobalClassFields.bigHilbertClassFieldQuotientToIdeleClassNormQuotient_mk _root_.GlobalClassFieldTheory.GlobalClassFields.bigHilbertClassFieldQuotientToSmallHilbertClassFieldQuotient_mk _root_.GlobalClassFieldTheory.GlobalClassFields.ideleClassNormQuotientTowerMap_mk _root_.GlobalClassFieldTheory.GlobalClassFields.narrowFiniteConductorRayClassGroupToIdeleClassNormQuotient_mk _root_.GlobalClassFieldTheory.GlobalClassFields.normQuotientEquivOfNarrowFiniteConductorsEqOfRayClassGroupCardsEqNormQuotientCards_mk _root_.GlobalClassFieldTheory.GlobalClassFields.realSignToBigHilbertClassFieldQuotient_apply _root_.GlobalClassFieldTheory.GlobalClassFields.realSignToNarrowClassKernel_apply _root_.GlobalClassFieldTheory.GlobalClassFields.smallHilbertClassFieldQuotientCongr_mk _root_.GlobalClassFieldTheory.GlobalClassFields.smallHilbertClassFieldQuotientEquivClassGroup_mk _root_.GlobalClassFieldTheory.GlobalClassFields.smallHilbertClassFieldQuotientToIdeleClassNormQuotient_mk _root_.GlobalClassFieldTheory.IdealClassFieldTheory.smallHilbertClassFieldIdeleExtensionMap_mk' _root_.GlobalClassFieldTheory.Reciprocity.cyclotomicZHatNormCompositeContinuous_apply _root_.GlobalClassFieldTheory.Reciprocity.cyclotomicZHatNormCompositeInMulNatRangeContinuous_apply _root_.GlobalClassFieldTheory.Reciprocity.cyclotomicZHatNormComposite_apply _root_.GlobalClassFieldTheory.Reciprocity.finitePlaceGlobalArtinMonoidHom_finitePlaceIdele _root_.GlobalClassFieldTheory.Reciprocity.globalArtinMonoidHom_finitePlaceIdele _root_.GlobalClassFieldTheory.Reciprocity.globalArtinMonoidHom_ideleNorm_eq_one _root_.GlobalClassFieldTheory.Reciprocity.globalArtinMonoidHom_infinitePlaceIdele _root_.GlobalClassFieldTheory.Reciprocity.globalArtinMonoidHom_relativeIdeleNorm_eq_one _root_.GlobalClassFieldTheory.Reciprocity.globalNormClassFromIdele_principalIdele _root_.GlobalClassFieldTheory.Reciprocity.globalNormClassFromIdele_relativeIdeleNorm_eq_one _root_.GlobalClassFieldTheory.Reciprocity.infinitePlaceGlobalArtinMonoidHom_finitePlaceIdele _root_.GlobalClassFieldTheory.Reciprocity.mem_globalArtinFiniteSupport_iff _root_.GlobalClassFieldTheory.Reciprocity.normalizedCyclotomicZHatIdeleValueContinuousMul_apply _root_.GlobalClassFieldTheory.Reciprocity.normalizedCyclotomicZHatIdeleValueContinuous_apply _root_.GlobalClassFieldTheory.Reciprocity.numberFieldCyclotomicZHatCompositumRestriction_infiniteGlobalArtinMonoidHom _root_.GlobalClassFieldTheory.Reciprocity.rationalCyclotomicZHatGlobalArtin_rationalIdeleArchimedeanPart _root_.GlobalClassFieldTheory.Reciprocity.rationalCyclotomicZHatGlobalArtin_rationalPositiveArchimedeanIdele _root_.GlobalClassFieldTheory.Reciprocity.rationalCyclotomicZHatIdeleValueContinuousAdd_apply _root_.GlobalClassFieldTheory.Reciprocity.rationalCyclotomicZHatIdeleValueReduction_apply _root_.GlobalClassFieldTheory.Reciprocity.rationalCyclotomicZHatIdeleValue_apply _root_.GlobalClassFieldTheory.Reciprocity.rationalCyclotomicZHatIdeleValue_rationalIdeleArchimedeanPart _root_.GlobalClassFieldTheory.Reciprocity.rationalIdeleArchimedeanPart_finiteComponent _root_.GlobalClassFieldTheory.Reciprocity.rationalIdeleArchimedeanPart_infiniteComponent _root_.GlobalClassFieldTheory.Reciprocity.rationalIdeleFinitePart_finiteComponent _root_.GlobalClassFieldTheory.Reciprocity.rationalIdeleFinitePart_infiniteComponent _root_.GlobalClassFieldTheory.Reciprocity.rationalPositiveArchimedeanIdele_finiteComponent _root_.GlobalClassFieldTheory.Reciprocity.restrictNormalHom_infiniteGlobalArtinMonoidHom _root_.GlobalClassFieldTheory.Reciprocity.restrictNormalHom_infiniteGlobalArtinMonoidHom_of_numberField _root_.GlobalClassFieldTheory.Reciprocity.restrictNormalHom_rationalCyclotomicZHatGlobalArtin _root_.IdeleClassGroup.normOneNorm_apply _root_.IdeleGroup.count_fractionalIdeal _root_.IdeleGroup.finitePlaceIdele_finiteComponent_of_ne _root_.IdeleGroup.finitePlaceIdele_finiteComponent_same _root_.IdeleGroup.finitePlaceIdele_infiniteComponent _root_.IdeleGroup.fractionalIdeal_finitePrimeIdele _root_.IdeleGroup.idealClass_finitePrimeIdele _root_.IdeleGroup.ideleNormContinuousMonoidHom_apply _root_.IdeleGroup.infinitePlaceIdeleContinuous_apply _root_.IdeleGroup.infinitePlaceIdele_finiteComponent _root_.IdeleGroup.infinitePlaceIdele_infiniteComponent_of_ne _root_.IdeleGroup.infinitePlaceIdele_infiniteComponent_same _root_.IsDiscreteValuationRing.addVal_ringEquiv _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.LocalClassFieldTheory.abstractFixedFieldCosetToAlgHom_mk _root_.LocalClassFieldTheory.intrinsicBaseEquivAmbientFixedField_apply_val _root_.LocalClassFieldTheory.intrinsicFrobeniusFixedFieldEquivAmbientEmbeddedField_apply_val _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.OAI.PrimeDegreePackets.ThetaConstruction.schwartzCM_apply _root_.RayClass.primesEquiv_val_eq_natGenerator _root_.RayClass.signToNarrow_mk _root_.IdeleGroup.idealClass_classRepresentative _root_.finiteIdeleOfSPlaceFactors_apply_mem _root_.finiteIdeleOfSPlaceFactors_apply_notMem _root_.ideleClassCongr_ideleClassNorm _root_.ideleClassCongr_refl _root_.ideleSupportedAtEquivSPlaceFactors_infinite _root_.ideleSupportedAtEquivSPlaceFactors_inside _root_.ideleSupportedAtEquivSPlaceFactors_outside_coe _root_.relativeIdeleClassBaseChangeMulEquiv_congrOfAlgEquiv
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI
attribute [local instance] OAI.starSubalgebraCommCStarAlgebra

set_option autoImplicit false

/-!
# Finite norm quotients for rational fixed fields

The abstract finite norm subgroup and quotient are identified with the
ordinary idele-class norm range and quotient of the actual fixed-field extension.
-/

noncomputable section

namespace GlobalClassFieldTheory
namespace Reciprocity

open ClassFormation
open LocalClassFieldTheory
open CyclicCohomology

attribute [local instance] GlobalClassFieldTheory.Reciprocity.rationalNormQuotientIdeleClassGroupIsMulCommutative
attribute [local instance] GlobalClassFieldTheory.Reciprocity.rationalNormQuotientIdeleClassSubgroupNormal
/-- The fixed-field comparison carries the abstract finite norm subgroup
exactly to the ordinary idele-class norm range of the actual fixed fields. -/
theorem
    map_rationalFiniteNormSubgroup_eq_ordinaryIdeleClassNormRange_concrete
    (K L : ClosedSubgroup
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
    (hLK : L.toSubgroup ≤ K.toSubgroup)
    (hnormal : (extensionSubgroup K L hLK).Normal)
    [hKfinite : Finite
      ((baseField
        (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ)).toSubgroup ⧸
        extensionSubgroup
          (baseField
            (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
          K (le_baseField K))]
    [hfinite : Finite
      (K.toSubgroup ⧸ extensionSubgroup K L hLK)] :
    let F := abstractFixedField ℚ (SeparableClosure ℚ) K
    let E := abstractRelativeFixedField ℚ (SeparableClosure ℚ) hLK
    letI := hnormal
    letI : FiniteDimensional ℚ F :=
      abstractFixedField_finiteDimensional
        ℚ (SeparableClosure ℚ) K hKfinite
    letI : FiniteDimensional F E :=
      abstractRelativeFixedField_finiteDimensional
        ℚ (SeparableClosure ℚ) K L hLK hKfinite hfinite
    letI : IsScalarTower ℚ F E :=
      IsScalarTower.of_algebraMap_eq' (RingHom.ext_rat _ _)
    letI : FiniteDimensional ℚ E :=
      FiniteDimensional.trans ℚ F E
    letI : NumberField F := NumberField.of_module_finite ℚ F
    letI : NumberField E := NumberField.of_module_finite ℚ E
    letI : IsGalois F E :=
      abstractRelativeFixedField_isGalois
        ℚ (SeparableClosure ℚ) K L hLK hnormal
    (finiteNormSubgroup rationalIdeleClassRepresentation K L hLK).map
        (rationalAbstractFixedFieldIdeleClassEquivFixed
          K).symm.toAddMonoidHom =
      (_root_.ideleClassNorm F E).range.toAddSubgroup := by
  let F := abstractFixedField ℚ (SeparableClosure ℚ) K
  let E := abstractRelativeFixedField ℚ (SeparableClosure ℚ) hLK
  let _ := hnormal
  let _ : FiniteDimensional ℚ F :=
    abstractFixedField_finiteDimensional
      ℚ (SeparableClosure ℚ) K hKfinite
  let _ : FiniteDimensional F E :=
    abstractRelativeFixedField_finiteDimensional
      ℚ (SeparableClosure ℚ) K L hLK hKfinite hfinite
  let _ : IsScalarTower ℚ F E :=
    IsScalarTower.of_algebraMap_eq' (RingHom.ext_rat _ _)
  let _ : FiniteDimensional ℚ E := FiniteDimensional.trans ℚ F E
  let _ : NumberField F := NumberField.of_module_finite ℚ F
  let _ : NumberField E := NumberField.of_module_finite ℚ E
  let _ : IsGalois F E :=
    abstractRelativeFixedField_isGalois
      ℚ (SeparableClosure ℚ) K L hLK hnormal
  let _ : CommGroup (IdeleClassGroup F) :=
    rationalNormQuotientIdeleClassCommGroup F
  let _ : CommGroup (IdeleClassGroup E) :=
    rationalNormQuotientIdeleClassCommGroup E
  let eK : Additive (IdeleClassGroup F) ≃+
      KummerTheory.ambientFixedAddSubgroup
        rationalIdeleClassRepresentation K :=
    rationalAbstractFixedFieldIdeleClassEquivFixed
      (hfinite := hKfinite) K
  let eUpper : Additive (IdeleClassGroup E) ≃+
      KummerTheory.ambientFixedAddSubgroup
        rationalIdeleClassRepresentation L :=
    rationalAbstractRelativeFixedFieldIdeleClassEquivFixed
      (hKfinite := hKfinite) (hfinite := hfinite) K L hLK
  let f :
      KummerTheory.ambientFixedAddSubgroup
          rationalIdeleClassRepresentation L →+
        KummerTheory.ambientFixedAddSubgroup
          rationalIdeleClassRepresentation K :=
    relativeNorm rationalIdeleClassRepresentation K L hLK
  let g : IdeleClassGroup E →* IdeleClassGroup F :=
    _root_.ideleClassNorm F E
  change f.range.map eK.symm.toAddMonoidHom = g.range.toAddSubgroup
  refine map_addRange_eq_monoidRange_toAddSubgroup_of_equiv
    (U := KummerTheory.ambientFixedAddSubgroup
      rationalIdeleClassRepresentation L)
    (A := KummerTheory.ambientFixedAddSubgroup
      rationalIdeleClassRepresentation K)
    (G := IdeleClassGroup E) (H := IdeleClassGroup F)
    (f := f) (g := g) (eU := eUpper) (eA := eK) ?_
  intro c
  have hcompat :
      f (eUpper c) = eK (Additive.ofMul (g (Additive.toMul c))) := by
    exact
      rationalAbstractRelativeFixedFieldIdeleClassEquivFixed_relativeNorm
        (hKfinite := hKfinite) (hfinite := hfinite) K L hLK hnormal c
  apply eK.injective
  exact Eq.trans (eK.apply_symm_apply (f (eUpper c))) hcompat

/-- The finite norm quotient in the rational absolute representation is
the ordinary idele-class quotient by the actual norm subgroup of the
fixed-field extension. -/
noncomputable def
    rationalFiniteNormQuotientEquivIdeleClassNormQuotient
    (K L : ClosedSubgroup
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
    (hLK : L.toSubgroup ≤ K.toSubgroup)
    (hnormal : (extensionSubgroup K L hLK).Normal)
    [hKfinite : Finite
      ((baseField
        (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ)).toSubgroup ⧸
        extensionSubgroup
          (baseField
            (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
          K (le_baseField K))]
    [hfinite : Finite
      (K.toSubgroup ⧸ extensionSubgroup K L hLK)] :
    FiniteNormQuotient rationalIdeleClassRepresentation K L hLK ≃+
      rationalOrdinaryNormQuotientAdditiveType K L hLK hnormal := by
  letI : (extensionSubgroup K L hLK).Normal := hnormal
  letI : FiniteDimensional ℚ
      (abstractFixedField ℚ (SeparableClosure ℚ) K) :=
    abstractFixedField_finiteDimensional
      ℚ (SeparableClosure ℚ) K hKfinite
  letI : FiniteDimensional
      (abstractFixedField ℚ (SeparableClosure ℚ) K)
      (abstractRelativeFixedField ℚ (SeparableClosure ℚ) hLK) :=
    abstractRelativeFixedField_finiteDimensional
      ℚ (SeparableClosure ℚ) K L hLK hKfinite hfinite
  letI : IsScalarTower ℚ
      (abstractFixedField ℚ (SeparableClosure ℚ) K)
      (abstractRelativeFixedField ℚ (SeparableClosure ℚ) hLK) :=
    IsScalarTower.of_algebraMap_eq'
      (R := ℚ)
      (S := abstractFixedField ℚ (SeparableClosure ℚ) K)
      (A := abstractRelativeFixedField ℚ (SeparableClosure ℚ) hLK)
      (RingHom.ext_rat
        (algebraMap ℚ (abstractRelativeFixedField ℚ (SeparableClosure ℚ) hLK))
        ((algebraMap
            (abstractFixedField ℚ (SeparableClosure ℚ) K)
            (abstractRelativeFixedField ℚ (SeparableClosure ℚ) hLK)).comp
          (algebraMap ℚ (abstractFixedField ℚ (SeparableClosure ℚ) K))))
  letI : NumberField (abstractFixedField ℚ (SeparableClosure ℚ) K) :=
    rationalNormQuotientAbstractFixedFieldNumberField
      (hKfinite := hKfinite) K
  letI : NumberField (abstractRelativeFixedField ℚ (SeparableClosure ℚ) hLK) :=
    rationalNormQuotientAbstractRelativeFixedFieldNumberField
      (hKfinite := hKfinite) (hfinite := hfinite) K L hLK
  letI : IsGalois
      (abstractFixedField ℚ (SeparableClosure ℚ) K)
      (abstractRelativeFixedField ℚ (SeparableClosure ℚ) hLK) :=
    abstractRelativeFixedField_isGalois
      ℚ (SeparableClosure ℚ) K L hLK hnormal
  letI : CommGroup (IdeleClassGroup (abstractFixedField ℚ (SeparableClosure ℚ) K)) :=
    rationalNormQuotientIdeleClassCommGroup
      (abstractFixedField ℚ (SeparableClosure ℚ) K)
  letI : (_root_.ideleClassNorm
      (abstractFixedField ℚ (SeparableClosure ℚ) K)
      (abstractRelativeFixedField ℚ (SeparableClosure ℚ) hLK)).range.Normal :=
    rationalNormQuotientIdeleClassSubgroupNormal
      (F := abstractFixedField ℚ (SeparableClosure ℚ) K)
      (_root_.ideleClassNorm
        (abstractFixedField ℚ (SeparableClosure ℚ) K)
        (abstractRelativeFixedField ℚ (SeparableClosure ℚ) hLK)).range
  change FiniteNormQuotient rationalIdeleClassRepresentation K L hLK ≃+
    Additive (IdeleClassGroup (abstractFixedField ℚ (SeparableClosure ℚ) K) ⧸
      (_root_.ideleClassNorm
        (abstractFixedField ℚ (SeparableClosure ℚ) K)
        (abstractRelativeFixedField ℚ (SeparableClosure ℚ) hLK)).range)
  exact addEquivTransQuotientOfEquivMapEq
    (Q := FiniteNormQuotient
      rationalIdeleClassRepresentation K L hLK)
    (A := KummerTheory.ambientFixedAddSubgroup
      rationalIdeleClassRepresentation K)
    (G := IdeleClassGroup (abstractFixedField ℚ (SeparableClosure ℚ) K))
    (S := finiteNormSubgroup rationalIdeleClassRepresentation K L hLK)
    (N := (_root_.ideleClassNorm
      (abstractFixedField ℚ (SeparableClosure ℚ) K)
      (abstractRelativeFixedField ℚ (SeparableClosure ℚ) hLK)).range)
    (eConcrete := rationalFiniteNormQuotientConcreteStep
      (hfinite := hfinite) K L hLK)
    (e := rationalAbstractFixedFieldIdeleClassEquivFixed
      (hfinite := hKfinite) K)
    (hmap := map_rationalFiniteNormSubgroup_eq_ordinaryIdeleClassNormRange_concrete
      (hKfinite := hKfinite) (hfinite := hfinite) K L hLK hnormal)

/-- The fixed-field norm-quotient comparison sends an abstract finite
norm class to the ordinary idele class of the transported
representative. -/
@[simp]
theorem
    rationalFiniteNormQuotientEquivIdeleClassNormQuotient_finiteNormClass
    (K L : ClosedSubgroup
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
    (hLK : L.toSubgroup ≤ K.toSubgroup)
    (hnormal : (extensionSubgroup K L hLK).Normal)
    [hKfinite : Finite
      ((baseField
        (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ)).toSubgroup ⧸
        extensionSubgroup
          (baseField
            (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
          K (le_baseField K))]
    [hfinite : Finite
      (K.toSubgroup ⧸ extensionSubgroup K L hLK)]
    (a : KummerTheory.ambientFixedAddSubgroup
      rationalIdeleClassRepresentation K) :
    rationalFiniteNormQuotientEquivIdeleClassNormQuotient
        K L hLK hnormal
        (finiteNormClass rationalIdeleClassRepresentation
          K L hLK a) =
      rationalFiniteNormQuotientClassValue
        (hKfinite := hKfinite) (hfinite := hfinite)
        K L hLK hnormal a := by
  let F := abstractFixedField ℚ (SeparableClosure ℚ) K
  let E := abstractRelativeFixedField ℚ (SeparableClosure ℚ) hLK
  let _ := hnormal
  let _ : FiniteDimensional ℚ F :=
    abstractFixedField_finiteDimensional
      ℚ (SeparableClosure ℚ) K hKfinite
  let _ : FiniteDimensional F E :=
    abstractRelativeFixedField_finiteDimensional
      ℚ (SeparableClosure ℚ) K L hLK hKfinite hfinite
  let _ : IsScalarTower ℚ F E :=
    IsScalarTower.of_algebraMap_eq' (RingHom.ext_rat _ _)
  let _ : FiniteDimensional ℚ E :=
    FiniteDimensional.trans ℚ F E
  let _ : NumberField F := NumberField.of_module_finite ℚ F
  let _ : NumberField E := NumberField.of_module_finite ℚ E
  let _ : IsGalois F E :=
    abstractRelativeFixedField_isGalois
      ℚ (SeparableClosure ℚ) K L hLK hnormal
  change
    rationalFiniteNormQuotientEquivIdeleClassNormQuotient
        K L hLK hnormal
        (finiteNormClass rationalIdeleClassRepresentation
          K L hLK a) =
      Additive.ofMul
        (QuotientGroup.mk'
          (_root_.ideleClassNorm F E).range
          (Additive.toMul
            ((rationalAbstractFixedFieldIdeleClassEquivFixed K).symm
              a)))
  simp only [
    rationalFiniteNormQuotientEquivIdeleClassNormQuotient,
    rationalFiniteNormQuotientConcreteStep,
    addEquivTransQuotientOfEquivMapEq,
    quotientAddEquivOfEquivMapEqToQuotient]
  rfl

end Reciprocity
end GlobalClassFieldTheory
end
end

section
-- module Solutions.OAIQ244_DUKE.GlobalClassFieldTheory_Reciprocity_FiniteGaloisRealizationCore
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 400000
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.infinitePlaceComplexificationOverfield_algebra _root_.GlobalClassFieldTheory.Reciprocity.infinitePlaceComplexificationOverfield_baseAlgebra _root_.GlobalClassFieldTheory.Reciprocity.ramifiedInfinitePlaceRealFixedField_algebra _root_.KummerTheory.primeCyclotomicBaseIsGalois _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.LubinTate.padicCompletedLevelField_algebra _root_.LubinTate.padicCompletedLevelField_isGalois _root_.LubinTate.padicCompletedLevelField_padicScalarTower _root_.LubinTate.padicCompletedStandardChangedCompositum_changedFieldAlgebra _root_.LubinTate.padicCompletedUnramifiedFieldAlgebra _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.diagonalLogAction _root_.OAI.PrimeDegreePackets.instTopologicalSpaceLocalAlgebra _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.LocalClassFieldTheory.normalizationIntegerRingIsIntegralClosure _root_.chosenFinitePlaceCompletionAlgebra _root_.chosenFinitePlaceLocalizedIntegerAlgebra _root_.chosenFinitePlaceLocalizedIsGalois _root_.cyclicPrimeDegreeIntermediate_isGalois _root_.cyclicPrimeSubextension_isGalois
attribute [-simp] _root_.IsDiscreteValuationRing.addVal_ringEquiv _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.OAI.PrimeDegreePackets.ThetaConstruction.schwartzCM_apply _root_.RayClass.primesEquiv_val_eq_natGenerator
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

/-!
# Finite Galois number-field extensions in the rational separable closure

An actual tower `L / K / ℚ` must be realized by compatible embeddings
before the rational absolute class formation can be applied.  We choose
only the upper embedding `L →ₐ[ℚ] SeparableClosure ℚ`; the lower embedding
is its restriction along `K →ₐ[ℚ] L`.  Thus the two field ranges, their
fixing subgroups, and the norm comparison all come from the existing
mathlib and LCFT constructions.

No second model of a number field, an idele class group, or a norm
quotient is introduced here.
-/

open scoped NumberField
open NumberField

noncomputable section

namespace GlobalClassFieldTheory
namespace Reciprocity

open ClassFormation
open AlgebraicNumberTheory
open LocalClassFieldTheory
open RamificationTheory

variable
    (K L : Type*) [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]

/-- The embedding of the lower field obtained by restricting the one
chosen embedding of the top field. -/
noncomputable def numberFieldTowerLowerEmbedding :
    K →ₐ[ℚ] SeparableClosure ℚ :=
  (numberFieldSeparableClosureEmbedding L).comp
    (IsScalarTower.toAlgHom ℚ K L)

/-- The copy of `K` obtained from the chosen copy of `L`; this is the
lower field in the compatible realization of `L / K`. -/
def numberFieldTowerBaseField :
    IntermediateField ℚ (SeparableClosure ℚ) :=
  (numberFieldTowerLowerEmbedding K L).fieldRange

omit [FiniteDimensional K L] [IsGalois K L] in
/-- The compatible embedded copy of `K` lies in the chosen embedded copy
of `L`. -/
theorem numberFieldTowerBaseField_le_topField :
    numberFieldTowerBaseField K L ≤
      numberFieldInRationalSeparableClosure L := by
  intro x hx
  rcases hx with ⟨y, rfl⟩
  exact ⟨algebraMap K L y, rfl⟩

/-- The standard inclusion algebra on the two nested field ranges. -/
noncomputable instance numberFieldTowerBaseFieldAlgebra :
    Algebra (numberFieldTowerBaseField K L)
      (numberFieldInRationalSeparableClosure L) :=
  (IntermediateField.inclusion
    (numberFieldTowerBaseField_le_topField K L)).toRingHom.toAlgebra

omit [FiniteDimensional K L] [IsGalois K L] in
/-- The two field-range equivalences form the same square as the original
tower `L / K`. -/
@[simp]
theorem numberFieldTowerFieldRangeEquiv_algebraMap (x : K) :
    (numberFieldSeparableClosureEmbedding L).equivFieldRange
        (algebraMap K L x) =
      algebraMap (numberFieldTowerBaseField K L)
        (numberFieldInRationalSeparableClosure L)
        ((numberFieldTowerLowerEmbedding K L).equivFieldRange x) := by
  rfl

/-- The closed subgroup representing the compatible embedded copy of
`K`. -/
def numberFieldTowerBaseSubgroup :
    ClosedSubgroup
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ) :=
  closedFixingSubgroup ℚ (SeparableClosure ℚ)
    (numberFieldTowerBaseField K L)

/-- The closed subgroup representing the chosen embedded copy of `L`. -/
def numberFieldTowerTopSubgroup :
    ClosedSubgroup
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ) :=
  closedFixingSubgroup ℚ (SeparableClosure ℚ)
    (numberFieldInRationalSeparableClosure L)

omit [FiniteDimensional K L] [IsGalois K L] in
/-- Inclusion of compatible field ranges gives the contravariant
inclusion of their fixing subgroups. -/
theorem numberFieldTowerTopSubgroup_le_baseSubgroup :
    (numberFieldTowerTopSubgroup L).toSubgroup ≤
      (numberFieldTowerBaseSubgroup K L).toSubgroup := by
  change
    (numberFieldInRationalSeparableClosure L).fixingSubgroup ≤
      (numberFieldTowerBaseField K L).fixingSubgroup
  exact
    (numberFieldTowerBaseField K L).fixingSubgroup_le
      (numberFieldTowerBaseField_le_topField K L)

/-- The algebra structure on the rational separable closure induced by
the compatible lower embedding in a number-field tower. -/
@[reducible]
noncomputable def numberFieldTowerSeparableClosureBaseAlgebra :
    Algebra K (SeparableClosure ℚ) :=
  (numberFieldTowerLowerEmbedding K L).toRingHom.toAlgebra

/-- A `K`-automorphism of the common rational separable closure,
viewed as the corresponding rational automorphism fixing the embedded
copy of `K`. -/
noncomputable def numberFieldTowerSeparableClosureToBaseSubgroup :
    letI : Algebra K (SeparableClosure ℚ) :=
      numberFieldTowerSeparableClosureBaseAlgebra K L
    Gal(SeparableClosure ℚ / K) →*
      (numberFieldTowerBaseSubgroup K L).toSubgroup := by
  let _ : Algebra K (SeparableClosure ℚ) :=
    numberFieldTowerSeparableClosureBaseAlgebra K L
  refine
    { toFun := fun σ =>
        ⟨AlgEquiv.restrictScalars ℚ σ, ?_⟩
      map_one' := by
        apply Subtype.ext
        rfl
      map_mul' := by
        intro σ τ
        apply Subtype.ext
        rfl }
  change
    AlgEquiv.restrictScalars ℚ σ ∈
      (numberFieldTowerBaseField K L).fixingSubgroup
  rw [IntermediateField.mem_fixingSubgroup_iff]
  intro x hx
  obtain ⟨y, rfl⟩ := hx
  exact σ.commutes y

/-- The compatible `K`-absolute Galois group is exactly the fixing
subgroup of the embedded copy of `K` inside the rational absolute
Galois group. -/
noncomputable def numberFieldTowerSeparableClosureEquivBaseSubgroup :
    letI : Algebra K (SeparableClosure ℚ) :=
      numberFieldTowerSeparableClosureBaseAlgebra K L
    Gal(SeparableClosure ℚ / K) ≃*
      (numberFieldTowerBaseSubgroup K L).toSubgroup := by
  letI : Algebra K (SeparableClosure ℚ) :=
    numberFieldTowerSeparableClosureBaseAlgebra K L
  refine
    { toFun := numberFieldTowerSeparableClosureToBaseSubgroup K L
      invFun := fun τ =>
        { τ.1 with
          commutes' := fun x => ?_ }
      left_inv := ?_
      right_inv := ?_
      map_mul' := map_mul
        (numberFieldTowerSeparableClosureToBaseSubgroup K L) }
  · have hτ :
        ∀ z ∈ numberFieldTowerBaseField K L,
          τ.1 z = z := by
      exact
        (IntermediateField.mem_fixingSubgroup_iff
          (numberFieldTowerBaseField K L) τ.1).1 τ.2
    exact
      hτ
        (numberFieldTowerLowerEmbedding K L x)
        ⟨x, rfl⟩
  · intro σ
    apply AlgEquiv.ext
    intro x
    rfl
  · intro τ
    apply Subtype.ext
    apply AlgEquiv.ext
    intro x
    rfl

omit [FiniteDimensional K L] [IsGalois K L] in
/-- Coercing the base-subgroup comparison equivalence gives restriction of
scalars to the rational base. -/
@[simp]
theorem numberFieldTowerSeparableClosureEquivBaseSubgroup_apply_coe
    (σ :
      letI : Algebra K (SeparableClosure ℚ) :=
        numberFieldTowerSeparableClosureBaseAlgebra K L
      Gal(SeparableClosure ℚ / K)) :
    letI : Algebra K (SeparableClosure ℚ) :=
      numberFieldTowerSeparableClosureBaseAlgebra K L
    ((numberFieldTowerSeparableClosureEquivBaseSubgroup K L σ :
        (numberFieldTowerBaseSubgroup K L).toSubgroup) :
      Gal(SeparableClosure ℚ / ℚ)) =
      AlgEquiv.restrictScalars ℚ σ := by
  let : Algebra K (SeparableClosure ℚ) :=
    numberFieldTowerSeparableClosureBaseAlgebra K L
  change
    (numberFieldTowerSeparableClosureToBaseSubgroup K L σ).1 =
      AlgEquiv.restrictScalars ℚ σ
  rfl

end Reciprocity
end GlobalClassFieldTheory
end
end

section
-- module Solutions.OAIQ244_DUKE.GlobalClassFieldTheory_Reciprocity_FiniteGaloisRealizationSubextension
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 400000
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.GlobalClassFields.finiteAbelianSubextensionAbstractRelativeFixedFieldFiniteDimensional _root_.KummerTheory.primeCyclotomicBaseFiniteDimensional _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.LubinTate.padicCompletedLevelField_algebra _root_.LubinTate.padicCompletedLevelField_finiteDimensional _root_.LubinTate.padicCompletedUnramifiedFieldAlgebra _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.instTopologicalSpaceLocalAlgebra _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.LocalClassFieldTheory.normalizationIntegerRingIsIntegralClosure _root_.chosenFinitePlaceCompletionAlgebra _root_.chosenFinitePlaceCompletionFiniteDimensional _root_.chosenFinitePlaceLocalizedFiniteDimensional
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

/-!
# The finite Galois subextension attached to a number-field tower

This module realizes `L / K` as a finite Galois subextension inside the common
rational separable closure.  It packages the relevant fixing subgroups,
normality, and finite-index data for abstract reciprocity.
-/

open scoped NumberField
open NumberField

noncomputable section

namespace GlobalClassFieldTheory
namespace Reciprocity

open ClassFormation
open CyclicCohomology
open AlgebraicNumberTheory
open LocalClassFieldTheory
open RamificationTheory

variable
    (K L : Type) [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]

/-- The lower fixing subgroup, with its finite absolute-index witness,
is the finite abstract field consumed by abstract reciprocity. -/
@[reducible]
noncomputable def numberFieldTowerFiniteAbstractField :
    FiniteAbstractField
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ) where
  field := numberFieldTowerBaseSubgroup K L
  finite := by
    simpa only [numberFieldTowerBaseSubgroup,
      numberFieldTowerBaseField] using
      (ambientEmbeddedAbsoluteQuotientFinite
        ℚ K (numberFieldTowerLowerEmbedding K L))

end Reciprocity
end GlobalClassFieldTheory
end
end

section
-- module Solutions.OAIQ244_DUKE.GlobalClassFieldTheory_Reciprocity_FiniteGaloisRealizationNormQuotient
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 400000
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.GlobalClassFields.finiteAbelianSubextensionAbstractRelativeFixedFieldFiniteDimensional _root_.GlobalClassFieldTheory.GlobalClassFields.finiteAbelianSubextensionAbstractRelativeFixedFieldIsAbelianGalois _root_.GlobalClassFieldTheory.Reciprocity.infinitePlaceComplexificationOverfield_algebra _root_.GlobalClassFieldTheory.Reciprocity.infinitePlaceComplexificationOverfield_baseAlgebra _root_.GlobalClassFieldTheory.Reciprocity.ramifiedInfinitePlaceRealFixedField_algebra _root_.KummerTheory.primeCyclotomicBaseIsGalois _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.LubinTate.padicCompletedLevelField_algebra _root_.LubinTate.padicCompletedLevelField_isGalois _root_.LubinTate.padicCompletedLevelField_padicScalarTower _root_.LubinTate.padicCompletedStandardChangedCompositum_changedFieldAlgebra _root_.LubinTate.padicCompletedUnramifiedFieldAlgebra _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.diagonalLogAction _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.LocalClassFieldTheory.normalizationIntegerRingIsIntegralClosure _root_.chosenFinitePlaceCompletionAlgebra _root_.chosenFinitePlaceLocalizedIntegerAlgebra _root_.chosenFinitePlaceLocalizedIsGalois _root_.cyclicPrimeDegreeIntermediate_isGalois _root_.cyclicPrimeSubextension_isGalois
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

/-!
# Norm quotients in the compatible Galois realization

This module identifies the abstract fixed fields with the embedded copies of
`K` and `L`, and transports the resulting idèle-class norm quotient and
reciprocity data to the original finite Galois extension.
-/

open scoped NumberField
open NumberField

noncomputable section

namespace GlobalClassFieldTheory
namespace Reciprocity

open ClassFormation
open CyclicCohomology
open AlgebraicNumberTheory
open LocalClassFieldTheory
open RamificationTheory

variable
    (K L : Type) [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]

omit [FiniteDimensional K L] [IsGalois K L] in
/-- The fixed field of the lower subgroup is the compatible embedded
copy of `K`. -/
theorem numberFieldTowerAbstractBaseField_eq :
    abstractFixedField ℚ (SeparableClosure ℚ)
        (numberFieldTowerBaseSubgroup K L) =
      numberFieldTowerBaseField K L :=
  InfiniteGalois.fixedField_fixingSubgroup
    (numberFieldTowerBaseField K L)

/-- The original base field is canonically equivalent to the actual
fixed field used by the rational class formation. -/
noncomputable def numberFieldTowerAbstractBaseFieldEquiv :
    K ≃ₐ[ℚ]
      abstractFixedField ℚ (SeparableClosure ℚ)
        (numberFieldTowerBaseSubgroup K L) :=
  (numberFieldTowerLowerEmbedding K L).equivFieldRange.trans
    (IntermediateField.equivOfEq
      (numberFieldTowerAbstractBaseField_eq K L).symm)

omit [FiniteDimensional K L] [IsGalois K L] in
/-- After restriction of scalars to `ℚ`, the upper relative fixed field
is the chosen embedded copy of `L`. -/
theorem numberFieldTowerAbstractTopField_restrictScalars_eq :
    (abstractRelativeFixedField ℚ (SeparableClosure ℚ)
        (numberFieldTowerTopSubgroup_le_baseSubgroup K L)).restrictScalars ℚ =
      numberFieldInRationalSeparableClosure L :=
  InfiniteGalois.fixedField_fixingSubgroup
    (numberFieldInRationalSeparableClosure L)

/-- The original top field is canonically equivalent over `ℚ` to the
actual relative fixed field used by the rational class formation. -/
noncomputable def numberFieldTowerAbstractTopFieldEquiv :
    L ≃ₐ[ℚ]
      (abstractRelativeFixedField ℚ (SeparableClosure ℚ)
        (numberFieldTowerTopSubgroup_le_baseSubgroup K L)).restrictScalars ℚ :=
  (numberFieldSeparableClosureEmbedding L).equivFieldRange.trans
    (IntermediateField.equivOfEq
      (numberFieldTowerAbstractTopField_restrictScalars_eq K L).symm)

end Reciprocity
end GlobalClassFieldTheory
end
end


