-- Prove2me | Definitions.Def_OAIQ244Duke062
-- name    : OAIQ244Duke062
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-13T22:26:45.435094+00:00
-- url     : https://prove2.me/theorems/e1503f61-9f6b-4340-b625-fbd926b04595
-- title:
--   Definitions bundle OAIQ244Duke062 of the split of OpenAI, Equidistribution of Prime-Degree Torus Packets with Arbitrary Local Type
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.DukePrimeDegree.prime_degree_packet_measure_equidistribution_unconditional` and `OAI.DukePrimeDegree.prime_degree_packet_measures_tendsto_haar_unconditional`, carved from OpenAI's openai/math development (OpenAI, *Equidistribution of Prime-Degree Torus Packets with Arbitrary Local Type*, OpenAI Math Release, September 24, 2026, result family 15, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 113 declarations of OpenAI's Lean: 36 definitions, 5 instances and 72 theorems. The definitions and types are `GlobalClassFieldTheory.ClassFieldAxiom.actualPushoutNormQuotientMap`, `GlobalClassFieldTheory.ClassFieldAxiom.allFinitePlaceLocalNormCondition`, `GlobalClassFieldTheory.ClassFieldAxiom.allInfinitePlaceLocalNormCondition`, `GlobalClassFieldTheory.ClassFieldAxiom.allPlaceLocalNormCondition`, `GlobalClassFieldTheory.ClassFieldAxiom.sUnitEquivSupportedPrincipalIdeleSubgroup`, `GlobalClassFieldTheory.ClassFieldAxiom.sUnitPrincipalIdelePowerQuotientEquivSupportedPrincipalQuotient`, `GlobalClassFieldTheory.ClassFieldAxiom.sUnitPrincipalIdelePowerSubgroup`, `GlobalClassFieldTheory.ClassFieldAxiom.supportedIdeleClassPowerDenominator`, `GlobalClassFieldTheory.ClassFieldAxiom.supportedIdeleClassPowerQuotientEquiv`, `GlobalClassFieldTheory.ClassFieldAxiom.supportedIdeleToClassPowerQuotient`, `GlobalClassFieldTheory.ClassFieldAxiom.supportedPrincipalIdeleSubgroup`, `GlobalClassFieldTheory.Reciprocity.finitePlaceNormLocalizedAut`, `IdeleGroup.classRepresentative`, `LocalClassFieldTheory.abelianizationEquivNormQuotient`, `LocalClassFieldTheory.concreteReciprocityAddEquivOfEmbedding`, `LocalClassFieldTheory.concreteReciprocityEquiv`, `LocalClassFieldTheory.concreteReciprocityEquivOfEmbedding`, `LocalClassFieldTheory.extensionQuotientCongr`, `LocalClassFieldTheory.finiteGaloisAbstractExtensionOfEmbedding`, `LocalClassFieldTheory.finiteGaloisConjugationOfEmbeddings`, `LocalClassFieldTheory.finiteGaloisEmbeddingNormAddZeroClass`, `LocalClassFieldTheory.finiteNormQuotientCongr`, `LocalFieldTheory.DiscreteValuationField.LocalField.chosenMixed_firstPrincipalUnitAlgebraicData`, `LocalFieldTheory.DiscreteValuationField.LocalField.chosenMixed_firstPrincipalUnitStructure_ofWithZeroValuation`, `LocalFieldTheory.DiscreteValuationField.LocalField.mixed_deepPrincipalUnitLinearEquivPi`, `LocalFieldTheory.DiscreteValuationField.LocalField.mixed_firstPrincipalUnitFiniteQuotientSetup`, `LocalFieldTheory.DiscreteValuationField.LocalField.mixed_firstPrincipalUnitStructure`, `LocalFieldTheory.DiscreteValuationField.LocalField.mixed_integralBasis`, `LocalFieldTheory.DiscreteValuationField.LocalField.mixed_maximalIdealPowLinearEquivPi`, `LubinTate.padicValuationUnitToCompletedUnramifiedWittUnit`, `finitePlacesAbove`, `ordinaryIdeleClassNormQuotientCongrOfAlgEquiv`, `relativeAdeleCongrOfAlgEquiv`, `relativeIdeleClassCongrOfAlgEquiv`, `relativeIdeleCongrOfAlgEquiv`, `relativePrincipalSupportedIntersectionAction`.
--
--   **Sources.** They come from these modules of lean/OAI/NumberTheory, in whole or in part: `AbstractClassFieldTheory_Reciprocity_MaximalUnramifiedReciprocity`, `AbstractClassFieldTheory_Reciprocity_MaximalUnramifiedSymbol`, `AlgebraicNumberTheory_Idele_ClassGroup_AlgEquiv`, `AlgebraicNumberTheory_Idele_ClassGroup_NormComparison`, `AlgebraicNumberTheory_Idele_ClassGroup_TowerAlgEquivNaturality`, `AlgebraicNumberTheory_Idele_ClassGroup_TowerBaseChange`, `AlgebraicNumberTheory_Idele_Cohomology_SupportedBridge`, `AlgebraicNumberTheory_Idele_SufficientlyLarge`, `GlobalClassFieldTheory_ClassFieldAxiom_CyclicIdeleClassNormIndex`, `GlobalClassFieldTheory_ClassFieldAxiom_HasseNormPrinciple`, `GlobalClassFieldTheory_ClassFieldAxiom_IdeleClassPowerLocalUnitQuotient_FinitePlacePowerIndex`, `GlobalClassFieldTheory_ClassFieldAxiom_IdeleClassPowerLocalUnitQuotient_PrimePowerKummerIndex`, `GlobalClassFieldTheory_ClassFieldAxiom_IdeleClassPowerLocalUnitQuotient_SupportedIdeleIndex`, `GlobalClassFieldTheory_ClassFieldAxiom_IdeleClassPowerLocalUnitQuotient_SupportedPrincipalQuotient`, `GlobalClassFieldTheory_ClassFieldAxiom_IdelePowerLocalUnitNormContainment`, `GlobalClassFieldTheory_Reciprocity_FinitePlaceArtin_NormRestriction`, `LocalClassFieldTheory_Finite_LocalReciprocity_ConcreteReciprocityCanonical`, `LocalClassFieldTheory_Finite_LocalReciprocity_ConcreteReciprocityTransport`, `LocalClassFieldTheory_Finite_LocalReciprocity_Main`, `LocalField_DiscreteValuationField_FieldUnitPowerIndexFormulas`, `LocalField_DiscreteValuationField_MixedCharacteristicStructure_Core`, `LocalField_DiscreteValuationField_MixedCharacteristicStructure_DeepPrincipalUnits`, `LocalField_DiscreteValuationField_MixedCharacteristicStructure_IntegralLattice`, `LubinTate_Padic_ChangedUniformizerCoefficient`.
--
--   **Imports.** It imports the bundles `OAIQ244Duke053`, `OAIQ244Duke054`, `OAIQ244Duke055`, `OAIQ244Duke059` and `OAIQ244Duke060` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ244Duke069`, `OAIQ244Duke070`, `OAIQ244Duke072`, `OAIQ244Duke073` and `OAIQ244Duke113`.
-- source:
--   OpenAI, Equidistribution of Prime-Degree Torus Packets with Arbitrary Local Type, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 15; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Equidistribution-of-Prime-Degree-Torus-Packets-with-Arbitrary-Local-Type-September-24-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/NumberTheory at commit 7ef5c0c

import Mathlib
import Mathlib.Algebra.Algebra.Basic
import Mathlib.Algebra.Algebra.Pi
import Mathlib.Algebra.Algebra.Tower
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.GroupWithZero.Finset
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Category.ModuleCat.Basic
import Mathlib.Algebra.CharP.Algebra
import Mathlib.Algebra.CharP.Lemmas
import Mathlib.Algebra.CharP.Subring
import Mathlib.Algebra.EuclideanDomain.Basic
import Mathlib.Algebra.Exact.Basic
import Mathlib.Algebra.Group.Action.Basic
import Mathlib.Algebra.Group.Equiv.Basic
import Mathlib.Algebra.Group.Equiv.TypeTags
import Mathlib.Algebra.Group.Hom.Basic
import Mathlib.Algebra.Group.Int.TypeTags
import Mathlib.Algebra.Group.Pi.Basic
import Mathlib.Algebra.Group.Pi.Units
import Mathlib.Algebra.Group.Subgroup.Basic
import Mathlib.Algebra.Group.Subgroup.Finite
import Mathlib.Algebra.Group.Subgroup.Ker
import Mathlib.Algebra.Group.Subgroup.Map
import Mathlib.Algebra.Group.Submonoid.Units
import Mathlib.Algebra.Group.TransferInstance
import Mathlib.Algebra.Group.Units.Equiv
import Mathlib.Algebra.Group.Units.Hom
import Mathlib.Algebra.GroupWithZero.Action.Prod
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
import Mathlib.Combinatorics.Hall.Finite
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Finsupp
import Mathlib.Data.Finsupp.Fintype
import Mathlib.Data.Int.ModEq
import Mathlib.Data.Int.WithZero
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.Nat.Prime.Basic
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
import Mathlib.FieldTheory.Galois.Abelian
import Mathlib.FieldTheory.Galois.Basic
import Mathlib.FieldTheory.Galois.Infinite
import Mathlib.FieldTheory.Galois.IsGaloisGroup
import Mathlib.FieldTheory.Galois.NormalBasis
import Mathlib.FieldTheory.Galois.Notation
import Mathlib.FieldTheory.Galois.Profinite
import Mathlib.FieldTheory.IntermediateField.Adjoin.Algebra
import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
import Mathlib.FieldTheory.IntermediateField.Basic
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.FieldTheory.IsSepClosed
import Mathlib.FieldTheory.KrullTopology
import Mathlib.FieldTheory.LinearDisjoint
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
import Mathlib.NumberTheory.Cyclotomic.PrimitiveRoots
import Mathlib.NumberTheory.LocalField.Basic
import Mathlib.NumberTheory.NumberField.AdeleRing
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.NumberTheory.NumberField.ClassNumber
import Mathlib.NumberTheory.NumberField.Completion.FinitePlace
import Mathlib.NumberTheory.NumberField.Completion.InfinitePlace
import Mathlib.NumberTheory.NumberField.Completion.LiesOverInstances
import Mathlib.NumberTheory.NumberField.Completion.Ramification
import Mathlib.NumberTheory.NumberField.Cyclotomic.Basic
import Mathlib.NumberTheory.NumberField.InfinitePlace.Ramification
import Mathlib.NumberTheory.NumberField.ProductFormula
import Mathlib.NumberTheory.NumberField.Units.DirichletTheorem
import Mathlib.NumberTheory.NumberField.Units.Regulator
import Mathlib.NumberTheory.Ostrowski
import Mathlib.NumberTheory.Padics.HeightOneSpectrum
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
import Mathlib.RingTheory.DedekindDomain.Different
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
import Mathlib.RingTheory.LocalRing.Module
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
import Mathlib.RingTheory.WittVector.Compare
import Mathlib.RingTheory.WittVector.Complete
import Mathlib.RingTheory.WittVector.FrobeniusFractionField
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Tactic
import Mathlib.Topology.Algebra.Category.ProfiniteGrp.Basic
import Mathlib.Topology.Algebra.ClopenNhdofOne
import Mathlib.Topology.Algebra.ContinuousMonoidHom
import Mathlib.Topology.Algebra.Field
import Mathlib.Topology.Algebra.Group.Basic
import Mathlib.Topology.Algebra.Group.ClosedSubgroup
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
import Definitions.Def_OAIQ244Duke053
import Definitions.Def_OAIQ244Duke054
import Definitions.Def_OAIQ244Duke055
import Definitions.Def_OAIQ244Duke059
import Definitions.Def_OAIQ244Duke060

section
-- module Solutions.OAIQ244_DUKE.AbstractClassFieldTheory_Reciprocity_MaximalUnramifiedSymbol
attribute [-instance] _root_.ClassFormation.FiniteAbelianSubextension.normOpenAddSubgroupPartialOrder _root_.ClassFormation.FiniteGaloisSubextension.abelianIntermediateField_normalInstance _root_.ClassFormation.FiniteGaloisSubextension.extensionSubgroup_over_intermediate_normalInstance _root_.ClassFormation.FiniteGaloisSubextension.inertiaImage_normalInstance _root_.ClassFormation.FiniteGaloisSubextension.intermediateField_normalInstance _root_.ClassFormation.FiniteGaloisSubextension.intermediateSubgroup_normalInstance _root_.ClassFormation.FiniteGaloisSubextension.upperQuotient_groupInstance _root_.ClassFormation.instIsAddTorsionFreeZHat _root_.ClassFormation.instIsMulTorsionFreeMultiplicativeZHat _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.GlobalClassFields.finiteAbelianSubextensionAbstractRelativeFixedFieldFiniteDimensional _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.KummerTheory.finite_finsupp_nsmulQuotient _root_.KummerTheory.finite_sUnit_nthPowerQuotient _root_.LocalClassFieldTheory.baseFixingExtensionQuotient_finite _root_.LocalClassFieldTheory.baseFixingExtensionQuotient_finite_of_isSeparable _root_.LocalClassFieldTheory.extensionSubgroupBase_normal _root_.LocalClassFieldTheory.finiteGaloisExtensionSubgroupOfEmbedding_normal _root_.LocalClassFieldTheory.finiteGaloisLocalField_integerRing_moduleFinite _root_.LocalClassFieldTheory.localDecompositionResidueFinite _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitQuotientCarrier_finite _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitSubquotientFinite _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.quotientMaximalIdealPowFinite _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.unitsModHigherPrincipalUnitGroupFinite _root_.LocalFieldTheory.DiscreteValuationField.finite_padicInt_finPi_nsmulQuotient _root_.LocalFieldTheory.DiscreteValuationField.finite_padicInt_pi_nsmulQuotient_of_coprime _root_.LocalFieldTheory.DiscreteValuationField.finite_valuationSubringUnits_nthPowerQuotient _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_multiplicative_nthPowerQuotient _root_.LocalFieldTheory.finite_nsmulAddQuotient_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.LubinTate.compatibleGroupFamiliesGroup _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.boundedRealFields_finite _root_.OAI.PrimeDegreePackets.instTopologicalSpaceLocalAlgebra _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RamificationTheory.HilbertRamification.ValuationSubring.inertiaGroup_normal _root_.RamificationTheory.HilbertRamification.ValuationSubring.ramificationGroupInInertiaAut_normal _root_.RayClass.Modulus.congruenceSubgroup_normal _root_.RayClass.approximationCompletionTopologicalSpace _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.LocalClassFieldTheory.comparisonIntegerRingIsIntegralClosure _root_.LocalClassFieldTheory.normalizationIntegerRingIsIntegralClosure _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen _root_.infiniteAdeleRingT2Space
attribute [-simp] _root_.ClassFormation.DegreeData.abstractReciprocityEquiv_apply_of _root_.ClassFormation.DegreeData.abstractReciprocityTotallyRamifiedFrobeniusInM_restriction _root_.ClassFormation.DegreeData.abstractReciprocityTotallyRamifiedLowerGenerator_inclusion_restriction _root_.ClassFormation.DegreeData.abstractReciprocityTotallyRamifiedRestrictionEquiv_lowerGenerator _root_.ClassFormation.DegreeData.abstractReciprocity_normResidueSymbol _root_.ClassFormation.DegreeData.frobeniusExponent_chosenDegreeOneFrobeniusLiftOfFiniteTotallyRamified _root_.ClassFormation.DegreeData.frobeniusExponent_chosenDegreeOneFrobeniusLiftOfTotallyRamified _root_.ClassFormation.DegreeData.frobeniusRestriction_chosenDegreeOneFrobeniusLiftOfFiniteTotallyRamified _root_.ClassFormation.DegreeData.frobeniusRestriction_chosenDegreeOneFrobeniusLiftOfTotallyRamified _root_.ClassFormation.DegreeData.normResidueSymbol_finiteReciprocityHom _root_.ClassFormation.FiniteAbelianSubextension.normSubgroupMap_val _root_.ClassFormation.FiniteGaloisSubextension.classFieldCandidate_field _root_.ClassFormation.FiniteGaloisSubextension.intermediateNormMap_finiteNormClass _root_.ClassFormation.FiniteGaloisSubextension.intermediateNormQuotientInclusion_finiteNormClass _root_.ClassFormation.abstractReciprocityNormMap_finiteNormClass _root_.ClassFormation.abstractReciprocityNormProjection_finiteNormClass _root_.ClassFormation.cyclicNormClassHom_apply _root_.ClassFormation.extensionFixedRepresentationEquiv_apply_coe _root_.ClassFormation.extensionFixedRepresentationEquiv_symm_apply_coe _root_.ClassFormation.mem_normFilterBasis_iff _root_.ClassFormation.toZModPow_zHatToPadicInt _root_.ClassFormation.zHatReductionRingHom_apply _root_.ClassFormation.zHatRingEquivProfiniteIntegerPrimeProduct_apply _root_.ClassFormation.zHatToPadicInt_intCast _root_.ClassFormation.zHatToProfiniteIntegerPrimeProduct_apply _root_.ClassFormation.zHatToProfiniteIntegerPrimeProduct_intCast _root_.ClassFormation.zHatUnitsContinuousMulEquivPrimeProduct_coe_apply _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.IsDiscreteValuationRing.addVal_ringEquiv _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.KummerTheory.torsionQuotientEquivOfZHatMulDecomposition_mk _root_.KummerTheory.zHatUnitsContinuousMulEquivPrimeProduct_rationalCyclotomicCharacter _root_.LocalClassFieldTheory.abstractFixedFieldUnitsEquivGaloisFixed_coe _root_.LocalClassFieldTheory.abstractRelativeFixedFieldUnitsEquivGaloisFixed_coe _root_.LocalClassFieldTheory.abstractRelativeUnitsEquiv_extensionUnitsEquiv _root_.LocalClassFieldTheory.baseFieldUnitsEquiv_val _root_.LocalClassFieldTheory.baseUnitsEquivGaloisAmbientFixed_val _root_.LocalClassFieldTheory.embeddedFieldUnitsEquivGaloisFixed_coe _root_.LocalClassFieldTheory.finiteGaloisUnitsEquivAbstractFixedOfEmbedding_coe _root_.LocalClassFieldTheory.finiteGaloisUnitsEquivAbstractFixed_coe _root_.LocalClassFieldTheory.finiteNormQuotientEquivEmbeddedNormQuotient_finiteNormClass _root_.LocalClassFieldTheory.finiteNormQuotientEquivNormQuotient_finiteNormClass _root_.LocalClassFieldTheory.finiteResidueFrobeniusFromZHat_apply _root_.LocalClassFieldTheory.finiteResidueFrobeniusFromZHat_one _root_.LocalClassFieldTheory.intermediateFieldUnitsEquivGaloisFixed_coe _root_.LocalClassFieldTheory.intrinsicFiniteAbstractBase_eq_base _root_.LocalClassFieldTheory.localBaseValuation_baseFieldUnitsEquiv _root_.LocalClassFieldTheory.residueAbsoluteDegreeIn_frobenius _root_.LocalClassFieldTheory.residueAbsoluteFrobenius_one _root_.LocalClassFieldTheory.residueFrobeniusToLimit_apply_component _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.LocalFieldTheory.residueField_algebraMap_residue _root_.OAI.PrimeDegreePackets.ThetaConstruction.schwartzCM_apply _root_.RayClass.primesEquiv_val_eq_natGenerator _root_.infinitePlace_mult_smul
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

section Representation

-- Mathlib's `Rep ℤ G` currently fixes the acting group to universe zero.
variable {G : IntegralRepGroupType} [Group G] [TopologicalSpace G]
variable {D : DegreeData G} {A : Rep ℤ G}

open DegreeData

namespace ValuationData

/-- A finite unramified reciprocity homomorphism which sends Frobenius to
the prime class intertwines the canonical valuation and normalized-degree
isomorphisms.  This is the generator calculation in the unramified norm-quotient equivalence,
expressed in the normalization needed. -/
theorem canonicalUnramifiedReciprocity_degree_of_generator
    (v : ValuationData D A)
    [IsTopologicalGroup G] [CompactSpace G] [T2Space G]
    (K : FiniteAbstractField G) (L : FiniteGaloisSubextension K.field) :
    letI : Finite
        (K.field.toSubgroup ⧸
          extensionSubgroup K.field L.field L.below) := L.finite
    ∀ (hUnramified : L.IsUnramified D)
      (r : Additive L.extensionQuotient →+
        FiniteNormQuotient A K.field L.field L.below)
      (_hr : r (Additive.ofMul (D.unramifiedFrobenius
          (K.toFiniteResidueAbstractField D) L.field L.below)) =
        finiteNormClass A K.field L.field L.below (v.chosenPrimeElement K))
      (q : Additive L.extensionQuotient),
    v.canonicalUnramifiedNormQuotientValuation
        L.toFiniteAbstractFieldExtension hUnramified
        (r q) =
      (finiteUnramifiedDegreeEquiv D (K.toFiniteResidueAbstractField D)
        L hUnramified
        q.toMul).toAdd := by
  let : Finite
      (K.field.toSubgroup ⧸
        extensionSubgroup K.field L.field L.below) := L.finite
  intro hUnramified r hr q
  let KR := K.toFiniteResidueAbstractField D
  let g : Additive L.extensionQuotient :=
    Additive.ofMul (D.unramifiedFrobenius KR L.field L.below)
  let lhs : Additive L.extensionQuotient →+
      ZMod (L.toFiniteAbstractFieldExtension.degree : ℕ) :=
    (v.canonicalUnramifiedNormQuotientValuation
      L.toFiniteAbstractFieldExtension hUnramified).comp r
  let rhs : Additive L.extensionQuotient →+
      ZMod (L.toFiniteAbstractFieldExtension.degree : ℕ) :=
    (finiteUnramifiedDegreeEquiv D
      KR L hUnramified).toAdditive.toAddMonoidHom
  change lhs q = rhs q
  have hgen : lhs g = rhs g := by
    change v.canonicalUnramifiedNormQuotientValuation
        L.toFiniteAbstractFieldExtension hUnramified
        (r g) =
      (finiteUnramifiedDegreeEquiv D KR L hUnramified
        g.toMul).toAdd
    rw [show r g = finiteNormClass A K.field L.field L.below
        (v.chosenPrimeElement K) from hr]
    change v.canonicalUnramifiedValuationHom
      L.toFiniteAbstractFieldExtension
      (v.chosenPrimeElement K) = _
    change v.canonicalValueReduction
        (L.toFiniteAbstractFieldExtension.degree : ℕ)
        _ (v.valuationAt K (v.chosenPrimeElement K)) = _
    exact (congrArg
      (v.canonicalValueReduction (L.toFiniteAbstractFieldExtension.degree : ℕ)
        L.toFiniteAbstractFieldExtension.degree.property)
      (v.valuationAt_chosenPrimeElement K)).trans <|
      (v.canonicalValueReduction_one (L.toFiniteAbstractFieldExtension.degree : ℕ)
        L.toFiniteAbstractFieldExtension.degree.property).trans <|
        congrArg Multiplicative.toAdd
          (finiteUnramifiedDegreeEquiv_unramifiedFrobenius D
            KR L hUnramified).symm
  have hqmem : q ∈ AddSubgroup.zmultiples g := by
    rw [show AddSubgroup.zmultiples g = ⊤ from
      D.unramifiedFrobenius_zmultiples_eq_top
        KR L.field L.below hUnramified]
    trivial
  obtain ⟨m, hm⟩ := AddSubgroup.mem_zmultiples_iff.mp hqmem
  rw [← hm, map_zsmul, map_zsmul, hgen]

/-- Applying normalized degree to the maximal-unramified symbol recovers the valuation. -/
@[simp]
theorem maximalUnramifiedNormResidue_degree
    (v : ValuationData D A)
    (K : FiniteAbstractField G)
    (a : ambientFixedAddSubgroup A K.field) :
    ((D.maximalUnramifiedDegreeEquiv (K.toFiniteResidueAbstractField D)
      (maximalUnramifiedNormResidueSymbol v K a).toMul).toAdd : ZHat) =
        (v.valuationAt K a : ZHat) := by
  change (D.maximalUnramifiedDegreeEquiv
      (K.toFiniteResidueAbstractField D)).toAdditive
      ((D.maximalUnramifiedDegreeEquiv
        (K.toFiniteResidueAbstractField D)).toAdditive.symm
        ((v.valueGroup).subtype (v.valuationAt K a))) =
    (v.valuationAt K a : ZHat)
  exact (D.maximalUnramifiedDegreeEquiv
    (K.toFiniteResidueAbstractField D)).toAdditive.apply_symm_apply
      ((v.valueGroup).subtype (v.valuationAt K a))

/-- At every finite unramified quotient, normalized degree of the
maximal-unramified symbol is valuation reduced modulo the extension degree. -/
theorem maximalUnramifiedNormResidueSymbol_finiteDegree
    (v : ValuationData D A)
    (K : FiniteAbstractField G) (L : FiniteGaloisSubextension K.field)
    (hUnramified : L.IsUnramified D)
    (a : ambientFixedAddSubgroup A K.field) :
    (finiteUnramifiedDegreeEquiv D (K.toFiniteResidueAbstractField D)
      L hUnramified
      (finiteUnramifiedRestriction D
        (K.toFiniteResidueAbstractField D) L hUnramified
        (maximalUnramifiedNormResidueSymbol v K a).toMul)).toAdd =
      zHatReduction
        (L.toFiniteAbstractFieldExtension.degree : ℕ)
        L.toFiniteAbstractFieldExtension.degree.property
        (v.valuationAt K a : ZHat) := by
  let KR := K.toFiniteResidueAbstractField D
  have h := finiteUnramifiedDegreeEquiv_restriction D
    KR L hUnramified
      (maximalUnramifiedNormResidueSymbol v K a).toMul
  have hv := maximalUnramifiedNormResidue_degree v K a
  exact congrArg Multiplicative.toAdd h |>.trans (by
    change zHatReduction
        (L.toFiniteAbstractFieldExtension.degree : ℕ)
        L.toFiniteAbstractFieldExtension.degree.property
        ((D.maximalUnramifiedDegreeEquiv KR
          (maximalUnramifiedNormResidueSymbol v K a).toMul).toAdd) = _
    rw [hv])

/-- The maximal-unramified symbol extends every finite unramified reciprocity map: after
restriction to `G(L/K)`, applying finite reciprocity gives the class of the
original element.  This is the non-circular compatibility statement which
identifies the symbol with the inverse-limit norm-residue map. -/
theorem maximalUnramifiedNormResidueSymbol_finiteReciprocity_of_generator
    (v : ValuationData D A) (hAxiom : v.SatisfiesUnramifiedUnitCohomology D)
    [IsTopologicalGroup G] [CompactSpace G] [T2Space G]
    (K : FiniteAbstractField G) (L : FiniteGaloisSubextension K.field) :
    letI : Finite
        (K.field.toSubgroup ⧸
          extensionSubgroup K.field L.field L.below) := L.finite
    ∀ (hUnramified : L.IsUnramified D)
      (r : Additive L.extensionQuotient →+
        FiniteNormQuotient A K.field L.field L.below)
      (_hr : r (Additive.ofMul (D.unramifiedFrobenius
          (K.toFiniteResidueAbstractField D) L.field L.below)) =
        finiteNormClass A K.field L.field L.below (v.chosenPrimeElement K))
      (a : ambientFixedAddSubgroup A K.field),
    r (Additive.ofMul
        (finiteUnramifiedRestriction D
          (K.toFiniteResidueAbstractField D) L hUnramified
          (maximalUnramifiedNormResidueSymbol v K a).toMul)) =
      finiteNormClass A K.field L.field L.below a := by
  let : Finite
      (K.field.toSubgroup ⧸
        extensionSubgroup K.field L.field L.below) := L.finite
  intro hUnramified r hr a
  apply v.canonicalUnramifiedNormQuotientValuation_injective
    hAxiom L.toFiniteAbstractFieldExtension L.normal hUnramified
  rw [canonicalUnramifiedReciprocity_degree_of_generator v
    K L hUnramified r hr]
  change _ = v.canonicalUnramifiedValuationHom
    L.toFiniteAbstractFieldExtension a
  exact maximalUnramifiedNormResidueSymbol_finiteDegree v
    K L hUnramified a

/-- The finite restriction of the maximal-unramified symbol is the
inverse of finite unramified reciprocity.  The map `r` is kept explicit
here so this statement records the uniqueness argument of maximal-unramified reciprocity
without anticipating the final name of the finite reciprocity equivalence: the unramified norm-quotient equivalence
promotes any reciprocity map with the Frobenius--prime value to an
equivalence, and the preceding compatibility identifies its inverse. -/
theorem maximalUnramifiedNormResidueSymbol_finiteRestriction_of_generator
    (v : ValuationData D A) (hAxiom : v.SatisfiesUnramifiedUnitCohomology D)
    [IsTopologicalGroup G] [CompactSpace G] [T2Space G]
    (K : FiniteAbstractField G) (L : FiniteGaloisSubextension K.field) :
    letI : Finite
        (K.field.toSubgroup ⧸
          extensionSubgroup K.field L.field L.below) := L.finite
    ∀ (hUnramified : L.IsUnramified D)
      (r : Additive L.extensionQuotient →+
        FiniteNormQuotient A K.field L.field L.below)
      (hr : r (Additive.ofMul (D.unramifiedFrobenius
          (K.toFiniteResidueAbstractField D) L.field L.below)) =
        finiteNormClass A K.field L.field L.below (v.chosenPrimeElement K))
      (a : ambientFixedAddSubgroup A K.field),
    (v.unramifiedReciprocity_equiv_of_generator hAxiom K L.field L.below
        hUnramified r hr).symm
        (finiteNormClass A K.field L.field L.below a) =
      Additive.ofMul
        (finiteUnramifiedRestriction D
          (K.toFiniteResidueAbstractField D) L hUnramified
          (maximalUnramifiedNormResidueSymbol v K a).toMul) := by
  let : Finite
      (K.field.toSubgroup ⧸
        extensionSubgroup K.field L.field L.below) := L.finite
  intro hUnramified r hr a
  apply (v.unramifiedReciprocity_equiv_of_generator hAxiom K L.field L.below
    hUnramified r hr).injective
  rw [AddEquiv.apply_symm_apply]
  exact (maximalUnramifiedNormResidueSymbol_finiteReciprocity_of_generator v hAxiom
    K L hUnramified r hr a).symm

end ValuationData

end Representation

end ClassFormation
end
end

section
-- module Solutions.OAIQ244_DUKE.AbstractClassFieldTheory_Reciprocity_MaximalUnramifiedReciprocity
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 400000
attribute [-instance] _root_.ClassFormation.FiniteAbelianSubextension.normOpenAddSubgroupPartialOrder _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.GlobalClassFields.finiteAbelianSubextensionAbstractRelativeFixedFieldFiniteDimensional _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalClassFieldTheory.baseFixingExtensionQuotient_finite _root_.LocalClassFieldTheory.baseFixingExtensionQuotient_finite_of_isSeparable _root_.LocalClassFieldTheory.extensionSubgroupBase_normal _root_.LocalClassFieldTheory.finiteGaloisExtensionSubgroupOfEmbedding_normal _root_.LocalClassFieldTheory.finiteGaloisLocalField_integerRing_moduleFinite _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.LubinTate.compatibleGroupFamiliesGroup _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RamificationTheory.HilbertRamification.ValuationSubring.inertiaGroup_normal _root_.RamificationTheory.HilbertRamification.ValuationSubring.ramificationGroupInInertiaAut_normal _root_.RayClass.Modulus.congruenceSubgroup_normal _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.ValuationSubring.charP _root_.CyclicCohomology.binaryCoefficientFamilyCommGroup _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.LocalClassFieldTheory.comparisonIntegerRingIsIntegralClosure _root_.LocalClassFieldTheory.normalizationIntegerRingIsIntegralClosure _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen _root_.infiniteAdeleRingT2Space _root_.relativeUnrestrictedSPlaceFactorCommGroup
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

/-!
# Abstract reciprocity, maximal-unramified reciprocity

The maximal-unramified norm-residue symbol is realized by the
valuation--Frobenius map whose restriction to every finite unramified
extension is the inverse of the unramified norm-quotient equivalence.  This file first proves that
finite compatibility and then records the two formulas.
-/

noncomputable section

namespace ClassFormation

open ClassFormation CyclicCohomology KummerTheory

-- Mathlib's `Rep ℤ G` currently fixes the acting group to universe zero.
variable {G : IntegralRepGroupType} [Group G] [TopologicalSpace G]
variable {D : DegreeData G} {A : Rep ℤ G}

namespace ValuationData

/-- On every finite unramified quotient, the maximal-unramified symbol is
the inverse of the actual reciprocity equivalence of the unramified norm-quotient equivalence.
This is the inverse-limit compatibility used to define the infinite symbol. -/
theorem maximalUnramifiedNormResidueSymbol_finiteRestriction
    (v : ValuationData D A) (hAxiom : v.SatisfiesUnramifiedUnitCohomology D)
    [IsTopologicalGroup G] [CompactSpace G] [T2Space G]
    [TotallyDisconnectedSpace G]
    (K : FiniteAbstractField G) (L : FiniteGaloisSubextension K.field)
    (hUnramified : L.IsUnramified D) :
    letI : Finite (K.field.toSubgroup ⧸
        extensionSubgroup K.field L.field L.below) := L.finite
    ∀ a : ambientFixedAddSubgroup A K.field,
    Additive.ofMul
        (DegreeData.finiteUnramifiedRestriction D
          (K.toFiniteResidueAbstractField D) L hUnramified
          (maximalUnramifiedNormResidueSymbol v K a).toMul) =
      (v.unramifiedReciprocityEquiv hAxiom
        K L.field L.below hUnramified).symm
        (finiteNormClass A K.field L.field L.below a) := by
  let : Finite (K.field.toSubgroup ⧸
      extensionSubgroup K.field L.field L.below) := L.finite
  intro a
  exact (maximalUnramifiedNormResidueSymbol_finiteRestriction_of_generator v hAxiom
    K L hUnramified
      (D.finiteReciprocityHom A v hAxiom K L.field L.below)
      (v.unramifiedReciprocity_frobenius_image hAxiom
        K L.field L.below hUnramified) a).symm

/-- For a finite unramified extension, the restriction of the
maximal-unramified norm-residue symbol is exactly the finite abstract
norm-residue symbol.  This is the source-level bridge from maximal
unramified reciprocity to the finite reciprocity theorem. -/
theorem normResidueSymbol_finiteNormClass_eq_maximalUnramifiedRestriction
    (v : ValuationData D A) (hcf : SatisfiesClassFieldAxiom A)
    [IsTopologicalGroup G] [CompactSpace G] [T2Space G]
    [TotallyDisconnectedSpace G]
    (K : FiniteAbstractField G) (L : FiniteGaloisSubextension K.field)
    (hUnramified : L.IsUnramified D)
    (a : ambientFixedAddSubgroup A K.field) :
    letI : Finite
        (K.field.toSubgroup ⧸
          extensionSubgroup K.field L.field L.below) := L.finite
    D.normResidueSymbol A v hcf K L
        (finiteNormClass A K.field L.field L.below a) =
      Additive.ofMul
        (Abelianization.of
          (DegreeData.finiteUnramifiedRestriction D
            (K.toFiniteResidueAbstractField D) L hUnramified
            (maximalUnramifiedNormResidueSymbol v K a).toMul)) := by
  let : Finite
      (K.field.toSubgroup ⧸
        extensionSubgroup K.field L.field L.below) := L.finite
  let hAxiom :=
    v.classFieldAxiom_implies_unramifiedUnitCohomology hcf
  let q :=
    DegreeData.finiteUnramifiedRestriction D
      (K.toFiniteResidueAbstractField D) L hUnramified
      (maximalUnramifiedNormResidueSymbol v K a).toMul
  have hrestriction :=
    maximalUnramifiedNormResidueSymbol_finiteRestriction
      v hAxiom K L hUnramified a
  have hreciprocity :
      v.unramifiedReciprocityEquiv hAxiom
          K L.field L.below hUnramified
          (Additive.ofMul q) =
        finiteNormClass A K.field L.field L.below a := by
    calc
      _ =
          v.unramifiedReciprocityEquiv hAxiom
            K L.field L.below hUnramified
            ((v.unramifiedReciprocityEquiv hAxiom
              K L.field L.below hUnramified).symm
              (finiteNormClass A K.field L.field L.below a)) :=
        congrArg
          (v.unramifiedReciprocityEquiv hAxiom
            K L.field L.below hUnramified)
          hrestriction
      _ = _ :=
        (v.unramifiedReciprocityEquiv hAxiom
          K L.field L.below hUnramified).apply_symm_apply _
  have hfinite : D.finiteReciprocityHom A v hAxiom K L.field L.below
        (Additive.ofMul q) = finiteNormClass A K.field L.field L.below a :=
    (v.unramifiedReciprocityEquiv_apply hAxiom K L.field L.below hUnramified
      (Additive.ofMul q)).symm.trans hreciprocity
  exact (congrArg (D.normResidueSymbol A v hcf K L) hfinite.symm).trans
    (D.normResidueSymbol_finiteReciprocityHom A v hcf K L q)

end ValuationData

end ClassFormation
end
end

section
-- module Solutions.OAIQ244_DUKE.LocalClassFieldTheory_Finite_LocalReciprocity_ConcreteReciprocityTransport
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.GlobalClassFields.finiteAbelianSubextensionAbstractRelativeFixedFieldFiniteDimensional _root_.GlobalClassFieldTheory.Reciprocity.infinitePlaceComplexificationOverfield_algebra _root_.GlobalClassFieldTheory.Reciprocity.infinitePlaceComplexificationOverfield_baseAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.KummerTheory.finite_finsupp_nsmulQuotient _root_.KummerTheory.finite_sUnit_nthPowerQuotient _root_.KummerTheory.primeCyclotomicBaseFiniteDimensional _root_.KummerTheory.primeCyclotomicBaseIsGalois _root_.LocalClassFieldTheory.baseFixingExtensionQuotient_finite_of_isSeparable _root_.LocalClassFieldTheory.finiteGaloisLocalField_integerRing_moduleFinite _root_.LocalClassFieldTheory.localDecompositionResidueFinite _root_.LocalClassFieldTheory.realComplexNormQuotientFinite _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitQuotientCarrier_finite _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitSubquotientFinite _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.quotientMaximalIdealPowFinite _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.residueFieldZModAlgebra _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.unitsModHigherPrincipalUnitGroupFinite _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedIntegralAlgebraContextValuationSubringAlgebra _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedQPadicContextValuationSubringTower _root_.LocalFieldTheory.DiscreteValuationField.finite_padicInt_finPi_nsmulQuotient _root_.LocalFieldTheory.DiscreteValuationField.finite_padicInt_pi_nsmulQuotient_of_coprime _root_.LocalFieldTheory.DiscreteValuationField.finite_valuationSubringUnits_nthPowerQuotient _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_multiplicative_nthPowerQuotient _root_.LocalFieldTheory.finite_nsmulAddQuotient_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.LubinTate.compatibleGroupFamiliesGroup _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.boundedRealFields_finite _root_.OAI.PrimeDegreePackets.instT2SpaceLocalAlgebra _root_.OAI.PrimeDegreePackets.instTopologicalSpaceLocalAlgebra _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.OAI.PrimeDegreePackets.xT2Space _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionResidueExtension_normal _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionResidueField.instField _root_.RamificationTheory.HilbertRamification.ValuationSubring.inertiaGroup_normal _root_.RamificationTheory.HilbertRamification.ValuationSubring.ramificationGroupInInertiaAut_normal _root_.RamificationTheory.HilbertRamification.ValuationSubring.selectedResidueField.instAlgebra _root_.RayClass.Modulus.congruenceSubgroup_normal _root_.RayClass.approximationCompletionTopologicalSpace _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.residueField.field _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.isDomain _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.isLocalRing _root_.ValuationTheory.ValuationSubring.charP _root_.CyclicCohomology.binaryCoefficientFamilyCommGroup _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.LocalClassFieldTheory.comparisonIntegerRingIsIntegralClosure _root_.LocalClassFieldTheory.normalizationIntegerRingIsIntegralClosure _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.chosenFinitePlaceCompletionAlgebra _root_.chosenFinitePlaceCompletionFiniteDimensional _root_.chosenFinitePlaceLocalizedFiniteDimensional _root_.chosenFinitePlaceLocalizedIsGalois _root_.cyclicPrimeDegreeIntermediate_isGalois _root_.cyclicPrimeSubextension_isGalois _root_.finiteIdeleGroupIsTopologicalGroup _root_.finiteIdeleGroupT2Space _root_.finiteLocalUnitsOpen _root_.finiteNormalClosure_isGalois _root_.ideleGroupIsTopologicalGroup _root_.ideleGroupT2Space _root_.infiniteAdeleRingT2Space _root_.infiniteIdeleGroupT2Space _root_.relativeAdeleRingIntermediateAlgebra _root_.relativeAdeleRingTopIntermediateAlgebra _root_.relativeUnrestrictedSPlaceFactorCommGroup
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

namespace LocalClassFieldTheory
open RamificationTheory KummerTheory CyclicCohomology

open LocalFieldTheory

open ClassFormation

/-!
# Finite local reciprocity: transport of abstract reciprocity to a field extension

This file contains the final comparison step in the proof of the local
reciprocity law.  Once the actual absolute-Galois datum, henselian valuation,
and class-field axiom have been constructed, the abstract reciprocity theorem is transported
through the concrete finite Galois realization in a separable closure and
through the actual field norm.

The coefficient module remains `(SeparableClosure K)ˣ`; this is essential in
imperfect positive characteristic.
-/

noncomputable section

variable (K L : Type) [Field K] [Field L] [Algebra K L]
  [FiniteDimensional K L] [IsGalois K L]

/-! ## Transport relative to an explicit embedding -/

/-- The finite abstract extension object determined by an explicit
embedding of `L` into the fixed separable closure. -/
def finiteGaloisAbstractExtensionOfEmbedding
    (i : L →ₐ[K] SeparableClosure K) : FiniteGaloisSubextension (B_p1 K) where
  field := finiteGaloisClosedFixingSubgroupOfEmbedding K L i
  below := fixingSubgroupLeBase K (SeparableClosure K)
    (finiteGaloisFieldRangeOfEmbedding K L i)
  normal := inferInstance
  finite := baseFixingExtensionQuotient_finite K (SeparableClosure K)
    (finiteGaloisFieldRangeOfEmbedding K L i)

/-- The additive reciprocity equivalence transported through an explicit
realization of `L/K` in the separable closure. -/
def concreteReciprocityAddEquivOfEmbedding
    (i : L →ₐ[K] SeparableClosure K)
    (D : DegreeData (G_p1 K)) (v : ValuationData D (A_p0 K))
    (hcf : SatisfiesClassFieldAxiom (A_p0 K)) :
    Additive (Abelianization Gal(L / K)) ≃+
      Additive (NormQuotient K L) :=
  (MulEquiv.toAdditive
      ((finiteGaloisAbstractQuotientEquivGaloisGroupOfEmbedding K L i).abelianizationCongr.symm)).trans
    ((D.abstractReciprocityEquiv (A_p0 K) v hcf (intrinsicFiniteAbstractBase K)
      (finiteGaloisAbstractExtensionOfEmbedding K L i)).trans
        (finiteNormQuotientEquivEmbeddedNormQuotient
          K (SeparableClosure K) L i))

/-- Multiplicative form of reciprocity transported through an explicit
embedding. -/
def concreteReciprocityEquivOfEmbedding
    (i : L →ₐ[K] SeparableClosure K)
    (D : DegreeData (G_p1 K)) (v : ValuationData D (A_p0 K))
    (hcf : SatisfiesClassFieldAxiom (A_p0 K)) :
    Abelianization Gal(L / K) ≃* NormQuotient K L := by
  let e : Additive (Abelianization Gal(L / K)) ≃+
      Additive (NormQuotient K L) :=
    concreteReciprocityAddEquivOfEmbedding K L i D v hcf
  let em : Multiplicative (Additive (Abelianization Gal(L / K))) ≃*
      Multiplicative (Additive (NormQuotient K L)) :=
    @AddEquiv.toMultiplicative
      (Additive (Abelianization Gal(L / K)))
      (Additive (NormQuotient K L)) inferInstance inferInstance e
  exact (MulEquiv.multiplicativeAdditive
      (Abelianization Gal(L / K))).symm.trans
    (em.trans
        (MulEquiv.multiplicativeAdditive (NormQuotient K L)))

/-- The public multiplicative form of the transported reciprocity
isomorphism `G(L/K)ᵃᵇ ≃ Kˣ/N_{L/K}Lˣ`. -/
def concreteReciprocityEquiv
    (D : DegreeData (G_p1 K)) (v : ValuationData D (A_p0 K))
    (hcf : SatisfiesClassFieldAxiom (A_p0 K)) :
    Abelianization Gal(L / K) ≃* NormQuotient K L :=
  concreteReciprocityEquivOfEmbedding K L
    (AlgebraicNumberTheory.separableEmbeddingIntoSeparableClosure K L) D v hcf

end
end LocalClassFieldTheory
end

section
-- module Solutions.OAIQ244_DUKE.LocalClassFieldTheory_Finite_LocalReciprocity_ConcreteReciprocityCanonical
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.GlobalClassFields.finiteAbelianSubextensionAbstractRelativeFixedFieldFiniteDimensional _root_.GlobalClassFieldTheory.Reciprocity.infinitePlaceComplexificationOverfield_algebra _root_.GlobalClassFieldTheory.Reciprocity.infinitePlaceComplexificationOverfield_baseAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.KummerTheory.finite_finsupp_nsmulQuotient _root_.KummerTheory.finite_sUnit_nthPowerQuotient _root_.KummerTheory.primeCyclotomicBaseFiniteDimensional _root_.KummerTheory.primeCyclotomicBaseIsGalois _root_.LocalClassFieldTheory.baseFixingExtensionQuotient_finite_of_isSeparable _root_.LocalClassFieldTheory.finiteGaloisLocalField_integerRing_moduleFinite _root_.LocalClassFieldTheory.localDecompositionResidueFinite _root_.LocalClassFieldTheory.realComplexNormQuotientFinite _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitQuotientCarrier_finite _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitSubquotientFinite _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.quotientMaximalIdealPowFinite _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.residueFieldZModAlgebra _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.unitsModHigherPrincipalUnitGroupFinite _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedIntegralAlgebraContextValuationSubringAlgebra _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedQPadicContextValuationSubringTower _root_.LocalFieldTheory.DiscreteValuationField.finite_padicInt_finPi_nsmulQuotient _root_.LocalFieldTheory.DiscreteValuationField.finite_padicInt_pi_nsmulQuotient_of_coprime _root_.LocalFieldTheory.DiscreteValuationField.finite_valuationSubringUnits_nthPowerQuotient _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_multiplicative_nthPowerQuotient _root_.LocalFieldTheory.finite_nsmulAddQuotient_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.LubinTate.compatibleGroupFamiliesGroup _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.boundedRealFields_finite _root_.OAI.PrimeDegreePackets.diagonalLogAction _root_.OAI.PrimeDegreePackets.instTopologicalSpaceLocalAlgebra _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionResidueExtension_normal _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionResidueField.instField _root_.RamificationTheory.HilbertRamification.ValuationSubring.inertiaGroup_normal _root_.RamificationTheory.HilbertRamification.ValuationSubring.ramificationGroupInInertiaAut_normal _root_.RamificationTheory.HilbertRamification.ValuationSubring.selectedResidueField.instAlgebra _root_.RayClass.Modulus.congruenceSubgroup_normal _root_.RayClass.approximationCompletionTopologicalSpace _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.RelativeIdeleGroup.relativeIdeleMulAction _root_.ValuationTheory.DiscreteValuationField.DVF.maximalIdealPowSuccQuotModule _root_.ValuationTheory.DiscreteValuationField.DVF.residueField.field _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.isDomain _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.isLocalRing _root_.ValuationTheory.ValuationSubring.charP _root_.CyclicCohomology.binaryCoefficientFamilyCommGroup _root_.CyclicCohomology.instMulDistribMulActionBinaryCoefficientFamily _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.LocalClassFieldTheory.comparisonIntegerRingIsIntegralClosure _root_.LocalClassFieldTheory.normalizationIntegerRingIsIntegralClosure _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.chosenFinitePlaceCompletionAlgebra _root_.chosenFinitePlaceCompletionFiniteDimensional _root_.chosenFinitePlaceLocalizedFiniteDimensional _root_.chosenFinitePlaceLocalizedIntegerAlgebra _root_.chosenFinitePlaceLocalizedIsGalois _root_.cyclicPrimeDegreeIntermediate_isGalois _root_.cyclicPrimeSubextension_isGalois _root_.finiteIdeleGroupIsTopologicalGroup _root_.finiteLocalUnitsOpen _root_.finiteNormalClosure_isGalois _root_.ideleGroupIsTopologicalGroup _root_.infiniteAdeleRingT2Space _root_.relativeAdeleRingIntermediateAlgebra _root_.relativeAdeleRingTopIntermediateAlgebra _root_.relativeUnrestrictedSPlaceFactorCommGroup
attribute [-simp] _root_.ClassFormation.DegreeData.finiteUnramifiedDegreeEquiv_unramifiedFrobenius _root_.ClassFormation.DegreeData.finiteUnramifiedDegreeHom_mk _root_.ClassFormation.DegreeData.finiteUnramifiedRestriction_frobenius _root_.ClassFormation.DegreeData.finiteUnramifiedRestriction_mk _root_.ClassFormation.DegreeData.maximalUnramifiedRestriction_frobenius _root_.ClassFormation.FiniteAbelianSubextension.extensionQuotientMk_apply _root_.ClassFormation.FiniteAbelianSubextension.normSubgroupMap_val _root_.ClassFormation.FiniteGaloisSubextension.classFieldCandidate_field _root_.ClassFormation.FiniteGaloisSubextension.intermediateFiniteAbelianOfCommutatorLe_field _root_.ClassFormation.ValuationData.maximalUnramifiedNormResidue_degree _root_.ClassFormation.mem_normFilterBasis_iff _root_.IsDiscreteValuationRing.addVal_ringEquiv _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.LocalClassFieldTheory.abstractFixedFieldUnitsEquivGaloisFixed_coe _root_.LocalClassFieldTheory.abstractRelativeFixedFieldUnitsEquivGaloisFixed_coe _root_.LocalClassFieldTheory.abstractRelativeUnitsEquiv_extensionUnitsEquiv _root_.LocalClassFieldTheory.baseFieldUnitsEquiv_val _root_.LocalClassFieldTheory.baseFixingCosetToAlgHom_mk _root_.LocalClassFieldTheory.localBaseValuation_baseFieldUnitsEquiv _root_.LocalClassFieldTheory.normQuotientMapOfRingEquiv_normClass _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.LocalFieldTheory.residueField_algebraMap_residue _root_.OAI.PrimeDegreePackets.ThetaConstruction.schwartzCM_apply _root_.RayClass.primesEquiv_val_eq_natGenerator _root_.infinitePlace_mult_smul
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

namespace LocalClassFieldTheory
open RamificationTheory CyclicCohomology KummerTheory

open LocalFieldTheory

open ClassFormation

/-!
# Finite local reciprocity: canonicity of local reciprocity

The construction of local reciprocity realizes a finite Galois extension in
a fixed separable closure.  This file proves that the transported reciprocity
isomorphism is independent of that realization.  Two embeddings are extended
to an automorphism of the separable closure, and
the abstract reciprocity naturality theorem supplies the required naturality.
-/

noncomputable section

variable (K L : Type) [Field K] [Field L] [Algebra K L]
  [FiniteDimensional K L] [IsGalois K L]

/-! ## Conjugating two realizations -/

omit [FiniteDimensional K L] [IsGalois K L] in
/-- With the right-exponent convention for abstract reciprocity, the conjugating
element is the inverse of the automorphism carrying `i` to `j`. -/
theorem finiteGaloisClosedFixingSubgroup_conjugator
    (i j : L →ₐ[K] SeparableClosure K) :
    conjugateClosedSubgroup
        (finiteGaloisClosedFixingSubgroupOfEmbedding K L i)
        (finiteGaloisEmbeddingConjugator K L i j)⁻¹ =
      finiteGaloisClosedFixingSubgroupOfEmbedding K L j := by
  let σ := finiteGaloisEmbeddingConjugator K L i j
  apply ClosedSubgroup.ext
  have hs :
      (conjugateClosedSubgroup
        (finiteGaloisClosedFixingSubgroupOfEmbedding K L i) σ⁻¹).toSubgroup =
        (finiteGaloisClosedFixingSubgroupOfEmbedding K L j).toSubgroup := by
    ext τ
    have hc : τ ∈ (conjugateClosedSubgroup
          (finiteGaloisClosedFixingSubgroupOfEmbedding K L i) σ⁻¹).toSubgroup ↔
        σ⁻¹ * τ * (σ⁻¹)⁻¹ ∈
          (finiteGaloisClosedFixingSubgroupOfEmbedding K L i).toSubgroup :=
      conjugateClosedSubgroup_mem
        (finiteGaloisClosedFixingSubgroupOfEmbedding K L i) σ⁻¹ τ
    rw [hc]
    change σ⁻¹ * τ * (σ⁻¹)⁻¹ ∈
        (finiteGaloisFieldRangeOfEmbedding K L i).fixingSubgroup ↔
      τ ∈ (finiteGaloisFieldRangeOfEmbedding K L j).fixingSubgroup
    rw [finiteGaloisFieldRange_conjugator K L i j]
    have hmap := IsGalois.map_fixingSubgroup
      (finiteGaloisFieldRangeOfEmbedding K L i)
      (finiteGaloisEmbeddingConjugator K L i j)
    have hmapmem := congrArg (fun H : Subgroup (G_p0 K) => τ ∈ H) hmap
    have hmem := Subgroup.mem_pointwise_smul_iff_inv_smul_mem
      (a := MulAut.conj (finiteGaloisEmbeddingConjugator K L i j))
      (S := (finiteGaloisFieldRangeOfEmbedding K L i).fixingSubgroup)
      (x := τ)
    refine Iff.trans ?_ (Iff.of_eq hmapmem.symm)
    refine Iff.trans ?_ hmem.symm
    simp [σ, mul_assoc]
  exact congrArg (fun H : Subgroup (G_p0 K) => H.carrier) hs

/-- The abstract base field is the top subgroup and hence is fixed by every
conjugation. -/
theorem finiteGaloisBase_conjugator
    (σ : G_p0 K) : conjugateClosedSubgroup (B_p0 K) σ = B_p0 K := by
  change conjugateClosedSubgroup
      (closedFixingSubgroup K (SeparableClosure K)
        (⊥ : IntermediateField K (SeparableClosure K))) σ =
    closedFixingSubgroup K (SeparableClosure K)
      (⊥ : IntermediateField K (SeparableClosure K))
  apply ClosedSubgroup.ext
  have hs :
      (conjugateClosedSubgroup
        (closedFixingSubgroup K (SeparableClosure K)
          (⊥ : IntermediateField K (SeparableClosure K))) σ).toSubgroup =
        (closedFixingSubgroup K (SeparableClosure K)
          (⊥ : IntermediateField K (SeparableClosure K))).toSubgroup := by
    ext τ
    have hc : τ ∈ (conjugateClosedSubgroup
          (closedFixingSubgroup K (SeparableClosure K)
            (⊥ : IntermediateField K (SeparableClosure K))) σ).toSubgroup ↔
        σ * τ * σ⁻¹ ∈
          (closedFixingSubgroup K (SeparableClosure K)
            (⊥ : IntermediateField K (SeparableClosure K))).toSubgroup :=
      conjugateClosedSubgroup_mem
        (closedFixingSubgroup K (SeparableClosure K)
          (⊥ : IntermediateField K (SeparableClosure K))) σ τ
    rw [hc]
    change σ * τ * σ⁻¹ ∈
        (⊥ : IntermediateField K (SeparableClosure K)).fixingSubgroup ↔
      τ ∈ (⊥ : IntermediateField K (SeparableClosure K)).fixingSubgroup
    rw [IntermediateField.fixingSubgroup_bot]
    simp
  exact congrArg (fun H : Subgroup (G_p0 K) => H.carrier) hs

/-- Raw quotient bridge for the explicit closed-fixing-subgroup presentation. -/
noncomputable instance finiteGaloisExtensionQuotientOfEmbedding_finite
    (i : L →ₐ[K] SeparableClosure K) :
    Finite ((B_p0 K).toSubgroup ⧸
      extensionSubgroup (B_p0 K)
        (finiteGaloisClosedFixingSubgroupOfEmbedding K L i)
        (fixingSubgroupLeBase K (SeparableClosure K)
          (finiteGaloisFieldRangeOfEmbedding K L i))) :=
  baseFixingExtensionQuotient_finite K (SeparableClosure K)
    (finiteGaloisFieldRangeOfEmbedding K L i)

/-! ## The two vertical maps of the abstract reciprocity naturality theorem -/

noncomputable def extensionQuotientCongr
    {Γ : Type} [Group Γ] [TopologicalSpace Γ]
    {K L K' L' : ClosedSubgroup Γ}
    (hLK : L.toSubgroup ≤ K.toSubgroup)
    (hL'K' : L'.toSubgroup ≤ K'.toSubgroup)
    [hN : (extensionSubgroup K L hLK).Normal]
    [hN' : (extensionSubgroup K' L' hL'K').Normal]
    (hK : K = K') (hL : L = L') :
    (K.toSubgroup ⧸ extensionSubgroup K L hLK) ≃*
      (K'.toSubgroup ⧸ extensionSubgroup K' L' hL'K') := by
  subst K'
  subst L'
  have hp : hLK = hL'K' := Subsingleton.elim _ _
  subst hL'K'
  exact MulEquiv.refl _

@[simp]
theorem extensionQuotientCongr_mk
    {Γ : Type} [Group Γ] [TopologicalSpace Γ]
    {K L K' L' : ClosedSubgroup Γ}
    (hLK : L.toSubgroup ≤ K.toSubgroup)
    (hL'K' : L'.toSubgroup ≤ K'.toSubgroup)
    [hN : (extensionSubgroup K L hLK).Normal]
    [hN' : (extensionSubgroup K' L' hL'K').Normal]
    (hK : K = K') (hL : L = L') (x : K.toSubgroup) :
    extensionQuotientCongr hLK hL'K' hK hL (QuotientGroup.mk x) =
      QuotientGroup.mk
        (MulEquiv.subgroupCongr
          (congrArg (fun H : ClosedSubgroup Γ => H.toSubgroup) hK) x) := by
  subst K'
  subst L'
  have hp : hLK = hL'K' := Subsingleton.elim _ _
  subst hL'K'
  have hn : hN = hN' := Subsingleton.elim _ _
  subst hN'
  rfl

noncomputable def finiteNormQuotientCongr
    {Γ : Type} [Group Γ] [TopologicalSpace Γ]
    (A : Rep ℤ Γ) {K L K' L' : ClosedSubgroup Γ}
    (hLK : L.toSubgroup ≤ K.toSubgroup)
    (hL'K' : L'.toSubgroup ≤ K'.toSubgroup)
    [hFinite : Finite (K.toSubgroup ⧸ extensionSubgroup K L hLK)]
    [hFinite' : Finite (K'.toSubgroup ⧸ extensionSubgroup K' L' hL'K')]
    (hK : K = K') (hL : L = L') :
    FiniteNormQuotient A K L hLK ≃+
      FiniteNormQuotient A K' L' hL'K' := by
  subst K'
  subst L'
  have hp : hLK = hL'K' := Subsingleton.elim _ _
  subst hL'K'
  exact AddEquiv.refl _

@[simp]
theorem finiteNormQuotientCongr_finiteNormClass
    {Γ : Type} [Group Γ] [TopologicalSpace Γ]
    (A : Rep ℤ Γ) {K L K' L' : ClosedSubgroup Γ}
    (hLK : L.toSubgroup ≤ K.toSubgroup)
    (hL'K' : L'.toSubgroup ≤ K'.toSubgroup)
    [hFinite : Finite (K.toSubgroup ⧸ extensionSubgroup K L hLK)]
    [hFinite' : Finite (K'.toSubgroup ⧸ extensionSubgroup K' L' hL'K')]
    (hK : K = K') (hL : L = L')
    (a : ambientFixedAddSubgroup A K) :
    finiteNormQuotientCongr A hLK hL'K' hK hL
        (finiteNormClass A K L hLK a) =
      finiteNormClass A K' L' hL'K'
        (AddEquiv.addSubgroupCongr
          (congrArg (ambientFixedAddSubgroup A) hK) a) := by
  subst K'
  subst L'
  have hp : hLK = hL'K' := Subsingleton.elim _ _
  subst hL'K'
  have hf : hFinite = hFinite' := Subsingleton.elim _ _
  subst hFinite'
  rfl

section EmbeddingConjugation

theorem finiteGaloisEmbeddingConjugate_normal
    (i : L →ₐ[K] SeparableClosure K) (s : G_p0 K) :
    (extensionSubgroup (conjugateClosedSubgroup (B_p0 K) s)
      (conjugateClosedSubgroup
        (finiteGaloisClosedFixingSubgroupOfEmbedding K L i) s)
      (conjugateClosedSubgroup_mono
        (fixingSubgroupLeBase K (SeparableClosure K)
          (finiteGaloisFieldRangeOfEmbedding K L i)) s)).Normal :=
  conjugateExtension_normal (B_p0 K)
    (finiteGaloisClosedFixingSubgroupOfEmbedding K L i)
    (fixingSubgroupLeBase K (SeparableClosure K)
      (finiteGaloisFieldRangeOfEmbedding K L i)) s
    (hLnormal := (finiteGaloisAbstractExtensionOfEmbedding K L i).normal)

attribute [local instance] finiteGaloisEmbeddingConjugate_normal

/-- Conjugation between the two concrete presentations of the abstract extension quotient. -/
def finiteGaloisConjugationOfEmbeddings
    (i j : L →ₐ[K] SeparableClosure K) :
    (finiteGaloisAbstractExtensionOfEmbedding K L i).extensionQuotient ≃*
      (finiteGaloisAbstractExtensionOfEmbedding K L j).extensionQuotient := by
  let hLK : (finiteGaloisClosedFixingSubgroupOfEmbedding K L i).toSubgroup ≤
      (B_p0 K).toSubgroup :=
    fixingSubgroupLeBase K (SeparableClosure K)
      (finiteGaloisFieldRangeOfEmbedding K L i)
  let s := (finiteGaloisEmbeddingConjugator K L i j)⁻¹
  have hB := finiteGaloisBase_conjugator K
    (finiteGaloisEmbeddingConjugator K L i j)⁻¹
  have hH := finiteGaloisClosedFixingSubgroup_conjugator K L i j
  let e := finiteReciprocityNaturalityConjugation (B_p0 K)
      (finiteGaloisClosedFixingSubgroupOfEmbedding K L i)
      hLK s
  let c := extensionQuotientCongr
    (conjugateClosedSubgroup_mono hLK s)
    (fixingSubgroupLeBase K (SeparableClosure K)
      (finiteGaloisFieldRangeOfEmbedding K L j)) hB hH
  exact
    ((finiteGaloisAbstractExtensionOfEmbedding K L i).extensionQuotientMulEquiv.trans
      (e.trans c)).trans
        (finiteGaloisAbstractExtensionOfEmbedding K L j).extensionQuotientMulEquiv.symm

/-- Conjugation between embedding models sends a quotient representative to its conjugate class. -/
@[simp]
theorem finiteGaloisConjugationOfEmbeddings_mk
    (i j : L →ₐ[K] SeparableClosure K) (τ : (B_p0 K).toSubgroup) :
    finiteGaloisConjugationOfEmbeddings K L i j (QuotientGroup.mk τ) =
      QuotientGroup.mk (finiteGaloisConjugateBaseElement K L i j τ) := by
  let hLK := fixingSubgroupLeBase K (SeparableClosure K)
    (finiteGaloisFieldRangeOfEmbedding K L i)
  change (finiteGaloisClosedFixingSubgroupOfEmbedding K L i).toSubgroup ≤
      (B_p0 K).toSubgroup at hLK
  let hLjK := fixingSubgroupLeBase K (SeparableClosure K)
    (finiteGaloisFieldRangeOfEmbedding K L j)
  change (finiteGaloisClosedFixingSubgroupOfEmbedding K L j).toSubgroup ≤
      (B_p0 K).toSubgroup at hLjK
  let s := (finiteGaloisEmbeddingConjugator K L i j)⁻¹
  have hB := finiteGaloisBase_conjugator K s
  have hH : conjugateClosedSubgroup
      (finiteGaloisClosedFixingSubgroupOfEmbedding K L i) s =
      finiteGaloisClosedFixingSubgroupOfEmbedding K L j :=
    finiteGaloisClosedFixingSubgroup_conjugator K L i j
  change extensionQuotientCongr
      (conjugateClosedSubgroup_mono hLK s)
      hLjK hB hH
      (finiteReciprocityNaturalityConjugation (B_p0 K)
        (finiteGaloisClosedFixingSubgroupOfEmbedding K L i) hLK s
        (QuotientGroup.mk τ)) = _
  rw [finiteReciprocityNaturalityConjugation_mk, extensionQuotientCongr_mk]
  apply congrArg QuotientGroup.mk
  apply Subtype.ext
  simp [finiteGaloisConjugateBaseElement,
    conjugateSubgroupEquiv_apply_coe, s, mul_assoc]

section EmbeddingNormConjugation

@[instance_reducible]
def finiteGaloisEmbeddingNormAddZeroClass
    (i : L →ₐ[K] SeparableClosure K) :=
  letI : Finite ((B_p0 K).toSubgroup ⧸
      extensionSubgroup (B_p0 K)
        (finiteGaloisClosedFixingSubgroupOfEmbedding K L i)
        (fixingSubgroupLeBase K (SeparableClosure K)
          (finiteGaloisFieldRangeOfEmbedding K L i))) :=
    finiteGaloisExtensionQuotientOfEmbedding_finite K L i
  show AddZeroClass (FiniteNormQuotient (AG K) (B_p0 K)
    (finiteGaloisClosedFixingSubgroupOfEmbedding K L i)
    (fixingSubgroupLeBase K (SeparableClosure K)
      (finiteGaloisFieldRangeOfEmbedding K L i))) from
    (finiteNormQuotientAddCommGroup (AG K) (B_p0 K)
      (finiteGaloisClosedFixingSubgroupOfEmbedding K L i)
      (fixingSubgroupLeBase K (SeparableClosure K)
        (finiteGaloisFieldRangeOfEmbedding K L i))).toAddZeroClass

attribute [local instance] finiteGaloisEmbeddingNormAddZeroClass

end EmbeddingNormConjugation

/-! ## Concrete comparison on representatives -/

theorem baseFixingExtensionQuotientEquivGaloisGroup_mk_apply
    (K Ω : Type) [Field K] [Field Ω] [Algebra K Ω] [IsGalois K Ω]
    (E : IntermediateField K Ω) [FiniteDimensional K E] [IsGalois K E]
    (τ : (closedFixingSubgroup K Ω
      (⊥ : IntermediateField K Ω)).toSubgroup) (x : E) :
    E.val ((baseFixingExtensionQuotientEquivGaloisGroup K Ω E
      (QuotientGroup.mk τ)) x) = τ.1 (E.val x) := by
  have hq :
      baseFixingExtensionQuotientEquivAmbient K Ω E
          (QuotientGroup.mk τ) =
        QuotientGroup.mk' (closedFixingSubgroup K Ω E).toSubgroup τ.1 := by
    rfl
  have hn := InfiniteGalois.normalAutEquivQuotient_apply
    (closedFixingSubgroup K Ω E) τ.1
  change InfiniteGalois.normalAutEquivQuotient (closedFixingSubgroup K Ω E)
      (QuotientGroup.mk' _ τ.1) = _ at hn
  rw [baseFixingExtensionQuotientEquivGaloisGroup, MulEquiv.trans_apply, hq,
    MulEquiv.trans_apply, hn, AlgEquiv.autCongr_apply]
  simp only [AlgEquiv.trans_apply, IntermediateField.equivOfEq_symm,
    IntermediateField.equivOfEq_apply]
  change
    (((AlgEquiv.restrictNormalHom
      (IntermediateField.fixedField
        (closedFixingSubgroup K Ω E).toSubgroup) τ.1)
      ⟨E.val x, _⟩ : IntermediateField.fixedField
        (closedFixingSubgroup K Ω E).toSubgroup) : Ω) =
      τ.1 (E.val x)
  calc
    (((AlgEquiv.restrictNormalHom
      (IntermediateField.fixedField
        (closedFixingSubgroup K Ω E).toSubgroup) τ.1)
      ⟨E.val x, _⟩ : IntermediateField.fixedField
        (closedFixingSubgroup K Ω E).toSubgroup) : Ω) =
        τ.1 (E.val x) := by
      rw [AlgEquiv.restrictNormalHom_apply]

/-- Formula for the quotient equivalence on a representative, expressed
without mentioning the auxiliary fixed-field equality used internally. -/
@[simp]
theorem finiteGaloisAbstractQuotientEquivGaloisGroupOfEmbedding_mk_apply
    (i : L →ₐ[K] SeparableClosure K) (τ : (B_p0 K).toSubgroup) (x : L) :
    i ((finiteGaloisAbstractQuotientEquivGaloisGroupOfEmbedding K L i
      (QuotientGroup.mk τ)) x) = τ.1 (i x) := by
  let E := finiteGaloisFieldRangeOfEmbedding K L i
  let e := finiteGaloisFieldRangeEquivOfEmbedding K L i
  let g := baseFixingExtensionQuotientEquivGaloisGroup
    K (SeparableClosure K) E (QuotientGroup.mk τ)
  have hb := baseFixingExtensionQuotientEquivGaloisGroup_mk_apply
    K (SeparableClosure K) E τ (e x)
  have he (y : E) : i (e.symm y) = E.val y := by
    exact congrArg Subtype.val (e.apply_symm_apply y)
  change i (((e.autCongr).symm g) x) = τ.1 (i x)
  calc
    i (((e.autCongr).symm g) x) = E.val (g (e x)) := by
      simpa only [AlgEquiv.autCongr_symm, AlgEquiv.autCongr_apply,
        AlgEquiv.trans_apply, AlgEquiv.symm_symm] using he (g (e x))
    _ = τ.1 (E.val (e x)) := hb
    _ = τ.1 (i x) := rfl

/-- The explicit norm-quotient comparison sends a base-unit representative
to the same representative in the ordinary field norm quotient. -/
@[simp]
theorem finiteNormQuotientEquivEmbeddedNormQuotient_finiteNormClass_baseUnit
    (i : L →ₐ[K] SeparableClosure K) (x : Kˣ) :
    finiteNormQuotientEquivEmbeddedNormQuotient
        K (SeparableClosure K) L i
        (finiteNormClass (AG K) (B_p0 K)
          (finiteGaloisClosedFixingSubgroupOfEmbedding K L i)
          (fixingSubgroupLeBase K (SeparableClosure K)
            (finiteGaloisFieldRangeOfEmbedding K L i))
          (baseUnitsEquivGaloisAmbientFixed K (SeparableClosure K)
            (Additive.ofMul x))) =
      (MonoidHom.toAdditive (normClass K L))
        (Additive.ofMul x) := by
  calc
    finiteNormQuotientEquivEmbeddedNormQuotient
        K (SeparableClosure K) L i
        (finiteNormClass (AG K) (B_p0 K)
          (finiteGaloisClosedFixingSubgroupOfEmbedding K L i)
          (fixingSubgroupLeBase K (SeparableClosure K)
            (finiteGaloisFieldRangeOfEmbedding K L i))
          (baseUnitsEquivGaloisAmbientFixed K (SeparableClosure K)
            (Additive.ofMul x))) =
      (MulEquiv.toAdditive
        (normQuotientEquivOfNormSubgroupEq K (AlgHom.fieldRange i) L
          (localNormSubgroup_fieldRange_eq K (SeparableClosure K) L i)))
        ((MonoidHom.toAdditive (normClass K (AlgHom.fieldRange i)))
          (Additive.ofMul x)) := by
      simp [AG, B_p0, finiteGaloisClosedFixingSubgroupOfEmbedding,
        finiteGaloisFieldRangeOfEmbedding]
    _ = (MonoidHom.toAdditive (normClass K L)) (Additive.ofMul x) := by
      change Additive.ofMul
          ((normQuotientEquivOfNormSubgroupEq K (AlgHom.fieldRange i) L
            (localNormSubgroup_fieldRange_eq K (SeparableClosure K) L i))
              (normClass K (AlgHom.fieldRange i) x)) =
        Additive.ofMul (normClass K L x)
      exact congrArg Additive.ofMul
        (normQuotientEquivOfNormSubgroupEq_normClass K (AlgHom.fieldRange i) L
          (localNormSubgroup_fieldRange_eq K (SeparableClosure K) L i) x)

/-! ## The two outer comparison squares -/

/-! ## The abstract reciprocity naturality theorem and embedding independence -/

end EmbeddingConjugation

end
end LocalClassFieldTheory
end

section
-- module Solutions.OAIQ244_DUKE.LocalClassFieldTheory_Finite_LocalReciprocity_Main
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 400000
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalClassFieldTheory.finiteGaloisLocalField_integerRing_moduleFinite _root_.LocalClassFieldTheory.realComplexNormQuotientFinite _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.CyclicCohomology.binaryCoefficientFamilyCommGroup _root_.LocalClassFieldTheory.comparisonIntegerRingIsIntegralClosure _root_.LocalClassFieldTheory.normalizationIntegerRingIsIntegralClosure _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen _root_.infiniteAdeleRingT2Space _root_.relativeUnrestrictedSPlaceFactorCommGroup
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

namespace LocalClassFieldTheory

open LocalFieldTheory

/-!
# Finite local reciprocity: the local reciprocity law

The residue Frobenius datum, the normalized henselian valuation, and the
class-field axiom constructed over the fixed separable closure are inserted
into the abstract reciprocity theorem.  The resulting isomorphism is independent of the
embedding used to realize the finite Galois extension in that closure.
-/

noncomputable section

variable (K L : Type) [Field K] [Field L] [Algebra K L]
  [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [FiniteDimensional K L] [IsGalois K L]

/-- **Finite local reciprocity (Local Reciprocity Law).**  For every finite Galois
extension of nonarchimedean local fields, reciprocity gives the canonical
isomorphism
`G(L/K)ᵃᵇ ≃ Kˣ / N_{L/K}(Lˣ)`.

The coefficient module used in the construction is
`(SeparableClosure K)ˣ`, in the fixed-separable-closure model. -/
noncomputable def abelianizationEquivNormQuotient :
    Abelianization (Gal(L / K)) ≃* NormQuotient K L :=
  concreteReciprocityEquiv K L
    (localResidueDatum K)
    (localHenselianValuation K)
    (separableClosureUnits_isClassFormation K)

end
end LocalClassFieldTheory
end

section
-- module Solutions.OAIQ244_DUKE.AlgebraicNumberTheory_Idele_ClassGroup_NormComparison
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.GlobalClassFields.ConductorialSubgroup.finiteIndex _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.KummerTheory.primeCyclotomicBaseFiniteDimensional _root_.LocalClassFieldTheory.finiteGaloisLocalField_integerRing_moduleFinite _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.residueFieldZModAlgebra _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedIntegralAlgebraContextValuationSubringAlgebra _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.CyclicCohomology.binaryCoefficientFamilyCommGroup _root_.LocalClassFieldTheory.comparisonIntegerRingIsIntegralClosure _root_.LocalClassFieldTheory.normalizationIntegerRingIsIntegralClosure _root_.chosenFinitePlaceCompletionAlgebra _root_.chosenFinitePlaceCompletionFiniteDimensional _root_.chosenFinitePlaceLocalizedFiniteDimensional _root_.relativeUnrestrictedSPlaceFactorCommGroup
attribute [-simp] _root_.IdeleGroup.finitePlaceIdele_finiteComponent_of_ne _root_.IdeleGroup.finitePlaceIdele_finiteComponent_same _root_.IdeleGroup.finitePlaceIdele_infiniteComponent _root_.IdeleGroup.infinitePlaceIdeleContinuous_apply _root_.IdeleGroup.infinitePlaceIdele_finiteComponent _root_.IdeleGroup.infinitePlaceIdele_infiniteComponent_of_ne _root_.IdeleGroup.infinitePlaceIdele_infiniteComponent_same _root_.IsDiscreteValuationRing.addVal_ringEquiv _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.OAI.PrimeDegreePackets.ThetaConstruction.schwartzCM_apply _root_.RayClass.primesEquiv_val_eq_natGenerator _root_.RayClass.signToNarrow_mk _root_.RelativeIdeleGroup.relativeFinitePlaceIdele_finiteComponent_of_ne _root_.RelativeIdeleGroup.relativeFinitePlaceIdele_finiteComponent_same _root_.RelativeIdeleGroup.relativeFinitePlaceIdele_infiniteComponent _root_.RelativeIdeleGroup.relativeInfinitePlaceIdele_finiteComponent _root_.RelativeIdeleGroup.relativeInfinitePlaceIdele_infiniteComponent_of_ne _root_.RelativeIdeleGroup.relativeInfinitePlaceIdele_infiniteComponent_same _root_.relativeAdeleMapOfCompatibleEquiv_tmul _root_.finiteIdeleOfSPlaceFactors_apply_mem _root_.finiteIdeleOfSPlaceFactors_apply_notMem _root_.ideleClassCongr_mk _root_.ideleCongr_finiteComponent _root_.ideleCongr_principalIdele _root_.ideleSupportedAtEquivSPlaceFactors_infinite _root_.ideleSupportedAtEquivSPlaceFactors_inside _root_.ideleSupportedAtEquivSPlaceFactors_outside_coe _root_.relativeAdeleCongr_tmul _root_.relativeIdeleClassCongr_ideleClassNorm _root_.relativeIdeleClassCongr_mk _root_.relativeIdeleCongr_coe _root_.relativeIdeleCongr_norm _root_.relativeIdeleCongr_principalIdele _root_.towerActualRelativeAdeleRingEquiv_tmul _root_.towerRelativeIdeleBaseChangeMulEquiv_principalIdele _root_.towerRelativeIdeleClassBaseChangeMulEquiv_mk _root_.towerRelativeIdeleViaOrdinaryMulEquiv_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

/-!
# Relative and ordinary idele-class norms

The determinant norm on relative ideles and the ordinary idele norm give
the same map after the canonical scalar-extension equivalence
`C(𝔸_K ⊗_K L) ≃ C_L`.  This comparison lets the cohomological results
proved in relative coordinates be stated with the usual norm
`N_{L/K} : C_L → C_K`.
-/

open scoped NumberField
open NumberField

noncomputable section

variable
    {K L : Type*}
    [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    [IsGalois K L]

omit [IsGalois K L] in
/-- The ordinary and relative presentations define the same norm subgroup
of `C_K`. -/
theorem ordinaryIdeleClassNorm_range_eq_relative :
    (_root_.ideleClassNorm K L).range =
      (RelativeIdeleGroup.classNorm K L).range := by
  ext c
  constructor
  · rintro ⟨d, rfl⟩
    refine
      ⟨(relativeIdeleClassBaseChangeMulEquiv
          (K := K) (L := L)).symm d, ?_⟩
    simpa using
      (ordinaryIdeleClassNorm_relativeIdeleClassBaseChange
        (K := K) (L := L)
        ((relativeIdeleClassBaseChangeMulEquiv
          (K := K) (L := L)).symm d)).symm
  · rintro ⟨d, rfl⟩
    exact
      ⟨relativeIdeleClassBaseChangeMulEquiv
          (K := K) (L := L) d,
        ordinaryIdeleClassNorm_relativeIdeleClassBaseChange
          (K := K) (L := L) d⟩
end
end

section
-- module Solutions.OAIQ244_DUKE.AlgebraicNumberTheory_Idele_ClassGroup_AlgEquiv
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.GlobalClassFields.ConductorialSubgroup.finiteIndex _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.KummerTheory.primeCyclotomicBaseFiniteDimensional _root_.LocalClassFieldTheory.finiteGaloisLocalField_integerRing_moduleFinite _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.residueFieldZModAlgebra _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedIntegralAlgebraContextValuationSubringAlgebra _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedQPadicContextValuationSubringTower _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.CyclicCohomology.binaryCoefficientFamilyCommGroup _root_.LocalClassFieldTheory.comparisonIntegerRingIsIntegralClosure _root_.LocalClassFieldTheory.normalizationIntegerRingIsIntegralClosure _root_.chosenFinitePlaceCompletionAlgebra _root_.chosenFinitePlaceCompletionFiniteDimensional _root_.chosenFinitePlaceLocalizedFiniteDimensional _root_.relativeUnrestrictedSPlaceFactorCommGroup
attribute [-simp] _root_.IdeleGroup.finitePlaceIdele_finiteComponent_of_ne _root_.IdeleGroup.finitePlaceIdele_finiteComponent_same _root_.IdeleGroup.finitePlaceIdele_infiniteComponent _root_.IdeleGroup.infinitePlaceIdeleContinuous_apply _root_.IdeleGroup.infinitePlaceIdele_finiteComponent _root_.IdeleGroup.infinitePlaceIdele_infiniteComponent_of_ne _root_.IdeleGroup.infinitePlaceIdele_infiniteComponent_same _root_.IsDiscreteValuationRing.addVal_ringEquiv _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.OAI.PrimeDegreePackets.ThetaConstruction.schwartzCM_apply _root_.RayClass.primesEquiv_val_eq_natGenerator _root_.RayClass.signToNarrow_mk _root_.RelativeIdeleGroup.relativeFinitePlaceIdele_finiteComponent_of_ne _root_.RelativeIdeleGroup.relativeFinitePlaceIdele_finiteComponent_same _root_.RelativeIdeleGroup.relativeFinitePlaceIdele_infiniteComponent _root_.RelativeIdeleGroup.relativeInfinitePlaceIdele_finiteComponent _root_.RelativeIdeleGroup.relativeInfinitePlaceIdele_infiniteComponent_of_ne _root_.RelativeIdeleGroup.relativeInfinitePlaceIdele_infiniteComponent_same _root_.finiteIdeleOfSPlaceFactors_apply_mem _root_.finiteIdeleOfSPlaceFactors_apply_notMem _root_.ideleSupportedAtEquivSPlaceFactors_infinite _root_.ideleSupportedAtEquivSPlaceFactors_inside _root_.ideleSupportedAtEquivSPlaceFactors_outside_coe _root_.towerActualRelativeAdeleRingEquiv_tmul _root_.towerRelativeIdeleBaseChangeMulEquiv_principalIdele _root_.towerRelativeIdeleClassBaseChangeMulEquiv_mk _root_.towerRelativeIdeleViaOrdinaryMulEquiv_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI
attribute [local instance] OAI.starSubalgebraCommCStarAlgebra

set_option autoImplicit false

/-!
# Relative idele classes under an isomorphic realization

If two finite extensions of a number field are isomorphic over the base,
their tensor-product presentations of the relative adeles are canonically
isomorphic.  This file descends that canonical isomorphism to relative
ideles and idele classes and records compatibility with the determinant
norm.

The construction is the direct tensor-product congruence

`𝔸_K ⊗[K] L ≃ 𝔸_K ⊗[K] M`

induced by an algebra equivalence `L ≃ₐ[K] M`.  In particular, no second
model of relative adeles or of the idele-class norm is introduced.
-/

open scoped NumberField TensorProduct
open NumberField
open IsDedekindDomain

noncomputable section

open RelativeIdeleGroup.Cohomology


universe u v w

variable
    {K : Type u} {L : Type v} {M : Type w}
    [Field K] [NumberField K]
    [Field L] [Algebra K L]
    [Field M] [Algebra K M]

section Absolute

variable
    {K : Type u} {M : Type w}
    [Field K] [NumberField K] [Algebra ℚ K]
    [Field M] [NumberField M] [Algebra ℚ M]

section RelativeTowerCongr

variable
    {K L K' L' : Type}
    [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    [Field K'] [NumberField K']
    [Field L'] [NumberField L'] [Algebra K' L']

/-- Compatible equivalences of number-field extensions induce the
canonical equivalence of their relative adele rings. -/
noncomputable def relativeAdeleCongrOfAlgEquiv
    (eK : K ≃ₐ[ℚ] K')
    (eL : L ≃ₐ[ℚ] L')
    (h : ∀ x : K,
      eL (algebraMap K L x) =
        algebraMap K' L' (eK x)) :
    RelativeAdeleRing K L ≃+*
      RelativeAdeleRing K' L' := by
  let eA := adeleCongr eK
  have hA : ∀ x : K,
      eA
          (algebraMap K
            (NumberField.AdeleRing (𝓞 K) K) x) =
        algebraMap K'
          (NumberField.AdeleRing (𝓞 K') K') (eK x) :=
    adeleCongr_algebraMap eK
  have hA' : ∀ x : K',
      eA.symm
          (algebraMap K'
            (NumberField.AdeleRing (𝓞 K') K') x) =
        algebraMap K
          (NumberField.AdeleRing (𝓞 K) K)
          (eK.symm x) := by
    intro x
    apply eA.injective
    calc
      eA
          (eA.symm
            (algebraMap K'
              (NumberField.AdeleRing (𝓞 K') K') x)) =
          algebraMap K'
            (NumberField.AdeleRing (𝓞 K') K') x :=
        eA.apply_symm_apply _
      _ =
          algebraMap K'
            (NumberField.AdeleRing (𝓞 K') K')
            (eK (eK.symm x)) := by
        rw [eK.apply_symm_apply]
      _ =
          eA
            (algebraMap K
              (NumberField.AdeleRing (𝓞 K) K)
              (eK.symm x)) :=
        (hA (eK.symm x)).symm
  have h' : ∀ x : K',
      eL.symm (algebraMap K' L' x) =
        algebraMap K L (eK.symm x) := by
    intro x
    apply eL.injective
    calc
      eL (eL.symm (algebraMap K' L' x)) =
          algebraMap K' L' x :=
        eL.apply_symm_apply _
      _ = algebraMap K' L' (eK (eK.symm x)) := by
        rw [eK.apply_symm_apply]
      _ = eL (algebraMap K L (eK.symm x)) :=
        (h (eK.symm x)).symm
  let f :=
    relativeAdeleMapOfCompatibleEquiv
      eK eA hA eL h
  let g :=
    relativeAdeleMapOfCompatibleEquiv
      eK.symm eA.symm hA' eL.symm h'
  exact
    { f with
      invFun := g
      left_inv := by
        intro z
        induction z using OAI.tensorInductionOn with
        | add x y hx hy =>
            calc
              g (f (x + y)) =
                  g (f x + f y) :=
                congrArg g (map_add f x y)
              _ = g (f x) + g (f y) :=
                map_add g (f x) (f y)
              _ = x + y :=
                congrArg₂ (· + ·) hx hy
        | tmul a x =>
            calc
              g (f (a ⊗ₜ[K] x)) =
                  g (eA a ⊗ₜ[K'] eL x) :=
                congrArg g
                  (relativeAdeleMapOfCompatibleEquiv_tmul
                    eK eA hA eL h a x)
              _ = eA.symm (eA a) ⊗ₜ[K] eL.symm (eL x) :=
                relativeAdeleMapOfCompatibleEquiv_tmul
                  eK.symm eA.symm hA' eL.symm h'
                  (eA a) (eL x)
              _ = a ⊗ₜ[K] x := by simp
      right_inv := by
        intro z
        induction z using OAI.tensorInductionOn with
        | add x y hx hy =>
            calc
              f (g (x + y)) =
                  f (g x + g y) :=
                congrArg f (map_add g x y)
              _ = f (g x) + f (g y) :=
                map_add f (g x) (g y)
              _ = x + y :=
                congrArg₂ (· + ·) hx hy
        | tmul a x =>
            calc
              f (g (a ⊗ₜ[K'] x)) =
                  f (eA.symm a ⊗ₜ[K] eL.symm x) :=
                congrArg f
                  (relativeAdeleMapOfCompatibleEquiv_tmul
                    eK.symm eA.symm hA' eL.symm h' a x)
              _ = eA (eA.symm a) ⊗ₜ[K'] eL (eL.symm x) :=
                relativeAdeleMapOfCompatibleEquiv_tmul
                  eK eA hA eL h (eA.symm a) (eL.symm x)
              _ = a ⊗ₜ[K'] x := by simp }

@[simp]
theorem relativeAdeleCongrOfAlgEquiv_tmul
    (eK : K ≃ₐ[ℚ] K')
    (eL : L ≃ₐ[ℚ] L')
    (h : ∀ x : K,
      eL (algebraMap K L x) =
        algebraMap K' L' (eK x))
    (a : NumberField.AdeleRing (𝓞 K) K)
    (x : L) :
    relativeAdeleCongrOfAlgEquiv eK eL h
        (a ⊗ₜ[K] x) =
      adeleCongr eK a ⊗ₜ[K'] eL x :=
  relativeAdeleMapOfCompatibleEquiv_tmul
    eK (adeleCongr eK)
    (adeleCongr_algebraMap eK) eL h a x

/-- Compatible equivalences of number-field extensions induce the
canonical equivalence of their relative idele groups. -/
noncomputable def relativeIdeleCongrOfAlgEquiv
    (eK : K ≃ₐ[ℚ] K')
    (eL : L ≃ₐ[ℚ] L')
    (h : ∀ x : K,
      eL (algebraMap K L x) =
        algebraMap K' L' (eK x)) :
    RelativeIdeleGroup K L ≃*
      RelativeIdeleGroup K' L' :=
  Units.mapEquiv
    (relativeAdeleCongrOfAlgEquiv eK eL h).toMulEquiv

@[simp]
theorem relativeIdeleCongrOfAlgEquiv_principalIdele
    (eK : K ≃ₐ[ℚ] K')
    (eL : L ≃ₐ[ℚ] L')
    (h : ∀ x : K,
      eL (algebraMap K L x) =
        algebraMap K' L' (eK x))
    (x : Lˣ) :
    relativeIdeleCongrOfAlgEquiv eK eL h
        (RelativeIdeleGroup.principalIdele K L x) =
      RelativeIdeleGroup.principalIdele K' L'
        (Units.mapEquiv eL.toMulEquiv x) := by
  apply Units.ext
  change
    relativeAdeleCongrOfAlgEquiv eK eL h
        ((1 : NumberField.AdeleRing (𝓞 K) K) ⊗ₜ[K] (x : L)) =
      (1 : NumberField.AdeleRing (𝓞 K') K') ⊗ₜ[K'] eL (x : L)
  rw [relativeAdeleCongrOfAlgEquiv_tmul]
  simp

/-- The semilinear relative-idele transport identifies the principal
subgroups. -/
theorem relativeIdelePrincipalSubgroup_map_congrOfAlgEquiv
    (eK : K ≃ₐ[ℚ] K')
    (eL : L ≃ₐ[ℚ] L')
    (h : ∀ x : K,
      eL (algebraMap K L x) =
        algebraMap K' L' (eK x)) :
    (RelativeIdeleGroup.principalSubgroup K L).map
        (relativeIdeleCongrOfAlgEquiv eK eL h) =
      RelativeIdeleGroup.principalSubgroup K' L' := by
  ext y
  constructor
  · rintro ⟨z, ⟨x, hx⟩, rfl⟩
    rw [← hx]
    exact
      ⟨Units.mapEquiv eL.toMulEquiv x,
        (relativeIdeleCongrOfAlgEquiv_principalIdele
          eK eL h x).symm⟩
  · rintro ⟨y, rfl⟩
    obtain ⟨x, rfl⟩ :=
      (Units.mapEquiv eL.toMulEquiv).surjective y
    exact
      ⟨RelativeIdeleGroup.principalIdele K L x,
        ⟨x, rfl⟩,
        relativeIdeleCongrOfAlgEquiv_principalIdele
          eK eL h x⟩

/-- Compatible equivalences of number-field extensions induce the
canonical equivalence of their existing relative idele class groups. -/
noncomputable def relativeIdeleClassCongrOfAlgEquiv
    (eK : K ≃ₐ[ℚ] K')
    (eL : L ≃ₐ[ℚ] L')
    (h : ∀ x : K,
      eL (algebraMap K L x) =
        algebraMap K' L' (eK x)) :
    RelativeIdeleGroup.ClassGroup K L ≃*
      RelativeIdeleGroup.ClassGroup K' L' :=
  QuotientGroup.congr
    (RelativeIdeleGroup.principalSubgroup K L)
    (RelativeIdeleGroup.principalSubgroup K' L')
    (relativeIdeleCongrOfAlgEquiv eK eL h)
    (relativeIdelePrincipalSubgroup_map_congrOfAlgEquiv
      eK eL h)

@[simp]
theorem relativeIdeleClassCongrOfAlgEquiv_mk
    (eK : K ≃ₐ[ℚ] K')
    (eL : L ≃ₐ[ℚ] L')
    (h : ∀ x : K,
      eL (algebraMap K L x) =
        algebraMap K' L' (eK x))
    (a : RelativeIdeleGroup K L) :
    relativeIdeleClassCongrOfAlgEquiv eK eL h
        (QuotientGroup.mk'
          (RelativeIdeleGroup.principalSubgroup K L) a) =
      QuotientGroup.mk'
        (RelativeIdeleGroup.principalSubgroup K' L')
        (relativeIdeleCongrOfAlgEquiv eK eL h a) :=
  rfl

section Norm

variable
    [FiniteDimensional K L]
    [FiniteDimensional K' L']

omit [FiniteDimensional K L] [FiniteDimensional K' L'] in
/-- Determinant norms on relative adele rings commute with compatible
equivalences of both fields in the extension. -/
theorem relativeAdeleCongrOfAlgEquiv_norm
    (eK : K ≃ₐ[ℚ] K')
    (eL : L ≃ₐ[ℚ] L')
    (h : ∀ x : K,
      eL (algebraMap K L x) =
        algebraMap K' L' (eK x))
    (z : RelativeAdeleRing K L) :
    adeleCongr eK
        (Algebra.norm
          (NumberField.AdeleRing (𝓞 K) K) z) =
      Algebra.norm
        (NumberField.AdeleRing (𝓞 K') K')
        (relativeAdeleCongrOfAlgEquiv eK eL h z) := by
  have hcompat :
      (algebraMap
          (NumberField.AdeleRing (𝓞 K') K')
          (RelativeAdeleRing K' L')).comp
          (adeleCongr eK).toRingHom =
        (relativeAdeleCongrOfAlgEquiv eK eL h).toRingHom.comp
          (algebraMap
            (NumberField.AdeleRing (𝓞 K) K)
            (RelativeAdeleRing K L)) := by
    ext a
    change
      (adeleCongr eK a) ⊗ₜ[K'] (1 : L') =
        relativeAdeleCongrOfAlgEquiv eK eL h
          (a ⊗ₜ[K] (1 : L))
    rw [relativeAdeleCongrOfAlgEquiv_tmul]
    simp
  have hnorm :=
    Algebra.norm_eq_of_equiv_equiv
      (adeleCongr eK)
      (relativeAdeleCongrOfAlgEquiv eK eL h)
      hcompat z
  simpa using congrArg (adeleCongr eK) hnorm

omit [FiniteDimensional K L] [FiniteDimensional K' L'] in
/-- The relative idele norm commutes with compatible equivalences of
number-field extensions. -/
theorem relativeIdeleCongrOfAlgEquiv_norm
    (eK : K ≃ₐ[ℚ] K')
    (eL : L ≃ₐ[ℚ] L')
    (h : ∀ x : K,
      eL (algebraMap K L x) =
        algebraMap K' L' (eK x))
    (a : RelativeIdeleGroup K L) :
    ideleCongr eK (RelativeIdeleGroup.norm K L a) =
      RelativeIdeleGroup.norm K' L'
        (relativeIdeleCongrOfAlgEquiv eK eL h a) := by
  apply
    (IdeleGroup.equivAdeleRingUnits
      (K := K')).injective
  apply Units.ext
  exact
    relativeAdeleCongrOfAlgEquiv_norm
      eK eL h (a : RelativeAdeleRing K L)

variable [IsGalois K L] [IsGalois K' L']

omit [IsGalois K L] [IsGalois K' L'] in
/-- The descended relative idele-class norm commutes with compatible
equivalences of number-field extensions. -/
@[simp]
theorem relativeIdeleClassCongrOfAlgEquiv_ideleClassNorm
    (eK : K ≃ₐ[ℚ] K')
    (eL : L ≃ₐ[ℚ] L')
    (h : ∀ x : K,
      eL (algebraMap K L x) =
        algebraMap K' L' (eK x))
    (c : RelativeIdeleGroup.ClassGroup K L) :
    ideleClassCongr eK
        (RelativeIdeleGroup.classNorm K L c) =
      RelativeIdeleGroup.classNorm K' L'
        (relativeIdeleClassCongrOfAlgEquiv
          eK eL h c) := by
  refine QuotientGroup.induction_on c ?_
  intro a
  exact congrArg
    (QuotientGroup.mk'
      (IdeleGroup.principalSubgroup K'))
    (relativeIdeleCongrOfAlgEquiv_norm eK eL h a)

omit [IsGalois K L] [IsGalois K' L'] in
/-- Under compatible equivalences of number-field extensions, the
relative class-norm subgroup is carried exactly to the relative
class-norm subgroup of the transported extension. -/
theorem relativeIdeleClassNorm_range_map_congrOfAlgEquiv
    (eK : K ≃ₐ[ℚ] K')
    (eL : L ≃ₐ[ℚ] L')
    (h : ∀ x : K,
      eL (algebraMap K L x) =
        algebraMap K' L' (eK x)) :
    (RelativeIdeleGroup.classNorm K L).range.map
        (ideleClassCongr eK).toMonoidHom =
      (RelativeIdeleGroup.classNorm K' L').range := by
  ext c
  constructor
  · rintro ⟨_, ⟨d, rfl⟩, rfl⟩
    exact
      ⟨relativeIdeleClassCongrOfAlgEquiv
          eK eL h d,
        (relativeIdeleClassCongrOfAlgEquiv_ideleClassNorm
          eK eL h d).symm⟩
  · rintro ⟨d, rfl⟩
    let c :=
      (relativeIdeleClassCongrOfAlgEquiv
        eK eL h).symm d
    refine
      ⟨RelativeIdeleGroup.classNorm K L c,
        ⟨c, rfl⟩, ?_⟩
    simpa [c] using
      (relativeIdeleClassCongrOfAlgEquiv_ideleClassNorm
        eK eL h c)

omit [FiniteDimensional K L] [FiniteDimensional K' L']
  [IsGalois K L] [IsGalois K' L'] in
/-- Under compatible equivalences of finite Galois number-field
extensions, the ordinary class-norm subgroup is carried exactly to the
ordinary class-norm subgroup of the transported extension. -/
theorem ordinaryIdeleClassNorm_range_map_congrOfAlgEquiv
    (eK : K ≃ₐ[ℚ] K')
    (eL : L ≃ₐ[ℚ] L')
    (h : ∀ x : K,
      eL (algebraMap K L x) =
        algebraMap K' L' (eK x)) :
    (_root_.ideleClassNorm K L).range.map
        (ideleClassCongr eK).toMonoidHom =
      (_root_.ideleClassNorm K' L').range := by
  rw [ordinaryIdeleClassNorm_range_eq_relative
      (K := K) (L := L),
    ordinaryIdeleClassNorm_range_eq_relative
      (K := K') (L := L')]
  exact
    relativeIdeleClassNorm_range_map_congrOfAlgEquiv
      eK eL h

-- Fix the canonical commutativity proof used by the norm-range quotients.
local instance normIdeleClassGroup_isMulCommutative
    (F : Type) [Field F] [NumberField F] :
    IsMulCommutative (IdeleClassGroup F) :=
  IsMulCommutative.of_comm (fun a b => mul_comm a b)

/-- Compatible equivalences of finite Galois number-field extensions
induce the canonical equivalence of their ordinary idele-class norm
quotients. -/
noncomputable def ordinaryIdeleClassNormQuotientCongrOfAlgEquiv
    (eK : K ≃ₐ[ℚ] K')
    (eL : L ≃ₐ[ℚ] L')
    (h : ∀ x : K,
      eL (algebraMap K L x) =
        algebraMap K' L' (eK x)) :
    (IdeleClassGroup K ⧸
        (_root_.ideleClassNorm K L).range) ≃*
      (IdeleClassGroup K' ⧸
        (_root_.ideleClassNorm K' L').range) :=
  QuotientGroup.congr
    (_root_.ideleClassNorm K L).range
    (_root_.ideleClassNorm K' L').range
    (ideleClassCongr eK)
    (ordinaryIdeleClassNorm_range_map_congrOfAlgEquiv
      eK eL h)

omit [FiniteDimensional K L] [FiniteDimensional K' L']
  [IsGalois K L] [IsGalois K' L'] in
/-- On an ordinary idele-class representative, transport of norm
quotients is induced by the existing idele-class transport. -/
@[simp]
theorem ordinaryIdeleClassNormQuotientCongrOfAlgEquiv_mk
    (eK : K ≃ₐ[ℚ] K')
    (eL : L ≃ₐ[ℚ] L')
    (h : ∀ x : K,
      eL (algebraMap K L x) =
        algebraMap K' L' (eK x))
    (c : IdeleClassGroup K) :
    ordinaryIdeleClassNormQuotientCongrOfAlgEquiv
        eK eL h
        (QuotientGroup.mk'
          (_root_.ideleClassNorm K L).range c) =
      QuotientGroup.mk'
        (_root_.ideleClassNorm K' L').range
        (ideleClassCongr eK c) :=
  rfl

end Norm

end RelativeTowerCongr
end Absolute
end
end

section
-- module Solutions.OAIQ244_DUKE.AlgebraicNumberTheory_Idele_ClassGroup_TowerBaseChange
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.GlobalClassFields.ConductorialSubgroup.finiteIndex _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.KummerTheory.primeCyclotomicBaseFiniteDimensional _root_.LocalClassFieldTheory.finiteGaloisLocalField_integerRing_moduleFinite _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.residueFieldZModAlgebra _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedIntegralAlgebraContextValuationSubringAlgebra _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedQPadicContextValuationSubringTower _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.CyclicCohomology.binaryCoefficientFamilyCommGroup _root_.LocalClassFieldTheory.comparisonIntegerRingIsIntegralClosure _root_.LocalClassFieldTheory.normalizationIntegerRingIsIntegralClosure _root_.chosenFinitePlaceBaseValued _root_.chosenFinitePlaceCompletionAlgebra _root_.chosenFinitePlaceCompletionFiniteDimensional _root_.chosenFinitePlaceLocalizedFiniteDimensional _root_.relativeUnrestrictedSPlaceFactorCommGroup
attribute [-simp] _root_.IdeleGroup.finitePlaceIdele_finiteComponent_of_ne _root_.IdeleGroup.finitePlaceIdele_finiteComponent_same _root_.IdeleGroup.finitePlaceIdele_infiniteComponent _root_.IdeleGroup.infinitePlaceIdeleContinuous_apply _root_.IdeleGroup.infinitePlaceIdele_finiteComponent _root_.IdeleGroup.infinitePlaceIdele_infiniteComponent_of_ne _root_.IdeleGroup.infinitePlaceIdele_infiniteComponent_same _root_.IsDiscreteValuationRing.addVal_ringEquiv _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.OAI.PrimeDegreePackets.ThetaConstruction.schwartzCM_apply _root_.RayClass.primesEquiv_val_eq_natGenerator _root_.RayClass.signToNarrow_mk _root_.RelativeIdeleGroup.relativeFinitePlaceIdele_finiteComponent_of_ne _root_.RelativeIdeleGroup.relativeFinitePlaceIdele_finiteComponent_same _root_.RelativeIdeleGroup.relativeFinitePlaceIdele_infiniteComponent _root_.RelativeIdeleGroup.relativeInfinitePlaceIdele_finiteComponent _root_.RelativeIdeleGroup.relativeInfinitePlaceIdele_infiniteComponent_of_ne _root_.RelativeIdeleGroup.relativeInfinitePlaceIdele_infiniteComponent_same _root_.relativeAdeleMapOfCompatibleEquiv_tmul _root_.finiteIdeleOfSPlaceFactors_apply_mem _root_.finiteIdeleOfSPlaceFactors_apply_notMem _root_.ideleClassCongr_mk _root_.ideleCongr_finiteComponent _root_.ideleCongr_principalIdele _root_.ideleSupportedAtEquivSPlaceFactors_infinite _root_.ideleSupportedAtEquivSPlaceFactors_inside _root_.ideleSupportedAtEquivSPlaceFactors_outside_coe _root_.ordinaryIdeleClassNormQuotientCongrOfAlgEquiv_mk _root_.relativeAdeleCongrOfAlgEquiv_tmul _root_.relativeAdeleCongr_tmul _root_.relativeIdeleClassCongrOfAlgEquiv_ideleClassNorm _root_.relativeIdeleClassCongrOfAlgEquiv_mk _root_.relativeIdeleClassCongr_ideleClassNorm _root_.relativeIdeleClassCongr_mk _root_.relativeIdeleCongrOfAlgEquiv_principalIdele _root_.relativeIdeleCongr_coe _root_.relativeIdeleCongr_norm _root_.relativeIdeleCongr_principalIdele
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI
attribute [local instance] OAI.starSubalgebraCommCStarAlgebra

set_option autoImplicit false

/-!
# The fixed-bottom tower model and the actual intermediate-field model

For a tower `K ⊂ M ⊂ L`, `IdeleClassTower` presents the ideles of `L`
as units of `(𝔸_K ⊗[K] M) ⊗[M] L`.  Here we compare that presentation
with the actual relative idele group `𝔸_M ⊗[M] L`, by passing through
the ordinary ideles of `L`.
-/

open scoped NumberField TensorProduct
open NumberField IsDedekindDomain

noncomputable section

open AlgebraicNumberTheory.Valuations

universe u

variable
    (K M L : Type u)
    [Field K] [NumberField K]
    [Field M] [NumberField M]
    [Field L] [NumberField L]
    [Algebra K M] [Algebra M L] [Algebra K L]
    [IsScalarTower K M L]
    [FiniteDimensional K M] [FiniteDimensional M L]

section RingComparison

attribute [local instance] towerBaseChange_towerRelativeIdeleGroupIsMulCommutative
attribute [local instance] towerBaseChange_relativeIdeleClassGroupIsMulCommutative
attribute [local instance] towerBaseChange_ideleClassGroupIsMulCommutative
theorem relativeAdeleBaseChangeRingEquiv_tower_finiteComponent
    (z : TowerRelativeAdeleRing K M L)
    (W : HeightOneSpectrum (𝓞 L)) :
    (relativeAdeleBaseChangeRingEquiv
        (K := M) (L := L)
        (towerActualRelativeAdeleRingEquiv K M L z)).2 W =
      (relativeAdeleBaseChangeRingEquiv
        (K := K) (L := L)
        (towerRelativeAdeleRingEquiv K M L z)).2 W := by
  induction z using OAI.tensorInductionOn with
  | add z₁ z₂ hz₁ hz₂ =>
      simp only [map_add]
      change
        (relativeAdeleBaseChangeRingEquiv
            (towerActualRelativeAdeleRingEquiv K M L z₁)).2 W +
          (relativeAdeleBaseChangeRingEquiv
            (towerActualRelativeAdeleRingEquiv K M L z₂)).2 W =
        (relativeAdeleBaseChangeRingEquiv
            (towerRelativeAdeleRingEquiv K M L z₁)).2 W +
          (relativeAdeleBaseChangeRingEquiv
            (towerRelativeAdeleRingEquiv K M L z₂)).2 W
      exact congrArg₂ (· + ·) hz₁ hz₂
  | tmul b x =>
      induction b using OAI.tensorInductionOn with
      | add b₁ b₂ hb₁ hb₂ =>
          simp only [TensorProduct.add_tmul, map_add]
          change
            (relativeAdeleBaseChangeRingEquiv
                (towerActualRelativeAdeleRingEquiv K M L
                  (b₁ ⊗ₜ[M] x))).2 W +
              (relativeAdeleBaseChangeRingEquiv
                (towerActualRelativeAdeleRingEquiv K M L
                  (b₂ ⊗ₜ[M] x))).2 W =
            (relativeAdeleBaseChangeRingEquiv
                (towerRelativeAdeleRingEquiv K M L
                  (b₁ ⊗ₜ[M] x))).2 W +
              (relativeAdeleBaseChangeRingEquiv
                (towerRelativeAdeleRingEquiv K M L
                  (b₂ ⊗ₜ[M] x))).2 W
          exact congrArg₂ (· + ·) hb₁ hb₂
      | tmul a m =>
          have hflatten :
              towerRelativeAdeleRingEquiv K M L
                  ((a ⊗ₜ[K] m) ⊗ₜ[M] x) =
                a ⊗ₜ[K] (algebraMap M L m * x) := by
            change
              towerRelativeAdeleFlatten K M L
                  ((a ⊗ₜ[K] m) ⊗ₜ[M] x) =
                a ⊗ₜ[K] (algebraMap M L m * x)
            rw [
              towerRelativeAdeleFlatten_tmul,
              intermediateAdeleInclusion_tmul,
              topFieldToOneStep_apply,
              Algebra.TensorProduct.tmul_mul_tmul, mul_one]
          let V := finitePlaceBelow (K := M) W
          let v := finitePlaceBelow (K := K) W
          have hv :
              finitePlaceBelow (K := K) V = v :=
            finitePlaceBelow_finitePlaceBelow
              (K := K) (M := M) (L := L) W
          have hcomponent
              (v' : HeightOneSpectrum (𝓞 K))
              (hv' : v' = v)
              (hV : finitePlaceBelow (K := K) V = v')
              (hWV : finitePlaceBelow (K := M) W = V)
              (hWv : finitePlaceBelow (K := K) W = v) :
              finitePlaceAdicCompletionMap M L V ⟨W, hWV⟩
                    (finitePlaceAdicCompletionMap K M v' ⟨V, hV⟩
                        (a.2 v') *
                      algebraMap M (V.adicCompletion M) m) *
                  algebraMap L (W.adicCompletion L) x =
                finitePlaceAdicCompletionMap K L v ⟨W, hWv⟩
                    (a.2 v) *
                  algebraMap L (W.adicCompletion L)
                    (algebraMap M L m * x) := by
            subst v'
            have hm :
                finitePlaceAdicCompletionMap M L V ⟨W, hWV⟩
                    (algebraMap M (V.adicCompletion M) m) =
                  algebraMap L (W.adicCompletion L)
                    (algebraMap M L m) := by
              change
                finitePlaceAdicCompletionMap M L V ⟨W, hWV⟩
                    (m : V.adicCompletion M) =
                  (algebraMap M L m : W.adicCompletion L)
              exact
                finitePlaceAdicCompletionMap_coe M L
                  V ⟨W, hWV⟩ m
            rw [map_mul,
              finitePlaceAdicCompletionMap_comp K L (M := M) v V W
                hV hWV hWv,
              hm,
              map_mul, mul_assoc]
          rw [towerActualRelativeAdeleRingEquiv_tmul, hflatten]
          rw [
            relativeAdeleBaseChangeRingEquiv_finiteComponent_tmul
              (K := M) (L := L)]
          change
            finitePlaceAdicCompletionMap M L V ⟨W, rfl⟩
                ((relativeAdeleBaseChangeRingEquiv
                  (K := K) (L := M) (a ⊗ₜ[K] m)).2 V) *
              algebraMap L (W.adicCompletion L) x =
            (relativeAdeleBaseChangeRingEquiv
              (K := K) (L := L)
              (a ⊗ₜ[K] (algebraMap M L m * x))).2 W
          rw [
            relativeAdeleBaseChangeRingEquiv_finiteComponent_tmul
              (K := K) (L := M),
            relativeAdeleBaseChangeRingEquiv_finiteComponent_tmul
              (K := K) (L := L)]
          exact hcomponent
            (finitePlaceBelow (K := K) V) hv rfl rfl rfl

theorem relativeAdeleBaseChangeRingEquiv_tower_infiniteComponent
    (z : TowerRelativeAdeleRing K M L)
    (W : InfinitePlace L) :
    (relativeAdeleBaseChangeRingEquiv
        (K := M) (L := L)
        (towerActualRelativeAdeleRingEquiv K M L z)).1 W =
      (relativeAdeleBaseChangeRingEquiv
        (K := K) (L := L)
        (towerRelativeAdeleRingEquiv K M L z)).1 W := by
  induction z using OAI.tensorInductionOn with
  | add z₁ z₂ hz₁ hz₂ =>
      simp only [map_add]
      change
        (relativeAdeleBaseChangeRingEquiv
            (towerActualRelativeAdeleRingEquiv K M L z₁)).1 W +
          (relativeAdeleBaseChangeRingEquiv
            (towerActualRelativeAdeleRingEquiv K M L z₂)).1 W =
        (relativeAdeleBaseChangeRingEquiv
            (towerRelativeAdeleRingEquiv K M L z₁)).1 W +
          (relativeAdeleBaseChangeRingEquiv
            (towerRelativeAdeleRingEquiv K M L z₂)).1 W
      exact congrArg₂ (· + ·) hz₁ hz₂
  | tmul b x =>
      induction b using OAI.tensorInductionOn with
      | add b₁ b₂ hb₁ hb₂ =>
          simp only [TensorProduct.add_tmul, map_add]
          change
            (relativeAdeleBaseChangeRingEquiv
                (towerActualRelativeAdeleRingEquiv K M L
                  (b₁ ⊗ₜ[M] x))).1 W +
              (relativeAdeleBaseChangeRingEquiv
                (towerActualRelativeAdeleRingEquiv K M L
                  (b₂ ⊗ₜ[M] x))).1 W =
            (relativeAdeleBaseChangeRingEquiv
                (towerRelativeAdeleRingEquiv K M L
                  (b₁ ⊗ₜ[M] x))).1 W +
              (relativeAdeleBaseChangeRingEquiv
                (towerRelativeAdeleRingEquiv K M L
                  (b₂ ⊗ₜ[M] x))).1 W
          exact congrArg₂ (· + ·) hb₁ hb₂
      | tmul a m =>
          have hflatten :
              towerRelativeAdeleRingEquiv K M L
                  ((a ⊗ₜ[K] m) ⊗ₜ[M] x) =
                a ⊗ₜ[K] (algebraMap M L m * x) := by
            change
              towerRelativeAdeleFlatten K M L
                  ((a ⊗ₜ[K] m) ⊗ₜ[M] x) =
                a ⊗ₜ[K] (algebraMap M L m * x)
            rw [
              towerRelativeAdeleFlatten_tmul,
              intermediateAdeleInclusion_tmul,
              topFieldToOneStep_apply,
              Algebra.TensorProduct.tmul_mul_tmul, mul_one]
          let V := infinitePlaceBelow (K := M) W
          let v := infinitePlaceBelow (K := K) W
          have hv :
              infinitePlaceBelow (K := K) V = v :=
            infinitePlaceBelow_infinitePlaceBelow
              (K := K) (M := M) (L := L) W
          have hcomponent
              (v' : InfinitePlace K)
              (hv' : v' = v)
              [hVv : V.1.LiesOver v'.1]
              [hWV : W.1.LiesOver V.1]
              [hWv : W.1.LiesOver v.1] :
              NumberField.LiesOver.completionMap
                    (v := V) (w := W)
                    (NumberField.LiesOver.completionMap
                        (v := v') (w := V) (a.1 v') *
                      algebraMap M V.Completion m) *
                  algebraMap L W.Completion x =
                NumberField.LiesOver.completionMap
                    (v := v) (w := W) (a.1 v) *
                  algebraMap L W.Completion
                    (algebraMap M L m * x) := by
            subst v'
            have hm :
                NumberField.LiesOver.completionMap
                    (v := V) (w := W)
                    (algebraMap M V.Completion m) =
                  algebraMap L W.Completion
                    (algebraMap M L m) := by
              have h :
                  algebraMap M V.Completion m =
                    ((WithAbs.toAbs V.1 m : WithAbs V.1) :
                      V.Completion) :=
                rfl
              rw [h,
                NumberField.LiesOver.completionMap_coe
                  (v := V) (w := W)]
              apply InfinitePlace.Completion.ext
              rw [
                InfinitePlace.Completion.algebraMap_toCompletion,
                UniformSpace.Completion.algebraMap_def]
              simp [WithAbs.algebraMap_left_apply,
                WithAbs.algebraMap_right_apply]
            rw [map_mul,
              infinitePlaceCompletionMap_comp_apply
                (K := K) (M := M) (L := L) W,
              hm,
              map_mul, mul_assoc]
          let : V.1.LiesOver v.1 :=
            ⟨congrArg (fun q : InfinitePlace K => q.1)
              hv⟩
          let : W.1.LiesOver V.1 := ⟨rfl⟩
          let : W.1.LiesOver v.1 := ⟨rfl⟩
          rw [towerActualRelativeAdeleRingEquiv_tmul, hflatten]
          rw [
            relativeAdeleBaseChangeRingEquiv_infiniteComponent_tmul
              (K := M) (L := L)]
          change
            NumberField.LiesOver.completionMap
                (v := V) (w := W)
                ((relativeAdeleBaseChangeRingEquiv
                  (K := K) (L := M) (a ⊗ₜ[K] m)).1 V) *
              algebraMap L W.Completion x =
            _
          rw [
            relativeAdeleBaseChangeRingEquiv_infiniteComponent_tmul
              (K := K) (L := M),
            relativeAdeleBaseChangeRingEquiv_infiniteComponent_tmul
              (K := K) (L := L)]
          exact hcomponent
            (infinitePlaceBelow (K := K) V) hv
            (hVv := ⟨rfl⟩)
            (hWV := ⟨rfl⟩)
            (hWv := ⟨rfl⟩)

/-- Passing from the fixed-bottom tower presentation to ordinary adeles
is independent of whether one first changes to the actual relative
presentation over the intermediate field. -/
theorem relativeAdeleBaseChangeRingEquiv_tower
    (z : TowerRelativeAdeleRing K M L) :
    relativeAdeleBaseChangeRingEquiv
        (K := M) (L := L)
        (towerActualRelativeAdeleRingEquiv K M L z) =
      relativeAdeleBaseChangeRingEquiv
        (K := K) (L := L)
        (towerRelativeAdeleRingEquiv K M L z) := by
  apply Prod.ext
  · funext W
    exact
      relativeAdeleBaseChangeRingEquiv_tower_infiniteComponent
        K M L z W
  · apply DFunLike.coe_injective
    funext W
    exact
      relativeAdeleBaseChangeRingEquiv_tower_finiteComponent
        K M L z W

end RingComparison

section ClassNormComparison

attribute [local instance] towerBaseChange_towerRelativeIdeleGroupIsMulCommutative
attribute [local instance] towerBaseChange_relativeIdeleClassGroupIsMulCommutative
attribute [local instance] towerBaseChange_ideleClassGroupIsMulCommutative
omit [NumberField L] [Algebra K L] [IsScalarTower K M L] in
@[simp]
theorem intermediateClassNormQuotientBaseChangeMulEquiv_mk
    (c : RelativeIdeleGroup.ClassGroup K M) :
    intermediateClassNormQuotientBaseChangeMulEquiv K M L
        (QuotientGroup.mk'
          (TowerRelativeIdeleGroup.classNorm K M L).range c) =
      QuotientGroup.mk'
        (RelativeIdeleGroup.classNorm M L).range
        (relativeIdeleClassBaseChangeMulEquiv
          (K := K) (L := M) c) :=
  rfl

end ClassNormComparison
end
end

section
-- module Solutions.OAIQ244_DUKE.AlgebraicNumberTheory_Idele_ClassGroup_TowerAlgEquivNaturality
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 400000
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.GlobalClassFields.ConductorialSubgroup.finiteIndex _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.KummerTheory.primeCyclotomicBaseFiniteDimensional _root_.KummerTheory.primeCyclotomicBaseNumberField _root_.LocalClassFieldTheory.finiteGaloisLocalField_integerRing_moduleFinite _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.residueFieldZModAlgebra _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedIntegralAlgebraContextValuationSubringAlgebra _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedQPadicContextValuationSubringTower _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.diagonalLogAction _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.CyclicCohomology.binaryCoefficientFamilyCommGroup _root_.LocalClassFieldTheory.comparisonIntegerRingIsIntegralClosure _root_.LocalClassFieldTheory.normalizationIntegerRingIsIntegralClosure _root_.chosenFinitePlaceCompletionAlgebra _root_.chosenFinitePlaceCompletionFiniteDimensional _root_.chosenFinitePlaceLocalizedFiniteDimensional _root_.relativeUnrestrictedSPlaceFactorCommGroup
attribute [-simp] _root_.IdeleGroup.finitePlaceIdele_finiteComponent_of_ne _root_.IdeleGroup.finitePlaceIdele_finiteComponent_same _root_.IdeleGroup.finitePlaceIdele_infiniteComponent _root_.IdeleGroup.infinitePlaceIdeleContinuous_apply _root_.IdeleGroup.infinitePlaceIdele_finiteComponent _root_.IdeleGroup.infinitePlaceIdele_infiniteComponent_of_ne _root_.IdeleGroup.infinitePlaceIdele_infiniteComponent_same _root_.IsDiscreteValuationRing.addVal_ringEquiv _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.OAI.PrimeDegreePackets.ThetaConstruction.schwartzCM_apply _root_.RayClass.primesEquiv_val_eq_natGenerator _root_.RayClass.signToNarrow_mk _root_.RelativeIdeleGroup.relativeFinitePlaceIdele_finiteComponent_of_ne _root_.RelativeIdeleGroup.relativeFinitePlaceIdele_finiteComponent_same _root_.RelativeIdeleGroup.relativeFinitePlaceIdele_infiniteComponent _root_.RelativeIdeleGroup.relativeInfinitePlaceIdele_finiteComponent _root_.RelativeIdeleGroup.relativeInfinitePlaceIdele_infiniteComponent_of_ne _root_.RelativeIdeleGroup.relativeInfinitePlaceIdele_infiniteComponent_same _root_.finiteIdeleOfSPlaceFactors_apply_mem _root_.finiteIdeleOfSPlaceFactors_apply_notMem _root_.ideleSupportedAtEquivSPlaceFactors_infinite _root_.ideleSupportedAtEquivSPlaceFactors_inside _root_.ideleSupportedAtEquivSPlaceFactors_outside_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

/-!
# Naturality of tower base change under number-field equivalences

The ordinary idele group of a finite extension is obtained from the
relative tensor presentation by scalar extension.  This file proves that
this comparison is natural when both fields in the extension are replaced
by compatible equivalent number fields.  The proof passes through the
fixed-bottom tower

`(𝔸_ℚ ⊗[ℚ] K) ⊗[K] L`

and therefore uses only tensor-product coherence; no new description of
local components is introduced.
-/

open scoped NumberField TensorProduct
open NumberField

noncomputable section

variable
    {K K' L L' : Type}
    [Field K] [NumberField K]
    [Field K'] [NumberField K']
    [Field L] [NumberField L] [Algebra K L]
    [Field L'] [NumberField L'] [Algebra K' L']
    [FiniteDimensional K L]
    [FiniteDimensional K' L']

section CongrComposition

variable
    {M N : Type}
    [Field M] [NumberField M]
    [Field N] [NumberField N]

/-- Transport of ordinary idele classes along the identity
number-field equivalence is the identity. -/
@[simp]
theorem ideleClassCongr_refl
    (c : IdeleClassGroup K) :
    ideleClassCongr
        (AlgEquiv.refl : K ≃ₐ[ℚ] K) c =
      c := by
  refine QuotientGroup.induction_on c ?_
  intro a
  change
    ideleClassCongr
        (AlgEquiv.refl : K ≃ₐ[ℚ] K)
        (QuotientGroup.mk'
          (IdeleGroup.principalSubgroup K) a) =
      QuotientGroup.mk'
        (IdeleGroup.principalSubgroup K) a
  rw [ideleClassCongr_mk]
  congr 1
  apply
    (IdeleGroup.equivAdeleRingUnits
      (K := K)).injective
  simp only [ideleCongr, MulEquiv.trans_apply,
    MulEquiv.apply_symm_apply]
  apply Units.ext
  let u : NumberField.AdeleRing (𝓞 K) K :=
    ((IdeleGroup.equivAdeleRingUnits (K := K) a :
      (NumberField.AdeleRing (𝓞 K) K)ˣ) :
      NumberField.AdeleRing (𝓞 K) K)
  change
    adeleCongr
        (AlgEquiv.refl : K ≃ₐ[ℚ] K) u =
      u
  let z : RelativeAdeleRing ℚ K :=
    (relativeAdeleBaseChangeRingEquiv
      (K := ℚ) (L := K)).symm u
  have hz :
      relativeAdeleBaseChangeRingEquiv
          (K := ℚ) (L := K) z = u :=
    (relativeAdeleBaseChangeRingEquiv
      (K := ℚ) (L := K)).apply_symm_apply u
  have hcongr :
      relativeAdeleCongr (K := ℚ)
          (AlgEquiv.refl : K ≃ₐ[ℚ] K) z = z := by
    induction z using OAI.tensorInductionOn with
    | add x y hx hy =>
        simpa only [map_add] using congrArg₂ (· + ·) hx hy
    | tmul b x =>
        rw [relativeAdeleCongr_tmul]
        rfl
  calc
    adeleCongr
          (AlgEquiv.refl : K ≃ₐ[ℚ] K) u =
        adeleCongr
          (AlgEquiv.refl : K ≃ₐ[ℚ] K)
          (relativeAdeleBaseChangeRingEquiv
            (K := ℚ) (L := K) z) :=
      congrArg _ hz.symm
    _ =
        relativeAdeleBaseChangeRingEquiv
          (K := ℚ) (L := K)
          (relativeAdeleCongr (K := ℚ)
            (AlgEquiv.refl : K ≃ₐ[ℚ] K) z) :=
      (relativeAdeleBaseChangeRingEquiv_relativeAdeleCongr
        (AlgEquiv.refl : K ≃ₐ[ℚ] K) z).symm
    _ =
        relativeAdeleBaseChangeRingEquiv
          (K := ℚ) (L := K) z := by
      rw [hcongr]
    _ = u := hz

end CongrComposition

omit [FiniteDimensional K L] [FiniteDimensional K' L'] in
/-- Before passing to ordinary adeles, compatible transport of a tower
agrees with transporting its flattened rational tensor presentation. -/
theorem relativeAdeleCongrOfAlgEquiv_towerActual
    (eK : K ≃ₐ[ℚ] K')
    (eL : L ≃ₐ[ℚ] L')
    (h : ∀ x : K,
      eL (algebraMap K L x) =
        algebraMap K' L' (eK x))
    (z : TowerRelativeAdeleRing ℚ K L) :
    relativeAdeleCongrOfAlgEquiv eK eL h
        (towerActualRelativeAdeleRingEquiv ℚ K L z) =
      towerActualRelativeAdeleRingEquiv ℚ K' L'
        (towerRelativeAdeleUnflatten ℚ K' L'
          (relativeAdeleCongr (K := ℚ) eL
            (towerRelativeAdeleFlatten ℚ K L z))) := by
  induction z using OAI.tensorInductionOn with
  | add z₁ z₂ hz₁ hz₂ =>
      simpa only [map_add] using congrArg₂ (· + ·) hz₁ hz₂
  | tmul b x =>
      induction b using OAI.tensorInductionOn with
      | add b₁ b₂ hb₁ hb₂ =>
          simpa only [TensorProduct.add_tmul, map_add] using
            congrArg₂ (· + ·) hb₁ hb₂
      | tmul a y =>
          have hK :
              adeleCongr eK
                  (relativeAdeleBaseChangeRingEquiv
                    (K := ℚ) (L := K) (a ⊗ₜ[ℚ] y)) =
                relativeAdeleBaseChangeRingEquiv
                  (K := ℚ) (L := K')
                  (a ⊗ₜ[ℚ] eK y) := by
            rw [←
              relativeAdeleBaseChangeRingEquiv_relativeAdeleCongr
                eK (a ⊗ₜ[ℚ] y),
              relativeAdeleCongr_tmul]
          change
            relativeAdeleCongrOfAlgEquiv eK eL h
                (relativeAdeleBaseChangeRingEquiv
                    (K := ℚ) (L := K) (a ⊗ₜ[ℚ] y) ⊗ₜ[K] x) =
              towerActualRelativeAdeleRingEquiv ℚ K' L'
                (towerRelativeAdeleUnflatten ℚ K' L'
                  (relativeAdeleCongr (K := ℚ) eL
                    (towerRelativeAdeleFlatten ℚ K L
                      ((a ⊗ₜ[ℚ] y) ⊗ₜ[K] x))))
          rw [relativeAdeleCongrOfAlgEquiv_tmul,
            towerRelativeAdeleFlatten_tmul,
            intermediateAdeleInclusion_tmul,
            topFieldToOneStep_apply,
            Algebra.TensorProduct.tmul_mul_tmul,
            mul_one,
            relativeAdeleCongr_tmul,
            map_mul, h,
            towerRelativeAdeleUnflatten_tmul,
            bottomAdeleToTower_apply,
            topFieldToTower_apply,
            Algebra.TensorProduct.tmul_mul_tmul,
            mul_one, one_mul,
            towerActualRelativeAdeleRingEquiv_tmul]
          rw [hK]
          change
            relativeAdeleBaseChangeRingEquiv
                  (K := ℚ) (L := K') (a ⊗ₜ[ℚ] eK y) ⊗ₜ[K'] eL x =
              relativeAdeleBaseChangeRingEquiv
                  (K := ℚ) (L := K') (a ⊗ₜ[ℚ] (1 : K')) ⊗ₜ[K']
                ((algebraMap K' L') (eK y) * eL x)
          have htmul :
              (a ⊗ₜ[ℚ] eK y : RelativeAdeleRing ℚ K') =
                (a ⊗ₜ[ℚ] (1 : K')) *
                  ((1 : NumberField.AdeleRing (𝓞 ℚ) ℚ) ⊗ₜ[ℚ] eK y) := by
            rw [Algebra.TensorProduct.tmul_mul_tmul,
              mul_one, one_mul]
          rw [htmul, map_mul,
            relativeAdeleBaseChangeRingEquiv_fieldInclusion]
          rw [mul_comm
            (relativeAdeleBaseChangeRingEquiv
              (K := ℚ) (L := K') (a ⊗ₜ[ℚ] (1 : K')))
            (algebraMap K'
              (NumberField.AdeleRing (𝓞 K') K') (eK y)),
            ← Algebra.smul_def, TensorProduct.smul_tmul,
            Algebra.smul_def]

/-- The relative-to-ordinary adele comparison commutes with compatible
equivalences of both fields in a finite extension. -/
theorem relativeAdeleBaseChangeRingEquiv_congrOfAlgEquiv
    (eK : K ≃ₐ[ℚ] K')
    (eL : L ≃ₐ[ℚ] L')
    (h : ∀ x : K,
      eL (algebraMap K L x) =
        algebraMap K' L' (eK x))
    (z : RelativeAdeleRing K L) :
    relativeAdeleBaseChangeRingEquiv
        (K := K') (L := L')
        (relativeAdeleCongrOfAlgEquiv eK eL h z) =
      adeleCongr eL
        (relativeAdeleBaseChangeRingEquiv
          (K := K) (L := L) z) := by
  let t : TowerRelativeAdeleRing ℚ K L :=
    (towerActualRelativeAdeleRingEquiv ℚ K L).symm z
  let q : RelativeAdeleRing ℚ L' :=
    relativeAdeleCongr (K := ℚ) eL
      (towerRelativeAdeleFlatten ℚ K L t)
  calc
    relativeAdeleBaseChangeRingEquiv
          (K := K') (L := L')
          (relativeAdeleCongrOfAlgEquiv eK eL h z) =
        relativeAdeleBaseChangeRingEquiv
          (K := K') (L := L')
          (relativeAdeleCongrOfAlgEquiv eK eL h
            (towerActualRelativeAdeleRingEquiv ℚ K L t)) := by
      rw [(towerActualRelativeAdeleRingEquiv ℚ K L).apply_symm_apply]
    _ =
        relativeAdeleBaseChangeRingEquiv
          (K := K') (L := L')
          (towerActualRelativeAdeleRingEquiv ℚ K' L'
            (towerRelativeAdeleUnflatten ℚ K' L' q)) := by
      rw [relativeAdeleCongrOfAlgEquiv_towerActual]
    _ =
        relativeAdeleBaseChangeRingEquiv
          (K := ℚ) (L := L')
          (towerRelativeAdeleRingEquiv ℚ K' L'
            (towerRelativeAdeleUnflatten ℚ K' L' q)) :=
      relativeAdeleBaseChangeRingEquiv_tower
        ℚ K' L' (towerRelativeAdeleUnflatten ℚ K' L' q)
    _ =
        relativeAdeleBaseChangeRingEquiv
          (K := ℚ) (L := L') q := by
      change
        relativeAdeleBaseChangeRingEquiv
            (K := ℚ) (L := L')
            ((towerRelativeAdeleRingEquiv ℚ K' L')
              ((towerRelativeAdeleRingEquiv ℚ K' L').symm q)) =
          relativeAdeleBaseChangeRingEquiv
            (K := ℚ) (L := L') q
      rw [RingEquiv.apply_symm_apply]
    _ =
        adeleCongr eL
          (relativeAdeleBaseChangeRingEquiv
            (K := ℚ) (L := L)
            (towerRelativeAdeleFlatten ℚ K L t)) :=
      relativeAdeleBaseChangeRingEquiv_relativeAdeleCongr
        eL (towerRelativeAdeleFlatten ℚ K L t)
    _ =
        adeleCongr eL
          (relativeAdeleBaseChangeRingEquiv
            (K := K) (L := L)
            (towerActualRelativeAdeleRingEquiv ℚ K L t)) := by
      change
        adeleCongr eL
          (relativeAdeleBaseChangeRingEquiv
            (K := ℚ) (L := L)
            ((towerRelativeAdeleRingEquiv ℚ K L) t)) =
          adeleCongr eL
            (relativeAdeleBaseChangeRingEquiv
              (K := K) (L := L)
              (towerActualRelativeAdeleRingEquiv ℚ K L t))
      rw [← relativeAdeleBaseChangeRingEquiv_tower]
    _ =
        adeleCongr eL
          (relativeAdeleBaseChangeRingEquiv
            (K := K) (L := L) z) := by
      rw [(towerActualRelativeAdeleRingEquiv ℚ K L).apply_symm_apply]

/-- The relative-to-ordinary idele comparison commutes with compatible
equivalences of both fields in a finite extension. -/
theorem relativeIdeleBaseChangeMulEquiv_congrOfAlgEquiv
    (eK : K ≃ₐ[ℚ] K')
    (eL : L ≃ₐ[ℚ] L')
    (h : ∀ x : K,
      eL (algebraMap K L x) =
        algebraMap K' L' (eK x))
    (a : RelativeIdeleGroup K L) :
    relativeIdeleBaseChangeMulEquiv
        (K := K') (L := L')
        (relativeIdeleCongrOfAlgEquiv eK eL h a) =
      ideleCongr eL
        (relativeIdeleBaseChangeMulEquiv
          (K := K) (L := L) a) := by
  apply
    (IdeleGroup.equivAdeleRingUnits
      (K := L')).injective
  rw [relativeIdeleBaseChangeMulEquiv_eq_ringUnits]
  simp only [ideleCongr, MulEquiv.trans_apply,
    MulEquiv.apply_symm_apply,
    relativeIdeleBaseChangeMulEquiv_eq_ringUnits]
  apply Units.ext
  exact
    relativeAdeleBaseChangeRingEquiv_congrOfAlgEquiv
      eK eL h (a : RelativeAdeleRing K L)

/-- The relative-to-ordinary idele-class comparison commutes with
compatible equivalences of both fields in a finite extension. -/
@[simp]
theorem relativeIdeleClassBaseChangeMulEquiv_congrOfAlgEquiv
    (eK : K ≃ₐ[ℚ] K')
    (eL : L ≃ₐ[ℚ] L')
    (h : ∀ x : K,
      eL (algebraMap K L x) =
        algebraMap K' L' (eK x))
    (c : RelativeIdeleGroup.ClassGroup K L) :
    relativeIdeleClassBaseChangeMulEquiv
        (K := K') (L := L')
        (relativeIdeleClassCongrOfAlgEquiv eK eL h c) =
      ideleClassCongr eL
        (relativeIdeleClassBaseChangeMulEquiv
          (K := K) (L := L) c) := by
  refine QuotientGroup.induction_on c ?_
  intro a
  exact congrArg
    (QuotientGroup.mk'
      (IdeleGroup.principalSubgroup L'))
    (relativeIdeleBaseChangeMulEquiv_congrOfAlgEquiv
      eK eL h a)

/-- Ordinary idele-class norms are natural under compatible
equivalences of finite number-field extensions. -/
@[simp]
theorem ideleClassCongr_ideleClassNorm
    (eK : K ≃ₐ[ℚ] K')
    (eL : L ≃ₐ[ℚ] L')
    (h : ∀ x : K,
      eL (algebraMap K L x) =
        algebraMap K' L' (eK x))
    (c : IdeleClassGroup L) :
    ideleClassCongr eK (_root_.ideleClassNorm K L c) =
      _root_.ideleClassNorm K' L' (ideleClassCongr eL c) := by
  let d : RelativeIdeleGroup.ClassGroup K L :=
    (relativeIdeleClassBaseChangeMulEquiv
      (K := K) (L := L)).symm c
  have hd :
      relativeIdeleClassBaseChangeMulEquiv
          (K := K) (L := L) d = c :=
    (relativeIdeleClassBaseChangeMulEquiv
      (K := K) (L := L)).apply_symm_apply c
  calc
    ideleClassCongr eK (_root_.ideleClassNorm K L c) =
        ideleClassCongr eK
          (_root_.ideleClassNorm K L
            (relativeIdeleClassBaseChangeMulEquiv
              (K := K) (L := L) d)) := by rw [hd]
    _ =
        ideleClassCongr eK
          (RelativeIdeleGroup.classNorm K L d) := by
      rw [ordinaryIdeleClassNorm_relativeIdeleClassBaseChange]
    _ =
        RelativeIdeleGroup.classNorm K' L'
          (relativeIdeleClassCongrOfAlgEquiv eK eL h d) :=
      relativeIdeleClassCongrOfAlgEquiv_ideleClassNorm
        eK eL h d
    _ =
        _root_.ideleClassNorm K' L'
          (relativeIdeleClassBaseChangeMulEquiv
            (K := K') (L := L')
            (relativeIdeleClassCongrOfAlgEquiv eK eL h d)) := by
      rw [ordinaryIdeleClassNorm_relativeIdeleClassBaseChange]
    _ =
        _root_.ideleClassNorm K' L'
          (ideleClassCongr eL
            (relativeIdeleClassBaseChangeMulEquiv
              (K := K) (L := L) d)) := by
      rw [relativeIdeleClassBaseChangeMulEquiv_congrOfAlgEquiv]
    _ =
        _root_.ideleClassNorm K' L'
          (ideleClassCongr eL c) := by
      rw [hd]
end
end

section
-- module Solutions.OAIQ244_DUKE.AlgebraicNumberTheory_Idele_SufficientlyLarge
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 400000
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.GlobalClassFields.ConductorialSubgroup.finiteIndex _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalClassFieldTheory.finiteGaloisLocalField_integerRing_moduleFinite _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.residueFieldZModAlgebra _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedIntegralAlgebraContextValuationSubringAlgebra _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.CyclicCohomology.binaryCoefficientFamilyCommGroup _root_.LocalClassFieldTheory.comparisonIntegerRingIsIntegralClosure _root_.LocalClassFieldTheory.normalizationIntegerRingIsIntegralClosure _root_.chosenFinitePlaceCompletionAlgebra _root_.relativeUnrestrictedSPlaceFactorCommGroup
attribute [-simp] _root_.IdeleGroup.finitePlaceIdele_finiteComponent_of_ne _root_.IdeleGroup.finitePlaceIdele_finiteComponent_same _root_.IdeleGroup.finitePlaceIdele_infiniteComponent _root_.IdeleGroup.infinitePlaceIdeleContinuous_apply _root_.IdeleGroup.infinitePlaceIdele_finiteComponent _root_.IdeleGroup.infinitePlaceIdele_infiniteComponent_of_ne _root_.IdeleGroup.infinitePlaceIdele_infiniteComponent_same _root_.IsDiscreteValuationRing.addVal_ringEquiv _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.OAI.PrimeDegreePackets.ThetaConstruction.schwartzCM_apply _root_.RayClass.primesEquiv_val_eq_natGenerator _root_.RayClass.signToNarrow_mk _root_.finiteIdeleOfSPlaceFactors_apply_mem _root_.finiteIdeleOfSPlaceFactors_apply_notMem _root_.ideleSupportedAtEquivSPlaceFactors_infinite _root_.ideleSupportedAtEquivSPlaceFactors_inside _root_.ideleSupportedAtEquivSPlaceFactors_outside_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

/-!
# A sufficiently large finite set of places

Finiteness of the ordinary ideal
class group lets us choose one idele representing each ideal class.  The
union of the (finite) supports of those representatives is a finite set
`S` for which

`I_K = I_K^S Kˣ`.
-/

open scoped NumberField
open NumberField IsDedekindDomain

noncomputable section


variable {K : Type*} [Field K] [NumberField K]

namespace IdeleGroup

/-- A chosen idele representing an ordinary ideal class. -/
def classRepresentative (c : ClassGroup (𝓞 K)) :
    IdeleGroup K :=
  Classical.choose (idealClass_surjective (K := K) c)

@[simp]
theorem idealClass_classRepresentative
    (c : ClassGroup (𝓞 K)) :
    idealClass (classRepresentative (K := K) c) = c :=
  Classical.choose_spec (idealClass_surjective (K := K) c)

end IdeleGroup
end
end

section
-- module Solutions.OAIQ244_DUKE.AlgebraicNumberTheory_Idele_Cohomology_SupportedBridge
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.GlobalClassFields.ConductorialSubgroup.finiteIndex _root_.GlobalClassFieldTheory.Reciprocity.infinitePlaceComplexificationOverfield_baseSmul _root_.GlobalClassFieldTheory.Reciprocity.infinitePlaceComplexificationOverfield_smul _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.DiscreteNthRootsSubgroup.instCommGroupSubtypeUnitsMemSubgroup _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.KummerTheory.finite_sUnit_nthPowerQuotient _root_.LocalClassFieldTheory.finiteGaloisLocalField_integerRing_moduleFinite _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.residueFieldZModAlgebra _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedIntegralAlgebraContextValuationSubringAlgebra _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.LubinTate.compatibleGroupFamiliesCommGroup _root_.LubinTate.compatibleGroupFamiliesGroup _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.diagonalLogAction _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.LocalClassFieldTheory.comparisonIntegerRingIsIntegralClosure _root_.LocalClassFieldTheory.normalizationIntegerRingIsIntegralClosure _root_.chosenFinitePlaceBaseValued _root_.chosenFinitePlaceCompletionAlgebra
attribute [-simp] _root_.IdeleGroup.finitePlaceIdele_finiteComponent_of_ne _root_.IdeleGroup.finitePlaceIdele_finiteComponent_same _root_.IdeleGroup.finitePlaceIdele_infiniteComponent _root_.IdeleGroup.infinitePlaceIdeleContinuous_apply _root_.IdeleGroup.infinitePlaceIdele_finiteComponent _root_.IdeleGroup.infinitePlaceIdele_infiniteComponent_of_ne _root_.IdeleGroup.infinitePlaceIdele_infiniteComponent_same _root_.IsDiscreteValuationRing.addVal_ringEquiv _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.KummerTheory.mem_sUnitFiniteKummerRadical_iff _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.OAI.PrimeDegreePackets.ThetaConstruction.schwartzCM_apply _root_.RayClass.primesEquiv_val_eq_natGenerator _root_.RayClass.signToNarrow_mk
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

/-!
# A sufficiently large unramified support for the idele-class calculation

This file constructs the finite set used in the idele-class Herbrand calculation.  It
contains the contractions of a sufficiently large set of places of `L`
and every finite place of `K` at which some place of `L` ramifies.

It also compares the concrete tensor-coordinate supported subgroup of
relative ideles with the ordinary supported idele subgroup of `L`.
-/

open scoped Classical NumberField TensorProduct
open NumberField IsDedekindDomain

noncomputable section


variable
    {K L : Type}
    [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]

/-- The finite set of places of `L` lying above a finite set of places
of `K`. -/
noncomputable def finitePlacesAbove
    (S : Finset (HeightOneSpectrum (𝓞 K))) :
    Finset (HeightOneSpectrum (𝓞 L)) :=
  (Set.Finite.preimage_finitePlaceBelow
    (K := K) (L := L) S.finite_toSet).toFinset

/-- A diagonal idele is supported at `T` exactly when its defining
field unit is a `T`-unit. -/
theorem principalIdele_mem_supportedAt_iff_sUnit
    (T : Finset (HeightOneSpectrum (𝓞 L)))
    (x : Lˣ) :
    IdeleGroup.principalIdele L x ∈
        IdeleGroup.supportedAt (K := L) (T : Set _) ↔
      x ∈ SUnitGroup (K := L) T := by
  rw [IdeleGroup.mem_supportedAt_iff, mem_SUnitGroup_iff]
  constructor
  · intro hx W hW
    have hunit := hx W (by simpa using hW)
    rw [
      HeightOneSpectrum.adicCompletionIntegers.mem_units_iff_valued_eq_one]
        at hunit
    change
      Valued.v
          (((IdeleGroup.finiteComponent W
            (IdeleGroup.principalIdele L x) :
              (W.adicCompletion L)ˣ) :
            W.adicCompletion L)) = 1 at hunit
    rw [IdeleGroup.finiteComponent_principalIdele,
      HeightOneSpectrum.valuedAdicCompletion_eq_valuation'] at hunit
    exact hunit
  · intro hx W hW
    rw [
      HeightOneSpectrum.adicCompletionIntegers.mem_units_iff_valued_eq_one]
    change
      Valued.v
          (((IdeleGroup.finiteComponent W
            (IdeleGroup.principalIdele L x) :
              (W.adicCompletion L)ˣ) :
            W.adicCompletion L)) = 1
    rw [IdeleGroup.finiteComponent_principalIdele,
      HeightOneSpectrum.valuedAdicCompletion_eq_valuation']
    exact hx W (by simpa using hW)

/-- The restricted Galois action on the intersection of the relative
principal and supported subgroups. -/
@[reducible]
noncomputable def relativePrincipalSupportedIntersectionAction
    (S : Finset (HeightOneSpectrum (𝓞 K))) :
    MulDistribMulAction (L ≃ₐ[K] L)
      ((RelativeIdeleGroup.principalSubgroup K L).subgroupOf
        (relativeIdeleLocalTensorDecompositionSupportedSubgroup
          (K := K) (L := L) S)) := by
  letI :=
    relativeIdeleLocalTensorDecompositionSupportedSubgroupAction
      (K := K) (L := L) S
  exact
    CyclicCohomology.stableSubgroupMulDistribMulAction
      ((RelativeIdeleGroup.principalSubgroup K L).subgroupOf
        (relativeIdeleLocalTensorDecompositionSupportedSubgroup
          (K := K) (L := L) S))
      (by
        intro σ z hz
        change
          (((σ • z :
              relativeIdeleLocalTensorDecompositionSupportedSubgroup
                (K := K) (L := L) S) :
            RelativeIdeleGroup K L)) ∈
              RelativeIdeleGroup.principalSubgroup K L
        rw [
          relativeIdeleLocalTensorDecompositionSupportedSubgroupAction_coe]
        obtain ⟨x, hx⟩ := hz
        refine
          ⟨Units.map σ.toRingEquiv.toMonoidHom x, ?_⟩
        calc
          RelativeIdeleGroup.principalIdele K L
              (Units.map σ.toRingEquiv.toMonoidHom x) =
              σ • RelativeIdeleGroup.principalIdele K L x :=
            (RelativeIdeleGroup.smul_principalIdele
              K L σ x).symm
          _ = σ • (z : RelativeIdeleGroup K L) :=
            congrArg (fun a : RelativeIdeleGroup K L => σ • a) hx)
end
end

section
-- module Solutions.OAIQ244_DUKE.LocalField_DiscreteValuationField_MixedCharacteristicStructure_IntegralLattice
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.infinitePlaceComplexificationOverfield_baseSmul _root_.GlobalClassFieldTheory.Reciprocity.infinitePlaceComplexificationOverfield_smul _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.KummerTheory.primeCyclotomicBaseFiniteDimensional _root_.LocalClassFieldTheory.finiteGaloisLocalField_integerRing_moduleFinite _root_.LocalClassFieldTheory.localDecompositionResidueFinite _root_.LocalClassFieldTheory.localDecompositionResidueFintype _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.residueFieldZModAlgebra _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedWithZeroValuationContextIntegralAlgebra _root_.LocalFieldTheory.DiscreteValuationField.finite_principalUnits_nthPowerKernel _root_.LocalFieldTheory.DiscreteValuationField.finite_residueRootsOfUnityGroup _root_.LocalFieldTheory.DiscreteValuationField.finite_valuationSubringUnits_nthPowerKernel _root_.LocalFieldTheory.DiscreteValuationField.finite_valuationSubringUnits_nthPowerQuotient _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.LubinTate.standardLubinTateLevelCompleteDVF_hasExtensionInstance _root_.LubinTate.standardLubinTateLevelField_galFinite _root_.LubinTate.standardLubinTateLevelField_isAbelianGalois _root_.LubinTate.standardLubinTateLevelField_isMulCommutative _root_.LubinTate.standardLubinTateUnitParameter_commGroup _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.boundedRealFields_finite _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.labelPrime_fact _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RamificationTheory.HilbertRamification.Higher.lowerRamificationGroup.instNormal _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionResidueField.instField _root_.RamificationTheory.HilbertRamification.ValuationSubring.selectedResidueField.instAlgebra _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.LocalClassFieldTheory.comparisonIntegerRingIsIntegralClosure _root_.LocalClassFieldTheory.normalizationIntegerRingIsIntegralClosure _root_.RamificationTheory.HilbertRamification.CompleteDVF.decompositionGroupMulSemiringAction _root_.RamificationTheory.HilbertRamification.CompleteDVF.decompositionGroupResidueFieldMulSemiringAction _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.chosenFinitePlaceCompletionAlgebra _root_.chosenFinitePlaceCompletionFiniteDimensional _root_.chosenFinitePlaceLocalizedFiniteDimensional _root_.chosenFinitePlaceLocalizedIntegerAlgebra _root_.chosenFinitePlaceLocalizedValuationHasExtension _root_.finiteLocalUnitsOpen _root_.infiniteAdeleRingT2Space _root_.relativeAdeleRingIntermediateAlgebra _root_.relativeAdeleRingTopIntermediateAlgebra _root_.scaledRelativeIntegerLatticeQuotientFinite
attribute [-simp] _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.IsDiscreteValuationRing.addVal_ringEquiv _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.EqualCharacteristicLaurent.coeffHom_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.EqualCharacteristicLaurent.powerSeriesEvalHom_C _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.EqualCharacteristicLaurent.powerSeriesEvalHom_X _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.EqualCharacteristicLaurent.powerSeriesEvalSubringHom_C _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.EqualCharacteristicLaurent.powerSeriesEvalSubringHom_X _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.iwasawaGlobalInverseLimitCarrier_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.iwasawaDegreeTerm_zero _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.iwasawaGn_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.iwasawaPartialProduct_zero_input _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.iwasawaSeedAtLevel_val _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.iwasawaSeedIdeal_val _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.iwasawaSeed_val _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitSuccQuotAddEquivResidue_iwasawaSeed _root_.LocalFieldTheory.DiscreteValuationField.LocalField.laurentSeriesEquivLaurentImageSubfield_apply_coe _root_.LocalFieldTheory.Padic.integerRingEquivPadicDVRValuationSubring_coe _root_.LocalFieldTheory.localIntegerValuationSubringEquiv_apply_coe _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.LocalFieldTheory.residueField_algebraMap_residue _root_.LubinTate.LubinTateSeries.standardLubinTateSeries_toPowerSeries _root_.LubinTate.SameUniformizer.coeff_recursiveIntertwiner _root_.LubinTate.SameUniformizer.constantCoeff_inVariable _root_.LubinTate.SameUniformizer.intertwinerApproximation_zero _root_.LubinTate.SameUniformizer.standardLubinTateEndomorphism_coeff_one _root_.LubinTate.padicValuationSubringToCompletedUnramifiedWittRing_uniformizer _root_.LubinTate.standardLubinTateBaseUniformizerUnit_coe _root_.LubinTate.standardLubinTateChangedUniformizerUnit_coe _root_.LubinTate.standardLubinTateEndomorphismEvalAt_one _root_.LubinTate.standardLubinTateEndomorphismEvalAt_zero _root_.LubinTate.standardLubinTateEndomorphismValue_one _root_.LubinTate.standardLubinTateEndomorphismValue_zero _root_.LubinTate.standardLubinTateLevelCoefficientHom_apply _root_.LubinTate.standardLubinTateLevelGenerator_coe _root_.LubinTate.standardLubinTateLevelPowerSeriesEval_C _root_.LubinTate.standardLubinTateLevelPowerSeriesEval_X _root_.LubinTate.standardLubinTateLevelPowerSeriesEval_coe _root_.LubinTate.standardLubinTatePolynomialIterateOverSeparableClosure_eval _root_.LubinTate.standardLubinTatePolynomialIterate_derivative_eval_zero _root_.LubinTate.standardLubinTatePolynomialIterate_eval_zero _root_.LubinTate.standardLubinTatePolynomialIterate_zero _root_.LubinTate.standardLubinTatePolynomial_derivative_eval_zero _root_.LubinTate.standardLubinTatePolynomial_eval _root_.LubinTate.standardLubinTatePolynomial_toPowerSeries _root_.LubinTate.standardLubinTatePolynomial_toPowerSeries_eq_series _root_.LubinTate.standardLubinTatePrimitiveLevelAction_coe _root_.LubinTate.standardLubinTatePrimitivePointIntegerAction_one _root_.LubinTate.standardLubinTatePrimitivePointInteger_coe _root_.LubinTate.standardLubinTatePrimitivePointIterateInteger_zero _root_.LubinTate.standardLubinTatePrimitivePolynomialOverField_coeff_zero _root_.LubinTate.standardLubinTatePrimitivePolynomial_coeff_zero _root_.LubinTate.standardLubinTatePrimitiveRootAction_one _root_.LubinTate.standardLubinTateUnitFactorFieldUnit_coe _root_.LubinTate.standardLubinTateUnitParameterAlgEquiv_apply_gen _root_.LubinTate.standardLubinTateUnitParameterAlgHom_apply_gen _root_.LubinTate.standardLubinTateUnitParameterChosenRepresentative_spec _root_.LubinTate.standardLubinTateUnitParameterEquivGal_apply _root_.LubinTate.standardLubinTateUnitParameterEquivGal_inv_class_apply_gen _root_.LubinTate.standardLubinTateUnitParameterLevelRoot_coe _root_.LubinTate.standardLubinTateUnitParameterLevelRoot_one _root_.LubinTate.standardLubinTateUnitParameterRoot_class _root_.LubinTate.standardLubinTateUnitParameterToGalHom_apply _root_.OAI.PrimeDegreePackets.ThetaConstruction.schwartzCM_apply _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteResidueActionOfHenselianDVF_apply _root_.RamificationTheory.HilbertRamification.CompleteDVF.decompositionResidueAction_algebraMap _root_.RamificationTheory.HilbertRamification.CompleteDVF.decompositionResidueAction_apply _root_.RamificationTheory.HilbertRamification.CompleteDVF.residueAction_apply _root_.RamificationTheory.HilbertRamification.Higher.dvfUniformizerQuotientUnit_mul_uniformizer _root_.RamificationTheory.HilbertRamification.Higher.dvfUniformizerRepresentativeHom_apply _root_.RamificationTheory.HilbertRamification.Higher.dvfValuationSubringUnitAut_apply _root_.RamificationTheory.HilbertRamification.Higher.intrinsicRamificationNumberOfUniqueExtension_one _root_.RamificationTheory.HilbertRamification.Higher.lowerRamificationGroup_neg_one _root_.RamificationTheory.HilbertRamification.Higher.mem_dvfHigherPrincipalUnitGroup_iff _root_.RamificationTheory.HilbertRamification.Higher.mem_lowerRamificationGroup_iff _root_.RamificationTheory.HilbertRamification.Higher.mem_valuationSubringDisplacementSubalgebraOfUniqueExtension_iff _root_.RamificationTheory.HilbertRamification.Higher.ramificationNumberDepthOfUniqueExtension_depth _root_.RamificationTheory.HilbertRamification.Higher.ramificationNumberOfUniqueExtension_one _root_.RamificationTheory.HilbertRamification.Higher.realRamificationIdeal_nat _root_.RamificationTheory.HilbertRamification.Higher.realRamificationIdeal_neg_one _root_.RamificationTheory.HilbertRamification.Higher.uniformizerGradedHom_mk _root_.RamificationTheory.HilbertRamification.Higher.valuationSubringAutOfUniqueExtension_apply_coe _root_.RamificationTheory.HilbertRamification.Higher.valuationSubringAutOfUniqueExtension_apply_inv_apply _root_.RamificationTheory.HilbertRamification.Higher.valuationSubringAutOfUniqueExtension_mul_apply _root_.RamificationTheory.HilbertRamification.Higher.valuationSubringAutOfUniqueExtension_one_apply _root_.RayClass.primesEquiv_val_eq_natGenerator _root_.LubinTate.standardLubinTateLevelAutomorphismIntegerRingEquiv_apply _root_.infinitePlace_mult_smul
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

/-!
# The integral lattice of a mixed-characteristic local field

This file identifies the integer ring of a mixed-characteristic local field
with the integral closure of the p-adic integers.  In particular it supplies
the finite free `Z_p` lattice of rank `[K : Q_p]` used in the proof of
the mixed-characteristic field-unit structure theorem.  The comparison is made for the canonical copy of `Q_p`
constructed in the local-field structure classification, not for a separately assumed scalar action.
-/

noncomputable section

universe u v

namespace LocalFieldTheory.DiscreteValuationField
namespace LocalField

open scoped WithZero nonZeroDivisors
open Module

variable {K : Type u} [Field K]

/-! ### Canonical mixed-characteristic scalar context -/

/-! ### the canonical `Z_p` integral basis -/

/--
Equips the target with its canonical `IsScalarTower` structure, namely `IsScalarTower
ℤ_[F.residueCharacteristic] ℚ_[F.residueCharacteristic] K`.
-/
instance mixedIntegralAlgebraContextQPadicTower
    (F : LocalField.{u, v} K) [CharZero K]
    [MixedIntegralAlgebraContext F] :
    IsScalarTower ℤ_[F.residueCharacteristic]
      ℚ_[F.residueCharacteristic] K :=
  IsScalarTower.of_algebraMap_eq (by intro z; rfl)

/--
Equips the target with its canonical `IsScalarTower` structure, namely `IsScalarTower
ℤ_[F.residueCharacteristic] F.toCompleteDVF.valuationSubring K`.
-/
instance mixedIntegralAlgebraContextValuationSubringTower
    (F : LocalField.{u, v} K) [CharZero K]
    [MixedIntegralAlgebraContext F] :
    IsScalarTower ℤ_[F.residueCharacteristic]
      F.toCompleteDVF.valuationSubring K :=
  F.padicIntValuationSubring_isScalarTower

/-- canonical integral-closure form: `O_K` is the integral closure of
`Z_p` in `K` for the canonical `Q_p`-algebra structure. -/
theorem valuationSubring_isIntegralClosure_over_padicInt
    (F : LocalField.{u, v} K) [CharZero K] :
    letI : MixedIntegralAlgebraContext F :=
      mixedIntegralAlgebraContext F
    IsIntegralClosure F.toCompleteDVF.valuationSubring
      ℤ_[F.residueCharacteristic] K := by
  let p : ℕ := F.residueCharacteristic
  let : MixedIntegralAlgebraContext F :=
    mixedIntegralAlgebraContext F
  let : Algebra.IsSeparable ℚ_[p] K := by infer_instance
  let hclosure : IsIntegralClosure F.toCompleteDVF.valuationSubring
      (Examples.Qp.padicCompleteDVF p).valuationSubring K :=
    _root_.ValuationTheory.DiscreteValuationField.ValuedExtension.target_valuationSubring_isIntegralClosure_of_finite_separable
      (Examples.Qp.padicCompleteDVF p) F.toCompleteDVF
  let e : ℤ_[p] ≃+* (Examples.Qp.padicCompleteDVF p).valuationSubring :=
    Examples.Qp.padicIntEquivValuationSubring p
  have hcompat :
      (algebraMap (Examples.Qp.padicCompleteDVF p).valuationSubring K).comp
          e.toRingHom =
        algebraMap ℤ_[p] K := by
    ext z
    rfl
  refine
    { algebraMap_injective := by
        intro a b hab
        exact Subtype.ext hab
      isIntegral_iff := ?_ }
  intro x
  exact (e.isIntegral_iff hcompat x).trans hclosure.isIntegral_iff

/-- The mixed-characteristic field-unit structure theorem, integral-basis finiteness: `O_K` is a finite
`Z_p`-module, with no separately assumed module structure. -/
theorem mixed_valuationSubring_moduleFinite
    (F : LocalField.{u, v} K) [CharZero K] :
    letI : MixedIntegralAlgebraContext F :=
      mixedIntegralAlgebraContext F
    Module.Finite ℤ_[F.residueCharacteristic]
      F.toCompleteDVF.valuationSubring := by
  let p : ℕ := F.residueCharacteristic
  let : MixedIntegralAlgebraContext F :=
    mixedIntegralAlgebraContext F
  let : IsIntegralClosure F.toCompleteDVF.valuationSubring ℤ_[p] K :=
    F.valuationSubring_isIntegralClosure_over_padicInt
  exact IsIntegralClosure.finite ℤ_[p] ℚ_[p] K
    F.toCompleteDVF.valuationSubring

/-- The mixed-characteristic field-unit structure theorem, integral-basis freeness. -/
theorem mixed_valuationSubring_moduleFree
    (F : LocalField.{u, v} K) [CharZero K] :
    letI : MixedIntegralAlgebraContext F :=
      mixedIntegralAlgebraContext F
    Module.Free ℤ_[F.residueCharacteristic]
      F.toCompleteDVF.valuationSubring := by
  let p : ℕ := F.residueCharacteristic
  let : MixedIntegralAlgebraContext F :=
    mixedIntegralAlgebraContext F
  let : IsIntegralClosure F.toCompleteDVF.valuationSubring ℤ_[p] K :=
    F.valuationSubring_isIntegralClosure_over_padicInt
  let : FaithfulSMul ℤ_[p] K :=
    FaithfulSMul.of_field_isFractionRing ℤ_[p] K ℚ_[p] K
  let : Module.IsTorsionFree ℤ_[p] K := inferInstance
  exact IsIntegralClosure.module_free
    ℤ_[p] ℚ_[p] K F.toCompleteDVF.valuationSubring

/-- The mixed-characteristic field-unit structure theorem, exact integral-basis rank. -/
theorem mixed_valuationSubring_finrank
    (F : LocalField.{u, v} K) [CharZero K] :
    letI : MixedIntegralAlgebraContext F :=
      mixedIntegralAlgebraContext F
    Module.finrank ℤ_[F.residueCharacteristic]
        F.toCompleteDVF.valuationSubring =
      Module.finrank ℚ_[F.residueCharacteristic] K := by
  let p : ℕ := F.residueCharacteristic
  let : MixedIntegralAlgebraContext F :=
    mixedIntegralAlgebraContext F
  let : IsIntegralClosure F.toCompleteDVF.valuationSubring ℤ_[p] K :=
    F.valuationSubring_isIntegralClosure_over_padicInt
  let : FaithfulSMul ℤ_[p] K :=
    FaithfulSMul.of_field_isFractionRing ℤ_[p] K ℚ_[p] K
  let : Module.IsTorsionFree ℤ_[p] K := inferInstance
  exact IsIntegralClosure.rank
    ℤ_[p] ℚ_[p] K F.toCompleteDVF.valuationSubring

/--
Equips the target with its canonical `Module.Finite` structure, namely `Module.Finite
ℤ_[F.residueCharacteristic] F.toCompleteDVF.valuationSubring`.
-/
noncomputable instance mixedIntegralLatticeContextModuleFinite
    (F : LocalField.{u, v} K) [CharZero K]
    [MixedIntegralLatticeContext F] :
    Module.Finite ℤ_[F.residueCharacteristic]
      F.toCompleteDVF.valuationSubring :=
  F.mixed_valuationSubring_moduleFinite

/--
Equips the target with its canonical `Module.Free` structure, namely `Module.Free
ℤ_[F.residueCharacteristic] F.toCompleteDVF.valuationSubring`.
-/
noncomputable instance mixedIntegralLatticeContextModuleFree
    (F : LocalField.{u, v} K) [CharZero K]
    [MixedIntegralLatticeContext F] :
    Module.Free ℤ_[F.residueCharacteristic]
      F.toCompleteDVF.valuationSubring :=
  F.mixed_valuationSubring_moduleFree

/-- A concrete integral basis indexed by the field degree `d = [K:Q_p]`. -/
noncomputable def mixed_integralBasis
    (F : LocalField.{u, v} K) [CharZero K] :
    letI : MixedIntegralLatticeContext F :=
      mixedIntegralLatticeContext F
    Basis (Fin (Module.finrank ℚ_[F.residueCharacteristic] K))
      ℤ_[F.residueCharacteristic] F.toCompleteDVF.valuationSubring := by
  let p : ℕ := F.residueCharacteristic
  letI : MixedIntegralLatticeContext F :=
    mixedIntegralLatticeContext F
  exact Module.finBasisOfFinrankEq ℤ_[p] F.toCompleteDVF.valuationSubring
    F.mixed_valuationSubring_finrank

/-- Every power of the maximal ideal is a finite `Z_p`-module. -/
theorem mixed_maximalIdealPow_moduleFinite
    (F : LocalField.{u, v} K) [CharZero K] (n : ℕ) :
    letI : MixedIntegralLatticeContext F :=
      mixedIntegralLatticeContext F
    Module.Finite ℤ_[F.residueCharacteristic]
      ((F.toCompleteDVF.maximalIdeal ^ n :
        Ideal F.toCompleteDVF.valuationSubring)) := by
  let p : ℕ := F.residueCharacteristic
  let : MixedIntegralLatticeContext F :=
    mixedIntegralLatticeContext F
  exact Module.Finite.of_injective
    (((F.toCompleteDVF.maximalIdeal ^ n :
      Ideal F.toCompleteDVF.valuationSubring).subtype).restrictScalars ℤ_[p])
    Subtype.val_injective

/-- Every maximal-ideal power is free over `Z_p`. -/
theorem mixed_maximalIdealPow_moduleFree
    (F : LocalField.{u, v} K) [CharZero K] (n : ℕ) :
    letI : MixedIntegralLatticeContext F :=
      mixedIntegralLatticeContext F
    Module.Free ℤ_[F.residueCharacteristic]
      ((F.toCompleteDVF.maximalIdeal ^ n :
        Ideal F.toCompleteDVF.valuationSubring)) := by
  let p : ℕ := F.residueCharacteristic
  let : MixedIntegralLatticeContext F :=
    mixedIntegralLatticeContext F
  let : Module.Finite ℤ_[p]
      ((F.toCompleteDVF.maximalIdeal ^ n :
        Ideal F.toCompleteDVF.valuationSubring)) :=
    F.mixed_maximalIdealPow_moduleFinite n
  let : Module.IsTorsionFree ℤ_[p] F.toCompleteDVF.valuationSubring :=
    inferInstance
  let : Module.IsTorsionFree ℤ_[p]
      ((F.toCompleteDVF.maximalIdeal ^ n :
        Ideal F.toCompleteDVF.valuationSubring)) := by
    refine Module.IsTorsionFree.of_smul_eq_zero ?_
    intro r x hrx
    have hrx' : r • (x : F.toCompleteDVF.valuationSubring) = 0 := by
      simpa using congrArg Subtype.val hrx
    rcases (smul_eq_zero.mp hrx') with hr | hx
    · exact Or.inl hr
    · exact Or.inr (Subtype.ext hx)
  exact Module.free_of_finite_type_torsion_free'

/-- The canonical maximal-ideal-power context. -/
theorem mixedMaximalIdealPowContext
    (F : LocalField.{u, v} K) [CharZero K] (n : ℕ) :
    letI : MixedIntegralLatticeContext F :=
      mixedIntegralLatticeContext F
    MixedMaximalIdealPowContext F n := by
  let : MixedIntegralLatticeContext F :=
    mixedIntegralLatticeContext F
  exact
    ⟨F.mixed_maximalIdealPow_moduleFinite n,
      F.mixed_maximalIdealPow_moduleFree n⟩

/-- A nonzero maximal-ideal power has the same `Z_p` rank as `O_K`, hence
rank exactly `[K:Q_p]`. -/
theorem mixed_maximalIdealPow_finrank
    (F : LocalField.{u, v} K) [CharZero K] (n : ℕ) :
    letI : MixedIntegralLatticeContext F :=
      mixedIntegralLatticeContext F
    letI : MixedMaximalIdealPowContext F n :=
      mixedMaximalIdealPowContext F n
    Module.finrank ℤ_[F.residueCharacteristic]
        ((F.toCompleteDVF.maximalIdeal ^ n :
          Ideal F.toCompleteDVF.valuationSubring)) =
      Module.finrank ℚ_[F.residueCharacteristic] K := by
  let p : ℕ := F.residueCharacteristic
  let : MixedIntegralLatticeContext F :=
    mixedIntegralLatticeContext F
  let : MixedMaximalIdealPowContext F n :=
    mixedMaximalIdealPowContext F n
  calc
    Module.finrank ℤ_[p]
        ((F.toCompleteDVF.maximalIdeal ^ n :
          Ideal F.toCompleteDVF.valuationSubring)) =
        Module.finrank ℤ_[p] F.toCompleteDVF.valuationSubring := by
          exact Ideal.finrank_eq_finrank
            F.mixed_integralBasis
            (F.toCompleteDVF.maximalIdeal ^ n)
            (pow_ne_zero n F.toCompleteDVF.maximalIdeal_ne_bot)
    _ = Module.finrank ℚ_[p] K :=
      F.mixed_valuationSubring_finrank

/-- Coordinate form for a deep additive ideal, the source side of
the deep exponential–logarithm equivalence. -/
noncomputable def mixed_maximalIdealPowLinearEquivPi
    (F : LocalField.{u, v} K) [CharZero K] (n : ℕ) :
    letI : MixedIntegralLatticeContext F :=
      mixedIntegralLatticeContext F
    letI : MixedMaximalIdealPowContext F n :=
      mixedMaximalIdealPowContext F n
    ((F.toCompleteDVF.maximalIdeal ^ n :
        Ideal F.toCompleteDVF.valuationSubring))
      ≃ₗ[ℤ_[F.residueCharacteristic]]
        (Fin (Module.finrank ℚ_[F.residueCharacteristic] K) →
          ℤ_[F.residueCharacteristic]) := by
  let p : ℕ := F.residueCharacteristic
  letI : MixedIntegralLatticeContext F :=
    mixedIntegralLatticeContext F
  letI : MixedMaximalIdealPowContext F n :=
    mixedMaximalIdealPowContext F n
  exact
    (Module.finBasisOfFinrankEq ℤ_[p]
      ((F.toCompleteDVF.maximalIdeal ^ n :
        Ideal F.toCompleteDVF.valuationSubring))
      (F.mixed_maximalIdealPow_finrank n)).equivFun

/-! ### The canonical `Z_p` action on `U^r` -/

end LocalField
end LocalFieldTheory.DiscreteValuationField
end
end

section
-- module Solutions.OAIQ244_DUKE.LocalField_DiscreteValuationField_MixedCharacteristicStructure_DeepPrincipalUnits
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_isCompleteDiscrete _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.DiscreteNthRootsSubgroup.instCommGroupSubtypeUnitsMemSubgroup _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalClassFieldTheory.finiteGaloisLocalField_integerRing_moduleFinite _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.residueFieldZModAlgebra _root_.LocalFieldTheory.DiscreteValuationField.finite_principalUnits_nthPowerKernel _root_.LocalFieldTheory.DiscreteValuationField.finite_residueRootsOfUnityGroup _root_.LocalFieldTheory.DiscreteValuationField.finite_valuationSubringUnits_nthPowerKernel _root_.LocalFieldTheory.DiscreteValuationField.finite_valuationSubringUnits_nthPowerQuotient _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.LubinTate.standardLubinTateLevelCompleteDVF_hasExtensionInstance _root_.LubinTate.standardLubinTateLevelField_galFinite _root_.LubinTate.standardLubinTateLevelField_isAbelianGalois _root_.LubinTate.standardLubinTateLevelField_isMulCommutative _root_.LubinTate.standardLubinTateUnitParameter_commGroup _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.labelPrime_fact _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RamificationTheory.HilbertRamification.Higher.lowerRamificationGroup.instNormal _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionFixedSubring.instIsLocalRing _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionResidueField.instField _root_.RamificationTheory.HilbertRamification.ValuationSubring.selectedResidueField.instAlgebra _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.CyclicCohomology.binaryCoefficientFamilyCommGroup _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.LocalClassFieldTheory.comparisonIntegerRingIsIntegralClosure _root_.LocalClassFieldTheory.normalizationIntegerRingIsIntegralClosure _root_.RamificationTheory.HilbertRamification.CompleteDVF.decompositionGroupMulSemiringAction _root_.RamificationTheory.HilbertRamification.CompleteDVF.decompositionGroupResidueFieldMulSemiringAction _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.chosenFinitePlaceCompletionAlgebra _root_.finiteLocalUnitsOpen _root_.infiniteAdeleRingT2Space _root_.relativeAdeleRingIntermediateAlgebra _root_.relativeAdeleRingTopIntermediateAlgebra _root_.relativeUnrestrictedSPlaceFactorCommGroup
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

/-!
# Deep principal units in mixed characteristic

This module equips the canonical `Z_p` lattice with the normalized valuation
topology and transports integral-basis coordinates through the deep
exponential--logarithm equivalence.
-/

noncomputable section

universe u v

namespace LocalFieldTheory.DiscreteValuationField
namespace LocalField

open scoped WithZero nonZeroDivisors
open Module

variable {K : Type u} [Field K]

/-! ### The canonical normalized-valuation model -/

/-! ### Continuity for the normalized valuation used by the deep exponential–logarithm equivalence -/

/-! ### the deep exponential–logarithm equivalence connected to the integral basis -/

/-- The deep principal-unit group is finite over `Z_p`; via logarithm it is
finite free of the same rank as `O_K`. -/
theorem mixed_deepPrincipalUnit_moduleFinite
    (v : _root_.Valuation K (WithZero (Multiplicative ℤ)))
    [ValuationTheory.DiscreteValuationField.Valuation.IsCompleteDiscrete v]
    [Finite (IsLocalRing.ResidueField v.valuationSubring)] [CharZero K]
    (hv : Function.Surjective v)
    (n : ℕ)
    (hlevel :
      (ramificationIndexOfWithZeroValuation v : ℚ) /
          (((ofWithZeroValuation v).residueCharacteristic : ℚ) - 1) <
        (n : ℚ)) :
    let F : LocalField.{u, 0} K := ofWithZeroValuation v
    let hn : 1 ≤ n := mixed_one_le_of_log_level v n hlevel
    letI : MixedWithZeroValuationContext v :=
      mixedWithZeroValuationContext v
    letI : Valued K (WithZero (Multiplicative ℤ)) := Valued.mk' v
    letI : Module ℤ_[F.residueCharacteristic]
        (Additive (LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup (F.toCompleteDVF) n)) :=
      F.higherPrincipalUnitPadicModule hn
    Module.Finite ℤ_[F.residueCharacteristic]
      (Additive (LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup (F.toCompleteDVF) n)) := by
  let F : LocalField.{u, 0} K := ofWithZeroValuation v
  let hn : 1 ≤ n := mixed_one_le_of_log_level v n hlevel
  let : MixedWithZeroValuationContext v :=
    mixedWithZeroValuationContext v
  let : Valued K (WithZero (Multiplicative ℤ)) := Valued.mk' v
  let : Module ℤ_[F.residueCharacteristic]
      (Additive (LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup (F.toCompleteDVF) n)) :=
    F.higherPrincipalUnitPadicModule hn
  let : Module.Finite ℤ_[F.residueCharacteristic]
      ((F.toCompleteDVF.maximalIdeal ^ n :
        Ideal F.toCompleteDVF.valuationSubring)) :=
    F.mixed_maximalIdealPow_moduleFinite n
  exact Module.Finite.equiv
    (mixed_deepLogLinearEquiv
      v hv n hlevel).symm

/-- Integral-basis coordinates after logarithm give the algebraic coordinate isomorphism `U^n ≃ Z_p^d`. -/
noncomputable def mixed_deepPrincipalUnitLinearEquivPi
    (v : _root_.Valuation K (WithZero (Multiplicative ℤ)))
    [ValuationTheory.DiscreteValuationField.Valuation.IsCompleteDiscrete v]
    [Finite (IsLocalRing.ResidueField v.valuationSubring)] [CharZero K]
    (hv : Function.Surjective v)
    (n : ℕ)
    (hlevel :
      (ramificationIndexOfWithZeroValuation v : ℚ) /
          (((ofWithZeroValuation v).residueCharacteristic : ℚ) - 1) <
        (n : ℚ)) :
    let F : LocalField.{u, 0} K := ofWithZeroValuation v
    let hn : 1 ≤ n := mixed_one_le_of_log_level v n hlevel
    letI : MixedWithZeroValuationContext v :=
      mixedWithZeroValuationContext v
    letI : Valued K (WithZero (Multiplicative ℤ)) := Valued.mk' v
    letI : Module ℤ_[F.residueCharacteristic]
        (Additive (LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup (F.toCompleteDVF) n)) :=
      F.higherPrincipalUnitPadicModule hn
    Additive (LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup (F.toCompleteDVF) n) ≃ₗ[
        ℤ_[F.residueCharacteristic]]
      (Fin (Module.finrank ℚ_[F.residueCharacteristic] K) →
        ℤ_[F.residueCharacteristic]) := by
  let F : LocalField.{u, 0} K := ofWithZeroValuation v
  let hn : 1 ≤ n := mixed_one_le_of_log_level v n hlevel
  letI : MixedWithZeroValuationContext v :=
    mixedWithZeroValuationContext v
  letI : Valued K (WithZero (Multiplicative ℤ)) := Valued.mk' v
  letI : Module ℤ_[F.residueCharacteristic]
      (Additive (LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup (F.toCompleteDVF) n)) :=
    F.higherPrincipalUnitPadicModule hn
  exact
    (mixed_deepLogLinearEquiv
      v hv n hlevel).trans
        (F.mixed_maximalIdealPowLinearEquivPi n)

end LocalField
end LocalFieldTheory.DiscreteValuationField
end
end

section
-- module Solutions.OAIQ244_DUKE.LocalField_DiscreteValuationField_MixedCharacteristicStructure_Core
attribute [-instance] _root_.ClassFormation.DegreeData.FrobeniusFixedFieldTower.extensionNormal _root_.ClassFormation.DegreeData.GaloisSubextension.extensionSubgroup_normalInstance _root_.ClassFormation.DegreeData.finiteReciprocityNaturalityFiniteAbstractConjugate_normal _root_.ClassFormation.DegreeData.finiteReciprocityNaturalityFiniteResidueConjugate_normal _root_.ClassFormation.FiniteAbstractField.toFiniteResidueAbstractField_extensionNormal _root_.ClassFormation.FiniteCyclicSubextension.instNormalSubtypeMemSubgroupFieldExtensionSubgroupField _root_.ClassFormation.FiniteGaloisSubextension.abelianIntermediateField_normalInstance _root_.ClassFormation.FiniteGaloisSubextension.extensionSubgroup_normalInstance _root_.ClassFormation.FiniteGaloisSubextension.extensionSubgroup_over_intermediate_normalInstance _root_.ClassFormation.FiniteGaloisSubextension.intermediateField_normalInstance _root_.ClassFormation.FiniteIntermediateField.galoisRefinement_normal _root_.ClassFormation.FiniteUnramifiedCyclicExtension.instNormalSubtypeMemSubgroupFieldExtensionSubgroupField _root_.ClassFormation.conjugateExtension_normal _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_isCompleteDiscrete _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.infinitePlaceComplexificationOverfield_baseSmul _root_.GlobalClassFieldTheory.Reciprocity.infinitePlaceComplexificationOverfield_smul _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.HilbertRamification.Dedekind.inertiaSubgroupOfDecomposition_normal _root_.KummerTheory.DiscreteNthRootsSubgroup.instCommGroupSubtypeUnitsMemSubgroup _root_.KummerTheory.DiscreteNthRootsSubgroup.instTopologicalSpaceSubtypeUnitsMemSubgroup _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalClassFieldTheory.extensionSubgroupBase_normal _root_.LocalClassFieldTheory.finiteGaloisExtensionSubgroupOfEmbedding_normal _root_.LocalClassFieldTheory.finiteGaloisLocalField_integerRing_moduleFinite _root_.LocalClassFieldTheory.localDecompositionResidueFinite _root_.LocalClassFieldTheory.localDecompositionResidueFintype _root_.LocalClassFieldTheory.localSeparableValuationHasExtension _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.residueFieldZModAlgebra _root_.LocalFieldTheory.DiscreteValuationField.finite_principalUnits_nthPowerKernel _root_.LocalFieldTheory.DiscreteValuationField.finite_residueRootsOfUnityGroup _root_.LocalFieldTheory.DiscreteValuationField.finite_valuationSubringUnits_nthPowerKernel _root_.LocalFieldTheory.DiscreteValuationField.finite_valuationSubringUnits_nthPowerQuotient _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.LubinTate.standardLubinTateLevelCompleteDVF_hasExtensionInstance _root_.LubinTate.standardLubinTateLevelField_galFinite _root_.LubinTate.standardLubinTateLevelField_isAbelianGalois _root_.LubinTate.standardLubinTateLevelField_isMulCommutative _root_.LubinTate.standardLubinTateUnitParameter_commGroup _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.boundedRealFields_finite _root_.OAI.PrimeDegreePackets.instT2SpaceLocalAlgebra _root_.OAI.PrimeDegreePackets.instTopologicalSpaceLocalAlgebra _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.labelPrime_fact _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.OAI.PrimeDegreePackets.xT2Space _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RamificationTheory.HilbertRamification.Higher.lowerRamificationGroup.instNormal _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionFixedSubring.instIsLocalRing _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionResidueField.instField _root_.RamificationTheory.HilbertRamification.ValuationSubring.inertiaGroup_normal _root_.RamificationTheory.HilbertRamification.ValuationSubring.ramificationGroupInInertiaAut_normal _root_.RamificationTheory.HilbertRamification.ValuationSubring.selectedResidueField.instAlgebra _root_.RayClass.Modulus.congruenceSubgroup_normal _root_.RayClass.approximationCompletionTopologicalSpace _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.CyclicCohomology.binaryCoefficientFamilyCommGroup _root_.LocalClassFieldTheory.intrinsicAbsoluteGaloisT2 _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.LocalClassFieldTheory.comparisonIntegerRingIsIntegralClosure _root_.LocalClassFieldTheory.normalizationIntegerRingIsIntegralClosure _root_.RamificationTheory.HilbertRamification.CompleteDVF.decompositionGroupMulSemiringAction _root_.RamificationTheory.HilbertRamification.CompleteDVF.decompositionGroupResidueFieldMulSemiringAction _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.chosenFinitePlaceCompletionAlgebra _root_.finiteIdeleGroupT2Space _root_.finiteLocalUnitsOpen _root_.ideleGroupT2Space _root_.infiniteAdeleRingT2Space _root_.infiniteIdeleGroupT2Space _root_.relativeAdeleRingIntermediateAlgebra _root_.relativeAdeleRingTopIntermediateAlgebra _root_.relativeUnrestrictedSPlaceFactorCommGroup _root_.scaledRelativeIntegerLatticeQuotientFinite
attribute [-simp] _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.IsDiscreteValuationRing.addVal_ringEquiv _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.EqualCharacteristicLaurent.coeffHom_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.EqualCharacteristicLaurent.powerSeriesEvalHom_C _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.EqualCharacteristicLaurent.powerSeriesEvalHom_X _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.EqualCharacteristicLaurent.powerSeriesEvalSubringHom_C _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.EqualCharacteristicLaurent.powerSeriesEvalSubringHom_X _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.iwasawaGlobalInverseLimitCarrier_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.iwasawaDegreeTerm_zero _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.iwasawaGn_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.iwasawaPartialProduct_zero_input _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.iwasawaSeedAtLevel_val _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.iwasawaSeedIdeal_val _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.iwasawaSeed_val _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitSuccQuotAddEquivResidue_iwasawaSeed _root_.LocalFieldTheory.DiscreteValuationField.LocalField.laurentSeriesEquivLaurentImageSubfield_apply_coe _root_.LocalFieldTheory.Padic.integerRingEquivPadicDVRValuationSubring_coe _root_.LocalFieldTheory.localIntegerValuationSubringEquiv_apply_coe _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.LocalFieldTheory.residueField_algebraMap_residue _root_.LubinTate.LubinTateSeries.standardLubinTateSeries_toPowerSeries _root_.LubinTate.SameUniformizer.coeff_recursiveIntertwiner _root_.LubinTate.SameUniformizer.constantCoeff_inVariable _root_.LubinTate.SameUniformizer.intertwinerApproximation_zero _root_.LubinTate.SameUniformizer.standardLubinTateEndomorphism_coeff_one _root_.LubinTate.padicValuationSubringToCompletedUnramifiedWittRing_uniformizer _root_.LubinTate.standardLubinTateBaseUniformizerUnit_coe _root_.LubinTate.standardLubinTateChangedUniformizerUnit_coe _root_.LubinTate.standardLubinTateEndomorphismEvalAt_one _root_.LubinTate.standardLubinTateEndomorphismEvalAt_zero _root_.LubinTate.standardLubinTateEndomorphismValue_one _root_.LubinTate.standardLubinTateEndomorphismValue_zero _root_.LubinTate.standardLubinTateLevelCoefficientHom_apply _root_.LubinTate.standardLubinTateLevelGenerator_coe _root_.LubinTate.standardLubinTateLevelPowerSeriesEval_C _root_.LubinTate.standardLubinTateLevelPowerSeriesEval_X _root_.LubinTate.standardLubinTateLevelPowerSeriesEval_coe _root_.LubinTate.standardLubinTatePolynomialIterateOverSeparableClosure_eval _root_.LubinTate.standardLubinTatePolynomialIterate_derivative_eval_zero _root_.LubinTate.standardLubinTatePolynomialIterate_eval_zero _root_.LubinTate.standardLubinTatePolynomialIterate_zero _root_.LubinTate.standardLubinTatePolynomial_derivative_eval_zero _root_.LubinTate.standardLubinTatePolynomial_eval _root_.LubinTate.standardLubinTatePolynomial_toPowerSeries _root_.LubinTate.standardLubinTatePolynomial_toPowerSeries_eq_series _root_.LubinTate.standardLubinTatePrimitiveLevelAction_coe _root_.LubinTate.standardLubinTatePrimitivePointIntegerAction_one _root_.LubinTate.standardLubinTatePrimitivePointInteger_coe _root_.LubinTate.standardLubinTatePrimitivePointIterateInteger_zero _root_.LubinTate.standardLubinTatePrimitivePolynomialOverField_coeff_zero _root_.LubinTate.standardLubinTatePrimitivePolynomial_coeff_zero _root_.LubinTate.standardLubinTatePrimitiveRootAction_one _root_.LubinTate.standardLubinTateUnitFactorFieldUnit_coe _root_.LubinTate.standardLubinTateUnitParameterAlgEquiv_apply_gen _root_.LubinTate.standardLubinTateUnitParameterAlgHom_apply_gen _root_.LubinTate.standardLubinTateUnitParameterChosenRepresentative_spec _root_.LubinTate.standardLubinTateUnitParameterEquivGal_apply _root_.LubinTate.standardLubinTateUnitParameterEquivGal_inv_class_apply_gen _root_.LubinTate.standardLubinTateUnitParameterLevelRoot_coe _root_.LubinTate.standardLubinTateUnitParameterLevelRoot_one _root_.LubinTate.standardLubinTateUnitParameterRoot_class _root_.LubinTate.standardLubinTateUnitParameterToGalHom_apply _root_.OAI.PrimeDegreePackets.ThetaConstruction.schwartzCM_apply _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteResidueActionOfHenselianDVF_apply _root_.RamificationTheory.HilbertRamification.CompleteDVF.decompositionResidueAction_algebraMap _root_.RamificationTheory.HilbertRamification.CompleteDVF.decompositionResidueAction_apply _root_.RamificationTheory.HilbertRamification.CompleteDVF.galEquivDecompositionGroup_coe _root_.RamificationTheory.HilbertRamification.CompleteDVF.residueAction_apply _root_.RamificationTheory.HilbertRamification.Higher.dvfUniformizerQuotientUnit_mul_uniformizer _root_.RamificationTheory.HilbertRamification.Higher.dvfUniformizerRepresentativeHom_apply _root_.RamificationTheory.HilbertRamification.Higher.dvfValuationSubringUnitAut_apply _root_.RamificationTheory.HilbertRamification.Higher.intrinsicRamificationNumberOfUniqueExtension_one _root_.RamificationTheory.HilbertRamification.Higher.lowerRamificationGroup_neg_one _root_.RamificationTheory.HilbertRamification.Higher.mem_dvfHigherPrincipalUnitGroup_iff _root_.RamificationTheory.HilbertRamification.Higher.mem_lowerRamificationGroup_iff _root_.RamificationTheory.HilbertRamification.Higher.mem_valuationSubringDisplacementSubalgebraOfUniqueExtension_iff _root_.RamificationTheory.HilbertRamification.Higher.ramificationNumberDepthOfUniqueExtension_depth _root_.RamificationTheory.HilbertRamification.Higher.ramificationNumberOfUniqueExtension_one _root_.RamificationTheory.HilbertRamification.Higher.realRamificationIdeal_nat _root_.RamificationTheory.HilbertRamification.Higher.realRamificationIdeal_neg_one _root_.RamificationTheory.HilbertRamification.Higher.uniformizerGradedHom_mk _root_.RamificationTheory.HilbertRamification.Higher.valuationSubringAutOfUniqueExtension_apply_coe _root_.RamificationTheory.HilbertRamification.Higher.valuationSubringAutOfUniqueExtension_apply_inv_apply _root_.RamificationTheory.HilbertRamification.Higher.valuationSubringAutOfUniqueExtension_mul_apply _root_.RamificationTheory.HilbertRamification.Higher.valuationSubringAutOfUniqueExtension_one_apply _root_.RayClass.primesEquiv_val_eq_natGenerator _root_.LubinTate.standardLubinTateLevelAutomorphismIntegerRingEquiv_apply _root_.infinitePlace_mult_smul
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

/-!
# First principal units in mixed characteristic

This module combines the deep free `Z_p` lattice with the finite quotient
exact sequence and packages the algebraic and topological structure of
the first principal-unit group.
-/

noncomputable section

universe u v

namespace LocalFieldTheory.DiscreteValuationField
namespace LocalField

open scoped WithZero nonZeroDivisors
open Module

variable {K : Type u} [Field K]

/-! ### The finite-level exact sequence and the first principal units -/

/-- The deep logarithmic lattice, viewed inside `U¹`, is finite free of the
field degree. -/
theorem mixed_principalUnitSuccKernelData
    (v : _root_.Valuation K (WithZero (Multiplicative ℤ)))
    [ValuationTheory.DiscreteValuationField.Valuation.IsCompleteDiscrete v]
    [Finite (IsLocalRing.ResidueField v.valuationSubring)] [CharZero K]
    (hv : Function.Surjective v)
    (n : ℕ)
    (hlevel :
      (ramificationIndexOfWithZeroValuation v : ℚ) /
          (((ofWithZeroValuation v).residueCharacteristic : ℚ) - 1) <
        (n : ℚ)) :
    let F : LocalField.{u, 0} K := ofWithZeroValuation v
    let p := F.residueCharacteristic
    let R := ℤ_[p]
    let M := Additive (LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup (F.toCompleteDVF) 1)
    letI : MixedQPadicContext F := mixedQPadicContext F
    letI : Module R M :=
      CompleteDVF.higherPrincipalUnitGroup.principalUnitPadicModule F
    let d := Module.finrank ℚ_[p] K
    FiniteFreeSubmoduleData R M
      (F.principalUnitSuccPadicSubmodule n) d := by
  let F : LocalField.{u, 0} K := ofWithZeroValuation v
  let p : ℕ := F.residueCharacteristic
  let R := ℤ_[p]
  let M := Additive (LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup (F.toCompleteDVF) 1)
  let : MixedQPadicContext F := mixedQPadicContext F
  let : Module R M :=
    CompleteDVF.higherPrincipalUnitGroup.principalUnitPadicModule F
  let d : ℕ := Module.finrank ℚ_[p] K
  let : Algebra R F.toCompleteDVF.valuationSubring :=
    F.padicIntValuationSubringAlgebra
  have hlevelSucc :
      (ramificationIndexOfWithZeroValuation v : ℚ) /
          ((F.residueCharacteristic : ℚ) - 1) < ((n + 1 : ℕ) : ℚ) :=
    lt_trans hlevel (by exact_mod_cast Nat.lt_succ_self n)
  let hr : 1 ≤ n + 1 := Nat.succ_le_succ (Nat.zero_le n)
  let deep := Additive
    (LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup (F.toCompleteDVF) (n + 1))
  let : Module R deep := F.higherPrincipalUnitPadicModule hr
  let : Module.Finite R deep :=
    mixed_deepPrincipalUnit_moduleFinite
      v hv (n + 1) hlevelSucc
  let eDeep : deep ≃ₗ[R] (Fin d → R) :=
    mixed_deepPrincipalUnitLinearEquivPi
      v hv (n + 1) hlevelSucc
  let higher := F.principalUnitSuccPadicSubmodule n
  let eHigher : deep ≃ₗ[R] higher :=
    F.higherPrincipalUnitLinearEquivPadicSubmodule hr
  let hHigherFinite : Module.Finite R higher :=
    F.higherPrincipalUnitPadicSubmodule_moduleFinite hr inferInstance
  let : Module.Free R deep := Module.Free.of_equiv eDeep.symm
  let hHigherFree : Module.Free R higher := Module.Free.of_equiv eHigher
  have hrankDeep : Module.finrank R deep = d := by
    simpa [d] using eDeep.finrank_eq
  have hrankHigher : Module.finrank R higher = d := by
    calc
      Module.finrank R higher = Module.finrank R deep := eHigher.finrank_eq.symm
      _ = d := hrankDeep
  exact
    { moduleFinite := hHigherFinite
      moduleFree := hHigherFree
      finrank := hrankHigher }

/-- The finite quotient map in the mixed-characteristic field-unit structure theorem, with the deep logarithmic
lattice identified as its finite free kernel. -/
noncomputable def mixed_firstPrincipalUnitFiniteQuotientSetup
    (v : _root_.Valuation K (WithZero (Multiplicative ℤ)))
    [ValuationTheory.DiscreteValuationField.Valuation.IsCompleteDiscrete v]
    [Finite (IsLocalRing.ResidueField v.valuationSubring)] [CharZero K]
    (hv : Function.Surjective v)
    (n : ℕ)
    (hlevel :
      (ramificationIndexOfWithZeroValuation v : ℚ) /
          (((ofWithZeroValuation v).residueCharacteristic : ℚ) - 1) <
        (n : ℚ)) :
    let F : LocalField.{u, 0} K := ofWithZeroValuation v
    let p := F.residueCharacteristic
    let R := ℤ_[p]
    let M := Additive (LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup (F.toCompleteDVF) 1)
    letI : MixedQPadicContext F := mixedQPadicContext F
    letI : Module R M :=
      CompleteDVF.higherPrincipalUnitGroup.principalUnitPadicModule F
    let d := Module.finrank ℚ_[p] K
    let q :=
      CompleteDVF.higherPrincipalUnitGroup.DiscretePrincipalUnitQuotient
        F.toCompleteDVF n
    letI : Module R q :=
      CompleteDVF.higherPrincipalUnitGroup.discretePrincipalUnitQuotientPadicModule F n
    FiniteQuotientSetup R M q d := by
  let F : LocalField.{u, 0} K := ofWithZeroValuation v
  let p : ℕ := F.residueCharacteristic
  let R := ℤ_[p]
  let M := Additive (LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup (F.toCompleteDVF) 1)
  letI : MixedQPadicContext F := mixedQPadicContext F
  letI : Module R M :=
    CompleteDVF.higherPrincipalUnitGroup.principalUnitPadicModule F
  let d : ℕ := Module.finrank ℚ_[p] K
  let higher := F.principalUnitSuccPadicSubmodule n
  let kernelData := mixed_principalUnitSuccKernelData
    v hv n hlevel
  let q :=
    CompleteDVF.higherPrincipalUnitGroup.DiscretePrincipalUnitQuotient
      F.toCompleteDVF n
  letI : Module R q :=
    CompleteDVF.higherPrincipalUnitGroup.discretePrincipalUnitQuotientPadicModule F n
  letI : Finite q := inferInstance
  letI : Module.Finite R q := Module.Finite.of_finite
  let projection : M →ₗ[R] q := F.principalUnitQuotientProjectionLinear n
  let U := LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.toPrincipalUnitFiltration
    F.toCompleteDVF
  let quotientKernel := (U.principalUnitSubgroup (n + 1)).subgroupOf
    (U.principalUnitSubgroup 1)
  have hsur : Function.Surjective projection := by
    intro y
    obtain ⟨x, hx⟩ :=
      QuotientGroup.mk'_surjective quotientKernel (Additive.toMul y.val)
    refine ⟨Additive.ofMul x, ?_⟩
    apply (CompleteDVF.higherPrincipalUnitGroup.DiscretePrincipalUnitQuotient.addEquiv
      F.toCompleteDVF n).injective
    apply Additive.toMul.injective
    exact hx
  let N := LinearMap.ker projection
  have hN : N = higher :=
    F.principalUnitQuotientProjectionLinear_ker n
  letI hNFinite : Module.Finite R N := by
    rw [hN]
    exact kernelData.moduleFinite
  letI hNFree : Module.Free R N := by
    rw [hN]
    exact kernelData.moduleFree
  have hrankN : Module.finrank R N = d := by
    rw [hN]
    exact kernelData.finrank
  have hqTorsion : Module.IsTorsion R q := by
    intro x
    exact F.discretePrincipalUnitQuotient_moduleIsTorsion n (x := x)
  exact
    { projection := projection
      projection_surjective := hsur
      kernelFinite := hNFinite
      kernelFree := hNFree
      kernelFinrank := hrankN
      quotientTorsion := hqTorsion }

/-- Algebraic data for the first principal units in the mixed-characteristic field-unit structure theorem.
The deep logarithmic lattice supplies the free kernel; the finite-level
principal-unit quotient detects all torsion. -/
noncomputable def chosenMixed_firstPrincipalUnitAlgebraicData
    (v : _root_.Valuation K (WithZero (Multiplicative ℤ)))
    [ValuationTheory.DiscreteValuationField.Valuation.IsCompleteDiscrete v]
    [Finite (IsLocalRing.ResidueField v.valuationSubring)] [CharZero K]
    (hv : Function.Surjective v)
    (n : ℕ)
    (hlevel :
      (ramificationIndexOfWithZeroValuation v : ℚ) /
          (((ofWithZeroValuation v).residueCharacteristic : ℚ) - 1) <
        (n : ℚ)) :
    let F : LocalField.{u, 0} K := ofWithZeroValuation v
    let p := F.residueCharacteristic
    let R := ℤ_[p]
    let M := Additive (LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup (F.toCompleteDVF) 1)
    letI : MixedQPadicContext F := mixedQPadicContext F
    letI : Module R M :=
      CompleteDVF.higherPrincipalUnitGroup.principalUnitPadicModule F
    let d := Module.finrank ℚ_[p] K
    FirstPrincipalUnitAlgebraicData R M p d := by
  let F : LocalField.{u, 0} K := ofWithZeroValuation v
  let p : ℕ := F.residueCharacteristic
  let R := ℤ_[p]
  let M := Additive (LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup (F.toCompleteDVF) 1)
  letI : MixedQPadicContext F := mixedQPadicContext F
  letI : Module R M :=
    CompleteDVF.higherPrincipalUnitGroup.principalUnitPadicModule F
  let d : ℕ := Module.finrank ℚ_[p] K
  let q :=
    CompleteDVF.higherPrincipalUnitGroup.DiscretePrincipalUnitQuotient
      F.toCompleteDVF n
  letI : Module R q :=
    CompleteDVF.higherPrincipalUnitGroup.discretePrincipalUnitQuotientPadicModule F n
  letI : Finite q := inferInstance
  letI : Module.Finite R q := Module.Finite.of_finite
  let setup :=
    mixed_firstPrincipalUnitFiniteQuotientSetup
      v hv n hlevel
  let exactData : FiniteRankTorsionData R M q d :=
    finite_rank_torsion_data_of_setup d setup
  letI : Module.Finite R M := exactData.moduleFinite
  let T := Submodule.torsion R M
  letI hTAddCommGroup : AddCommGroup T := Submodule.addCommGroup T
  letI hTAddGroup : AddGroup T := hTAddCommGroup.toAddGroup
  letI hTModule : Module R T := Submodule.module T
  letI : Finite T := exactData.finiteTorsion
  letI hqAddGroup : AddGroup q := inferInstance
  let U1 := LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup (F.toCompleteDVF) 1
  let valuationUnitsToFieldUnits :=
    _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.valuationSubringUnitsToFieldUnits F.toCompleteDVF
  let principalToField : U1 →* K :=
    (Units.coeHom K).comp
      (valuationUnitsToFieldUnits.comp U1.subtype)
  have hvaluationUnitsToFieldUnits :
      Function.Injective valuationUnitsToFieldUnits := by
    intro x y hxy
    apply Units.ext
    apply Subtype.ext
    have hxy' := congrArg (fun z : Kˣ => (z : K)) hxy
    simpa [valuationUnitsToFieldUnits] using hxy'
  have hprincipalToField : Function.Injective principalToField := by
    exact Units.val_injective.comp
      (hvaluationUnitsToFieldUnits.comp Subtype.val_injective)
  have hcyclic : IsAddCyclic T :=
    isAddCyclic_of_injective_multiplicative_map
      T.subtype.toAddMonoidHom principalToField
      T.subtype_injective hprincipalToField
  let tproj : T →ₗ[R] q := exactData.torsionProjection
  have hqP : IsPGroup p (Multiplicative q) :=
    F.discretePrincipalUnitQuotient_isPGroup n
  let hcardExists :=
    exists_card_eq_prime_power_of_injective_addMonoidHom
      tproj.toAddMonoidHom exactData.torsionProjection_injective hqP
  let a : ℕ := Classical.choose hcardExists
  have hcard : Nat.card T = p ^ a :=
    Classical.choose_spec hcardExists
  refine
    { a := a
      moduleFinite := exactData.moduleFinite
      finiteTorsion := exactData.finiteTorsion
      cyclicTorsion := hcyclic
      cardTorsion := hcard
      finrankFree := exactData.finrankFree }

/-- The mixed-characteristic field-unit structure theorem, principal-unit factor in its literal algebraic and
topological form.  The finite torsion is a cyclic `p`-group and the free
factor has rank `[K : Q_p]`. -/
noncomputable def mixed_firstPrincipalUnitStructure
    (v : _root_.Valuation K (WithZero (Multiplicative ℤ)))
    [ValuationTheory.DiscreteValuationField.Valuation.IsCompleteDiscrete v]
    [Finite (IsLocalRing.ResidueField v.valuationSubring)] [CharZero K]
    (hv : Function.Surjective v)
    (n : ℕ)
    (hlevel :
      (ramificationIndexOfWithZeroValuation v : ℚ) /
          (((ofWithZeroValuation v).residueCharacteristic : ℚ) - 1) <
        (n : ℚ)) :
    let F : LocalField.{u, 0} K := ofWithZeroValuation v
    letI : MixedWithZeroValuationContext v :=
      mixedWithZeroValuationContext v
    letI : Valued K (WithZero (Multiplicative ℤ)) := Valued.mk' v
    let d := Module.finrank ℚ_[F.residueCharacteristic] K
    Σ a : ℕ,
      Multiplicative
          (ZMod (F.residueCharacteristic ^ a) ×
            (Fin d → ℤ_[F.residueCharacteristic])) ≃ₜ*
        LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup (F.toCompleteDVF) 1 := by
  let F : LocalField.{u, 0} K := ofWithZeroValuation v
  let p : ℕ := F.residueCharacteristic
  let R := ℤ_[p]
  let M := Additive (LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup (F.toCompleteDVF) 1)
  letI : MixedWithZeroValuationContext v :=
    mixedWithZeroValuationContext v
  letI : Valued K (WithZero (Multiplicative ℤ)) := Valued.mk' v
  let d : ℕ := Module.finrank ℚ_[p] K
  let T := Submodule.torsion R M
  letI : AddCommGroup T := Submodule.addCommGroup T
  letI : Module R T := Submodule.module T
  let data :=
    chosenMixed_firstPrincipalUnitAlgebraicData
      v hv n hlevel
  letI : Module.Finite R M := data.moduleFinite
  letI : Finite T := data.finiteTorsion
  letI : ContinuousAdd M :=
    CompleteDVF.higherPrincipalUnitGroup.principalUnitPadicContinuousAddOfWithZeroValuation v
  letI : ContinuousSMul R M :=
    continuousSMul_padicInt_firstPrincipalUnit_ofWithZeroValuation v
  letI : CompactSpace M := Module.Finite.compactSpace R M
  letI : T2Space M :=
    T2Space.of_injective_continuous Additive.toMul.injective continuous_toMul
  let eAdd :=
    CompleteDVF.higherPrincipalUnitGroup.chosenPadicModuleContinuousAddEquivZModProdFinPi
      p M data.a d data.cyclicTorsion data.cardTorsion data.finrankFree
  exact ⟨data.a, continuousMulEquivOfAdditiveTarget eAdd⟩

/-- The mixed-characteristic field-unit structure theorem, principal-unit factor with the logarithmic depth
chosen internally.  Thus the statement retains only the hypotheses attached
to the local field and a normalized valuation. -/
noncomputable def chosenMixed_firstPrincipalUnitStructure_ofWithZeroValuation
    (v : _root_.Valuation K (WithZero (Multiplicative ℤ)))
    [ValuationTheory.DiscreteValuationField.Valuation.IsCompleteDiscrete v]
    [Finite (IsLocalRing.ResidueField v.valuationSubring)] [CharZero K]
    (hv : Function.Surjective v) :
    let F : LocalField.{u, 0} K := ofWithZeroValuation v
    letI : MixedWithZeroValuationContext v :=
      mixedWithZeroValuationContext v
    letI : Valued K (WithZero (Multiplicative ℤ)) := Valued.mk' v
    let d := Module.finrank ℚ_[F.residueCharacteristic] K
    Σ a : ℕ,
      Multiplicative
          (ZMod (F.residueCharacteristic ^ a) ×
            (Fin d → ℤ_[F.residueCharacteristic])) ≃ₜ*
        LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup (F.toCompleteDVF) 1 := by
  let F : LocalField.{u, 0} K := ofWithZeroValuation v
  let hex := exists_nat_gt
    ((ramificationIndexOfWithZeroValuation v : ℚ) /
      ((F.residueCharacteristic : ℚ) - 1))
  let n : ℕ := Classical.choose hex
  have hn := Classical.choose_spec hex
  exact mixed_firstPrincipalUnitStructure
    v hv n (by simpa [F] using hn)

end LocalField
end LocalFieldTheory.DiscreteValuationField
end
end

section
-- module Solutions.OAIQ244_DUKE.LocalField_DiscreteValuationField_FieldUnitPowerIndexFormulas
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 400000
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_isCompleteDiscrete _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.DiscreteNthRootsSubgroup.instCommGroupSubtypeUnitsMemSubgroup _root_.KummerTheory.DiscreteNthRootsSubgroup.instTopologicalSpaceSubtypeUnitsMemSubgroup _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalClassFieldTheory.finiteGaloisLocalField_integerRing_moduleFinite _root_.LocalClassFieldTheory.localDecompositionResidueFinite _root_.LocalClassFieldTheory.localDecompositionResidueFintype _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LubinTate.standardLubinTateLevelCompleteDVF_hasExtensionInstance _root_.LubinTate.standardLubinTateLevelField_galFinite _root_.LubinTate.standardLubinTateLevelField_isAbelianGalois _root_.LubinTate.standardLubinTateLevelField_isMulCommutative _root_.LubinTate.standardLubinTateUnitParameter_commGroup _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.boundedRealFields_finite _root_.OAI.PrimeDegreePackets.instTopologicalSpaceLocalAlgebra _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.labelPrime_fact _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RamificationTheory.HilbertRamification.Higher.lowerRamificationGroup.instNormal _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionFixedSubring.instIsLocalRing _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionResidueField.instField _root_.RamificationTheory.HilbertRamification.ValuationSubring.selectedResidueField.instAlgebra _root_.RayClass.approximationCompletionTopologicalSpace _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.CyclicCohomology.binaryCoefficientFamilyCommGroup _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.LocalClassFieldTheory.comparisonIntegerRingIsIntegralClosure _root_.LocalClassFieldTheory.normalizationIntegerRingIsIntegralClosure _root_.RamificationTheory.HilbertRamification.CompleteDVF.decompositionGroupMulSemiringAction _root_.RamificationTheory.HilbertRamification.CompleteDVF.decompositionGroupResidueFieldMulSemiringAction _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.chosenFinitePlaceCompletionAlgebra _root_.finiteLocalUnitsOpen _root_.infiniteAdeleRingT2Space _root_.relativeAdeleRingIntermediateAlgebra _root_.relativeAdeleRingTopIntermediateAlgebra _root_.relativeUnrestrictedSPlaceFactorCommGroup
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

/-!
# Power indices in local-field unit groups

The index formulas below use the actual principal-unit structures from
the field-unit structure theorem.  Both the natural-cardinality form and the literal rational
form involving the normalized local absolute value are recorded.
-/

noncomputable section

universe u

namespace LocalFieldTheory.DiscreteValuationField
namespace LocalField

variable {K : Type u} [Field K]

/-- The local-field power-index formula in mixed characteristic, in natural-cardinality form for
the full field-unit group. -/
theorem mixed_fieldIndex
    (v : _root_.Valuation K (WithZero (Multiplicative ℤ)))
    [ValuationTheory.DiscreteValuationField.Valuation.IsCompleteDiscrete v]
    [Finite (IsLocalRing.ResidueField v.valuationSubring)] [CharZero K]
    (hv : Function.Surjective v)
    {n : ℕ} [NeZero n]
    [Finite (Kˣ ⧸ (powMonoidHom n : Kˣ →* Kˣ).range)]
    [Finite
      ((CompleteDVF.higherPrincipalUnitGroup
        (ofWithZeroValuation v).toCompleteDVF) 1 ⧸
        (powMonoidHom n : ((CompleteDVF.higherPrincipalUnitGroup
            (ofWithZeroValuation v).toCompleteDVF) 1) →* ((CompleteDVF.higherPrincipalUnitGroup
            (ofWithZeroValuation v).toCompleteDVF) 1)).range)] :
    let F : LocalField.{u, 0} K := ofWithZeroValuation v
    letI : MixedWithZeroValuationContext v :=
      mixedWithZeroValuationContext v
    letI : Valued K (WithZero (Multiplicative ℤ)) := Valued.mk' v
    let d := Module.finrank ℚ_[F.residueCharacteristic] K
    Nat.card (Kˣ ⧸ (powMonoidHom n : Kˣ →* Kˣ).range) =
      n * (Nat.card ((powMonoidHom n : Kˣ →* Kˣ).ker) *
        F.residueCharacteristic ^
          (d * padicValNat F.residueCharacteristic n)) := by
  let F : LocalField.{u, 0} K := ofWithZeroValuation v
  let : MixedWithZeroValuationContext v :=
    mixedWithZeroValuationContext v
  let : Valued K (WithZero (Multiplicative ℤ)) := Valued.mk' v
  let d := Module.finrank ℚ_[F.residueCharacteristic] K
  let hex :=
    WithZeroValuation.exists_valuationSubring_valuation_eq_exp_neg_one_of_surjective
      v hv
  let π := Classical.choose hex
  have hπval : v (π : K) = WithZero.exp (-1 : ℤ) :=
    Classical.choose_spec hex
  have hπ : v.IsUniformizer (π : K) :=
    WithZeroValuation.isUniformizer_of_valuation_eq_exp_neg_one
      v (π : K) hπval
  obtain ⟨a, e⟩ :=
    chosenMixed_firstPrincipalUnitStructure_ofWithZeroValuation
      v hv
  exact
    card_fieldUnits_nthPowerQuotient_of_mixedPrincipalUnitStructure
      (p := F.residueCharacteristic) (F := F.toCompleteDVF) hπ
      (ZMod (F.residueCharacteristic ^ a)) d e.symm.toMulEquiv

end LocalField
end LocalFieldTheory.DiscreteValuationField
end
end

section
-- module Solutions.OAIQ244_DUKE.GlobalClassFieldTheory_ClassFieldAxiom_IdeleClassPowerLocalUnitQuotient_FinitePlacePowerIndex
attribute [-instance] _root_.ClassFormation.DegreeData.FiniteAbstractExtension.ramificationQuotientFinite _root_.ClassFormation.DegreeData.FiniteAbstractExtension.representedQuotientFinite _root_.ClassFormation.DegreeData.FiniteAbstractExtension.residueQuotientFinite _root_.ClassFormation.DegreeData.FiniteAmbientFrobeniusFixedFieldTower.ambientRepresentedQuotientFinite _root_.ClassFormation.DegreeData.FiniteResidueAbstractExtension.instFiniteQuotientSubtypeMemSubgroupFieldBaseExtensionSubgroupField _root_.ClassFormation.DegreeData.FiniteTower.baseQuotientFinite _root_.ClassFormation.DegreeData.FiniteTower.topQuotientFinite _root_.ClassFormation.DegreeData.FiniteTower.totalQuotientFinite _root_.ClassFormation.DegreeData.FrobeniusFixedFieldTower.baseAbsoluteFiniteInstance _root_.ClassFormation.DegreeData.FrobeniusFixedFieldTower.extensionFinite _root_.ClassFormation.DegreeData.FrobeniusFixedFieldTower.fieldAbsoluteFiniteInstance _root_.ClassFormation.DegreeData.FrobeniusPowerFixedFieldTower.baseRepresentedAbsoluteFinite _root_.ClassFormation.DegreeData.FrobeniusPowerFixedFieldTower.fieldRepresentedAbsoluteFinite _root_.ClassFormation.DegreeData.FrobeniusPowerFixedFieldTower.relativeRepresentedQuotientFinite _root_.ClassFormation.FiniteAbstractField.instFiniteQuotientSubtypeMemSubgroupBaseFieldExtensionSubgroupField _root_.ClassFormation.FiniteAbstractField.toFiniteResidueAbstractField_extensionFinite _root_.ClassFormation.FiniteAbstractFieldExtension.instFiniteQuotientSubtypeMemSubgroupFieldBaseExtensionSubgroupField _root_.ClassFormation.FiniteCyclicSubextension.instFiniteQuotientSubtypeMemSubgroupFieldExtensionSubgroupField _root_.ClassFormation.FiniteUnramifiedCyclicExtension.instFiniteQuotientSubtypeMemSubgroupBaseFieldExtensionSubgroupField _root_.ClassFormation.FiniteUnramifiedCyclicExtension.instFiniteQuotientSubtypeMemSubgroupFieldExtensionSubgroupField _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.DiscreteNthRootsSubgroup.instCommGroupSubtypeUnitsMemSubgroup _root_.KummerTheory.DiscreteNthRootsSubgroup.instTopologicalSpaceSubtypeUnitsMemSubgroup _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.KummerTheory.finite_finsupp_nsmulQuotient _root_.KummerTheory.finite_sUnit_nthPowerQuotient _root_.LocalClassFieldTheory.baseFixingExtensionQuotient_finite _root_.LocalClassFieldTheory.baseFixingExtensionQuotient_finite_of_isSeparable _root_.LocalClassFieldTheory.finiteGaloisExtensionQuotientOfEmbedding_finite _root_.LocalClassFieldTheory.finiteGaloisLocalField_integerRing_moduleFinite _root_.LocalClassFieldTheory.localDecompositionResidueFinite _root_.LocalClassFieldTheory.localSeparableValuationHasExtension _root_.LocalFieldTheory.localIntegerValuation_residueFinite _root_.LubinTate.standardLubinTateLevelCompleteDVF_hasExtensionInstance _root_.LubinTate.standardLubinTateLevelField_galFinite _root_.LubinTate.standardLubinTateLevelField_isAbelianGalois _root_.LubinTate.standardLubinTateLevelField_isMulCommutative _root_.LubinTate.standardLubinTateUnitParameter_commGroup _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.boundedRealFields_finite _root_.OAI.PrimeDegreePackets.instTopologicalSpaceLocalAlgebra _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_finite_residue _root_.OAI.PrimeDegreePackets.labelPrime_fact _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RamificationTheory.HilbertRamification.Higher.lowerRamificationGroup.instNormal _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionResidueField.instField _root_.RamificationTheory.HilbertRamification.ValuationSubring.selectedResidueField.instAlgebra _root_.RayClass.approximationCompletionTopologicalSpace _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.CyclicCohomology.binaryCoefficientFamilyCommGroup _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.LocalClassFieldTheory.comparisonIntegerRingIsIntegralClosure _root_.LocalClassFieldTheory.normalizationIntegerRingIsIntegralClosure _root_.RamificationTheory.HilbertRamification.CompleteDVF.decompositionGroupMulSemiringAction _root_.RamificationTheory.HilbertRamification.CompleteDVF.decompositionGroupResidueFieldMulSemiringAction _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.chosenFinitePlaceBaseValued _root_.chosenFinitePlaceCompletionAlgebra _root_.relativeAdeleRingIntermediateAlgebra _root_.relativeAdeleRingTopIntermediateAlgebra _root_.relativeUnrestrictedSPlaceFactorCommGroup
attribute [-simp] _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.IsDiscreteValuationRing.addVal_ringEquiv _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.LocalFieldTheory.residueField_algebraMap_residue _root_.OAI.PrimeDegreePackets.ThetaConstruction.schwartzCM_apply _root_.RayClass.primesEquiv_val_eq_natGenerator _root_.infinitePlace_mult_smul
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

/-!
# Finite-place power indices

This file supplies the completion instances and local cardinality formulas used
to evaluate finite-place factors in idele power quotients.
-/

open scoped NumberField Classical NNReal ValuativeRel TensorProduct
open NumberField IsDedekindDomain

noncomputable section

namespace GlobalClassFieldTheory.ClassFieldAxiom

variable {K : Type} [Field K] [NumberField K]

/-- The finite-place local power index in the integral form used before
applying the global product formula.  The two copies of `n` are
respectively the uniformizer direction and the `n`-th roots of unity
already contained in `K`. -/
theorem card_finitePlace_nthPowerQuotient
    (n : ℕ+)
    (hmu : (primitiveRoots (n : ℕ) K).Nonempty)
    (v₀ : HeightOneSpectrum (𝓞 K)) :
    let ν :
        Valuation (v₀.adicCompletion K)
          (WithZero (Multiplicative ℤ)) :=
      Valued.v
    let F :=
      LocalFieldTheory.DiscreteValuationField.LocalField.ofWithZeroValuation ν
    letI :
        LocalFieldTheory.DiscreteValuationField.LocalField.MixedWithZeroValuationContext
          ν :=
      LocalFieldTheory.DiscreteValuationField.LocalField.mixedWithZeroValuationContext ν
    letI :
        Valued (v₀.adicCompletion K)
          (WithZero (Multiplicative ℤ)) :=
      Valued.mk' ν
    let d :=
      Module.finrank ℚ_[F.residueCharacteristic]
        (v₀.adicCompletion K)
    Nat.card
        ((v₀.adicCompletion K)ˣ ⧸
          (powMonoidHom (n : ℕ) :
            (v₀.adicCompletion K)ˣ →*
              (v₀.adicCompletion K)ˣ).range) =
      (n : ℕ) *
        ((n : ℕ) *
          F.residueCharacteristic ^
            (d *
              padicValNat F.residueCharacteristic (n : ℕ))) := by
  let ν :
      Valuation (v₀.adicCompletion K)
        (WithZero (Multiplicative ℤ)) :=
    Valued.v
  let F :=
    LocalFieldTheory.DiscreteValuationField.LocalField.ofWithZeroValuation ν
  let : NeZero (n : ℕ) := ⟨n.ne_zero⟩
  have hν : Function.Surjective ν :=
    v₀.valuedAdicCompletion_surjective K
  let :
      LocalFieldTheory.DiscreteValuationField.LocalField.MixedWithZeroValuationContext
        ν :=
    LocalFieldTheory.DiscreteValuationField.LocalField.mixedWithZeroValuationContext ν
  let :
      Valued (v₀.adicCompletion K)
        (WithZero (Multiplicative ℤ)) :=
    Valued.mk' ν
  let d :=
    Module.finrank ℚ_[F.residueCharacteristic]
      (v₀.adicCompletion K)
  obtain ⟨a, e⟩ :=
    LocalFieldTheory.DiscreteValuationField.LocalField.chosenMixed_firstPrincipalUnitStructure_ofWithZeroValuation
      ν hν
  let U :=
    LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup
      F.toCompleteDVF 1
  let A :=
    ZMod (F.residueCharacteristic ^ a) ×
      (Fin d → ℤ_[F.residueCharacteristic])
  let : Finite
      (A ⧸ LocalFieldTheory.nsmulAddSubgroup A (n : ℕ)) := by
    infer_instance
  let emul : U ≃* Multiplicative A := by
    let direct :
        Valued (v₀.adicCompletion K)
          (WithZero (Multiplicative ℤ)) :=
      Valued.mk' ν
    letI : TopologicalSpace (v₀.adicCompletion K) :=
      direct.toTopologicalSpace
    exact e.symm.toMulEquiv
  let : Finite
      (U ⧸
        (powMonoidHom (n : ℕ) : U →* U).range) :=
    LocalFieldTheory.finite_nthPowerQuotient_of_mulEquiv
      U (Multiplicative A) (n : ℕ) emul
  let hex := F.toCompleteDVF.exists_uniformizer
  let π := Classical.choose hex
  have hπ :
      F.toCompleteDVF.valuation.IsUniformizer
        (π : v₀.adicCompletion K) :=
    Classical.choose_spec hex
  let : Finite
      ((v₀.adicCompletion K)ˣ ⧸
        (powMonoidHom (n : ℕ) :
          (v₀.adicCompletion K)ˣ →*
            (v₀.adicCompletion K)ˣ).range) :=
    LocalFieldTheory.DiscreteValuationField.finite_fieldUnits_nthPowerQuotient_of_finite_principalUnits
      F.toCompleteDVF hπ (n : ℕ)
  have hindex :=
    LocalFieldTheory.DiscreteValuationField.LocalField.mixed_fieldIndex
      ν hν (n := (n : ℕ))
  have hroots :
      Nat.card
          ((powMonoidHom (n : ℕ) :
            (v₀.adicCompletion K)ˣ →*
              (v₀.adicCompletion K)ˣ).ker) =
        (n : ℕ) := by
    rw [
      LocalFieldTheory.powMonoidHom_ker_units_eq_rootsOfUnity]
    obtain ⟨ζ, hζ⟩ := hmu
    have hζprim : IsPrimitiveRoot ζ (n : ℕ) :=
      (mem_primitiveRoots n.pos).mp hζ
    exact
      (hζprim.map_of_injective
        (algebraMap K (v₀.adicCompletion K)).injective).card_rootsOfUnity
  simpa only [hroots] using hindex

/-- The finite local power-index formula with the
residue-characteristic contribution packaged as
`finitePlaceNthPowerDefect`. -/
theorem card_finitePlace_nthPowerQuotient_eq_defect
    (n : ℕ+)
    (hmu : (primitiveRoots (n : ℕ) K).Nonempty)
    (v₀ : HeightOneSpectrum (𝓞 K)) :
    Nat.card
        ((v₀.adicCompletion K)ˣ ⧸
          (powMonoidHom (n : ℕ) :
            (v₀.adicCompletion K)ˣ →*
              (v₀.adicCompletion K)ˣ).range) =
      (n : ℕ) *
        ((n : ℕ) *
          finitePlaceNthPowerDefect (K := K) n v₀) := by
  simpa [finitePlaceNthPowerDefect] using
    card_finitePlace_nthPowerQuotient
      (K := K) n hmu v₀


end GlobalClassFieldTheory.ClassFieldAxiom
end
end

section
-- module Solutions.OAIQ244_DUKE.GlobalClassFieldTheory_ClassFieldAxiom_IdelePowerLocalUnitNormContainment
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 400000
attribute [-instance] _root_.GlobalClassFieldTheory.GlobalClassFields.ConductorialSubgroup.finiteIndex _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalClassFieldTheory.finiteGaloisLocalField_integerRing_moduleFinite _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.LocalClassFieldTheory.comparisonIntegerRingIsIntegralClosure _root_.LocalClassFieldTheory.normalizationIntegerRingIsIntegralClosure
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI
attribute [local instance] OAI.starSubalgebraCommCStarAlgebra

set_option autoImplicit false

/-!
# Norm containment for idele power-local-unit subgroups

This module packages the finite-place local norm conditions and proves the
global norm containment and principal-intersection identity used in the
idele-class norm-index argument.
-/

open scoped NumberField Classical NNReal IsMulCommutative
open NumberField IsDedekindDomain
open AlgebraicNumberTheory.Valuations
open HilbertRamification
open KummerTheory
open LocalFieldTheory

noncomputable section

namespace GlobalClassFieldTheory.ClassFieldAxiom

variable {K : Type*} [Field K] [NumberField K]

/-- The simultaneous local norm condition at every finite place. -/
def allFinitePlaceLocalNormCondition
    {K L : Type}
    [Field K] [NumberField K]
    [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L] :
    Subgroup (IdeleGroup K) :=
  ⨅ v : HeightOneSpectrum (𝓞 K),
    (_root_.chosenFinitePlaceLocalNormSubgroup
      (K := K) (L := L) v).comap
        (IdeleGroup.finiteComponent v)


end GlobalClassFieldTheory.ClassFieldAxiom
end
end

section
-- module Solutions.OAIQ244_DUKE.GlobalClassFieldTheory_ClassFieldAxiom_IdeleClassPowerLocalUnitQuotient_SupportedIdeleIndex
attribute [-instance] _root_.GlobalClassFieldTheory.GlobalClassFields.ConductorialSubgroup.finiteIndex _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalClassFieldTheory.finiteGaloisLocalField_integerRing_moduleFinite _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.CyclicCohomology.binaryCoefficientFamilyCommGroup _root_.LocalClassFieldTheory.comparisonIntegerRingIsIntegralClosure _root_.LocalClassFieldTheory.normalizationIntegerRingIsIntegralClosure _root_.chosenFinitePlaceCompletionAlgebra _root_.relativeUnrestrictedSPlaceFactorCommGroup
attribute [-simp] _root_.IdeleGroup.extension_finiteComponent _root_.IdeleGroup.extension_principalIdele _root_.IdeleGroup.extension_self _root_.IdeleGroup.finitePlaceIdele_finiteComponent_of_ne _root_.IdeleGroup.finitePlaceIdele_finiteComponent_same _root_.IdeleGroup.finitePlaceIdele_infiniteComponent _root_.IdeleGroup.infinitePlaceIdeleContinuous_apply _root_.IdeleGroup.infinitePlaceIdele_finiteComponent _root_.IdeleGroup.infinitePlaceIdele_infiniteComponent_of_ne _root_.IdeleGroup.infinitePlaceIdele_infiniteComponent_same _root_.IdeleGroup.norm_principalIdele _root_.IdeleGroup.norm_relativeIdeleBaseChangeMulEquiv _root_.IsDiscreteValuationRing.addVal_ringEquiv _root_.OAI.PrimeDegreePackets.ThetaConstruction.schwartzCM_apply _root_.RayClass.primesEquiv_val_eq_natGenerator _root_.RayClass.signToNarrow_mk _root_.IdeleGroup.idealClass_classRepresentative _root_.finiteIdeleOfSPlaceFactors_apply_mem _root_.finiteIdeleOfSPlaceFactors_apply_notMem _root_.ideleClassCongr_ideleClassNorm _root_.ideleClassCongr_mk _root_.ideleClassCongr_refl _root_.ideleClassExtension_mk _root_.ideleClassExtension_self _root_.ideleClassNorm_mk _root_.ideleCongr_finiteComponent _root_.ideleCongr_principalIdele _root_.ideleSupportedAtEquivSPlaceFactors_infinite _root_.ideleSupportedAtEquivSPlaceFactors_inside _root_.ideleSupportedAtEquivSPlaceFactors_outside_coe _root_.infinitePlace_mult_smul _root_.intermediateClassNormQuotientBaseChangeMulEquiv_mk _root_.ordinaryIdeleClassNormQuotientCongrOfAlgEquiv_mk _root_.ordinaryIdeleClassNorm_relativeIdeleClassBaseChange _root_.relativeFiniteIdeleMulEquiv_apply _root_.relativeFiniteIdeleToFiniteIdele_apply _root_.relativeIdeleBaseChangeMulEquiv_finite _root_.relativeIdeleBaseChangeMulEquiv_infinite _root_.relativeIdeleBaseChangeMulEquiv_principalIdele _root_.relativeIdeleClassBaseChangeMulEquiv_classInclusion _root_.relativeIdeleClassBaseChangeMulEquiv_congrOfAlgEquiv _root_.relativeIdeleClassBaseChangeMulEquiv_mk _root_.relativeIdeleClassCongrOfAlgEquiv_ideleClassNorm _root_.relativeIdeleClassCongr_ideleClassNorm _root_.relativeIdeleCongr_norm _root_.towerRelativeIdeleViaOrdinaryMulEquiv_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

/-!
# Supported idele power quotient

This file expresses the supported idele quotient as the product of its local
archimedean and finite-place power indices and evaluates its cardinality.
-/

open scoped NumberField Classical NNReal ValuativeRel TensorProduct
open NumberField IsDedekindDomain
open AlgebraicNumberTheory.Valuations
open KummerTheory
open LocalFieldTheory
open LocalFieldTheory.IsNonarchimedeanLocalField

noncomputable section

namespace GlobalClassFieldTheory.ClassFieldAxiom

variable {K : Type} [Field K] [NumberField K]

/-- The middle term in the supported exact sequence, evaluated as the
product of its actual local power indices.  The archimedean factors are
the sign indices, while each finite factor is the finite local
power index.  The following product-formula step evaluates the remaining
finite defect product. -/
theorem card_supportedIdeleQuotient_eq_localPowerIndexProduct
    (n : ℕ+)
    (hmu : (primitiveRoots (n : ℕ) K).Nonempty)
    (S T : Finset (HeightOneSpectrum (𝓞 K))) :
    Nat.card
        (IdeleGroup.supportedAt
              (K := K) (S ∪ T :
                Set (HeightOneSpectrum (𝓞 K))) ⧸
          supportedIdelePowerLocalUnitSubgroup (K := K) n S T) =
      (∏ w : InfinitePlace K,
          if w.IsReal ∧ Even (n : ℕ) then 2 else 1) *
        ∏ v : ↥S,
          (n : ℕ) *
            ((n : ℕ) *
              finitePlaceNthPowerDefect (K := K) n v.1) := by
  classical
  rw [
    card_supportedIdeleQuotient_eq_localPowerClasses
      (K := K) n S T,
    Nat.card_prod,
    Nat.card_pi,
    Nat.card_pi]
  congr 1
  · apply Finset.prod_congr rfl
    intro w _
    exact card_infinitePlace_nthPowerQuotient (K := K) n w
  · apply Finset.prod_congr rfl
    intro v _
    exact
      card_finitePlace_nthPowerQuotient_eq_defect
        (K := K) n hmu v.1

/-- The middle term of the supported exact sequence has cardinality
`n^(2s)`, where `s` is the number of infinite places plus the number of
finite places in `S`. -/
theorem card_supportedIdeleQuotient_eq_power_two_totalPlaceCard
    (n : ℕ+)
    (hmu : (primitiveRoots (n : ℕ) K).Nonempty)
    (S T : Finset (HeightOneSpectrum (𝓞 K)))
    (hS :
      ∀ v : HeightOneSpectrum (𝓞 K),
        v.asIdeal ∣
            Ideal.span {((n : ℕ) : 𝓞 K)} →
          v ∈ S) :
    Nat.card
        (IdeleGroup.supportedAt
              (K := K)
              (S ∪ T :
                Set (HeightOneSpectrum (𝓞 K))) ⧸
          supportedIdelePowerLocalUnitSubgroup
            (K := K) n S T) =
      (n : ℕ) ^
        (2 * totalPlaceCard (K := K) S) := by
  have hfinite :
      (∏ v : ↥S,
          (n : ℕ) *
            ((n : ℕ) *
              finitePlaceNthPowerDefect
                (K := K) n v.1)) =
        (n : ℕ) ^ (2 * S.card) *
          (n : ℕ) ^ Module.finrank ℚ K := by
    calc
      (∏ v : ↥S,
          (n : ℕ) *
            ((n : ℕ) *
              finitePlaceNthPowerDefect
                (K := K) n v.1)) =
          ∏ v : ↥S,
            (n : ℕ) ^ 2 *
              finitePlaceNthPowerDefect
                (K := K) n v.1 := by
        apply Finset.prod_congr rfl
        intro v _
        ring
      _ =
          (∏ _v : ↥S, (n : ℕ) ^ 2) *
            ∏ v : ↥S,
              finitePlaceNthPowerDefect
                (K := K) n v.1 := by
        rw [Finset.prod_mul_distrib]
      _ = _ := by
        rw [
          prod_finitePlaceNthPowerDefect
            (K := K) n S hS]
        simp [pow_mul]
  rw [
    card_supportedIdeleQuotient_eq_localPowerIndexProduct
      (K := K) n hmu S T,
    hfinite]
  calc
    ((∏ w : InfinitePlace K,
        if w.IsReal ∧ Even (n : ℕ) then 2 else 1) *
          ((n : ℕ) ^ (2 * S.card) *
            (n : ℕ) ^ Module.finrank ℚ K)) =
        ((∏ w : InfinitePlace K,
            if w.IsReal ∧ Even (n : ℕ) then 2 else 1) *
          (n : ℕ) ^ Module.finrank ℚ K) *
            (n : ℕ) ^ (2 * S.card) := by
      ac_rfl
    _ =
        (n : ℕ) ^
            (2 * Fintype.card (InfinitePlace K)) *
          (n : ℕ) ^ (2 * S.card) := by
      rw [
        prod_infinitePlace_nthPowerIndex_mul_natDegree
          (K := K) n hmu]
    _ =
        (n : ℕ) ^
          (2 * totalPlaceCard (K := K) S) := by
      rw [← pow_add]
      congr 1
      unfold totalPlaceCard
      omega


end GlobalClassFieldTheory.ClassFieldAxiom
end
end

section
-- module Solutions.OAIQ244_DUKE.GlobalClassFieldTheory_ClassFieldAxiom_IdeleClassPowerLocalUnitQuotient_SupportedPrincipalQuotient
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 400000
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.GlobalClassFields.ConductorialSubgroup.finiteIndex _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalClassFieldTheory.finiteGaloisLocalField_integerRing_moduleFinite _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.residueFieldZModAlgebra _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedIntegralAlgebraContextValuationSubringAlgebra _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LubinTate.compatibleGroupFamiliesCommGroup _root_.LubinTate.compatibleGroupFamiliesGroup _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.LocalClassFieldTheory.comparisonIntegerRingIsIntegralClosure _root_.LocalClassFieldTheory.normalizationIntegerRingIsIntegralClosure _root_.chosenFinitePlaceCompletionAlgebra
attribute [-simp] _root_.IdeleGroup.finitePlaceIdele_finiteComponent_of_ne _root_.IdeleGroup.finitePlaceIdele_finiteComponent_same _root_.IdeleGroup.finitePlaceIdele_infiniteComponent _root_.IdeleGroup.infinitePlaceIdeleContinuous_apply _root_.IdeleGroup.infinitePlaceIdele_finiteComponent _root_.IdeleGroup.infinitePlaceIdele_infiniteComponent_of_ne _root_.IdeleGroup.infinitePlaceIdele_infiniteComponent_same _root_.IsDiscreteValuationRing.addVal_ringEquiv _root_.KummerTheory.mem_sUnitFiniteKummerRadical_iff _root_.OAI.PrimeDegreePackets.ThetaConstruction.schwartzCM_apply _root_.RayClass.primesEquiv_val_eq_natGenerator _root_.RayClass.signToNarrow_mk
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI
attribute [local instance] OAI.starSubalgebraCommCStarAlgebra

set_option autoImplicit false

/-!
# Supported principal ideles and the idele-class quotient

This file identifies supported principal ideles with the corresponding
`S`-unit group and derives the exact-sequence cardinal identities.
-/

open scoped NumberField Classical NNReal ValuativeRel TensorProduct
open NumberField IsDedekindDomain
open AlgebraicNumberTheory.Valuations
open KummerTheory
open LocalFieldTheory
open LocalFieldTheory.IsNonarchimedeanLocalField

noncomputable section

namespace GlobalClassFieldTheory.ClassFieldAxiom

variable {K : Type} [Field K] [NumberField K]

/-- Principal ideles lying in `I_K^{S ∪ T}`, expressed as a subgroup of
the supported idele group. -/
def supportedPrincipalIdeleSubgroup
    (S T : Finset (HeightOneSpectrum (𝓞 K))) :
    Subgroup
      (IdeleGroup.supportedAt
        (K := K) (S ∪ T : Set (HeightOneSpectrum (𝓞 K)))) :=
  (IdeleGroup.principalSubgroup K).comap
    (IdeleGroup.supportedAt
      (K := K) (S ∪ T : Set (HeightOneSpectrum (𝓞 K)))).subtype

/-- The diagonal map identifies the `(S ∪ T)`-units with the principal
ideles lying in `I_K^{S ∪ T}`. -/
noncomputable def sUnitEquivSupportedPrincipalIdeleSubgroup
    (S T : Finset (HeightOneSpectrum (𝓞 K))) :
    SUnitGroup (K := K) (S ∪ T) ≃*
      supportedPrincipalIdeleSubgroup (K := K) S T := by
  let f :
      SUnitGroup (K := K) (S ∪ T) →*
        supportedPrincipalIdeleSubgroup (K := K) S T :=
    { toFun := fun x => by
        have hsupp :
            IdeleGroup.principalIdele K (x : Kˣ) ∈
              IdeleGroup.supportedAt
                (K := K)
                (S ∪ T : Set (HeightOneSpectrum (𝓞 K))) := by
          simpa only [Finset.coe_union] using
            (_root_.principalIdele_mem_supportedAt_iff_sUnit
              (L := K) (S ∪ T) (x : Kˣ)).2 x.property
        refine ⟨⟨IdeleGroup.principalIdele K (x : Kˣ), hsupp⟩, ?_⟩
        exact ⟨(x : Kˣ), rfl⟩
      map_one' := by
        apply Subtype.ext
        apply Subtype.ext
        simp
      map_mul' := by
        intro x y
        apply Subtype.ext
        apply Subtype.ext
        simp }
  apply MulEquiv.ofBijective f
  constructor
  · intro x y hxy
    apply Subtype.ext
    apply IdeleGroup.principalIdele_injective K
    have h :=
      congrArg
        (fun z :
          supportedPrincipalIdeleSubgroup (K := K) S T =>
            ((z :
                IdeleGroup.supportedAt
                  (K := K)
                  (S ∪ T :
                    Set (HeightOneSpectrum (𝓞 K)))) :
              IdeleGroup K))
        hxy
    exact h
  · intro y
    obtain ⟨x, hx⟩ := y.property
    have hsupp :
        IdeleGroup.principalIdele K x ∈
          IdeleGroup.supportedAt
            (K := K)
            (S ∪ T : Set (HeightOneSpectrum (𝓞 K))) := by
      rw [hx]
      exact y.1.property
    have hxS : x ∈ SUnitGroup (K := K) (S ∪ T) := by
      apply
        (_root_.principalIdele_mem_supportedAt_iff_sUnit
          (L := K) (S ∪ T) x).1
      simpa only [Finset.coe_union] using hsupp
    refine ⟨⟨x, hxS⟩, ?_⟩
    apply Subtype.ext
    apply Subtype.ext
    exact hx

/-- The supported-principal-idele equivalence has underlying idele equal
to the principal idele of the original `S`-unit. -/
@[simp]
theorem sUnitEquivSupportedPrincipalIdeleSubgroup_coe
    (S T : Finset (HeightOneSpectrum (𝓞 K)))
    (x : SUnitGroup (K := K) (S ∪ T)) :
    (((sUnitEquivSupportedPrincipalIdeleSubgroup
          (K := K) S T x :
        supportedPrincipalIdeleSubgroup (K := K) S T) :
      IdeleGroup.supportedAt
        (K := K)
        (S ∪ T : Set (HeightOneSpectrum (𝓞 K)))) :
      IdeleGroup K) =
        IdeleGroup.principalIdele K (x : Kˣ) :=
  rfl

/-- Under the preceding diagonal equivalence, this is the subgroup of
`(S ∪ T)`-units whose principal ideles belong to `h(S,T)`. -/
def sUnitPrincipalIdelePowerSubgroup
    (n : ℕ+)
    (S T : Finset (HeightOneSpectrum (𝓞 K))) :
    Subgroup (SUnitGroup (K := K) (S ∪ T)) :=
  (principalIdelePowerLocalUnitSubgroup (K := K) n S T).comap
    (SUnitGroup (K := K) (S ∪ T)).subtype

/-- The diagonal equivalence carries the principal part of `h(S,T)`
to the intersection of `h(S,T)` with the supported principal ideles. -/
theorem sUnitPrincipalIdelePowerSubgroup_map
    (n : ℕ+)
    (S T : Finset (HeightOneSpectrum (𝓞 K))) :
    (sUnitPrincipalIdelePowerSubgroup (K := K) n S T).map
        (sUnitEquivSupportedPrincipalIdeleSubgroup
          (K := K) S T).toMonoidHom =
      (supportedIdelePowerLocalUnitSubgroup
        (K := K) n S T).subgroupOf
          (supportedPrincipalIdeleSubgroup (K := K) S T) := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    have hy' :
      IdeleGroup.principalIdele K (y : Kˣ) ∈
        idelePowerLocalUnitSubgroup (K := K) n S T := by
      exact hy
    show
      (((sUnitEquivSupportedPrincipalIdeleSubgroup
            (K := K) S T y :
          supportedPrincipalIdeleSubgroup (K := K) S T) :
        IdeleGroup.supportedAt
          (K := K)
          (S ∪ T : Set (HeightOneSpectrum (𝓞 K)))) :
        IdeleGroup K) ∈
          idelePowerLocalUnitSubgroup (K := K) n S T
    rw [sUnitEquivSupportedPrincipalIdeleSubgroup_coe]
    exact hy'
  · intro hx
    let e :=
      sUnitEquivSupportedPrincipalIdeleSubgroup
        (K := K) S T
    refine ⟨e.symm x, ?_, e.apply_symm_apply x⟩
    have hx' :
        e (e.symm x) ∈
          (supportedIdelePowerLocalUnitSubgroup
            (K := K) n S T).subgroupOf
              (supportedPrincipalIdeleSubgroup (K := K) S T) := by
      rw [e.apply_symm_apply]
      exact hx
    change
      IdeleGroup.principalIdele K ((e.symm x : _) : Kˣ) ∈
        idelePowerLocalUnitSubgroup (K := K) n S T
    have hxIdele :
        (((e (e.symm x) :
              supportedPrincipalIdeleSubgroup (K := K) S T) :
            IdeleGroup.supportedAt
              (K := K)
              (S ∪ T : Set (HeightOneSpectrum (𝓞 K)))) :
          IdeleGroup K) ∈
            idelePowerLocalUnitSubgroup (K := K) n S T := by
      exact hx'
    rw [sUnitEquivSupportedPrincipalIdeleSubgroup_coe] at hxIdele
    exact hxIdele

/-- The left term in the supported exact sequence, expressed as the
actual quotient of `(S ∪ T)`-units satisfying the principal
`h(S,T)`-condition. -/
noncomputable def
    sUnitPrincipalIdelePowerQuotientEquivSupportedPrincipalQuotient
    (n : ℕ+)
    (S T : Finset (HeightOneSpectrum (𝓞 K))) :
    SUnitGroup (K := K) (S ∪ T) ⧸
        sUnitPrincipalIdelePowerSubgroup (K := K) n S T ≃*
      supportedPrincipalIdeleSubgroup (K := K) S T ⧸
        (supportedIdelePowerLocalUnitSubgroup
          (K := K) n S T).subgroupOf
            (supportedPrincipalIdeleSubgroup (K := K) S T) :=
  QuotientGroup.congr
    (sUnitPrincipalIdelePowerSubgroup (K := K) n S T)
    ((supportedIdelePowerLocalUnitSubgroup
      (K := K) n S T).subgroupOf
        (supportedPrincipalIdeleSubgroup (K := K) S T))
    (sUnitEquivSupportedPrincipalIdeleSubgroup
      (K := K) S T)
    (sUnitPrincipalIdelePowerSubgroup_map
      (K := K) n S T)

/-- Cardinal form of the diagonal identification of the left term in
the supported exact sequence. -/
theorem card_supportedPrincipalQuotient_eq_sUnitPrincipalQuotient
    (n : ℕ+)
    (S T : Finset (HeightOneSpectrum (𝓞 K))) :
    Nat.card
        (supportedPrincipalIdeleSubgroup (K := K) S T ⧸
          (supportedIdelePowerLocalUnitSubgroup
            (K := K) n S T).subgroupOf
              (supportedPrincipalIdeleSubgroup (K := K) S T)) =
      Nat.card
        (SUnitGroup (K := K) (S ∪ T) ⧸
          sUnitPrincipalIdelePowerSubgroup (K := K) n S T) :=
  Nat.card_congr
    (sUnitPrincipalIdelePowerQuotientEquivSupportedPrincipalQuotient
      (K := K) n S T).symm.toEquiv

/-- The denominator in the supported realization of
`C_K/C_K(S,T)`: it is generated by `h(S,T)` and the principal ideles
which are supported at `S ∪ T`. -/
def supportedIdeleClassPowerDenominator
    (n : ℕ+)
    (S T : Finset (HeightOneSpectrum (𝓞 K))) :
    Subgroup
      (IdeleGroup.supportedAt
        (K := K) (S ∪ T : Set (HeightOneSpectrum (𝓞 K)))) :=
  supportedIdelePowerLocalUnitSubgroup (K := K) n S T ⊔
    supportedPrincipalIdeleSubgroup (K := K) S T

section SupportedClassQuotient

local instance supportedClassQuotient_isMulCommutative :
    IsMulCommutative (IdeleClassGroup K) :=
  ⟨⟨fun a b => mul_comm a b⟩⟩

/-- The natural map from supported ideles to
`C_K/C_K(S,T)`. -/
def supportedIdeleToClassPowerQuotient
    (n : ℕ+)
    (S T : Finset (HeightOneSpectrum (𝓞 K))) :
    IdeleGroup.supportedAt
          (K := K) (S ∪ T : Set (HeightOneSpectrum (𝓞 K))) →*
      IdeleClassPowerLocalUnitQuotient (K := K) n S T :=
  (QuotientGroup.mk'
      (ideleClassPowerLocalUnitSubgroup (K := K) n S T)).comp
    ((QuotientGroup.mk'
        (IdeleGroup.principalSubgroup K)).comp
      (IdeleGroup.supportedAt
        (K := K) (S ∪ T : Set (HeightOneSpectrum (𝓞 K)))).subtype)

/-- The kernel of the supported class-quotient map is precisely the
subgroup generated by `h(S,T)` and the supported principal ideles. -/
theorem supportedIdeleToClassPowerQuotient_ker
    (n : ℕ+)
    (S T : Finset (HeightOneSpectrum (𝓞 K))) :
    (supportedIdeleToClassPowerQuotient
      (K := K) n S T).ker =
      supportedIdeleClassPowerDenominator (K := K) n S T := by
  let U :=
    IdeleGroup.supportedAt
      (K := K) (S ∪ T : Set (HeightOneSpectrum (𝓞 K)))
  let H :=
    supportedIdelePowerLocalUnitSubgroup (K := K) n S T
  let P := supportedPrincipalIdeleSubgroup (K := K) S T
  ext x
  rw [MonoidHom.mem_ker]
  change
    QuotientGroup.mk'
        (ideleClassPowerLocalUnitSubgroup (K := K) n S T)
        (QuotientGroup.mk'
          (IdeleGroup.principalSubgroup K) (x : IdeleGroup K)) = 1 ↔
      x ∈ H ⊔ P
  constructor
  · intro hx
    have hxClass :
        QuotientGroup.mk'
            (IdeleGroup.principalSubgroup K)
            (x : IdeleGroup K) ∈
          ideleClassPowerLocalUnitSubgroup (K := K) n S T :=
      (QuotientGroup.eq_one_iff _).mp hx
    rcases hxClass with ⟨h, hh, heq⟩
    have hhU :
        h ∈ U :=
      idelePowerLocalUnitSubgroup_le_supportedAt
        (K := K) n S T hh
    let hU : U := ⟨h, hhU⟩
    have hpDiv :
        (x : IdeleGroup K) / h ∈
          IdeleGroup.principalSubgroup K := by
      have hpInv :
          h / (x : IdeleGroup K) ∈
            IdeleGroup.principalSubgroup K :=
        (QuotientGroup.eq_iff_div_mem).mp heq
      simpa [div_eq_mul_inv, mul_comm] using
        (IdeleGroup.principalSubgroup K).inv_mem hpInv
    let pU : U := x / hU
    have hpU : pU ∈ P := by
      exact hpDiv
    apply Subgroup.mem_sup.mpr
    refine ⟨hU, hh, pU, hpU, ?_⟩
    simp [pU]
  · intro hx
    apply (QuotientGroup.eq_one_iff _).mpr
    rcases Subgroup.mem_sup.mp hx with
      ⟨h, hh, p, hp, rfl⟩
    have hhClass :
        QuotientGroup.mk'
            (IdeleGroup.principalSubgroup K)
            (h : IdeleGroup K) ∈
          ideleClassPowerLocalUnitSubgroup (K := K) n S T := by
      exact ⟨(h : IdeleGroup K), hh, rfl⟩
    have hpOne :
        QuotientGroup.mk'
            (IdeleGroup.principalSubgroup K)
            (p : IdeleGroup K) = 1 :=
      (QuotientGroup.eq_one_iff _).mpr hp
    have hmul :
        QuotientGroup.mk'
            (IdeleGroup.principalSubgroup K)
            ((h * p : U) : IdeleGroup K) =
          QuotientGroup.mk'
              (IdeleGroup.principalSubgroup K)
              (h : IdeleGroup K) *
            QuotientGroup.mk'
              (IdeleGroup.principalSubgroup K)
              (p : IdeleGroup K) := by
      simp
    rw [hmul, hpOne]
    exact
      (ideleClassPowerLocalUnitSubgroup (K := K) n S T).mul_mem
        hhClass
        (ideleClassPowerLocalUnitSubgroup (K := K) n S T).one_mem

/-- If `S ∪ T` is sufficiently large, every class modulo `C_K(S,T)`
has a supported representative. -/
theorem supportedIdeleToClassPowerQuotient_surjective
    (n : ℕ+)
    (S T : Finset (HeightOneSpectrum (𝓞 K)))
    (hLarge :
      IdeleGroup.supportedAt
            (K := K) (S ∪ T : Set (HeightOneSpectrum (𝓞 K))) ⊔
          IdeleGroup.principalSubgroup K =
        ⊤) :
    Function.Surjective
      (supportedIdeleToClassPowerQuotient
        (K := K) n S T) := by
  intro q
  refine q.inductionOn' ?_
  intro c
  refine c.inductionOn' ?_
  intro a
  have ha :
      a ∈
        IdeleGroup.supportedAt
              (K := K) (S ∪ T :
                Set (HeightOneSpectrum (𝓞 K))) ⊔
            IdeleGroup.principalSubgroup K := by
    rw [hLarge]
    exact Subgroup.mem_top a
  rcases Subgroup.mem_sup.mp ha with
    ⟨u, hu, p, hp, hup⟩
  refine ⟨⟨u, hu⟩, ?_⟩
  change
    QuotientGroup.mk'
        (ideleClassPowerLocalUnitSubgroup (K := K) n S T)
        (QuotientGroup.mk'
          (IdeleGroup.principalSubgroup K) u) =
      QuotientGroup.mk'
        (ideleClassPowerLocalUnitSubgroup (K := K) n S T)
        (QuotientGroup.mk'
          (IdeleGroup.principalSubgroup K) a)
  rw [← hup, map_mul]
  have hpOne :
      QuotientGroup.mk'
          (IdeleGroup.principalSubgroup K) p = 1 :=
    (QuotientGroup.eq_one_iff _).mpr hp
  rw [hpOne]
  simp

/-- Supported realization of the idele-class index quotient. -/
noncomputable def
    supportedIdeleClassPowerQuotientEquiv
    (n : ℕ+)
    (S T : Finset (HeightOneSpectrum (𝓞 K)))
    (hLarge :
      IdeleGroup.supportedAt
            (K := K) (S ∪ T : Set (HeightOneSpectrum (𝓞 K))) ⊔
          IdeleGroup.principalSubgroup K =
        ⊤) :
    IdeleGroup.supportedAt
          (K := K) (S ∪ T : Set (HeightOneSpectrum (𝓞 K))) ⧸
        supportedIdeleClassPowerDenominator (K := K) n S T ≃*
      IdeleClassPowerLocalUnitQuotient (K := K) n S T :=
  (QuotientGroup.quotientMulEquivOfEq
      (supportedIdeleToClassPowerQuotient_ker
        (K := K) n S T).symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective
      (supportedIdeleToClassPowerQuotient
        (K := K) n S T)
      (supportedIdeleToClassPowerQuotient_surjective
        (K := K) n S T hLarge))

/-- Cardinal form of the supported realization of
`[C_K:C_K(S,T)]`. -/
theorem card_ideleClassPowerLocalUnitQuotient_eq_supported
    (n : ℕ+)
    (S T : Finset (HeightOneSpectrum (𝓞 K)))
    (hLarge :
      IdeleGroup.supportedAt
            (K := K) (S ∪ T : Set (HeightOneSpectrum (𝓞 K))) ⊔
          IdeleGroup.principalSubgroup K =
        ⊤) :
    Nat.card
        (IdeleClassPowerLocalUnitQuotient (K := K) n S T) =
      Nat.card
        (IdeleGroup.supportedAt
              (K := K) (S ∪ T :
                Set (HeightOneSpectrum (𝓞 K))) ⧸
          supportedIdeleClassPowerDenominator (K := K) n S T) :=
  Nat.card_congr
    (supportedIdeleClassPowerQuotientEquiv
      (K := K) n S T hLarge).symm.toEquiv

end SupportedClassQuotient

/-- The cardinal identity furnished by the supported exact sequence:

`1 → (I_K^{S∪T} ∩ Kˣ)/(h(S,T) ∩ Kˣ)
   → I_K^{S∪T}/h(S,T)
   → I_K^{S∪T}Kˣ/h(S,T)Kˣ → 1`.

The first factor is written intrinsically as the relative index of
`h(S,T)` in the supported principal ideles. -/
theorem card_supportedPrincipalQuotient_mul_card_supportedClassQuotient
    (n : ℕ+)
    (S T : Finset (HeightOneSpectrum (𝓞 K))) :
    Nat.card
          (supportedPrincipalIdeleSubgroup (K := K) S T ⧸
            (supportedIdelePowerLocalUnitSubgroup (K := K) n S T).subgroupOf
              (supportedPrincipalIdeleSubgroup (K := K) S T)) *
        Nat.card
          (IdeleGroup.supportedAt
                (K := K) (S ∪ T :
                  Set (HeightOneSpectrum (𝓞 K))) ⧸
            supportedIdeleClassPowerDenominator (K := K) n S T) =
      Nat.card
        (IdeleGroup.supportedAt
              (K := K) (S ∪ T :
                Set (HeightOneSpectrum (𝓞 K))) ⧸
          supportedIdelePowerLocalUnitSubgroup (K := K) n S T) := by
  let U :=
    IdeleGroup.supportedAt
      (K := K) (S ∪ T : Set (HeightOneSpectrum (𝓞 K)))
  let H :=
    supportedIdelePowerLocalUnitSubgroup (K := K) n S T
  let P := supportedPrincipalIdeleSubgroup (K := K) S T
  change
    (H.subgroupOf P).index * (H ⊔ P).index = H.index
  have h :=
    Subgroup.relIndex_mul_index
      (H := H) (K := H ⊔ P) le_sup_left
  rw [Subgroup.relIndex_sup_left P H] at h
  exact h

/-- The exact-sequence cardinal identity with the right-hand term
identified with the actual idele-class quotient `C_K/C_K(S,T)`. -/
theorem card_supportedPrincipalQuotient_mul_card_ideleClassQuotient
    (n : ℕ+)
    (S T : Finset (HeightOneSpectrum (𝓞 K)))
    (hLarge :
      IdeleGroup.supportedAt
            (K := K) (S ∪ T : Set (HeightOneSpectrum (𝓞 K))) ⊔
          IdeleGroup.principalSubgroup K =
        ⊤) :
    Nat.card
          (supportedPrincipalIdeleSubgroup (K := K) S T ⧸
            (supportedIdelePowerLocalUnitSubgroup (K := K) n S T).subgroupOf
              (supportedPrincipalIdeleSubgroup (K := K) S T)) *
        Nat.card
          (IdeleClassPowerLocalUnitQuotient (K := K) n S T) =
      Nat.card
        (IdeleGroup.supportedAt
              (K := K) (S ∪ T :
                Set (HeightOneSpectrum (𝓞 K))) ⧸
          supportedIdelePowerLocalUnitSubgroup (K := K) n S T) := by
  rw [
    card_ideleClassPowerLocalUnitQuotient_eq_supported
      (K := K) n S T hLarge]
  exact
    card_supportedPrincipalQuotient_mul_card_supportedClassQuotient
      (K := K) n S T

/-- The exact-sequence identity in intrinsic `S`-unit notation. -/
theorem card_sUnitPrincipalQuotient_mul_card_ideleClassQuotient
    (n : ℕ+)
    (S T : Finset (HeightOneSpectrum (𝓞 K)))
    (hLarge :
      IdeleGroup.supportedAt
            (K := K) (S ∪ T : Set (HeightOneSpectrum (𝓞 K))) ⊔
          IdeleGroup.principalSubgroup K =
        ⊤) :
    Nat.card
          (SUnitGroup (K := K) (S ∪ T) ⧸
            sUnitPrincipalIdelePowerSubgroup (K := K) n S T) *
        Nat.card
          (IdeleClassPowerLocalUnitQuotient (K := K) n S T) =
      Nat.card
        (IdeleGroup.supportedAt
              (K := K) (S ∪ T :
                Set (HeightOneSpectrum (𝓞 K))) ⧸
          supportedIdelePowerLocalUnitSubgroup (K := K) n S T) := by
  rw [
    ← card_supportedPrincipalQuotient_eq_sUnitPrincipalQuotient
      (K := K) n S T]
  exact
    card_supportedPrincipalQuotient_mul_card_ideleClassQuotient
      (K := K) n S T hLarge


end GlobalClassFieldTheory.ClassFieldAxiom
end
end

section
-- module Solutions.OAIQ244_DUKE.GlobalClassFieldTheory_ClassFieldAxiom_IdeleClassPowerLocalUnitQuotient_PrimePowerKummerIndex
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 400000
attribute [-instance] _root_.GlobalClassFieldTheory.GlobalClassFields.ConductorialSubgroup.finiteIndex _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalClassFieldTheory.finiteGaloisLocalField_integerRing_moduleFinite _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.LocalClassFieldTheory.comparisonIntegerRingIsIntegralClosure _root_.LocalClassFieldTheory.normalizationIntegerRingIsIntegralClosure
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI
attribute [local instance] OAI.starSubalgebraCommCStarAlgebra

set_option autoImplicit false

/-!
# Prime-power Kummer norm index

This file combines the supported local index, principal-ideles exact sequence,
and norm containment to prove the prime-power Kummer norm-index theorem.
-/

open scoped NumberField Classical NNReal ValuativeRel TensorProduct
open NumberField IsDedekindDomain
open AlgebraicNumberTheory.Valuations
open KummerTheory
open LocalFieldTheory
open LocalFieldTheory.IsNonarchimedeanLocalField

noncomputable section

namespace GlobalClassFieldTheory.ClassFieldAxiom

variable {K : Type} [Field K] [NumberField K]

/-- The actual exact-sequence product after evaluating the middle local
power quotient as `n^(2s)`. -/
theorem card_sUnitPrincipalQuotient_mul_card_ideleClassQuotient_eq_power_two_totalPlaceCard
    (n : ℕ+)
    (hmu : (primitiveRoots (n : ℕ) K).Nonempty)
    (S T : Finset (HeightOneSpectrum (𝓞 K)))
    (hS :
      ∀ v : HeightOneSpectrum (𝓞 K),
        v.asIdeal ∣
            Ideal.span {((n : ℕ) : 𝓞 K)} →
          v ∈ S)
    (hLarge :
      IdeleGroup.supportedAt
            (K := K)
            (S ∪ T :
              Set (HeightOneSpectrum (𝓞 K))) ⊔
          IdeleGroup.principalSubgroup K =
        ⊤) :
    Nat.card
          (SUnitGroup (K := K) (S ∪ T) ⧸
            sUnitPrincipalIdelePowerSubgroup
              (K := K) n S T) *
        Nat.card
          (IdeleClassPowerLocalUnitQuotient
            (K := K) n S T) =
      (n : ℕ) ^
        (2 * totalPlaceCard (K := K) S) := by
  rw [
    card_sUnitPrincipalQuotient_mul_card_ideleClassQuotient
      (K := K) n S T hLarge,
    card_supportedIdeleQuotient_eq_power_two_totalPlaceCard
      (K := K) n hmu S T hS]


end GlobalClassFieldTheory.ClassFieldAxiom
end
end

section
-- module Solutions.OAIQ244_DUKE.GlobalClassFieldTheory_ClassFieldAxiom_CyclicIdeleClassNormIndex
attribute [-instance] _root_.GlobalClassFieldTheory.GlobalClassFields.ConductorialSubgroup.finiteIndex _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalClassFieldTheory.finiteGaloisLocalField_integerRing_moduleFinite _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.LocalClassFieldTheory.comparisonIntegerRingIsIntegralClosure _root_.LocalClassFieldTheory.normalizationIntegerRingIsIntegralClosure
attribute [-simp] _root_.IdeleGroup.finitePlaceIdele_finiteComponent_of_ne _root_.IdeleGroup.finitePlaceIdele_finiteComponent_same _root_.IdeleGroup.finitePlaceIdele_infiniteComponent _root_.IdeleGroup.infinitePlaceIdeleContinuous_apply _root_.IdeleGroup.infinitePlaceIdele_finiteComponent _root_.IdeleGroup.infinitePlaceIdele_infiniteComponent_of_ne _root_.IdeleGroup.infinitePlaceIdele_infiniteComponent_same _root_.IsDiscreteValuationRing.addVal_ringEquiv _root_.OAI.PrimeDegreePackets.ThetaConstruction.schwartzCM_apply _root_.RayClass.primesEquiv_val_eq_natGenerator _root_.RayClass.signToNarrow_mk _root_.RelativeIdeleGroup.relativeFinitePlaceIdele_finiteComponent_of_ne _root_.RelativeIdeleGroup.relativeFinitePlaceIdele_finiteComponent_same _root_.RelativeIdeleGroup.relativeFinitePlaceIdele_infiniteComponent _root_.RelativeIdeleGroup.relativeInfinitePlaceIdele_finiteComponent _root_.RelativeIdeleGroup.relativeInfinitePlaceIdele_infiniteComponent_of_ne _root_.RelativeIdeleGroup.relativeInfinitePlaceIdele_infiniteComponent_same
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI
attribute [local instance] OAI.starSubalgebraCommCStarAlgebra

set_option autoImplicit false

/-!
# The global class-field axiom

This file proves the cyclic idele-class norm-index formula.  The first
input is the `H⁻¹` calculation for the principal-idele term in

`1 → Lˣ → I_L → C_L → 1`.

For a cyclic extension this term vanishes by Hilbert 90.  The result below
is transported through the actual low-degree Tate comparison and then
through the equivariant identification of `Lˣ` with the subgroup of
principal relative ideles.
-/

noncomputable section

namespace GlobalClassFieldTheory.ClassFieldAxiom

open CyclicCohomology
open CyclicCohomology.ProfiniteCohomology.Herbrand

/-- Specialization of the exponent calculation to the actual relative
idele class group. -/
theorem ideleClassHerbrandH0_pow_finrank_eq_one
    (K L : Type)
    [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    (q :
      letI :=
        RelativeIdeleGroup.Cohomology.ideleClassMulDistribMulAction K L
      HerbrandH0 (L ≃ₐ[K] L)
        (RelativeIdeleGroup.ClassGroup K L)) :
    letI :=
      RelativeIdeleGroup.Cohomology.ideleClassMulDistribMulAction K L
    q ^ Module.finrank K L = 1 := by
  let :=
    RelativeIdeleGroup.Cohomology.ideleClassMulDistribMulAction K L
  rw [← IsGalois.card_aut_eq_finrank,
    Nat.card_eq_fintype_card]
  exact herbrandH0_pow_card_eq_one q

section NormQuotientCommutativity

local instance cyclicNormBase_isMulCommutative
    (A : Type) [Field A] [NumberField A] :
    IsMulCommutative (IdeleClassGroup A) :=
  ⟨⟨fun a b => mul_comm a b⟩⟩

/-- On the actual class-norm quotient, every power coprime to the
extension degree is injective. -/
theorem ideleClassNormQuotient_pow_injective_of_coprime
    (K L : Type)
    [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    (d : ℕ)
    (hd : d.Coprime (Module.finrank K L)) :
    Function.Injective
      (fun q : RelativeIdeleGroup.Cohomology.IdeleClassNormQuotient K L => q ^ d) := by
  let :=
    RelativeIdeleGroup.Cohomology.ideleClassMulDistribMulAction K L
  let e :=
    RelativeIdeleGroup.Cohomology.ideleClassHerbrandH0EquivNormQuotient K L
  have hpow :
      Function.Injective
        (fun x : HerbrandH0 (L ≃ₐ[K] L) (RelativeIdeleGroup.ClassGroup K L) =>
          x ^ d) :=
    pow_injective_of_exponent_of_coprime
      (A := HerbrandH0 (L ≃ₐ[K] L) (RelativeIdeleGroup.ClassGroup K L))
      (Module.finrank K L) d
      (ideleClassHerbrandH0_pow_finrank_eq_one K L) hd
  intro x y hxy
  apply e.symm.injective
  apply hpow
  exact
    ((map_pow e.symm x d).symm.trans (congrArg e.symm hxy)).trans
      (map_pow e.symm y d)

/-- Source-producing form of the roots-of-unity base-change step.  For a
pushout square `N = M ⊗[K] L`, if `[M:K]` is coprime
to `[L:K]`, the induced map

`C_K / N_{L/K}C_L → C_M / N_{N/M}C_N`

is injective.  The target is expressed in the fixed-bottom-field tower
model, so no unproved identification `𝔸_K ⊗_K M ≃ 𝔸_M` is assumed. -/
theorem pushoutNormQuotientMap_injective_of_coprime
    (K M L N : Type)
    [Field K] [NumberField K]
    [Field M] [NumberField M]
    [Field L] [NumberField L]
    [Field N] [NumberField N]
    [Algebra K M] [Algebra K L]
    [Algebra M N] [Algebra L N] [Algebra K N]
    [IsScalarTower K M N] [IsScalarTower K L N]
    [Algebra.IsPushout K M L N]
    [FiniteDimensional K M] [FiniteDimensional K L]
    [FiniteDimensional M N] [FiniteDimensional L N]
    [IsGalois K L]
    (hcoprime :
      (Module.finrank K M).Coprime
        (Module.finrank K L)) :
    Function.Injective
      (pushoutNormQuotientMap K M L N) :=
  pushoutNormQuotientMap_injective_of_pow_injective
    K M L N
    (ideleClassNormQuotient_pow_injective_of_coprime
      K L (Module.finrank K M) hcoprime)

section IntermediateNormQuotientCommutativity

local instance cyclicNormRelative_isMulCommutative_r6b6cce_1
    (A B : Type) [Field A] [NumberField A] [Field B] [Algebra A B] :
    IsMulCommutative (RelativeIdeleGroup.ClassGroup A B) :=
  ⟨⟨fun a b => mul_comm a b⟩⟩
/-- The pushout map with its target changed from the fixed-bottom tower
presentation to the actual norm quotient `C_M / N_{N/M} C_N`.

Only the Galois hypothesis on the auxiliary extension `M/K` is needed
for this last comparison. -/
noncomputable def actualPushoutNormQuotientMap
    (K M L N : Type)
    [Field K] [NumberField K]
    [Field M] [NumberField M]
    [Field L] [NumberField L]
    [Field N] [NumberField N]
    [Algebra K M] [Algebra K L]
    [Algebra M N] [Algebra L N] [Algebra K N]
    [IsScalarTower K M N] [IsScalarTower K L N]
    [Algebra.IsPushout K M L N]
    [FiniteDimensional K M] [FiniteDimensional K L]
    [FiniteDimensional M N] [FiniteDimensional L N]
    [IsGalois K M] :
    RelativeIdeleGroup.Cohomology.IdeleClassNormQuotient K L →
      RelativeIdeleGroup.Cohomology.IdeleClassNormQuotient M N :=
  fun q =>
    intermediateClassNormQuotientBaseChangeMulEquiv
      K M N (pushoutNormQuotientMap K M L N q)

/-- The actual pushout norm-quotient map sends a quotient representative
to the corresponding base-changed representative. -/
@[simp]
theorem actualPushoutNormQuotientMap_mk
    (K M L N : Type)
    [Field K] [NumberField K]
    [Field M] [NumberField M]
    [Field L] [NumberField L]
    [Field N] [NumberField N]
    [Algebra K M] [Algebra K L]
    [Algebra M N] [Algebra L N] [Algebra K N]
    [IsScalarTower K M N] [IsScalarTower K L N]
    [Algebra.IsPushout K M L N]
    [FiniteDimensional K M] [FiniteDimensional K L]
    [FiniteDimensional M N] [FiniteDimensional L N]
    [IsGalois K M]
    (c : IdeleClassGroup K) :
    actualPushoutNormQuotientMap K M L N
        (QuotientGroup.mk'
          (RelativeIdeleGroup.Cohomology.ideleClassNorm K L).range c) =
      QuotientGroup.mk'
        (RelativeIdeleGroup.Cohomology.ideleClassNorm M N).range
        (_root_.relativeIdeleClassBaseChangeMulEquiv
          (K := K) (L := M)
          (RelativeIdeleGroup.classInclusion K M c)) := by
  change
    intermediateClassNormQuotientBaseChangeMulEquiv
        K M N
        (pushoutNormQuotientMap K M L N
          (QuotientGroup.mk'
            (RelativeIdeleGroup.classNorm K L).range c)) =
      QuotientGroup.mk'
        (RelativeIdeleGroup.classNorm M N).range
        (_root_.relativeIdeleClassBaseChangeMulEquiv
          (K := K) (L := M)
          (RelativeIdeleGroup.classInclusion K M c))
  rw [pushoutNormQuotientMap_mk,
    intermediateClassNormQuotientBaseChangeMulEquiv_mk]

/-- Actual-target form of the injective roots-of-unity base-change
step. -/
theorem actualPushoutNormQuotientMap_injective_of_coprime
    (K M L N : Type)
    [Field K] [NumberField K]
    [Field M] [NumberField M]
    [Field L] [NumberField L]
    [Field N] [NumberField N]
    [Algebra K M] [Algebra K L]
    [Algebra M N] [Algebra L N] [Algebra K N]
    [IsScalarTower K M N] [IsScalarTower K L N]
    [Algebra.IsPushout K M L N]
    [FiniteDimensional K M] [FiniteDimensional K L]
    [FiniteDimensional M N] [FiniteDimensional L N]
    [IsGalois K L] [IsGalois K M]
    (hcoprime :
      (Module.finrank K M).Coprime
        (Module.finrank K L)) :
    Function.Injective
      (actualPushoutNormQuotientMap K M L N) := by
  intro x y hxy
  apply
    pushoutNormQuotientMap_injective_of_coprime
      K M L N hcoprime
  apply
    (intermediateClassNormQuotientBaseChangeMulEquiv K M N).injective
  exact hxy

end IntermediateNormQuotientCommutativity

end NormQuotientCommutativity

end GlobalClassFieldTheory.ClassFieldAxiom
end
end

section
-- module Solutions.OAIQ244_DUKE.GlobalClassFieldTheory_ClassFieldAxiom_HasseNormPrinciple
attribute [-instance] _root_.GlobalClassFieldTheory.GlobalClassFields.ConductorialSubgroup.finiteIndex _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalClassFieldTheory.finiteGaloisLocalField_integerRing_moduleFinite _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.LocalClassFieldTheory.comparisonIntegerRingIsIntegralClosure _root_.LocalClassFieldTheory.normalizationIntegerRingIsIntegralClosure
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

/-!
# The Hasse norm principle: the concrete local-global map

This file proves the Hasse norm principle on the actual idele and field norm
maps.  The local condition is expressed canonically:
at a place `v` it is the image of the determinant norm on
`K_v ⊗[K] L`.  At finite places this is the chosen completion norm
subgroup by
`_root_.finitePlaceLocalTensorNorm_range_eq_chosenLocalNormSubgroup`.

The resulting homomorphism

`Kˣ / N(Lˣ) ⟶ I_K / I_K,loc-norm`

is the concrete diagonal local-norm map.  Its injectivity is exactly the
Hasse norm principle.  The global-to-local inclusion and this equivalence
are independent of the global class-field axiom; the reverse inclusion
follows from degree-minus-one Tate-cohomology vanishing.
-/

open scoped NumberField TensorProduct
open NumberField

noncomputable section

namespace GlobalClassFieldTheory.ClassFieldAxiom

open CategoryTheory
open CyclicCohomology.ProfiniteCohomology.Herbrand

/-- Ideles whose component at every infinite place lies in the image of
the determinant norm on the corresponding archimedean local tensor
algebra. -/
def allInfinitePlaceLocalNormCondition
    {K L : Type}
    [Field K] [NumberField K]
    [Field L] [Algebra K L]
  [FiniteDimensional K L] :
    Subgroup (IdeleGroup K) :=
  ⨅ v : InfinitePlace K,
    (Units.map
      (Algebra.norm v.Completion :
        (v.Completion ⊗[K] L) →* v.Completion)).range.comap
      (IdeleGroup.infiniteComponent v)

/-- The simultaneous determinant-norm condition at every finite and
infinite place. -/
def allPlaceLocalNormCondition
    {K L : Type}
    [Field K] [NumberField K]
    [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L] :
    Subgroup (IdeleGroup K) :=
  allFinitePlaceLocalNormCondition (K := K) (L := L) ⊓
    allInfinitePlaceLocalNormCondition (K := K) (L := L)

end GlobalClassFieldTheory.ClassFieldAxiom
end
end

section
-- module Solutions.OAIQ244_DUKE.GlobalClassFieldTheory_Reciprocity_FinitePlaceArtin_NormRestriction
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.infinitePlaceComplexificationOverfield_algebra _root_.GlobalClassFieldTheory.Reciprocity.infinitePlaceComplexificationOverfield_baseAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalCyclotomicCompletionAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalCyclotomicLocalizedCompletionFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalCyclotomicLocalizedCompletionIsAlgebraic _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.residueFieldZModAlgebra _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedIntegralAlgebraContextValuationSubringAlgebra _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedIntegralAlgebraContextValuationSubringTower _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedIntegralLatticeContextModuleFinite _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedIntegralLatticeContextModuleFree _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedQPadicContextValuationSubringTower _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.diagonalLogAction _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.LocalClassFieldTheory.normalizationIntegerRingIsIntegralClosure _root_.chosenFinitePlaceCompletionAlgebra _root_.chosenFinitePlaceCompletionContinuousSMul _root_.chosenFinitePlaceCompletionFiniteDimensional _root_.chosenFinitePlaceCompletionLocallyCompactSpace _root_.chosenFinitePlaceExtensionCompletionAlgebra _root_.chosenFinitePlaceExtensionCompletionSMul _root_.chosenFinitePlaceLocalizedFiniteDimensional _root_.chosenFinitePlaceLocalizedIntegerAlgebra _root_.chosenFinitePlaceLocalizedIntegerModuleFinite _root_.chosenFinitePlaceLocalizedIsGalois _root_.chosenFinitePlaceLocalizedIsIntegralClosure _root_.chosenFinitePlaceLocalizedIsNonarchimedeanLocalField _root_.chosenFinitePlaceLocalizedIsUltrametricDist _root_.chosenFinitePlaceLocalizedIsValuativeTopology _root_.chosenFinitePlaceLocalizedLocallyCompactSpace _root_.chosenFinitePlaceLocalizedValuationCompatible _root_.chosenFinitePlaceLocalizedValuationHasExtension _root_.chosenFinitePlaceLocalizedValuationIsNontrivial _root_.chosenFinitePlaceLocalizedValuativeRel _root_.chosenFinitePlaceLocalizedValuativeRelIsNontrivial _root_.chosenFinitePlaceLocalizedValued
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI
attribute [local instance] OAI.starSubalgebraCommCStarAlgebra

set_option autoImplicit false

/-!
# Norm--restriction for finite-place Artin homomorphisms

This module proves norm--restriction naturality for finite-place Artin maps in an actual square of number fields and their chosen completed local extensions.
-/

open scoped Classical IsMulCommutative NNReal NumberField
open NumberField IsDedekindDomain

noncomputable section

namespace GlobalClassFieldTheory
namespace Reciprocity

open AlgebraicNumberTheory.Valuations
open HilbertRamification
open LocalClassFieldTheory
open LocalFieldTheory

variable {K L : Type}
    [Field K] [NumberField K]
    [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsAbelianGalois K L]

abbrev finitePlaceNormLocalizedAut
    (F M : Type) [Field F] [Field M] [Algebra F M]
    [NumberField F]
    (v : HeightOneSpectrum (𝓞 F))
    (w : AbsoluteValueExtension
      (NumberField.HeightOneSpectrum.adicAbv F v) M) :=
  let vF := NumberField.HeightOneSpectrum.adicAbv F v
  letI hwF :=
    AbsoluteValue.extensionCompletionAlgebra
      (K := F) w.1
  letI : SMul F w.1.Completion := hwF.toSMul
  letI : Algebra vF.Completion w.1.Completion :=
    AbsoluteValue.completionAlgebra vF w.1 w.2
  let E :=
    AlgebraicNumberTheory.Valuations.LocalizedCompletion vF w
  E ≃ₐ[vF.Completion] E

end Reciprocity
end GlobalClassFieldTheory
end
end

section
-- module Solutions.OAIQ244_DUKE.LubinTate_Padic_ChangedUniformizerCoefficient
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalClassFieldTheory.finiteGaloisLocalField_integerRing_moduleFinite _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitInverseLimitCarrierPadicModule _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitInverseLimitCarrierPadicSMul _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitQuotientCarrierPadicModule _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitQuotientCarrier_finite _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.adicPrincipalUnitsContinuousAdd _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.adicPrincipalUnitsContinuousSMul _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.adicPrincipalUnitsPadicModule _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.discretePrincipalUnitQuotientFinite _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.discretePrincipalUnitQuotientPadicModule _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitPadicModule _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitPadicSMul _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitProdiscreteLimitContinuousAdd _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitProdiscreteLimitContinuousSMul _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitProdiscreteLimitPadicModule _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.residueFieldZModAlgebra _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedIntegralAlgebraContextFieldAlgebra _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedIntegralAlgebraContextQPadic _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedIntegralAlgebraContextQPadicTower _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedIntegralAlgebraContextValuationSubringAlgebra _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedIntegralAlgebraContextValuationSubringTower _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedIntegralLatticeContextAlgebra _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedIntegralLatticeContextModuleFinite _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedIntegralLatticeContextModuleFree _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedMaximalIdealPowContextModuleFinite _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedMaximalIdealPowContextModuleFree _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedQPadicContextAlgebra _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedQPadicContextFact _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedQPadicContextFiniteDimensional _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedQPadicContextValuationExtension _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedQPadicContextValuationSubringTower _root_.LocalFieldTheory.DiscreteValuationField.finite_principalUnits_nthPowerKernel _root_.LocalFieldTheory.DiscreteValuationField.finite_residueRootsOfUnityGroup _root_.LocalFieldTheory.DiscreteValuationField.finite_valuationSubringUnits_nthPowerKernel _root_.LocalFieldTheory.DiscreteValuationField.finite_valuationSubringUnits_nthPowerQuotient _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.LubinTate.standardLubinTateLevelCompleteDVF_hasExtensionInstance _root_.LubinTate.standardLubinTateLevelField_galFinite _root_.LubinTate.standardLubinTateLevelField_isAbelianGalois _root_.LubinTate.standardLubinTateLevelField_isMulCommutative _root_.LubinTate.standardLubinTateUnitParameter_commGroup _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RamificationTheory.HilbertRamification.Higher.lowerRamificationGroup.instNormal _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionResidueField.instField _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.LocalClassFieldTheory.comparisonIntegerRingIsIntegralClosure _root_.LocalClassFieldTheory.normalizationIntegerRingIsIntegralClosure _root_.RamificationTheory.HilbertRamification.CompleteDVF.decompositionGroupMulSemiringAction _root_.RamificationTheory.HilbertRamification.CompleteDVF.decompositionGroupResidueFieldMulSemiringAction _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen _root_.infiniteAdeleRingT2Space
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

/-!
# The coefficient source for the p-adic changed-uniformizer intertwiner

Let `k` be an algebraic closure of `ZMod p`.  The Witt ring `W(k)` is the
integer ring of the completed maximal-unramified coefficient field used in
the changed-uniformizer construction. Mathlib's `WittVector.frobeniusRotation` supplies the
actual unit `ε ∈ W(k)ˣ` satisfying

`φ(ε) = ε u`

for every p-adic integer unit `u`.  This is precisely the linear-coefficient
equation for the semilinear changed-uniformizer intertwiner.

No second p-adic integer ring or Frobenius is introduced here: the base map
uses mathlib's equivalence `W(ZMod p) ≃+* ℤ_[p]`, and `φ` is
`WittVector.frobenius`.
-/

noncomputable section

namespace LubinTate

open LocalFieldTheory.DiscreteValuationField
open LocalFieldTheory.DiscreteValuationField.Examples.Qp

/-- The induced map on p-adic integer units. -/
noncomputable def padicValuationUnitToCompletedUnramifiedWittUnit
    (p : ℕ) [Fact p.Prime] :
    (padicLocalField p).valuationSubringˣ →*
      (padicCompletedUnramifiedWittRing p)ˣ :=
  Units.map
    (padicValuationSubringToCompletedUnramifiedWittRing p).toMonoidHom

end LubinTate

end
end


