-- Prove2me | Definitions.Def_OAIQ244Duke008
-- name    : OAIQ244Duke008
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-13T06:11:31.921666+00:00
-- url     : https://prove2.me/theorems/849cb7fe-40bb-445e-a1f3-1784c6c62118
-- title:
--   Definitions bundle OAIQ244Duke008 of the split of OpenAI, Equidistribution of Prime-Degree Torus Packets with Arbitrary Local Type
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.DukePrimeDegree.prime_degree_packet_measure_equidistribution_unconditional` and `OAI.DukePrimeDegree.prime_degree_packet_measures_tendsto_haar_unconditional`, carved from OpenAI's openai/math development (OpenAI, *Equidistribution of Prime-Degree Torus Packets with Arbitrary Local Type*, OpenAI Math Release, September 24, 2026, result family 15, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 268 declarations of OpenAI's Lean: 112 definitions, 3 inductive types or structures, 18 instances and 135 theorems. The definitions and types are `GlobalClassFieldTheory.Reciprocity.finitePlaceNormCompletion`, `KummerTheory.PrimeCyclotomicBase`, `KummerTheory.additiveCoordinatesLinearEquiv`, `KummerTheory.additivePiLinearEquiv`, `KummerTheory.additiveZModModuleOfPowEqOne`, `KummerTheory.finiteKummerRootSet`, `KummerTheory.finiteSupportField`, `KummerTheory.finsuppModHom`, `KummerTheory.monoidKerEquivMultiplicativeLinearKer`, `KummerTheory.numberFieldTorsionNthPowerQuotientEquivZMod`, `LocalClassFieldTheory.FilteredLiftState`, `LocalClassFieldTheory.FilteredLiftStep`, `LocalClassFieldTheory.UnitsTateCardinalityData`, `LocalClassFieldTheory.absoluteCompletionRingEquivComplex`, `LocalClassFieldTheory.absoluteCompletionRingEquivReal`, `LocalClassFieldTheory.abstractFixedField`, `LocalClassFieldTheory.abstractRelativeFixedField`, `LocalClassFieldTheory.abstractSubgroupEquivGaloisGroup`, `LocalClassFieldTheory.chosenFilteredLiftCorrectionSequence`, `LocalClassFieldTheory.chosenFilteredLiftStateSequence`, `LocalClassFieldTheory.chosenNormalBasisCoordinateMaximalSubmodule`, `LocalClassFieldTheory.chosenNormalBasisIntegerUnitsQuotientMap`, `LocalClassFieldTheory.chosenNormalBasisPrincipalUnitCorrectionProduct`, `LocalClassFieldTheory.chosenNormalBasisPrincipalUnitSubgroupInclusion`, `LocalClassFieldTheory.filteredCorrectionProduct`, `LocalClassFieldTheory.finiteGaloisFieldRangeEquivOfEmbedding`, `LocalClassFieldTheory.finiteGaloisFieldRangeOfEmbedding`, `LocalClassFieldTheory.finiteResidueExtensionEmbeddingInto`, `LocalClassFieldTheory.finiteResidueExtensionEquivIntermediateIn`, `LocalClassFieldTheory.finiteResidueFrobeniusExponentEquiv`, `LocalClassFieldTheory.finiteResidueFrobeniusExponentHom`, `LocalClassFieldTheory.finiteResidueFrobeniusIntegerPowers`, `LocalClassFieldTheory.finiteResidueGaloisIntermediateFieldIn`, `LocalClassFieldTheory.finiteResidueIntermediateFieldIn`, `LocalClassFieldTheory.finiteSeparableAlgHomFintype`, `LocalClassFieldTheory.finiteSeparableAlgHomFintypeForNormProduct`, `LocalClassFieldTheory.galoisAmbientUnitsRep`, `LocalClassFieldTheory.galoisGroupValueGroupMulDistribMulAction`, `LocalClassFieldTheory.intermediateFieldUnitsToGaloisAmbient`, `LocalClassFieldTheory.intrinsicAbsoluteGalois` and 75 more.
--
--   **Sources.** They come from these modules of lean/OAI/NumberTheory, in whole or in part: `AlgebraicNumberTheory_Galois_CyclicPrimeSubextension`, `AlgebraicNumberTheory_Idele_Cohomology_SPlaces_LocalBlocks`, `AlgebraicNumberTheory_Idele_Cohomology_SPlaces_OutsideIntegralInduced_ChosenPlace`, `AlgebraicNumberTheory_Idele_NormApproximation_InfinitePlaces`, `AlgebraicNumberTheory_SUnit_GaloisAction`, `AlgebraicNumberTheory_SUnit_Herbrand`, `AlgebraicNumberTheory_SUnit_LogLattice`, `AlgebraicNumberTheory_SUnit_Rank`, `DukePrimeDegree_Entropy_PredecessorWholeFutureEntropy`, `GlobalClassFieldTheory_ClassFieldAxiom_SUnitLocalPowerMap`, `GlobalClassFieldTheory_Reciprocity_FinitePlaceArtin_NormRestriction`, `GroupTheory_Finite`, `KummerTheory_Concrete_CyclotomicPrimeBaseChange`, `KummerTheory_Concrete_SUnitPreparation_SUnitPowerQuotient`, `KummerTheory_Concrete_SimpleExtensionLocalBehavior`, `Kummer_Concrete_FiniteGeneration`, `Kummer_Concrete_InfiniteInverse`, `Kummer_Concrete_SUnitPreparation_PrimePowerKernelCoordinates`, `LocalClassFieldTheory_ClassFormation_ArchimedeanNormQuotient`, `LocalClassFieldTheory_ClassFormation_CohomologyBridge`, `LocalClassFieldTheory_ClassFormation_FilteredLiftingSequence`, `LocalClassFieldTheory_ClassFormation_NormalBasis`, `LocalClassFieldTheory_ClassFormation_NormalBasisGaloisAction`, `LocalClassFieldTheory_ClassFormation_NormalBasisInfiniteProduct`, `LocalClassFieldTheory_ClassFormation_Valuation`, `LocalClassFieldTheory_Finite_LocalReciprocity_AbsoluteUnitsFixedField`, `LocalClassFieldTheory_Finite_LocalReciprocity_AbstractFixedFieldNorm`, `LocalClassFieldTheory_Finite_LocalReciprocity_FiniteAbstractFixedField`, `LocalClassFieldTheory_Finite_LocalReciprocity_FiniteExtensionClassFieldAxiom`, `LocalClassFieldTheory_Finite_LocalReciprocity_FiniteGaloisRealization`, `LocalClassFieldTheory_Finite_LocalReciprocity_FiniteResidueFinrankTransfer`, `LocalClassFieldTheory_Finite_LocalReciprocity_FiniteResidueFrobenius`, `LocalClassFieldTheory_Finite_LocalReciprocity_IntrinsicAbsoluteData`, `LocalClassFieldTheory_Finite_LocalReciprocity_LocalResidueDatum`, `LocalClassFieldTheory_Finite_LocalReciprocity_ResidueAbsoluteFrobenius`, `LocalClassFieldTheory_Finite_LocalReciprocity_ResidueActionIndex`, `LocalClassFieldTheory_Finite_LocalReciprocity_ResidueAlgebraicClosureDegree`, `LocalClassFieldTheory_Finite_LocalReciprocity_ResidueAlgebraicallyClosed`, `LocalClassFieldTheory_Finite_LocalReciprocity_ResidueDatum`, `LocalClassFieldTheory_Finite_LocalReciprocity_SeparableFixedFieldNorm`, `LocalClassFieldTheory_Finite_LocalReciprocity_SeparableNormProduct`, `LocalClassFieldTheory_Finite_LocalReciprocity_SeparableUnitsNorm`, `LocalClassFieldTheory_Finite_LocalReciprocity_TateTransport`, `LocalField_NonarchimedeanLocalField_NormalizedIntegerValuation`, `LocalField_NonarchimedeanLocalField_PrincipalUnitQuotients`, `LocalField_NonarchimedeanLocalField_ResidueExtension`, `LocalField_NonarchimedeanLocalField_UnramifiedFrobenius`, `Ramification_ClosedSubgroups`, `Ramification_GaloisValuation_AbsoluteGalois_AbsoluteRamification`, `Ramification_GaloisValuation_AbsoluteGalois_FiniteLevelValuationRestriction`, `Ramification_GaloisValuation_ClosedFixingSubgroup`, `Ramification_HilbertRamification_RamificationGroup`, `Ramification_HilbertRamification_ResidueExactSequence`, `Ramification_HilbertRamification_ValuationSubring`, `Ramification_ProfiniteInvariant`, `Valuation_Completion_FiniteProductNormTrace`, `Valuation_DiscreteValuationField_AdicPower`, `Valuation_DiscreteValuationField_ChevalleyExtension`, `Valuation_LocalRingEquiv`, `Valuation_UniqueRing`.
--
--   **Imports.** It imports no bundle or statement, only Mathlib.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ244Duke018`, `OAIQ244Duke019`, `OAIQ244Duke020`, `OAIQ244Duke021`, `OAIQ244Duke022` and `OAIQ244Duke024`.
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
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Combinatorics.Hall.Finite
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Finsupp
import Mathlib.Data.Finsupp.Fintype
import Mathlib.Data.Int.ModEq
import Mathlib.Data.Int.WithZero
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.Nat.Pairing
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Rat.Cast.CharZero
import Mathlib.Data.Rat.Lemmas
import Mathlib.Data.Set.Finite.Range
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.ZMod.QuotientGroup
import Mathlib.Dynamics.BirkhoffSum.Basic
import Mathlib.Dynamics.Ergodic.Conservative
import Mathlib.Dynamics.Ergodic.MeasurePreserving
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
import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
import Mathlib.LinearAlgebra.Matrix.Gershgorin
import Mathlib.LinearAlgebra.Pi
import Mathlib.LinearAlgebra.Quotient.Pi
import Mathlib.LinearAlgebra.StdBasis
import Mathlib.LinearAlgebra.TensorProduct.Basis
import Mathlib.LinearAlgebra.TensorProduct.RightExactness
import Mathlib.LinearAlgebra.Trace
import Mathlib.Logic.Equiv.Fin.Rotate
import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Mathlib.MeasureTheory.Covering.Besicovitch
import Mathlib.MeasureTheory.Function.ConditionalExpectation.CondJensen
import Mathlib.MeasureTheory.Function.ContinuousMapDense
import Mathlib.MeasureTheory.Function.Floor
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.Lebesgue.Markov
import Mathlib.MeasureTheory.Measure.Haar.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Measure.Prokhorov
import Mathlib.MeasureTheory.Measure.Regular
import Mathlib.MeasureTheory.OuterMeasure.BorelCantelli
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
import Mathlib.NumberTheory.Padics.WithVal
import Mathlib.NumberTheory.RamificationInertia.Galois
import Mathlib.NumberTheory.RamificationInertia.Inertia
import Mathlib.NumberTheory.RamificationInertia.Ramification
import Mathlib.NumberTheory.RamificationInertia.Valuation
import Mathlib.Order.Filter.AtTopBot.Tendsto
import Mathlib.Probability.Kernel.Disintegration.StandardBorel
import Mathlib.Probability.Kernel.MeasurableIntegral
import Mathlib.Probability.Kernel.MeasurableLIntegral
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
import Mathlib.RingTheory.Polynomial.RationalRoot
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
import Mathlib.Topology.Algebra.MulAction
import Mathlib.Topology.Algebra.Nonarchimedean.AdicTopology
import Mathlib.Topology.Algebra.OpenSubgroup
import Mathlib.Topology.Algebra.Order.Field
import Mathlib.Topology.Algebra.Polynomial
import Mathlib.Topology.Algebra.Ring.Basic
import Mathlib.Topology.Algebra.Ring.Compact
import Mathlib.Topology.Algebra.UniformRing
import Mathlib.Topology.Algebra.Valued.LocallyCompact
import Mathlib.Topology.Algebra.Valued.NormedValued
import Mathlib.Topology.Algebra.Valued.ValuativeRel
import Mathlib.Topology.Algebra.Valued.ValuedField
import Mathlib.Topology.Algebra.Valued.WithZeroMulInt
import Mathlib.Topology.Compactness.Lindelof
import Mathlib.Topology.Compactness.LocallyCompact
import Mathlib.Topology.Connected.Clopen
import Mathlib.Topology.Homeomorph.Defs
import Mathlib.Topology.Homeomorph.Lemmas
import Mathlib.Topology.Homeomorph.TransferInstance
import Mathlib.Topology.Instances.Matrix
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Topology.Instances.Sign
import Mathlib.Topology.Instances.ZMod
import Mathlib.Topology.Maps.Basic
import Mathlib.Topology.MetricSpace.Ultra.Basic
import Mathlib.Topology.MetricSpace.UniformConvergence
import Mathlib.Topology.Neighborhoods
import Mathlib.Topology.Order
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.Sequences
import Mathlib.Topology.Sets.Opens
import Mathlib.Topology.UniformSpace.AbsoluteValue
import Mathlib.Topology.UniformSpace.HeineCantor
import Mathlib.Topology.WithTopology

section
-- module Solutions.OAIQ244_DUKE.LocalField_NonarchimedeanLocalField_PrincipalUnitQuotients
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
/-!
# Successive principal-unit quotients

Develops `U^n/U^(n+1)` and identifies it with the additive ideal quotient
`𝓂^n/𝓂^(n+1)` through the first-order map `a ↦ 1 + a`.
-/

set_option autoImplicit false

namespace LocalFieldTheory

noncomputable section

universe u

open scoped ValuativeRel

open Filter

/-! ### Separatedness of the principal-unit filtration -/

/-- Krull separatedness of the maximal-ideal filtration of the valuation integer
ring of a nonarchimedean local field. -/
theorem maximalIdeal_iInf_pow_eq_bot
    (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] :
    (⨅ n : Nat, (𝓂[K] ^ n : Ideal 𝒪[K])) = ⊥ := by
  exact Ideal.iInf_pow_eq_bot_of_isLocalRing
    (I := (𝓂[K] : Ideal 𝒪[K])) Ideal.IsPrime.ne_top'

/-- An element of the valuation integer ring lying in every power of the
maximal ideal is zero. -/
theorem eq_zero_of_mem_all_maximalIdeal_pow
    (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] (x : 𝒪[K])
    (hx : ∀ n : Nat, x ∈ (𝓂[K] ^ n : Ideal 𝒪[K])) :
    x = 0 := by
  have hxInf : x ∈ (⨅ n : Nat, (𝓂[K] ^ n : Ideal 𝒪[K])) := by
    rw [Ideal.mem_iInf]
    exact hx
  rw [maximalIdeal_iInf_pow_eq_bot K] at hxInf
  exact (Ideal.mem_bot.mp hxInf)

/-! ### Maximal-ideal powers as local neighborhoods -/

/-- Each power of the maximal ideal is closed in the valuation integer ring. -/
theorem isClosed_maximalIdeal_pow
    (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] (n : Nat) :
    IsClosed (((𝓂[K] ^ n : Ideal 𝒪[K]) : Set 𝒪[K])) := by
  rcases IsDiscreteValuationRing.exists_irreducible 𝒪[K] with ⟨ϖ, hϖ⟩
  have hset := Irreducible.maximalIdeal_pow_eq_setOfPred_le_v_coe_pow
    (v := ValuativeRel.valuation K) hϖ n
  rw [hset]
  have hclosed :
      IsClosed {x : 𝒪[K] |
        (ValuativeRel.valuation K).restrict (x : K) ≤
          (ValuativeRel.valuation K).restrict ((ϖ : K) ^ n)} :=
    ((ValuativeRel.valuation K).isClosed_closedBall
      ((ValuativeRel.valuation K).restrict ((ϖ : K) ^ n))).preimage
        (continuous_subtype_val : Continuous (fun x : 𝒪[K] => (x : K)))
  convert hclosed using 1
  all_goals try with_reducible_and_instances rfl
  ext x
  simp only [Set.mem_ofPred_eq]
  rw [← map_pow, Valuation.restrict_le_iff, map_pow]

/-- Each power of the maximal ideal is a zero-neighborhood in the valuation
integer ring. -/
theorem maximalIdeal_pow_mem_nhds_zero
    (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] (n : Nat) :
    (((𝓂[K] ^ n : Ideal 𝒪[K]) : Set 𝒪[K])) ∈ nhds (0 : 𝒪[K]) := by
  rcases IsDiscreteValuationRing.exists_irreducible 𝒪[K] with ⟨ϖ, hϖ⟩
  let γ : (ValuativeRel.ValueGroupWithZero K)ˣ :=
    Units.mk0 (ValuativeRel.valuation K ((ϖ : 𝒪[K]) : K) ^ n)
      (pow_ne_zero n (ne_of_gt (Valuation.integer.v_irreducible_pos
        (v := ValuativeRel.valuation K) hϖ)))
  refine (mem_nhds_subtype ((ValuativeRel.valuation K).integer : Set K)
      (0 : 𝒪[K]) (((𝓂[K] ^ n : Ideal 𝒪[K]) : Set 𝒪[K]))).2 ?_
  refine ⟨{x : K | ValuativeRel.valuation K x <
      (γ : ValuativeRel.ValueGroupWithZero K)}, ?_, ?_⟩
  · exact (IsValuativeTopology.hasBasis_nhds_zero K).mem_of_mem (i := γ) trivial
  · intro x hx
    change x ∈ ((𝓂[K] ^ n : Ideal 𝒪[K]) : Set 𝒪[K])
    have hset := Irreducible.maximalIdeal_pow_eq_setOfPred_le_v_coe_pow
      (v := ValuativeRel.valuation K) hϖ n
    rw [hset]
    have hxv : ValuativeRel.valuation K ((x : 𝒪[K]) : K) <
        (γ : ValuativeRel.ValueGroupWithZero K) := hx
    exact le_of_lt hxv

/-! ### Finite correction products for complete lifting -/

end
end LocalFieldTheory
end

section
-- module Solutions.OAIQ244_DUKE.LocalField_NonarchimedeanLocalField_ResidueExtension
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
/-!
# Residue extensions

Constructs the maps induced on valuation rings, residue fields, and residue
units by a valued extension, with degree, trace, norm, and Frobenius results.
-/

set_option autoImplicit false

namespace LocalFieldTheory

noncomputable section

universe u

open scoped ValuativeRel

/-- The finite-field norm on residue-field units is surjective for the canonical
residue extension induced by a valuation extension. -/
theorem residueField_units_norm_surjective_of_valuationExtension (K L : Type u)
    [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
    [Algebra K L]
    [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)] :
    Function.Surjective (Units.map (Algebra.norm 𝓀[K] (S := 𝓀[L]))) := by
  let := Fintype.ofFinite 𝓀[K]
  exact FiniteField.unitsMap_norm_surjective 𝓀[K] 𝓀[L]

end
end LocalFieldTheory
end

section
-- module Solutions.OAIQ244_DUKE.LocalClassFieldTheory_ClassFormation_Valuation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

set_option autoImplicit false
/-! Provides the public declarations in the `LocalClassFieldTheory.ClassFormation.Valuation` Lean module. -/

namespace LocalClassFieldTheory

open LocalFieldTheory

noncomputable section

universe u

open scoped ValuativeRel
open IsNonarchimedeanLocalField

/-- The trivial Galois action on the value group `ℤ`, written
multiplicatively so that it is a multiplicative Galois module. -/
@[implicit_reducible]
def galoisGroupValueGroupMulDistribMulAction
    (K L : Type u) [Field K] [Field L] [Algebra K L] :
    MulDistribMulAction (Gal(L / K)) (Multiplicative Int) where
  smul _ n := n
  one_smul := by intro n; rfl
  mul_smul := by intro _ _ n; rfl
  smul_mul := by intro _ m n; rfl
  smul_one := by intro _; rfl

end
end LocalClassFieldTheory
end

section
-- module Solutions.OAIQ244_DUKE.Valuation_DiscreteValuationField_AdicPower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

set_option autoImplicit false

namespace ValuationTheory

/-!
# Adic completeness and positive powers of an ideal

This file contains small generic source lemmas used to pass from completeness
for a positive power `I ^ n` back to completeness for `I`.
-/

noncomputable section

namespace DiscreteValuationField

variable {R : Type*} [CommRing R]
variable {M : Type*} [AddCommGroup M] [Module R M]
variable {N : Type*} [AddCommGroup N] [Module R N]

/-- If a module is Hausdorff for a positive power of an ideal, then it is
Hausdorff for the ideal itself. -/
theorem isHausdorff_of_isHausdorff_pow
    (I : Ideal R) {n : ℕ} (_hn : 0 < n)
    [IsHausdorff (I ^ n) M] :
    IsHausdorff I M := by
  refine ⟨fun x hx => IsHausdorff.haus
    (inferInstance : IsHausdorff (I ^ n) M) x ?_⟩
  intro k
  simpa [pow_mul] using hx (n * k)

/-- If a module is precomplete for a positive power of an ideal, then it is
precomplete for the ideal itself. -/
theorem isPrecomplete_of_isPrecomplete_pow
    (I : Ideal R) {n : ℕ} (hn : 0 < n)
    [IsPrecomplete (I ^ n) M] :
    IsPrecomplete I M := by
  refine ⟨fun f hf => ?_⟩
  have hsub :
      ∀ {a b : ℕ}, a ≤ b →
        f (n * a) ≡ f (n * b)
          [SMOD ((I ^ n) ^ a • ⊤ : Submodule R M)] := by
    intro a b hab
    have hle : n * a ≤ n * b := Nat.mul_le_mul_left n hab
    simpa [pow_mul] using hf hle
  obtain ⟨L, hL⟩ :=
    IsPrecomplete.prec (I := I ^ n) (M := M)
      (inferInstance : IsPrecomplete (I ^ n) M)
      (f := fun k => f (n * k)) hsub
  refine ⟨L, fun m => ?_⟩
  have hm : m ≤ n * m := by
    simpa using Nat.mul_le_mul_right m (Nat.succ_le_of_lt hn)
  have hfm : f m ≡ f (n * m)
      [SMOD (I ^ m • ⊤ : Submodule R M)] :=
    hf hm
  have htail : f (n * m) ≡ L
      [SMOD (I ^ m • ⊤ : Submodule R M)] := by
    apply SModEq.mono (Submodule.pow_smul_top_le I M hm)
    simpa [pow_mul] using hL m
  exact hfm.trans htail

/-- If a module is complete for a positive power of an ideal, then it is
complete for the ideal itself. -/
theorem isAdicComplete_of_isAdicComplete_pow
    (I : Ideal R) {n : ℕ} (hn : 0 < n)
    [IsAdicComplete (I ^ n) M] :
    IsAdicComplete I M where
  toIsHausdorff := isHausdorff_of_isHausdorff_pow (M := M) I hn
  toIsPrecomplete := isPrecomplete_of_isPrecomplete_pow (M := M) I hn

end DiscreteValuationField

end

end ValuationTheory
end

section
-- module Solutions.OAIQ244_DUKE.Valuation_DiscreteValuationField_ChevalleyExtension
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

set_option autoImplicit false

namespace ValuationTheory

/-!
# Chevalley's valuation extension theorem

Mathlib has the predicate `Valuation.HasExtension` and the induced valuation
subring/residue-field API.  This file proves the field-extension form of
Chevalley's valuation extension theorem from mathlib's maximal local subring
construction: a local subring of a field is dominated by a valuation subring.
-/

noncomputable section

universe u v w x y z

namespace DiscreteValuationField
namespace Valuation

variable {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L]
variable {ΓK : Type w} [LinearOrderedCommGroupWithZero ΓK]

/-- If a valuation subring `B` of the extension field dominates the base
valuation ring locally, then any base-field element whose image lies in `B`
already lies in the base valuation ring. -/
theorem mem_base_valuationSubring_of_lift_mem
    (vK : _root_.Valuation K ΓK)
    (B : ValuationSubring L)
    (hB : ∀ x : vK.valuationSubring, algebraMap vK.valuationSubring L x ∈ B.toSubring)
    (hlocal : IsLocalHom
      ((algebraMap vK.valuationSubring L).codRestrict B.toSubring hB))
    {x : K} (hxB : algebraMap K L x ∈ B.toSubring) :
    x ∈ vK.valuationSubring := by
  let A := vK.valuationSubring
  rcases A.mem_or_inv_mem x with hxA | hxinvA
  · exact hxA
  · by_cases hx0 : x = 0
    · simp [hx0]
    let y : A := ⟨x⁻¹, hxinvA⟩
    let f : A →+* B.toSubring :=
      (algebraMap A L).codRestrict B.toSubring hB
    let : IsLocalHom f := by
      dsimp [f, A]
      exact hlocal
    have hfy_unit : IsUnit (f y) := by
      apply IsUnit.of_mul_eq_one (⟨algebraMap K L x, hxB⟩ : B.toSubring)
      ext
      change (algebraMap K L) (x⁻¹) * (algebraMap K L) x = 1
      rw [← map_mul, inv_mul_cancel₀ hx0, map_one]
    have hy_unit : IsUnit y := IsUnit.of_map f y hfy_unit
    have hy_val : A.valuation (x⁻¹) = 1 := by
      simpa [y] using (A.valuation_eq_one_iff y).1 hy_unit
    have hx_val : A.valuation x = 1 := by
      rw [← inv_inv x, map_inv₀, hy_val, inv_one]
    exact A.mem_of_valuation_le_one x hx_val.le

/-- Chevalley's theorem in valuation-subring form.

For any field extension `L / K`, a valuation subring of `K` admits a dominating
valuation subring of `L`, and the original valuation subring is exactly the
pullback of the extension valuation subring along `K → L`.  This is the
construction-level statement behind `chevalley_hasSomeExtensionTo`; downstream
finite-extension arguments can use the returned subring `B` before passing to
its canonical valuation. -/
theorem exists_extension_valuationSubring
    (vK : _root_.Valuation K ΓK) :
    ∃ B : ValuationSubring L,
      ∃ hB : ∀ x : vK.valuationSubring,
        algebraMap vK.valuationSubring L x ∈ B.toSubring,
        IsLocalHom
          ((algebraMap vK.valuationSubring L).codRestrict B.toSubring hB) ∧
        ∀ x : K, algebraMap K L x ∈ B.toSubring ↔
          x ∈ vK.valuationSubring := by
  obtain ⟨B, hB, hlocal⟩ :=
    IsLocalRing.exists_factor_valuationRing
      (f := algebraMap vK.valuationSubring L)
  refine ⟨B, hB, hlocal, ?_⟩
  intro x
  constructor
  · intro hxB
    exact mem_base_valuationSubring_of_lift_mem vK B hB hlocal hxB
  · intro hxA
    have hxB :
        algebraMap vK.valuationSubring L
            (⟨x, hxA⟩ : vK.valuationSubring) ∈ B.toSubring :=
      hB ⟨x, hxA⟩
    rw [IsScalarTower.algebraMap_apply vK.valuationSubring K L] at hxB
    simpa using hxB

/-- A `HasExtension` proof for the canonical valuation attached to a valuation
subring gives exact pullback of valuation subrings. -/
theorem valuationSubring_pullback_of_hasExtension_valuation
    (vK : _root_.Valuation K ΓK) (B : ValuationSubring L)
    [vK.HasExtension B.valuation] (x : K) :
    algebraMap K L x ∈ B.toSubring ↔ x ∈ vK.valuationSubring := by
  constructor
  · intro hxB
    have hx_le : B.valuation (algebraMap K L x) ≤ 1 :=
      (B.valuation_le_one_iff (algebraMap K L x)).2 hxB
    have hxK_le : vK x ≤ 1 :=
      (_root_.Valuation.HasExtension.val_map_le_one_iff vK B.valuation x).1 hx_le
    exact (vK.mem_valuationSubring_iff x).1 hxK_le
  · intro hxK
    have hxK_le : vK x ≤ 1 :=
      (vK.mem_valuationSubring_iff x).2 hxK
    have hx_le : B.valuation (algebraMap K L x) ≤ 1 :=
      (_root_.Valuation.HasExtension.val_map_le_one_iff vK B.valuation x).2 hxK_le
    exact (B.valuation_le_one_iff (algebraMap K L x)).1 hx_le

end Valuation
end DiscreteValuationField

end

end ValuationTheory
end

section
-- module Solutions.OAIQ244_DUKE.Valuation_UniqueRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

set_option autoImplicit false

namespace ValuationTheory

/-!
# The unique-extension characterization: automorphism invariance from unique extension

The pullback of an extension valuation ring by a ground-field automorphism is
again an extension valuation ring.  Hence uniqueness forces the chosen ring
to be fixed by every automorphism of the extension field.  This is the first
Galois-theoretic step in the converse direction of the unique-extension characterization.
-/

noncomputable section

open scoped Pointwise

namespace Valuations

/-- The canonical homomorphism from the base valuation ring into an extension
valuation ring, without identifying either ring with the valuation subring of
its canonical valuation. -/
def valuationSubringMapOfHasExtension
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    (V : ValuationSubring K) (W : ValuationSubring L)
    (hW : V.valuation.HasExtension W.valuation) : V →+* W := by
  letI : V.valuation.HasExtension W.valuation := hW
  exact (algebraMap K L).restrict V.toSubring W.toSubring (by
    intro x hx
    exact
      (ValuationTheory.DiscreteValuationField.Valuation.valuationSubring_pullback_of_hasExtension_valuation
        V.valuation W x).2 (by
          simpa only [ValuationSubring.valuationSubring_valuation,
            ValuationSubring.mem_toSubring] using hx))

end Valuations
end

end ValuationTheory
end

section
-- module Solutions.OAIQ244_DUKE.Valuation_LocalRingEquiv
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

set_option autoImplicit false

/-!
# Local-ring equivalences and maximal ideals

Equivalences of local rings preserve the maximal ideal and all of its powers.
The resulting membership criterion is useful when transporting principal-unit
filtrations between equivalent valuation rings.
-/

namespace ValuationTheory

/-- A local-ring equivalence maps the maximal ideal onto the maximal ideal. -/
theorem ringEquiv_map_maximalIdeal
    {R S : Type*} [CommRing R] [CommRing S]
    [IsLocalRing R] [IsLocalRing S] (e : R ≃+* S) :
    Ideal.map e.toRingHom (IsLocalRing.maximalIdeal R) =
      IsLocalRing.maximalIdeal S := by
  apply le_antisymm
  · rw [Ideal.map_le_iff_le_comap]
    intro x hx
    change e x ∈ IsLocalRing.maximalIdeal S
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff] at hx ⊢
    intro h
    have h' := h.map e.symm.toRingHom
    exact hx (by simpa using h')
  · intro y hy
    obtain ⟨x, rfl⟩ := e.surjective y
    apply Ideal.mem_map_of_mem
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff] at hy ⊢
    intro h
    exact hy (h.map e.toRingHom)

/-- A local-ring equivalence maps every power of the maximal ideal onto the
corresponding power. -/
theorem ringEquiv_map_maximalIdeal_pow
    {R S : Type*} [CommRing R] [CommRing S]
    [IsLocalRing R] [IsLocalRing S] (e : R ≃+* S) (n : ℕ) :
    Ideal.map e.toRingHom (IsLocalRing.maximalIdeal R ^ n) =
      IsLocalRing.maximalIdeal S ^ n := by
  rw [Ideal.map_pow, ringEquiv_map_maximalIdeal]

/-- Membership in a maximal-ideal power is preserved by a local-ring
equivalence. -/
theorem ringEquiv_mem_maximalIdeal_pow_iff
    {R S : Type*} [CommRing R] [CommRing S]
    [IsLocalRing R] [IsLocalRing S] (e : R ≃+* S) (n : ℕ) (x : R) :
    e x ∈ IsLocalRing.maximalIdeal S ^ n ↔
      x ∈ IsLocalRing.maximalIdeal R ^ n := by
  rw [← ringEquiv_map_maximalIdeal_pow e n]
  constructor
  · intro hx
    rcases (Ideal.mem_map_iff_of_surjective e.toRingHom e.surjective).1 hx with
      ⟨y, hy, hey⟩
    exact e.injective hey ▸ hy
  · exact Ideal.mem_map_of_mem e.toRingHom

end ValuationTheory
end

section
-- module Solutions.OAIQ244_DUKE.Ramification_HilbertRamification_ValuationSubring
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

set_option autoImplicit false

namespace RamificationTheory

/-!
# Hilbert ramification theory: valuation-subring layer

This file manages the ordinary valuation-subring decomposition/inertia exact
sequence.  For an arbitrary valuation subring the residue action need not be
onto the full residue automorphism group; the canonical theorem is the exact
sequence with target equal to the range of the residue action.
-/

noncomputable section

universe u v

namespace HilbertRamification
namespace ValuationSubring

variable (K : Type u) {L : Type v} [Field K] [Field L] [Algebra K L]

/-- finite Galois ramification theory:
the decomposition group of a valuation subring. -/
abbrev decompositionGroup (A : _root_.ValuationSubring L) :
    Subgroup (L ≃ₐ[K] L) :=
  A.decompositionSubgroup K

/-- finite Galois ramification theory:
the inertia group of a valuation subring. -/
abbrev inertiaGroup (A : _root_.ValuationSubring L) :
    Subgroup (decompositionGroup K A) :=
  A.inertiaSubgroup K

/-- The residue action of the decomposition group on the residue field. -/
abbrev residueAction (A : _root_.ValuationSubring L) :
    decompositionGroup K A →*
      (IsLocalRing.ResidueField A ≃+* IsLocalRing.ResidueField A) :=
  MulSemiringAction.toRingAut
    (A.decompositionSubgroup K) (IsLocalRing.ResidueField A)

/-- The inertia group is the kernel of the residue action. -/
theorem residueAction_ker (A : _root_.ValuationSubring L) :
    MonoidHom.ker (residueAction K A) = inertiaGroup K A := by
  rfl

/-- Provides the instance `inertiaGroup_normal`. -/
instance inertiaGroup_normal (A : _root_.ValuationSubring L) :
    (inertiaGroup K A).Normal := by
  rw [← residueAction_ker (K := K) A]
  infer_instance

/-- finite Galois ramification theory:
the unit quotient `σ x / x` attached to an automorphism in the decomposition
group.  This is the expression used in the definition of the ramification
group. -/
def automorphismUnitQuotient
    (A : _root_.ValuationSubring L) (σ : decompositionGroup K A) (x : Lˣ) :
    Lˣ :=
  Units.mapEquiv ((σ : L ≃ₐ[K] L).toMulEquiv) x / x

/-- States the theorem `automorphismUnitQuotient_one`. -/
@[simp] theorem automorphismUnitQuotient_one
    (A : _root_.ValuationSubring L) (x : Lˣ) :
    automorphismUnitQuotient K A 1 x = 1 := by
  ext
  simp [automorphismUnitQuotient]

/-- States the theorem `automorphismUnitQuotient_mul`. -/
theorem automorphismUnitQuotient_mul
    (A : _root_.ValuationSubring L) (σ τ : decompositionGroup K A) (x : Lˣ) :
    automorphismUnitQuotient K A (σ * τ) x =
      automorphismUnitQuotient K A σ
        (Units.mapEquiv ((τ : L ≃ₐ[K] L).toMulEquiv) x) *
      automorphismUnitQuotient K A τ x := by
  ext
  simp [automorphismUnitQuotient, div_eq_mul_inv, mul_assoc]

/-- The decomposition and inertia subgroup definitions:
the ramification group `R_w`, as the subgroup of inertia whose unit quotients
`σ x / x` are principal units for every `x : Lˣ`. -/
def ramificationGroup (A : _root_.ValuationSubring L) :
    Subgroup (inertiaGroup K A) where
  carrier :=
    {σ | ∀ x : Lˣ,
      automorphismUnitQuotient K A (σ : decompositionGroup K A) x ∈
        A.principalUnitGroup}
  one_mem' := by
    intro x
    have hmap : Units.mapEquiv (AlgEquiv.toMulEquiv (1 : L ≃ₐ[K] L)) x = x := by
      ext
      rfl
    simp [automorphismUnitQuotient, hmap]
  mul_mem' := by
    intro σ τ hσ hτ x
    change
      automorphismUnitQuotient K A ((σ * τ : inertiaGroup K A) : decompositionGroup K A) x ∈
        A.principalUnitGroup
    have hx :
        automorphismUnitQuotient K A (σ : decompositionGroup K A)
            (Units.mapEquiv (((τ : decompositionGroup K A) : L ≃ₐ[K] L).toMulEquiv) x) *
          automorphismUnitQuotient K A (τ : decompositionGroup K A) x ∈
          A.principalUnitGroup :=
      A.principalUnitGroup.mul_mem
      (hσ (Units.mapEquiv (((τ : decompositionGroup K A) : L ≃ₐ[K] L).toMulEquiv) x))
      (hτ x)
    simpa [automorphismUnitQuotient_mul] using hx
  inv_mem' := by
    intro σ hσ x
    let y : Lˣ :=
      Units.mapEquiv
        ((((σ : decompositionGroup K A)⁻¹ : decompositionGroup K A) :
          L ≃ₐ[K] L).toMulEquiv) x
    have hy :
        automorphismUnitQuotient K A (σ : decompositionGroup K A) y ∈
          A.principalUnitGroup :=
      hσ y
    have hyinv :
        (automorphismUnitQuotient K A (σ : decompositionGroup K A) y)⁻¹ ∈
          A.principalUnitGroup :=
      A.principalUnitGroup.inv_mem hy
    have hquot :
        automorphismUnitQuotient K A
            ((σ⁻¹ : inertiaGroup K A) : decompositionGroup K A) x =
          (automorphismUnitQuotient K A (σ : decompositionGroup K A) y)⁻¹ := by
      ext
      simp [automorphismUnitQuotient, y, div_eq_mul_inv]
    rw [hquot]
    exact hyinv

/-- States the theorem `mem_ramificationGroup_iff`. -/
@[simp] theorem mem_ramificationGroup_iff
    (A : _root_.ValuationSubring L) (σ : inertiaGroup K A) :
    σ ∈ ramificationGroup K A ↔
      ∀ x : Lˣ,
        automorphismUnitQuotient K A (σ : decompositionGroup K A) x ∈
          A.principalUnitGroup :=
  Iff.rfl


/-- finite Galois ramification theory:
the decomposition field `Z_w` is the fixed field of the decomposition group. -/
abbrev decompositionField (A : _root_.ValuationSubring L) :
    IntermediateField K L :=
  IntermediateField.fixedField (decompositionGroup K A)

/-- States the theorem `mem_decompositionField_iff`. -/
@[simp] theorem mem_decompositionField_iff
    (A : _root_.ValuationSubring L) (x : L) :
    x ∈ decompositionField K A ↔
      ∀ σ ∈ decompositionGroup K A, σ x = x := by
  exact IntermediateField.mem_fixedField_iff
    (H := decompositionGroup K A) x

/-- The inertia group as a subgroup of the full `K`-automorphism group of `L`.
This is the subgroup whose fixed field is the classical inertia field. -/
abbrev inertiaGroupInAut (A : _root_.ValuationSubring L) :
    Subgroup (L ≃ₐ[K] L) :=
  Subgroup.map (decompositionGroup K A).subtype (inertiaGroup K A)

/-- The canonical inclusion `I_w -> G(L/K)`. -/
def inertiaGroupToAut (A : _root_.ValuationSubring L) :
    inertiaGroup K A →* (L ≃ₐ[K] L) :=
  (decompositionGroup K A).subtype.comp (inertiaGroup K A).subtype

/-- States the theorem `inertiaGroupToAut_apply`. -/
@[simp] theorem inertiaGroupToAut_apply
    (A : _root_.ValuationSubring L) (σ : inertiaGroup K A) :
    inertiaGroupToAut (K := K) A σ =
      ((σ : decompositionGroup K A) : L ≃ₐ[K] L) :=
  rfl

/-- The inertia-field definition:
the inertia field `T_w` is the fixed field of the inertia group. -/
abbrev inertiaField (A : _root_.ValuationSubring L) :
    IntermediateField K L :=
  IntermediateField.fixedField (inertiaGroupInAut K A)

/-- States the theorem `mem_inertiaField_iff`. -/
@[simp] theorem mem_inertiaField_iff
    (A : _root_.ValuationSubring L) (x : L) :
    x ∈ inertiaField K A ↔
      ∀ σ : inertiaGroup K A, ((σ : decompositionGroup K A) : L ≃ₐ[K] L) x = x := by
  rw [inertiaField, IntermediateField.mem_fixedField_iff]
  constructor
  · intro h σ
    exact h ((σ : decompositionGroup K A) : L ≃ₐ[K] L)
      ⟨(σ : decompositionGroup K A), σ.property, rfl⟩
  · intro h σ hσ
    rcases hσ with ⟨τ, hτ, rfl⟩
    exact h ⟨τ, hτ⟩

/-- The inertia subgroup, viewed inside the full automorphism group, lies in
the decomposition group. -/
theorem inertiaGroupInAut_le_decompositionGroup
    (A : _root_.ValuationSubring L) :
    inertiaGroupInAut K A ≤ decompositionGroup K A := by
  rintro σ ⟨τ, _hτ, rfl⟩
  exact τ.property

/-- The ramification group as a subgroup of the full automorphism group. -/
abbrev ramificationGroupInAut (A : _root_.ValuationSubring L) :
    Subgroup (L ≃ₐ[K] L) :=
  Subgroup.map (inertiaGroupToAut (K := K) A) (ramificationGroup K A)

/-- The ramification-field definition:
the ramification field `V_w` is the fixed field of the ramification group. -/
abbrev ramificationField (A : _root_.ValuationSubring L) :
    IntermediateField K L :=
  IntermediateField.fixedField (ramificationGroupInAut K A)

/-- States the theorem `mem_ramificationField_iff`. -/
@[simp] theorem mem_ramificationField_iff
    (A : _root_.ValuationSubring L) (x : L) :
    x ∈ ramificationField K A ↔
      ∀ σ : ramificationGroup K A,
        (((σ : inertiaGroup K A) : decompositionGroup K A) : L ≃ₐ[K] L) x = x := by
  rw [ramificationField, IntermediateField.mem_fixedField_iff]
  constructor
  · intro h σ
    exact h (inertiaGroupToAut (K := K) A (σ : inertiaGroup K A))
      ⟨(σ : inertiaGroup K A), σ.property, rfl⟩
  · intro h σ hσ
    rcases hσ with ⟨τ, hτ, rfl⟩
    exact h ⟨τ, hτ⟩

/-- The ramification subgroup, viewed in `G(L/K)`, lies in inertia. -/
theorem ramificationGroupInAut_le_inertiaGroupInAut
    (A : _root_.ValuationSubring L) :
    ramificationGroupInAut K A ≤ inertiaGroupInAut K A := by
  rintro σ ⟨τ, _hτ, rfl⟩
  exact ⟨(τ : decompositionGroup K A), τ.property, rfl⟩

/-- finite Galois ramification theory:
the inertia field is contained in the ramification field. -/
theorem inertiaField_le_ramificationField
    (A : _root_.ValuationSubring L) :
    inertiaField K A ≤ ramificationField K A :=
  IntermediateField.fixedField_le
    (ramificationGroupInAut_le_inertiaGroupInAut (K := K) A)

/-- The ramification-field definition source:
the ramification field, viewed as an intermediate field over the inertia field
`T_w`. -/
abbrev ramificationFieldOverInertiaField
    (A : _root_.ValuationSubring L) :
    IntermediateField (inertiaField K A) L :=
  IntermediateField.extendScalars
    (inertiaField_le_ramificationField (K := K) A)

/-- States the theorem `ramificationFieldOverInertiaField_restrictScalars`. -/
@[simp] theorem ramificationFieldOverInertiaField_restrictScalars
    (A : _root_.ValuationSubring L) :
    (ramificationFieldOverInertiaField K A).restrictScalars K =
      ramificationField K A :=
  rfl

/-- finite Galois ramification theory:
the decomposition field is contained in the inertia field. -/
theorem decompositionField_le_inertiaField
    (A : _root_.ValuationSubring L) :
    decompositionField K A ≤ inertiaField K A :=
  IntermediateField.fixedField_le
    (inertiaGroupInAut_le_decompositionGroup (K := K) A)

/-- finite Galois ramification theory:
the decomposition field is contained in the ramification field. -/
theorem decompositionField_le_ramificationField
    (A : _root_.ValuationSubring L) :
    decompositionField K A ≤ ramificationField K A :=
  (decompositionField_le_inertiaField (K := K) A).trans
    (inertiaField_le_ramificationField (K := K) A)

/-- The ramification-field definition source:
the ramification field, viewed as an intermediate field over the decomposition
field `Z_w`.  This is the field appearing in `V_w | Z_w`. -/
abbrev ramificationFieldOverDecompositionField
    (A : _root_.ValuationSubring L) :
    IntermediateField (decompositionField K A) L :=
  IntermediateField.extendScalars
    (decompositionField_le_ramificationField (K := K) A)

/-- States the theorem `ramificationFieldOverDecompositionField_restrictScalars`. -/
@[simp] theorem ramificationFieldOverDecompositionField_restrictScalars
    (A : _root_.ValuationSubring L) :
    (ramificationFieldOverDecompositionField K A).restrictScalars K =
      ramificationField K A :=
  rfl

/-- The inertia-field definition source:
the inertia field, viewed as an intermediate field over the decomposition
field `Z_w`.  This is the field appearing in `G(T_w/Z_w)`. -/
abbrev inertiaFieldOverDecompositionField
    (A : _root_.ValuationSubring L) :
    IntermediateField (decompositionField K A) L :=
  IntermediateField.extendScalars
    (decompositionField_le_inertiaField (K := K) A)

/-- States the theorem `mem_inertiaFieldOverDecompositionField_iff`. -/
@[simp] theorem mem_inertiaFieldOverDecompositionField_iff
    (A : _root_.ValuationSubring L) (x : L) :
    x ∈ inertiaFieldOverDecompositionField K A ↔
      ∀ σ : inertiaGroup K A, ((σ : decompositionGroup K A) : L ≃ₐ[K] L) x = x := by
  rw [inertiaFieldOverDecompositionField, IntermediateField.mem_extendScalars,
    mem_inertiaField_iff]

/-- States the theorem `inertiaFieldOverDecompositionField_restrictScalars`. -/
@[simp] theorem inertiaFieldOverDecompositionField_restrictScalars
    (A : _root_.ValuationSubring L) :
    (inertiaFieldOverDecompositionField K A).restrictScalars K =
      inertiaField K A :=
  rfl

/-- The fixed-field description of decomposition source:
the decomposition group is the Galois group over its fixed field. -/
def decompositionGroupEquivGalDecompositionField_of_finiteDimensional
    [FiniteDimensional K L] (A : _root_.ValuationSubring L) :
    decompositionGroup K A ≃* (L ≃ₐ[decompositionField K A] L) :=
  IntermediateField.subgroupEquivAlgEquiv (decompositionGroup K A)

/--
States the theorem `decompositionGroupEquivGalDecompositionField_of_finiteDimensional_apply`.
-/
@[simp] theorem decompositionGroupEquivGalDecompositionField_of_finiteDimensional_apply
    [FiniteDimensional K L] (A : _root_.ValuationSubring L)
    (σ : decompositionGroup K A) (x : L) :
    decompositionGroupEquivGalDecompositionField_of_finiteDimensional (K := K) A σ x =
      ((σ : L ≃ₐ[K] L) x) :=
  rfl


section IntermediateFieldFunctoriality

variable {M : Type*} [Field M] [Algebra K M] [Algebra M L]
  [IsScalarTower K M L]

/-- Restrict scalars on automorphisms along an intermediate field
`K ⊆ M ⊆ L`.  This is the inclusion `G(L/M) -> G(L/K)` used in
scalar-restriction compatibility of ramification subgroups. -/
def restrictAutomorphismScalars : (L ≃ₐ[M] L) →* (L ≃ₐ[K] L) where
  toFun σ :=
    { σ with
      commutes' := by
        intro a
        simp [IsScalarTower.algebraMap_eq K M L, σ.commutes (algebraMap K M a)] }
  map_one' := by
    ext x
    rfl
  map_mul' σ τ := by
    ext x
    rfl

end IntermediateFieldFunctoriality

/-- The ordinary valuation-subring first-isomorphism form:
`D/I` is the range of the residue action. -/
def quotientInertiaEquivResidueActionRange
    (A : _root_.ValuationSubring L) :
    decompositionGroup K A ⧸ inertiaGroup K A ≃*
      (residueAction K A).range :=
  (QuotientGroup.quotientMulEquivOfEq
      (residueAction_ker K A).symm).trans
    (QuotientGroup.quotientKerEquivRange (residueAction K A))

/-- States the theorem `quotientInertiaEquivResidueActionRange_mk`. -/
@[simp] theorem quotientInertiaEquivResidueActionRange_mk
    (A : _root_.ValuationSubring L) (σ : decompositionGroup K A) :
    quotientInertiaEquivResidueActionRange (K := K) A
        (QuotientGroup.mk' (inertiaGroup K A) σ) =
      (residueAction K A).rangeRestrict σ :=
  rfl

end ValuationSubring
end HilbertRamification

end
end RamificationTheory
end

section
-- module Solutions.OAIQ244_DUKE.LocalClassFieldTheory_ClassFormation_CohomologyBridge
attribute [-instance] _root_.RamificationTheory.HilbertRamification.ValuationSubring.inertiaGroup_normal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

set_option autoImplicit false

namespace LocalClassFieldTheory

/-!
# The actual low-degree Tate quotients as Herbrand quotients

This file compares the concrete multiplicative Herbrand quotients from
low-degree cyclic cohomology with the Tate objects built from mathlib's actual
Galois representation on `Lˣ`.  The comparison uses the standard Galois action
on units; it does not introduce a replacement coefficient object.
-/

noncomputable section

open scoped BigOperators

open CategoryTheory

variable (K L : Type) [Field K] [Field L] [Algebra K L]

/-- The multiplicative group structure on an additive submodule quotient.
This is passed explicitly at concrete call sites to avoid rediscovering it by
unfolding the coefficient representation. -/
@[implicit_reducible]
def multiplicativeQuotientGroup
    {M : Type} [AddCommGroup M] (N : Submodule ℤ M) :
    Group (Multiplicative (M ⧸ N)) :=
  Multiplicative.group

/-- Kernel of a homomorphism into a multiplicative additive quotient, with the
codomain structure supplied directly. -/
def kernelOfAdditiveQuotientHom
    {G M : Type} [Group G] [AddCommGroup M]
    (N : Submodule ℤ M) (f : G →* Multiplicative (M ⧸ N)) : Subgroup G :=
  @MonoidHom.ker G inferInstance (Multiplicative (M ⧸ N))
    (multiplicativeQuotientGroup N).toMulOneClass f

/-- First-isomorphism-theorem comparison for a surjection onto a
multiplicative additive quotient. -/
def quotientMulEquivOfSurjectiveAdditiveQuotient
    {G M : Type} [CommGroup G] [AddCommGroup M]
    (N : Submodule ℤ M) (S : Subgroup G)
    (f : G →* Multiplicative (M ⧸ N))
    (hker : kernelOfAdditiveQuotientHom N f = S)
    (hsurj : Function.Surjective f) :
    G ⧸ S ≃* Multiplicative (M ⧸ N) := by
  letI : Group (Multiplicative (M ⧸ N)) := multiplicativeQuotientGroup N
  exact
    (QuotientGroup.quotientMulEquivOfEq hker.symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective f hsurj)

/-- Forget the type tags in an equivalence whose codomain is the
multiplicative form of an additive group. -/
def mulEquivMultiplicativeToEquiv
    {G B : Type} [Group G] [AddCommGroup B]
    (e : G ≃* Multiplicative B) : G ≃ B where
  toFun q := Multiplicative.toAdd (e q)
  invFun q := e.symm (Multiplicative.ofAdd q)
  left_inv q := e.left_inv q
  right_inv q := e.right_inv (Multiplicative.ofAdd q)

end
end LocalClassFieldTheory
end

section
-- module Solutions.OAIQ244_DUKE.LocalClassFieldTheory_ClassFormation_NormalBasisGaloisAction
attribute [-instance] _root_.RamificationTheory.HilbertRamification.ValuationSubring.inertiaGroup_normal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

set_option autoImplicit false
/-! Provides the public declarations in the `LocalClassFieldTheory.ClassFormation.NormalBasisGaloisAction` Lean module. -/

namespace LocalClassFieldTheory

open LocalFieldTheory

noncomputable section

universe uG uA u

open scoped ValuativeRel
open IsNonarchimedeanLocalField

/-- An invariant subgroup satisfies the relation-preservation condition
needed for the action on its quotient. -/
theorem quotientActionOfSubgroupStable
    (G : Type uG) (A : Type uA) [Group G] [CommGroup A]
    [MulDistribMulAction G A] (V : Subgroup A)
    (hstable : ∀ (g : G) (a : A), a ∈ V → g • a ∈ V) :
    MulAction.QuotientAction G V where
  inv_mul_mem g a b hab := by
    have hsmul : g • (a⁻¹ * b) ∈ V := hstable g (a⁻¹ * b) hab
    simpa [MulDistribMulAction.smul_mul, map_inv] using hsmul

/-- Descend an action by group automorphisms to the quotient by an invariant
subgroup. -/
@[implicit_reducible]
def quotientMulDistribMulActionOfSubgroupStable
    (G : Type uG) (A : Type uA) [Group G] [CommGroup A]
    [MulDistribMulAction G A] (V : Subgroup A)
    (hstable : ∀ (g : G) (a : A), a ∈ V → g • a ∈ V) :
    MulDistribMulAction G (A ⧸ V) := by
  letI : MulAction.QuotientAction G V :=
    quotientActionOfSubgroupStable G A V hstable
  exact
    { smul := (· • ·)
      one_smul := one_smul G
      mul_smul := mul_smul
      smul_mul := by
        intro g x y
        refine Quotient.inductionOn₂' x y ?_
        intro a b
        exact congrArg QuotientGroup.mk
          (MulDistribMulAction.smul_mul g a b)
      smul_one := by
        intro g
        exact congrArg QuotientGroup.mk
          (MulDistribMulAction.smul_one g) }

variable (K L : Type u) [Field K] [Field L] [Algebra K L]
  [FiniteDimensional K L] [IsGalois K L]
  [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]

variable [ValuativeRel L]
  [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]
  [IsIntegralClosure 𝒪[L] 𝒪[K] L]

/-- Inclusion of a chosen normal-basis principal-unit subgroup into all
integer units. -/
def chosenNormalBasisPrincipalUnitSubgroupInclusion
    (V : Subgroup 𝒪[L]ˣ) : V →* 𝒪[L]ˣ :=
  V.subtype

/-- Projection of integer units to the quotient by `V^n`. -/
def chosenNormalBasisIntegerUnitsQuotientMap
    (V : Subgroup 𝒪[L]ˣ) : 𝒪[L]ˣ →* (𝒪[L]ˣ ⧸ V) :=
  QuotientGroup.mk' V

end
end LocalClassFieldTheory
end

section
-- module Solutions.OAIQ244_DUKE.LocalClassFieldTheory_ClassFormation_NormalBasisInfiniteProduct
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

set_option autoImplicit false
/-! Provides the public declarations in the `LocalClassFieldTheory.ClassFormation.NormalBasisInfiniteProduct` Lean module. -/

namespace LocalClassFieldTheory

open LocalFieldTheory

noncomputable section

universe u

open scoped BigOperators
open scoped ValuativeRel
open Filter IsNonarchimedeanLocalField

variable (K L : Type u) [Field K] [Field L] [Algebra K L]
  [FiniteDimensional K L] [IsGalois K L]
  [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [ValuativeRel L]
  [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]

/-- Finite products of a normal-basis correction sequence. -/
def chosenNormalBasisPrincipalUnitCorrectionProduct (z : Nat → 𝒪[L]ˣ) :
    Nat → 𝒪[L]ˣ
  | 0 => 1
  | d + 1 => chosenNormalBasisPrincipalUnitCorrectionProduct z d * z d

end
end LocalClassFieldTheory
end

section
-- module Solutions.OAIQ244_DUKE.LocalClassFieldTheory_ClassFormation_FilteredLiftingSequence
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

set_option autoImplicit false

namespace LocalClassFieldTheory

/-!
# Recursive correction sequences

This file isolates the dependent-choice bookkeeping in the infinite-product
argument of the local class-field-axiom theorem.  A one-step lift in a filtered commutative
group produces compatible correction and remainder sequences.  No
cohomological input is hidden here: the existence of each one-step lift is an
explicit parameter, discharged for the normal-basis filtration in the next
file.
-/

noncomputable section

universe u

/-- Left-to-right finite products of a correction sequence. -/
def filteredCorrectionProduct {A : Type u} [Monoid A] (z : Nat → A) : Nat → A
  | 0 => 1
  | d + 1 => filteredCorrectionProduct z d * z d

/-- The empty correction product is the identity. -/
@[simp]
theorem filteredCorrectionProduct_zero {A : Type u} [Monoid A] (z : Nat → A) :
    filteredCorrectionProduct z 0 = 1 :=
  rfl

/-- A successor correction product appends the correction at the preceding index. -/
@[simp]
theorem filteredCorrectionProduct_succ {A : Type u} [Monoid A]
    (z : Nat → A) (d : Nat) :
    filteredCorrectionProduct z (d + 1) = filteredCorrectionProduct z d * z d :=
  rfl

/-- A remainder at depth `n + i`, carrying both its filtration condition and
the condition that must be preserved by one-step lifting. -/
structure FilteredLiftState (A : Type u) (P : Nat → A → Prop)
    (R : A → Prop) (n i : Nat) where
  /-- The current remainder at relative depth `i`. -/
  value : A
  /-- The current remainder lies in filtration level `n + i`. -/
  mem : P (n + i) value
  /-- The current remainder satisfies the condition preserved by each lifting step. -/
  stable : R value

/-- One correction step `a_i = F(b_i) a_(i+1)`. -/
structure FilteredLiftStep (A : Type u) [CommGroup A]
    (P : Nat → A → Prop) (R : A → Prop) (F : A →* A)
    (n i : Nat) (s : FilteredLiftState A P R n i) where
  /-- The correction chosen at relative depth `i`. -/
  correction : A
  /-- The correction lies in the same filtration level `n + i` as the current remainder. -/
  correction_mem : P (n + i) correction
  /-- The remainder state after removing the current correction, one level deeper. -/
  next : FilteredLiftState A P R n (i + 1)
  /-- The current remainder is the image of the correction under `F` times the next remainder. -/
  equation : s.value = F correction * next.value

/-- The recursively chosen remainder sequence. -/
noncomputable def chosenFilteredLiftStateSequence
    (A : Type u) [CommGroup A] (P : Nat → A → Prop) (R : A → Prop)
    (F : A →* A) (n : Nat) (initial : FilteredLiftState A P R n 0)
    (step : ∀ i (s : FilteredLiftState A P R n i),
      Nonempty (FilteredLiftStep A P R F n i s)) :
    (i : Nat) → FilteredLiftState A P R n i
  | 0 => initial
  | i + 1 =>
      (Classical.choice
        (step i (chosenFilteredLiftStateSequence A P R F n initial step i))).next

/-- The recursively chosen correction at depth `n + i`. -/
noncomputable def chosenFilteredLiftCorrectionSequence
    (A : Type u) [CommGroup A] (P : Nat → A → Prop) (R : A → Prop)
    (F : A →* A) (n : Nat) (initial : FilteredLiftState A P R n 0)
    (step : ∀ i (s : FilteredLiftState A P R n i),
      Nonempty (FilteredLiftStep A P R F n i s)) (i : Nat) : A :=
  (Classical.choice
    (step i (chosenFilteredLiftStateSequence A P R F n initial step i))).correction

/-- The chosen filtered-lift sequence starts at the supplied initial state. -/
@[simp]
theorem chosenFilteredLiftStateSequence_zero
    (A : Type u) [CommGroup A] (P : Nat → A → Prop) (R : A → Prop)
    (F : A →* A) (n : Nat) (initial : FilteredLiftState A P R n 0)
    (step : ∀ i (s : FilteredLiftState A P R n i),
      Nonempty (FilteredLiftStep A P R F n i s)) :
    chosenFilteredLiftStateSequence A P R F n initial step 0 = initial :=
  rfl

/-- Each successor state is the next state of the chosen lifting step. -/
@[simp]
theorem chosenFilteredLiftStateSequence_succ
    (A : Type u) [CommGroup A] (P : Nat → A → Prop) (R : A → Prop)
    (F : A →* A) (n : Nat) (initial : FilteredLiftState A P R n 0)
    (step : ∀ i (s : FilteredLiftState A P R n i),
      Nonempty (FilteredLiftStep A P R F n i s)) (i : Nat) :
    chosenFilteredLiftStateSequence A P R F n initial step (i + 1) =
      (Classical.choice
        (step i (chosenFilteredLiftStateSequence A P R F n initial step i))).next :=
  rfl

/-- Every chosen correction lies at the advertised filtration level. -/
theorem chosenFilteredLiftCorrectionSequence_mem
    (A : Type u) [CommGroup A] (P : Nat → A → Prop) (R : A → Prop)
    (F : A →* A) (n : Nat) (initial : FilteredLiftState A P R n 0)
    (step : ∀ i (s : FilteredLiftState A P R n i),
      Nonempty (FilteredLiftStep A P R F n i s)) (i : Nat) :
    P (n + i)
      (chosenFilteredLiftCorrectionSequence A P R F n initial step i) :=
  (Classical.choice
    (step i (chosenFilteredLiftStateSequence A P R F n initial step i))).correction_mem

/-- The defining one-step recurrence for the chosen sequences. -/
theorem chosenFilteredLiftStateSequence_equation
    (A : Type u) [CommGroup A] (P : Nat → A → Prop) (R : A → Prop)
    (F : A →* A) (n : Nat) (initial : FilteredLiftState A P R n 0)
    (step : ∀ i (s : FilteredLiftState A P R n i),
      Nonempty (FilteredLiftStep A P R F n i s)) (i : Nat) :
    (chosenFilteredLiftStateSequence A P R F n initial step i).value =
      F (chosenFilteredLiftCorrectionSequence A P R F n initial step i) *
        (chosenFilteredLiftStateSequence A P R F n initial step (i + 1)).value := by
  exact (Classical.choice
    (step i (chosenFilteredLiftStateSequence A P R F n initial step i))).equation

/-- The initial remainder equals the image under `F` of the first `d`
corrections, times the depth-`d` remainder. -/
theorem filteredLift_initial_eq_correctionProduct_mul_state
    (A : Type u) [CommGroup A] (P : Nat → A → Prop) (R : A → Prop)
    (F : A →* A) (n : Nat) (initial : FilteredLiftState A P R n 0)
    (step : ∀ i (s : FilteredLiftState A P R n i),
      Nonempty (FilteredLiftStep A P R F n i s)) (d : Nat) :
    initial.value =
      F (filteredCorrectionProduct
          (chosenFilteredLiftCorrectionSequence A P R F n initial step) d) *
        (chosenFilteredLiftStateSequence A P R F n initial step d).value := by
  induction d with
  | zero =>
      rw [filteredCorrectionProduct_zero, chosenFilteredLiftStateSequence_zero,
        map_one, one_mul]
  | succ d ih =>
      rw [filteredCorrectionProduct_succ, map_mul]
      rw [mul_assoc, ← chosenFilteredLiftStateSequence_equation
        A P R F n initial step d]
      exact ih

end
end LocalClassFieldTheory
end

section
-- module Solutions.OAIQ244_DUKE.LocalClassFieldTheory_ClassFormation_NormalBasis
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

set_option autoImplicit false
/-! Provides the public declarations in the `LocalClassFieldTheory.ClassFormation.NormalBasis` Lean module. -/

namespace LocalClassFieldTheory

open LocalFieldTheory

noncomputable section

universe u

open scoped ValuativeRel

variable (K L : Type u) [Field K] [ValuativeRel K] [Field L]
  [Algebra K L] [FiniteDimensional K L] [IsGalois K L]

section GradedCoordinates

variable [TopologicalSpace K] [IsNonarchimedeanLocalField K]

/-- Coordinate functions all of whose values lie in the maximal ideal of
`𝒪_K`. -/
def chosenNormalBasisCoordinateMaximalSubmodule :
    Submodule 𝒪[K] (Gal(L / K) → 𝒪[K]) :=
  Submodule.pi Set.univ (fun _ => (𝓂[K] : Ideal 𝒪[K]))

/-! ### The actual `Gal(L / K)` action and right-regular equivariance -/

end GradedCoordinates

end
end LocalClassFieldTheory
end

section
-- module Solutions.OAIQ244_DUKE.LocalClassFieldTheory_Finite_LocalReciprocity_FiniteExtensionClassFieldAxiom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

set_option autoImplicit false

namespace LocalClassFieldTheory

open LocalFieldTheory

open ValuationTheory

/-!
# Finite local reciprocity

The local class-field-axiom theorem on finite extensions of a local field.

Mathlib's local-field predicate is topology-first, while the local class-field-axiom theorem also
needs a compatible local-field structure on the finite extension.  This file
constructs that structure from the spectral norm.  In particular, the target
valuation ring is proved integral over the base valuation ring; no local-field
structure on the target is assumed.
-/

noncomputable section

open scoped NNReal ValuativeRel

/-- Finite-cardinality data for the two actual unit Tate groups.  Bundling the
`H⁰` finiteness proof keeps `Nat.card` honest when the local-field
structure on the extension is constructed inside a theorem. -/
structure UnitsTateCardinalityData
    (K L : Type) [Field K] [Field L] [Algebra K L] [FiniteDimensional K L] where
  /-- Finiteness of the degree-zero Tate cohomology group of the unit representation. -/
  finiteH0 : Finite (tateCohomology (Rep.ofAlgebraAutOnUnits K L) 0)
  /-- The degree-zero unit Tate group has cardinality equal to the extension degree. -/
  cardH0 :
    letI := finiteH0
    Nat.card (tateCohomology (Rep.ofAlgebraAutOnUnits K L) 0) = Module.finrank K L
  /-- The degree-minus-one unit Tate group is trivial at the level of cardinality. -/
  cardHminusOne : Nat.card (tateCohomology (Rep.ofAlgebraAutOnUnits K L) (-1)) = 1

end
end LocalClassFieldTheory
end

section
-- module Solutions.OAIQ244_DUKE.Valuation_Completion_FiniteProductNormTrace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

set_option autoImplicit false

/-!
# Norms and traces on finite dependent products

These algebraic lemmas are the finite-product linear algebra used in
tensor-product norm and trace formulas.  Mathlib has the binary trace formula and the
determinant of a binary product map; the dependent finite-product versions
are recorded here so that the local factors are allowed to have different
field degrees.
-/

noncomputable section

namespace ValuationTheory
namespace Completion

universe u v w

open Module

/-- Multiplication on a binary product is the product of the two
multiplication endomorphisms. -/
theorem algebra_lmul_prod_eq_prodMap
    {R S T : Type*} [CommRing R] [CommRing S] [CommRing T]
    [Algebra R S] [Algebra R T] (x : S × T) :
    Algebra.lmul R (S × T) x =
      (Algebra.lmul R S x.1).prodMap (Algebra.lmul R T x.2) := by
  apply LinearMap.ext
  intro y
  rcases y with ⟨y, z⟩
  rfl

/-- The algebra norm on a binary product is the product of the component
norms. -/
theorem algebra_norm_prod_apply
    {R S T : Type*} [CommRing R] [CommRing S] [CommRing T]
    [Algebra R S] [Algebra R T]
    [Module.Free R S] [Module.Finite R S]
    [Module.Free R T] [Module.Finite R T]
    (x : S × T) :
    Algebra.norm R x = Algebra.norm R x.1 * Algebra.norm R x.2 := by
  rw [Algebra.norm_apply, algebra_lmul_prod_eq_prodMap,
    LinearMap.det_prodMap, ← Algebra.norm_apply, ← Algebra.norm_apply]

end Completion
end ValuationTheory

end
end

section
-- module Solutions.OAIQ244_DUKE.Ramification_GaloisValuation_ClosedFixingSubgroup
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

set_option autoImplicit false

/-!
# Closed fixing subgroups

This module packages the closed subgroup attached to an intermediate field in
the Krull topology.
-/

noncomputable section

namespace RamificationTheory

/-- The closed fixing subgroup attached to an intermediate field. -/
@[implicit_reducible]
noncomputable def closedFixingSubgroup
    (k Ω : Type*) [Field k] [Field Ω] [Algebra k Ω] [IsGalois k Ω]
    (K : IntermediateField k Ω) : ClosedSubgroup Gal(Ω/k) :=
  ⟨K.fixingSubgroup, InfiniteGalois.fixingSubgroup_isClosed K⟩

end RamificationTheory
end
end

section
-- module Solutions.OAIQ244_DUKE.LocalClassFieldTheory_Finite_LocalReciprocity_AbsoluteUnitsFixedField
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

set_option autoImplicit false

namespace LocalClassFieldTheory

open RamificationTheory

/-!
# Finite local reciprocity: Galois units and fixed fields

For local reciprocity the coefficient module in the abstract class formation is
`A = (K^sep)ˣ`.  This file identifies its subgroup fixed by the actual closed
fixing subgroup of an intermediate field `E` with the image of `Eˣ`.

The result is stated for an arbitrary Galois ambient extension.  In particular
it applies to `SeparableClosure K / K` for every field `K`; no perfectness,
local-field, or finite-dimensional hypothesis is needed.  Using the separable
closure is essential in positive characteristic: the fixed field of
`Aut(K^alg/K)` inside `K^alg` need not be `K` when `K` is imperfect.
-/

noncomputable section

variable (K Ω : Type) [Field K] [Field Ω] [Algebra K Ω]

/-- The actual Galois representation on `Ωˣ`, written additively for the
group-cohomology API. -/
abbrev galoisAmbientUnitsRep : Rep ℤ (Gal(Ω / K)) :=
  Rep.ofAlgebraAutOnUnits K Ω

/-- Inclusion of the units of an intermediate field into the units of the
chosen Galois ambient field, in additive notation. -/
def intermediateFieldUnitsToGaloisAmbient
    (E : IntermediateField K Ω) :
    Additive Eˣ →+ Additive Ωˣ :=
  MonoidHom.toAdditive (Units.map E.val.toRingHom)

/-- States the theorem `intermediateFieldUnitsToGaloisAmbient_apply`. -/
@[simp]
theorem intermediateFieldUnitsToGaloisAmbient_apply
    (E : IntermediateField K Ω) (x : Eˣ) :
    intermediateFieldUnitsToGaloisAmbient K Ω E (Additive.ofMul x) =
      Additive.ofMul (Units.map E.val.toRingHom x) :=
  rfl

end
end LocalClassFieldTheory
end

section
-- module Solutions.OAIQ244_DUKE.LocalClassFieldTheory_Finite_LocalReciprocity_FiniteGaloisRealization
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

set_option autoImplicit false

namespace LocalClassFieldTheory
open RamificationTheory

/-!
# Finite local reciprocity: realizing finite Galois extensions in a separable closure

Every finite Galois extension `L/K` is embedded into the chosen separable
closure of `K`.  Its image supplies the concrete closed subgroup used by the
abstract class-field theory.  The resulting abstract fixed coefficient group
is `Lˣ`, and the resulting abstract extension quotient is the actual
`Gal(L/K)`.

No perfectness hypothesis is imposed; this includes equal-characteristic
local fields such as finite extensions of `𝔽_q((t))`.
-/

noncomputable section

variable (K L : Type) [Field K] [Field L] [Algebra K L]
  [FiniteDimensional K L] [IsGalois K L]

/-! ## Realization relative to an explicit embedding -/

/-- The embedded copy of `L` determined by an explicit embedding into the
fixed separable closure.  Keeping the embedding visible is what makes the
canonicity argument in the finite local reciprocity theorem meaningful. -/
def finiteGaloisFieldRangeOfEmbedding
    (i : L →ₐ[K] SeparableClosure K) :
    IntermediateField K (SeparableClosure K) :=
  AlgHom.fieldRange i

/-- An explicit embedding identifies `L` with its field range. -/
def finiteGaloisFieldRangeEquivOfEmbedding
    (i : L →ₐ[K] SeparableClosure K) :
    L ≃ₐ[K] finiteGaloisFieldRangeOfEmbedding K L i :=
  AlgEquiv.ofInjectiveField i

/-- The image of an embedded finite Galois extension is again Galois over the base field. -/
noncomputable instance finiteGaloisFieldRangeOfEmbedding_isGalois
    (i : L →ₐ[K] SeparableClosure K) :
    IsGalois K (finiteGaloisFieldRangeOfEmbedding K L i) :=
  IsGalois.of_algEquiv (finiteGaloisFieldRangeEquivOfEmbedding K L i)

/-- The image of an embedded finite extension is finite-dimensional over the base field. -/
noncomputable instance finiteGaloisFieldRangeOfEmbedding_finiteDimensional
    (i : L →ₐ[K] SeparableClosure K) :
    FiniteDimensional K (finiteGaloisFieldRangeOfEmbedding K L i) :=
  (finiteGaloisFieldRangeEquivOfEmbedding K L i).toLinearEquiv.finiteDimensional

/-! ## The chosen realization -/

end
end LocalClassFieldTheory
end

section
-- module Solutions.OAIQ244_DUKE.LocalClassFieldTheory_Finite_LocalReciprocity_IntrinsicAbsoluteData
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

set_option autoImplicit false

/-!
# Intrinsic absolute Galois data

This module packages the absolute Galois group of a field, its integral unit
representation, and its distinguished abstract base field using the chosen
separable closure.
-/

noncomputable section

namespace LocalClassFieldTheory

open RamificationTheory

/-- The absolute Galois group of a field, formed using its chosen separable closure. -/
abbrev intrinsicAbsoluteGalois
    (F : Type) [Field F] :=
  Gal(SeparableClosure F / F)
end LocalClassFieldTheory
end
end

section
-- module Solutions.OAIQ244_DUKE.LocalClassFieldTheory_Finite_LocalReciprocity_SeparableUnitsNorm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

set_option autoImplicit false

namespace LocalClassFieldTheory
open RamificationTheory

open LocalFieldTheory

/-!
# Finite local reciprocity: the abstract norm on separable-closure units

The coefficient module in local class field theory is the unit group of a
separable closure.  This file compares the norm defined in the abstract class-formation framework by a
sum over abstract Galois cosets with the ordinary field norm.  The comparison
is proved first for an arbitrary (possibly infinite) Galois ambient field, so
it does not require the ground field to be perfect.
-/

noncomputable section

open scoped BigOperators

variable (K : Type) (Ω : Type) [Field K] [Field Ω] [Algebra K Ω]
  [IsGalois K Ω]

section EmbeddedFiniteGaloisExtension

variable (L : Type) [Field L] [Algebra K L]
  [FiniteDimensional K L] [IsGalois K L]
  (i : L →ₐ[K] Ω)

noncomputable local instance embeddedFieldRangeFiniteDimensional :
    FiniteDimensional K (AlgHom.fieldRange i) :=
  (AlgEquiv.ofInjectiveField i).toLinearEquiv.finiteDimensional

noncomputable local instance embeddedFieldRangeIsGalois :
    IsGalois K (AlgHom.fieldRange i) :=
  IsGalois.of_algEquiv (AlgEquiv.ofInjectiveField i)

end EmbeddedFiniteGaloisExtension

end
end LocalClassFieldTheory
end

section
-- module Solutions.OAIQ244_DUKE.LocalClassFieldTheory_Finite_LocalReciprocity_FiniteAbstractFixedField
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

set_option autoImplicit false

namespace LocalClassFieldTheory
open RamificationTheory

/-!
# Finite local reciprocity: finite abstract fields inside a separable closure

The abstract fields to which the class field axiom is applied are the open
closed subgroups of the absolute Galois group.  This file turns the explicit
finite-index witness from the abstract class-formation data into the corresponding finite fixed
field.  It is the field-theoretic input needed before the local class-field-axiom theorem can be
applied.
-/

noncomputable section

variable (k Ω : Type) [Field k] [Field Ω] [Algebra k Ω] [IsGalois k Ω]

/-- The concrete fixed field represented by an abstract closed subgroup. -/
abbrev abstractFixedField (H : ClosedSubgroup (Gal(Ω / k))) :
    IntermediateField k Ω :=
  IntermediateField.fixedField H.toSubgroup

omit [IsGalois k Ω] in
/-- Inclusion of abstract subgroups reverses to inclusion of their concrete
fixed fields. -/
theorem abstractFixedField_le {K L : ClosedSubgroup (Gal(Ω / k))}
    (hLK : L.toSubgroup ≤ K.toSubgroup) :
    abstractFixedField k Ω K ≤ abstractFixedField k Ω L :=
  IntermediateField.fixedField_le hLK

/-- The abstract subgroup representing a fixed field is canonically the
absolute Galois group of the ambient extension over that fixed field. -/
def abstractSubgroupEquivGaloisGroup
    (H : ClosedSubgroup (Gal(Ω / k))) :
    H.toSubgroup ≃* Gal(Ω / abstractFixedField k Ω H) :=
  (MulEquiv.subgroupCongr
      (InfiniteGalois.fixingSubgroup_fixedField H).symm).trans
    (IntermediateField.fixingSubgroupEquiv (abstractFixedField k Ω H))

/-- States the theorem `abstractSubgroupEquivGaloisGroup_apply`. -/
@[simp]
theorem abstractSubgroupEquivGaloisGroup_apply
    (H : ClosedSubgroup (Gal(Ω / k))) (σ : H.toSubgroup) (x : Ω) :
    abstractSubgroupEquivGaloisGroup k Ω H σ x = σ.1 x :=
  rfl

/-- The upper fixed field, regarded as an intermediate field over the lower
fixed field in a relative abstract extension. -/
abbrev abstractRelativeFixedField
    {K L : ClosedSubgroup (Gal(Ω / k))}
    (hLK : L.toSubgroup ≤ K.toSubgroup) :
    IntermediateField (abstractFixedField k Ω K) Ω :=
  IntermediateField.extendScalars (abstractFixedField_le k Ω hLK)

end
end LocalClassFieldTheory
end

section
-- module Solutions.OAIQ244_DUKE.LocalClassFieldTheory_Finite_LocalReciprocity_TateTransport
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

set_option autoImplicit false

namespace LocalClassFieldTheory

/-!
# The local class-field-axiom theorem: transport of cyclic Tate complexes

The fixed-field realization of an abstract extension changes both the
presentation of its cyclic group and the presentation of its coefficient
module.  This file records the two honest functorial comparisons needed to
transport the local class-field-axiom theorem: reindexing a representation along a group
isomorphism and replacing a representation by an isomorphic one.
-/

noncomputable section

open CategoryTheory

section CyclicGenerator

variable {Q P : Type} [Group Q] [Group P]

/-- A generator remains a generator after applying a group isomorphism. -/
theorem map_cyclicGenerator (e : Q ≃* P) (g : Q)
    (hg : ∀ q : Q, q ∈ Subgroup.zpowers g) :
    ∀ p : P, p ∈ Subgroup.zpowers (e g) := by
  intro p
  obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp (hg (e.symm p))
  apply Subgroup.mem_zpowers_iff.mpr
  refine ⟨n, ?_⟩
  rw [← map_zpow e, hn, e.apply_symm_apply]

end CyclicGenerator

section GroupEquiv

variable {R Q P : Type} [CommRing R]
  [CommGroup Q] [CommGroup P] [Fintype Q] [Fintype P]

theorem res_norm_eq (e : Q ≃* P) (A : Rep R P) :
    let Ares : Rep R Q :=
      Rep.res e.toMonoidHom A
    ModuleCat.ofHom Ares.norm.hom.toLinearMap =
      ModuleCat.ofHom A.norm.hom.toLinearMap := by
  let Ares : Rep R Q :=
    Rep.res e.toMonoidHom A
  apply congrArg ModuleCat.ofHom
  change Representation.norm Ares.ρ = Representation.norm A.ρ
  simp only [Representation.norm]
  exact Fintype.sum_equiv e.toEquiv
    (fun q : Q => Ares.ρ q)
    (fun p : P => A.ρ p) (fun _ => rfl)

/-- Reindexing along a group isomorphism preserves the cyclic `H⁰`
short complex. -/
def normHomCompSubResEquivIso
    (e : Q ≃* P) (A : Rep R P) (g : Q) :
    Rep.FiniteCyclicGroup.normHomCompSub
        (Rep.res e.toMonoidHom A) g ≅
      Rep.FiniteCyclicGroup.normHomCompSub A (e g) := by
  let Ares : Rep R Q :=
    Rep.res e.toMonoidHom A
  let i : ModuleCat.of R Ares.V ≅ ModuleCat.of R A.V := Iso.refl _
  refine ShortComplex.isoMk i i i ?_ ?_
  · simpa [Ares, i] using (res_norm_eq e A).symm
  · rfl

/-- Reindexing along a group isomorphism preserves the cyclic `H⁻¹`
short complex. -/
def subCompNormHomResEquivIso
    (e : Q ≃* P) (A : Rep R P) (g : Q) :
    Rep.FiniteCyclicGroup.subCompNormHom
        (Rep.res e.toMonoidHom A) g ≅
      Rep.FiniteCyclicGroup.subCompNormHom A (e g) := by
  let Ares : Rep R Q :=
    Rep.res e.toMonoidHom A
  let i : ModuleCat.of R Ares.V ≅ ModuleCat.of R A.V := Iso.refl _
  refine ShortComplex.isoMk i i i ?_ ?_
  · rfl
  · simpa [Ares, i] using (res_norm_eq e A).symm

/-- Homology-level group-reindexing comparison in degree zero. -/
def normHomCompSubHomologyResEquivIso
    (e : Q ≃* P) (A : Rep R P) (g : Q) :
    (Rep.FiniteCyclicGroup.normHomCompSub
        (Rep.res e.toMonoidHom A) g).homology ≅
      (Rep.FiniteCyclicGroup.normHomCompSub A (e g)).homology :=
  ShortComplex.homologyMapIso (normHomCompSubResEquivIso e A g)

/-- Homology-level group-reindexing comparison in degree minus one. -/
def subCompNormHomHomologyResEquivIso
    (e : Q ≃* P) (A : Rep R P) (g : Q) :
    (Rep.FiniteCyclicGroup.subCompNormHom
        (Rep.res e.toMonoidHom A) g).homology ≅
      (Rep.FiniteCyclicGroup.subCompNormHom A (e g)).homology :=
  ShortComplex.homologyMapIso (subCompNormHomResEquivIso e A g)

end GroupEquiv

section RepresentationIso

variable {R Q : Type} [CommRing R] [CommGroup Q] [Fintype Q]

/-- Isomorphic representations have isomorphic cyclic `H⁰` short
complexes. -/
def normHomCompSubIsoOfRepIso
    {M N : Rep R Q} (e : M ≅ N) (g : Q) :
    Rep.FiniteCyclicGroup.normHomCompSub M g ≅
      Rep.FiniteCyclicGroup.normHomCompSub N g := by
  let i : ModuleCat.of R M.V ≅ ModuleCat.of R N.V :=
    (forget₂ (Rep R Q) (ModuleCat R)).mapIso e
  refine ShortComplex.isoMk i i i ?_ ?_
  · have h := congrArg
      (fun f : M ⟶ N => ModuleCat.ofHom f.hom.toLinearMap)
      (Rep.norm_comm e.hom)
    simpa [i, Rep.norm] using h
  · have hrep :
        e.hom ≫ (Rep.applyAsHom N g - 𝟙 N) =
          (Rep.applyAsHom M g - 𝟙 M) ≫ e.hom := by
      rw [Preadditive.comp_sub, Preadditive.sub_comp, Category.comp_id,
        Category.id_comp, Rep.applyAsHom_comm]
    let F := forget₂ (Rep R Q) (ModuleCat R)
    change F.map e.hom ≫ F.map (Rep.applyAsHom N g - 𝟙 N) =
      F.map (Rep.applyAsHom M g - 𝟙 M) ≫ F.map e.hom
    rw [← F.map_comp, ← F.map_comp, hrep]

/-- Isomorphic representations have isomorphic cyclic `H⁻¹` short
complexes. -/
def subCompNormHomIsoOfRepIso
    {M N : Rep R Q} (e : M ≅ N) (g : Q) :
    Rep.FiniteCyclicGroup.subCompNormHom M g ≅
      Rep.FiniteCyclicGroup.subCompNormHom N g := by
  let i : ModuleCat.of R M.V ≅ ModuleCat.of R N.V :=
    (forget₂ (Rep R Q) (ModuleCat R)).mapIso e
  refine ShortComplex.isoMk i i i ?_ ?_
  · have hrep :
        e.hom ≫ (Rep.applyAsHom N g - 𝟙 N) =
          (Rep.applyAsHom M g - 𝟙 M) ≫ e.hom := by
      rw [Preadditive.comp_sub, Preadditive.sub_comp, Category.comp_id,
        Category.id_comp, Rep.applyAsHom_comm]
    let F := forget₂ (Rep R Q) (ModuleCat R)
    change F.map e.hom ≫ F.map (Rep.applyAsHom N g - 𝟙 N) =
      F.map (Rep.applyAsHom M g - 𝟙 M) ≫ F.map e.hom
    rw [← F.map_comp, ← F.map_comp, hrep]
  · have h := congrArg
      (fun f : M ⟶ N => ModuleCat.ofHom f.hom.toLinearMap)
      (Rep.norm_comm e.hom)
    simpa [i, Rep.norm] using h

/-- Homology-level representation-isomorphism comparison in degree zero. -/
def normHomCompSubHomologyIsoOfRepIso
    {M N : Rep R Q} (e : M ≅ N) (g : Q) :
    (Rep.FiniteCyclicGroup.normHomCompSub M g).homology ≅
      (Rep.FiniteCyclicGroup.normHomCompSub N g).homology :=
  ShortComplex.homologyMapIso (normHomCompSubIsoOfRepIso e g)

/-- Homology-level representation-isomorphism comparison in degree
minus one. -/
def subCompNormHomHomologyIsoOfRepIso
    {M N : Rep R Q} (e : M ≅ N) (g : Q) :
    (Rep.FiniteCyclicGroup.subCompNormHom M g).homology ≅
      (Rep.FiniteCyclicGroup.subCompNormHom N g).homology :=
  ShortComplex.homologyMapIso (subCompNormHomIsoOfRepIso e g)

end RepresentationIso

end
end LocalClassFieldTheory
end

section
-- module Solutions.OAIQ244_DUKE.LocalClassFieldTheory_Finite_LocalReciprocity_SeparableNormProduct
attribute [-instance] _root_.LocalClassFieldTheory.finiteGaloisFieldRangeOfEmbedding_finiteDimensional
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

set_option autoImplicit false

/-!
# Separable field norms as products of embeddings

For a finite separable extension, the field norm becomes the product over all
base-field embeddings after mapping into a separably closed ambient field.
The ambient field need not be a normal extension of the base field.
-/

noncomputable section

open scoped BigOperators

namespace LocalClassFieldTheory

noncomputable local instance finiteSeparableAlgHomFintypeForNormProduct
    {k E T : Type} [Field k] [Field E] [Field T]
    [Algebra k E] [Algebra k T]
    [FiniteDimensional k E] [Algebra.IsSeparable k E] :
    Fintype (E →ₐ[k] T) :=
  PowerBasis.AlgHom.fintype (Field.powerBasisOfFiniteOfSeparable k E)

/-- The embeddings of a finite separable tower above a power-basis generator
split into embeddings of the lower field and their extensions. -/
theorem prod_embeddings_algebraMap_powerBasisGen_eq
    (k Ω : Type) [Field k] [Field Ω] [Algebra k Ω] [IsSepClosed Ω]
    {L E : Type} [Field L] [Field E]
    [Algebra k L] [Algebra k E] [Algebra L E] [IsScalarTower k L E]
    [FiniteDimensional k L] [Algebra.IsSeparable k L]
    [Algebra.IsSeparable k E] [FiniteDimensional k E]
    (pb : PowerBasis k L) :
    ∏ σ : E →ₐ[k] Ω, σ (algebraMap L E pb.gen) =
      ((@Finset.univ (L →ₐ[k] Ω) (PowerBasis.AlgHom.fintype pb)).prod
        (fun σ => σ pb.gen)) ^ Module.finrank L E := by
  have : FiniteDimensional L E := FiniteDimensional.right k L E
  have : Algebra.IsSeparable L E :=
    Algebra.isSeparable_tower_top_of_isSeparable k L E
  let : Fintype (L →ₐ[k] Ω) := PowerBasis.AlgHom.fintype pb
  rw [Fintype.prod_equiv algHomEquivSigma
    (fun σ : E →ₐ[k] Ω => σ (algebraMap L E pb.gen))
    (fun σ => σ.1 pb.gen)]
  rw [← Finset.univ_sigma_univ, Finset.prod_sigma, ← Finset.prod_pow]
  · refine Finset.prod_congr rfl fun σ _ => ?_
    let : Algebra L Ω := σ.toRingHom.toAlgebra
    simp_rw [Finset.prod_const]
    congr
    rw [Finset.card_univ, Fintype.card_eq_nat_card]
    exact AlgHom.natCard_of_splits L E Ω (fun x =>
      IsSepClosed.splits_codomain _ (Algebra.IsSeparable.isSeparable L x))
  · intro σ
    change σ (algebraMap L E pb.gen) =
      (σ.comp (IsScalarTower.toAlgHom k L E)) pb.gen
    exact (AlgHom.comp_apply σ (IsScalarTower.toAlgHom k L E) pb.gen).symm

/-- Mapping the norm of an element of a finite separable extension into a
separably closed field gives the product of all base-field embeddings. -/
theorem algebraMap_norm_eq_prod_embeddings_of_isSepClosed
    (k Ω E : Type) [Field k] [Field Ω] [Field E]
    [Algebra k Ω] [IsSepClosed Ω] [Algebra k E]
    [FiniteDimensional k E] [Algebra.IsSeparable k E]
    (x : E) :
    algebraMap k Ω (Algebra.norm k x) = ∏ σ : E →ₐ[k] Ω, σ x := by
  have hx := Algebra.IsSeparable.isIntegral k x
  let : Algebra.IsSeparable k
      (IntermediateField.adjoin k ({x} : Set E)) :=
    Algebra.isSeparable_tower_bot_of_isSeparable k
      (IntermediateField.adjoin k ({x} : Set E)) E
  rw [Algebra.norm_eq_norm_adjoin k x, map_pow,
    ← IntermediateField.adjoin.powerBasis_gen hx,
    Algebra.norm_eq_prod_embeddings_gen Ω
      (IntermediateField.adjoin.powerBasis hx)
      (IsSepClosed.splits_codomain _
        (Algebra.IsSeparable.isSeparable k
          (IntermediateField.adjoin.powerBasis hx).gen))]
  · simpa only [IntermediateField.adjoin.powerBasis_gen,
      IntermediateField.AdjoinSimple.algebraMap_gen] using
      (prod_embeddings_algebraMap_powerBasisGen_eq
        (L := IntermediateField.adjoin k ({x} : Set E)) (E := E)
        k Ω (IntermediateField.adjoin.powerBasis hx)).symm
  · exact Algebra.IsSeparable.isSeparable k _

end LocalClassFieldTheory
end
end

section
-- module Solutions.OAIQ244_DUKE.LocalClassFieldTheory_Finite_LocalReciprocity_SeparableFixedFieldNorm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

set_option autoImplicit false

namespace LocalClassFieldTheory
open RamificationTheory

open LocalFieldTheory

/-!
# Finite local reciprocity: norms from arbitrary finite separable fixed fields

The henselian condition in the abstract class-formation framework quantifies over every finite abstract
field, not only over normal ones.  For an intermediate finite separable field
`E` in a separably closed Galois ambient field, the left cosets of
`Gal(Ω / E)` are canonically the `K`-embeddings `E → Ω`.  This file uses that
identification to compare the abstract class-formation coset norm with the ordinary field
norm, without a normality assumption on `E / K`.
-/

noncomputable section

open scoped BigOperators

variable (K Ω : Type) [Field K] [Field Ω] [Algebra K Ω]
  [IsGalois K Ω] [IsSepClosed Ω]

section NormAsProduct

noncomputable local instance finiteSeparableAlgHomFintype
    {k F T : Type} [Field k] [Field F] [Field T]
    [Algebra k F] [Algebra k T]
    [FiniteDimensional k F] [Algebra.IsSeparable k F] :
    Fintype (F →ₐ[k] T) :=
  PowerBasis.AlgHom.fintype (Field.powerBasisOfFiniteOfSeparable k F)

end NormAsProduct

end
end LocalClassFieldTheory
end

section
-- module Solutions.OAIQ244_DUKE.LocalClassFieldTheory_Finite_LocalReciprocity_AbstractFixedFieldNorm
set_option maxHeartbeats 800000
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

set_option autoImplicit false

namespace LocalClassFieldTheory

/-- Compat: the two `Module (ResidueField R) (ResidueField S)` instances (the algebra one and Mathlib's
explicit one) agree; they were definitionally equal for the older Mathlib. -/
theorem residueModule_eq {R S : Type*} [CommRing R] [CommRing S] [IsLocalRing R] [IsLocalRing S]
    [Algebra R S] [IsLocalHom (algebraMap R S)] :
    (Algebra.toModule : Module (IsLocalRing.ResidueField R) (IsLocalRing.ResidueField S)) =
      IsLocalRing.ResidueField.instModule := by
  ext r x
  rfl

/-- Compat: Mathlib's two `Algebra (ResidueField R) (ResidueField S)` instances agree. -/
theorem residueAlgebra_eq {R S : Type*} [CommRing R] [CommRing S] [IsLocalRing R] [IsLocalRing S]
    [Algebra R S] [IsLocalHom (algebraMap R S)] [Algebra.IsIntegral R (IsLocalRing.ResidueField S)] :
    (IsLocalRing.ResidueField.algebraOfIsIntegral : Algebra (IsLocalRing.ResidueField R) (IsLocalRing.ResidueField S)) =
      IsLocalRing.ResidueField.instAlgebra := by
  apply Algebra.algebra_ext
  intro r
  obtain ⟨r, rfl⟩ := IsLocalRing.residue_surjective r
  rfl

open RamificationTheory

open LocalFieldTheory

/-!
# Finite local reciprocity: the norm of an arbitrary finite abstract field

The abstract class-formation framework indexes finite fields by closed subgroups, whereas the local norm
calculation is stated for their concrete fixed intermediate fields.  This file
identifies the two presentations.  In particular, it does not assume that the
finite fixed field is normal over the local ground field.
-/

end LocalClassFieldTheory
end

section
-- module Solutions.OAIQ244_DUKE.Ramification_GaloisValuation_AbsoluteGalois_FiniteLevelValuationRestriction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

set_option autoImplicit false

namespace RamificationTheory

open ValuationTheory

/-!
# Finite-level valuation restriction for absolute Galois arguments

This file isolates the valuation-restriction and separable-power lemmas
used to pass from absolute Galois questions to finite intermediate fields.
-/

noncomputable section

universe u v w z

namespace ValuationSubring

variable {K : Type u} [Field K] (A : ValuationSubring K)

section RestrictIntermediateField

variable {K : Type u} {Ω : Type v} [Field K] [Field Ω] [Algebra K Ω]

/-- Restrict a valuation subring of an ambient field to an intermediate field. -/
def restrictIntermediateField
    (A : ValuationSubring Ω) (E : IntermediateField K Ω) :
    ValuationSubring E :=
  A.comap (algebraMap E Ω)

/-- States the theorem `restrictIntermediateField_eq_comap`. -/
@[simp] theorem restrictIntermediateField_eq_comap
    (A : ValuationSubring Ω) (E : IntermediateField K Ω) :
    (restrictIntermediateField A E) = A.comap (algebraMap E Ω) :=
  rfl

/-- States the theorem `mem_restrictIntermediateField_iff`. -/
@[simp] theorem mem_restrictIntermediateField_iff
    (A : ValuationSubring Ω) (E : IntermediateField K Ω) (x : E) :
    x ∈ (restrictIntermediateField A E) ↔ (x : Ω) ∈ A :=
  Iff.rfl

/-- States the theorem `restrictIntermediateField_hasExtension`. -/
theorem restrictIntermediateField_hasExtension
    {Γ : Type w} [LinearOrderedCommGroupWithZero Γ]
    (v : Valuation K Γ) (A : ValuationSubring Ω)
    [_root_.Valuation.HasExtension v A.valuation]
    (E : IntermediateField K Ω) :
    _root_.Valuation.HasExtension v ((restrictIntermediateField A E)).valuation := by
  apply _root_.Valuation.HasExtension.ofComapInteger
  ext x
  simp only [Subring.mem_comap, Valuation.mem_integer_iff,
    ValuationSubring.valuation_le_one_iff,
    mem_restrictIntermediateField_iff]
  change algebraMap E Ω (algebraMap K E x) ∈ A ↔ v x ≤ 1
  rw [← IsScalarTower.algebraMap_apply K E Ω x]
  rw [← A.valuation_le_one_iff (algebraMap K Ω x)]
  exact _root_.Valuation.HasExtension.val_map_le_one_iff
    (vR := v) (vA := A.valuation) x

open scoped Pointwise

/-- A `K`-algebra automorphic translate of an extension valuation subring is
again an extension of the base valuation. -/
theorem smul_hasExtension
    {Γ : Type w} [LinearOrderedCommGroupWithZero Γ]
    (v : Valuation K Γ) (A : ValuationSubring Ω)
    [_root_.Valuation.HasExtension v A.valuation]
    (σ : Ω ≃ₐ[K] Ω) :
    _root_.Valuation.HasExtension v (σ • A).valuation := by
  apply _root_.Valuation.HasExtension.ofComapInteger
  ext x
  simp [ValuationSubring.integer_valuation, Valuation.mem_integer_iff]
  rw [Subring.mem_pointwise_smul_iff_inv_smul_mem]
  have hcomm : (σ⁻¹) (algebraMap K Ω x) = algebraMap K Ω x :=
    (σ⁻¹).commutes x
  change (σ⁻¹) (algebraMap K Ω x) ∈ A.toSubring ↔ v x ≤ 1
  rw [hcomm]
  change (algebraMap K Ω x) ∈ A ↔ v x ≤ 1
  rw [← A.valuation_le_one_iff (algebraMap K Ω x)]
  exact _root_.Valuation.HasExtension.val_map_le_one_iff
    (vR := v) (vA := A.valuation) x

end RestrictIntermediateField

end ValuationSubring


end

end RamificationTheory
end

section
-- module Solutions.OAIQ244_DUKE.Ramification_GaloisValuation_AbsoluteGalois_AbsoluteRamification
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

set_option autoImplicit false

namespace RamificationTheory

open ValuationTheory

/-!
# Absolute Galois ramification

This file develops the decomposition and inertia subgroups of an absolute
Galois group after the finite-level valuation-restriction layer.
-/

noncomputable section

universe u v w z

namespace Field
namespace absoluteGaloisGroup

open scoped Topology Pointwise
open CategoryTheory

section AbsoluteRamification

variable (K : Type u) [Field K]

/-- The absolute decomposition subgroup attached to a chosen valuation subring
of the algebraic closure. -/
abbrev decompositionSubgroup
    (A : ValuationSubring (AlgebraicClosure K)) :
    Subgroup (Field.absoluteGaloisGroup K) :=
  A.decompositionSubgroup K

/-- Provides the instance `decompositionSubgroupMulSemiringAction`. -/
instance decompositionSubgroupMulSemiringAction
    (A : ValuationSubring (AlgebraicClosure K)) :
    MulSemiringAction (decompositionSubgroup K A) A := by
  change MulSemiringAction (A.decompositionSubgroup K) A
  infer_instance

/-- The absolute decomposition-group action on the residue field of the chosen
valuation subring. -/
noncomputable def decompositionResidueAction
    (A : ValuationSubring (AlgebraicClosure K)) :
    decompositionSubgroup K A →*
      (IsLocalRing.ResidueField A ≃+* IsLocalRing.ResidueField A) :=
  MulSemiringAction.toRingAut
    (decompositionSubgroup K A) (IsLocalRing.ResidueField A)

/-- If the absolute decomposition subgroup is all of `G_K`, every absolute
automorphism can be viewed as a decomposition element. -/
def toDecompositionSubgroupOfEqTop
    (A : ValuationSubring (AlgebraicClosure K))
    (hA : decompositionSubgroup K A = ⊤) :
    Field.absoluteGaloisGroup K →*
      decompositionSubgroup K A where
  toFun σ := ⟨σ, by rw [hA]; exact Subgroup.mem_top σ⟩
  map_one' := by
    ext
    rfl
  map_mul' _ _ := by
    ext
    rfl

/-- States the theorem `toDecompositionSubgroupOfEqTop_coe`. -/
@[simp] theorem toDecompositionSubgroupOfEqTop_coe
    (A : ValuationSubring (AlgebraicClosure K))
    (hA : decompositionSubgroup K A = ⊤)
    (σ : Field.absoluteGaloisGroup K) :
    (toDecompositionSubgroupOfEqTop K A hA σ :
      Field.absoluteGaloisGroup K) = σ :=
  rfl

/-- When `D_A = G_K`, the decomposition residue action becomes an ambient
absolute Galois action on the residue field. -/
noncomputable def absoluteResidueActionOfDecompositionSubgroupEqTop
    (A : ValuationSubring (AlgebraicClosure K))
    (hA : decompositionSubgroup K A = ⊤) :
    Field.absoluteGaloisGroup K →*
      (IsLocalRing.ResidueField A ≃+* IsLocalRing.ResidueField A) :=
  (decompositionResidueAction K A).comp
    (toDecompositionSubgroupOfEqTop K A hA)

/-- States the theorem `absoluteResidueActionOfDecompositionSubgroupEqTop_apply`. -/
@[simp] theorem absoluteResidueActionOfDecompositionSubgroupEqTop_apply
    (A : ValuationSubring (AlgebraicClosure K))
    (hA : decompositionSubgroup K A = ⊤)
    (σ : Field.absoluteGaloisGroup K) :
    absoluteResidueActionOfDecompositionSubgroupEqTop K A hA σ =
      decompositionResidueAction K A
        (toDecompositionSubgroupOfEqTop K A hA σ) :=
  rfl

end AbsoluteRamification

end absoluteGaloisGroup
end Field

end

end RamificationTheory
end

section
-- module Solutions.OAIQ244_DUKE.LocalClassFieldTheory_Finite_LocalReciprocity_FiniteResidueFrobenius
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

set_option autoImplicit false

namespace LocalClassFieldTheory

/-!
# Finite local reciprocity: finite residue Frobenius coordinates

The degree map used in local reciprocity comes from the arithmetic Frobenius
on the algebraic closure of the finite residue field.  This file constructs
the finite-level source of that map: for every finite extension of a finite
field, exponentiation of Frobenius identifies its Galois group with the
appropriate cyclic quotient of `ℤ̂`.

No cyclic generator is chosen.  The generator is the actual arithmetic
Frobenius `x ↦ x ^ #k`, and the exponent map is obtained by factoring its
integer powers through `ZMod [L : k]`.
-/

noncomputable section

universe u v w

variable (k : Type u) (L : Type v)
  [Field k] [Fintype k] [Field L] [Finite L] [Algebra k L]

/-- Integer powers of the arithmetic Frobenius, written additively. -/
def finiteResidueFrobeniusIntegerPowers :
    ℤ →+ Additive (L ≃ₐ[k] L) :=
  zmultiplesHom (Additive (L ≃ₐ[k] L)) (Additive.ofMul
    (FiniteField.frobeniusAlgEquivOfAlgebraic k L))

/-- The order relation which lets integer Frobenius powers factor through
`ZMod [L : k]`. -/
theorem finiteResidueFrobeniusIntegerPowers_degree_eq_zero :
    finiteResidueFrobeniusIntegerPowers k L (Module.finrank k L) = 0 := by
  apply Additive.ext
  change (FiniteField.frobeniusAlgEquivOfAlgebraic k L) ^
      (Module.finrank k L : ℤ) = 1
  rw [← FiniteField.orderOf_frobeniusAlgEquivOfAlgebraic (K := k) (L := L)]
  rw [zpow_natCast, pow_orderOf_eq_one]

/-- The canonical finite-level exponent homomorphism
`Z/[L:k]Z → Gal(L/k)`, sending `1` to arithmetic Frobenius. -/
def finiteResidueFrobeniusExponentHom :
    Multiplicative (ZMod (Module.finrank k L)) →* (L ≃ₐ[k] L) :=
  AddMonoidHom.toMultiplicative
    (ZMod.lift (Module.finrank k L)
      ⟨finiteResidueFrobeniusIntegerPowers k L,
        finiteResidueFrobeniusIntegerPowers_degree_eq_zero k L⟩)

/-- An integer residue exponent maps to the corresponding power of Frobenius. -/
@[simp]
theorem finiteResidueFrobeniusExponentHom_intCast (m : ℤ) :
    finiteResidueFrobeniusExponentHom k L
        (Multiplicative.ofAdd (m : ZMod (Module.finrank k L))) =
      (FiniteField.frobeniusAlgEquivOfAlgebraic k L) ^ m := by
  change
    (ZMod.lift (Module.finrank k L)
      ⟨finiteResidueFrobeniusIntegerPowers k L,
        finiteResidueFrobeniusIntegerPowers_degree_eq_zero k L⟩)
      (m : ZMod (Module.finrank k L)) =
        Additive.ofMul ((FiniteField.frobeniusAlgEquivOfAlgebraic k L) ^ m)
  rw [ZMod.lift_coe]
  rfl

/-- Residue exponent one maps to the arithmetic Frobenius automorphism. -/
@[simp]
theorem finiteResidueFrobeniusExponentHom_one :
    finiteResidueFrobeniusExponentHom k L
        (Multiplicative.ofAdd (1 : ZMod (Module.finrank k L))) =
      FiniteField.frobeniusAlgEquivOfAlgebraic k L := by
  simpa using finiteResidueFrobeniusExponentHom_intCast k L 1

/-- Every finite residue-field automorphism is a power of arithmetic
Frobenius, so the canonical exponent homomorphism is onto. -/
theorem finiteResidueFrobeniusExponentHom_surjective :
    Function.Surjective (finiteResidueFrobeniusExponentHom k L) := by
  intro sigma
  obtain ⟨m, hm⟩ :=
    (FiniteField.bijective_frobeniusAlgEquivOfAlgebraic_pow k L).2 sigma
  refine ⟨Multiplicative.ofAdd
    ((m.1 : ℤ) : ZMod (Module.finrank k L)), ?_⟩
  rw [finiteResidueFrobeniusExponentHom_intCast]
  simpa [zpow_natCast] using hm

/-- The finite-level Frobenius exponent homomorphism is injective. -/
theorem finiteResidueFrobeniusExponentHom_injective :
    Function.Injective (finiteResidueFrobeniusExponentHom k L) := by
  let : NeZero (Module.finrank k L) := ⟨Module.finrank_pos.ne'⟩
  have hcard :
      Nat.card (Multiplicative (ZMod (Module.finrank k L))) =
        Nat.card (L ≃ₐ[k] L) := by
    rw [Nat.card_congr Multiplicative.toAdd,
      Nat.card_zmod, IsGalois.card_aut_eq_finrank]
  exact ((finiteResidueFrobeniusExponentHom_surjective k L).bijective_of_nat_card_le
    hcard.le).1

/-- Canonical finite-level Frobenius coordinates. -/
def finiteResidueFrobeniusExponentEquiv :
    Multiplicative (ZMod (Module.finrank k L)) ≃* (L ≃ₐ[k] L) :=
  MulEquiv.ofBijective (finiteResidueFrobeniusExponentHom k L)
    ⟨finiteResidueFrobeniusExponentHom_injective k L,
      finiteResidueFrobeniusExponentHom_surjective k L⟩

/-- The Frobenius exponent equivalence has the same underlying map as the exponent homomorphism. -/
@[simp]
theorem finiteResidueFrobeniusExponentEquiv_apply (z) :
    finiteResidueFrobeniusExponentEquiv k L z =
      finiteResidueFrobeniusExponentHom k L z :=
  rfl

/-- The Frobenius exponent equivalence sends one to arithmetic Frobenius. -/
@[simp]
theorem finiteResidueFrobeniusExponentEquiv_one :
    finiteResidueFrobeniusExponentEquiv k L
        (Multiplicative.ofAdd (1 : ZMod (Module.finrank k L))) =
      FiniteField.frobeniusAlgEquivOfAlgebraic k L :=
  finiteResidueFrobeniusExponentHom_one k L

section Tower

variable {E : Type v} {F : Type w}
  [Field E] [Finite E] [Field F] [Finite F]
  [Algebra k E] [Algebra k F] [Algebra E F]
  [IsScalarTower k E F] [Normal k E]

/-- Arithmetic Frobenius commutes with restriction in a tower of finite
extensions of a finite field. -/
theorem restrictNormalHom_finiteResidueFrobenius :
    AlgEquiv.restrictNormalHom E
        (FiniteField.frobeniusAlgEquivOfAlgebraic k F) =
      FiniteField.frobeniusAlgEquivOfAlgebraic k E := by
  apply AlgEquiv.ext
  intro x
  apply (algebraMap E F).injective
  calc
    (algebraMap E F)
        (((AlgEquiv.restrictNormalHom E)
          (FiniteField.frobeniusAlgEquivOfAlgebraic k F)) x) =
        FiniteField.frobeniusAlgEquivOfAlgebraic k F
          (algebraMap E F x) :=
      AlgEquiv.restrictNormal_commutes
        (FiniteField.frobeniusAlgEquivOfAlgebraic k F) E x
    _ = (algebraMap E F
        ((FiniteField.frobeniusAlgEquivOfAlgebraic k E) x) : F) := by
      simp only [FiniteField.coe_frobeniusAlgEquivOfAlgebraic]
      exact (map_pow (algebraMap E F) x (Fintype.card k)).symm

end Tower

end
end LocalClassFieldTheory
end

section
-- module Solutions.OAIQ244_DUKE.LocalClassFieldTheory_Finite_LocalReciprocity_ResidueAbsoluteFrobenius
attribute [-instance] _root_.LocalClassFieldTheory.finiteGaloisFieldRangeOfEmbedding_isGalois
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

set_option autoImplicit false

namespace LocalClassFieldTheory

/-!
# Finite local reciprocity: Frobenius on an infinite residue extension

The finite Frobenius exponent maps are compatible with restriction.  This
file therefore assembles them in the actual inverse-limit presentation of an
infinite Galois group.  It produces the canonical continuous homomorphism
from the profinite integers to the Galois group of an algebraic Galois
extension of a finite field.

For an algebraic closure this is the Frobenius map compared with the degree
map in finite local reciprocity. The construction itself does not require a
bijectivity hypothesis.
-/

noncomputable section

universe u v

open CategoryTheory Opposite
open FiniteGaloisIntermediateField ProfiniteGrp
variable (k : Type u) (Omega : Type v)
  [Field k] [Fintype k] [Field Omega] [Algebra k Omega]
  [IsGalois k Omega]

/-- Arithmetic Frobenius on an algebraic Galois extension restricts to
arithmetic Frobenius on every finite Galois intermediate field. -/
theorem restrictNormalHom_frobeniusAlgEquivOfAlgebraic
    (E : FiniteGaloisIntermediateField k Omega) :
    AlgEquiv.restrictNormalHom E
        (FiniteField.frobeniusAlgEquivOfAlgebraic k Omega) =
      FiniteField.frobeniusAlgEquivOfAlgebraic k E := by
  apply AlgEquiv.ext
  intro x
  apply (algebraMap E Omega).injective
  calc
    algebraMap E Omega
        ((AlgEquiv.restrictNormalHom E
          (FiniteField.frobeniusAlgEquivOfAlgebraic k Omega)) x) =
        FiniteField.frobeniusAlgEquivOfAlgebraic k Omega
          (algebraMap E Omega x) :=
      AlgEquiv.restrictNormal_commutes
        (FiniteField.frobeniusAlgEquivOfAlgebraic k Omega) E x
    _ = algebraMap E Omega
        (FiniteField.frobeniusAlgEquivOfAlgebraic k E x) := by
      simp only [FiniteField.coe_frobeniusAlgEquivOfAlgebraic]
      exact (map_pow (algebraMap E Omega) x (Fintype.card k)).symm

end
end LocalClassFieldTheory
end

section
-- module Solutions.OAIQ244_DUKE.LocalClassFieldTheory_Finite_LocalReciprocity_ResidueAlgebraicClosureDegree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

set_option autoImplicit false

namespace LocalClassFieldTheory

/-!
# Finite local reciprocity: degree coordinates on any residue algebraic closure

The residue field obtained from a valuation ring in a separable closure is
not definitionally Mathlib's chosen `AlgebraicClosure`.  The construction of
the degree map must therefore work on any algebraically closed algebraic
extension of the finite residue field.

This file repeats the inverse-limit detection argument in that intrinsic
setting.  The resulting map is the inverse of the canonical arithmetic
Frobenius homomorphism itself; no equivalence with a chosen algebraic closure
and no generator of a finite cyclic group enters its definition.
-/

noncomputable section

universe u v

open CategoryTheory Opposite
open FiniteGaloisIntermediateField ProfiniteGrp
open RamificationTheory.Field.absoluteGaloisGroup
open Polynomial

variable (k : Type u) [Field k] [Fintype k]
variable (Omega : Type v) [Field Omega] [Algebra k Omega]
  [Algebra.IsAlgebraic k Omega] [IsAlgClosed Omega]

instance finiteResidueBaseRingCharPrime : Fact (ringChar k).Prime :=
  ⟨CharP.char_is_prime k (ringChar k)⟩

instance residueAlgebraicClosureIsAlgClosure : IsAlgClosure k Omega :=
  ⟨inferInstance, inferInstance⟩

instance residueAlgebraicClosureIsGalois : IsGalois k Omega := by
  infer_instance

instance residueAlgebraicClosureGaloisT2 :
    T2Space (Omega ≃ₐ[k] Omega) := by
  infer_instance

/-- Embed the degree-`n` finite extension of `k` into the given residue
algebraic closure.  This choice is used only to prove that all profinite
coordinates are detected. -/
noncomputable def finiteResidueExtensionEmbeddingInto
    (n : ℕ) [NeZero n] :
    FiniteField.Extension k (ringChar k) n →ₐ[k] Omega := by
  letI : Module.IsTorsionFree k Omega :=
    Module.isTorsionFree_iff_algebraMap_injective.mpr
      (algebraMap k Omega).injective
  exact IsAlgClosed.lift (R := k)
    (S := FiniteField.Extension k (ringChar k) n) (M := Omega)

/-- The image of the degree-`n` finite extension in the given residue
algebraic closure. -/
noncomputable def finiteResidueIntermediateFieldIn
    (n : ℕ) [NeZero n] : IntermediateField k Omega :=
  (⊤ : IntermediateField k
      (FiniteField.Extension k (ringChar k) n)).map
    (finiteResidueExtensionEmbeddingInto k Omega n)

/-- The model finite field is canonically isomorphic to its embedded image. -/
noncomputable def finiteResidueExtensionEquivIntermediateIn
    (n : ℕ) [NeZero n] :
    FiniteField.Extension k (ringChar k) n ≃ₐ[k]
      finiteResidueIntermediateFieldIn k Omega n :=
  IntermediateField.topEquiv.symm.trans
    (IntermediateField.equivMap ⊤
      (finiteResidueExtensionEmbeddingInto k Omega n))

/-- An actual degree-`n` finite Galois intermediate field in any residue
algebraic closure. -/
noncomputable def finiteResidueGaloisIntermediateFieldIn
    (n : ℕ) [NeZero n] : FiniteGaloisIntermediateField k Omega where
  toIntermediateField := finiteResidueIntermediateFieldIn k Omega n
  finiteDimensional := Module.Finite.equiv
    (finiteResidueExtensionEquivIntermediateIn k Omega n).toLinearEquiv
  isGalois := IsGalois.of_algEquiv
    (finiteResidueExtensionEquivIntermediateIn k Omega n)

omit [Algebra.IsAlgebraic k Omega] in
/-- States the theorem `finrank_finiteResidueGaloisIntermediateFieldIn`. -/
@[simp]
theorem finrank_finiteResidueGaloisIntermediateFieldIn
    (n : ℕ) [NeZero n] :
    Module.finrank k
        (finiteResidueGaloisIntermediateFieldIn k Omega n) = n := by
  calc
    Module.finrank k
        (finiteResidueGaloisIntermediateFieldIn k Omega n) =
        Module.finrank k
          (FiniteField.Extension k (ringChar k) n) :=
      (finiteResidueExtensionEquivIntermediateIn k Omega n).toLinearEquiv.finrank_eq.symm
    _ = n := FiniteField.finrank_extension k (ringChar k) n

omit [IsAlgClosed Omega] in
/-- In any algebraic closure of a finite field, the fixed points of arithmetic
Frobenius are exactly the base field. -/
theorem mem_range_algebraMap_iff_frobenius_fixed_in
    (x : Omega) :
    x ∈ Set.range (algebraMap k Omega) ↔
      FiniteField.frobeniusAlgEquivOfAlgebraic k Omega x = x := by
  constructor
  · rintro ⟨a, rfl⟩
    simp only [FiniteField.coe_frobeniusAlgEquivOfAlgebraic]
    rw [← map_pow, FiniteField.pow_card]
  · intro hx
    have hxpow : x ^ Fintype.card k = x := by
      simpa only [FiniteField.coe_frobeniusAlgEquivOfAlgebraic] using hx
    let p : k[X] := X ^ Fintype.card k - X
    have hpne : p ≠ 0 :=
      FiniteField.X_pow_card_sub_X_ne_zero k Fintype.one_lt_card
    have hxroot : x ∈ p.rootSet Omega := by
      rw [Polynomial.mem_rootSet_of_ne hpne]
      simp [p, hxpow]
    have hsplits : (p.map (algebraMap k k)).Splits := by
      simpa only [p] using (FiniteField.isSplittingField_sub k k).splits
    have himage := hsplits.image_rootSet (Algebra.ofId k Omega)
    rw [← himage] at hxroot
    rcases hxroot with ⟨a, _ha, hax⟩
    exact ⟨a, hax⟩

end
end LocalClassFieldTheory
end

section
-- module Solutions.OAIQ244_DUKE.LocalClassFieldTheory_Finite_LocalReciprocity_ResidueAlgebraicallyClosed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

set_option autoImplicit false

namespace LocalClassFieldTheory

/-!
# Residues of algebraically closed valued fields

The residue field of a valuation ring in an algebraically closed field is
algebraically closed.  This is the missing source needed to apply the
intrinsic finite-field degree map to the residue of an algebraic closure of a
local field.
-/

noncomputable section

universe u

variable {Omega : Type u} [Field Omega] [IsAlgClosed Omega]

/-- The residue field of a valuation subring of an algebraically closed field
is algebraically closed.  A monic irreducible residue polynomial is lifted
monically to the valuation ring.  A root in the ambient algebraically closed
field is integral, hence lies back in the valuation ring and can be reduced. -/
theorem valuationSubring_residueField_isAlgClosed
    (A : ValuationSubring Omega) :
    IsAlgClosed (IsLocalRing.ResidueField A) := by
  apply IsAlgClosed.of_exists_root
  intro p hpmonic hpirreducible
  have hlifts : p ∈ Polynomial.lifts (IsLocalRing.residue A) := by
    rw [Polynomial.mem_lifts]
    exact (Polynomial.map_surjective
      (IsLocalRing.residue A) IsLocalRing.residue_surjective) p
  obtain ⟨q, hqmap, hqdegree, hqmonic⟩ :=
    Polynomial.lifts_and_degree_eq_and_monic hlifts hpmonic
  have hqmapSubtypeDegree :
      (q.map A.subtype).degree ≠ 0 := by
    rw [Polynomial.degree_map_eq_of_injective A.subtype_injective q]
    rw [hqdegree]
    exact ne_of_gt (Polynomial.degree_pos_of_irreducible hpirreducible)
  obtain ⟨x, hxroot⟩ :=
    IsAlgClosed.exists_root (q.map A.subtype) hqmapSubtypeDegree
  have hxIntegral : IsIntegral A x := by
    refine ⟨q, hqmonic, ?_⟩
    change Polynomial.eval₂ A.subtype x q = 0
    simpa [Polynomial.eval_map] using hxroot
  have hxA : x ∈ A := by
    let hAIntegers : A.valuation.Integers A :=
      { hom_inj := A.subtype_injective
        map_le_one := fun a =>
          (A.valuation_le_one_iff (a : Omega)).mpr a.property
        exists_of_le_one := fun {r} hr =>
          ⟨⟨r, (A.valuation_le_one_iff r).mp hr⟩, rfl⟩ }
    have hxValuation : A.valuation x ≤ 1 :=
      (hAIntegers.isIntegral_iff_v_le_one).mp hxIntegral
    exact (A.valuation_le_one_iff x).mp hxValuation
  let xA : A := ⟨x, hxA⟩
  have hxrootEval₂ : Polynomial.eval₂ A.subtype x q = 0 := by
    rw [← Polynomial.eval_map]
    exact hxroot
  have hxrootA : q.eval xA = 0 := by
    apply A.subtype_injective
    rw [← Polynomial.eval₂_at_apply A.subtype xA]
    simpa [xA] using hxrootEval₂
  refine ⟨IsLocalRing.residue A xA, ?_⟩
  rw [← hqmap]
  simp [Polynomial.eval_map, hxrootA]

/-! ## Residues under a purely inseparable ambient extension -/

section PurelyInseparableComap

variable {F Omega : Type u} [Field F] [Field Omega] [Algebra F Omega]

/-- The inclusion from the pullback of a valuation ring to the ambient
valuation ring. -/
def valuationSubringComapMap (A : ValuationSubring Omega) :
    A.comap (algebraMap F Omega) →+* A where
  toFun x := ⟨algebraMap F Omega x, x.property⟩
  map_one' := by ext; simp
  map_mul' x y := by ext; simp
  map_zero' := by ext; simp
  map_add' x y := by ext; simp

/-- Pullback along a field embedding gives a local map of valuation rings. -/
theorem valuationSubringComapMap_isLocalHom (A : ValuationSubring Omega) :
    IsLocalHom (valuationSubringComapMap (F := F) A) := by
  constructor
  intro x hx
  obtain ⟨u, hu⟩ := hx
  have hx0 : (x : F) ≠ 0 := by
    intro hzero
    have hmapZero : valuationSubringComapMap (F := F) A x = 0 := by
      apply Subtype.ext
      simp [valuationSubringComapMap, hzero]
    exact Units.ne_zero u (hu.trans hmapZero)
  let xinv : A.comap (algebraMap F Omega) :=
    ⟨(x : F)⁻¹, by
      change algebraMap F Omega ((x : F)⁻¹) ∈ A
      rw [map_inv₀]
      have hu' : algebraMap F Omega (x : F) = ((u : A) : Omega) := by
        have h := congrArg Subtype.val hu
        exact h.symm
      rw [hu']
      have hinv : (((u : A) : Omega))⁻¹ = (((u⁻¹ : Aˣ) : A) : Omega) := by
        have hprod :
            ((u : A) : Omega) * (((u⁻¹ : Aˣ) : A) : Omega) = 1 := by
          have hprodA : (u : A) * ((u⁻¹ : Aˣ) : A) = 1 := u.val_inv
          exact congrArg A.subtype hprodA
        exact (eq_inv_of_mul_eq_one_right hprod).symm
      rw [hinv]
      exact (u⁻¹ : Aˣ).val.property⟩
  let xu : (A.comap (algebraMap F Omega))ˣ :=
    { val := x
      inv := xinv
      val_inv := by apply Subtype.ext; simp [xinv, hx0]
      inv_val := by apply Subtype.ext; simp [xinv, hx0] }
  exact ⟨xu, rfl⟩

/-- The residue-field embedding induced by pullback of a valuation ring. -/
noncomputable def valuationSubringComapResidueMap
    (A : ValuationSubring Omega) :
    IsLocalRing.ResidueField (A.comap (algebraMap F Omega)) →+*
      IsLocalRing.ResidueField A := by
  letI : IsLocalHom (valuationSubringComapMap (F := F) A) :=
    valuationSubringComapMap_isLocalHom (F := F) A
  exact IsLocalRing.ResidueField.map (valuationSubringComapMap (F := F) A)

/-- States the theorem `valuationSubringComapResidueMap_residue`. -/
@[simp] theorem valuationSubringComapResidueMap_residue
    (A : ValuationSubring Omega)
    (x : A.comap (algebraMap F Omega)) :
    valuationSubringComapResidueMap (F := F) A
        (IsLocalRing.residue (A.comap (algebraMap F Omega)) x) =
      IsLocalRing.residue A (valuationSubringComapMap (F := F) A x) :=
  rfl

/-- A purely inseparable extension remains purely inseparable after passing
to the residue fields of a valuation ring and its pullback.  In positive
characteristic this is the same Frobenius-power argument; in characteristic
zero the ambient purely inseparable extension is already trivial. -/
theorem valuationSubring_comap_residueField_isPurelyInseparable
    [IsPurelyInseparable F Omega] (A : ValuationSubring Omega) :
    letI : Algebra
        (IsLocalRing.ResidueField (A.comap (algebraMap F Omega)))
        (IsLocalRing.ResidueField A) :=
      (valuationSubringComapResidueMap (F := F) A).toAlgebra
    IsPurelyInseparable
      (IsLocalRing.ResidueField (A.comap (algebraMap F Omega)))
      (IsLocalRing.ResidueField A) := by
  let B := A.comap (algebraMap F Omega)
  let barI := valuationSubringComapResidueMap (F := F) A
  let : Algebra (IsLocalRing.ResidueField B)
      (IsLocalRing.ResidueField A) := barI.toAlgebra
  obtain ⟨q, hqF⟩ := ExpChar.exists F
  let : ExpChar F q := hqF
  cases hqF with
  | zero =>
      let : Algebra.IsSeparable F Omega := inferInstance
      rw [isPurelyInseparable_iff_pow_mem
        (IsLocalRing.ResidueField B)
        (ringExpChar (IsLocalRing.ResidueField B))]
      intro y
      obtain ⟨a, rfl⟩ := IsLocalRing.residue_surjective y
      obtain ⟨z, hz⟩ :=
        IsPurelyInseparable.surjective_algebraMap_of_isSeparable F Omega
          (a : Omega)
      let zB : B := ⟨z, by
        change algebraMap F Omega z ∈ A
        rw [hz]
        exact a.property⟩
      refine ⟨0, IsLocalRing.residue B zB, ?_⟩
      simp only [pow_zero, pow_one]
      change barI (IsLocalRing.residue B zB) = IsLocalRing.residue A a
      dsimp only [barI, B]
      rw [valuationSubringComapResidueMap_residue]
      apply congrArg (IsLocalRing.residue A)
      apply Subtype.ext
      exact hz
  | prime hq =>
      let : CharP Omega q :=
        charP_of_injective_algebraMap (algebraMap F Omega).injective q
      let : CharP A q := A.subtype.charP A.subtype_injective q
      let : CharP (IsLocalRing.ResidueField A) q :=
        CharP.of_ringHom_of_ne_zero (IsLocalRing.residue A) q hq.ne_zero
      let : CharP (IsLocalRing.ResidueField B) q :=
        barI.charP barI.injective q
      let : ExpChar (IsLocalRing.ResidueField B) q := ExpChar.prime hq
      rw [isPurelyInseparable_iff_pow_mem
        (IsLocalRing.ResidueField B) q]
      intro y
      obtain ⟨a, rfl⟩ := IsLocalRing.residue_surjective y
      obtain ⟨n, z, hz⟩ := IsPurelyInseparable.pow_mem F q (a : Omega)
      let zB : B := ⟨z, by
        change algebraMap F Omega z ∈ A
        rw [hz]
        exact pow_mem a.property _⟩
      refine ⟨n, IsLocalRing.residue B zB, ?_⟩
      change barI (IsLocalRing.residue B zB) =
        (IsLocalRing.residue A a) ^ q ^ n
      dsimp only [barI, B]
      rw [valuationSubringComapResidueMap_residue]
      rw [← map_pow]
      apply congrArg (IsLocalRing.residue A)
      apply Subtype.ext
      exact hz

end PurelyInseparableComap

end
end LocalClassFieldTheory
end

section
-- module Solutions.OAIQ244_DUKE.LocalClassFieldTheory_Finite_LocalReciprocity_ResidueDatum
attribute [-instance] _root_.LocalClassFieldTheory.finiteGaloisFieldRangeOfEmbedding_isGalois
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

set_option autoImplicit false

namespace LocalClassFieldTheory
open RamificationTheory

/-!
# Finite local reciprocity: the residue datum and its finite indices

The arithmetic-Frobenius degree on an algebraic closure of a finite field is
packaged as the initial datum of the abstract class-formation framework.  For every finite residue
subextension, the image of its fixing subgroup is proved to be exactly
`n ℤ̂`; consequently the abstract residue degree is the ordinary field
degree.  This is the finite-coordinate comparison needed in the local-field
specialization.
-/

noncomputable section

variable (k Omega : Type)
  [Field k] [Fintype k] [Field Omega] [Algebra k Omega]
  [Algebra.IsAlgebraic k Omega] [IsAlgClosed Omega]

omit [Fintype k] [Algebra.IsAlgebraic k Omega] [IsAlgClosed Omega] in
theorem mem_fixingSubgroup_iff_restrictNormalHom_eq_one
    (E : FiniteGaloisIntermediateField k Omega)
    (sigma : Omega ≃ₐ[k] Omega) :
    sigma ∈ E.toIntermediateField.fixingSubgroup ↔
      AlgEquiv.restrictNormalHom E sigma = 1 := by
  constructor
  · intro hsigma
    rw [IntermediateField.mem_fixingSubgroup_iff] at hsigma
    apply AlgEquiv.ext
    intro x
    apply Subtype.ext
    change ((AlgEquiv.restrictNormalHom E sigma x : E) : Omega) = (x : Omega)
    rw [AlgEquiv.restrictNormalHom_apply]
    exact hsigma x x.property
  · intro hsigma
    rw [IntermediateField.mem_fixingSubgroup_iff]
    intro x hx
    let y : E := ⟨x, hx⟩
    have hy := congrArg (fun tau : E ≃ₐ[k] E => tau y) hsigma
    have hyval := congrArg Subtype.val hy
    rw [AlgEquiv.restrictNormalHom_apply] at hyval
    simpa [y] using hyval

end
end LocalClassFieldTheory
end

section
-- module Solutions.OAIQ244_DUKE.Ramification_HilbertRamification_RamificationGroup
attribute [-instance] _root_.RamificationTheory.Field.absoluteGaloisGroup.decompositionSubgroupMulSemiringAction _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

set_option autoImplicit false

namespace RamificationTheory

/-!
# Hilbert ramification theory: ramification subgroup source lemmas

This file records the first structural facts about the classical ramification
subgroup `R_w`.  The key point for the later character map
`I_w -> Hom(Delta/Gamma, lambda*)` is that `R_w` is a normal subgroup of
`I_w`, not merely a subgroup.
-/

noncomputable section

universe u v

namespace HilbertRamification
namespace ValuationSubring

variable (K : Type u) {L : Type v} [Field K] [Field L] [Algebra K L]

/-- A decomposition-group automorphism preserves the principal unit group of
the valuation subring it stabilizes. -/
theorem decompositionGroup_mapEquiv_mem_principalUnitGroup
    (A : _root_.ValuationSubring L) (τ : decompositionGroup K A)
    {u : Lˣ} (hu : u ∈ A.principalUnitGroup) :
    Units.mapEquiv ((τ : L ≃ₐ[K] L).toMulEquiv) u ∈ A.principalUnitGroup := by
  let uA : A.unitGroup := ⟨u, A.principal_units_le_units hu⟩
  let eA : A ≃+* A := MulSemiringAction.toRingEquiv (decompositionGroup K A) A τ
  let uA' : A.unitGroup :=
    A.unitGroupMulEquiv.symm
      (Units.mapEquiv eA.toMulEquiv (A.unitGroupMulEquiv uA))
  have huKer :
      A.unitGroupMulEquiv uA ∈
        (Units.map (IsLocalRing.residue A).toMonoidHom).ker :=
    (A.coe_mem_principalUnitGroup_iff (x := uA)).mp hu
  have huRes :
      IsLocalRing.residue A (A.unitGroupMulEquiv uA : A) = 1 := by
    have h :=
      congrArg
        (fun z : (IsLocalRing.ResidueField A)ˣ =>
          (z : IsLocalRing.ResidueField A))
        (MonoidHom.mem_ker.mp huKer)
    simpa using h
  have hresMapped :
      Units.map (IsLocalRing.residue A).toMonoidHom
          (Units.mapEquiv eA.toMulEquiv (A.unitGroupMulEquiv uA)) = 1 := by
    ext
    change
      IsLocalRing.residue A
          (MulSemiringAction.toRingEquiv (decompositionGroup K A) A τ
            (A.unitGroupMulEquiv uA : A)) = 1
    calc
      IsLocalRing.residue A
          (MulSemiringAction.toRingEquiv (decompositionGroup K A) A τ
            (A.unitGroupMulEquiv uA : A)) =
          τ • IsLocalRing.residue A (A.unitGroupMulEquiv uA : A) := by
        rw [← IsLocalRing.ResidueField.residue_smul]
        rfl
      _ = τ • (1 : IsLocalRing.ResidueField A) := by
        rw [huRes]
      _ = 1 := by
        simp
  have huA' :
      (uA' : Lˣ) ∈ A.principalUnitGroup := by
    rw [A.coe_mem_principalUnitGroup_iff (x := uA')]
    rw [MonoidHom.mem_ker]
    simpa [uA'] using hresMapped
  have huA'_coe :
      (uA' : Lˣ) =
        Units.mapEquiv ((τ : L ≃ₐ[K] L).toMulEquiv) u := by
    ext
    rfl
  rw [← huA'_coe]
  exact huA'

/-- The normality calculation for the ramification subgroup:
the ramification group is normal in inertia. -/
instance ramificationGroup_normal (A : _root_.ValuationSubring L) :
    (ramificationGroup K A).Normal := by
  refine ⟨?_⟩
  intro σ hσ τ
  rw [mem_ramificationGroup_iff] at hσ ⊢
  intro x
  have hquot :
      automorphismUnitQuotient K A
          (((τ * σ * τ⁻¹ : inertiaGroup K A) : decompositionGroup K A)) x =
        Units.mapEquiv (((τ : decompositionGroup K A) : L ≃ₐ[K] L).toMulEquiv)
          (automorphismUnitQuotient K A (σ : decompositionGroup K A)
            (Units.mapEquiv
              ((((τ⁻¹ : inertiaGroup K A) : decompositionGroup K A) :
                L ≃ₐ[K] L).toMulEquiv) x)) := by
    ext
    simp [automorphismUnitQuotient, div_eq_mul_inv, mul_assoc]
  rw [hquot]
  exact decompositionGroup_mapEquiv_mem_principalUnitGroup (K := K) A
    (τ : decompositionGroup K A)
    (hσ (Units.mapEquiv
      ((((τ⁻¹ : inertiaGroup K A) : decompositionGroup K A) :
        L ≃ₐ[K] L).toMulEquiv) x))

/-- The inertia group is canonically equivalent to its image in the ambient
`K`-automorphism group. -/
def inertiaGroupEquivInAut
    (A : _root_.ValuationSubring L) :
    inertiaGroup K A ≃* inertiaGroupInAut K A :=
  (inertiaGroup K A).equivMapOfInjective
    (decompositionGroup K A).subtype
    Subtype.coe_injective

/-- The ramification subgroup, viewed as a subgroup of ambient inertia. -/
abbrev ramificationGroupInInertiaAut
    (A : _root_.ValuationSubring L) :
    Subgroup (inertiaGroupInAut K A) :=
  Subgroup.map (inertiaGroupEquivInAut (K := K) A).toMonoidHom
    (ramificationGroup K A)

/-- States the theorem `mem_ramificationGroupInInertiaAut_iff`. -/
@[simp] theorem mem_ramificationGroupInInertiaAut_iff
    (A : _root_.ValuationSubring L) (σ : inertiaGroupInAut K A) :
    σ ∈ ramificationGroupInInertiaAut K A ↔
      ∃ τ : ramificationGroup K A,
        inertiaGroupEquivInAut (K := K) A τ = σ := by
  constructor
  · rintro ⟨τ, hτ, rfl⟩
    exact ⟨⟨τ, hτ⟩, rfl⟩
  · rintro ⟨τ, rfl⟩
    exact ⟨(τ : inertiaGroup K A), τ.property, rfl⟩

/-- The ambient copy of `R_w` is normal inside the ambient copy of `I_w`. -/
instance ramificationGroupInInertiaAut_normal
    (A : _root_.ValuationSubring L) :
    (ramificationGroupInInertiaAut K A).Normal := by
  let e := inertiaGroupEquivInAut (K := K) A
  simpa [ramificationGroupInInertiaAut, e] using
    (Subgroup.Normal.map (ramificationGroup_normal (K := K) A)
      e.toMonoidHom e.surjective)

/-- The tame-inertia quotient identification source:
transport the quotient `I_w/R_w` to the corresponding quotient of the ambient
automorphism subgroups. -/
def inertiaGroupQuotientRamificationEquivInertiaAutQuotient
    (A : _root_.ValuationSubring L) :
    inertiaGroup K A ⧸ ramificationGroup K A ≃*
      inertiaGroupInAut K A ⧸ ramificationGroupInInertiaAut K A :=
  QuotientGroup.congr
    (ramificationGroup K A)
    (ramificationGroupInInertiaAut K A)
    (inertiaGroupEquivInAut (K := K) A)
    rfl

/-- States the theorem `inertiaGroupQuotientRamificationEquivInertiaAutQuotient_mk`. -/
@[simp] theorem inertiaGroupQuotientRamificationEquivInertiaAutQuotient_mk
    (A : _root_.ValuationSubring L) (σ : inertiaGroup K A) :
    inertiaGroupQuotientRamificationEquivInertiaAutQuotient
        (K := K) A (QuotientGroup.mk' (ramificationGroup K A) σ) =
      QuotientGroup.mk' (ramificationGroupInInertiaAut K A)
        (inertiaGroupEquivInAut (K := K) A σ) :=
  rfl

end ValuationSubring
end HilbertRamification

end
end RamificationTheory
end

section
-- module Solutions.OAIQ244_DUKE.Ramification_ClosedSubgroups
attribute [-instance] _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

set_option autoImplicit false

namespace RamificationTheory

/-!
# finite Galois ramification theory: closed canonical subgroups

The paragraph following the decomposition and inertia subgroup definitions observes that the
decomposition, inertia, and ramification groups are closed in the Krull topology, also for an
infinite Galois extension. Each failure is witnessed by one field element, hence persists on a
coset of the open subgroup fixing the finite simple extension generated by that element.
-/

noncomputable section

universe u v

namespace HilbertRamification
namespace ValuationSubring

open scoped Pointwise Topology

variable (K : Type u) {L : Type v} [Field K] [Field L] [Algebra K L]
variable [Algebra.IsAlgebraic K L]

omit [Algebra.IsAlgebraic K L] in
theorem mem_decompositionGroup_iff_apply_mem
    (A : _root_.ValuationSubring L) (sigma : L ≃ₐ[K] L) :
    sigma ∈ decompositionGroup K A ↔
      ∀ x : L, sigma x ∈ A ↔ x ∈ A := by
  change sigma • A = A ↔ _
  constructor
  · intro hsigma x
    have hmem := congrArg (fun B : _root_.ValuationSubring L => sigma x ∈ B) hsigma
    change (sigma x ∈ sigma • A) = (sigma x ∈ A) at hmem
    rw [_root_.ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem] at hmem
    change (sigma⁻¹ (sigma x) ∈ A) = (sigma x ∈ A) at hmem
    have hinv : sigma⁻¹ (sigma x) = x := by simp
    rw [hinv] at hmem
    exact hmem.symm.to_iff
  · intro hsigma
    ext x
    rw [_root_.ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem]
    simpa using (hsigma (sigma⁻¹ x)).symm

/-- The valuation-subring decomposition group is closed in the Krull
topology. -/
theorem decompositionGroup_isClosed
    (A : _root_.ValuationSubring L) :
    IsClosed (decompositionGroup K A : Set (L ≃ₐ[K] L)) where
  isOpen_compl := isOpen_iff_mem_nhds.mpr fun sigma hsigma => by
    rw [Set.mem_compl_iff, SetLike.mem_coe,
      mem_decompositionGroup_iff_apply_mem] at hsigma
    rcases Classical.not_forall.mp hsigma with ⟨x, hx⟩
    let E : IntermediateField K L := IntermediateField.adjoin K {x}
    let : FiniteDimensional K E :=
      IntermediateField.adjoin.finiteDimensional
        (Algebra.IsIntegral.isIntegral x)
    apply mem_nhds_iff.mpr
    refine ⟨sigma • (E.fixingSubgroup : Set (L ≃ₐ[K] L)), ?_, ?_, ?_⟩
    · intro tau htau
      rcases Set.mem_smul_set.mp htau with ⟨g, hg, rfl⟩
      rw [Set.mem_compl_iff, SetLike.mem_coe,
        mem_decompositionGroup_iff_apply_mem]
      intro hmem
      apply hx
      have hgx : g x = x :=
        (IntermediateField.mem_fixingSubgroup_iff E g).mp hg x
          (IntermediateField.subset_adjoin (F := K) (S := {x}) (by simp))
      simpa [AlgEquiv.mul_apply, hgx] using hmem x
    · exact E.fixingSubgroup_isOpen.smul sigma
    · exact ⟨1, E.fixingSubgroup.one_mem, by simp⟩

end ValuationSubring
end HilbertRamification

end
end RamificationTheory
end

section
-- module Solutions.OAIQ244_DUKE.Ramification_ProfiniteInvariant
attribute [-instance] _root_.RamificationTheory.Field.absoluteGaloisGroup.decompositionSubgroupMulSemiringAction _root_.RamificationTheory.HilbertRamification.ValuationSubring.inertiaGroup_normal _root_.RamificationTheory.HilbertRamification.ValuationSubring.ramificationGroupInInertiaAut_normal _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

set_option autoImplicit false

namespace RamificationTheory

/-!
# Profinite invariant rings: normality on prime residue fields

The finite invariant-ring API proves that a prime residue extension is
normal. The residue-action exact sequence also needs the corresponding profinite
statement.  The proof is the same finite-orbit argument as in this construction: an
element of the discrete ring is fixed by an open normal subgroup, so its
orbit polynomial is computed in a finite quotient.
-/

noncomputable section

open scoped Pointwise

variable {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]
variable {G : Type*} [Group G] [MulSemiringAction G B] [SMulCommClass G A B]
variable [TopologicalSpace G] [CompactSpace G] [TotallyDisconnectedSpace G]
variable [IsTopologicalGroup G] [TopologicalSpace B] [DiscreteTopology B]
variable [ContinuousSMul G B] [Algebra.IsInvariant A B G]

namespace Ideal.Quotient

attribute [local instance] Ideal.Quotient.field

include G

/-- Profinite version of `Ideal.Quotient.normal`.

Every element has a finite orbit because the action on `B` is continuous and
`B` is discrete.  Passing to an open normal subgroup fixing a representative
reduces the splitting calculation to the finite quotient action. -/
theorem normal_of_profinite
    (P : Ideal A) (Q : Ideal B) [P.IsMaximal] [Q.IsMaximal] [Q.LiesOver P] :
    Normal (A ⧸ P) (B ⧸ Q) := by
  cases subsingleton_or_nontrivial B
  · cases ‹Q.IsMaximal›.ne_top (Subsingleton.elim _ _)
  have hIntegral : Algebra.IsIntegral A B :=
    Algebra.IsInvariant.isIntegral_of_profinite (G := G)
  constructor
  intro x
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
  obtain ⟨N, hN⟩ :=
    ProfiniteGrp.exist_openNormalSubgroup_sub_open_nhds_of_one
      (stabilizer_isOpen G x) (MulAction.mem_stabilizer_iff.mpr (one_smul G x))
  let B' := FixedPoints.subalgebra A B N.1.1
  let x' : B' := ⟨x, fun g ↦ hN g.2⟩
  let j : B' →ₐ[A] B := B'.val
  have hjx : j x' = x := rfl
  let : Algebra.IsInvariant A B' (G ⧸ N.1.1) := inferInstance
  cases nonempty_fintype (G ⧸ N.1.1)
  obtain ⟨p, hp, _hdegree, hpmonic⟩ :=
    Polynomial.lifts_and_degree_eq_and_monic
      (Algebra.IsInvariant.charpoly_mem_lifts A B' (G ⧸ N.1.1) x')
      (MulSemiringAction.monic_charpoly (G ⧸ N.1.1) x')
  let qB : B →+* B ⧸ Q := Ideal.Quotient.mk Q
  let qB' : B' →+* B ⧸ Q := qB.comp j.toRingHom
  have hroot : Polynomial.aeval (Ideal.Quotient.mk Q x)
      (p.map (algebraMap A (A ⧸ P))) = 0 := by
    rw [Polynomial.aeval_def, ← Polynomial.eval_map]
    have hmap :
        (p.map (algebraMap A B')).map qB' =
          p.map ((algebraMap (A ⧸ P) (B ⧸ Q)).comp
            (Ideal.Quotient.mk P)) := by
      rw [Polynomial.map_map]
      apply congrArg (fun f : A →+* B ⧸ Q ↦ p.map f)
      ext a
      rfl
    calc
      Polynomial.eval (Ideal.Quotient.mk Q x)
          ((p.map (algebraMap A (A ⧸ P))).map
            (algebraMap (A ⧸ P) (B ⧸ Q))) =
          Polynomial.eval (Ideal.Quotient.mk Q x)
            ((p.map (algebraMap A B')).map qB') := by
        rw [hmap, Polynomial.map_map, Ideal.Quotient.algebraMap_eq]
      _ = 0 := by
        rw [hp, show Ideal.Quotient.mk Q x = qB' x' from rfl,
          Polynomial.eval_map_apply, MulSemiringAction.eval_charpoly, map_zero]
  have hdiv := minpoly.dvd (A ⧸ P) (Ideal.Quotient.mk Q x)
    (p := p.map (algebraMap A (A ⧸ P))) hroot
  refine Polynomial.Splits.of_dvd ?_ ?_ ((Polynomial.map_dvd_map' _).mpr hdiv)
  · rw [Polynomial.map_map, ← IsScalarTower.algebraMap_eq,
      IsScalarTower.algebraMap_eq A B', ← Polynomial.map_map, hp,
      MulSemiringAction.charpoly_eq, Polynomial.map_prod]
    exact Polynomial.Splits.prod
      (fun _ _ ↦ (Polynomial.Splits.X_sub_C _).map _)
  · exact ((hpmonic.map _).map _).ne_zero

end Ideal.Quotient

end

end RamificationTheory
end

section
-- module Solutions.OAIQ244_DUKE.Ramification_HilbertRamification_ResidueExactSequence
attribute [-instance] _root_.RamificationTheory.Field.absoluteGaloisGroup.decompositionSubgroupMulSemiringAction _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

set_option autoImplicit false

namespace RamificationTheory

/-!
# The residue-action exact sequence

For a (possibly infinite) Galois extension and a chosen extension valuation,
the residue extension over the decomposition field is normal and reduction
gives the exact sequence

`1 → I_w → G_w → Gal(λ/κ) → 1`.

The base residue field is presented intrinsically as the quotient of the
fixed subring of the chosen valuation ring by the contraction of its maximal
ideal.  This fixed subring is exactly the valuation ring on the decomposition
field.  The profinite surjectivity proof is the compact inverse-limit argument
used in this construction, supplied by `Ideal.Quotient.stabilizerHom_surjective_of_profinite`.
-/

noncomputable section

universe u v

namespace HilbertRamification
namespace ValuationSubring

open scoped Pointwise Topology

variable (K : Type u) {L : Type v} [Field K] [Field L] [Algebra K L]
variable [IsGalois K L]

/-- The valuation ring on the decomposition field, represented inside the
chosen valuation ring as the fixed subring of the decomposition group. -/
abbrev decompositionFixedSubring (A : _root_.ValuationSubring L) : Subring A :=
  FixedPoints.subring A (decompositionGroup K A)

/-- The maximal ideal of the decomposition-field valuation ring. -/
abbrev decompositionFixedMaximalIdeal (A : _root_.ValuationSubring L) :
    Ideal (decompositionFixedSubring K A) :=
  (IsLocalRing.maximalIdeal A).comap (decompositionFixedSubring K A).subtype

/-- The actual base residue field `κ` in the residue-action exact sequence. -/
abbrev decompositionResidueField (A : _root_.ValuationSubring L) :=
  decompositionFixedSubring K A ⧸ decompositionFixedMaximalIdeal K A

/-- The actual target residue field `λ`. -/
abbrev selectedResidueField (A : _root_.ValuationSubring L) :=
  IsLocalRing.ResidueField A

/-- The literal valuation ring on the classical decomposition field `Z_w`. -/
abbrev decompositionFieldValuationSubring
    (A : _root_.ValuationSubring L) :
    _root_.ValuationSubring (decompositionField K A) :=
  A.comap (decompositionField K A).val

/-- The fixed-subring presentation used in the residue-action exact sequence is canonically
the literal valuation ring on `Z_w`. -/
def decompositionFieldValuationSubringEquivFixedSubring
    (A : _root_.ValuationSubring L) :
    decompositionFieldValuationSubring K A ≃+*
      decompositionFixedSubring K A where
  toFun z :=
    ⟨⟨((z : decompositionField K A) : L), z.property⟩, by
      intro sigma
      apply Subtype.ext
      change ((sigma : decompositionGroup K A) : L ≃ₐ[K] L)
          ((z : decompositionField K A) : L) =
        ((z : decompositionField K A) : L)
      exact (IntermediateField.mem_fixedField_iff
        (H := decompositionGroup K A) ((z : decompositionField K A) : L)).mp
          (z : decompositionField K A).property
          (sigma : L ≃ₐ[K] L) sigma.property⟩
  invFun r := by
    let z : decompositionField K A :=
      ⟨((r : A) : L), by
        rw [IntermediateField.mem_fixedField_iff]
        intro sigma hsigma
        have hr := r.property ⟨sigma, hsigma⟩
        exact congrArg Subtype.val hr⟩
    exact ⟨z, r.val.property⟩
  left_inv z := by ext; rfl
  right_inv r := by ext; rfl
  map_add' _ _ := by ext; rfl
  map_mul' _ _ := by ext; rfl

/-- Provides the instance `instIsLocalRing`. -/
instance decompositionFixedSubring.instIsLocalRing
    (A : _root_.ValuationSubring L) :
    IsLocalRing (decompositionFixedSubring K A) :=
  (decompositionFieldValuationSubringEquivFixedSubring (K := K) A).isLocalRing

theorem decompositionGroup_action_locallyConstant
    (A : _root_.ValuationSubring L) (a : A) :
    IsLocallyConstant (fun g : decompositionGroup K A ↦ g • a) := by
  rw [IsLocallyConstant.iff_exists_open]
  intro sigma
  let E : IntermediateField K L := IntermediateField.adjoin K {(a : L)}
  let : FiniteDimensional K E :=
    IntermediateField.adjoin.finiteDimensional
      (Algebra.IsIntegral.isIntegral (a : L))
  let U : Set (decompositionGroup K A) :=
    ((↑) : decompositionGroup K A → (L ≃ₐ[K] L)) ⁻¹'
      (((sigma : L ≃ₐ[K] L)) • (E.fixingSubgroup : Set (L ≃ₐ[K] L)))
  refine ⟨U, E.fixingSubgroup_isOpen.smul
      (sigma : L ≃ₐ[K] L) |>.preimage continuous_subtype_val, ?_, ?_⟩
  · exact ⟨1, E.fixingSubgroup.one_mem, by simp⟩
  · intro tau htau
    rcases htau with ⟨g, hg, heq⟩
    have hga : g (a : L) = (a : L) :=
      (IntermediateField.mem_fixingSubgroup_iff E g).mp hg (a : L)
        (IntermediateField.subset_adjoin (F := K) (S := {(a : L)}) (by simp))
    apply Subtype.ext
    change (((tau : decompositionGroup K A) : L ≃ₐ[K] L) (a : L)) =
      (((sigma : decompositionGroup K A) : L ≃ₐ[K] L) (a : L))
    rw [← heq]
    simp [AlgEquiv.mul_apply, hga]

theorem decompositionGroup_continuousSMul
    (A : _root_.ValuationSubring L) :
    letI : TopologicalSpace A := ⊥
    ContinuousSMul (decompositionGroup K A) A := by
  let : TopologicalSpace A := ⊥
  let : DiscreteTopology A := ⟨rfl⟩
  constructor
  rw [continuous_prod_of_discrete_right]
  intro a
  exact (decompositionGroup_action_locallyConstant (K := K) A a).continuous

theorem decompositionGroup_compactSpace
    (A : _root_.ValuationSubring L) :
    CompactSpace (decompositionGroup K A) := by
  have hc : IsCompact (decompositionGroup K A : Set (L ≃ₐ[K] L)) :=
    (decompositionGroup_isClosed K A).isCompact
  exact isCompact_iff_compactSpace.mp hc

omit [IsGalois K L] in
theorem decompositionFixedSubring_smulCommClass
    (A : _root_.ValuationSubring L) :
    SMulCommClass (decompositionGroup K A)
      (decompositionFixedSubring K A) A := by
  constructor
  intro g r x
  change g • ((r : A) * x) = (r : A) * (g • x)
  rw [smul_mul', r.property g]

omit [IsGalois K L] in
theorem decompositionFixedSubring_isInvariant
    (A : _root_.ValuationSubring L) :
    Algebra.IsInvariant (decompositionFixedSubring K A) A
      (decompositionGroup K A) := by
  constructor
  intro x hx
  exact ⟨⟨x, hx⟩, rfl⟩

/-- Provides the instance `instSMulCommClass`. -/
instance decompositionFixedSubring.instSMulCommClass
    (A : _root_.ValuationSubring L) :
    SMulCommClass (decompositionGroup K A)
      (decompositionFixedSubring K A) A :=
  decompositionFixedSubring_smulCommClass (K := K) A

theorem decompositionFixedMaximalIdeal_isMaximal
    (A : _root_.ValuationSubring L) :
    (decompositionFixedMaximalIdeal K A).IsMaximal := by
  let : TopologicalSpace A := ⊥
  let : DiscreteTopology A := ⟨rfl⟩
  let : CompactSpace (decompositionGroup K A) :=
    decompositionGroup_compactSpace (K := K) A
  let : ContinuousSMul (decompositionGroup K A) A :=
    decompositionGroup_continuousSMul (K := K) A
  let : SMulCommClass (decompositionGroup K A)
      (decompositionFixedSubring K A) A :=
    decompositionFixedSubring_smulCommClass (K := K) A
  let : Algebra.IsInvariant (decompositionFixedSubring K A) A
      (decompositionGroup K A) :=
    decompositionFixedSubring_isInvariant (K := K) A
  let : Algebra.IsIntegral (decompositionFixedSubring K A) A :=
    Algebra.IsInvariant.isIntegral_of_profinite
      (G := decompositionGroup K A)
  exact Ideal.isMaximal_comap_of_isIntegral_of_isMaximal'
    (decompositionFixedSubring K A).subtype
    (fun x => Algebra.IsIntegral.isIntegral x)
    (IsLocalRing.maximalIdeal A)

/-- Provides the instance `instIsMaximal`. -/
instance decompositionFixedMaximalIdeal.instIsMaximal
    (A : _root_.ValuationSubring L) :
    (decompositionFixedMaximalIdeal K A).IsMaximal :=
  decompositionFixedMaximalIdeal_isMaximal (K := K) A

/-- The contracted ideal used in the intrinsic presentation is the actual
maximal ideal of the valuation ring on `Z_w`. -/
theorem decompositionFixedMaximalIdeal_eq_maximalIdeal
    (A : _root_.ValuationSubring L) :
    decompositionFixedMaximalIdeal K A =
      IsLocalRing.maximalIdeal (decompositionFixedSubring K A) :=
  IsLocalRing.eq_maximalIdeal
    (decompositionFixedMaximalIdeal.instIsMaximal (K := K) A)

/-- Canonical identification of the literal residue field of `Z_w` with the
base residue field used by the residue-action exact sequence. -/
def decompositionFieldResidueEquiv
    (A : _root_.ValuationSubring L) :
    IsLocalRing.ResidueField (decompositionFieldValuationSubring K A) ≃+*
      decompositionResidueField K A :=
  (IsLocalRing.ResidueField.mapEquiv
      (decompositionFieldValuationSubringEquivFixedSubring (K := K) A)).trans
    (Ideal.quotientEquivAlgOfEq ℤ
      (decompositionFixedMaximalIdeal_eq_maximalIdeal (K := K) A).symm).toRingEquiv

/-- Provides the instance `instLiesOver`. -/
instance selectedMaximalIdeal.instLiesOver
    (A : _root_.ValuationSubring L) :
    (IsLocalRing.maximalIdeal A).LiesOver
      (decompositionFixedMaximalIdeal K A) := by
  constructor
  rfl

/-- Provides the instance `instField`. -/
noncomputable instance decompositionResidueField.instField
    (A : _root_.ValuationSubring L) :
    Field (decompositionResidueField K A) :=
  Ideal.Quotient.field (decompositionFixedMaximalIdeal K A)

/-- Provides the instance `instAlgebra`. -/
noncomputable instance selectedResidueField.instAlgebra
    (A : _root_.ValuationSubring L) :
    Algebra (decompositionResidueField K A) (selectedResidueField A) :=
  Ideal.Quotient.algebraQuotientOfLEComap
    (le_of_eq ((IsLocalRing.maximalIdeal A).over_def
      (decompositionFixedMaximalIdeal K A)))

omit [IsGalois K L] in
/-- Every decomposition-group automorphism stabilizes the maximal ideal of
the selected valuation ring. -/
theorem decompositionGroup_maximalIdeal_stabilizer_eq_top
    (A : _root_.ValuationSubring L) :
    MulAction.stabilizer (decompositionGroup K A)
        (IsLocalRing.maximalIdeal A) = ⊤ := by
  apply top_unique
  intro sigma _hsigma
  change sigma • IsLocalRing.maximalIdeal A = IsLocalRing.maximalIdeal A
  apply Ideal.ext
  intro x
  rw [Ideal.mem_pointwise_smul_iff_inv_smul_mem]
  simp only [IsLocalRing.mem_maximalIdeal]
  constructor
  · intro hnonunit hx
    apply hnonunit
    simpa using hx.map (MulSemiringAction.toRingAut
      (decompositionGroup K A) A sigma⁻¹)
  · intro hnonunit hx
    apply hnonunit
    simpa using hx.map (MulSemiringAction.toRingAut
      (decompositionGroup K A) A sigma)

/-- The canonical identification of the decomposition group with the
stabilizer of the selected maximal ideal. -/
def decompositionGroupToMaximalIdealStabilizer
    (A : _root_.ValuationSubring L) :
    decompositionGroup K A →*
      MulAction.stabilizer (decompositionGroup K A)
        (IsLocalRing.maximalIdeal A) where
  toFun sigma := ⟨sigma, by
    rw [decompositionGroup_maximalIdeal_stabilizer_eq_top (K := K) A]
    exact Subgroup.mem_top sigma⟩
  map_one' := rfl
  map_mul' _ _ := rfl

/-- The residue-action exact sequence: the residue action of `G_w` on `λ/κ`. -/
def decompositionGroupResidueAction
    (A : _root_.ValuationSubring L) :
    decompositionGroup K A →*
      (selectedResidueField A ≃ₐ[decompositionResidueField K A]
        selectedResidueField A) :=
  (Ideal.Quotient.stabilizerHom
      (IsLocalRing.maximalIdeal A)
      (decompositionFixedMaximalIdeal K A)
      (decompositionGroup K A)).comp
    (decompositionGroupToMaximalIdealStabilizer (K := K) A)

omit [IsGalois K L] in
/-- States the theorem `decompositionGroupResidueAction_residue`. -/
@[simp] theorem decompositionGroupResidueAction_residue
    (A : _root_.ValuationSubring L)
    (sigma : decompositionGroup K A) (x : A) :
    decompositionGroupResidueAction (K := K) A sigma
        (IsLocalRing.residue A x) =
      IsLocalRing.residue A (sigma • x) :=
  rfl

/-- The residue-action exact sequence, including the infinite case: reduction is onto the full
residue Galois group. -/
theorem decompositionGroupResidueAction_surjective
    (A : _root_.ValuationSubring L) :
    Function.Surjective (decompositionGroupResidueAction (K := K) A) := by
  let : TopologicalSpace A := ⊥
  let : DiscreteTopology A := ⟨rfl⟩
  let : CompactSpace (decompositionGroup K A) :=
    decompositionGroup_compactSpace (K := K) A
  let : ContinuousSMul (decompositionGroup K A) A :=
    decompositionGroup_continuousSMul (K := K) A
  let : SMulCommClass (decompositionGroup K A)
      (decompositionFixedSubring K A) A :=
    decompositionFixedSubring_smulCommClass (K := K) A
  let : Algebra.IsInvariant (decompositionFixedSubring K A) A
      (decompositionGroup K A) :=
    decompositionFixedSubring_isInvariant (K := K) A
  intro sigma
  obtain ⟨tau, htau⟩ :=
    Ideal.Quotient.stabilizerHom_surjective_of_profinite
      (G := decompositionGroup K A)
      (decompositionFixedMaximalIdeal K A)
      (IsLocalRing.maximalIdeal A) sigma
  refine ⟨tau.1, ?_⟩
  have htau_eq :
      decompositionGroupToMaximalIdealStabilizer (K := K) A tau.1 = tau := by
    apply Subtype.ext
    rfl
  change
    Ideal.Quotient.stabilizerHom
        (IsLocalRing.maximalIdeal A)
        (decompositionFixedMaximalIdeal K A)
        (decompositionGroup K A)
        (decompositionGroupToMaximalIdealStabilizer (K := K) A tau.1) =
      sigma
  rw [htau_eq]
  exact htau

/-- The residue-action exact sequence: `λ/κ` is normal, also in the infinite case. -/
instance decompositionResidueExtension_normal
    (A : _root_.ValuationSubring L) :
    Normal (decompositionResidueField K A) (selectedResidueField A) := by
  let : TopologicalSpace A := ⊥
  let : DiscreteTopology A := ⟨rfl⟩
  let : CompactSpace (decompositionGroup K A) :=
    decompositionGroup_compactSpace (K := K) A
  let : ContinuousSMul (decompositionGroup K A) A :=
    decompositionGroup_continuousSMul (K := K) A
  let : SMulCommClass (decompositionGroup K A)
      (decompositionFixedSubring K A) A :=
    decompositionFixedSubring_smulCommClass (K := K) A
  let : Algebra.IsInvariant (decompositionFixedSubring K A) A
      (decompositionGroup K A) :=
    decompositionFixedSubring_isInvariant (K := K) A
  exact RamificationTheory.Ideal.Quotient.normal_of_profinite
    (G := decompositionGroup K A)
    (decompositionFixedMaximalIdeal K A)
    (IsLocalRing.maximalIdeal A)

end ValuationSubring
end HilbertRamification

end

end RamificationTheory
end

section
-- module Solutions.OAIQ244_DUKE.LocalClassFieldTheory_Finite_LocalReciprocity_ResidueActionIndex
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

set_option autoImplicit false

namespace LocalClassFieldTheory

open RamificationTheory

/-!
# Finite local reciprocity: residue-action image indices

This file separates the two group-theoretic comparisons used by the local
degree map.  The residue-action exact-sequence theorem supplies the actual action of an absolute
decomposition group on the selected residue algebraic closure.  Once the
decomposition group is all of the absolute Galois group, that action is
surjective.  If a finite-index subgroup has residue-action image equal to the
fixing group of a finite residue subextension, its degree image has the
ordinary residue-field index.
-/

noncomputable section

universe u v

open _root_.RamificationTheory.HilbertRamification.ValuationSubring

variable (K : Type u) {L : Type v} [Field K] [Field L] [Algebra K L]
  [IsGalois K L]

/-- View every ambient Galois automorphism as a decomposition-group element
when the chosen extension valuation has full decomposition group.  This is
kept generic in the Galois ambient field: the ambient field is the
separable closure, not the algebraic closure (the latter need not be Galois
over an imperfect local field). -/
noncomputable def toDecompositionGroupOfEqTop
    (A : _root_.ValuationSubring L)
    (hA : decompositionGroup K A = ⊤) :
    (L ≃ₐ[K] L) →* decompositionGroup K A where
  toFun sigma := ⟨sigma, by rw [hA]; exact Subgroup.mem_top sigma⟩
  map_one' := by ext; rfl
  map_mul' _ _ := by ext; rfl

omit [IsGalois K L] in
/-- States the theorem `toDecompositionGroupOfEqTop_coe`. -/
@[simp] theorem toDecompositionGroupOfEqTop_coe
    (A : _root_.ValuationSubring L)
    (hA : decompositionGroup K A = ⊤)
    (sigma : L ≃ₐ[K] L) :
    (toDecompositionGroupOfEqTop K A hA sigma : L ≃ₐ[K] L) = sigma :=
  rfl

/-- The residue action from the exact sequence, viewed on the whole Galois group
when the chosen extension valuation has full decomposition group. -/
noncomputable def residueAlgActionOfEqTop
    (A : _root_.ValuationSubring L)
    (hA : decompositionGroup K A = ⊤) :
    (L ≃ₐ[K] L) →*
      (selectedResidueField A ≃ₐ[decompositionResidueField K A]
        selectedResidueField A) :=
  (decompositionGroupResidueAction (K := K) A).comp
    (toDecompositionGroupOfEqTop K A hA)

/-- States the theorem `residueAlgActionOfEqTop_surjective`. -/
theorem residueAlgActionOfEqTop_surjective
    (A : _root_.ValuationSubring L)
    (hA : decompositionGroup K A = ⊤) :
    Function.Surjective (residueAlgActionOfEqTop K A hA) := by
  intro tau
  obtain ⟨sigma, hsigma⟩ :=
    decompositionGroupResidueAction_surjective (K := K) A tau
  refine ⟨(sigma : L ≃ₐ[K] L), ?_⟩
  have heq :
      toDecompositionGroupOfEqTop K A hA (sigma : L ≃ₐ[K] L) = sigma := by
    ext
    rfl
  simpa [residueAlgActionOfEqTop, heq] using hsigma

end
end LocalClassFieldTheory
end

section
-- module Solutions.OAIQ244_DUKE.LocalClassFieldTheory_Finite_LocalReciprocity_LocalResidueDatum
set_option synthInstance.maxHeartbeats 400000
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

set_option autoImplicit false

namespace LocalClassFieldTheory

open ValuationTheory RamificationTheory LocalFieldTheory

/-!
# Finite local reciprocity: the local residue degree datum

For a nonarchimedean local field `K`, this file makes the choices implicit in
the construction explicit.  The canonical local valuation is packaged as a complete
DVF, Chevalley's theorem chooses an extension to `AlgebraicClosure K`, and
that valuation is pulled back to `SeparableClosure K`.  Finite-separable
uniqueness shows that its decomposition subgroup is the whole Galois group.
The residue field of the decomposition field is then identified with the
finite residue field of `K`.

The remaining step is topological: the reduction action is shown continuous
for the two Krull topologies and is composed with the intrinsic finite-field
degree map from `ResidueAlgebraicClosureDegree`.  The selected residue field
is algebraically closed because its extension to the residue of
`AlgebraicClosure K` is purely inseparable and the selected residue field is
perfect over the finite base residue field.
-/

noncomputable section

open scoped Pointwise ValuativeRel
open _root_.RamificationTheory.HilbertRamification.ValuationSubring
open Field.absoluteGaloisGroup

variable (K : Type) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]

local instance localSeparableClosureAlgebra :
    Algebra (SeparableClosure K) (AlgebraicClosure K) :=
  (separableClosure K (AlgebraicClosure K)).val.toRingHom.toAlgebra

/-! ## The canonical complete discrete valuation and its absolute extension -/

/-! ## Identification of the finite base residue field -/

/-! ## Continuity of reduction and the local degree map -/

end
end LocalClassFieldTheory
end

section
-- module Solutions.OAIQ244_DUKE.LocalClassFieldTheory_Finite_LocalReciprocity_FiniteResidueFinrankTransfer
set_option synthInstance.maxHeartbeats 400000
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

set_option autoImplicit false

namespace LocalClassFieldTheory
open RamificationTheory

open LocalFieldTheory ValuationTheory

/-!
# Finite local reciprocity: comparison of the two finite residue-field models

The residue-action exact sequence presents the residue field of a
finite fixed field intrinsically, inside the selected residue algebraic
closure.  The norm formula uses the literal residue field of the spectral
valuation on that fixed field.  This file compares those presentations by
the uniqueness of the finite extension valuation.
-/

noncomputable section

open scoped ValuativeRel
open _root_.RamificationTheory.HilbertRamification.ValuationSubring

universe u v

/-- If the decomposition group of an ambient valuation ring is the whole
Galois group, its decomposition-field valuation ring is canonically
equivalent to the given valuation ring on the ground field. -/
noncomputable def valuationSubringEquivDecompositionFieldOfEqTop
    {F : Type u} {Omega : Type v} [Field F] [Field Omega] [Algebra F Omega]
    [IsGalois F Omega]
    (A : ValuationSubring Omega) (C : ValuationSubring F)
    (hC : A.comap (algebraMap F Omega) = C)
    (hA : decompositionGroup F A = ⊤) :
    C ≃+* decompositionFieldValuationSubring F A := by
  let Z := decompositionField F A
  have hZ : Z = ⊥ := by
    change IntermediateField.fixedField (decompositionGroup F A) = ⊥
    rw [hA]
    simpa using
      (InfiniteGalois.fixedField_fixingSubgroup
        (⊥ : IntermediateField F Omega))
  let eFZ : F ≃ₐ[F] Z :=
    (IntermediateField.botEquiv F Omega).symm.trans
      (IntermediateField.equivOfEq hZ.symm)
  refine
    { toFun := fun x => ⟨eFZ (x : F), ?_⟩
      invFun := fun z => ⟨eFZ.symm (z : Z), ?_⟩
      left_inv := fun x => by
        apply Subtype.ext
        exact eFZ.symm_apply_apply (x : F)
      right_inv := fun z => by
        apply Subtype.ext
        exact eFZ.apply_symm_apply (z : Z)
      map_add' := fun x y => by
        apply Subtype.ext
        exact map_add eFZ (x : F) (y : F)
      map_mul' := fun x y => by
        apply Subtype.ext
        exact map_mul eFZ (x : F) (y : F) }
  · change ((eFZ x : Z) : Omega) ∈ A
    have he : ((eFZ x : Z) : Omega) =
        algebraMap F Omega (x : F) := by
      rfl
    rw [he]
    have hx : (x : F) ∈ A.comap (algebraMap F Omega) := by
      rw [hC]
      exact x.property
    exact hx
  · have hz : eFZ.symm (z : Z) ∈ A.comap (algebraMap F Omega) := by
      change algebraMap F Omega (eFZ.symm (z : Z)) ∈ A
      have he : algebraMap F Omega (eFZ.symm (z : Z)) =
          ((z : Z) : Omega) := by
        exact congrArg Subtype.val (eFZ.apply_symm_apply (z : Z))
      rw [he]
      exact z.property
    rw [hC] at hz
    exact hz

/-! ## The finite fixed-field comparison -/

end
end LocalClassFieldTheory
end

section
-- module Solutions.OAIQ244_DUKE.GroupTheory_Finite
attribute [-instance] _root_.RamificationTheory.HilbertRamification.ValuationSubring.inertiaGroup_normal _root_.RamificationTheory.HilbertRamification.ValuationSubring.ramificationGroupInInertiaAut_normal _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

set_option autoImplicit false

/-!
# Finite group theory for the splitting corollaries

This file isolates the finite-group inputs for prime-power and normal-closure
splitting arguments.

For the prime-power subgroup reduction, a proper subgroup of a finite group of order `p ^ v` is
contained in a subgroup of index `p`.  The proof below gives the
slightly stronger statement for arbitrary finite `p`-groups.  In the
cyclic case the resulting subgroup is normal, hence produces the
degree-`p` quotient used to choose the intermediate field.

For the normal-closure splitting argument, the normal closure is encoded by a core-free subgroup
`H`.  The canonical map from left cosets to double cosets is
surjective.  If it does not decrease cardinality, its right subgroup
is contained in the normal core of `H`; therefore it is trivial when
`H` is core-free.
-/

noncomputable section

universe uG

section PrimePower

variable {G : Type uG} [Group G] [Finite G]

/-- A proper subgroup of a finite group of prime-power order is
contained in a subgroup of index `p`.

This is the group-theoretic step in the prime-power subgroup reduction.  Mathlib's Sylow
extension theorem proves the stronger result without a cyclicity
assumption. -/
theorem exists_index_prime_supergroup_of_card_prime_power
    {p v : ℕ}
    (hp : p.Prime)
    (hv : 0 < v)
    (hGcard : Nat.card G = p ^ v)
    (D : Subgroup G)
    (hD : D ≠ ⊤) :
    ∃ P : Subgroup G, D ≤ P ∧ P.index = p := by
  let : Fact p.Prime := ⟨hp⟩
  have hGp : IsPGroup p G :=
    IsPGroup.of_card hGcard
  have hDp : IsPGroup p D :=
    hGp.to_subgroup D
  obtain ⟨m, hDcard⟩ :=
    IsPGroup.exists_card_eq hDp
  have hmv : m < v := by
    have hmle : m ≤ v := by
      apply
        (Nat.pow_le_pow_iff_right hp.one_lt).mp
      rw [← hDcard, ← hGcard]
      exact D.card_le_card_group
    have hmne : m ≠ v := by
      intro hmv
      apply hD
      apply
        (Subgroup.card_eq_iff_eq_top D).mp
      rw [hDcard, hmv, hGcard]
    exact lt_of_le_of_ne hmle hmne
  have hmPred : m ≤ v - 1 :=
    Nat.le_sub_one_of_lt hmv
  have hpowDvd :
      p ^ (v - 1) ∣ Nat.card G := by
    rw [hGcard]
    exact
      pow_dvd_pow p (Nat.sub_le v 1)
  obtain ⟨P, hPcard, hDP⟩ :=
    Sylow.exists_subgroup_card_pow_prime_le
      p hpowDvd D hDcard hmPred
  refine ⟨P, hDP, ?_⟩
  have hmul :
      p ^ (v - 1) * P.index = p ^ v := by
    simpa [hPcard, hGcard] using
      P.card_mul_index
  have hvPred : v - 1 + 1 = v :=
    Nat.sub_add_cancel hv
  rw [← hvPred, pow_succ] at hmul
  exact
    Nat.mul_left_cancel (pow_pos hp.pos _) hmul

/-- In a cyclic finite group of prime-power order, the index-`p`
supergroup is normal and its quotient has order `p`. -/
theorem cyclic_exists_normal_index_prime_supergroup
    [IsCyclic G]
    {p v : ℕ}
    (hp : p.Prime)
    (hv : 0 < v)
    (hGcard : Nat.card G = p ^ v)
    (D : Subgroup G)
    (hD : D ≠ ⊤) :
    ∃ P : Subgroup G,
      D ≤ P ∧
      P.index = p ∧
      P.Normal ∧
      Nat.card (G ⧸ P) = p := by
  obtain ⟨P, hDP, hPindex⟩ :=
    exists_index_prime_supergroup_of_card_prime_power
      hp hv hGcard D hD
  have hPnormal : P.Normal :=
    inferInstance
  refine
    ⟨P, hDP, hPindex, hPnormal, ?_⟩
  rw [← P.index_eq_card]
  exact hPindex

omit [Finite G] in
/-- In a cyclic group of finite prime-power cardinality, every proper
subgroup is contained in every subgroup of index `p`. -/
theorem subgroup_le_index_prime_subgroup_of_ne_top_cyclic_prime_power
    [IsCyclic G]
    {p exponent : ℕ}
    (hp : p.Prime)
    (hcard : Nat.card G = p ^ exponent)
    (P D : Subgroup G)
    (hPindex : P.index = p)
    (hD : D ≠ ⊤) :
    D ≤ P := by
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := G)
  have hgtop : Subgroup.zpowers g = ⊤ :=
    (Subgroup.eq_top_iff' (Subgroup.zpowers g)).2 hg
  obtain ⟨n, hn⟩ :=
    (Subgroup.le_zpowers_iff g D).1 (by
      rw [hgtop]
      exact le_top)
  have hgorder : orderOf g = p ^ exponent :=
    (orderOf_eq_card_of_forall_mem_zpowers hg).trans hcard
  have hngcd : n.gcd (orderOf g) ≠ 1 := by
    intro hngcd
    apply hD
    rw [hn]
    apply top_unique
    rw [← hgtop, Subgroup.zpowers_le]
    exact mem_zpowers_pow_iff.mpr hngcd
  have hpdiv : p ∣ n := by
    by_contra hpnot
    apply hngcd
    rw [hgorder]
    exact
      (((hp.coprime_iff_not_dvd).2 hpnot).symm.pow_right
        exponent).gcd_eq_one
  obtain ⟨k, rfl⟩ := hpdiv
  rw [hn]
  apply (Subgroup.zpowers_le).2
  have hpow := P.pow_index_mem (g ^ k)
  rw [hPindex] at hpow
  have heq : (g ^ k) ^ p = g ^ (p * k) := by
    simp only [← pow_mul, Nat.mul_comm]
  rw [← heq]
  exact hpow

end PrimePower
end
end

section
-- module Solutions.OAIQ244_DUKE.AlgebraicNumberTheory_Galois_CyclicPrimeSubextension
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

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

variable {K L : Type}
    [Field K] [NumberField K]
    [Field L] [NumberField L]
    [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    [IsCyclic (L ≃ₐ[K] L)]

omit [NumberField K] [NumberField L] [IsGalois K L] in
/-- A cyclic group of nonzero prime-power order has an actual normal
subgroup of index `p`. -/
theorem exists_index_prime_normal_subgroup
    {p exponent : ℕ}
    (hp : p.Prime)
    (hexponent : 0 < exponent)
    (hcard :
      Nat.card (L ≃ₐ[K] L) =
        p ^ exponent) :
    ∃ P : Subgroup (L ≃ₐ[K] L),
      P.index = p ∧
      P.Normal ∧
      Nat.card ((L ≃ₐ[K] L) ⧸ P) = p := by
  have hgroupCard :
      1 < Nat.card (L ≃ₐ[K] L) := by
    rw [hcard]
    exact
      one_lt_pow₀ hp.one_lt hexponent.ne'
  let : Nontrivial (L ≃ₐ[K] L) :=
    Finite.one_lt_card_iff_nontrivial.mp
      hgroupCard
  obtain
      ⟨P, _hbot, hPindex, hPnormal,
        hPquotient⟩ :=
    cyclic_exists_normal_index_prime_supergroup
      hp hexponent hcard
      (⊥ : Subgroup (L ≃ₐ[K] L))
      bot_ne_top
  exact
    ⟨P, hPindex, hPnormal, hPquotient⟩

/-- The chosen index-`p` subgroup of the global cyclic Galois group. -/
noncomputable def cyclicPrimeIndexSubgroup
    {p exponent : ℕ}
    (hp : p.Prime)
    (hexponent : 0 < exponent)
    (hcard :
      Nat.card (L ≃ₐ[K] L) =
        p ^ exponent) :
    Subgroup (L ≃ₐ[K] L) :=
  (exists_index_prime_normal_subgroup
    (K := K) (L := L)
    hp hexponent hcard).choose

omit [NumberField K] [NumberField L] [IsGalois K L] in
theorem cyclicPrimeIndexSubgroup_index
    {p exponent : ℕ}
    (hp : p.Prime)
    (hexponent : 0 < exponent)
    (hcard :
      Nat.card (L ≃ₐ[K] L) =
        p ^ exponent) :
    (cyclicPrimeIndexSubgroup
      (K := K) (L := L)
      hp hexponent hcard).index = p :=
  (exists_index_prime_normal_subgroup
    (K := K) (L := L)
    hp hexponent hcard).choose_spec.1

omit [NumberField K] [NumberField L] [IsGalois K L] in
theorem cyclicPrimeIndexSubgroup_normal
    {p exponent : ℕ}
    (hp : p.Prime)
    (hexponent : 0 < exponent)
    (hcard :
      Nat.card (L ≃ₐ[K] L) =
        p ^ exponent) :
    (cyclicPrimeIndexSubgroup
      (K := K) (L := L)
      hp hexponent hcard).Normal :=
  (exists_index_prime_normal_subgroup
    (K := K) (L := L)
    hp hexponent hcard).choose_spec.2.1

omit [NumberField K] [NumberField L] [IsGalois K L] in
theorem cyclicPrimeIndexSubgroup_quotient_card
    {p exponent : ℕ}
    (hp : p.Prime)
    (hexponent : 0 < exponent)
    (hcard :
      Nat.card (L ≃ₐ[K] L) =
        p ^ exponent) :
    Nat.card
        ((L ≃ₐ[K] L) ⧸
          cyclicPrimeIndexSubgroup
            (K := K) (L := L)
            hp hexponent hcard) =
      p :=
  (exists_index_prime_normal_subgroup
    (K := K) (L := L)
    hp hexponent hcard).choose_spec.2.2

/-- The actual degree-`p` intermediate field in the cyclic prime-power reduction. -/
noncomputable def cyclicPrimeSubextension
    {p exponent : ℕ}
    (hp : p.Prime)
    (hexponent : 0 < exponent)
    (hcard :
      Nat.card (L ≃ₐ[K] L) =
        p ^ exponent) :
    IntermediateField K L :=
  IntermediateField.fixedField
    (cyclicPrimeIndexSubgroup
      (K := K) (L := L)
      hp hexponent hcard)

omit [NumberField K] [NumberField L] in
/-- The constructed intermediate extension is Galois over `K`. -/
noncomputable instance cyclicPrimeSubextension_isGalois
    {p exponent : ℕ}
    (hp : p.Prime)
    (hexponent : 0 < exponent)
    (hcard :
      Nat.card (L ≃ₐ[K] L) =
        p ^ exponent) :
    IsGalois K
      (cyclicPrimeSubextension
        (K := K) (L := L)
        hp hexponent hcard) := by
  unfold cyclicPrimeSubextension
  let P :=
    cyclicPrimeIndexSubgroup
      (K := K) (L := L)
      hp hexponent hcard
  let : P.Normal :=
    cyclicPrimeIndexSubgroup_normal
      (K := K) (L := L)
      hp hexponent hcard
  infer_instance

omit [NumberField K] [NumberField L] in
/-- The constructed intermediate extension has degree exactly `p`. -/
theorem cyclicPrimeSubextension_finrank
    {p exponent : ℕ}
    (hp : p.Prime)
    (hexponent : 0 < exponent)
    (hcard :
      Nat.card (L ≃ₐ[K] L) =
        p ^ exponent) :
    Module.finrank K
        (cyclicPrimeSubextension
          (K := K) (L := L)
          hp hexponent hcard) =
      p := by
  let P :=
    cyclicPrimeIndexSubgroup
      (K := K) (L := L)
      hp hexponent hcard
  let M :=
    cyclicPrimeSubextension
      (K := K) (L := L)
      hp hexponent hcard
  let : P.Normal :=
    cyclicPrimeIndexSubgroup_normal
      (K := K) (L := L)
      hp hexponent hcard
  let : IsGalois K M :=
    cyclicPrimeSubextension_isGalois
      (K := K) (L := L)
      hp hexponent hcard
  calc
    Module.finrank K M =
        Nat.card (M ≃ₐ[K] M) :=
      (IsGalois.card_aut_eq_finrank K M).symm
    _ = Nat.card ((L ≃ₐ[K] L) ⧸ P) :=
      Nat.card_congr
        (IsGalois.normalAutEquivQuotient P).symm.toEquiv
    _ = p :=
      cyclicPrimeIndexSubgroup_quotient_card
        (K := K) (L := L)
        hp hexponent hcard

omit [NumberField K] [NumberField L] in
/-- The Galois group of the constructed degree-`p` extension is
cyclic. -/
theorem cyclicPrimeSubextension_isCyclic
    {p exponent : ℕ}
    (hp : p.Prime)
    (hexponent : 0 < exponent)
    (hcard :
      Nat.card (L ≃ₐ[K] L) =
        p ^ exponent) :
    IsCyclic
      (cyclicPrimeSubextension
          (K := K) (L := L)
          hp hexponent hcard ≃ₐ[K]
        cyclicPrimeSubextension
          (K := K) (L := L)
          hp hexponent hcard) := by
  let P :=
    cyclicPrimeIndexSubgroup
      (K := K) (L := L)
      hp hexponent hcard
  let : P.Normal :=
    cyclicPrimeIndexSubgroup_normal
      (K := K) (L := L)
      hp hexponent hcard
  have hquotient :
      IsCyclic ((L ≃ₐ[K] L) ⧸ P) :=
    isCyclic_of_surjective
      (QuotientGroup.mk' P)
      (QuotientGroup.mk'_surjective P)
  exact
    (IsGalois.normalAutEquivQuotient P).isCyclic.mp
      hquotient
end
end

section
-- module Solutions.OAIQ244_DUKE.LocalField_NonarchimedeanLocalField_UnramifiedFrobenius
attribute [-instance] _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionFixedSubring.instIsLocalRing _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionResidueField.instField _root_.RamificationTheory.HilbertRamification.ValuationSubring.selectedResidueField.instAlgebra _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

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

/-- Arithmetic Frobenius of the actual residue-field extension supplied by a
valuation extension. This is finite Galois ramification theory's finite-field Frobenius,
applied to the canonical residue extension `𝓀[L]/𝓀[K]`. -/
noncomputable def residueExtensionArithmeticFrobeniusOfValuationExtension
    (K L : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] [Field L] [ValuativeRel L]
    [TopologicalSpace L] [IsNonarchimedeanLocalField L] [Algebra K L]
    [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)] :
    𝓀[L] ≃ₐ[𝓀[K]] 𝓀[L] := by
  letI := Fintype.ofFinite 𝓀[K]
  letI : Algebra.IsAlgebraic 𝓀[K] 𝓀[L] := inferInstance
  exact FiniteField.frobeniusAlgEquivOfAlgebraic 𝓀[K] 𝓀[L]

/-- The order of residue arithmetic Frobenius is the degree of the finite residue-field extension. -/
theorem orderOf_residueExtensionArithmeticFrobeniusOfValuationExtension
    (K L : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] [Field L] [ValuativeRel L]
    [TopologicalSpace L] [IsNonarchimedeanLocalField L] [Algebra K L]
    [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)] :
    orderOf (residueExtensionArithmeticFrobeniusOfValuationExtension K L) =
      Module.finrank 𝓀[K] 𝓀[L] := by
  let := Fintype.ofFinite 𝓀[K]
  let : Algebra.IsAlgebraic 𝓀[K] 𝓀[L] := inferInstance
  simpa [residueExtensionArithmeticFrobeniusOfValuationExtension] using
    (FiniteField.orderOf_frobeniusAlgEquivOfAlgebraic
      (K := 𝓀[K]) (L := 𝓀[L]))

/-- Arithmetic Frobenius generates the automorphism group of a finite residue-field extension. -/
theorem residueExtensionArithmeticFrobeniusOfValuationExtension_generates
    (K L : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] [Field L] [ValuativeRel L]
    [TopologicalSpace L] [IsNonarchimedeanLocalField L] [Algebra K L]
    [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)] :
    ∀ σ : 𝓀[L] ≃ₐ[𝓀[K]] 𝓀[L],
      σ ∈ Subgroup.zpowers (residueExtensionArithmeticFrobeniusOfValuationExtension K L) := by
  let := Fintype.ofFinite 𝓀[K]
  let : Algebra.IsAlgebraic 𝓀[K] 𝓀[L] := inferInstance
  intro σ
  rcases
      (FiniteField.bijective_frobeniusAlgEquivOfAlgebraic_pow
        (K := 𝓀[K]) (L := 𝓀[L])).2 σ with
    ⟨n, hn⟩
  refine ⟨(n : ℕ), ?_⟩
  rw [← hn]
  simp [residueExtensionArithmeticFrobeniusOfValuationExtension]

/-- Internal quotient construction for a specified additive generator. The
public local-field API below supplies `horder` and `hgen` from the already proved
Frobenius source lemmas, so these hypotheses are not exposed as new endpoints. -/
noncomputable def zmodAddEquivOfGenerator {A : Type*} [AddGroup A]
    (g : A) {n : Nat} (horder : addOrderOf g = n)
    (hgen : AddSubgroup.zmultiples g = ⊤) :
    ZMod n ≃+ A := by
  let f : { f : ℤ →+ A // f n = 0 } :=
    ⟨zmultiplesHom A g, by
      rw [← horder]
      simp [zmultiplesHom_apply]⟩
  refine AddEquiv.ofBijective (ZMod.lift n f) ⟨?_, ?_⟩
  · rw [ZMod.lift_injective]
    intro m hm
    rw [ZMod.intCast_zmod_eq_zero_iff_dvd]
    rw [show f.1 m = (m : ℤ) • g by rfl] at hm
    rw [← horder]
    exact (addOrderOf_dvd_iff_zsmul_eq_zero (x := g)).mpr hm
  · intro x
    have hx : x ∈ AddSubgroup.zmultiples g := by
      rw [hgen]
      exact AddSubgroup.mem_top x
    rcases hx with ⟨i, hi⟩
    exact ⟨(i : ZMod n), by simpa [f, ZMod.lift_coe] using hi⟩

theorem zmodAddEquivOfGenerator_apply_one {A : Type*} [AddGroup A]
    (g : A) {n : Nat} (horder : addOrderOf g = n)
    (hgen : AddSubgroup.zmultiples g = ⊤) :
    zmodAddEquivOfGenerator g horder hgen (1 : ZMod n) = g := by
  unfold zmodAddEquivOfGenerator
  dsimp [AddEquiv.ofBijective, Equiv.ofBijective]
  let f : { f : ℤ →+ A // f n = 0 } :=
    ⟨zmultiplesHom A g, by
      rw [← horder]
      simp [zmultiplesHom_apply]⟩
  change (ZMod.lift n f) (1 : ZMod n) = g
  have hcast : Int.castAddHom (ZMod n) (1 : ℤ) = (1 : ZMod n) := by
    simp [Int.castAddHom]
  rw [← hcast, ZMod.lift_castAddHom]
  simp [f, zmultiplesHom_apply]

lemma additive_zmultiples_eq_top_of_zpowers_eq_top {G : Type*} [Group G]
    (g : G) (hgen : Subgroup.zpowers g = ⊤) :
    AddSubgroup.zmultiples (Additive.ofMul g) = ⊤ := by
  ext x
  constructor
  · intro _
    exact AddSubgroup.mem_top x
  · intro _
    change x ∈ (AddSubgroup.zmultiples (Additive.ofMul g) : Set (Additive G))
    rw [← ofMul_image_zpowers_eq_zmultiples_ofMul]
    refine ⟨Additive.toMul x, ?_, rfl⟩
    rw [hgen]
    exact Subgroup.mem_top (Additive.toMul x)

noncomputable def zmodCyclicMulEquivOfGenerator {G : Type*} [Group G]
    (g : G) {n : Nat} (horder : orderOf g = n)
    (hgen : Subgroup.zpowers g = ⊤) :
    Multiplicative (ZMod n) ≃* G :=
  AddEquiv.toMultiplicative <|
    zmodAddEquivOfGenerator (Additive.ofMul g)
      (by simpa [addOrderOf_ofMul_eq_orderOf] using horder)
      (additive_zmultiples_eq_top_of_zpowers_eq_top g hgen)

theorem zmodCyclicMulEquivOfGenerator_apply_one {G : Type*} [Group G]
    (g : G) {n : Nat} (horder : orderOf g = n)
    (hgen : Subgroup.zpowers g = ⊤) :
    zmodCyclicMulEquivOfGenerator g horder hgen
      (Multiplicative.ofAdd (1 : ZMod n)) = g := by
  unfold zmodCyclicMulEquivOfGenerator
  change Additive.toMul
      (zmodAddEquivOfGenerator (Additive.ofMul g)
        (by simpa [addOrderOf_ofMul_eq_orderOf] using horder)
        (additive_zmultiples_eq_top_of_zpowers_eq_top g hgen) (1 : ZMod n)) = g
  rw [zmodAddEquivOfGenerator_apply_one]
  rfl

end
end LocalFieldTheory
end

section
-- module Solutions.OAIQ244_DUKE.LocalClassFieldTheory_ClassFormation_ArchimedeanNormQuotient
attribute [-instance] _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionResidueField.instField _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

set_option autoImplicit false

/-!
# The real/complex norm quotient

At a ramified infinite place the local extension is `ℂ/ℝ`.  Its norm
subgroup consists exactly of the positive real units, so the sign map
identifies the norm quotient with `ℤˣ`, a group of order two.
-/

open LocalFieldTheory

noncomputable section

namespace LocalClassFieldTheory

universe u v w z

open NumberField
open scoped Classical NumberField.LiesOver

variable
    {K L : Type}
    [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]

/-- The underlying absolute-value completion of a real infinite place
is the real numbers. -/
def absoluteCompletionRingEquivReal
    (v : InfinitePlace K) (hv : v.IsReal) :
    v.1.Completion ≃+* ℝ :=
  (InfinitePlace.Completion.equiv v).symm.trans
    (InfinitePlace.Completion.ringEquivRealOfIsReal hv)

/-- The underlying absolute-value completion of a complex infinite
place is the complex numbers. -/
def absoluteCompletionRingEquivComplex
    (v : InfinitePlace K) (hv : v.IsComplex) :
    v.1.Completion ≃+* ℂ :=
  (InfinitePlace.Completion.equiv v).symm.trans
    (InfinitePlace.Completion.ringEquivComplexOfIsComplex hv)

/-- Compatibility of a square of ring equivalences is symmetric. -/
theorem ringEquiv_compat_symm
    {K : Type u} {L : Type v} {K' : Type w} {L' : Type z}
    [Field K] [Field L] [Field K'] [Field L']
    [Algebra K L] [Algebra K' L']
    (eK : K ≃+* K') (eL : L ≃+* L')
    (he :
      RingHom.comp (algebraMap K' L') eK =
        RingHom.comp eL (algebraMap K L)) :
    RingHom.comp (algebraMap K L) eK.symm =
      RingHom.comp eL.symm (algebraMap K' L') := by
  ext x
  apply eL.injective
  have hx := DFunLike.congr_fun he (eK.symm x)
  simpa using hx.symm

/-- The sign of a nonzero real number, regarded as an integral unit. -/
def realUnitsSign : ℝˣ →* ℤˣ :=
  Units.map
    ((SignType.castHom (α := ℤ)).comp
      (signHom (α := ℝ)))

/-- Coercing `realUnitsSign x` to an integer recovers the usual sign of
the underlying nonzero real number. -/
@[simp]
theorem realUnitsSign_coe (x : ℝˣ) :
    ((realUnitsSign x : ℤˣ) : ℤ) =
      (SignType.sign (x : ℝ) : ℤ) :=
  rfl

/-- Both integral signs occur. -/
theorem realUnitsSign_surjective :
    Function.Surjective realUnitsSign := by
  intro u
  rcases Int.units_eq_one_or u with rfl | rfl
  · exact ⟨1, by simp [realUnitsSign]⟩
  · exact ⟨-1, by
      apply Units.ext
      simp [realUnitsSign]⟩

/-- A nonzero real unit has trivial sign precisely when it is positive. -/
@[simp]
theorem mem_realUnitsSign_ker_iff (x : ℝˣ) :
    x ∈ realUnitsSign.ker ↔ 0 < (x : ℝ) := by
  rw [MonoidHom.mem_ker]
  constructor
  · intro hx
    have hxv := congrArg Units.val hx
    have hs : SignType.sign (x : ℝ) = 1 := by
      cases hsign : SignType.sign (x : ℝ) <;>
        simp [realUnitsSign_coe, hsign] at hxv ⊢
    exact sign_eq_one_iff.mp hs
  · intro hx
    apply Units.ext
    simp [realUnitsSign, sign_pos hx]

/-- The sign homomorphism is continuous for the native topology on
real units and the discrete topology on `ℤˣ`. -/
@[fun_prop]
theorem realUnitsSign_continuous :
    Continuous realUnitsSign := by
  apply continuous_of_continuousAt_one _
  rw [continuousAt_def, map_one]
  intro V hV
  have hposOpen :
      IsOpen {x : ℝˣ | 0 < (x : ℝ)} :=
    isOpen_Ioi.preimage Units.continuous_val
  have hposOne :
      (1 : ℝˣ) ∈ {x : ℝˣ | 0 < (x : ℝ)} := by
    norm_num
  apply Filter.mem_of_superset (hposOpen.mem_nhds hposOne)
  intro x hx
  have hsign : realUnitsSign x = 1 :=
    MonoidHom.mem_ker.mp
      ((mem_realUnitsSign_ker_iff x).2 hx)
  change realUnitsSign x ∈ V
  rw [hsign]
  exact mem_of_mem_nhds hV

end LocalClassFieldTheory
end
end

section
-- module Solutions.OAIQ244_DUKE.AlgebraicNumberTheory_Idele_Cohomology_SPlaces_LocalBlocks
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

set_option autoImplicit false

/-!
# The local blocks occurring in a relative `S`-idele

For a finite set `S` of finite places, the unrestricted factors consist
of every infinite place and the finite places in `S`.  This file packages
those two kinds of concrete tensor factors into one finite dependent
family and identifies it equivariantly with the induced local blocks of
the local tensor decomposition.
-/

open scoped NumberField TensorProduct
open NumberField IsDedekindDomain

noncomputable section

open LocalClassFieldTheory

variable {K L : Type}
    [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]

/-- A fixed infinite place of `L` above the given infinite place of
`K`. -/
noncomputable def chosenInfinitePlaceAbove
    (v : InfinitePlace K) : InfinitePlace L :=
  Classical.choose
    (InfinitePlace.comap_surjective (K := L) v)

omit [NumberField K] [NumberField L] [FiniteDimensional K L] in
/-- The chosen infinite place above `v` restricts back to `v`. -/
@[simp]
theorem chosenInfinitePlaceAbove_comap
    (v : InfinitePlace K) :
    (chosenInfinitePlaceAbove (L := L) v).comap
        (algebraMap K L) = v :=
  Classical.choose_spec
    (InfinitePlace.comap_surjective (K := L) v)

/-- Infinite places and the selected finite places form the finite
unrestricted index family of a relative `S`-idele. -/
abbrev RelativeUnrestrictedSPlaceIndex
    (S : Finset (HeightOneSpectrum (𝓞 K))) :=
  Sum (InfinitePlace K)
    {v : HeightOneSpectrum (𝓞 K) // v ∈ S}
end
end

section
-- module Solutions.OAIQ244_DUKE.AlgebraicNumberTheory_Idele_Cohomology_SPlaces_OutsideIntegralInduced_ChosenPlace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

set_option autoImplicit false

/-!
# Integral induced blocks at the chosen finite place

This file specializes the integral induced-block construction to the actual
chosen localization above a finite place and proves its unramified Tate
cohomology consequences.
-/

open scoped NumberField TensorProduct ValuativeRel NNReal
open NumberField IsDedekindDomain

noncomputable section

open LocalClassFieldTheory
open LocalFieldTheory

variable
    {K : Type} {L : Type}
    [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]

section ChosenFinitePlace

theorem zpowers_generator_map
    {G H : Type*} [Group G] [Group H]
    (e : G ≃* H) (g : G)
    (hg : ∀ x : G, x ∈ Subgroup.zpowers g) :
    ∀ y : H, y ∈ Subgroup.zpowers (e g) := by
  intro y
  have hmem : e.symm y ∈ Subgroup.zpowers g :=
    hg (e.symm y)
  have himage : e (e.symm y) ∈
      (Subgroup.zpowers g).map e.toMonoidHom :=
    ⟨e.symm y, hmem, rfl⟩
  rw [MonoidHom.map_zpowers] at himage
  simpa using himage

theorem subsingleton_of_equiv_of_equiv
    {A B C : Type*}
    (eAB : A ≃ B) (eBC : B ≃ C)
    (hC : Subsingleton C) :
    Subsingleton A :=
  ⟨fun _ _ ↦
    eAB.injective
      (eBC.injective (@Subsingleton.elim C hC _ _))⟩

/-- Forget multiplication using the dictionaries already present in the equivalence. -/
def underlyingEquivOfMulEquiv
    {A B : Type*} {mulA : Mul A} {mulB : Mul B}
    (e : @MulEquiv A B mulA mulB) : A ≃ B :=
  e.toEquiv

theorem apply_of_zpowers_generator_map
    {G H : Type*} [Group G] [Group H]
    {P : H → Prop}
    (e : G ≃* H) (g : G)
    (hg : ∀ x : G, x ∈ Subgroup.zpowers g)
    (hP : ∀ h : H,
      (∀ y : H, y ∈ Subgroup.zpowers h) → P h) :
    P (e g) :=
  hP (e g) (zpowers_generator_map e g hg)

end ChosenFinitePlace
end
end

section
-- module Solutions.OAIQ244_DUKE.AlgebraicNumberTheory_Idele_NormApproximation_InfinitePlaces
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

set_option autoImplicit false

/-!
# Archimedean norm approximation

This file supplies the archimedean source used in the norm-approximation
argument. At a real place the positive units have
an `n`-th root, while at a complex place every unit has one.  Consequently
the standard positive subgroup is contained in the determinant-norm image
of every scalar extension of positive degree.
-/

open scoped NumberField TensorProduct
open NumberField IsDedekindDomain
open LocalFieldTheory

noncomputable section

open LocalClassFieldTheory

universe u v

section ArchimedeanNorm

variable {K : Type u} [Field K] [NumberField K]

variable {L : Type v} [Field L] [Algebra K L]
    [FiniteDimensional K L]

/-- Determinant norm on the actual tensor factor used by the infinite
component of the relative adele ring. -/
def infiniteTensorDetNorm
    (v : InfinitePlace K) :
    (v.Completion ⊗[K] L)ˣ →* v.Completionˣ :=
  Units.map (Algebra.norm v.Completion)

/-- Image of the determinant norm on an infinite tensor factor. -/
def infiniteTensorNormSubgroup
    (v : InfinitePlace K) :
    Subgroup v.Completionˣ :=
  (infiniteTensorDetNorm (K := K) (L := L) v).range

end ArchimedeanNorm
end
end

section
-- module Solutions.OAIQ244_DUKE.AlgebraicNumberTheory_SUnit_Rank
attribute [-instance] _root_.RamificationTheory.HilbertRamification.ValuationSubring.selectedResidueField.instAlgebra _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

set_option autoImplicit false

/-!
# Torsion and rank sources for `S`-units

This file supplies the algebraic rank and torsion input for `S`-units.
The finite set `S` contains the finite places; all infinite places are
understood to be present.
-/

noncomputable section

open IsDedekindDomain
open scoped NumberField nonZeroDivisors


variable {K : Type*} [Field K] [NumberField K]

namespace SUnitGroup

section PrimePowerSources

variable (S : Finset (HeightOneSpectrum (𝓞 K)))

/-- The class-number power of a prime ideal is principal. -/
theorem primeIdealPower_classNumber_isPrincipal (v : S) :
    ((v : HeightOneSpectrum (𝓞 K)).asIdeal ^
      NumberField.classNumber K).IsPrincipal := by
  have hv0 :
      (v : HeightOneSpectrum (𝓞 K)).asIdeal ^
          NumberField.classNumber K ≠ 0 :=
    pow_ne_zero _ (v : HeightOneSpectrum (𝓞 K)).ne_bot
  apply (ClassGroup.mk0_eq_one_iff
    (mem_nonZeroDivisors_iff_ne_zero.mpr hv0)).mp
  have hpow :
      (ClassGroup.mk0
        ⟨(v : HeightOneSpectrum (𝓞 K)).asIdeal,
          mem_nonZeroDivisors_iff_ne_zero.mpr
            (v : HeightOneSpectrum (𝓞 K)).ne_bot⟩) ^
          Fintype.card (ClassGroup (𝓞 K)) = 1 :=
    pow_card_eq_one
      (x := ClassGroup.mk0
        ⟨(v : HeightOneSpectrum (𝓞 K)).asIdeal,
          mem_nonZeroDivisors_iff_ne_zero.mpr
            (v : HeightOneSpectrum (𝓞 K)).ne_bot⟩)
  let I : (Ideal (𝓞 K))⁰ :=
    ⟨(v : HeightOneSpectrum (𝓞 K)).asIdeal,
      mem_nonZeroDivisors_iff_ne_zero.mpr
        (v : HeightOneSpectrum (𝓞 K)).ne_bot⟩
  have hsub :
      (⟨(v : HeightOneSpectrum (𝓞 K)).asIdeal ^
          NumberField.classNumber K,
        mem_nonZeroDivisors_iff_ne_zero.mpr hv0⟩ :
          (Ideal (𝓞 K))⁰) =
        I ^ NumberField.classNumber K := by
    rfl
  rw [hsub, map_pow]
  exact hpow

/-- A generator of the principal `classNumber K`-th power of a prime ideal. -/
noncomputable def primePowerGenerator (v : S) : 𝓞 K :=
  let I :=
    (v : HeightOneSpectrum (𝓞 K)).asIdeal ^
      NumberField.classNumber K
  letI : I.IsPrincipal :=
    primeIdealPower_classNumber_isPrincipal (K := K) S v
  Submodule.IsPrincipal.generator I

theorem span_primePowerGenerator (v : S) :
    Ideal.span {primePowerGenerator (K := K) S v} =
      (v : HeightOneSpectrum (𝓞 K)).asIdeal ^
        NumberField.classNumber K := by
  let I :=
    (v : HeightOneSpectrum (𝓞 K)).asIdeal ^
      NumberField.classNumber K
  let : I.IsPrincipal :=
    primeIdealPower_classNumber_isPrincipal (K := K) S v
  simp [primePowerGenerator]

theorem primePowerGenerator_ne_zero (v : S) :
    primePowerGenerator (K := K) S v ≠ 0 := by
  intro hzero
  have hv0 :
      (v : HeightOneSpectrum (𝓞 K)).asIdeal ^
          NumberField.classNumber K ≠ 0 :=
    pow_ne_zero _ (v : HeightOneSpectrum (𝓞 K)).ne_bot
  apply hv0
  rw [← span_primePowerGenerator (K := K) S v, hzero]
  simp

theorem spanSingleton_primePowerGenerator (v : S) :
    FractionalIdeal.spanSingleton (𝓞 K)⁰
        (algebraMap (𝓞 K) K (primePowerGenerator (K := K) S v)) =
      ((v : HeightOneSpectrum (𝓞 K)).asIdeal :
        FractionalIdeal (𝓞 K)⁰ K) ^ NumberField.classNumber K := by
  rw [← FractionalIdeal.coeIdeal_span_singleton,
    span_primePowerGenerator (K := K) S v,
    FractionalIdeal.coeIdeal_pow]

noncomputable def classNumberBasisVector (v : S) : S → ℤ := by
  classical
  exact fun w =>
    if w = v then (NumberField.classNumber K : ℤ) else 0

end PrimePowerSources

end SUnitGroup
end
end

section
-- module Solutions.OAIQ244_DUKE.AlgebraicNumberTheory_SUnit_LogLattice
attribute [-instance] _root_.RamificationTheory.HilbertRamification.ValuationSubring.selectedResidueField.instAlgebra _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

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

/-- The nonzero scale converting an integral divisor coordinate into
the logarithm of the corresponding normalized finite absolute value. -/
noncomputable def finiteLogWeight (v : S) : ℝ :=
  -Real.log
    (Ideal.absNorm
      (v : HeightOneSpectrum (𝓞 K)).asIdeal : ℝ)

theorem finiteLogWeight_ne_zero (v : S) :
    finiteLogWeight (K := K) S v ≠ 0 := by
  have hNv :
      (1 : ℝ) <
        (Ideal.absNorm
          (v : HeightOneSpectrum (𝓞 K)).asIdeal : ℝ) := by
    exact_mod_cast
      NumberField.HeightOneSpectrum.one_lt_absNorm
        (v : HeightOneSpectrum (𝓞 K))
  exact neg_ne_zero.mpr (ne_of_gt (Real.log_pos hNv))

end FullLogarithmicSpace

section Decomposition

/-- The logarithmic rank: the number of places in the
`S`-unit theorem minus one. -/
def logRank : ℕ :=
  Fintype.card (NumberField.InfinitePlace K) + S.card - 1

/-- The additive realization of the roots of unity of `K`. -/
abbrev RootsOfUnityAdditive :=
  (NumberField.Units.torsion K).toAddSubgroup.toIntSubmodule

/-- The multiplicative realization of the additive roots-of-unity
submodule is canonically the usual group `μ(K)`. -/
noncomputable def multiplicativeRootsOfUnityEquiv :
    Multiplicative (RootsOfUnityAdditive (K := K)) ≃*
      NumberField.Units.torsion K where
  toFun x :=
    ⟨Additive.toMul
      ((Multiplicative.toAdd x :
        RootsOfUnityAdditive (K := K)) :
        Additive (𝓞 K)ˣ),
      (Multiplicative.toAdd x :
        RootsOfUnityAdditive (K := K)).property⟩
  invFun u :=
    Multiplicative.ofAdd
      (⟨Additive.ofMul (u : (𝓞 K)ˣ), u.property⟩ :
        RootsOfUnityAdditive (K := K))
  left_inv x := by
    rfl
  right_inv u := by
    rfl
  map_mul' x y := by
    rfl

end Decomposition

end SUnitGroup
end
end

section
-- module Solutions.OAIQ244_DUKE.AlgebraicNumberTheory_SUnit_GaloisAction
attribute [-instance] _root_.RamificationTheory.HilbertRamification.ValuationSubring.selectedResidueField.instAlgebra _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

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

noncomputable section

variable
    (K L : Type*) [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]

/-- Absolute ideal norms are invariant under a ring automorphism. -/
theorem absNorm_map_ringEquiv
    {R : Type*} [CommRing R] [IsDedekindDomain R]
    [Module.Free ℤ R] [Infinite R]
    (e : R ≃+* R) (I : Ideal R) :
    Ideal.absNorm (I.map e) = Ideal.absNorm I := by
  rw [Ideal.absNorm_apply, Ideal.absNorm_apply,
    Submodule.cardQuot_apply, Submodule.cardQuot_apply]
  exact Nat.card_congr
    (Ideal.quotientEquiv I (I.map e) e rfl).toEquiv.symm

theorem toNNReal_apply_congr
    {e f : NNReal} (he : e ≠ 0) (hf : f ≠ 0)
    (hef : e = f) (q : WithZero (Multiplicative ℤ)) :
    ((WithZeroMulInt.toNNReal he q : NNReal) : ℝ) =
      ((WithZeroMulInt.toNNReal hf q : NNReal) : ℝ) := by
  subst f
  rfl
end
end

section
-- module Solutions.OAIQ244_DUKE.AlgebraicNumberTheory_SUnit_Herbrand
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

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

variable
    (K L : Type*) [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]

section LocalDegreeInterpretation

/-- The finite local degree at the place `P`, in the standard
ramification-index times inertia-degree form
`[L_P : K_p] = e(P/p) f(P/p)`. -/
noncomputable def finiteLogPlaceLocalDegree
    (P : HeightOneSpectrum (𝓞 L)) : ℕ :=
  let p := P.asIdeal.under (𝓞 K)
  p.ramificationIdxIn (𝓞 L) *
    p.inertiaDegIn (𝓞 L)

end LocalDegreeInterpretation
end
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Entropy_PredecessorWholeFutureEntropy
attribute [-instance] _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Exact predecessor-word entropy conditioned on the whole terminal future -/

noncomputable section
open MeasureTheory Set
namespace DukePrimeDegree

def fullFutureObservation {Y : Type*} (T : Y → Y) (Q : Y → ℕ) (r : ℕ)
    (y : Y) : ℕ → ℕ := fun k => Q (T^[r+k] y)

end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.Kummer_Concrete_FiniteGeneration
attribute [-instance] _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

/-!
# finite actual-field form

Let `L/K` be a finite abelian Galois extension whose Galois group is killed by
`n`, and suppose that `K` contains a primitive `n`-th root of unity.  This file
proves that `L` is generated over `K` by all nonzero `beta : L` such that
`beta ^ n` belongs to `K`.

The proof uses finite-abelian character separation and the finite Kummer
character isomorphism.  It is the finite `n`-th-power, actual-field form of
the Kummer generation theorem; it is not the general abstract-module or infinite statement.
-/

noncomputable section

namespace KummerTheory

open scoped IsMulCommutative

section FiniteKummerGeneration

variable {K L : Type*} [Field K] [Field L] [Algebra K L]

/-- All nonzero elements of `L` whose `n`-th power comes from `K`. -/
def finiteKummerRootSet (n : ℕ+) : Set L :=
  {beta | beta ≠ 0 ∧
    ∃ a : Kˣ, beta ^ (n : ℕ) = algebraMap K L (a : K)}

end FiniteKummerGeneration

end KummerTheory
end
end

section
-- module Solutions.OAIQ244_DUKE.Kummer_Concrete_InfiniteInverse
attribute [-instance] _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

/-!
# infinite inverse inclusion

Any radical appearing in `K(√[n]{Δ})` uses only finitely many of the
adjoined roots.  The corresponding admissible finite-support subgroup
`Δ₀ ≤ Δ` gives a finite Galois Kummer stage.  Applying the finite inverse
theorem at that stage shows that the original radical already belongs to
`Δ₀`, hence to `Δ`.
-/

noncomputable section

namespace KummerTheory

variable {K Omega : Type*} [Field K] [Field Omega] [Algebra K Omega]

section FiniteSupportField

variable (n : ℕ+)
  (T : Finset Omega)

/-- The finite field generated by the selected radical roots. -/
def finiteSupportField : IntermediateField K Omega :=
  IntermediateField.adjoin K (T : Set Omega)

end FiniteSupportField

end KummerTheory
end
end

section
-- module Solutions.OAIQ244_DUKE.KummerTheory_Concrete_SUnitPreparation_SUnitPowerQuotient
attribute [-instance] _root_.RamificationTheory.HilbertRamification.ValuationSubring.inertiaGroup_normal _root_.RamificationTheory.HilbertRamification.ValuationSubring.ramificationGroupInInertiaAut_normal _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

/-!
# Power quotients of S-unit groups

The finite `n`-th-power quotient of an `S`-unit group, its cardinality, and explicit `ZMod n` coordinates.
-/

open scoped NumberField Classical IsMulCommutative NNReal ValuativeRel
open NumberField IsDedekindDomain
open LocalFieldTheory

noncomputable section

namespace KummerTheory

variable {K : Type*} [Field K]
    [numberFieldK : NumberField K]

/-- Coordinatewise reduction of a finite free `ℤ`-module modulo `n`. -/
def finsuppModHom (d n : ℕ) :
    (Fin d →₀ ℤ) →+ (Fin d → ZMod n) where
  toFun x i := x i
  map_zero' := by
    ext i
    simp
  map_add' x y := by
    ext i
    simp

/-- Every vector over `ZMod n` has an integral lift. -/
theorem finsuppModHom_surjective (d n : ℕ) :
    Function.Surjective (finsuppModHom d n) := by
  intro y
  choose x hx using fun i => ZMod.intCast_surjective (y i)
  let x' : Fin d →₀ ℤ :=
    (Finsupp.equivFunOnFinite).symm x
  refine ⟨x', ?_⟩
  ext i
  exact hx i

omit [NumberField K] in
/-- A primitive `n`-th root in `K` embeds a cyclic subgroup of order `n`
into the roots of unity of the integer ring. -/
theorem n_dvd_numberField_torsionOrder
    (n : ℕ+)
    (hmu : (primitiveRoots (n : ℕ) K).Nonempty) :
    (n : ℕ) ∣ NumberField.Units.torsionOrder K := by
  let _ : NeZero (n : ℕ) := ⟨n.ne_zero⟩
  obtain ⟨ζ, hζ⟩ := hmu
  have hζprim : IsPrimitiveRoot ζ (n : ℕ) :=
    (mem_primitiveRoots n.pos).mp hζ
  let ζO : 𝓞 K := hζprim.toInteger
  have hζOprim : IsPrimitiveRoot ζO (n : ℕ) :=
    hζprim.toInteger_isPrimitiveRoot
  let hu : IsUnit ζO := hζOprim.isUnit n.ne_zero
  let u : (𝓞 K)ˣ := hu.unit
  have huval : (u : 𝓞 K) = ζO :=
    hu.unit_spec
  have huprim : IsPrimitiveRoot u (n : ℕ) := by
    rw [← IsPrimitiveRoot.coe_units_iff, huval]
    exact hζOprim
  have hutorsion : u ∈ NumberField.Units.torsion K := by
    rw [NumberField.Units.torsion,
      CommGroup.mem_torsion,
      isOfFinOrder_iff_pow_eq_one]
    exact ⟨n, n.pos, huprim.pow_eq_one⟩
  let ut : NumberField.Units.torsion K :=
    ⟨u, hutorsion⟩
  have hutprim : IsPrimitiveRoot ut (n : ℕ) := by
    rw [← IsPrimitiveRoot.coe_submonoidClass_iff]
    exact huprim
  rw [NumberField.Units.torsionOrder,
    hutprim.eq_orderOf]
  exact orderOf_dvd_natCard ut

include numberFieldK in
/-- If `K` contains a primitive `n`-th root, the quotient of its roots of
unity by `n`-th powers has cardinality `n`. -/
theorem card_numberField_torsion_nthPowerQuotient
    (n : ℕ+)
    (hmu : (primitiveRoots (n : ℕ) K).Nonempty) :
    Nat.card
        (NumberField.Units.torsion K ⧸
          (powMonoidHom (n : ℕ) :
            NumberField.Units.torsion K →*
              NumberField.Units.torsion K).range) =
      (n : ℕ) := by
  let T := NumberField.Units.torsion K
  let P :=
    (powMonoidHom (n : ℕ) : T →* T).range
  have hcardP :
      Nat.card P =
        Nat.card T / (Nat.card T).gcd (n : ℕ) := by
    exact IsCyclic.card_powMonoidHom_range T (n : ℕ)
  have hgcd_dvd : (Nat.card T).gcd (n : ℕ) ∣ Nat.card T :=
    Nat.gcd_dvd_left _ _
  have hcard_factor :
      (Nat.card T).gcd (n : ℕ) *
          (Nat.card T / (Nat.card T).gcd (n : ℕ)) =
        Nat.card T :=
    Nat.mul_div_cancel' hgcd_dvd
  have hquotient :
      Nat.card (T ⧸ P) *
          (Nat.card T / (Nat.card T).gcd (n : ℕ)) =
        Nat.card T := by
    rw [← hcardP]
    exact (Subgroup.card_eq_card_quotient_mul_card_subgroup P).symm
  have hfactor_pos :
      0 < Nat.card T / (Nat.card T).gcd (n : ℕ) := by
    rw [Nat.div_pos_iff]
    have hTpos : 0 < Nat.card T := Nat.card_pos
    exact ⟨Nat.gcd_pos_of_pos_left _ hTpos,
      Nat.gcd_le_left (m := Nat.card T) (n : ℕ) hTpos⟩
  have hcard :
      Nat.card (T ⧸ P) =
        (Nat.card T).gcd (n : ℕ) := by
    exact Nat.eq_of_mul_eq_mul_right hfactor_pos
      (hquotient.trans hcard_factor.symm)
  change Nat.card (T ⧸ P) = (n : ℕ)
  rw [hcard, Nat.gcd_eq_right]
  simpa [T, NumberField.Units.torsionOrder] using
    n_dvd_numberField_torsionOrder (K := K) n hmu

/-- The roots-of-unity contribution to the `S`-unit quotient is one
copy of `ZMod n`. -/
noncomputable def numberFieldTorsionNthPowerQuotientEquivZMod
    (n : ℕ+)
    (hmu : (primitiveRoots (n : ℕ) K).Nonempty) :
    NumberField.Units.torsion K ⧸
        (powMonoidHom (n : ℕ) :
          NumberField.Units.torsion K →*
            NumberField.Units.torsion K).range ≃*
      Multiplicative (ZMod (n : ℕ)) := by
  letI : IsCyclic
      (NumberField.Units.torsion K ⧸
        (powMonoidHom (n : ℕ) :
          NumberField.Units.torsion K →*
            NumberField.Units.torsion K).range) :=
    isCyclic_of_surjective
      (QuotientGroup.mk'
        (powMonoidHom (n : ℕ) :
          NumberField.Units.torsion K →*
            NumberField.Units.torsion K).range)
      (QuotientGroup.mk'_surjective _)
  apply mulEquivOfCyclicCardEq
  rw [card_numberField_torsion_nthPowerQuotient
    (K := K) n hmu]
  simp

end KummerTheory
end
end

section
-- module Solutions.OAIQ244_DUKE.Kummer_Concrete_SUnitPreparation_PrimePowerKernelCoordinates
attribute [-instance] _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionResidueField.instField _root_.RamificationTheory.HilbertRamification.ValuationSubring.selectedResidueField.instAlgebra _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois
set_option synthInstance.maxHeartbeats 400000
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

/-!
# Prime-power kernel coordinates

Linear-algebraic coordinates for kernels of surjections between finite free modules over `ZMod (p ^ v)`.
-/

open scoped Classical IsMulCommutative

noncomputable section

namespace KummerTheory

/-- A prime-power residue ring is local.  This instance is the algebraic
input needed to turn the projective kernel in the finite S-unit preparation argument into a free
`ZMod (p ^ v)`-module. -/
theorem zmodPrimePower_isLocalRing
    (p v : ℕ) (hp : p.Prime) (hv : 0 < v) :
    IsLocalRing (ZMod (p ^ v)) := by
  let : Fact (1 < p ^ v) := ⟨by
    calc
      1 < p := hp.one_lt
      _ = p ^ 1 := (pow_one p).symm
      _ ≤ p ^ v :=
        Nat.pow_le_pow_right hp.pos
          (Nat.succ_le_iff.mpr hv)⟩
  have hmodulus : p ∣ p ^ v := by
    exact dvd_pow_self p hv.ne'
  apply IsLocalRing.of_nonunits_add
  intro a b ha hb
  have hunit (x : ZMod (p ^ v)) :
      IsUnit x ↔ ¬ p ∣ x.val := by
    constructor
    · intro hx
      apply (ZMod.isUnit_natCast_iff_not_dvd_pow hp hv).1
      simpa only [ZMod.natCast_zmod_val] using hx
    · intro hx
      have hcast :=
        (ZMod.isUnit_natCast_iff_not_dvd_pow hp hv).2 hx
      simpa only [ZMod.natCast_zmod_val] using hcast
  have ha' : p ∣ a.val := by
    change ¬ IsUnit a at ha
    exact Classical.not_not.mp
      (mt (hunit a).2 ha)
  have hb' : p ∣ b.val := by
    change ¬ IsUnit b at hb
    exact Classical.not_not.mp
      (mt (hunit b).2 hb)
  have hsum : p ∣ a.val + b.val :=
    dvd_add ha' hb'
  have hmultiple :
      p ∣ p ^ v * ((a.val + b.val) / p ^ v) :=
    dvd_mul_of_dvd_left hmodulus _
  have hrem :
      p ∣ (a.val + b.val) % p ^ v := by
    apply (Nat.dvd_add_iff_left hmultiple).mpr
    simpa only [Nat.mod_add_div] using hsum
  change ¬ IsUnit (a + b)
  intro hab
  apply (hunit (a + b)).1 hab
  rw [ZMod.val_add]
  exact hrem

/-- Over a local ring, the kernel of a surjection between finite free
modules is free.  The proof constructs the splitting explicitly and then
uses finite projective modules over local rings. -/
theorem free_ker_of_surjective_linearMap_of_isLocalRing
    {R M N : Type*} [CommRing R] [IsLocalRing R]
    [AddCommGroup M] [AddCommGroup N]
    [Module R M] [Module R N]
    [Module.Free R M] [Module.Free R N]
    [Finite M]
    (f : M →ₗ[R] N) (hf : Function.Surjective f) :
    Module.Free R (LinearMap.ker f) := by
  obtain ⟨sec, hsec⟩ :=
    Module.projective_lifting_property
      f LinearMap.id hf
  let q : M →ₗ[R] M :=
    LinearMap.id - sec.comp f
  have hq (x : M) : q x ∈ LinearMap.ker f := by
    rw [LinearMap.mem_ker]
    change f (x - sec (f x)) = 0
    rw [map_sub]
    have hsec_apply :
        f (sec (f x)) = f x := by
      have :=
        DFunLike.congr_fun hsec (f x)
      simpa using this
    rw [hsec_apply, sub_self]
  let projection : M →ₗ[R] LinearMap.ker f :=
    LinearMap.codRestrict (LinearMap.ker f) q hq
  have hprojection :
      projection.comp (LinearMap.ker f).subtype =
        LinearMap.id := by
    ext x
    change x.1 - sec (f x.1) = x.1
    rw [show f x.1 = 0 from x.2]
    simp
  let : Module.Projective R (LinearMap.ker f) :=
    Module.Projective.of_split
      (LinearMap.ker f).subtype projection hprojection
  let : Module.Finite R (LinearMap.ker f) :=
    Module.Finite.of_finite
  exact Module.free_of_flat_of_isLocalRing

/-- The cardinality of a finite free module is the cardinality of the
coefficient ring raised to the size of a chosen basis. -/
theorem card_eq_card_pow_card_chooseBasisIndex
    {R M : Type*} [Semiring R]
    [AddCommMonoid M] [Module R M]
    [Module.Free R M] [Finite R] [Finite M] :
    Nat.card M =
      Nat.card R ^
        Fintype.card (Module.Free.ChooseBasisIndex R M) := by
  let : Fintype R :=
    Fintype.ofFinite R
  let : Fintype M :=
    Fintype.ofFinite M
  let : Module.Finite R M :=
    Module.Finite.of_finite
  rw [Nat.card_congr
    (Module.Free.chooseBasis R M).repr.toEquiv]
  simp only [Nat.card_eq_fintype_card,
    Fintype.card_finsupp]

/-- Multiplicative product coordinates, interpreted as a `ZMod n`-linear
equivalence on the additive presentations. -/
noncomputable def additiveCoordinatesLinearEquiv
    {G A B : Type*} [CommGroup G] [AddCommGroup A]
    [AddCommGroup B] (n : ℕ)
    [Module (ZMod n) (Additive G)]
    [Module (ZMod n) A] [Module (ZMod n) B]
    (e : G ≃* Multiplicative A × Multiplicative B) :
    Additive G ≃ₗ[ZMod n] A × B := by
  let eAdd : Additive G ≃+ A × B :=
    MulEquiv.toAdditiveLeft e
  exact
  { eAdd with
    map_smul' := by
      simpa using ZMod.map_smul eAdd }

/-- The canonical `ZMod n`-module on the additive presentation of a
commutative group of exponent dividing `n`. -/
@[reducible]
noncomputable def additiveZModModuleOfPowEqOne
    {G : Type*} [CommGroup G] (n : ℕ)
    (h : ∀ g : G, g ^ n = 1) :
    Module (ZMod n) (Additive G) :=
  AddCommGroup.zmodModule <| by
    intro x
    apply Additive.toMul.injective
    simpa using h (Additive.toMul x)

/-- Multiplicative function coordinates, interpreted as a `ZMod n`-linear
equivalence on the additive presentations. -/
noncomputable def additivePiLinearEquiv
    {G A : Type*} [CommGroup G] [AddCommGroup A]
    {ι : Type*} (n : ℕ)
    [Module (ZMod n) (Additive G)]
    [Module (ZMod n) A]
    (e : G ≃* (ι → Multiplicative A)) :
    Additive G ≃ₗ[ZMod n] (ι → A) := by
  let eAdd : Additive G ≃+ (ι → A) :=
    MulEquiv.toAdditiveLeft e
  exact
  { eAdd with
    map_smul' := by
      simpa using ZMod.map_smul eAdd }

/-- The multiplicative kernel of a homomorphism is the multiplicative
presentation of the kernel of its induced `ZMod n`-linear map. -/
noncomputable def monoidKerEquivMultiplicativeLinearKer
    {G H : Type*} [CommGroup G] [CommGroup H]
    (n : ℕ)
    [Module (ZMod n) (Additive G)]
    [Module (ZMod n) (Additive H)]
    (f : G →* H) :
    f.ker ≃*
      Multiplicative
        (LinearMap.ker
          (f.toAdditive.toZModLinearMap n)) where
  toFun x :=
    Multiplicative.ofAdd
      ⟨Additive.ofMul x.1, by
        rw [LinearMap.mem_ker]
        apply Additive.toMul.injective
        exact x.2⟩
  invFun x :=
    ⟨Additive.toMul (Multiplicative.toAdd x).1, by
      change f (Additive.toMul (Multiplicative.toAdd x).1) = 1
      have hx := (Multiplicative.toAdd x).2
      rw [LinearMap.mem_ker] at hx
      exact congrArg Additive.toMul hx⟩
  left_inv x := by
    apply Subtype.ext
    rfl
  right_inv x := by
    apply Multiplicative.toAdd.injective
    apply Subtype.ext
    rfl
  map_mul' x y := by
    apply Multiplicative.toAdd.injective
    apply Subtype.ext
    rfl

/-- A surjection between finite free `ZMod (p ^ v)`-modules has a
kernel with genuine coordinates.  Its number of coordinates is read off
from the cardinality of the kernel. -/
theorem exists_kernelMulEquiv_pi_zmod_of_primePower
    {G H : Type*} [CommGroup G] [CommGroup H]
    (n p v q : ℕ)
    (hp : p.Prime) (hv : 0 < v)
    (hn : n = p ^ v)
    [Module (ZMod n) (Additive G)]
    [Module (ZMod n) (Additive H)]
    (freeG : Module.Free (ZMod n) (Additive G))
    (freeH : Module.Free (ZMod n) (Additive H))
    [Finite G]
    (f : G →* H) (hf : Function.Surjective f)
    (hcard : Nat.card f.ker = n ^ q) :
    Nonempty
      (f.ker ≃*
        (Fin q → Multiplicative (ZMod n))) := by
  have hn_one : 1 < n := by
    rw [hn]
    calc
      1 < p := hp.one_lt
      _ = p ^ 1 := (pow_one p).symm
      _ ≤ p ^ v :=
        Nat.pow_le_pow_right hp.pos
          (Nat.succ_le_iff.mpr hv)
  let : Module.Free (ZMod n) (Additive G) :=
    freeG
  let : Module.Free (ZMod n) (Additive H) :=
    freeH
  let : NeZero n := ⟨by omega⟩
  let : IsLocalRing (ZMod n) := by
    rw [hn]
    exact zmodPrimePower_isLocalRing p v hp hv
  let fLinear :
      Additive G →ₗ[ZMod n] Additive H :=
    f.toAdditive.toZModLinearMap n
  have hfLinear :
      Function.Surjective fLinear := by
    intro y
    obtain ⟨x, hx⟩ := hf (Additive.toMul y)
    refine ⟨Additive.ofMul x, ?_⟩
    apply Additive.toMul.injective
    exact hx
  let : Module.Free (ZMod n)
      (LinearMap.ker fLinear) :=
    free_ker_of_surjective_linearMap_of_isLocalRing
      fLinear hfLinear
  let : Module.Finite (ZMod n)
      (LinearMap.ker fLinear) :=
    Module.Finite.of_finite
  let I :=
    Module.Free.ChooseBasisIndex
      (ZMod n) (LinearMap.ker fLinear)
  let b₀ :=
    Module.Free.chooseBasis
      (ZMod n) (LinearMap.ker fLinear)
  have hlinearCard :
      Nat.card (LinearMap.ker fLinear) = n ^ q := by
    calc
      Nat.card (LinearMap.ker fLinear) =
          Nat.card (Multiplicative
            (LinearMap.ker fLinear)) := rfl
      _ = Nat.card f.ker :=
        Nat.card_congr
          (monoidKerEquivMultiplicativeLinearKer
            n f).symm.toEquiv
      _ = n ^ q := hcard
  have hbasisCard :
      Nat.card (LinearMap.ker fLinear) =
        n ^ Fintype.card I := by
    simpa only [Nat.card_zmod] using
      (card_eq_card_pow_card_chooseBasisIndex
        (R := ZMod n)
        (M := LinearMap.ker fLinear))
  have hI : Fintype.card I = q := by
    apply Nat.pow_right_injective hn_one
    exact hbasisCard.symm.trans hlinearCard
  let eI : I ≃ Fin q :=
    (Fintype.equivFin I).trans (finCongr hI)
  let b := b₀.reindex eI
  exact ⟨
    (monoidKerEquivMultiplicativeLinearKer n f).trans <|
      b.repr.toAddEquiv.toMultiplicative |>.trans <|
        (Finsupp.addEquivFunOnFinite).toMultiplicative |>.trans
          (MulEquiv.refl _)⟩

/-- The exponent-`n` statement read directly from coordinates
`Gal(E/K) ≃ (Z/nZ)^r`. -/
theorem galois_pow_eq_one_of_equiv_pi_zmod
    {K Omega : Type*} [Field K] [Field Omega] [Algebra K Omega]
    (E : IntermediateField K Omega)
    (n : ℕ+) (r : ℕ)
    (eG :
      (E ≃ₐ[K] E) ≃*
        (Fin r → Multiplicative (ZMod (n : ℕ))))
    (sigma : E ≃ₐ[K] E) :
    sigma ^ (n : ℕ) = 1 := by
  apply eG.injective
  rw [map_pow, map_one]
  ext i
  apply Multiplicative.toAdd.injective
  change
    (n : ℕ) • Multiplicative.toAdd (eG sigma i) = 0
  simp

end KummerTheory
end
end

section
-- module Solutions.OAIQ244_DUKE.GlobalClassFieldTheory_ClassFieldAxiom_SUnitLocalPowerMap
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

/-!
# S-unit localization modulo local powers

This module constructs the localization map from an S-unit group to the
finite product of local unit power classes and proves its kernel and
surjectivity properties for the Kummer prime set.
-/

open scoped NumberField Classical NNReal IsMulCommutative
open NumberField IsDedekindDomain
open KummerTheory
open LocalFieldTheory

noncomputable section

namespace GlobalClassFieldTheory.ClassFieldAxiom

variable {K : Type} [Field K] [NumberField K]

/-- An integral unit in an adic completion is an `n`-th power among
integral units exactly when it is an `n`-th power among field units. -/
theorem mem_powMonoidHom_range_adicCompletionIntegers_iff
    (v : HeightOneSpectrum (𝓞 K))
    (n : ℕ+)
    (x : (v.adicCompletionIntegers K)ˣ) :
    x ∈ (powMonoidHom (n : ℕ) :
          (v.adicCompletionIntegers K)ˣ →*
            (v.adicCompletionIntegers K)ˣ).range ↔
      Units.map
          (algebraMap (v.adicCompletionIntegers K)
            (v.adicCompletion K)).toMonoidHom x ∈
        (powMonoidHom (n : ℕ) :
          (v.adicCompletion K)ˣ →*
            (v.adicCompletion K)ˣ).range := by
  constructor
  · intro hx
    obtain ⟨y, hy⟩ :=
      (MonoidHom.mem_range
        (G := (v.adicCompletionIntegers K)ˣ)).mp hx
    apply
      (MonoidHom.mem_range
        (G := (v.adicCompletion K)ˣ)).mpr
    refine ⟨Units.map
      (algebraMap (v.adicCompletionIntegers K)
        (v.adicCompletion K)).toMonoidHom y, ?_⟩
    rw [powMonoidHom_apply] at hy ⊢
    rw [← map_pow, hy]
  · intro hx
    obtain ⟨y, hy⟩ :=
      (MonoidHom.mem_range
        (G := (v.adicCompletion K)ˣ)).mp hx
    rw [powMonoidHom_apply] at hy
    have hxVal :
        Valued.v
            (((Units.map
              (algebraMap (v.adicCompletionIntegers K)
                (v.adicCompletion K)).toMonoidHom x :
                  (v.adicCompletion K)ˣ) :
                v.adicCompletion K)) =
          1 :=
      (HeightOneSpectrum.adicCompletionIntegers.isUnit_iff_valued_eq_one
        (K := K) (v := v)).mp x.isUnit
    have hyValPow :
        Valued.v (((y ^ (n : ℕ) : (v.adicCompletion K)ˣ) :
          v.adicCompletion K)) = 1 := by
      rw [hy]
      exact hxVal
    have hyValPow' :
        Valued.v ((y : (v.adicCompletion K)ˣ) :
            v.adicCompletion K) ^ (n : ℕ) = 1 := by
      rw [Units.val_pow_eq_pow_val] at hyValPow
      rw [map_pow] at hyValPow
      exact hyValPow
    have hyVal :
        Valued.v ((y : (v.adicCompletion K)ˣ) :
            v.adicCompletion K) = 1 :=
      (pow_left_injective
        (M := WithZero (Multiplicative ℤ))
        (n := (n : ℕ)) n.ne_zero)
          (by simpa only [one_pow] using hyValPow')
    let yO : v.adicCompletionIntegers K :=
      ⟨(y : v.adicCompletion K), hyVal.le⟩
    have hyOUnit : IsUnit yO :=
      Valuation.Integers.isUnit_of_one'
        (HeightOneSpectrum.adicCompletionIntegers.integers K v) (by
          change
            Valued.v ((y : (v.adicCompletion K)ˣ) :
              v.adicCompletion K) = 1
          exact hyVal)
    obtain ⟨z, hz⟩ := hyOUnit
    have hzField :
        Units.map
            (algebraMap (v.adicCompletionIntegers K)
              (v.adicCompletion K)).toMonoidHom z =
          y := by
      apply Units.ext
      change ((z : v.adicCompletionIntegers K) :
        v.adicCompletion K) = (y : v.adicCompletion K)
      rw [hz]
    apply
      (MonoidHom.mem_range
        (G := (v.adicCompletionIntegers K)ˣ)).mpr
    refine ⟨z, ?_⟩
    rw [powMonoidHom_apply]
    apply Units.map_injective
      (f := (algebraMap (v.adicCompletionIntegers K)
        (v.adicCompletion K)).toMonoidHom)
      (FaithfulSMul.algebraMap_injective
        (v.adicCompletionIntegers K)
        (v.adicCompletion K))
    rw [map_pow, hzField, hy]

end GlobalClassFieldTheory.ClassFieldAxiom
end
end

section
-- module Solutions.OAIQ244_DUKE.LocalField_NonarchimedeanLocalField_NormalizedIntegerValuation
attribute [-instance] _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

/-!
# The normalized integer valuation of a local field

The Kummer branch of the local existence theorem uses power-class index
formulas stated for valuations with value group
`WithZero (Multiplicative ℤ)`.  A nonarchimedean local field carries its
canonical valuation in an intrinsic value group.  This file transports that
valuation to the integer model and proves that completeness and the finite
residue field are preserved.
-/

noncomputable section

namespace LocalFieldTheory

open scoped ValuativeRel

universe u

variable (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]

/-- The canonical local valuation, normalized to the value group
`WithZero (Multiplicative ℤ)`. -/
noncomputable def localIntegerValuation :
    _root_.Valuation K (WithZero (Multiplicative ℤ)) :=
  _root_.Valuation.map
    (IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt K).toMulEquiv.toMonoidWithZeroHom
    (IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt K).toOrderIso.monotone
    (ValuativeRel.valuation K)

/-- The integer-valued valuation applies the canonical value-group isomorphism. -/
@[simp]
theorem localIntegerValuation_apply (x : K) :
    localIntegerValuation K x =
      IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt K
        (ValuativeRel.valuation K x) :=
  rfl

end LocalFieldTheory

end
end

section
-- module Solutions.OAIQ244_DUKE.GlobalClassFieldTheory_Reciprocity_FinitePlaceArtin_NormRestriction
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

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

open LocalClassFieldTheory
open LocalFieldTheory

variable {K L : Type}
    [Field K] [NumberField K]
    [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsAbelianGalois K L]

abbrev finitePlaceNormCompletion
    (F : Type) [Field F] [NumberField F]
    (v : HeightOneSpectrum (𝓞 F)) :=
  (NumberField.HeightOneSpectrum.adicAbv F v).Completion

end Reciprocity
end GlobalClassFieldTheory
end
end

section
-- module Solutions.OAIQ244_DUKE.KummerTheory_Concrete_CyclotomicPrimeBaseChange
attribute [-instance] _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

/-!
# Prime cyclotomic base change

This file constructs the roots-of-unity base change for a prime-degree
extension.  If `L / K` has prime degree `p`, the
cyclotomic extension `K(μ_p) / K` has degree strictly smaller than `p`.
The two degrees are therefore coprime, and

`K(μ_p) ⊗[K] L`

is an actual field, Galois of degree `p` over `K(μ_p)`.
-/

open scoped NumberField TensorProduct
open NumberField

noncomputable section

namespace KummerTheory

universe u

variable
    (K L : Type u)
    [Field K] [NumberField K]
    [Field L] [NumberField L]
    [Algebra K L] [IsGalois K L]

/-- The prime cyclotomic base field used for prime-degree base change. -/
abbrev PrimeCyclotomicBase (p : ℕ) :=
  CyclotomicField p K

end KummerTheory
end
end

section
-- module Solutions.OAIQ244_DUKE.KummerTheory_Concrete_SimpleExtensionLocalBehavior
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

/-!
# Unramified finite places in simple Kummer extensions

This file proves the local unit case of the Kummer ramification criterion.
If both `b` and the exponent `n` are units at a finite place, then the
chosen localization of `K(ⁿ√b) / K` at that place is unramified.

The proof uses the existing algebraic localization, mathlib's minimal
polynomial API, and the complete-DVF different criterion.  No auxiliary
Kummer extension or alternative notion of unramifiedness is introduced.
-/

open scoped NumberField Classical NNReal TensorProduct ValuativeRel
open NumberField IsDedekindDomain
open LocalFieldTheory
open LocalClassFieldTheory

noncomputable section

namespace KummerTheory

variable {K : Type} [Field K] [NumberField K]

theorem valuativeRelExtension_isNontrivial
    {C F : Type}
    [Field C] [Field F] [Algebra C F]
    [ValuativeRel C] [ValuativeRel F]
    [Valuation.HasExtension
      (ValuativeRel.valuation C) (ValuativeRel.valuation F)]
    [(ValuativeRel.valuation C).IsNontrivial] :
    (ValuativeRel.valuation F).IsNontrivial := {
  exists_val_nontrivial := by
    let vC := ValuativeRel.valuation C
    let vF := ValuativeRel.valuation F
    rcases Valuation.IsNontrivial.exists_val_nontrivial
        (v := vC) with ⟨x, hx0, hx1⟩
    refine ⟨algebraMap C F x, ?_, ?_⟩
    · intro h
      have hm :
          vF (algebraMap C F x) =
            vF (algebraMap C F 0) := by
        simpa only [map_zero] using h
      exact hx0 (by
        simpa only [map_zero] using
          ((Valuation.HasExtension.val_map_eq_iff vC vF x 0).1 hm))
    · intro h
      have hm :
          vF (algebraMap C F x) =
            vF (algebraMap C F 1) := by
        simpa only [map_one] using h
      exact hx1 (by
        simpa only [map_one] using
          ((Valuation.HasExtension.val_map_eq_iff vC vF x 1).1 hm)) }

end KummerTheory
end
end


