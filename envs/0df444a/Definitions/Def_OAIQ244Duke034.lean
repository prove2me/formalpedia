-- Prove2me | Definitions.Def_OAIQ244Duke034
-- name    : OAIQ244Duke034
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-13T06:32:34.938718+00:00
-- url     : https://prove2.me/theorems/68e4ab22-12aa-4fc3-8d03-2c11cf41e9ee
-- title:
--   Definitions bundle OAIQ244Duke034 of the split of OpenAI, Equidistribution of Prime-Degree Torus Packets with Arbitrary Local Type
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.DukePrimeDegree.prime_degree_packet_measure_equidistribution_unconditional` and `OAI.DukePrimeDegree.prime_degree_packet_measures_tendsto_haar_unconditional`, carved from OpenAI's openai/math development (OpenAI, *Equidistribution of Prime-Degree Torus Packets with Arbitrary Local Type*, OpenAI Math Release, September 24, 2026, result family 15, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 75 declarations of OpenAI's Lean: 11 definitions, 1 inductive type or structure, 17 instances and 46 theorems. The definitions and types are `GlobalClassFieldTheory.Reciprocity.infinitePlaceBaseFourthRootField`, `GlobalClassFieldTheory.Reciprocity.infinitePlaceComplexificationOverfieldComplexPlace`, `GlobalClassFieldTheory.Reciprocity.infinitePlaceEmbeddedExtensionField`, `OAI.DukePrimeDegree.PhysicalPrefixWindow`, `OAI.DukePrimeDegree.RootPrefixCoordinates.factorParam`, `OAI.DukePrimeDegree.RootPrefixCoordinates.fullRectangleCoordinates`, `OAI.DukePrimeDegree.transverseLogDiagonal`, `RamificationTheory.HilbertRamification.Higher.dvfUniformizerQuotientUnit`, `RamificationTheory.HilbertRamification.Higher.dvfUniformizerRepresentativeHom`, `RamificationTheory.HilbertRamification.Higher.ramificationNumberOfUniqueExtension`, `RamificationTheory.HilbertRamification.Higher.uniformizerGradedHom`, `RamificationTheory.HilbertRamification.Higher.valuationSubringAlgEquivOfUniqueExtension`.
--
--   **Sources.** They come from these modules of lean/OAI/NumberTheory, in whole or in part: `AlgebraicNumberTheory_Idele_Extension_EmbeddingNorm`, `AlgebraicNumberTheory_RayClass_Rational`, `DukePrimeDegree_Geometry_PhysicalPrefixWindows`, `DukePrimeDegree_Geometry_PrefixExchangeRegions`, `DukePrimeDegree_Geometry_RootPrefixFactorChart`, `DukePrimeDegree_Geometry_TransverseDiagonalData`, `GlobalClassFieldTheory_GlobalClassFields_ClassFieldRealization`, `GlobalClassFieldTheory_Reciprocity_ComplexificationArtin_InfinitePlaceOverfield`, `GlobalClassFieldTheory_Reciprocity_ComplexificationArtin_RationalComplexification`, `GlobalClassFieldTheory_Reciprocity_InfinitePlaceArtin`, `GlobalClassFieldTheory_Reciprocity_RationalPrimeFactorization`, `KummerTheory_Concrete_SUnitKummerUnramified`, `KummerTheory_Concrete_SUnitPreparation_FullSUnitKummerExtension`, `Kummer_Concrete_FiniteSupport`, `LocalField_DiscreteValuationField_Basic`, `LocalField_DiscreteValuationField_PadicValuationComparison`, `LocalField_DiscreteValuationField_Units`, `LocalField_DiscreteValuationField_ValuationSubringUnits_ValuationSubringUnitMap`, `Ramification_HilbertRamification_CompleteDVF`, `Ramification_HilbertRamification_Monogeneity`, `Ramification_HilbertRamification_RamificationNumber`, `Ramification_HilbertRamification_UniformizerGradedHom`, `Ramification_HilbertRamification_UniqueExtensionIntegralClosure`, `Valuation_DiscreteValuationField_Basic`, `Valuation_DiscreteValuationField_Extensions`.
--
--   **Imports.** It imports the published bundle `Def_DukePrimeDegree`; the bundles `OAIQ244Duke015`, `OAIQ244Duke016`, `OAIQ244Duke017`, `OAIQ244Duke018`, `OAIQ244Duke019`, `OAIQ244Duke021` and `OAIQ244Duke022` of this split.
--
--   **Imported by** (directly, in this split): the bundle `OAIQ244Duke044`.
-- source:
--   OpenAI, Equidistribution of Prime-Degree Torus Packets with Arbitrary Local Type, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 15; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Equidistribution-of-Prime-Degree-Torus-Packets-with-Arbitrary-Local-Type-September-24-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/NumberTheory at commit 7ef5c0c

import Mathlib
import Mathlib.Algebra.Algebra.Basic
import Mathlib.Algebra.Algebra.Pi
import Mathlib.Algebra.Algebra.Tower
import Mathlib.Algebra.BigOperators.Finprod
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Lemmas
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
import Mathlib.Algebra.Group.Hom.Instances
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
import Mathlib.Algebra.GroupWithZero.Action.Prod
import Mathlib.Algebra.Module.Equiv.Basic
import Mathlib.Algebra.Module.LinearMap.Polynomial
import Mathlib.Algebra.Module.MinimalAxioms
import Mathlib.Algebra.Module.PID
import Mathlib.Algebra.Module.Shrink
import Mathlib.Algebra.Module.Torsion.Basic
import Mathlib.Algebra.Module.ZLattice.Basic
import Mathlib.Algebra.Module.ZMod
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Algebra.Order.Field.Power
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Algebra.Order.Group.Cyclic
import Mathlib.Algebra.Order.Hom.Units
import Mathlib.Algebra.Order.Ring.IsNonarchimedean
import Mathlib.Algebra.Order.WithTop.Untop0
import Mathlib.Algebra.Polynomial.Div
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Algebra.Polynomial.FieldDivision
import Mathlib.Algebra.Polynomial.Lifts
import Mathlib.Algebra.Polynomial.Monic
import Mathlib.Algebra.Polynomial.Splits
import Mathlib.Algebra.Ring.GeomSum
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
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Finsupp
import Mathlib.Data.Finset.Max
import Mathlib.Data.Finsupp.Fintype
import Mathlib.Data.Int.ModEq
import Mathlib.Data.Int.WithZero
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.Nat.GCD.BigOperators
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Rat.Cast.CharZero
import Mathlib.Data.Rat.Lemmas
import Mathlib.Data.Set.Finite.Range
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.ZMod.QuotientGroup
import Mathlib.Data.ZMod.QuotientRing
import Mathlib.Data.ZMod.Units
import Mathlib.Dynamics.BirkhoffSum.Basic
import Mathlib.Dynamics.Ergodic.Conservative
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
import Mathlib.FieldTheory.IntermediateField.Basic
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.FieldTheory.IsAlgClosed.Basic
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
import Mathlib.FieldTheory.SplittingField.Construction
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
import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
import Mathlib.LinearAlgebra.Matrix.Gershgorin
import Mathlib.LinearAlgebra.Pi
import Mathlib.LinearAlgebra.Quotient.Pi
import Mathlib.LinearAlgebra.StdBasis
import Mathlib.LinearAlgebra.TensorProduct.Basis
import Mathlib.LinearAlgebra.TensorProduct.RightExactness
import Mathlib.LinearAlgebra.Trace
import Mathlib.Logic.Equiv.Fin.Rotate
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Mathlib.MeasureTheory.Covering.Besicovitch
import Mathlib.MeasureTheory.Function.ContinuousMapDense
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Measure.Haar.Basic
import Mathlib.MeasureTheory.Measure.Prokhorov
import Mathlib.MeasureTheory.Measure.Regular
import Mathlib.MeasureTheory.OuterMeasure.BorelCantelli
import Mathlib.NumberTheory.Cyclotomic.Basic
import Mathlib.NumberTheory.Cyclotomic.CyclotomicCharacter
import Mathlib.NumberTheory.Cyclotomic.Discriminant
import Mathlib.NumberTheory.Cyclotomic.Gal
import Mathlib.NumberTheory.LocalField.Basic
import Mathlib.NumberTheory.NumberField.AdeleRing
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.NumberTheory.NumberField.CMField
import Mathlib.NumberTheory.NumberField.ClassNumber
import Mathlib.NumberTheory.NumberField.Completion.FinitePlace
import Mathlib.NumberTheory.NumberField.Completion.InfinitePlace
import Mathlib.NumberTheory.NumberField.Completion.LiesOverInstances
import Mathlib.NumberTheory.NumberField.Completion.Ramification
import Mathlib.NumberTheory.NumberField.Cyclotomic.Basic
import Mathlib.NumberTheory.NumberField.Cyclotomic.Galois
import Mathlib.NumberTheory.NumberField.Cyclotomic.Ideal
import Mathlib.NumberTheory.NumberField.InfinitePlace.Ramification
import Mathlib.NumberTheory.NumberField.ProductFormula
import Mathlib.NumberTheory.NumberField.Units.Basic
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
import Mathlib.NumberTheory.RamificationInertia.Unramified
import Mathlib.NumberTheory.RamificationInertia.Valuation
import Mathlib.Order.Filter.AtTopBot.Tendsto
import Mathlib.Probability.Kernel.Disintegration.StandardBorel
import Mathlib.Probability.Kernel.MeasurableIntegral
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
import Mathlib.RingTheory.Finiteness.Cardinality
import Mathlib.RingTheory.Finiteness.Finsupp
import Mathlib.RingTheory.FormalGroup.Basic
import Mathlib.RingTheory.FractionalIdeal.Norm
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Ideal.Defs
import Mathlib.RingTheory.Ideal.GoingUp
import Mathlib.RingTheory.Ideal.IsPrincipalPowQuotient
import Mathlib.RingTheory.Ideal.Norm.AbsNorm
import Mathlib.RingTheory.Ideal.Norm.RelNorm
import Mathlib.RingTheory.Ideal.Quotient.Index
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.RingTheory.IntegralClosure.IsIntegralClosure.Basic
import Mathlib.RingTheory.Invariant.Basic
import Mathlib.RingTheory.Invariant.Profinite
import Mathlib.RingTheory.IsAdjoinRoot
import Mathlib.RingTheory.IsTensorProduct
import Mathlib.RingTheory.LaurentSeries
import Mathlib.RingTheory.LocalRing.Basic
import Mathlib.RingTheory.LocalRing.Module
import Mathlib.RingTheory.LocalRing.ResidueField.Basic
import Mathlib.RingTheory.Localization.Away.Basic
import Mathlib.RingTheory.Localization.Finiteness
import Mathlib.RingTheory.MvPowerSeries.Expand
import Mathlib.RingTheory.MvPowerSeries.Inverse
import Mathlib.RingTheory.MvPowerSeries.Order
import Mathlib.RingTheory.MvPowerSeries.Substitution
import Mathlib.RingTheory.MvPowerSeries.Trunc
import Mathlib.RingTheory.Nakayama
import Mathlib.RingTheory.Norm.Basic
import Mathlib.RingTheory.Norm.Defs
import Mathlib.RingTheory.Norm.Transitivity
import Mathlib.RingTheory.Polynomial.ContentIdeal
import Mathlib.RingTheory.Polynomial.Cyclotomic.Roots
import Mathlib.RingTheory.Polynomial.Eisenstein.Basic
import Mathlib.RingTheory.Polynomial.Eisenstein.IsIntegral
import Mathlib.RingTheory.Polynomial.GaussLemma
import Mathlib.RingTheory.Polynomial.RationalRoot
import Mathlib.RingTheory.Polynomial.Vieta
import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.RingTheory.PowerSeries.Binomial
import Mathlib.RingTheory.PowerSeries.Evaluation
import Mathlib.RingTheory.PowerSeries.Expand
import Mathlib.RingTheory.PowerSeries.Inverse
import Mathlib.RingTheory.PowerSeries.Log
import Mathlib.RingTheory.PowerSeries.Order
import Mathlib.RingTheory.PowerSeries.Substitution
import Mathlib.RingTheory.PowerSeries.Trunc
import Mathlib.RingTheory.PowerSeries.WellKnown
import Mathlib.RingTheory.QuasiFinite.Basic
import Mathlib.RingTheory.RamificationInertia.Basic
import Mathlib.RingTheory.RamificationInertia.Inertia
import Mathlib.RingTheory.RootsOfUnity.Basic
import Mathlib.RingTheory.RootsOfUnity.Complex
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
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
import Mathlib.Tactic.Ring
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
import Mathlib.Topology.Order.MonotoneContinuity
import Mathlib.Topology.Sequences
import Mathlib.Topology.Sets.Opens
import Mathlib.Topology.UniformSpace.AbsoluteValue
import Mathlib.Topology.UniformSpace.HeineCantor
import Mathlib.Topology.WithTopology
import Definitions.Def_DukePrimeDegree
import Definitions.Def_OAIQ244Duke015
import Definitions.Def_OAIQ244Duke016
import Definitions.Def_OAIQ244Duke017
import Definitions.Def_OAIQ244Duke018
import Definitions.Def_OAIQ244Duke019
import Definitions.Def_OAIQ244Duke021
import Definitions.Def_OAIQ244Duke022

section
-- module Solutions.OAIQ244_DUKE.AlgebraicNumberTheory_Idele_Extension_EmbeddingNorm
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.PrimeDegreePackets.diagonalLogAction _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionResidueField.instField _root_.RamificationTheory.HilbertRamification.ValuationSubring.selectedResidueField.instAlgebra _root_.RelativeIdeleGroup.principalQuotientAction _root_.ValuationTheory.DiscreteValuationField.DVF.maximalIdealPowSuccQuotModule _root_.ValuationTheory.DiscreteValuationField.DVF.residueField.field _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.isDomain _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.isLocalRing _root_.CyclicCohomology.binaryCoefficientFamilyCommGroup _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteIdeleGroupIsTopologicalGroup _root_.finiteLocalUnitsOpen _root_.ideleGroupIsTopologicalGroup _root_.relativeAdeleRingIntermediateAlgebra _root_.relativeAdeleRingTopIntermediateAlgebra
attribute [-simp] _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.IsDiscreteValuationRing.addVal_ringEquiv _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.LocalFieldTheory.residueField_algebraMap_residue _root_.OAI.PrimeDegreePackets.ThetaConstruction.schwartzCM_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

/-!
# Norms through an ambient Galois extension

This file proves the embedded-subextension determinant-norm formula.
If `L/K` is embedded in a finite Galois extension `M/K`, extending the
determinant norm of an element of `A ⊗[K] L` to `A ⊗[K] M` gives the
product over all `K`-embeddings `L → M`.
-/

open scoped BigOperators TensorProduct
open NumberField

noncomputable section

namespace RelativeIdeleGroup

universe u v w z

section UniversalPolynomial

variable
    {K : Type u} {L : Type v} {M : Type w}
    [Field K] [Field L] [Field M]
    [Algebra K L] [Algebra K M] [Algebra L M]
    [IsScalarTower K L M]
    [FiniteDimensional K L] [FiniteDimensional K M]
    [IsGalois K M]

/-- Full scalar-extension norm formula for a subextension of a
finite Galois extension. -/
theorem includeLeft_norm_eq_prod_scalarEmbeddings
    [Infinite K]
    (A : Type*) [CommRing A] [Algebra K A]
    [Nontrivial A] (x : A ⊗[K] L) :
    (Algebra.TensorProduct.includeLeft
      (R := K) (S := K) (A := A) (B := M))
        (Algebra.norm A x) =
      ∏ f : L →ₐ[K] M,
        scalarEmbedding A f x := by
  classical
  let b := Module.Free.chooseBasis K L
  let c : Module.Free.ChooseBasisIndex K L → A :=
    fun i ↦
      (Algebra.TensorProduct.basis A b).repr x i
  let iL : A →+* A ⊗[K] M :=
    (Algebra.TensorProduct.includeLeft
      (R := K) (S := K) (A := A) (B := M)).toRingHom
  let iR : M →+* A ⊗[K] M :=
    (Algebra.TensorProduct.includeRight
      (R := K) (A := A) (B := M)).toRingHom
  have hmaps :
      iL.comp (algebraMap K A) =
        iR.comp (algebraMap K M) := by
    ext t
    simp [iL, iR]
  have hleft :
      MvPolynomial.eval₂ iR
          (fun i ↦ iL (c i))
          (MvPolynomial.map (algebraMap K M)
            (normPolynomial b)) =
        iL (Algebra.norm A x) := by
    rw [MvPolynomial.eval₂_map]
    rw [← hmaps]
    rw [← MvPolynomial.hom_eval₂]
    rw [eval₂_normPolynomial_baseChange]
  have hright :
      MvPolynomial.eval₂ iR
          (fun i ↦ iL (c i))
          (embeddingProductPolynomial
            (M := M) b) =
        ∏ f : L →ₐ[K] M,
          scalarEmbedding A f x := by
    rw [embeddingProductPolynomial,
      MvPolynomial.eval₂_prod]
    apply Finset.prod_congr rfl
    intro f hf
    exact
      eval₂_embeddingPolynomial_baseChange
        A b f x
  change iL (Algebra.norm A x) =
    ∏ f : L →ₐ[K] M,
      scalarEmbedding A f x
  rw [← hright, ← hleft,
    map_normPolynomial_eq_embeddingProductPolynomial b]

end UniversalPolynomial

section RelativeAdeles

variable
    {K : Type u} {L : Type v} {M : Type w}
    [Field K] [Field L] [Field M]
    [NumberField K]
    [Algebra K L] [Algebra K M] [Algebra L M]
    [IsScalarTower K L M]
    [FiniteDimensional K L] [FiniteDimensional K M]
    [IsGalois K M]

/-- The embedded-subextension adèle form of the Galois product norm formula. -/
theorem adeleInclusion_norm_eq_prod_embeddings
    (x : RelativeAdeleRing K L) :
    adeleInclusion K M
        (Algebra.norm
          (NumberField.AdeleRing (𝓞 K) K) x) =
      ∏ f : L →ₐ[K] M,
        adeleEmbedding f x := by
  exact
    includeLeft_norm_eq_prod_scalarEmbeddings
      (K := K) (L := L) (M := M)
      (NumberField.AdeleRing (𝓞 K) K) x

/-- The embedded-subextension idèle form of the Galois product norm formula. -/
theorem inclusion_norm_eq_prod_embeddings
    (a : RelativeIdeleGroup K L) :
    inclusion K M (norm K L a) =
      ∏ f : L →ₐ[K] M,
        ideleEmbedding f a := by
  apply Units.ext
  simp only [inclusion, norm, MonoidHom.comp_apply,
    Units.coe_map, Units.coe_prod, ideleEmbedding,
    adeleEmbedding]
  exact
    adeleInclusion_norm_eq_prod_embeddings
      (K := K) (L := L) (M := M)
      (a : RelativeAdeleRing K L)

end RelativeAdeles

end RelativeIdeleGroup
end
end

section
-- module Solutions.OAIQ244_DUKE.LocalField_DiscreteValuationField_Units
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.DiscreteValuationField.ValuedNorm.filtrationPreimageClassInQuotient_normal _root_.LocalFieldTheory.DiscreteValuationField.ValuedNorm.filtrationPreimageSubgroup_normal _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

namespace LocalFieldTheory

/-!
# Principal-unit filtrations

This file provides a theorem API for antitone principal-unit filtrations used by
ramification and norm arguments.
-/

universe u v

open scoped BigOperators

namespace DiscreteValuationField

namespace AntitoneSubgroupFiltration

variable {G : Type u} [Group G] (U : AntitoneSubgroupFiltration G)

/-- The type in `Finite (U.principalUnitGradedPiece n)` is finite. -/
noncomputable instance principalUnitGradedPieceFinite
    (n : ℕ) [(U.principalUnitSubgroup (n + 1)).Normal]
    [Finite (U.principalUnitSubquotient n (n + 1))] :
    Finite (U.principalUnitGradedPiece n) :=
  Finite.of_equiv (U.principalUnitSubquotient n (n + 1))
    (U.principalUnitGradedPieceEquivSubquotient n).symm.toEquiv

end AntitoneSubgroupFiltration

end DiscreteValuationField

end LocalFieldTheory
end

section
-- module Solutions.OAIQ244_DUKE.AlgebraicNumberTheory_RayClass_Rational
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.PrimeDegreePackets.instNonemptyLeafTestSpace _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionResidueField.instField _root_.RamificationTheory.HilbertRamification.ValuationSubring.selectedResidueField.instAlgebra _root_.ValuationTheory.DiscreteValuationField.DVF.residueField.field _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

/-!
# Ray class groups of the rational numbers

This file computes ray class groups of the rational numbers. A positive integer
`m` determines a full narrow ray modulus: its finite part has exponent
`m.factorization p` at `p`, and its real place imposes positivity. The
positive generator of an ideal prime to this modulus gives the explicit
isomorphism with `(ZMod m)ˣ`.
-/

open scoped NumberField Classical
open NumberField IsDedekindDomain

noncomputable section


namespace RayClass

attribute [local instance] RayClass.rationalRingOfIntegersIsPrincipalIdealRing
local instance rationalNatGeneratorPrimeFact_r862dfd_1
    (v : HeightOneSpectrum (𝓞 ℚ)) :
    Fact (Nat.Prime (Rat.HeightOneSpectrum.natGenerator v)) :=
  ⟨Rat.HeightOneSpectrum.prime_natGenerator v⟩
local instance rationalPrimesEquivPrimeFact_r862dfd_1
    (v : HeightOneSpectrum (𝓞 ℚ)) :
    Fact
      (Nat.Prime
        ((Rat.HeightOneSpectrum.primesEquiv
          (R := 𝓞 ℚ) v : Nat.Primes) : ℕ)) :=
  ⟨(Rat.HeightOneSpectrum.primesEquiv
    (R := 𝓞 ℚ) v).property⟩
/-- Zero principal-ideal exponent at a rational finite place forces
valuation one. -/
theorem valuation_eq_one_of_principal_count_eq_zero
    (x : ℚˣ) (v : HeightOneSpectrum (𝓞 ℚ))
    (hcount :
      FractionalIdeal.count ℚ v
        (toPrincipalIdeal (𝓞 ℚ) ℚ x :
          FractionalIdeal (nonZeroDivisors (𝓞 ℚ)) ℚ) = 0) :
    v.valuation ℚ (x : ℚ) = 1 := by
  rw [IdeleGroup.count_toPrincipalIdeal] at hcount
  have hlog :
      WithZero.log (v.valuation ℚ (x : ℚ)) = 0 :=
    neg_eq_zero.mp hcount
  have hvne : v.valuation ℚ (x : ℚ) ≠ 0 :=
    (v.valuation ℚ).ne_zero_of_unit x
  exact withZero_eq_one_of_log_eq_zero hvne hlog

/-- A rational prime with zero principal-ideal exponent does not divide
the denominator. -/
theorem not_dvd_den_of_principal_count_eq_zero
    (x : ℚˣ) (v : HeightOneSpectrum (𝓞 ℚ))
    (hcount :
      FractionalIdeal.count ℚ v
        (toPrincipalIdeal (𝓞 ℚ) ℚ x :
          FractionalIdeal (nonZeroDivisors (𝓞 ℚ)) ℚ) = 0) :
    ¬ Rat.HeightOneSpectrum.natGenerator v ∣ (x : ℚ).den := by
  let p := Rat.HeightOneSpectrum.natGenerator v
  let : Fact p.Prime :=
    ⟨Rat.HeightOneSpectrum.prime_natGenerator v⟩
  have hequiv :=
    Rat.HeightOneSpectrum.valuation_equiv_padicValuation v
  have hpval : Rat.padicValuation p (x : ℚ) = 1 :=
    hequiv.eq_one_iff_eq_one.mp
      (valuation_eq_one_of_principal_count_eq_zero x v hcount)
  apply Rat.padicValuation_le_one_iff.mp
  exact le_of_eq hpval

/-- A rational prime with zero principal-ideal exponent does not divide
the numerator. -/
theorem not_dvd_num_of_principal_count_eq_zero
    (x : ℚˣ) (v : HeightOneSpectrum (𝓞 ℚ))
    (hcount :
      FractionalIdeal.count ℚ v
        (toPrincipalIdeal (𝓞 ℚ) ℚ x :
          FractionalIdeal (nonZeroDivisors (𝓞 ℚ)) ℚ) = 0) :
    ¬ Rat.HeightOneSpectrum.natGenerator v ∣ (x : ℚ).num.natAbs := by
  let p := Rat.HeightOneSpectrum.natGenerator v
  let : Fact p.Prime :=
    ⟨Rat.HeightOneSpectrum.prime_natGenerator v⟩
  have hpval :
      Rat.padicValuation p (x : ℚ) = 1 :=
    (Rat.HeightOneSpectrum.valuation_equiv_padicValuation v).eq_one_iff_eq_one.mp
      (valuation_eq_one_of_principal_count_eq_zero x v hcount)
  have hden : ¬ p ∣ (x : ℚ).den :=
    not_dvd_den_of_principal_count_eq_zero x v hcount
  have hdenval :
      Int.padicValuation p ((x : ℚ).den : ℤ) = 1 :=
    Int.padicValuation_eq_one_iff.mpr
      (by simpa only [Int.natCast_dvd_natCast] using hden)
  rw [← (x : ℚ).num_div_den, map_div₀,
    Rat.padicValuation_cast, ← Int.cast_natCast,
    Rat.padicValuation_cast, hdenval, div_one] at hpval
  exact fun hpdiv =>
    (Int.padicValuation_eq_one_iff.mp hpval)
      (Int.natCast_dvd.mpr hpdiv)

/-! ### The local congruence condition over `ℚ` -/

end RayClass
end
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Geometry_RootPrefixFactorChart
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.InitialRootStep.nextConjugatedKernel_markov _root_.OAI.DukePrimeDegree.positiveRootGeneratedGroup_secondCountable _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Actual one-root transversals inside every remaining-group chart -/

noncomputable section
open Matrix Set
open scoped Topology

namespace DukePrimeDegree
open PrimeDegreePackets

namespace RootPrefixCoordinates
variable {n : ℕ} (s : InitialRootStep n) {T : Type*} [TopologicalSpace T]
  (C : RootPrefixCoordinates n s.processed T) (g : G n)

def factorParam (z : FactorTransverse s (T := T) × ℝ) : G n :=
  C.factorBase s g z.1 * Matrix.SpecialLinearGroup.transvection s.distinct z.2

end RootPrefixCoordinates
end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Geometry_PrefixExchangeRegions
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.EliminationChain.futureAmbientKernel_markov _root_.OAI.DukePrimeDegree.EliminationChain.wholeFutureProbabilityKernel_markov _root_.OAI.DukePrimeDegree.InitialRootStep.nextConjugatedKernel_markov _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Injective open regions in the exchanged prefix chart -/

noncomputable section
open Matrix MeasureTheory Set
namespace DukePrimeDegree
open PrimeDegreePackets
namespace RootPrefixCoordinates
variable {d : ℕ} (q : InitialRootStep (d+1)) {T : Type*} [TopologicalSpace T]
    (C : RootPrefixCoordinates (d+1) q.processed T) (g : G (d+1)) (k : Fin (d+1))
    {D : Finset (Fin (d+1))} (c : EliminationChain (insert q.root q.processed) D)
    (hfinal : c.finalEntries = allPositiveRoots (d+1))

def fullRectangleCoordinates (Q : RootTransverseRectangle (C.factorPivotDomain q g k))
    (z : Q.first × (Q.second × ℝ)) : (UpperRootTransverse (d+1) × T) ×
      (positiveRootGeneratedGroup (q.remaining.erase q.root) × ℝ) :=
  (z.1.val,(z.2.1.val,z.2.2))

end RootPrefixCoordinates
end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Geometry_PhysicalPrefixWindows
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.EliminationChain.futureAmbientKernel_markov _root_.OAI.DukePrimeDegree.EliminationChain.wholeFutureProbabilityKernel_markov _root_.OAI.DukePrimeDegree.InitialRootStep.nextConjugatedKernel_markov _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Physical product windows covering compact prefix-time sets -/

noncomputable section
open Matrix MeasureTheory ProbabilityTheory Set
namespace DukePrimeDegree
open PrimeDegreePackets

structure PhysicalPrefixWindow {d : ℕ} (q : InitialRootStep (d+1))
    {T : Type*} [TopologicalSpace T]
    (C : RootPrefixCoordinates (d+1) q.processed T) (g : G (d+1)) where
  pivot : Fin (d+1)
  rectangle : RootTransverseRectangle (C.factorPivotDomain q g pivot)
  second_nonempty : rectangle.second.Nonempty
  box : RootBox q.distinct pivot
  transverse_eq : box.transverse = range (C.rectangleSlice q g pivot rectangle)
  interval : Set ℝ
  interval_open : IsOpen interval
  radius : ℝ
  box_time_bound : box.time ⊆ rootLeafWindow radius 0
  second_bound : Set (positiveRootGeneratedGroup (q.remaining.erase q.root))
  second_bound_compact : IsCompact second_bound
  second_subset : rectangle.second ⊆ second_bound
  interval_bound : Set ℝ
  interval_bound_compact : IsCompact interval_bound
  interval_subset : interval ⊆ interval_bound
  window : ∀ w : rectangle.first × rectangle.second,
    (Homeomorph.addRight (C.rectangleTime q g pivot rectangle w)) '' interval ⊆ box.time

end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Geometry_TransverseDiagonalData
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.EliminationChain.futureAmbientKernel_markov _root_.OAI.DukePrimeDegree.EliminationChain.wholeFutureProbabilityKernel_markov _root_.OAI.DukePrimeDegree.InitialRootStep.nextConjugatedKernel_markov _root_.OAI.DukePrimeDegree.positiveRootGeneratedGroup_secondCountable _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Diagonal coordinates on the transverse lower triangular slice

Column ratios are fixed by the diagonal action; the logarithms of the
absolute diagonal entries are translated linearly. These are the actual
transverse coordinates, before choosing any finite entropy approximation.
-/

noncomputable section
open Matrix Set
open scoped Topology BigOperators
namespace DukePrimeDegree
open PrimeDegreePackets

def transverseLogDiagonal {n : ℕ} (s : UpperRootTransverse n) : Fin n → ℝ :=
  fun i => Real.log |s.val.val i i|

end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.GlobalClassFieldTheory_GlobalClassFields_ClassFieldRealization
attribute [-instance] _root_.ClassFormation.DegreeData.frobeniusClosure_isTopologicalGroup _root_.ClassFormation.FiniteGaloisSubextension.extensionSubgroup_over_intermediate_normalInstance _root_.ClassFormation.FiniteGaloisSubextension.intermediateField_normalInstance _root_.ClassFormation.conjugateExtension_normal _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalClassFieldTheory.finiteGaloisExtensionSubgroupOfEmbedding_normal _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.LubinTate.compatibleGroupFamiliesGroup _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionResidueField.instField _root_.RamificationTheory.HilbertRamification.ValuationSubring.selectedResidueField.instAlgebra _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.maximalIdealPowSuccQuotModule _root_.ValuationTheory.DiscreteValuationField.DVF.residueField.field _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen _root_.relativeAdeleRingIntermediateAlgebra _root_.relativeAdeleRingTopIntermediateAlgebra
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

/-!
# Concrete realization of finite abelian subextensions

A finite abelian subextension in the abstract class-formation lattice is
represented by two nested closed subgroups of an ambient Galois group.  Its
upper relative fixed field is an actual finite extension of the lower fixed
field.  The quotient-to-Galois-group equivalence transports the commutativity
carried by the abstract package, so this actual extension is abelian Galois.
-/

noncomputable section

namespace GlobalClassFieldTheory
namespace GlobalClassFields

open ClassFormation
open LocalClassFieldTheory
open CyclicCohomology
open scoped IsMulCommutative

universe u v w

variable
    {k Ω : Type}
    [Field k] [Field Ω] [Algebra k Ω] [IsGalois k Ω]
    {K : ClosedSubgroup (Gal(Ω / k))}

/-- The relative fixed field represented by a finite abelian subextension is
finite-dimensional over the fixed field represented by its base subgroup. -/
noncomputable instance
    finiteAbelianSubextensionAbstractRelativeFixedFieldFiniteDimensional
    [hKfinite : Finite
      ((baseField Gal(Ω / k)).toSubgroup ⧸
        extensionSubgroup
          (baseField Gal(Ω / k)) K (le_baseField K))]
    (L : FiniteAbelianSubextension K) :
    FiniteDimensional
      (abstractFixedField k Ω K)
      (abstractRelativeFixedField k Ω L.below) :=
  abstractRelativeFixedField_finiteDimensional
    k Ω K L.field L.below hKfinite L.finite

end GlobalClassFields
end GlobalClassFieldTheory
end
end

section
-- module Solutions.OAIQ244_DUKE.Valuation_DiscreteValuationField_Basic
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.DiscreteValuationField.LocalField.residueField_charP_residueCharacteristic _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.RamificationTheory.HilbertRamification.Higher.lowerRamificationGroup.instNormal _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.RamificationTheory.HilbertRamification.CompleteDVF.decompositionGroupMulSemiringAction _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen
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

/-- The valuation ring of a DVF is Noetherian. -/
theorem valuationSubring_isNoetherianRing (F : DVF.{u, v} K) :
    IsNoetherianRing F.valuationSubring := by
  have : IsDiscreteValuationRing F.valuationSubring :=
    F.valuationSubring_isDiscreteValuationRing
  infer_instance

/-! ### Successive quotients of powers of the maximal ideal -/

end DVF
end DiscreteValuationField

end

end ValuationTheory
end

section
-- module Solutions.OAIQ244_DUKE.Valuation_DiscreteValuationField_Extensions
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.DiscreteValuationField.LocalField.residueField_charP_residueCharacteristic _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.RamificationTheory.HilbertRamification.Higher.lowerRamificationGroup.instNormal _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.RamificationTheory.HilbertRamification.CompleteDVF.decompositionGroupMulSemiringAction _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

namespace ValuationTheory

/-!
# Finite extensions of discretely valued fields

The extension relation is ambient data: an algebra, finite-dimensionality, and
mathlib's `Valuation.HasExtension` property.  There is deliberately no
proof-irrelevant marker object.  All invariants and maps are defined once for
`DVF` values and can therefore be used unchanged for Henselian and complete
discretely valued fields through their canonical `toDVF` projections.
-/

noncomputable section

universe u v w x

namespace DiscreteValuationField
namespace ValuedExtension

variable {K : Type u} {L : Type w} [Field K] [Field L]
variable [Algebra K L] [FiniteDimensional K L]
variable (base : DVF.{u, v} K) (target : DVF.{w, x} L)
variable [base.valuation.HasExtension target.valuation]

omit [FiniteDimensional K L] in
/-- Maximal-ideal membership is reflected by a valued extension. -/
theorem integerMap_mem_maximalIdeal_iff (a : base.valuationSubring) :
    integerMap base target a ∈ target.maximalIdeal ↔
      a ∈ base.maximalIdeal := by
  rw [target.mem_maximalIdeal_iff (integerMap base target a),
    base.mem_maximalIdeal_iff a, integerMap_apply base target a]
  exact _root_.Valuation.HasExtension.val_map_lt_one_iff
    (vR := base.valuation) (vA := target.valuation) (a : K)

omit [FiniteDimensional K L] in
/-- The target maximal ideal pulls back to the base maximal ideal. -/
theorem maximalIdeal_comap_integerMap_eq :
    target.maximalIdeal.comap (integerMap base target) =
      base.maximalIdeal := by
  ext a
  exact integerMap_mem_maximalIdeal_iff base target a

omit [FiniteDimensional K L] in
/-- The source maximal ideal maps into the target maximal ideal. -/
theorem maximalIdeal_map_integerMap_le :
    Ideal.map (integerMap base target) base.maximalIdeal ≤
      target.maximalIdeal := by
  rw [Ideal.map_le_iff_le_comap,
    maximalIdeal_comap_integerMap_eq base target]

/- A valued extension preserves the residue-field characteristic. -/

end ValuedExtension
end DiscreteValuationField
end
end ValuationTheory
end

section
-- module Solutions.OAIQ244_DUKE.LocalField_DiscreteValuationField_Basic
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_isCompleteDiscrete _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.DiscreteValuationField.Examples.Qp.padicDVRValuation_isRankOneDiscrete _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.RamificationTheory.HilbertRamification.Higher.lowerRamificationGroup.instNormal _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.RamificationTheory.HilbertRamification.CompleteDVF.decompositionGroupMulSemiringAction _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

/-!
# Local fields

A local-field package here is a chosen complete discretely valued field with
finite residue field.  The topology-first mathlib class remains available
through imports; this file only adds the chosen-valuation API needed downstream.
-/

universe u v w x

namespace LocalFieldTheory.DiscreteValuationField

open ValuationTheory.DiscreteValuationField

namespace LocalField

variable {K : Type u} [Field K]

/-- A local field package has a uniformizer. -/
theorem exists_uniformizer (F : LocalField.{u, v} K) :
    ∃ pi : F.valuationSubring, F.toCompleteDVF.valuation.IsUniformizer (pi : K) :=
  F.toCompleteDVF.exists_uniformizer

end LocalField
end LocalFieldTheory.DiscreteValuationField
end

section
-- module Solutions.OAIQ244_DUKE.LocalField_DiscreteValuationField_ValuationSubringUnits_ValuationSubringUnitMap
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.RamificationTheory.HilbertRamification.Higher.lowerRamificationGroup.instNormal _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.RamificationTheory.HilbertRamification.CompleteDVF.decompositionGroupMulSemiringAction _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

/-!
# Valuation-subring units inside field units

This file defines the canonical homomorphism from units of a complete-DVF
valuation ring to units of its fraction field.
-/

noncomputable section

universe u v

namespace LocalFieldTheory.DiscreteValuationField
open ValuationTheory.DiscreteValuationField

namespace CompleteDVF

variable {K : Type u} [Field K]

/--
Establishes the membership statement `(CompleteDVF.valuationSubringUnitsToFieldUnits F) a ∈
F.valuation.valuationSubring.unitGroup`.
-/
theorem valuationSubringUnitsToFieldUnits_mem_unitGroup
    (F : CompleteDVF.{u, v} K) (a : F.valuationSubringˣ) :
    (LocalFieldTheory.DiscreteValuationField.CompleteDVF.valuationSubringUnitsToFieldUnits F) a ∈
      F.valuation.valuationSubring.unitGroup := by
  change
    ((F.valuation.valuationSubring.unitGroupMulEquiv.symm a :
      F.valuation.valuationSubring.unitGroup) : Kˣ) ∈
      F.valuation.valuationSubring.unitGroup
  exact (F.valuation.valuationSubring.unitGroupMulEquiv.symm a).2


end CompleteDVF
end LocalFieldTheory.DiscreteValuationField

end
end

section
-- module Solutions.OAIQ244_DUKE.GlobalClassFieldTheory_Reciprocity_RationalPrimeFactorization
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.KummerTheory.nthRootsSubgroupFintype _root_.LocalFieldTheory.DiscreteValuationField.LocalField.residueCharacteristic.fact_prime _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionResidueField.instField _root_.RamificationTheory.HilbertRamification.ValuationSubring.selectedResidueField.instAlgebra _root_.ValuationTheory.DiscreteValuationField.DVF.residueField.field _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.CyclicCohomology.binaryCoefficientFamilyCommGroup _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic
attribute [-simp] _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.IsDiscreteValuationRing.addVal_ringEquiv _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.OAI.PrimeDegreePackets.ThetaConstruction.schwartzCM_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

/-!
# Prime factorization of a nonzero rational number

This file records the elementary rational factorization needed for the
principal-idele calculation over `ℚ`.  At a fixed rational prime `p`, removing
the `p`-power from `x : ℚˣ` leaves the sign of `x` times the finite product of
the powers of all primes different from `p`.

The last declarations package rational `p`-adic units as units of `ℤ_[p]` and
identify the reduction of a natural unit modulo `p ^ k`.
-/

open scoped BigOperators Classical

noncomputable section

namespace GlobalClassFieldTheory
namespace Reciprocity

local instance localInst_r862dfd_1 (p : Nat.Primes) : Fact p.1.Prime :=
  ⟨p.2⟩
/-- The `p`-adic unit part of `x` is its sign times the finite product of
`q ^ padicValRat q x` over the primes `q ≠ p`. -/
theorem rationalPrimeUnit_factorization
    (x : ℚˣ) (p : Nat.Primes) :
    (rationalPrimeUnit x p : ℚ) =
      (((x : ℚ).num.sign : ℤ) : ℚ) *
        ∏ q ∈ (rationalPrimeFactorizationSupport x p).erase p.1,
          (q : ℚ) ^ padicValRat q (x : ℚ) := by
  let s := rationalPrimeFactorizationSupport x p
  let f : ℕ → ℚ :=
    fun q => (q : ℚ) ^ padicValRat q (x : ℚ)
  have hp_mem : p.1 ∈ s :=
    mem_rationalPrimeFactorizationSupport x p
  have hsplit :
      f p.1 * ∏ q ∈ s.erase p.1, f q =
        ∏ q ∈ s, f q :=
    Finset.mul_prod_erase s f hp_mem
  have hfactor :
      (x : ℚ) =
        (((x : ℚ).num.sign : ℤ) : ℚ) *
          ∏ q ∈ s, f q := by
    simpa only [s, f] using
      rational_factorization_over_support x p
  have hp0 : (p.1 : ℚ) ≠ 0 := by
    exact_mod_cast p.2.ne_zero
  rw [rationalPrimeUnit_val]
  calc
    (p.1 : ℚ) ^ (-padicValRat p.1 (x : ℚ)) * (x : ℚ) =
        (p.1 : ℚ) ^ (-padicValRat p.1 (x : ℚ)) *
          ((((x : ℚ).num.sign : ℤ) : ℚ) *
            ∏ q ∈ s, f q) :=
      congrArg
        (fun y : ℚ =>
          (p.1 : ℚ) ^ (-padicValRat p.1 (x : ℚ)) * y)
        hfactor
    _ =
        (p.1 : ℚ) ^ (-padicValRat p.1 (x : ℚ)) *
          ((((x : ℚ).num.sign : ℤ) : ℚ) *
            (f p.1 * ∏ q ∈ s.erase p.1, f q)) := by
      rw [hsplit]
    _ =
        (((x : ℚ).num.sign : ℤ) : ℚ) *
          (((p.1 : ℚ) ^ (-padicValRat p.1 (x : ℚ)) *
              (p.1 : ℚ) ^ padicValRat p.1 (x : ℚ)) *
            ∏ q ∈ s.erase p.1, f q) := by
      dsimp only [f]
      ring
    _ =
        (((x : ℚ).num.sign : ℤ) : ℚ) *
          ∏ q ∈ s.erase p.1, f q := by
      rw [← zpow_add₀ hp0, neg_add_cancel, zpow_zero, one_mul]
    _ =
        (((x : ℚ).num.sign : ℤ) : ℚ) *
          ∏ q ∈
              (rationalPrimeFactorizationSupport x p).erase p.1,
            (q : ℚ) ^ padicValRat q (x : ℚ) := by
      rfl

/-- A positive natural number greater than one, prime to `p`, gives a
genuine non-torsion unit of `ℤ_[p]`. -/
theorem padicNatUnit_not_isOfFinOrder_of_one_lt
    (p : Nat.Primes) (n : ℕ)
    (hcoprime : p.1.Coprime n)
    (hn : 1 < n) :
    ¬ IsOfFinOrder (padicNatUnit p n hcoprime) := by
  intro hfinite
  obtain ⟨k, hk, hpow⟩ :=
    isOfFinOrder_iff_pow_eq_one.mp hfinite
  have hval :=
    congrArg
      (fun z : ℤ_[p.1]ˣ => (z : ℤ_[p.1]))
      hpow
  have hnat : n ^ k = 1 := by
    rw [Units.val_pow_eq_pow_val,
      padicNatUnit_val] at hval
    simp at hval
    apply Nat.cast_injective (R := ℤ_[p.1])
    simpa only [Nat.cast_pow, Nat.cast_one] using hval
  exact
    (Nat.ne_of_gt
      (Nat.one_lt_pow hk.ne' hn)) hnat

/-- The rational prime-unit factorization, lifted from `ℚ` to an exact
identity of units of `ℤ_[p]`. -/
theorem padicIntUnitOfRat_rationalPrimeUnit_factorization
    (x : ℚˣ) (p : Nat.Primes) :
    padicIntUnitOfRat p (rationalPrimeUnit x p : ℚ)
        (rationalPrimeUnit x p).ne_zero
        (padicValRat_rationalPrimeUnit x p) =
      rationalSignPadicUnit x p *
        ∏ q :
            ↥((rationalPrimeFactorizationSupport x p).erase p.1),
          (padicNatUnit p q.1
              (coprime_of_mem_rationalPrimeFactorizationSupport_erase
                x p q.2)) ^
            padicValRat q.1 (x : ℚ) := by
  let : Fact p.1.Prime := ⟨p.2⟩
  have hQ :=
    congrArg (algebraMap ℚ ℚ_[p.1])
      (rationalPrimeUnit_factorization x p)
  let ι := PadicInt.Coe.ringHom (p := p.1)
  have hι_apply (z : ℤ_[p.1]) :
      ι z = (z : ℚ_[p.1]) := rfl
  have hι : Function.Injective ι :=
    fun _ _ h => PadicInt.ext h
  have hprod :
      (∏ q :
          ↥((rationalPrimeFactorizationSupport x p).erase p.1),
        ι
          (((padicNatUnit p q.1
                (coprime_of_mem_rationalPrimeFactorizationSupport_erase
                  x p q.2)) ^
              padicValRat q.1 (x : ℚ) : ℤ_[p.1]ˣ) : ℤ_[p.1])) =
        ∏ q ∈ (rationalPrimeFactorizationSupport x p).erase p.1,
          (q : ℚ_[p.1]) ^ padicValRat q (x : ℚ) := by
    calc
      _ =
          ∏ q :
              ↥((rationalPrimeFactorizationSupport x p).erase p.1),
            (q.1 : ℚ_[p.1]) ^ padicValRat q.1 (x : ℚ) := by
        apply Finset.prod_congr rfl
        intro q _
        let u : ℤ_[p.1]ˣ :=
          padicNatUnit p q.1
            (coprime_of_mem_rationalPrimeFactorizationSupport_erase
              x p q.2)
        let n : ℤ := padicValRat q.1 (x : ℚ)
        have hu : (u : ℤ_[p.1]) = q.1 := by
          dsimp only [u]
          exact
            padicNatUnit_val p q.1
              (coprime_of_mem_rationalPrimeFactorizationSupport_erase
                x p q.2)
        have huQ : ((u : ℤ_[p.1]) : ℚ_[p.1]) = (q.1 : ℚ_[p.1]) := by
          simpa only [PadicInt.coe_natCast] using
            congrArg (fun z : ℤ_[p.1] => (z : ℚ_[p.1])) hu
        let U : ℤ_[p.1]ˣ →* ℚ_[p.1]ˣ :=
          Units.map ι.toMonoidHom
        have hUQ : ((U u : ℚ_[p.1]ˣ) : ℚ_[p.1]) =
            (q.1 : ℚ_[p.1]) := by
          change ι (u : ℤ_[p.1]) = (q.1 : ℚ_[p.1])
          simpa only [hι_apply] using huQ
        change
          ((((u ^ n : ℤ_[p.1]ˣ) : ℤ_[p.1]) : ℚ_[p.1])) =
            (q.1 : ℚ_[p.1]) ^ n
        calc
          _ = ((U (u ^ n) : ℚ_[p.1]ˣ) : ℚ_[p.1]) := rfl
          _ = (((U u) ^ n : ℚ_[p.1]ˣ) : ℚ_[p.1]) :=
            congrArg (fun v : ℚ_[p.1]ˣ => (v : ℚ_[p.1]))
              (map_zpow U u n)
          _ = ((U u : ℚ_[p.1]ˣ) : ℚ_[p.1]) ^ n :=
            Units.val_zpow_eq_zpow_val (U u) n
          _ = _ := congrArg (fun z : ℚ_[p.1] => z ^ n) hUQ
      _ = _ :=
        Finset.prod_coe_sort
          ((rationalPrimeFactorizationSupport x p).erase p.1)
          (fun q : ℕ =>
            (q : ℚ_[p.1]) ^ padicValRat q (x : ℚ))
  apply Units.ext
  apply hι
  rw [Units.val_mul, Units.coe_prod]
  change
    ι
        (padicIntUnitOfRat p (rationalPrimeUnit x p : ℚ)
          (rationalPrimeUnit x p).ne_zero
          (padicValRat_rationalPrimeUnit x p) : ℤ_[p.1]) =
      ι
        ((rationalSignPadicUnit x p : ℤ_[p.1]) *
          ∏ q :
              ↥((rationalPrimeFactorizationSupport x p).erase p.1),
            (((padicNatUnit p q.1
                (coprime_of_mem_rationalPrimeFactorizationSupport_erase
                  x p q.2)) ^
              padicValRat q.1 (x : ℚ) : ℤ_[p.1]ˣ) : ℤ_[p.1]))
  rw [map_mul, map_prod]
  rw [hprod]
  simp only [hι_apply, padicIntUnitOfRat_coe,
    rationalSignPadicUnit_coe]
  change
    (algebraMap ℚ ℚ_[p.1]) (rationalPrimeUnit x p : ℚ) =
      (algebraMap ℚ ℚ_[p.1])
          (((x : ℚ).num.sign : ℤ) : ℚ) *
        ∏ q ∈ (rationalPrimeFactorizationSupport x p).erase p.1,
          (q : ℚ_[p.1]) ^ padicValRat q (x : ℚ)
  simpa only [map_mul, map_prod, map_zpow₀,
    map_natCast] using hQ

/-- The rational prime-unit factorization after reduction modulo `p ^ k`. -/
theorem padicIntUnitOfRat_rationalPrimeUnit_toZModPow
    (x : ℚˣ) (p : Nat.Primes) (k : ℕ) :
    Units.map (PadicInt.toZModPow k).toMonoidHom
        (padicIntUnitOfRat p (rationalPrimeUnit x p : ℚ)
          (rationalPrimeUnit x p).ne_zero
          (padicValRat_rationalPrimeUnit x p)) =
      Units.map (PadicInt.toZModPow k).toMonoidHom
          (rationalSignPadicUnit x p) *
        ∏ q :
            ↥((rationalPrimeFactorizationSupport x p).erase p.1),
          (ZMod.unitOfCoprime q.1
              ((coprime_of_mem_rationalPrimeFactorizationSupport_erase
                x p q.2).symm.pow_right k)) ^
            padicValRat q.1 (x : ℚ) := by
  have h :=
    congrArg
      (Units.map (PadicInt.toZModPow k).toMonoidHom)
      (padicIntUnitOfRat_rationalPrimeUnit_factorization x p)
  simpa only [map_mul, map_prod, map_zpow,
    padicNatUnit_toZModPow] using h

/-- Multiplying the reduced rational prime-unit by the inverse powers of all
prime factors away from `p` recovers the reduced sign. -/
theorem padicIntUnitOfRat_rationalPrimeUnit_mul_inverseFactors_toZModPow
    (x : ℚˣ) (p : Nat.Primes) (k : ℕ) :
    Units.map (PadicInt.toZModPow k).toMonoidHom
          (padicIntUnitOfRat p (rationalPrimeUnit x p : ℚ)
            (rationalPrimeUnit x p).ne_zero
            (padicValRat_rationalPrimeUnit x p)) *
        ∏ q :
            ↥((rationalPrimeFactorizationSupport x p).erase p.1),
          (ZMod.unitOfCoprime q.1
              ((coprime_of_mem_rationalPrimeFactorizationSupport_erase
                x p q.2).symm.pow_right k)) ^
            (-padicValRat q.1 (x : ℚ)) =
      Units.map (PadicInt.toZModPow k).toMonoidHom
        (rationalSignPadicUnit x p) := by
  rw [padicIntUnitOfRat_rationalPrimeUnit_toZModPow]
  rw [mul_assoc, ← Finset.prod_mul_distrib]
  simp

/-- Prime-valued support form of the reduced rational product formula.
The direct `p`-adic unit factor times all inverse away-from-`p` factors
is the reduced rational sign. -/
theorem
    padicIntUnitOfRat_rationalPrimeUnit_mul_primeSupportInverseFactors_toZModPow
    (x : ℚˣ) (p : Nat.Primes) (k : ℕ) :
    Units.map (PadicInt.toZModPow k).toMonoidHom
          (padicIntUnitOfRat p (rationalPrimeUnit x p : ℚ)
            (rationalPrimeUnit x p).ne_zero
            (padicValRat_rationalPrimeUnit x p)) *
        ∏ q :
            ↥((rationalPrimeFactorizationPrimeSupport x p).erase p),
          (ZMod.unitOfCoprime q.1.1
              ((coprime_of_mem_rationalPrimeFactorizationSupport_erase
                x p
                ((mem_rationalPrimeFactorizationPrimeSupport_erase_iff
                  x p q.1).1 q.2)).symm.pow_right k)) ^
            (-padicValRat q.1.1 (x : ℚ)) =
      Units.map (PadicInt.toZModPow k).toMonoidHom
        (rationalSignPadicUnit x p) := by
  have hprod :
      (∏ q :
          ↥((rationalPrimeFactorizationPrimeSupport x p).erase p),
        (ZMod.unitOfCoprime q.1.1
            ((coprime_of_mem_rationalPrimeFactorizationSupport_erase
              x p
              ((mem_rationalPrimeFactorizationPrimeSupport_erase_iff
                x p q.1).1 q.2)).symm.pow_right k)) ^
          (-padicValRat q.1.1 (x : ℚ))) =
        ∏ q :
            ↥((rationalPrimeFactorizationSupport x p).erase p.1),
          (ZMod.unitOfCoprime q.1
              ((coprime_of_mem_rationalPrimeFactorizationSupport_erase
                x p q.2).symm.pow_right k)) ^
            (-padicValRat q.1 (x : ℚ)) := by
    refine
      Fintype.prod_equiv
        (rationalPrimeFactorizationSupportEraseEquiv x p).symm
        _ _ ?_
    intro q
    rfl
  rw [hprod]
  exact
    padicIntUnitOfRat_rationalPrimeUnit_mul_inverseFactors_toZModPow
      x p k

end Reciprocity
end GlobalClassFieldTheory
end
end

section
-- module Solutions.OAIQ244_DUKE.Ramification_HilbertRamification_CompleteDVF
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.DiscreteValuationField.LocalField.residueField_charP_residueCharacteristic _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.LubinTate.Valuations.exponentialValuationSubringIsLocalRing _root_.LubinTate.compatibleGroupFamiliesGroup _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.RamificationTheory.HilbertRamification.Higher.lowerRamificationGroup.instNormal _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionFixedSubring.instIsLocalRing _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionFixedSubring.instSMulCommClass _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionResidueField.instField _root_.RamificationTheory.HilbertRamification.ValuationSubring.ramificationGroup_normal _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

/-!
# Decomposition and inertia for finite extensions of complete DVFs

For a finite separable extension of complete discretely valued fields, the
extension of the base valuation is unique.  Consequently every
base-field automorphism stabilizes the chosen target valuation ring and the
full Galois group is the decomposition group.  Reduction then gives the
finite Galois exact sequence

`1 -> I(L/K) -> Gal(L/K) -> Gal(k_L/k_K) -> 1`.

The valuation-subring definitions and their ordinary exactness are reused
from `HilbertRamification.ValuationSubring`; this file only supplies the
complete-DVF specialization and the finite-Galois surjectivity theorem.
-/

noncomputable section

open scoped Pointwise

universe u v w x

namespace RamificationTheory.HilbertRamification.CompleteDVF

open ValuationTheory.DiscreteValuationField
open ValuationTheory.DiscreteValuationField.ValuedExtension

variable {K : Type u} {L : Type w} [Field K] [Field L] [Algebra K L]
variable (base : CompleteDVF.{u, v} K) (target : CompleteDVF.{w, x} L)
variable [base.valuation.HasExtension target.valuation]

noncomputable instance decompositionGroupResidueFieldMulSemiringAction :
    MulSemiringAction
      (ValuationSubring.decompositionGroup K
        target.valuation.valuationSubring)
      target.residueField := by
  change MulSemiringAction
    (target.valuation.valuationSubring.decompositionSubgroup K)
    (IsLocalRing.ResidueField target.valuation.valuationSubring)
  infer_instance

end RamificationTheory.HilbertRamification.CompleteDVF

end
end

section
-- module Solutions.OAIQ244_DUKE.Ramification_HilbertRamification_UniqueExtensionIntegralClosure
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.DiscreteValuationField.LocalField.residueField_charP_residueCharacteristic _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.RamificationTheory.HilbertRamification.ValuationSubring.selectedResidueField.instAlgebra _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.RamificationTheory.HilbertRamification.CompleteDVF.decompositionGroupMulSemiringAction _root_.RamificationTheory.HilbertRamification.CompleteDVF.decompositionGroupResidueFieldMulSemiringAction _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen _root_.relativeAdeleRingIntermediateAlgebra _root_.relativeAdeleRingTopIntermediateAlgebra
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

/-!
# Integral closure for a unique discrete valuation extension

This file supplies the noncomplete integral-closure input used in
ramification-number theory.  For a finite Galois extension with a uniquely chosen
extension of the base discrete valuation, the Galois orbit polynomial of an
integer has coefficients in the base valuation ring.  Consequently the target
valuation ring is integral, hence finite, over the base valuation ring.

No completeness or Henselian hypothesis is used.
-/

noncomputable section

universe u v w x

namespace RamificationTheory.HilbertRamification
namespace Higher

open RamificationTheory.DiscreteValuationField.DVF
open ValuationTheory.DiscreteValuationField.Valuation
open scoped Polynomial

variable {K : Type u} {L : Type w} [Field K] [Field L] [Algebra K L]
variable {base : ValuationTheory.DiscreteValuationField.DVF.{u, v} K}
variable {target : ValuationTheory.DiscreteValuationField.DVF.{w, x} L}
variable [FiniteDimensional K L] [base.valuation.HasExtension target.valuation]
variable [IsGalois K L]

/-- Under the standing hypotheses, the target valuation ring is the actual
integral closure of the base valuation ring in `L`. -/
theorem target_valuationSubring_isIntegralClosure_of_uniqueExtension
    (huniq : HasUniqueValuationExtension.{u, v, w, x, x}
      base target) :
    IsIntegralClosure target.valuationSubring base.valuationSubring L := by
  let : Algebra.IsIntegral base.valuationSubring target.valuationSubring :=
    target_valuationSubring_isIntegral_of_uniqueExtension
      (base := base) (target := target) huniq
  exact valuationSubring_isIntegralClosure_of_isIntegral
    (L := L) base.valuation target.valuation

/-- The target valuation ring is finite over the base valuation ring.  This
is the noncomplete replacement for the completeness-based finite-module input
formerly used by the ramification-number theory monogeneity proof. -/
theorem target_valuationSubring_moduleFinite_of_uniqueExtension
    (huniq : HasUniqueValuationExtension.{u, v, w, x, x}
      base target) :
    Module.Finite base.valuationSubring target.valuationSubring := by
  let : IsNoetherianRing base.valuationSubring :=
    base.valuationSubring_isNoetherianRing
  let : IsIntegralClosure target.valuationSubring base.valuationSubring L :=
    target_valuationSubring_isIntegralClosure_of_uniqueExtension
      (base := base) (target := target) huniq
  exact moduleFinite_valuationSubring_of_isIntegralClosure
    (L := L) base.valuation target.valuation

end Higher
end RamificationTheory.HilbertRamification
end
end

section
-- module Solutions.OAIQ244_DUKE.Ramification_HilbertRamification_Monogeneity
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.HilbertRamification.Dedekind.basePrime_isPrime _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.DiscreteValuationField.Examples.Qp.padicDVRValuation_isRankOneDiscrete _root_.LocalFieldTheory.DiscreteValuationField.LocalField.residueField_charP_residueCharacteristic _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionFixedMaximalIdeal.instIsMaximal _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionResidueField.instField _root_.RamificationTheory.HilbertRamification.ValuationSubring.selectedResidueField.instAlgebra _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.RamificationTheory.HilbertRamification.CompleteDVF.decompositionGroupMulSemiringAction _root_.RamificationTheory.HilbertRamification.CompleteDVF.decompositionGroupResidueFieldMulSemiringAction _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen _root_.relativeAdeleRingIntermediateAlgebra _root_.relativeAdeleRingTopIntermediateAlgebra
attribute [-simp] _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.IsDiscreteValuationRing.addVal_ringEquiv _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.coe_valuationSubringUnitsToFieldUnits_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.multiplicativeIntegerValuationOfUniformizer_val _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.LocalFieldTheory.residueField_algebraMap_residue _root_.OAI.PrimeDegreePackets.ThetaConstruction.schwartzCM_apply _root_.RamificationTheory.HilbertRamification.Higher.dvfValuationSubringUnitAut_apply _root_.RamificationTheory.HilbertRamification.Higher.mem_dvfHigherPrincipalUnitGroup_iff _root_.RamificationTheory.HilbertRamification.Higher.mem_valuationSubringDisplacementSubalgebraOfUniqueExtension_iff _root_.ValuationTheory.DiscreteValuationField.ValuedExtension.Henselian.integralClosureValuationSubringIntegerMapOfMemOrInv_apply _root_.ValuationTheory.DiscreteValuationField.ValuedExtension.integralClosureRingEquivTargetValuationSubringOfModuleFinite_apply _root_.ValuationTheory.DiscreteValuationField.ValuedExtension.integralClosureToTargetValuationSubringOfHasExtension_apply _root_.ValuationTheory.DiscreteValuationField.ValuedExtension.integralClosureValuationSubringIntegerMapOfMemOrInv_apply _root_.ValuationTheory.DiscreteValuationField.ValuedExtension.targetValuationSubringToIntegralClosureOfModuleFinite_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

/-!
# Monogeneity over a noncomplete discretely valued field

This file proves the algebraic, noncomplete form of the monogeneity argument
used in the monogenic integral-generator theorem.  The proof uses the finite integral
closure supplied by unique extension, a primitive residue element, the
representative adjustment , and Nakayama's lemma.
-/

noncomputable section

universe u v w x

namespace RamificationTheory.HilbertRamification
open ValuationTheory.DiscreteValuationField
open ValuationTheory.DiscreteValuationField.ResidueField
namespace Higher

open scoped Polynomial

variable {K : Type u} {L : Type w} [Field K] [Field L] [Algebra K L]
variable {base : ValuationTheory.DiscreteValuationField.DVF.{u, v} K}
variable {target : ValuationTheory.DiscreteValuationField.DVF.{w, x} L}
variable [FiniteDimensional K L] [base.valuation.HasExtension target.valuation]
variable [IsGalois K L]

omit [FiniteDimensional K L] [IsGalois K L] in
/-- A local injection of DVRs maps the source maximal ideal to the power of
the target maximal ideal indexed by its ramification index. -/
theorem map_maximalIdeal_eq_pow_ramificationIdx_dvf :
    Ideal.map (algebraMap base.valuationSubring target.valuationSubring)
        base.maximalIdeal =
      target.maximalIdeal ^
        Ideal.ramificationIdx' base.maximalIdeal target.maximalIdeal := by
  let i := algebraMap base.valuationSubring target.valuationSubring
  let p := base.maximalIdeal
  let P := target.maximalIdeal
  have hi : Function.Injective i := by
    intro a b hab
    apply Subtype.ext
    apply (algebraMap K L).injective
    exact congrArg Subtype.val hab
  have hp0 : p ≠ ⊥ :=
    IsDiscreteValuationRing.not_a_field base.valuationSubring
  have hmap0 : Ideal.map i p ≠ ⊥ :=
    (Ideal.map_eq_bot_iff_of_injective hi).not.mpr hp0
  obtain ⟨pi, hpi⟩ :=
    IsDiscreteValuationRing.exists_irreducible target.valuationSubring
  obtain ⟨m, hm⟩ :=
    IsDiscreteValuationRing.ideal_eq_span_pow_irreducible hmap0 hpi
  have hmapPow : Ideal.map i p = P ^ m := by
    rw [hm, show P = IsLocalRing.maximalIdeal target.valuationSubring from rfl,
      hpi.maximalIdeal_eq, Ideal.span_singleton_pow]
  have hnot : ¬ Ideal.map i p ≤ P ^ (m + 1) := by
    rw [hmapPow]
    exact not_le_of_gt
      (Ideal.pow_succ_lt_pow
        (IsDiscreteValuationRing.not_a_field target.valuationSubring) m)
  have he : Ideal.ramificationIdx' p P = m :=
    Ideal.ramificationIdx'_spec (by rw [hmapPow]) hnot
  change Ideal.map i p = P ^ Ideal.ramificationIdx' p P
  rw [he]
  exact hmapPow

omit [FiniteDimensional K L] [IsGalois K L] in
/-- Lift a residue polynomial coefficientwise to the base valuation ring. -/
theorem exists_base_polynomial_lift_residue_eq_dvf
    (fbar : base.residueField[X]) :
    ∃ P : base.valuationSubring[X], P.map base.residueMap = fbar :=
  Polynomial.map_surjective base.residueMap base.residue_surjective fbar

omit [FiniteDimensional K L] [IsGalois K L] in
/-- A nonzero reduced derivative lifts to a unit derivative. -/
theorem polynomial_derivative_eval_isUnit_of_reduced_ne_zero_dvf
    {P : Polynomial target.valuationSubring} {a : target.valuationSubring}
    (hsimple :
      ((P.map target.residueMap).derivative).eval
        (target.residueMap a) ≠ 0) :
    IsUnit (P.derivative.eval a) := by
  apply (target.residue_ne_zero_iff_isUnit (P.derivative.eval a)).1
  calc
    target.residueMap (P.derivative.eval a) =
        (P.derivative.map target.residueMap).eval
          (target.residueMap a) := by
      exact
        (Polynomial.eval_map_apply
          (f := target.residueMap) (p := P.derivative) a).symm
    _ = ((P.map target.residueMap).derivative).eval
          (target.residueMap a) := by
      rw [Polynomial.derivative_map]
    _ ≠ 0 := hsimple

omit [FiniteDimensional K L] [IsGalois K L] in
/-- Every residue class is represented in the algebra generated by a lift of
a primitive residue element. -/
theorem exists_mem_adjoin_residue_eq_dvf
    [Algebra.IsAlgebraic base.residueField target.residueField]
    {a : target.valuationSubring}
    (hprim :
      IntermediateField.adjoin base.residueField
          ({target.residueMap a} : Set target.residueField) =
        (⊤ : IntermediateField base.residueField target.residueField))
    (zbar : target.residueField) :
    ∃ z : target.valuationSubring,
      z ∈ Algebra.adjoin base.valuationSubring
          ({a} : Set target.valuationSubring) ∧
        target.residueMap z = zbar := by
  have htop :
      Algebra.adjoin base.residueField
          ({target.residueMap a} : Set target.residueField) =
        (⊤ : Subalgebra base.residueField target.residueField) :=
    Algebra.adjoin_eq_top_of_primitive_element
      (Algebra.IsAlgebraic.isAlgebraic (target.residueMap a)) hprim
  have hz :
      zbar ∈ Algebra.adjoin base.residueField
          ({target.residueMap a} : Set target.residueField) := by
    simp [htop]
  rcases Algebra.adjoin_mem_exists_aeval
      base.residueField (target.residueMap a) hz with
    ⟨fbar, hfbar⟩
  rcases exists_base_polynomial_lift_residue_eq_dvf
      (base := base) fbar with
    ⟨P, hP⟩
  refine ⟨Polynomial.aeval a P, ?_, ?_⟩
  · exact
      Polynomial.aeval_mem_adjoin_singleton
        (R := base.valuationSubring) (p := P) a
  · rw [base_polynomial_aeval_residue_eq_dvf
      (base := base) (target := target) P a, hP]
    simpa [Polynomial.aeval_def] using hfbar

omit [FiniteDimensional K L] [IsGalois K L] in
/-- First-order approximation by the algebra generated by a primitive residue
lift. -/
theorem exists_mem_adjoin_sub_mem_maximalIdeal_dvf
    [Algebra.IsAlgebraic base.residueField target.residueField]
    {a : target.valuationSubring}
    (hprim :
      IntermediateField.adjoin base.residueField
          ({target.residueMap a} : Set target.residueField) =
        (⊤ : IntermediateField base.residueField target.residueField))
    (z : target.valuationSubring) :
    ∃ y : target.valuationSubring,
      y ∈ Algebra.adjoin base.valuationSubring
          ({a} : Set target.valuationSubring) ∧
        z - y ∈ target.maximalIdeal := by
  rcases exists_mem_adjoin_residue_eq_dvf
      (base := base) (target := target) hprim
      (target.residueMap z) with
    ⟨y, hy, hyres⟩
  refine ⟨y, hy, ?_⟩
  rw [← target.residue_eq_zero_iff, map_sub, hyres, sub_self]

omit [FiniteDimensional K L] [IsGalois K L] in
/-- Approximation to arbitrary maximal-ideal order, using the fact that the
lifted minimal polynomial evaluates to a target uniformizer. -/
theorem exists_mem_adjoin_sub_mem_maximalIdeal_pow_dvf
    [Algebra.IsAlgebraic base.residueField target.residueField]
    {P : base.valuationSubring[X]} {a : target.valuationSubring}
    (hprim :
      IntermediateField.adjoin base.residueField
          ({target.residueMap a} : Set target.residueField) =
        (⊤ : IntermediateField base.residueField target.residueField))
    (hpi :
      target.valuation.IsUniformizer
        (Polynomial.aeval a P : L))
    (n : ℕ) (z : target.valuationSubring) :
    ∃ y : target.valuationSubring,
      y ∈ Algebra.adjoin base.valuationSubring
          ({a} : Set target.valuationSubring) ∧
        z - y ∈ target.maximalIdeal ^ n := by
  let pi : target.valuationSubring := Polynomial.aeval a P
  let A : Subalgebra base.valuationSubring target.valuationSubring :=
    Algebra.adjoin base.valuationSubring ({a} : Set target.valuationSubring)
  have hpiA : pi ∈ A := by
    exact
      Polynomial.aeval_mem_adjoin_singleton
        (R := base.valuationSubring) (p := P) a
  induction n generalizing z with
  | zero =>
      refine ⟨0, A.zero_mem, ?_⟩
      simp
  | succ n ih =>
      rcases ih z with ⟨y, hyA, hdiff⟩
      have hdiv : pi ^ n ∣ z - y := by
        exact
          (target.mem_maximalIdeal_pow_iff_uniformizer_pow_dvd
            (pi := pi) (x := z - y) hpi n).1
            (by simpa [pi] using hdiff)
      rcases hdiv with ⟨b, hb⟩
      rcases exists_mem_adjoin_sub_mem_maximalIdeal_dvf
          (base := base) (target := target) (a := a) hprim b with
        ⟨c, hcA, hbc⟩
      refine ⟨y + pi ^ n * c, ?_, ?_⟩
      · exact A.add_mem hyA (A.mul_mem (A.pow_mem hpiA n) hcA)
      · have hpiPow : pi ^ n ∈ target.maximalIdeal ^ n := by
          exact
            (target.mem_maximalIdeal_pow_iff_uniformizer_pow_dvd
              (pi := pi) (x := pi ^ n) hpi n).2
              ⟨1, by rw [mul_one]⟩
        have hmul :
            pi ^ n * (b - c) ∈
              target.maximalIdeal ^ n * target.maximalIdeal :=
          Ideal.mul_mem_mul hpiPow hbc
        have hre : z - (y + pi ^ n * c) = pi ^ n * (b - c) := by
          calc
            z - (y + pi ^ n * c) = (z - y) - pi ^ n * c := by ring
            _ = pi ^ n * b - pi ^ n * c := by rw [hb]
            _ = pi ^ n * (b - c) := by ring
        rw [hre]
        simpa [pow_succ] using hmul

end Higher
end RamificationTheory.HilbertRamification
end
end

section
-- module Solutions.OAIQ244_DUKE.Ramification_HilbertRamification_RamificationNumber
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.DiscreteValuationField.Examples.Qp.padicDVRValuation_isRankOneDiscrete _root_.LocalFieldTheory.DiscreteValuationField.LocalField.residueField_charP_residueCharacteristic _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.RamificationTheory.HilbertRamification.ValuationSubring.selectedResidueField.instAlgebra _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.RamificationTheory.HilbertRamification.CompleteDVF.decompositionGroupMulSemiringAction _root_.RamificationTheory.HilbertRamification.CompleteDVF.decompositionGroupResidueFieldMulSemiringAction _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen _root_.relativeAdeleRingIntermediateAlgebra _root_.relativeAdeleRingTopIntermediateAlgebra
attribute [-simp] _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.coe_valuationSubringUnitsToFieldUnits_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.multiplicativeIntegerValuationOfUniformizer_val _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.LocalFieldTheory.residueField_algebraMap_residue _root_.OAI.PrimeDegreePackets.ThetaConstruction.schwartzCM_apply _root_.RamificationTheory.HilbertRamification.Higher.dvfValuationSubringUnitAut_apply _root_.RamificationTheory.HilbertRamification.Higher.mem_dvfHigherPrincipalUnitGroup_iff _root_.ValuationTheory.DiscreteValuationField.ValuedExtension.Henselian.integralClosureValuationSubringIntegerMapOfMemOrInv_apply _root_.ValuationTheory.DiscreteValuationField.ValuedExtension.integralClosureRingEquivTargetValuationSubringOfModuleFinite_apply _root_.ValuationTheory.DiscreteValuationField.ValuedExtension.integralClosureToTargetValuationSubringOfHasExtension_apply _root_.ValuationTheory.DiscreteValuationField.ValuedExtension.integralClosureValuationSubringIntegerMapOfMemOrInv_apply _root_.ValuationTheory.DiscreteValuationField.ValuedExtension.targetValuationSubringToIntegralClosureOfModuleFinite_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

/-!
# Ramification numbers for a general discretely valued field

This file gives the noncomplete version of the ramification number used in
ramification-number theory.  Under the stated unique-extension and
separable-residue hypotheses, the monogenic integral-generator theorem supplies
an integral generator.  We choose that generator internally, so downstream
statements do not carry a generator hypothesis.
-/

noncomputable section

universe u v w x

namespace RamificationTheory.HilbertRamification
namespace Higher


variable {K : Type u} {L : Type w} [Field K] [Field L] [Algebra K L]
variable {base : ValuationTheory.DiscreteValuationField.DVF.{u, v} K}
variable {target : ValuationTheory.DiscreteValuationField.DVF.{w, x} L}
variable [base.valuation.HasExtension target.valuation]

/-- Ramification number attached to an integral element, before choosing the
integral generator. -/
def ramificationNumberOfUniqueExtension
    (huniq :
      RamificationTheory.DiscreteValuationField.DVF.HasUniqueValuationExtension.{u, v, w, x, x}
        base target)
    (a : target.valuationSubring) (sigma : Gal(L/K)) : ℕ∞ :=
  IsDiscreteValuationRing.addVal target.valuationSubring
    (valuationSubringAutOfUniqueExtension
      (base := base) (target := target) huniq sigma a - a)

/-- States the theorem `ramificationNumberOfUniqueExtension_one`. -/
@[simp] theorem ramificationNumberOfUniqueExtension_one
    (huniq :
      RamificationTheory.DiscreteValuationField.DVF.HasUniqueValuationExtension.{u, v, w, x, x}
        base target)
    (a : target.valuationSubring) :
    ramificationNumberOfUniqueExtension
      (base := base) (target := target) huniq a 1 = ⊤ := by
  simp [ramificationNumberOfUniqueExtension]

/-- States the theorem `natCast_le_ramificationNumberOfUniqueExtension_iff`. -/
theorem natCast_le_ramificationNumberOfUniqueExtension_iff
    (huniq :
      RamificationTheory.DiscreteValuationField.DVF.HasUniqueValuationExtension.{u, v, w, x, x}
        base target)
    (a : target.valuationSubring) (sigma : Gal(L/K)) (n : ℕ) :
    (n : ℕ∞) ≤ ramificationNumberOfUniqueExtension
        (base := base) (target := target) huniq a sigma ↔
      valuationSubringAutOfUniqueExtension
          (base := base) (target := target) huniq sigma a - a ∈
        target.maximalIdeal ^ n := by
  exact (IsDiscreteValuationRing.mem_maximalIdeal_pow_iff_addVal_ge
    (valuationSubringAutOfUniqueExtension
      (base := base) (target := target) huniq sigma a - a) n).symm

/-- The ramification number is independent of the monogenic generator. -/
theorem ramificationNumberOfUniqueExtension_eq_of_adjoin_eq_top
    (huniq :
      RamificationTheory.DiscreteValuationField.DVF.HasUniqueValuationExtension.{u, v, w, x, x}
        base target)
    {a b : target.valuationSubring}
    (ha : Algebra.adjoin base.valuationSubring
      ({a} : Set target.valuationSubring) = ⊤)
    (hb : Algebra.adjoin base.valuationSubring
      ({b} : Set target.valuationSubring) = ⊤)
    (sigma : Gal(L/K)) :
    ramificationNumberOfUniqueExtension
        (base := base) (target := target) huniq a sigma =
      ramificationNumberOfUniqueExtension
        (base := base) (target := target) huniq b sigma := by
  apply le_antisymm
  · rw [← ENat.forall_natCast_le_iff_le]
    intro n han
    rw [natCast_le_ramificationNumberOfUniqueExtension_iff] at han ⊢
    exact valuationSubringAutOfUniqueExtension_sub_mem_of_mem_adjoin
      (base := base) (target := target) huniq han (by rw [ha]; simp)
  · rw [← ENat.forall_natCast_le_iff_le]
    intro n hbn
    rw [natCast_le_ramificationNumberOfUniqueExtension_iff] at hbn ⊢
    exact valuationSubringAutOfUniqueExtension_sub_mem_of_mem_adjoin
      (base := base) (target := target) huniq hbn (by rw [hb]; simp)

end Higher
end RamificationTheory.HilbertRamification
end
end

section
-- module Solutions.OAIQ244_DUKE.Ramification_HilbertRamification_UniformizerGradedHom
attribute [-instance] _root_.ClassFormation.DegreeData.GaloisSubextension.extensionSubgroup_normalInstance _root_.ClassFormation.FiniteCyclicSubextension.instNormalSubtypeMemSubgroupFieldExtensionSubgroupField _root_.ClassFormation.FiniteGaloisSubextension.extensionSubgroup_normalInstance _root_.ClassFormation.FiniteGaloisSubextension.extensionSubgroup_over_intermediate_normalInstance _root_.ClassFormation.FiniteGaloisSubextension.intermediateField_normalInstance _root_.ClassFormation.FiniteUnramifiedCyclicExtension.instNormalSubtypeMemSubgroupFieldExtensionSubgroupField _root_.ClassFormation.conjugateExtension_normal _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.HilbertRamification.Dedekind.inertiaSubgroupOfDecomposition_normal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalClassFieldTheory.extensionSubgroupBase_normal _root_.LocalClassFieldTheory.finiteGaloisExtensionSubgroupOfEmbedding_normal _root_.LocalFieldTheory.DiscreteValuationField.Examples.Qp.padicDVRValuation_isRankOneDiscrete _root_.LocalFieldTheory.DiscreteValuationField.LocalField.residueField_charP_residueCharacteristic _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.LubinTate.compatibleGroupFamiliesCommGroup _root_.LubinTate.compatibleGroupFamiliesGroup _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.RamificationTheory.HilbertRamification.ValuationSubring.inertiaGroup_normal _root_.RamificationTheory.HilbertRamification.ValuationSubring.ramificationGroupInInertiaAut_normal _root_.RamificationTheory.HilbertRamification.ValuationSubring.selectedResidueField.instAlgebra _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.CyclicCohomology.binaryCoefficientFamilyCommGroup _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.RamificationTheory.HilbertRamification.CompleteDVF.decompositionGroupMulSemiringAction _root_.RamificationTheory.HilbertRamification.CompleteDVF.decompositionGroupResidueFieldMulSemiringAction _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen _root_.relativeAdeleRingIntermediateAlgebra _root_.relativeAdeleRingTopIntermediateAlgebra
attribute [-simp] _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.IsDiscreteValuationRing.addVal_ringEquiv _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.coe_valuationSubringUnitsToFieldUnits_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.multiplicativeIntegerValuationOfUniformizer_val _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.LocalFieldTheory.residueField_algebraMap_residue _root_.OAI.PrimeDegreePackets.ThetaConstruction.schwartzCM_apply _root_.RamificationTheory.HilbertRamification.Higher.mem_valuationSubringDisplacementSubalgebraOfUniqueExtension_iff _root_.RamificationTheory.HilbertRamification.Higher.ramificationNumberOfUniqueExtension_one _root_.ValuationTheory.DiscreteValuationField.ValuedExtension.Henselian.integralClosureValuationSubringIntegerMapOfMemOrInv_apply _root_.ValuationTheory.DiscreteValuationField.ValuedExtension.integralClosureRingEquivTargetValuationSubringOfModuleFinite_apply _root_.ValuationTheory.DiscreteValuationField.ValuedExtension.integralClosureToTargetValuationSubringOfHasExtension_apply _root_.ValuationTheory.DiscreteValuationField.ValuedExtension.integralClosureValuationSubringIntegerMapOfMemOrInv_apply _root_.ValuationTheory.DiscreteValuationField.ValuedExtension.targetValuationSubringToIntegralClosureOfModuleFinite_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

/-!
# First ramification-quotient homomorphism over general DVFs

This file constructs the graded uniformizer homomorphism under the standing
hypotheses of ramification-number theory.  Completeness is not assumed.  The
injectivity statement includes the necessary separability hypothesis on the
residue extension; the unconditional printed assertion is false for fiercely
ramified extensions.
-/

noncomputable section

universe u v w x

namespace RamificationTheory.HilbertRamification
namespace Higher

open ValuationTheory.DiscreteValuationField.ResidueField


variable {K : Type u} {L : Type w} [Field K] [Field L] [Algebra K L]
variable {base : ValuationTheory.DiscreteValuationField.DVF.{u, v} K}
variable {target : ValuationTheory.DiscreteValuationField.DVF.{w, x} L}
variable [FiniteDimensional K L] [base.valuation.HasExtension target.valuation]
variable [IsGalois K L]

omit [FiniteDimensional K L] [IsGalois K L] in
/-- Every Galois conjugate of a target uniformizer differs from it by a
valuation-ring unit. -/
theorem exists_dvfUniformizerQuotientUnit
    (huniq :
      RamificationTheory.DiscreteValuationField.DVF.HasUniqueValuationExtension.{u, v, w, x, x}
        base target)
    {pi : target.valuationSubring}
    (hpi : target.valuation.IsUniformizer (pi : L))
    (sigma : Gal(L/K)) :
    ∃ a : target.valuationSubringˣ,
      valuationSubringAutOfUniqueExtension
          (base := base) (target := target) huniq sigma pi =
        (a : target.valuationSubring) * pi := by
  let sigmaPi :=
    valuationSubringAutOfUniqueExtension
      (base := base) (target := target) huniq sigma pi
  have hpiMem : pi ∈ target.maximalIdeal :=
    target.uniformizer_mem_maximalIdeal hpi
  have hpiDvd : pi ∣ sigmaPi := by
    have hsigmaMem : sigmaPi ∈ target.maximalIdeal ^ 1 := by
      exact
        (valuationSubringAutOfUniqueExtension_mem_maximalIdeal_pow_iff
          (base := base) (target := target) huniq sigma 1 pi).2
          (by simpa using hpiMem)
    rw [← Ideal.mem_span_singleton]
    have hsigmaMem' : sigmaPi ∈ target.maximalIdeal := by
      simpa using hsigmaMem
    rw [target.maximalIdeal_eq_span_uniformizer hpi] at hsigmaMem'
    exact hsigmaMem'
  have hsigmaDvd : sigmaPi ∣ pi := by
    have hinvMem :
        valuationSubringAutOfUniqueExtension
            (base := base) (target := target) huniq sigma⁻¹ pi ∈
          target.maximalIdeal ^ 1 :=
      (valuationSubringAutOfUniqueExtension_mem_maximalIdeal_pow_iff
        (base := base) (target := target) huniq sigma⁻¹ 1 pi).2
        (by simpa using hpiMem)
    have hdiv :
        pi ∣ valuationSubringAutOfUniqueExtension
            (base := base) (target := target) huniq sigma⁻¹ pi := by
      rw [← Ideal.mem_span_singleton]
      have hinvMem' :
          valuationSubringAutOfUniqueExtension
              (base := base) (target := target) huniq sigma⁻¹ pi ∈
            target.maximalIdeal := by
        simpa using hinvMem
      rw [target.maximalIdeal_eq_span_uniformizer hpi] at hinvMem'
      exact hinvMem'
    rcases hdiv with ⟨b, hb⟩
    refine
      ⟨valuationSubringAutOfUniqueExtension
        (base := base) (target := target) huniq sigma b, ?_⟩
    calc
      pi =
          valuationSubringAutOfUniqueExtension
            (base := base) (target := target) huniq sigma
            (valuationSubringAutOfUniqueExtension
              (base := base) (target := target) huniq sigma⁻¹ pi) := by
        rw [valuationSubringAutOfUniqueExtension_apply_inv_apply]
      _ = valuationSubringAutOfUniqueExtension
            (base := base) (target := target) huniq sigma (pi * b) := by
        rw [hb]
      _ = sigmaPi *
          valuationSubringAutOfUniqueExtension
            (base := base) (target := target) huniq sigma b := by
        simp [sigmaPi]
  rcases hpiDvd with ⟨a, ha⟩
  rcases hsigmaDvd with ⟨b, hb⟩
  have hpi0 : pi ≠ 0 := by
    intro hzero
    have hzeroL :=
      congrArg (fun z : target.valuationSubring => (z : L)) hzero
    exact hpi.ne_zero (by simpa using hzeroL)
  have hab : a * b = 1 := by
    apply mul_left_cancel₀ hpi0
    calc
      pi * (a * b) = (pi * a) * b := by rw [mul_assoc]
      _ = sigmaPi * b := by rw [← ha]
      _ = pi := hb.symm
      _ = pi * 1 := by rw [mul_one]
  refine ⟨⟨a, b, hab, ?_⟩, ?_⟩
  · simpa [mul_comm] using hab
  · change sigmaPi = a * pi
    simpa [mul_comm] using ha

/-- The chosen unit sigma(pi)/pi. -/
noncomputable def dvfUniformizerQuotientUnit
    (huniq :
      RamificationTheory.DiscreteValuationField.DVF.HasUniqueValuationExtension.{u, v, w, x, x}
        base target)
    (pi : target.valuationSubring)
    (hpi : target.valuation.IsUniformizer (pi : L))
    (sigma : Gal(L/K)) : target.valuationSubringˣ :=
  Classical.choose
    (exists_dvfUniformizerQuotientUnit
      (base := base) (target := target) huniq hpi sigma)

omit [FiniteDimensional K L] [IsGalois K L] in
/-- States the theorem `dvfUniformizerQuotientUnit_mul_uniformizer`. -/
@[simp] theorem dvfUniformizerQuotientUnit_mul_uniformizer
    (huniq :
      RamificationTheory.DiscreteValuationField.DVF.HasUniqueValuationExtension.{u, v, w, x, x}
        base target)
    (pi : target.valuationSubring)
    (hpi : target.valuation.IsUniformizer (pi : L))
    (sigma : Gal(L/K)) :
    valuationSubringAutOfUniqueExtension
        (base := base) (target := target) huniq sigma pi =
      (dvfUniformizerQuotientUnit
        (base := base) (target := target) huniq pi hpi sigma :
          target.valuationSubring) * pi :=
  Classical.choose_spec
    (exists_dvfUniformizerQuotientUnit
      (base := base) (target := target) huniq hpi sigma)

omit [FiniteDimensional K L] [IsGalois K L] in
/-- Exact cocycle identity for the chosen quotient units. -/
theorem dvfUniformizerQuotientUnit_mul_eq
    (huniq :
      RamificationTheory.DiscreteValuationField.DVF.HasUniqueValuationExtension.{u, v, w, x, x}
        base target)
    (pi : target.valuationSubring)
    (hpi : target.valuation.IsUniformizer (pi : L))
    (sigma tau : Gal(L/K)) :
    dvfUniformizerQuotientUnit
        (base := base) (target := target) huniq pi hpi (sigma * tau) =
      dvfValuationSubringUnitAut
          (base := base) (target := target) huniq sigma
          (dvfUniformizerQuotientUnit
            (base := base) (target := target) huniq pi hpi tau) *
        dvfUniformizerQuotientUnit
          (base := base) (target := target) huniq pi hpi sigma := by
  apply Units.ext
  have hpi0 : pi ≠ 0 := by
    intro hzero
    have hzeroL :=
      congrArg (fun z : target.valuationSubring => (z : L)) hzero
    exact hpi.ne_zero (by simpa using hzeroL)
  apply mul_right_cancel₀ hpi0
  calc
    ((dvfUniformizerQuotientUnit
        (base := base) (target := target) huniq pi hpi (sigma * tau) :
          target.valuationSubringˣ) : target.valuationSubring) * pi =
        valuationSubringAutOfUniqueExtension
          (base := base) (target := target) huniq (sigma * tau) pi := by
      rw [dvfUniformizerQuotientUnit_mul_uniformizer
        (base := base) (target := target) huniq pi hpi (sigma * tau)]
    _ = valuationSubringAutOfUniqueExtension
          (base := base) (target := target) huniq sigma
          (valuationSubringAutOfUniqueExtension
            (base := base) (target := target) huniq tau pi) := by
      rw [valuationSubringAutOfUniqueExtension_mul_apply]
    _ = valuationSubringAutOfUniqueExtension
          (base := base) (target := target) huniq sigma
          ((dvfUniformizerQuotientUnit
              (base := base) (target := target) huniq pi hpi tau :
                target.valuationSubringˣ) : target.valuationSubring) *
            valuationSubringAutOfUniqueExtension
              (base := base) (target := target) huniq sigma pi := by
      rw [dvfUniformizerQuotientUnit_mul_uniformizer
        (base := base) (target := target) huniq pi hpi tau]
      simp
    _ =
        ((dvfValuationSubringUnitAut
              (base := base) (target := target) huniq sigma
              (dvfUniformizerQuotientUnit
                (base := base) (target := target) huniq pi hpi tau) *
            dvfUniformizerQuotientUnit
              (base := base) (target := target) huniq pi hpi sigma :
            target.valuationSubringˣ) : target.valuationSubring) * pi := by
      rw [dvfUniformizerQuotientUnit_mul_uniformizer
        (base := base) (target := target) huniq pi hpi sigma]
      simp [mul_assoc]

omit [FiniteDimensional K L] [IsGalois K L] in
/-- Quotient-unit membership is equivalent to one-deeper displacement of the
uniformizer. -/
theorem dvfUniformizerQuotientUnit_mem_iff_uniformizer_sub_mem
    (huniq :
      RamificationTheory.DiscreteValuationField.DVF.HasUniqueValuationExtension.{u, v, w, x, x}
        base target)
    {pi : target.valuationSubring}
    (hpi : target.valuation.IsUniformizer (pi : L))
    (n : ℕ) (sigma : Gal(L/K)) :
    dvfUniformizerQuotientUnit
        (base := base) (target := target) huniq pi hpi sigma ∈
      dvfHigherPrincipalUnitGroup target n ↔
      valuationSubringAutOfUniqueExtension
          (base := base) (target := target) huniq sigma pi - pi ∈
        target.maximalIdeal ^ (n + 1) := by
  let a : target.valuationSubring :=
    (dvfUniformizerQuotientUnit
      (base := base) (target := target) huniq pi hpi sigma :
        target.valuationSubring)
  change a - 1 ∈ target.maximalIdeal ^ n ↔ _
  have hmul :
      (a - 1) * pi =
        valuationSubringAutOfUniqueExtension
            (base := base) (target := target) huniq sigma pi - pi := by
    dsimp [a]
    rw [dvfUniformizerQuotientUnit_mul_uniformizer
      (base := base) (target := target) huniq pi hpi sigma]
    ring
  constructor
  · intro ha
    rw [← hmul]
    rw [target.mem_maximalIdeal_pow_iff_uniformizer_pow_dvd
      (pi := pi) (x := (a - 1) * pi) hpi (n + 1)]
    rw [target.mem_maximalIdeal_pow_iff_uniformizer_pow_dvd
      (pi := pi) (x := a - 1) hpi n] at ha
    rcases ha with ⟨b, hb⟩
    refine ⟨b, ?_⟩
    calc
      (a - 1) * pi = (pi ^ n * b) * pi := by rw [hb]
      _ = pi ^ (n + 1) * b := by rw [pow_succ]; ring
  · intro hdiff
    rw [← hmul] at hdiff
    rw [target.mem_maximalIdeal_pow_iff_uniformizer_pow_dvd
      (pi := pi) (x := (a - 1) * pi) hpi (n + 1)] at hdiff
    rw [target.mem_maximalIdeal_pow_iff_uniformizer_pow_dvd
      (pi := pi) (x := a - 1) hpi n]
    rcases hdiff with ⟨b, hb⟩
    refine ⟨b, ?_⟩
    have hpi0 : pi ≠ 0 := by
      intro hzero
      have hzeroL :=
        congrArg (fun z : target.valuationSubring => (z : L)) hzero
      exact hpi.ne_zero (by simpa using hzeroL)
    apply mul_right_cancel₀ hpi0
    calc
      (a - 1) * pi = pi ^ (n + 1) * b := hb
      _ = (pi ^ n * b) * pi := by rw [pow_succ]; ring

omit [FiniteDimensional K L] [IsGalois K L] in
/-- If sigma lies in G_n, then sigma(pi)/pi lies in U_L^n. -/
theorem dvfUniformizerQuotientUnit_mem_of_mem_lowerRamificationGroup
    (huniq :
      RamificationTheory.DiscreteValuationField.DVF.HasUniqueValuationExtension.{u, v, w, x, x}
        base target)
    {pi : target.valuationSubring}
    (hpi : target.valuation.IsUniformizer (pi : L))
    {n : ℕ} {sigma : Gal(L/K)}
    (hsigma :
      sigma ∈ lowerRamificationGroup
        (base := base) (target := target) huniq (n : ℝ)) :
    dvfUniformizerQuotientUnit
        (base := base) (target := target) huniq pi hpi sigma ∈
      dvfHigherPrincipalUnitGroup target n := by
  exact
    (dvfUniformizerQuotientUnit_mem_iff_uniformizer_sub_mem
      (base := base) (target := target) huniq hpi n sigma).2
      ((mem_lowerRamificationGroup_nat_iff
        (base := base) (target := target) huniq n sigma).1 hsigma pi)

omit [FiniteDimensional K L] [IsGalois K L] in
/-- A G_n automorphism acts trivially on every unit modulo U_L^(n+1). -/
theorem dvfValuationSubringUnitAut_div_mem_succ
    (huniq :
      RamificationTheory.DiscreteValuationField.DVF.HasUniqueValuationExtension.{u, v, w, x, x}
        base target)
    {n : ℕ} {sigma : Gal(L/K)}
    (hsigma :
      sigma ∈ lowerRamificationGroup
        (base := base) (target := target) huniq (n : ℝ))
    (a : target.valuationSubringˣ) :
    dvfValuationSubringUnitAut
        (base := base) (target := target) huniq sigma a / a ∈
      dvfHigherPrincipalUnitGroup target (n + 1) := by
  rw [mem_dvfHigherPrincipalUnitGroup_iff]
  have hdiff :
      valuationSubringAutOfUniqueExtension
          (base := base) (target := target) huniq sigma
          (a : target.valuationSubring) -
        (a : target.valuationSubring) ∈
      target.maximalIdeal ^ (n + 1) :=
    (mem_lowerRamificationGroup_nat_iff
      (base := base) (target := target) huniq n sigma).1 hsigma a
  have hre :
      ((dvfValuationSubringUnitAut
          (base := base) (target := target) huniq sigma a / a :
            target.valuationSubringˣ) : target.valuationSubring) - 1 =
        ((a⁻¹ : target.valuationSubringˣ) : target.valuationSubring) *
          (valuationSubringAutOfUniqueExtension
              (base := base) (target := target) huniq sigma
              (a : target.valuationSubring) -
            (a : target.valuationSubring)) := by
    simp [div_eq_mul_inv]
    have hinv :
        ((a⁻¹ : target.valuationSubringˣ) : target.valuationSubring) *
          (a : target.valuationSubring) = 1 := by
      exact_mod_cast Units.inv_mul a
    rw [mul_sub, hinv]
    ring
  rw [hre]
  exact Ideal.mul_mem_left _ _ hdiff

/-- Representative homomorphism from G_n to the literal principal-unit
graded quotient. -/
noncomputable def dvfUniformizerRepresentativeHom
    (huniq :
      RamificationTheory.DiscreteValuationField.DVF.HasUniqueValuationExtension.{u, v, w, x, x}
        base target)
    (pi : target.valuationSubring)
    (hpi : target.valuation.IsUniformizer (pi : L))
    (n : ℕ) :
    lowerRamificationGroup
        (base := base) (target := target) huniq (n : ℝ) →*
      dvfPrincipalUnitGradedPiece target n where
  toFun sigma :=
    QuotientGroup.mk'
      ((dvfHigherPrincipalUnitGroup target (n + 1)).subgroupOf
        (dvfHigherPrincipalUnitGroup target n))
      ⟨dvfUniformizerQuotientUnit
          (base := base) (target := target) huniq pi hpi
          (sigma : Gal(L/K)),
        dvfUniformizerQuotientUnit_mem_of_mem_lowerRamificationGroup
          (base := base) (target := target) huniq hpi sigma.property⟩
  map_one' := by
    let oneN :
        lowerRamificationGroup
          (base := base) (target := target) huniq (n : ℝ) := 1
    let u1 : dvfHigherPrincipalUnitGroup target n :=
      ⟨dvfUniformizerQuotientUnit
          (base := base) (target := target) huniq pi hpi 1,
        dvfUniformizerQuotientUnit_mem_of_mem_lowerRamificationGroup
          (base := base) (target := target) huniq hpi oneN.property⟩
    change
      QuotientGroup.mk'
          ((dvfHigherPrincipalUnitGroup target (n + 1)).subgroupOf
            (dvfHigherPrincipalUnitGroup target n)) u1 = 1
    apply
      (QuotientGroup.eq_one_iff
        (N := (dvfHigherPrincipalUnitGroup target (n + 1)).subgroupOf
          (dvfHigherPrincipalUnitGroup target n)) u1).2
    change
      dvfUniformizerQuotientUnit
          (base := base) (target := target) huniq pi hpi 1 ∈
        dvfHigherPrincipalUnitGroup target (n + 1)
    exact
      dvfUniformizerQuotientUnit_mem_of_mem_lowerRamificationGroup
        (base := base) (target := target) huniq hpi
        (lowerRamificationGroup
          (base := base) (target := target) huniq
          ((n + 1 : ℕ) : ℝ)).one_mem
  map_mul' := by
    intro sigma tau
    apply
      (QuotientGroup.eq_iff_div_mem
        (N := (dvfHigherPrincipalUnitGroup target (n + 1)).subgroupOf
          (dvfHigherPrincipalUnitGroup target n))).2
    change
      dvfUniformizerQuotientUnit
            (base := base) (target := target) huniq pi hpi
            ((sigma : Gal(L/K)) * (tau : Gal(L/K))) /
          (dvfUniformizerQuotientUnit
              (base := base) (target := target) huniq pi hpi
              (sigma : Gal(L/K)) *
            dvfUniformizerQuotientUnit
              (base := base) (target := target) huniq pi hpi
              (tau : Gal(L/K))) ∈
        dvfHigherPrincipalUnitGroup target (n + 1)
    have hact :=
      dvfValuationSubringUnitAut_div_mem_succ
        (base := base) (target := target) huniq sigma.property
        (dvfUniformizerQuotientUnit
          (base := base) (target := target) huniq pi hpi
          (tau : Gal(L/K)))
    rw [dvfUniformizerQuotientUnit_mul_eq
      (base := base) (target := target) huniq pi hpi
      (sigma : Gal(L/K)) (tau : Gal(L/K))]
    simpa [div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm] using hact

omit [FiniteDimensional K L] [IsGalois K L] in
/-- States the theorem `dvfUniformizerRepresentativeHom_apply`. -/
@[simp] theorem dvfUniformizerRepresentativeHom_apply
    (huniq :
      RamificationTheory.DiscreteValuationField.DVF.HasUniqueValuationExtension.{u, v, w, x, x}
        base target)
    (pi : target.valuationSubring)
    (hpi : target.valuation.IsUniformizer (pi : L))
    (n : ℕ)
    (sigma :
      lowerRamificationGroup
        (base := base) (target := target) huniq (n : ℝ)) :
    dvfUniformizerRepresentativeHom
        (base := base) (target := target) huniq pi hpi n sigma =
      QuotientGroup.mk'
        ((dvfHigherPrincipalUnitGroup target (n + 1)).subgroupOf
          (dvfHigherPrincipalUnitGroup target n))
        ⟨dvfUniformizerQuotientUnit
            (base := base) (target := target) huniq pi hpi
            (sigma : Gal(L/K)),
          dvfUniformizerQuotientUnit_mem_of_mem_lowerRamificationGroup
            (base := base) (target := target) huniq hpi sigma.property⟩ :=
  rfl

/-- The first ramification-quotient homomorphism: the uniformizer quotient descends
to G_n/G_(n+1) with values in U_L^n/U_L^(n+1). -/
noncomputable def uniformizerGradedHom
    (huniq :
      RamificationTheory.DiscreteValuationField.DVF.HasUniqueValuationExtension.{u, v, w, x, x}
        base target)
    (pi : target.valuationSubring)
    (hpi : target.valuation.IsUniformizer (pi : L))
    (n : ℕ) :
    lowerRamificationGradedPiece (base := base) (target := target) huniq n →*
      dvfPrincipalUnitGradedPiece target n :=
  QuotientGroup.lift
    ((lowerRamificationGroup
      (base := base) (target := target) huniq
      ((n + 1 : ℕ) : ℝ)).subgroupOf
      (lowerRamificationGroup
        (base := base) (target := target) huniq (n : ℝ)))
    (dvfUniformizerRepresentativeHom
      (base := base) (target := target) huniq pi hpi n)
    (by
      intro sigma hsigma
      rw [MonoidHom.mem_ker]
      change
        QuotientGroup.mk'
            ((dvfHigherPrincipalUnitGroup target (n + 1)).subgroupOf
              (dvfHigherPrincipalUnitGroup target n))
            ⟨dvfUniformizerQuotientUnit
                (base := base) (target := target) huniq pi hpi
                (sigma : Gal(L/K)),
              dvfUniformizerQuotientUnit_mem_of_mem_lowerRamificationGroup
                (base := base) (target := target) huniq hpi sigma.property⟩ =
          1
      apply
        (QuotientGroup.eq_one_iff
          (N := (dvfHigherPrincipalUnitGroup target (n + 1)).subgroupOf
            (dvfHigherPrincipalUnitGroup target n))
          ⟨dvfUniformizerQuotientUnit
              (base := base) (target := target) huniq pi hpi
              (sigma : Gal(L/K)),
            dvfUniformizerQuotientUnit_mem_of_mem_lowerRamificationGroup
              (base := base) (target := target) huniq hpi sigma.property⟩).2
      change
        dvfUniformizerQuotientUnit
            (base := base) (target := target) huniq pi hpi
            (sigma : Gal(L/K)) ∈
          dvfHigherPrincipalUnitGroup target (n + 1)
      exact
        dvfUniformizerQuotientUnit_mem_of_mem_lowerRamificationGroup
          (base := base) (target := target) huniq hpi
          (by simpa [Subgroup.mem_subgroupOf] using hsigma))

omit [FiniteDimensional K L] [IsGalois K L] in
/-- States the theorem `uniformizerGradedHom_mk`. -/
@[simp] theorem uniformizerGradedHom_mk
    (huniq :
      RamificationTheory.DiscreteValuationField.DVF.HasUniqueValuationExtension.{u, v, w, x, x}
        base target)
    (pi : target.valuationSubring)
    (hpi : target.valuation.IsUniformizer (pi : L))
    (n : ℕ)
    (sigma :
      lowerRamificationGroup
        (base := base) (target := target) huniq (n : ℝ)) :
    uniformizerGradedHom
        (base := base) (target := target) huniq pi hpi n
        (QuotientGroup.mk'
          ((lowerRamificationGroup
            (base := base) (target := target) huniq
            ((n + 1 : ℕ) : ℝ)).subgroupOf
            (lowerRamificationGroup
              (base := base) (target := target) huniq (n : ℝ))) sigma) =
      dvfUniformizerRepresentativeHom
        (base := base) (target := target) huniq pi hpi n sigma :=
  rfl

/-- The unique-extension ring automorphism as an algebra automorphism over
the base valuation ring. -/
def valuationSubringAlgEquivOfUniqueExtension
    (huniq :
      RamificationTheory.DiscreteValuationField.DVF.HasUniqueValuationExtension.{u, v, w, x, x}
        base target)
    (sigma : Gal(L/K)) :
    target.valuationSubring ≃ₐ[base.valuationSubring]
      target.valuationSubring :=
  { valuationSubringAutOfUniqueExtension
      (base := base) (target := target) huniq sigma with
    commutes' := by
      intro a
      apply Subtype.ext
      simp [valuationSubringAutOfUniqueExtension] }

end Higher
end RamificationTheory.HilbertRamification
end
end

section
-- module Solutions.OAIQ244_DUKE.LocalField_DiscreteValuationField_PadicValuationComparison
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionResidueField.instField _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

/-!
# Comparison of the chosen and canonical valuations on the p-adic field

The concrete local-field package on `ℚ_[p]` uses the DVR valuation obtained
from `ℤ_[p]`, whereas mathlib's nonarchimedean-local-field API uses
`ValuativeRel.valuation ℚ_[p]`.  This file proves that these are equivalent
valuations and makes the comparison usable when transporting valuation
extensions.
-/

noncomputable section

open scoped ValuativeRel

namespace LocalFieldTheory
namespace DiscreteValuationField
namespace Examples
namespace Qp

universe u v

/-- The DVR valuation on `ℚ_[p]` obtained from `ℤ_[p]` is equivalent to the
canonical valuation attached to the p-adic valuative relation. -/
theorem padicDVRValuation_isEquiv_valuativeRelValuation
    (p : ℕ) [Fact p.Prime] :
    (padicDVRValuation p).IsEquiv
      (ValuativeRel.valuation ℚ_[p]) := by
  apply _root_.Valuation.isEquiv_of_val_le_one
  intro a
  have hcanonical :
      ValuativeRel.valuation ℚ_[p] a ≤ 1 ↔ ‖a‖ ≤ 1 := by
    simpa only [_root_.Valuation.mem_integer_iff] using
      LocalFieldTheory.Padic.integer_mem_iff_norm_le_one p a
  exact
    (LocalFieldTheory.DiscreteValuationField.LocalField.padicDVRValuation_le_one_iff_norm_le_one
      p a).trans
      hcanonical.symm

end Qp
end Examples
end DiscreteValuationField
end LocalFieldTheory
end
end

section
-- module Solutions.OAIQ244_DUKE.GlobalClassFieldTheory_Reciprocity_InfinitePlaceArtin
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable
attribute [-simp] _root_.GlobalClassFieldTheory.Reciprocity.infinitePlaceComplexificationOverfieldEmbedding_coe _root_.IsDiscreteValuationRing.addVal_ringEquiv _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.OAI.PrimeDegreePackets.ThetaConstruction.schwartzCM_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

/-!
# Archimedean Artin homomorphisms

At a ramified infinite place, the local extension is complex over
real.  Its Artin homomorphism sends the sign of a real unit to the
corresponding complex-conjugation element of the decomposition group.
At an unramified infinite place the decomposition group, and hence the
local homomorphism, is trivial.
-/

open scoped BigOperators Classical IsMulCommutative NumberField
  NumberField.LiesOver
open NumberField IsDedekindDomain
open IdeleGroup RelativeIdeleGroup

noncomputable section

namespace GlobalClassFieldTheory
namespace Reciprocity

open HilbertRamification
open LocalFieldTheory

variable {K L : Type}
    [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]

section Galois

variable [IsGalois K L]

omit [NumberField K] [NumberField L] in
/-- At a ramified real place, the actual chosen local Artin symbol of
negative one is complex conjugation along the chosen infinite place
upstairs.  The statement exposes the intrinsic property of the Artin
value, without exposing the auxiliary conjugation chosen in its
construction. -/
theorem chosenInfinitePlaceArtinMonoidHom_neg_one_isConj_of_ramified
    (v : InfinitePlace K)
    (hRamified :
      (chosenInfinitePlaceAbove (L := L) v).IsRamified K) :
    NumberField.ComplexEmbedding.IsConj
      (InfinitePlace.embedding
        (chosenInfinitePlaceAbove (L := L) v))
      (chosenInfinitePlaceArtinMonoidHom
        (K := K) (L := L) v (-1 : v.Completionˣ)) := by
  let w := chosenInfinitePlaceAbove (L := L) v
  have hw :
      w.comap (algebraMap K L) = v :=
    chosenInfinitePlaceAbove_comap (L := L) v
  have hvReal : v.IsReal := by
    rw [← hw]
    exact hRamified.isReal
  have hsign :
      LocalClassFieldTheory.realUnitsSign
          (Units.mapEquiv
            (InfinitePlace.Completion.ringEquivRealOfIsReal
              hvReal).toMulEquiv
            (-1 : v.Completionˣ)) =
        (-1 : ℤˣ) := by
    apply Units.ext
    simp [LocalClassFieldTheory.realUnitsSign]
  have hConj :=
    ramifiedInfinitePlaceConjugation_isConj
      (K := K) w hRamified
  change
    NumberField.ComplexEmbedding.IsConj
      (InfinitePlace.embedding w)
      (chosenInfinitePlaceArtinMonoidHom
        (K := K) (L := L) v (-1 : v.Completionˣ))
  have hUnramified : ¬ w.IsUnramified K := hRamified
  have hUnramified' :
      ¬ (chosenInfinitePlaceAbove (L := L) v).IsUnramified K := by
    simpa only [w] using hUnramified
  have hsignNe :
      LocalClassFieldTheory.realUnitsSign
          (Units.mapEquiv
            (InfinitePlace.Completion.ringEquivRealOfIsReal
              hvReal).toMulEquiv
            (-1 : v.Completionˣ)) ≠ 1 := by
    rw [hsign]
    decide
  unfold chosenInfinitePlaceArtinMonoidHom
  unfold infinitePlaceArtinMonoidHomOfPlace
  simp only [dite_eq_right hUnramified', MonoidHom.comp_apply]
  change
    NumberField.ComplexEmbedding.IsConj
      (InfinitePlace.embedding w)
      (if
          LocalClassFieldTheory.realUnitsSign
              (Units.mapEquiv
                (InfinitePlace.Completion.ringEquivRealOfIsReal
                  hvReal).toMulEquiv
                (-1 : v.Completionˣ)) =
            1 then
        1
      else
        ramifiedInfinitePlaceConjugation
          (K := K)
          (chosenInfinitePlaceAbove (L := L) v)
          hUnramified')
  rw [ite_eq_right hsignNe]
  simpa only [w] using hConj

end Galois

end Reciprocity
end GlobalClassFieldTheory
end
end

section
-- module Solutions.OAIQ244_DUKE.GlobalClassFieldTheory_Reciprocity_ComplexificationArtin_RationalComplexification
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalIntermediateFieldAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.PrimeDegreePackets.boundedRealFields_finite _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable
attribute [-simp] _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.OAI.PrimeDegreePackets.ThetaConstruction.schwartzCM_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

/-!
# The rational cyclotomic complexification

This module realizes the quadratic complexification as the fourth-root
cyclotomic field and proves the rational principal-idele Artin formula.
-/

open scoped BigOperators Classical IsMulCommutative NumberField
open NumberField IsDedekindDomain
open IdeleGroup

noncomputable section

namespace GlobalClassFieldTheory
namespace Reciprocity

local instance rationalComplexificationPrimeFact_r862dfd_1 :
    Fact rationalComplexificationPrime.1.Prime :=
  ⟨rationalComplexificationPrime.2⟩
attribute [local instance] GlobalClassFieldTheory.Reciprocity.rationalComplexificationPrimeSquareNeZero
noncomputable instance complexFourthRootField_numberField :
    NumberField complexFourthRootField :=
  IsCyclotomicExtension.numberField
    ({4} : Set ℕ) ℚ complexFourthRootField

theorem rationalComplexification_signCharacter_ne_one_of_num_neg
    (x : ℚˣ) (hx : (x : ℚ).num < 0) :
    Units.map (PadicInt.toZModPow 2).toMonoidHom
        (rationalSignPadicUnit x rationalComplexificationPrime) ≠
      1 := by
  intro h
  have hval := congrArg Units.val h
  rw [rationalSignPadicUnit_toZModPow_val] at hval
  rw [Int.sign_eq_neg_one_of_neg hx] at hval
  norm_num [rationalComplexificationPrime] at hval
  exact (by decide : (-1 : ZMod (2 ^ 2)) ≠ 1) hval

theorem rationalComplexification_signCharacter_eq_one_of_num_pos
    (x : ℚˣ) (hx : 0 < (x : ℚ).num) :
    Units.map (PadicInt.toZModPow 2).toMonoidHom
        (rationalSignPadicUnit x rationalComplexificationPrime) =
      1 := by
  apply Units.ext
  rw [rationalSignPadicUnit_toZModPow_val]
  rw [Int.sign_eq_one_of_pos hx]
  norm_num

end Reciprocity
end GlobalClassFieldTheory
end
end

section
-- module Solutions.OAIQ244_DUKE.GlobalClassFieldTheory_Reciprocity_ComplexificationArtin_InfinitePlaceOverfield
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalIntermediateFieldAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.PrimeDegreePackets.diagonalLogAction _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable
attribute [-simp] _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.OAI.PrimeDegreePackets.ThetaConstruction.schwartzCM_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

/-!
# The complex-conjugation overfield at an infinite place

This module realizes the embedded field `L(i)` inside `ℂ`, constructs its
complex place, and identifies ambient complex conjugation on that field.
-/

open scoped Classical IsMulCommutative
open NumberField

noncomputable section

namespace GlobalClassFieldTheory
namespace Reciprocity

section ComplexConjugationOverextension

variable
    {K L : Type}
    [Field K]
    [Field L] [NumberField L] [Algebra K L]

variable
    [NumberField K]
    [FiniteDimensional K L] [IsAbelianGalois K L]

attribute [local instance] GlobalClassFieldTheory.Reciprocity.infinitePlaceComplexificationOverfieldRationalAlgebra
noncomputable instance
    infinitePlaceComplexificationOverfield_finiteDimensional
    (v : InfinitePlace K) :
    FiniteDimensional ℚ
      (infinitePlaceComplexificationOverfield
        (K := K) (L := L) v) := by
  let φ :=
    (InfinitePlace.embedding
      (chosenInfinitePlaceAbove (L := L) v)).toRatAlgHom
  let : FiniteDimensional ℚ φ.fieldRange :=
    φ.equivFieldRange.toLinearEquiv.finiteDimensional
  exact
    IntermediateField.finiteDimensional_sup
      φ.fieldRange complexFourthRootField

noncomputable instance
    infinitePlaceComplexificationOverfield_numberField
    (v : InfinitePlace K) :
    NumberField
      (infinitePlaceComplexificationOverfield
        (K := K) (L := L) v) :=
  NumberField.of_module_finite ℚ
    (infinitePlaceComplexificationOverfield
      (K := K) (L := L) v)

noncomputable instance
    infinitePlaceComplexificationOverfield_algebra
    (v : InfinitePlace K) :
    Algebra L
      (infinitePlaceComplexificationOverfield
        (K := K) (L := L) v) :=
  (infinitePlaceComplexificationOverfieldEmbedding
    (K := K) (L := L) v).toRingHom.toAlgebra

/-- The scalar action belonging to the chosen top-field embedding. -/
noncomputable instance
    infinitePlaceComplexificationOverfield_smul
    (v : InfinitePlace K) :
    SMul L
      (infinitePlaceComplexificationOverfield
        (K := K) (L := L) v) :=
  (infinitePlaceComplexificationOverfield_algebra
    (K := K) (L := L) v).toSMul

instance
    infinitePlaceComplexificationOverfield_ratScalarTower
    (v : InfinitePlace K) :
    IsScalarTower ℚ L
      (infinitePlaceComplexificationOverfield
        (K := K) (L := L) v) :=
  IsScalarTower.of_algebraMap_eq'
    (infinitePlaceComplexificationOverfieldEmbedding
      (K := K) (L := L) v).comp_algebraMap.symm

noncomputable instance
    infinitePlaceComplexificationOverfield_baseAlgebra
    (v : InfinitePlace K) :
    Algebra K
      (infinitePlaceComplexificationOverfield
        (K := K) (L := L) v) :=
  ((infinitePlaceComplexificationOverfieldEmbedding
      (K := K) (L := L) v).comp
    (IsScalarTower.toAlgHom ℚ K L)).toRingHom.toAlgebra

/-- The scalar action induced from the original base-field embedding. -/
noncomputable instance
    infinitePlaceComplexificationOverfield_baseSmul
    (v : InfinitePlace K) :
    SMul K
      (infinitePlaceComplexificationOverfield
        (K := K) (L := L) v) :=
  (infinitePlaceComplexificationOverfield_baseAlgebra
    (K := K) (L := L) v).toSMul

instance
    infinitePlaceComplexificationOverfield_baseRatScalarTower
    (v : InfinitePlace K) :
    IsScalarTower ℚ K
      (infinitePlaceComplexificationOverfield
        (K := K) (L := L) v) :=
  IsScalarTower.of_algebraMap_eq'
    (((infinitePlaceComplexificationOverfieldEmbedding
        (K := K) (L := L) v).comp
      (IsScalarTower.toAlgHom ℚ K L)).comp_algebraMap).symm

instance
    infinitePlaceComplexificationOverfield_scalarTower
    (v : InfinitePlace K) :
    IsScalarTower K L
      (infinitePlaceComplexificationOverfield
        (K := K) (L := L) v) :=
  IsScalarTower.of_algebraMap_eq' rfl

noncomputable instance
    infinitePlaceComplexificationOverfield_finiteDimensional_over_extension
    (v : InfinitePlace K) :
    FiniteDimensional L
      (infinitePlaceComplexificationOverfield
        (K := K) (L := L) v) :=
  FiniteDimensional.right ℚ L
    (infinitePlaceComplexificationOverfield
      (K := K) (L := L) v)

/-- The copy of the given abelian extension inside the concrete
complexification overfield, viewed over the original base field. -/
noncomputable def infinitePlaceEmbeddedExtensionField
    (v : InfinitePlace K) :
    IntermediateField K
      (infinitePlaceComplexificationOverfield
        (K := K) (L := L) v) :=
  (IsScalarTower.toAlgHom K L
    (infinitePlaceComplexificationOverfield
      (K := K) (L := L) v)).fieldRange

noncomputable instance
    infinitePlaceEmbeddedExtensionField_isAbelianGalois
    (v : InfinitePlace K) :
    IsAbelianGalois K
      (infinitePlaceEmbeddedExtensionField
        (K := K) (L := L) v) :=
  IsAbelianGalois.of_algHom
    (IsScalarTower.toAlgHom K L
      (infinitePlaceComplexificationOverfield
        (K := K) (L := L) v)).equivFieldRange.symm.toAlgHom

/-- The fourth-root cyclotomic factor over the original base field,
inside the concrete complexification overfield. -/
noncomputable def infinitePlaceBaseFourthRootField
    (v : InfinitePlace K) :
    IntermediateField K
      (infinitePlaceComplexificationOverfield
        (K := K) (L := L) v) :=
  IntermediateField.adjoin K
    {z :
        infinitePlaceComplexificationOverfield
          (K := K) (L := L) v |
      ∃ n ∈ ({4} : Set ℕ), n ≠ 0 ∧ z ^ n = 1}

noncomputable instance
    infinitePlaceBaseFourthRootField_isCyclotomic
    (v : InfinitePlace K) :
    IsCyclotomicExtension {4} K
      (infinitePlaceBaseFourthRootField
        (K := K) (L := L) v) := by
  apply
    IntermediateField.isCyclotomicExtension_adjoin_of_exists_isPrimitiveRoot
      ({4} : Set ℕ) K
      (infinitePlaceComplexificationOverfield
        (K := K) (L := L) v)
  intro n hn _hn0
  rw [Set.mem_singleton_iff] at hn
  subst n
  let C :=
    infinitePlaceComplexificationOverfield
      (K := K) (L := L) v
  let ζ : C :=
    ⟨Complex.I,
      (show complexFourthRootField ≤ C from le_sup_right)
        (IntermediateField.subset_adjoin
          ℚ
          {z : ℂ |
            ∃ n ∈ ({4} : Set ℕ),
              n ≠ 0 ∧ z ^ n = 1}
          ⟨4, Set.mem_singleton 4, by norm_num,
            by norm_num [pow_succ, Complex.I_sq]⟩)⟩
  refine ⟨ζ, ?_⟩
  apply IsPrimitiveRoot.of_map_of_injective
    (f :=
      (C.val : C →ₐ[ℚ] ℂ))
    (ζ := ζ)
    (k := 4)
  · change IsPrimitiveRoot Complex.I 4
    exact complexI_isPrimitiveRoot_four
  · exact C.val.injective

noncomputable instance
    infinitePlaceBaseFourthRootField_isAbelianGalois
    (v : InfinitePlace K) :
    IsAbelianGalois K
      (infinitePlaceBaseFourthRootField
        (K := K) (L := L) v) :=
  IsCyclotomicExtension.isAbelianGalois
    ({4} : Set ℕ) K
    (infinitePlaceBaseFourthRootField
      (K := K) (L := L) v)

/-- The infinite place on the concrete overfield induced by its
inclusion into `ℂ`. -/
noncomputable def infinitePlaceComplexificationOverfieldComplexPlace
    (v : InfinitePlace K) :
    InfinitePlace
      (infinitePlaceComplexificationOverfield
        (K := K) (L := L) v) :=
  InfinitePlace.mk
    (infinitePlaceComplexificationOverfield
      (K := K) (L := L) v).val.toRingHom

end ComplexConjugationOverextension

end Reciprocity
end GlobalClassFieldTheory
end
end

section
-- module Solutions.OAIQ244_DUKE.Kummer_Concrete_FiniteSupport
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

/-!
# finite radical support

Membership in `K(√[n]{Δ})` uses only finitely many of the adjoined roots.
For such a finite root set this file chooses the corresponding coefficients
in `Δ`, records them in a finite subset of `Kˣ`, and forms the subgroup they
generate.  The resulting subgroup lies in `Δ`, and every selected root has
its `n`-th power in that finitely generated subgroup.

These are the concrete finite-support data needed for the later reduction to
finite Kummer theory; no finite Kummer endpoint is assumed here.
-/

noncomputable section

namespace KummerTheory

variable {K Omega : Type*} [Field K] [Field Omega] [Algebra K Omega]

/-- An element of a radical extension belongs to the field generated by a
finite subset of the full Kummer root set. -/
theorem exists_finset_kummerRootSet_of_mem_kummerRadicalExtension
    (n : ℕ+) (Delta : Subgroup Kˣ) {beta : Omega}
    (hbeta : beta ∈ kummerRadicalExtension (K := K) (Omega := Omega) n Delta) :
    ∃ T : Finset Omega,
      (T : Set Omega) ⊆ kummerRootSet (K := K) (Omega := Omega) n Delta ∧
      beta ∈ IntermediateField.adjoin K (T : Set Omega) := by
  exact IntermediateField.exists_finset_of_mem_adjoin hbeta


end KummerTheory
end
end

section
-- module Solutions.OAIQ244_DUKE.KummerTheory_Concrete_SUnitPreparation_FullSUnitKummerExtension
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.CyclicCohomology.binaryCoefficientFamilyCommGroup _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace
attribute [-simp] _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.IsDiscreteValuationRing.addVal_ringEquiv _root_.KummerTheory.mem_sUnitFiniteKummerRadical_iff _root_.LocalFieldTheory.residueField_algebraMap_residue _root_.OAI.PrimeDegreePackets.ThetaConstruction.schwartzCM_apply _root_.sUnit_smul_coe
set_option synthInstance.maxHeartbeats 400000
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

/-!
# The full S-unit Kummer extension

Construction, finite generation, Galois structure, cardinality, and coordinates for the Kummer extension generated by all `S`-unit roots.
-/

open scoped NumberField Classical IsMulCommutative NNReal ValuativeRel
open NumberField IsDedekindDomain
open LocalFieldTheory

noncomputable section

namespace KummerTheory

variable {K : Type*} [Field K]
    [numberFieldK : NumberField K]

/-- Every root used to generate the full `S`-unit Kummer extension can be
rescaled by an element of `Kˣ` to become the root of an actual `S`-unit.
The rescaling does not change the simple intermediate field that it
generates.  This is the source-producing step needed to apply the local
unramified Kummer criterion to every generator of the full extension. -/
theorem exists_sUnitRoot_adjoin_eq_of_mem_fullSUnitKummerRootSet
    {Omega : Type*} [Field Omega] [Algebra K Omega]
    (n : ℕ+)
    (S : Finset (HeightOneSpectrum (𝓞 K)))
    {beta : Omega}
    (hbeta :
      beta ∈
        KummerTheory.kummerRootSet
          (K := K) (Omega := Omega) n
          (fullSUnitKummerSubgroup (K := K) n S).1) :
    ∃ (u : SUnitGroup (K := K) S) (alpha : Omegaˣ),
      alpha ^ (n : ℕ) =
          Units.map (algebraMap K Omega).toMonoidHom u.1 ∧
        IntermediateField.adjoin K {(alpha : Omega)} =
          IntermediateField.adjoin K {beta} := by
  have hbetaNe : beta ≠ 0 :=
    KummerTheory.kummerRootSet_ne_zero
      n (fullSUnitKummerSubgroup (K := K) n S).1 hbeta
  obtain ⟨a, hbetaPow⟩ := hbeta
  obtain ⟨u, hu, z, hz, huz⟩ :=
    Subgroup.mem_sup.mp a.property
  obtain ⟨c, hc⟩ :=
    (KummerTheory.mem_unitNthPowersSubgroup_iff n).mp hz
  let uS : SUnitGroup (K := K) S := ⟨u, hu⟩
  let betaUnit : Omegaˣ :=
    Units.mk0 beta hbetaNe
  let cOmega : Omegaˣ :=
    Units.map (algebraMap K Omega).toMonoidHom c
  let alpha : Omegaˣ := betaUnit / cOmega
  have hbetaUnitPow :
      betaUnit ^ (n : ℕ) =
        Units.map (algebraMap K Omega).toMonoidHom a.1 := by
    apply Units.ext
    exact hbetaPow
  have hcOmegaPow :
      cOmega ^ (n : ℕ) =
        Units.map (algebraMap K Omega).toMonoidHom z := by
    dsimp only [cOmega]
    rw [← map_pow, hc]
  have hau : a.1 / z = u := by
    rw [← huz]
    simp
  have halphaPow :
      alpha ^ (n : ℕ) =
        Units.map (algebraMap K Omega).toMonoidHom u := by
    dsimp only [alpha]
    rw [div_pow, hbetaUnitPow, hcOmegaPow, ← map_div, hau]
  refine ⟨uS, alpha, halphaPow, ?_⟩
  let Rbeta := IntermediateField.adjoin K {beta}
  let Ralpha := IntermediateField.adjoin K {(alpha : Omega)}
  have halphaMem : (alpha : Omega) ∈ Rbeta := by
    have halphaVal :
        (alpha : Omega) =
          beta / algebraMap K Omega (c : K) := by
      simp [alpha, betaUnit, cOmega]
    rw [halphaVal]
    exact Rbeta.div_mem
      (IntermediateField.subset_adjoin K {beta}
        (Set.mem_singleton beta))
      (Rbeta.algebraMap_mem (c : K))
  have hrecover : alpha * cOmega = betaUnit :=
    div_mul_cancel betaUnit cOmega
  have hbetaMem : beta ∈ Ralpha := by
    have hrecoverVal :
        (alpha : Omega) *
            algebraMap K Omega (c : K) = beta := by
      simpa [betaUnit, cOmega] using
        congrArg Units.val hrecover
    rw [← hrecoverVal]
    exact Ralpha.mul_mem
      (IntermediateField.subset_adjoin K {(alpha : Omega)}
        (Set.mem_singleton (alpha : Omega)))
      (Ralpha.algebraMap_mem (c : K))
  apply le_antisymm
  · apply IntermediateField.adjoin_le_iff.mpr
    intro x hx
    rw [Set.mem_singleton_iff] at hx
    subst x
    exact halphaMem
  · apply IntermediateField.adjoin_le_iff.mpr
    intro x hx
    rw [Set.mem_singleton_iff] at hx
    subst x
    exact hbetaMem

end KummerTheory
end
end

section
-- module Solutions.OAIQ244_DUKE.KummerTheory_Concrete_SUnitKummerUnramified
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.infinitePlaceComplexificationOverfield_algebra _root_.GlobalClassFieldTheory.Reciprocity.infinitePlaceComplexificationOverfield_baseAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.OAI.PrimeDegreePackets.diagonalLogAction _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.cyclicPrimeDegreeIntermediate_isGalois _root_.cyclicPrimeSubextension_isGalois
attribute [-simp] _root_.IsDiscreteValuationRing.addVal_ringEquiv _root_.OAI.PrimeDegreePackets.ThetaConstruction.schwartzCM_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

/-!
# Unramifiedness of the full `S`-unit Kummer extension

This file supplies the ramification input in the existence proof for the
global norm topology.  Every defining root of

`K(√[n]{Kˢ}) / K`

is first rescaled to the root of an actual `S`-unit.  Its simple
intermediate field is then identified with the chosen simple Kummer
extension attached to that unit.  The finite set of such simple fields
generating the full extension is used to kill the full inertia group away
from `S`.
-/

open scoped NumberField Classical
open NumberField IsDedekindDomain
open AlgebraicNumberTheory.Valuations
open HilbertRamification
open HilbertRamification.Dedekind

noncomputable section

namespace KummerTheory

variable {K : Type} [Field K] [NumberField K]

omit [NumberField K] in
/-- An arbitrary nonzero root of `X ^ n - b` in the separable closure
generates the same intermediate field as the chosen simple Kummer root,
provided that the base field contains the `n`-th roots of unity. -/
theorem adjoin_rootUnit_eq_chosenSimpleKummerExtension
    (n : ℕ+) (hn : ((n : ℕ) : K) ≠ 0)
    (hmu : (primitiveRoots (n : ℕ) K).Nonempty)
    (b : Kˣ) (alpha : (SeparableClosure K)ˣ)
    (halpha :
      alpha ^ (n : ℕ) =
        Units.map
          (algebraMap K (SeparableClosure K)).toMonoidHom b) :
    IntermediateField.adjoin K
        {(alpha : SeparableClosure K)} =
      chosenSimpleKummerExtension K n hn b := by
  let E := chosenSimpleKummerExtension K n hn b
  have hbE :
      b ∈
        finiteKummerRadicalSubgroup
          (K := K) (L := E) n := by
    exact
      ⟨chosenSimpleKummerRootUnit K n hn b,
        chosenSimpleKummerRootUnit_pow K n hn b⟩
  have halphaRoot :
      (alpha : SeparableClosure K) ∈
        kummerRootSet
          (K := K) (Omega := SeparableClosure K) n
          (finiteKummerRadicalSubgroup
            (K := K) (L := E) n) := by
    refine ⟨⟨b, hbE⟩, ?_⟩
    simpa using congrArg Units.val halpha
  have halphaE : (alpha : SeparableClosure K) ∈ E :=
    kummerRootSet_finiteKummerRadicalSubgroup_le
      E n hmu halphaRoot
  let R :=
    IntermediateField.adjoin K
      {(alpha : SeparableClosure K)}
  let alphaR : Rˣ :=
    Units.mk0
      ⟨(alpha : SeparableClosure K),
        IntermediateField.subset_adjoin K
          {(alpha : SeparableClosure K)}
          (Set.mem_singleton (alpha : SeparableClosure K))⟩
      (by
        intro hzero
        apply alpha.ne_zero
        exact congrArg Subtype.val hzero)
  have hbR :
      b ∈
        finiteKummerRadicalSubgroup
          (K := K) (L := R) n := by
    refine ⟨alphaR, ?_⟩
    apply Units.ext
    apply Subtype.ext
    simpa [alphaR] using congrArg Units.val halpha
  have hchosenRoot :
      chosenSimpleKummerRoot K n hn b ∈
        kummerRootSet
          (K := K) (Omega := SeparableClosure K) n
          (finiteKummerRadicalSubgroup
            (K := K) (L := R) n) := by
    exact
      ⟨⟨b, hbR⟩,
        chosenSimpleKummerRoot_pow K n hn b⟩
  have hchosenRootR :
      chosenSimpleKummerRoot K n hn b ∈ R :=
    kummerRootSet_finiteKummerRadicalSubgroup_le
      R n hmu hchosenRoot
  apply le_antisymm
  · apply IntermediateField.adjoin_le_iff.mpr
    intro x hx
    rw [Set.mem_singleton_iff] at hx
    subst x
    exact halphaE
  · change
      IntermediateField.adjoin K
          {chosenSimpleKummerRoot K n hn b} ≤ R
    apply IntermediateField.adjoin_le_iff.mpr
    intro x hx
    rw [Set.mem_singleton_iff] at hx
    subst x
    exact hchosenRootR

/-- Internal source data for a defining root of the full `S`-unit Kummer
extension.  Inside the simple field generated by the original root, this
produces an actual root of an `S`-unit which still generates the whole
simple field, together with its concrete simple-Kummer model. -/
theorem exists_sUnitRootUnit_generating_internalAdjoin
    {Omega : Type} [Field Omega] [Algebra K Omega]
    [IsSepClosure K Omega]
    (E : IntermediateField K Omega)
    (n : ℕ+) (hn : ((n : ℕ) : K) ≠ 0)
    (hmu : (primitiveRoots (n : ℕ) K).Nonempty)
    (S : Finset (HeightOneSpectrum (𝓞 K)))
    (beta : E)
    (hbeta :
      (beta : Omega) ∈
        kummerRootSet
          (K := K) (Omega := Omega) n
          (fullSUnitKummerSubgroup (K := K) n S).1) :
    let B := IntermediateField.adjoin K {beta}
    ∃ (u : SUnitGroup (K := K) S) (alpha : Bˣ)
        (_ : B ≃ₐ[K] chosenSimpleKummerExtension K n hn u.1),
      alpha ^ (n : ℕ) =
          Units.map (algebraMap K B).toMonoidHom u.1 ∧
        IntermediateField.adjoin K {(alpha : B)} = ⊤ := by
  classical
  dsimp only
  let B := IntermediateField.adjoin K {beta}
  obtain ⟨u, alphaOmega, halphaOmega, hadjoinOmega⟩ :=
    exists_sUnitRoot_adjoin_eq_of_mem_fullSUnitKummerRootSet
      (K := K) n S hbeta
  have hbetaAdjoinE :
      IntermediateField.adjoin K {(beta : Omega)} ≤ E := by
    apply IntermediateField.adjoin_le_iff.mpr
    intro x hx
    rw [Set.mem_singleton_iff] at hx
    subst x
    exact beta.property
  have halphaOmegaMem :
      (alphaOmega : Omega) ∈
        IntermediateField.adjoin K {(beta : Omega)} := by
    rw [← hadjoinOmega]
    exact
      IntermediateField.subset_adjoin K
        {(alphaOmega : Omega)}
        (Set.mem_singleton (alphaOmega : Omega))
  let alphaE : Eˣ :=
    Units.mk0
      ⟨(alphaOmega : Omega),
        hbetaAdjoinE halphaOmegaMem⟩
      (by
        intro hzero
        apply alphaOmega.ne_zero
        exact congrArg Subtype.val hzero)
  have hadjoinE :
      IntermediateField.adjoin K {(alphaE : E)} = B := by
    exact
      adjoin_subtype_eq_of_adjoin_ambient_eq
        E (alphaE : E) beta hadjoinOmega
  let alphaB : Bˣ :=
    Units.mk0
      ⟨(alphaE : E), by
        rw [← hadjoinE]
        exact
          IntermediateField.subset_adjoin K
            {(alphaE : E)}
            (Set.mem_singleton (alphaE : E))⟩
      (by
        intro hzero
        apply alphaE.ne_zero
        exact congrArg Subtype.val hzero)
  have halphaOmegaVal :=
    congrArg Units.val halphaOmega
  simp only [Units.val_pow_eq_pow_val,
    Units.coe_map] at halphaOmegaVal
  have halphaB :
      alphaB ^ (n : ℕ) =
        Units.map (algebraMap K B).toMonoidHom u.1 := by
    apply Units.ext
    apply Subtype.ext
    apply Subtype.ext
    simpa [alphaB, alphaE] using halphaOmegaVal
  have hgenerate :
      IntermediateField.adjoin K {(alphaB : B)} = ⊤ := by
    apply IntermediateField.map_injective B.val
    calc
      (IntermediateField.adjoin K {(alphaB : B)}).map B.val =
          IntermediateField.adjoin K
            {B.val (alphaB : B)} := by
        rw [IntermediateField.adjoin_map,
          Set.image_singleton]
      _ = IntermediateField.adjoin K {(alphaE : E)} := by
        rfl
      _ = B := hadjoinE
      _ = B.val.fieldRange :=
        (IntermediateField.fieldRange_val B).symm
      _ = (⊤ : IntermediateField K B).map B.val :=
        (AlgHom.fieldRange_eq_map B.val)
  let eOmega : Omega ≃ₐ[K] SeparableClosure K :=
    IsSepClosure.equiv K Omega (SeparableClosure K)
  let alphaSep : (SeparableClosure K)ˣ :=
    Units.map eOmega.toMonoidHom alphaOmega
  have halphaSep :
      alphaSep ^ (n : ℕ) =
        Units.map
          (algebraMap K (SeparableClosure K)).toMonoidHom u.1 := by
    apply Units.ext
    simp only [Units.val_pow_eq_pow_val,
      alphaSep, Units.coe_map]
    rw [← map_pow, halphaOmegaVal]
    exact eOmega.commutes (u.1 : K)
  have hmap :
      (IntermediateField.adjoin K
          {(alphaOmega : Omega)}).map eOmega.toAlgHom =
        IntermediateField.adjoin K
          {(alphaSep : SeparableClosure K)} := by
    rw [IntermediateField.adjoin_map, Set.image_singleton]
    rfl
  have hsimple :
      IntermediateField.adjoin K
          {(alphaSep : SeparableClosure K)} =
        chosenSimpleKummerExtension K n hn u.1 :=
    adjoin_rootUnit_eq_chosenSimpleKummerExtension
      n hn hmu u.1 alphaSep halphaSep
  let eAmbient :
      B ≃ₐ[K]
        IntermediateField.adjoin K {(beta : Omega)} :=
    adjoinSubtypeEquivAmbientAdjoin E beta
  let eSimple : B ≃ₐ[K] chosenSimpleKummerExtension K n hn u.1 :=
    eAmbient.trans
      ((IntermediateField.equivOfEq hadjoinOmega.symm).trans
        ((IntermediateField.equivMap
            (IntermediateField.adjoin K {(alphaOmega : Omega)})
            eOmega.toAlgHom).trans
          ((IntermediateField.equivOfEq hmap).trans
            (IntermediateField.equivOfEq hsimple))))
  exact ⟨u, alphaB, eSimple, halphaB, hgenerate⟩

/-- The simple intermediate field generated by any defining root of the
full `S`-unit Kummer extension is Galois over the base field.  The proof
rescales the defining root to an actual `S`-unit root and transports the
concrete simple-Kummer Galois structure across the resulting algebra
equivalence. -/
theorem fullSUnitKummerRoot_internalAdjoin_isGalois
    {Omega : Type} [Field Omega] [Algebra K Omega]
    [IsSepClosure K Omega]
    (E : IntermediateField K Omega)
    (n : ℕ+) (hn : ((n : ℕ) : K) ≠ 0)
    (hmu : (primitiveRoots (n : ℕ) K).Nonempty)
    (S : Finset (HeightOneSpectrum (𝓞 K)))
    (beta : E)
    (hbeta :
      (beta : Omega) ∈
        kummerRootSet
          (K := K) (Omega := Omega) n
          (fullSUnitKummerSubgroup (K := K) n S).1) :
    IsGalois K (IntermediateField.adjoin K {beta}) := by
  obtain ⟨u, _, eSimple, _, _⟩ :=
    exists_sUnitRootUnit_generating_internalAdjoin
      (K := K) E n hn hmu S beta hbeta
  let L := chosenSimpleKummerExtension K n hn u.1
  let : FiniteDimensional K L :=
    chosenSimpleKummerExtension_finiteDimensional K n hn u.1
  let : IsAbelianGalois K L :=
    chosenSimpleKummerExtension_isAbelianGalois K n hn hmu u.1
  exact IsGalois.of_algEquiv eSimple.symm

end KummerTheory
end
end


