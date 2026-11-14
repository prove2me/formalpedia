-- Prove2me | Definitions.Def_OAIQ244Duke101
-- name    : OAIQ244Duke101
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-14T03:03:08.369419+00:00
-- url     : https://prove2.me/theorems/5234fc15-e419-486b-b8e7-eb74486cb8b6
-- title:
--   Definitions bundle OAIQ244Duke101 of the split of OpenAI, Equidistribution of Prime-Degree Torus Packets with Arbitrary Local Type
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.DukePrimeDegree.prime_degree_packet_measure_equidistribution_unconditional` and `OAI.DukePrimeDegree.prime_degree_packet_measures_tendsto_haar_unconditional`, carved from OpenAI's openai/math development (OpenAI, *Equidistribution of Prime-Degree Torus Packets with Arbitrary Local Type*, OpenAI Math Release, September 24, 2026, result family 15, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 60 declarations of OpenAI's Lean: 15 definitions, 7 instances and 38 theorems. The definitions and types are `GlobalClassFieldTheory.GlobalClassFields.chosenFinitePlaceArithmeticFrobenius`, `GlobalClassFieldTheory.Reciprocity.automorphismCyclicFixedTopExtension`, `GlobalClassFieldTheory.Reciprocity.finitePlaceCyclotomicCompositumExtension`, `GlobalClassFieldTheory.Reciprocity.finitePlaceSeparableClosureDecompositionRestriction`, `GlobalClassFieldTheory.Reciprocity.finitePlaceSeparableClosureTopCyclotomicRestriction`, `GlobalClassFieldTheory.Reciprocity.finitePlaceSeparableClosureTopDecompositionInclusion`, `GlobalClassFieldTheory.Reciprocity.finitePlaceSeparableClosureTopExtension`, `GlobalClassFieldTheory.Reciprocity.normTopologyIdeleClassCommGroup`, `GlobalClassFieldTheory.Reciprocity.numberFieldTowerFiniteNormClassPublicValue`, `GlobalClassFieldTheory.Reciprocity.numberFieldTowerFinitePlaceExtensionToSeparableClosure`, `GlobalClassFieldTheory.Reciprocity.numberFieldTowerRestrictedTopAlgebra`, `GlobalClassFieldTheory.Reciprocity.numberFieldTowerSeparableClosureTopAlgebra`, `GlobalClassFieldTheory.Reciprocity.ramifiedInfinitePlaceOverextensionCyclotomicRestriction`, `GlobalClassFieldTheory.Reciprocity.rationalComplexificationEmbeddingInInfinitePlaceOverfield`, `GlobalClassFieldTheory.Reciprocity.realizedTowerIdeleClassCommGroup`.
--
--   **Sources.** They come from these modules of lean/OAI/NumberTheory, in whole or in part: `GlobalClassFieldTheory_ClassFieldAxiom_IdeleClassFormation`, `GlobalClassFieldTheory_GlobalClassFields_ArithmeticUnramifiedPrimeArtin`, `GlobalClassFieldTheory_Reciprocity_ComplexificationArtin_InfinitePlaceOverfield`, `GlobalClassFieldTheory_Reciprocity_ComplexificationArtin_RamifiedOverextension`, `GlobalClassFieldTheory_Reciprocity_ComplexificationArtin_RationalComplexification`, `GlobalClassFieldTheory_Reciprocity_FiniteGaloisRealization`, `GlobalClassFieldTheory_Reciprocity_FiniteGaloisRealizationCore`, `GlobalClassFieldTheory_Reciprocity_FiniteGaloisRealizationFinitePlace`, `GlobalClassFieldTheory_Reciprocity_FiniteGaloisRealizationSubextension`, `GlobalClassFieldTheory_Reciprocity_FinitePlaceCyclotomicFrobeniusLift`, `GlobalClassFieldTheory_Reciprocity_IdeleClassNormTopology`, `GlobalClassFieldTheory_Reciprocity_LocalGlobalArtinCompatibility_SeparableClosurePadicLift`.
--
--   **Imports.** It imports the bundles `OAIQ244Duke083`, `OAIQ244Duke097` and `OAIQ244Duke098` of this split.
--
--   **Imported by** (directly, in this split): the bundle `OAIQ244Duke120`.
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
import Mathlib.Algebra.Colimit.DirectLimit
import Mathlib.Algebra.EuclideanDomain.Basic
import Mathlib.Algebra.Exact.Basic
import Mathlib.Algebra.Group.Action.Basic
import Mathlib.Algebra.Group.Equiv.Basic
import Mathlib.Algebra.Group.Equiv.TypeTags
import Mathlib.Algebra.Group.Hom.Basic
import Mathlib.Algebra.Group.Hom.Instances
import Mathlib.Algebra.Group.Int.TypeTags
import Mathlib.Algebra.Group.Pi.Basic
import Mathlib.Algebra.Group.Pi.Units
import Mathlib.Algebra.Group.Subgroup.Basic
import Mathlib.Algebra.Group.Subgroup.Finite
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
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Combinatorics.Hall.Finite
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
import Mathlib.GroupTheory.QuotientGroup.Defs
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
import Mathlib.NumberTheory.Cyclotomic.Discriminant
import Mathlib.NumberTheory.Cyclotomic.Gal
import Mathlib.NumberTheory.Cyclotomic.PrimitiveRoots
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
import Mathlib.Topology.Algebra.FilterBasis
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
import Mathlib.Topology.Order.MonotoneContinuity
import Mathlib.Topology.Sets.Opens
import Mathlib.Topology.UniformSpace.AbsoluteValue
import Mathlib.Topology.WithTopology
import Definitions.Def_OAIQ244Duke083
import Definitions.Def_OAIQ244Duke097
import Definitions.Def_OAIQ244Duke098

section
-- module Solutions.OAIQ244_DUKE.GlobalClassFieldTheory_ClassFieldAxiom_IdeleClassFormation
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 400000
attribute [-instance] _root_.GlobalClassFieldTheory.GlobalClassFields.bigHilbertClassFieldNormSubgroup_normal _root_.GlobalClassFieldTheory.GlobalClassFields.finiteAbelianSubextensionAbstractRelativeFixedFieldFiniteDimensional _root_.GlobalClassFieldTheory.GlobalClassFields.finiteAbelianSubextensionAbstractRelativeFixedFieldIsAbelianGalois _root_.GlobalClassFieldTheory.Reciprocity.infinitePlaceComplexificationOverfield_baseSmul _root_.GlobalClassFieldTheory.Reciprocity.infinitePlaceComplexificationOverfield_smul _root_.GlobalClassFieldTheory.Reciprocity.numberFieldTowerBaseFieldAlgebra _root_.GlobalClassFieldTheory.Reciprocity.numberFieldTowerBaseSubgroupAbsoluteQuotientFinite _root_.GlobalClassFieldTheory.Reciprocity.numberFieldTowerExtensionQuotientFinite _root_.GlobalClassFieldTheory.Reciprocity.numberFieldTowerExtensionSubgroupNormal _root_.GlobalClassFieldTheory.Reciprocity.rationalCyclotomicZHatCompositum_algebra _root_.GlobalClassFieldTheory.Reciprocity.rationalCyclotomicZHatFiniteLayerCompositum_algebra _root_.GlobalClassFieldTheory.Reciprocity.rationalCyclotomicZHatFiniteLayerCompositum_smul _root_.GlobalClassFieldTheory.Reciprocity.rationalCyclotomicZHatFiniteLayerInCompositum_algebra _root_.GlobalClassFieldTheory.Reciprocity.rationalCyclotomicZHatFiniteLayerInCompositum_smul _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalClassFieldTheory.finiteGaloisLocalField_integerRing_moduleFinite _root_.LubinTate.padicCompletedLevelField_algebra _root_.LubinTate.padicCompletedLevelField_isGalois _root_.LubinTate.padicCompletedLevelField_padicScalarTower _root_.LubinTate.padicCompletedUnramifiedFieldAlgebra _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.instTopologicalSpaceLocalAlgebra _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.LocalClassFieldTheory.comparisonIntegerRingIsIntegralClosure _root_.LocalClassFieldTheory.normalizationIntegerRingIsIntegralClosure
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

/-!
# The rational idele-class formation

This module identifies the fixed-field idele-class representation with
concrete relative idele class groups and transfers the cyclic low-degree Tate
cohomology calculation to prove the abstract class-field axiom.
-/

namespace GlobalClassFieldTheory

open scoped NumberField TensorProduct
open NumberField
open CyclicCohomology ClassFormation
open LocalClassFieldTheory

noncomputable section

open CategoryTheory

namespace Reciprocity

/-- The rational absolute idele-class representation satisfies the
abstract class-field axiom. -/
theorem rationalIdeleClassRepresentation_satisfiesClassFieldAxiom :
    SatisfiesClassFieldAxiom rationalIdeleClassRepresentation := by
  rintro ⟨K, hKfinite⟩
  rintro ⟨L, hLK, hnormal, hfinite, g, hg⟩
  let := hKfinite
  let := hnormal
  let := hfinite
  let Q := K.toSubgroup ⧸ extensionSubgroup K L hLK
  let : Fintype Q := Fintype.ofFinite Q
  let F := abstractFixedField ℚ (SeparableClosure ℚ) K
  let E := abstractRelativeFixedField ℚ (SeparableClosure ℚ) hLK
  let : FiniteDimensional ℚ F :=
    abstractFixedField_finiteDimensional
      ℚ (SeparableClosure ℚ) K hKfinite
  let : FiniteDimensional F E :=
    abstractRelativeFixedField_finiteDimensional
      ℚ (SeparableClosure ℚ) K L hLK hKfinite hfinite
  let : IsScalarTower ℚ F E :=
    IsScalarTower.of_algebraMap_eq' rfl
  let : FiniteDimensional ℚ E :=
    FiniteDimensional.trans ℚ F E
  let : NumberField F := NumberField.of_module_finite ℚ F
  let : NumberField E := NumberField.of_module_finite ℚ E
  let : IsGalois F E :=
    abstractRelativeFixedField_isGalois
      ℚ (SeparableClosure ℚ) K L hLK hnormal
  let eQ : Q ≃* Gal(E / F) :=
    abstractExtensionQuotientEquivGaloisGroup
      ℚ (SeparableClosure ℚ) K L hLK hnormal
  let g' : Gal(E / F) := eQ g
  have hg' : ∀ σ : Gal(E / F),
      σ ∈ Subgroup.zpowers g' :=
    map_cyclicGenerator eQ g hg
  let :=
    RelativeIdeleGroup.Cohomology.ideleClassMulDistribMulAction F E
  have hIdeleClassTateCard :=
    ClassFieldAxiom.ideleClass_tate_lowDegree_finite_card_eq_finrank_cyclic
      F E g' hg'
  let : IsCyclic Q :=
    CyclicCohomology.isCyclic_of_generator g hg
  let : CommGroup Q := IsCyclic.commGroup
  let : IsCyclic (Gal(E / F)) :=
    CyclicCohomology.isCyclic_of_generator g' hg'
  let : CommGroup (Gal(E / F)) := IsCyclic.commGroup
  let M :=
    extensionFixedRepresentation rationalIdeleClassRepresentation
      K L hLK hnormal
  let U :=
    Rep.ofMulDistribMulAction (E ≃ₐ[F] E)
      (RelativeIdeleGroup.ClassGroup F E)
  let eM : M ≅ Rep.res eQ.toMonoidHom U := by
    let e :=
      rationalAbstractExtensionIdeleClassEquiv K L hLK hnormal
    refine Rep.mkIso (Representation.Equiv.mk e.toIntLinearEquiv ?_)
    intro q
    apply LinearMap.ext
    intro x
    exact
      rationalAbstractExtensionIdeleClassEquiv_action
        K L hLK hnormal q x
  let eH0 :
      (Rep.FiniteCyclicGroup.normHomCompSub M g).homology ≅
        (Rep.FiniteCyclicGroup.normHomCompSub U g').homology :=
    (normHomCompSubHomologyIsoOfRepIso eM g) ≪≫
      normHomCompSubHomologyResEquivIso eQ U g
  let eHm1 :
      (Rep.FiniteCyclicGroup.subCompNormHom M g).homology ≅
        (Rep.FiniteCyclicGroup.subCompNormHom U g').homology :=
    (subCompNormHomHomologyIsoOfRepIso eM g) ≪≫
      subCompNormHomHomologyResEquivIso eQ U g
  let eTateH0 :
      tateCohomology M 0 ≅ tateCohomology U 0 :=
    TateCohomology.isoFiniteCyclicZero M g hg ≪≫ eH0 ≪≫
      (TateCohomology.isoFiniteCyclicZero U g' hg').symm
  let eTateHm1 :
      tateCohomology M (-1) ≅ tateCohomology U (-1) :=
    TateCohomology.isoFiniteCyclicNegOne M g hg ≪≫ eHm1 ≪≫
      (TateCohomology.isoFiniteCyclicNegOne U g' hg').symm
  let : Finite (tateCohomology U 0) := hIdeleClassTateCard.1
  let : Finite (tateCohomology U (-1)) := hIdeleClassTateCard.2.1
  let : Finite (tateCohomology M 0) :=
    Finite.of_equiv
      (tateCohomology U 0) eTateH0.symm.toLinearEquiv.toEquiv
  let : Finite (tateCohomology M (-1)) :=
    Finite.of_equiv
      (tateCohomology U (-1)) eTateHm1.symm.toLinearEquiv.toEquiv
  refine
    { finiteTateHZero := by
        change Finite (tateCohomology M 0)
        infer_instance
      finiteTateHMinusOne := by
        change Finite (tateCohomology M (-1))
        infer_instance
      tateHZero_card := ?_
      tateHMinusOne_card := ?_ }
  · change Nat.card (tateCohomology M 0) =
      ((DegreeData.FiniteAbstractExtension.ofInclusion
        L K hLK).degree : ℕ)
    calc
      Nat.card (tateCohomology M 0) =
          Nat.card (tateCohomology U 0) :=
        Nat.card_congr eTateH0.toLinearEquiv.toEquiv
      _ = Module.finrank F E := hIdeleClassTateCard.2.2.1
      _ =
          ((DegreeData.FiniteAbstractExtension.ofInclusion
            L K hLK).degree : ℕ) :=
        (finiteAbstractExtension_degree_eq_finrank
          ℚ (SeparableClosure ℚ) K L hLK hnormal
            hKfinite hfinite).symm
  · change Nat.card (tateCohomology M (-1)) = 1
    calc
      Nat.card (tateCohomology M (-1)) =
          Nat.card (tateCohomology U (-1)) :=
        Nat.card_congr eTateHm1.toLinearEquiv.toEquiv
      _ = 1 := hIdeleClassTateCard.2.2.2

end Reciprocity

end
end GlobalClassFieldTheory
end

section
-- module Solutions.OAIQ244_DUKE.GlobalClassFieldTheory_Reciprocity_ComplexificationArtin_RationalComplexification
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.GlobalClassFields.ConductorialSubgroup.finiteIndex _root_.GlobalClassFieldTheory.GlobalClassFields.bigHilbertClassFieldNormSubgroup_normal _root_.GlobalClassFieldTheory.GlobalClassFields.ideleClassNorm_rangeFiniteIndex _root_.GlobalClassFieldTheory.GlobalClassFields.smallHilbertClassFieldNormSubgroupFiniteIndex _root_.GlobalClassFieldTheory.Reciprocity.infinitePlaceComplexificationOverfield_finiteDimensional _root_.GlobalClassFieldTheory.Reciprocity.infinitePlaceComplexificationOverfield_numberField _root_.GlobalClassFieldTheory.Reciprocity.ramifiedInfinitePlaceRealFixedField_numberField _root_.GlobalClassFieldTheory.Reciprocity.rationalIdeleClassDirectLimitMonoid _root_.GlobalClassFieldTheory.Reciprocity.rationalIntermediateFieldAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalIntermediateFieldNumberField _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalTowerClassGroupCommGroup _root_.GlobalClassFieldTheory.Reciprocity.rationalTowerClassGroupMul _root_.KummerTheory.primeCyclotomicBaseFiniteDimensional _root_.KummerTheory.primeCyclotomicBaseIsGalois _root_.KummerTheory.primeCyclotomicBaseNumberField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.boundedRealFields_numberField _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.GlobalClassFieldTheory.GlobalClassFields.bigHilbertNormQuotient_finite _root_.GlobalClassFieldTheory.GlobalClassFields.bigHilbertNormSubgroup_finiteIndex _root_.GlobalClassFieldTheory.Reciprocity.instNumberFieldSubtypeSeparableClosureRatMemIntermediateFieldAbstractFixedFieldOfFiniteQuotientAlgEquivSubgroupBaseFieldExtensionSubgroup _root_.GlobalClassFieldTheory.Reciprocity.instMonoidClassGroupRatSubtypeSeparableClosureMemIntermediateField _root_.GlobalClassFieldTheory.Reciprocity.rationalAbstractRelativeClassGroupCommGroup _root_.GlobalClassFieldTheory.Reciprocity.rationalAbstractRelativeClassGroupMul _root_.GlobalClassFieldTheory.Reciprocity.rationalAbstractRelativeClassGroupMulOneClass _root_.GlobalClassFieldTheory.Reciprocity.rationalAbstractTowerClassGroupCommGroup _root_.GlobalClassFieldTheory.Reciprocity.rationalAbstractTowerClassGroupMul _root_.GlobalClassFieldTheory.Reciprocity.rationalAbstractTowerClassGroupMulOneClass
attribute [-simp] _root_.GlobalClassFieldTheory.ClassFieldAxiom.actualPushoutNormQuotientMap_mk _root_.GlobalClassFieldTheory.ClassFieldAxiom.hasseNormDiagonal_mk _root_.GlobalClassFieldTheory.ClassFieldAxiom.sUnitEquivSupportedPrincipalIdeleSubgroup_coe _root_.GlobalClassFieldTheory.GlobalClassFields.ConductorialSubgroup.ideleClassQuotientEquivOfNarrowFiniteConductorsEqOfRayClassGroupCardsEqQuotientCards_mk _root_.GlobalClassFieldTheory.GlobalClassFields.ConductorialSubgroup.mem_fullConductorInfinitePart_iff _root_.GlobalClassFieldTheory.GlobalClassFields.ConductorialSubgroup.narrowFiniteConductorRayClassGroupEquivQuotientOfCardEq_mk _root_.GlobalClassFieldTheory.GlobalClassFields.ConductorialSubgroup.narrowFiniteConductorRayClassGroupToQuotient_mk _root_.GlobalClassFieldTheory.GlobalClassFields.bigHilbertClassFieldQuotientCongr_mk _root_.GlobalClassFieldTheory.GlobalClassFields.bigHilbertClassFieldQuotientEquivNarrowClassGroup_mk _root_.GlobalClassFieldTheory.GlobalClassFields.bigHilbertClassFieldQuotientToIdeleClassNormQuotient_mk _root_.GlobalClassFieldTheory.GlobalClassFields.bigHilbertClassFieldQuotientToSmallHilbertClassFieldQuotient_mk _root_.GlobalClassFieldTheory.GlobalClassFields.ideleClassNormQuotientTowerMap_mk _root_.GlobalClassFieldTheory.GlobalClassFields.narrowFiniteConductorRayClassGroupToIdeleClassNormQuotient_mk _root_.GlobalClassFieldTheory.GlobalClassFields.normQuotientEquivOfNarrowFiniteConductorsEqOfRayClassGroupCardsEqNormQuotientCards_mk _root_.GlobalClassFieldTheory.GlobalClassFields.realSignToBigHilbertClassFieldQuotient_apply _root_.GlobalClassFieldTheory.GlobalClassFields.realSignToNarrowClassKernel_apply _root_.GlobalClassFieldTheory.GlobalClassFields.smallHilbertClassFieldQuotientCongr_mk _root_.GlobalClassFieldTheory.GlobalClassFields.smallHilbertClassFieldQuotientEquivClassGroup_mk _root_.GlobalClassFieldTheory.GlobalClassFields.smallHilbertClassFieldQuotientToIdeleClassNormQuotient_mk _root_.GlobalClassFieldTheory.IdealClassFieldTheory.smallHilbertClassFieldIdeleExtensionMap_mk' _root_.GlobalClassFieldTheory.Reciprocity.chosenFinitePlaceArtinMonoidHom_eq_one_iff_chosenLocalNorm _root_.GlobalClassFieldTheory.Reciprocity.chosenInfinitePlaceArtinMonoidHom_eq_one_iff_infiniteTensorNorm _root_.GlobalClassFieldTheory.Reciprocity.cyclotomicZHatNormCompositeContinuous_apply _root_.GlobalClassFieldTheory.Reciprocity.cyclotomicZHatNormCompositeInMulNatRangeContinuous_apply _root_.GlobalClassFieldTheory.Reciprocity.globalNormClassFromIdele_principalIdele _root_.GlobalClassFieldTheory.Reciprocity.globalNormClassFromIdele_relativeIdeleNorm_eq_one _root_.GlobalClassFieldTheory.Reciprocity.mem_globalArtinFiniteSupport_iff _root_.GlobalClassFieldTheory.Reciprocity.normalizedCyclotomicZHatIdeleClassValueContinuousMul_mk _root_.GlobalClassFieldTheory.Reciprocity.normalizedCyclotomicZHatIdeleClassValueContinuous_mk _root_.GlobalClassFieldTheory.Reciprocity.normalizedCyclotomicZHatIdeleClassValue_range _root_.GlobalClassFieldTheory.Reciprocity.normalizedCyclotomicZHatIdeleValueContinuousMul_apply _root_.GlobalClassFieldTheory.Reciprocity.normalizedCyclotomicZHatIdeleValueContinuous_apply _root_.GlobalClassFieldTheory.Reciprocity.rationalAbstractFixedFieldIdeleClassEquivFixed_coe _root_.GlobalClassFieldTheory.Reciprocity.rationalCyclotomicIdeleClassValuationData_valuationAt_fixed_apply _root_.GlobalClassFieldTheory.Reciprocity.rationalCyclotomicZHatIdeleClassNormComposite_apply _root_.GlobalClassFieldTheory.Reciprocity.rationalCyclotomicZHatIdeleClassValueContinuousMul_mk _root_.GlobalClassFieldTheory.Reciprocity.rationalCyclotomicZHatIdeleClassValueContinuous_mk _root_.GlobalClassFieldTheory.Reciprocity.rationalCyclotomicZHatIdeleClassValue_range _root_.GlobalClassFieldTheory.Reciprocity.rationalCyclotomicZHatIdeleValueContinuousAdd_apply _root_.GlobalClassFieldTheory.Reciprocity.rationalCyclotomicZHatIdeleValueReduction_apply _root_.GlobalClassFieldTheory.Reciprocity.rationalFiniteNormQuotientEquivIdeleClassNormQuotient_finiteNormClass _root_.GlobalClassFieldTheory.Reciprocity.rationalIntermediateIdeleClassEquivGaloisFixed_coe _root_.IdeleClassGroup.normOneNorm_apply _root_.IdeleGroup.count_fractionalIdeal _root_.IdeleGroup.fractionalIdeal_finitePrimeIdele _root_.IdeleGroup.idealClass_finitePrimeIdele _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.OAI.PrimeDegreePackets.ThetaConstruction.schwartzCM_apply _root_.RayClass.signToNarrow_mk
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI
attribute [local instance] OAI.starSubalgebraCommCStarAlgebra

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

local instance rationalComplexificationPrimeFact_r03cd58_1 :
    Fact rationalComplexificationPrime.1.Prime :=
  ⟨rationalComplexificationPrime.2⟩
attribute [local instance] GlobalClassFieldTheory.Reciprocity.rationalComplexificationPrimeSquareNeZero
attribute [local instance] GlobalClassFieldTheory.Reciprocity.rationalComplexificationCyclotomicField_finiteDimensional
attribute [local instance] GlobalClassFieldTheory.Reciprocity.rationalComplexificationCyclotomicField_numberField
attribute [local instance] GlobalClassFieldTheory.Reciprocity.rationalComplexificationCyclotomicField_isAbelianGalois
/-- The chosen global Artin product for the actual rational
complexification is trivial on every rational principal idele. -/
@[simp]
theorem rationalComplexificationGlobalArtin_principalIdele
    (x : ℚˣ) :
    globalArtinMonoidHom
        (K := ℚ)
        (L := rationalComplexificationCyclotomicField)
        (IdeleGroup.principalIdele ℚ x) =
      1 := by
  rw [globalArtinMonoidHom_apply, Fintype.prod_unique]
  let u :=
    IdeleGroup.infiniteComponent
      Rat.infinitePlace
      (IdeleGroup.principalIdele ℚ x)
  let infiniteFactor :=
    chosenInfinitePlaceArtinMonoidHom
      (K := ℚ)
      (L := rationalComplexificationCyclotomicField)
      Rat.infinitePlace u
  let finiteFactor :=
    ∏ᶠ v : HeightOneSpectrum (𝓞 ℚ),
      chosenFinitePlaceArtinMonoidHom
        (K := ℚ)
        (L := rationalComplexificationCyclotomicField)
        v
        (IdeleGroup.finiteComponent v
          (IdeleGroup.principalIdele ℚ x))
  change infiniteFactor * finiteFactor = 1
  let character :=
    rationalComplexificationCharacter
  have hfiniteCharacter :
      character finiteFactor =
        Units.map (PadicInt.toZModPow 2).toMonoidHom
          (rationalSignPadicUnit x rationalComplexificationPrime) := by
    simpa only [character, finiteFactor] using
      rationalComplexificationFiniteArtin_character x
  have hnum : (x : ℚ).num ≠ 0 :=
    Rat.num_ne_zero.mpr x.ne_zero
  have hunique :=
    rationalComplexification_existsUnique_nontrivial
  rcases lt_or_gt_of_ne hnum with hnegative | hpositive
  · have hinfinite : infiniteFactor ≠ 1 := by
      simpa only [infiniteFactor, u] using
        rationalComplexificationPrincipalInfiniteArtin_ne_one_of_num_neg
          x hnegative
    have hsign :
        Units.map (PadicInt.toZModPow 2).toMonoidHom
            (rationalSignPadicUnit x rationalComplexificationPrime) ≠
          1 :=
      rationalComplexification_signCharacter_ne_one_of_num_neg
        x hnegative
    have hfinite : finiteFactor ≠ 1 := by
      intro h
      apply hsign
      rw [← hfiniteCharacter, h, map_one]
    have heq : infiniteFactor = finiteFactor :=
      hunique.unique hinfinite hfinite
    have hinvNe : finiteFactor⁻¹ ≠ 1 :=
      inv_ne_one.mpr hfinite
    have hinvEq : finiteFactor⁻¹ = finiteFactor :=
      hunique.unique hinvNe hfinite
    calc
      infiniteFactor * finiteFactor =
          finiteFactor⁻¹ * finiteFactor := by
        rw [heq, hinvEq]
      _ = 1 := inv_mul_cancel finiteFactor
  · have hinfinite : infiniteFactor = 1 := by
      simpa only [infiniteFactor, u] using
        rationalComplexificationPrincipalInfiniteArtin_eq_one_of_num_pos
          x hpositive
    have hsign :
        Units.map (PadicInt.toZModPow 2).toMonoidHom
            (rationalSignPadicUnit x rationalComplexificationPrime) =
          1 :=
      rationalComplexification_signCharacter_eq_one_of_num_pos
        x hpositive
    have hfinite : finiteFactor = 1 := by
      apply character.injective
      rw [hfiniteCharacter, hsign, map_one]
    rw [hinfinite, hfinite, mul_one]

end Reciprocity
end GlobalClassFieldTheory
end
end

section
-- module Solutions.OAIQ244_DUKE.GlobalClassFieldTheory_Reciprocity_ComplexificationArtin_InfinitePlaceOverfield
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.numberFieldTowerBaseFieldAlgebra _root_.GlobalClassFieldTheory.Reciprocity.ramifiedInfinitePlaceOverextension_isAbelianGalois _root_.GlobalClassFieldTheory.Reciprocity.ramifiedInfinitePlaceRealFixedField_algebra _root_.GlobalClassFieldTheory.Reciprocity.ramifiedInfinitePlaceRealFixedField_numberField _root_.GlobalClassFieldTheory.Reciprocity.ramifiedInfinitePlaceRealFixedField_ratScalarTower _root_.GlobalClassFieldTheory.Reciprocity.ramifiedInfinitePlaceRealFixedField_scalarTower _root_.GlobalClassFieldTheory.Reciprocity.rationalIdeleClassDirectLimitMonoid _root_.GlobalClassFieldTheory.Reciprocity.rationalIdeleClassDirectLimitSMul _root_.GlobalClassFieldTheory.Reciprocity.rationalIntermediateFieldAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalTowerClassGroupMul _root_.KummerTheory.primeCyclotomicBaseIsGalois _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.diagonalLogAction _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.GlobalClassFieldTheory.Reciprocity.instMonoidClassGroupRatSubtypeSeparableClosureMemIntermediateField _root_.GlobalClassFieldTheory.Reciprocity.instSMulAlgEquivRatSeparableClosureClassGroupSubtypeMemIntermediateField _root_.GlobalClassFieldTheory.Reciprocity.rationalAbstractRelativeClassGroupMul _root_.GlobalClassFieldTheory.Reciprocity.rationalAbstractTowerClassGroupMul
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI
attribute [local instance] OAI.starSubalgebraCommCStarAlgebra

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
/-- The cyclotomic fourth-root field embeds into the concrete
overfield through its copy in `ℂ`. -/
noncomputable def
    rationalComplexificationEmbeddingInInfinitePlaceOverfield
    (v : InfinitePlace K) :
    rationalComplexificationCyclotomicField →ₐ[ℚ]
      infinitePlaceComplexificationOverfield
        (K := K) (L := L) v :=
  (IntermediateField.inclusion
      (show
        complexFourthRootField ≤
          infinitePlaceComplexificationOverfield
            (K := K) (L := L) v from
        le_sup_right)).comp
    (rationalComplexificationComplexEquiv.toAlgHom)

noncomputable instance
    rationalComplexification_infinitePlaceOverfield_algebra
    (v : InfinitePlace K) :
    Algebra rationalComplexificationCyclotomicField
      (infinitePlaceComplexificationOverfield
        (K := K) (L := L) v) :=
  (rationalComplexificationEmbeddingInInfinitePlaceOverfield
    (K := K) (L := L) v).toRingHom.toAlgebra

/-- The scalar action induced by the concrete fourth-root-field
embedding.  Declaring it directly keeps instance search away from
unrelated intermediate-field algebra structures. -/
noncomputable instance
    rationalComplexification_infinitePlaceOverfield_smul
    (v : InfinitePlace K) :
    SMul rationalComplexificationCyclotomicField
      (infinitePlaceComplexificationOverfield
        (K := K) (L := L) v) :=
  (rationalComplexification_infinitePlaceOverfield_algebra
    (K := K) (L := L) v).toSMul

instance
    rationalComplexification_infinitePlaceOverfield_scalarTower
    (v : InfinitePlace K) :
    IsScalarTower ℚ rationalComplexificationCyclotomicField
      (infinitePlaceComplexificationOverfield
        (K := K) (L := L) v) :=
  IsScalarTower.of_algebraMap_eq'
    (rationalComplexificationEmbeddingInInfinitePlaceOverfield
      (K := K) (L := L) v).comp_algebraMap.symm

noncomputable instance
    infinitePlaceComplexificationOverfield_isTotallyComplex
    (v : InfinitePlace K) :
    IsTotallyComplex
      (infinitePlaceComplexificationOverfield
        (K := K) (L := L) v) :=
  NumberField.isTotallyComplex_of_algebra
    rationalComplexificationCyclotomicField
    (infinitePlaceComplexificationOverfield
      (K := K) (L := L) v)

end ComplexConjugationOverextension

end Reciprocity
end GlobalClassFieldTheory
end
end

section
-- module Solutions.OAIQ244_DUKE.GlobalClassFieldTheory_Reciprocity_ComplexificationArtin_RamifiedOverextension
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.numberFieldTowerBaseFieldAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalIdeleClassDirectLimitMonoid _root_.GlobalClassFieldTheory.Reciprocity.rationalIdeleClassDirectLimitSMul _root_.GlobalClassFieldTheory.Reciprocity.rationalIntermediateFieldAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalTowerClassGroupCommGroup _root_.GlobalClassFieldTheory.Reciprocity.rationalTowerClassGroupMul _root_.KummerTheory.primeCyclotomicBaseIsGalois _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.GlobalClassFieldTheory.Reciprocity.instMonoidClassGroupRatSubtypeSeparableClosureMemIntermediateField _root_.GlobalClassFieldTheory.Reciprocity.instSMulAlgEquivRatSeparableClosureClassGroupSubtypeMemIntermediateField _root_.GlobalClassFieldTheory.Reciprocity.rationalAbstractRelativeClassGroupCommGroup _root_.GlobalClassFieldTheory.Reciprocity.rationalAbstractRelativeClassGroupMul _root_.GlobalClassFieldTheory.Reciprocity.rationalAbstractRelativeClassGroupMulOneClass _root_.GlobalClassFieldTheory.Reciprocity.rationalAbstractTowerClassGroupCommGroup _root_.GlobalClassFieldTheory.Reciprocity.rationalAbstractTowerClassGroupMul _root_.GlobalClassFieldTheory.Reciprocity.rationalAbstractTowerClassGroupMulOneClass _root_.GlobalClassFieldTheory.Reciprocity.rationalOrdinaryNormQuotientAdditiveTypeAddCommGroup
attribute [-simp] _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.OAI.PrimeDegreePackets.ThetaConstruction.schwartzCM_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI
attribute [local instance] OAI.starSubalgebraCommCStarAlgebra

set_option autoImplicit false

/-!
# The quadratic overextension at a ramified real place

This module constructs the real fixed field of complex conjugation, the
quadratic overextension above it, and the faithful cyclotomic restriction.
-/

open scoped Classical IsMulCommutative
open NumberField

noncomputable section

namespace GlobalClassFieldTheory
namespace Reciprocity

attribute [local instance]
  infinitePlaceComplexificationOverfieldRationalAlgebra

section ComplexConjugationOverextension

variable
    {K L : Type}
    [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsAbelianGalois K L]

attribute [local instance]
  rationalComplexificationCyclotomicField_isAbelianGalois

/-- Restriction of the quadratic overextension Galois group to the
rational fourth-root factor. -/
noncomputable def
    ramifiedInfinitePlaceOverextensionCyclotomicRestriction
    (v : InfinitePlace K)
    (hRamified :
      (chosenInfinitePlaceAbove (L := L) v).IsRamified K) :
    Gal(
      (infinitePlaceComplexificationOverfield
        (K := K) (L := L) v) /
      (ramifiedInfinitePlaceRealFixedField
        (K := K) (L := L) v hRamified)) →*
      Gal(rationalComplexificationCyclotomicField / ℚ) :=
  (AlgEquiv.restrictNormalHom
    rationalComplexificationCyclotomicField).comp
      (AlgEquiv.restrictScalarsHom ℚ)

omit [NumberField K] [FiniteDimensional K L] in
/-- The mapped primitive fourth root in the overfield is not fixed by
ambient complex conjugation. -/
theorem ramifiedInfinitePlaceOverfieldConjugation_map_zeta_ne
    (v : InfinitePlace K)
    (hRamified :
      (chosenInfinitePlaceAbove (L := L) v).IsRamified K) :
    ramifiedInfinitePlaceOverfieldConjugation
        (K := K) (L := L) v hRamified
        (algebraMap rationalComplexificationCyclotomicField
          (infinitePlaceComplexificationOverfield
            (K := K) (L := L) v)
          (IsCyclotomicExtension.zeta
            4 ℚ rationalComplexificationCyclotomicField)) ≠
      algebraMap rationalComplexificationCyclotomicField
        (infinitePlaceComplexificationOverfield
          (K := K) (L := L) v)
        (IsCyclotomicExtension.zeta
          4 ℚ rationalComplexificationCyclotomicField) := by
  let ζ :=
    IsCyclotomicExtension.zeta
      4 ℚ rationalComplexificationCyclotomicField
  let j :
      infinitePlaceComplexificationOverfield
        (K := K) (L := L) v :=
    algebraMap rationalComplexificationCyclotomicField
      (infinitePlaceComplexificationOverfield
        (K := K) (L := L) v) ζ
  have hζ :
      IsPrimitiveRoot ζ 4 :=
    IsCyclotomicExtension.zeta_spec
      4 ℚ rationalComplexificationCyclotomicField
  have hj :
      IsPrimitiveRoot j 4 :=
    hζ.map_of_injective
      (algebraMap rationalComplexificationCyclotomicField
        (infinitePlaceComplexificationOverfield
          (K := K) (L := L) v)).injective
  have hj2 : j ^ 2 = -1 :=
    (hj.pow (by norm_num : 0 < 4)
      (show 4 = 2 * 2 by norm_num)).eq_neg_one_of_two_right
  intro hfixed
  have hfixedComplex :
      star (j : ℂ) = (j : ℂ) := by
    simpa only [j,
      ramifiedInfinitePlaceOverfieldConjugation_apply] using
      congrArg Subtype.val hfixed
  have hj2Complex : (j : ℂ) ^ 2 = -1 :=
    congrArg Subtype.val hj2
  have hjIm : (j : ℂ).im = 0 :=
    Complex.conj_eq_iff_im.mp hfixedComplex
  have hjRe := congrArg Complex.re hj2Complex
  simp only [pow_two, Complex.mul_re,
    Complex.neg_re, Complex.one_re] at hjRe
  nlinarith [hjIm, sq_nonneg (j : ℂ).re]

omit [NumberField K] [FiniteDimensional K L] in
/-- The distinguished overextension conjugation restricts
nontrivially to the rational fourth-root factor. -/
theorem
    ramifiedInfinitePlaceOverextensionCyclotomicRestriction_conjugation_ne_one
    (v : InfinitePlace K)
    (hRamified :
      (chosenInfinitePlaceAbove (L := L) v).IsRamified K) :
    ramifiedInfinitePlaceOverextensionCyclotomicRestriction
        (K := K) (L := L) v hRamified
        (ramifiedInfinitePlaceOverextensionConjugation
          (K := K) (L := L) v hRamified) ≠
      1 := by
  intro h
  apply
    ramifiedInfinitePlaceOverfieldConjugation_map_zeta_ne
      (K := K) (L := L) v hRamified
  have hz :=
    DFunLike.congr_fun h
      (IsCyclotomicExtension.zeta
        4 ℚ rationalComplexificationCyclotomicField)
  change
    ramifiedInfinitePlaceOverextensionCyclotomicRestriction
        (K := K) (L := L) v hRamified
        (ramifiedInfinitePlaceOverextensionConjugation
          (K := K) (L := L) v hRamified)
        (IsCyclotomicExtension.zeta
          4 ℚ rationalComplexificationCyclotomicField) =
      IsCyclotomicExtension.zeta
        4 ℚ rationalComplexificationCyclotomicField at hz
  have hz' :=
    congrArg
      (algebraMap rationalComplexificationCyclotomicField
        (infinitePlaceComplexificationOverfield
          (K := K) (L := L) v))
      hz
  change
    (algebraMap rationalComplexificationCyclotomicField
      (infinitePlaceComplexificationOverfield
        (K := K) (L := L) v))
        (((AlgEquiv.restrictNormalHom
          rationalComplexificationCyclotomicField)
            ((ramifiedInfinitePlaceOverextensionConjugation
              (K := K) (L := L) v hRamified).restrictScalars ℚ))
          (IsCyclotomicExtension.zeta
            4 ℚ rationalComplexificationCyclotomicField)) =
      (algebraMap rationalComplexificationCyclotomicField
        (infinitePlaceComplexificationOverfield
          (K := K) (L := L) v))
        (IsCyclotomicExtension.zeta
          4 ℚ rationalComplexificationCyclotomicField) at hz'
  calc
    ramifiedInfinitePlaceOverfieldConjugation
        (K := K) (L := L) v hRamified
        (algebraMap rationalComplexificationCyclotomicField
          (infinitePlaceComplexificationOverfield
            (K := K) (L := L) v)
          (IsCyclotomicExtension.zeta
            4 ℚ rationalComplexificationCyclotomicField)) =
      (ramifiedInfinitePlaceOverextensionConjugation
        (K := K) (L := L) v hRamified).restrictScalars ℚ
        (algebraMap rationalComplexificationCyclotomicField
          (infinitePlaceComplexificationOverfield
            (K := K) (L := L) v)
          (IsCyclotomicExtension.zeta
            4 ℚ rationalComplexificationCyclotomicField)) := by
      exact
        (ramifiedInfinitePlaceOverextensionConjugation_apply
          (K := K) (L := L) v hRamified _).symm
    _ =
        (algebraMap rationalComplexificationCyclotomicField
          (infinitePlaceComplexificationOverfield
            (K := K) (L := L) v))
          (((AlgEquiv.restrictNormalHom
            rationalComplexificationCyclotomicField)
              ((ramifiedInfinitePlaceOverextensionConjugation
                (K := K) (L := L) v hRamified).restrictScalars ℚ))
            (IsCyclotomicExtension.zeta
              4 ℚ rationalComplexificationCyclotomicField)) := by
      exact
        (AlgEquiv.restrictNormal_commutes
          ((ramifiedInfinitePlaceOverextensionConjugation
            (K := K) (L := L) v hRamified).restrictScalars ℚ)
          rationalComplexificationCyclotomicField
          (IsCyclotomicExtension.zeta
            4 ℚ rationalComplexificationCyclotomicField)).symm
    _ =
        (algebraMap rationalComplexificationCyclotomicField
          (infinitePlaceComplexificationOverfield
            (K := K) (L := L) v))
          (IsCyclotomicExtension.zeta
            4 ℚ rationalComplexificationCyclotomicField) := hz'

omit [NumberField K] [FiniteDimensional K L] in
/-- Restriction to the rational fourth-root factor is injective on the
quadratic overextension. -/
theorem
    ramifiedInfinitePlaceOverextensionCyclotomicRestriction_injective
    (v : InfinitePlace K)
    (hRamified :
      (chosenInfinitePlaceAbove (L := L) v).IsRamified K) :
    Function.Injective
      (ramifiedInfinitePlaceOverextensionCyclotomicRestriction
        (K := K) (L := L) v hRamified) := by
  apply
    (injective_iff_map_eq_one
      (ramifiedInfinitePlaceOverextensionCyclotomicRestriction
        (K := K) (L := L) v hRamified)).2
  intro σ hσ
  rcases
      ramifiedInfinitePlaceOverextension_eq_one_or_conjugation
        (K := K) (L := L) v hRamified σ with hσOne | hσConj
  · exact hσOne
  · subst σ
    exact
      (ramifiedInfinitePlaceOverextensionCyclotomicRestriction_conjugation_ne_one
        (K := K) (L := L) v hRamified hσ).elim

end ComplexConjugationOverextension

end Reciprocity
end GlobalClassFieldTheory
end
end

section
-- module Solutions.OAIQ244_DUKE.GlobalClassFieldTheory_Reciprocity_FiniteGaloisRealizationCore
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 400000
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.complexFourthRootField_finiteDimensional _root_.GlobalClassFieldTheory.Reciprocity.infinitePlaceComplexificationOverfield_algebra _root_.GlobalClassFieldTheory.Reciprocity.infinitePlaceComplexificationOverfield_baseAlgebra _root_.GlobalClassFieldTheory.Reciprocity.infinitePlaceComplexificationOverfield_baseSmul _root_.GlobalClassFieldTheory.Reciprocity.infinitePlaceComplexificationOverfield_finiteDimensional _root_.GlobalClassFieldTheory.Reciprocity.infinitePlaceComplexificationOverfield_smul _root_.GlobalClassFieldTheory.Reciprocity.numberFieldTowerBaseSubgroupAbsoluteQuotientFinite _root_.GlobalClassFieldTheory.Reciprocity.numberFieldTowerExtensionQuotientFinite _root_.GlobalClassFieldTheory.Reciprocity.numberFieldTowerExtensionSubgroupNormal _root_.GlobalClassFieldTheory.Reciprocity.ramifiedInfinitePlaceRealFixedField_algebra _root_.GlobalClassFieldTheory.Reciprocity.rationalComplexification_infinitePlaceOverfield_algebra _root_.GlobalClassFieldTheory.Reciprocity.rationalComplexification_infinitePlaceOverfield_smul _root_.KummerTheory.primeCyclotomicBaseFiniteDimensional _root_.KummerTheory.primeCyclotomicBaseIsGalois _root_.KummerTheory.primeCyclotomicBaseNumberField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.LubinTate.padicCompletedLevelField_algebra _root_.LubinTate.padicCompletedLevelField_finiteDimensional _root_.LubinTate.padicCompletedLevelField_isGalois _root_.LubinTate.padicCompletedLevelField_padicScalarTower _root_.LubinTate.padicCompletedStandardChangedCompositum_changedFieldAlgebra _root_.LubinTate.padicCompletedUnramifiedFieldAlgebra _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.diagonalLogAction _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.LocalClassFieldTheory.normalizationIntegerRingIsIntegralClosure _root_.chosenFinitePlaceCompletionAlgebra _root_.chosenFinitePlaceCompletionFiniteDimensional _root_.chosenFinitePlaceLocalizedFiniteDimensional _root_.chosenFinitePlaceLocalizedIntegerAlgebra _root_.chosenFinitePlaceLocalizedIsGalois _root_.cyclicPrimeDegreeIntermediate_isGalois _root_.cyclicPrimeSubextension_isGalois
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

noncomputable instance numberFieldTowerBaseField_finiteDimensional :
    FiniteDimensional ℚ (numberFieldTowerBaseField K L) :=
  (numberFieldTowerLowerEmbedding K L).equivFieldRange.toLinearEquiv.finiteDimensional

noncomputable instance numberFieldTowerBaseField_numberField :
    NumberField (numberFieldTowerBaseField K L) :=
  NumberField.of_module_finite ℚ (numberFieldTowerBaseField K L)

noncomputable instance numberFieldTowerTopField_isGalois :
    IsGalois (numberFieldTowerBaseField K L)
      (numberFieldInRationalSeparableClosure L) := by
  let _ : Algebra
      (numberFieldTowerLowerEmbedding K L).fieldRange
      (numberFieldSeparableClosureEmbedding L).fieldRange :=
    numberFieldTowerBaseFieldAlgebra K L
  exact
    IsGalois.of_equiv_equiv
      (F := K) (E := L)
      (M := (numberFieldTowerLowerEmbedding K L).fieldRange)
      (N := (numberFieldSeparableClosureEmbedding L).fieldRange)
      (f :=
        (numberFieldTowerLowerEmbedding K L).equivFieldRange.toRingEquiv)
      (g :=
        (numberFieldSeparableClosureEmbedding L).equivFieldRange.toRingEquiv)
      (by
        apply RingHom.ext
        intro x
        exact
          (numberFieldTowerFieldRangeEquiv_algebraMap K L x).symm)

/-- The algebra structure on the rational separable closure induced by
the chosen embedding of the top number field. -/
@[reducible]
noncomputable def numberFieldTowerSeparableClosureTopAlgebra :
    Algebra L (SeparableClosure ℚ) :=
  (numberFieldSeparableClosureEmbedding L).toRingHom.toAlgebra

omit [FiniteDimensional K L] [IsGalois K L] in
/-- The compatible lower embedding also realizes the standard
`ℚ → K` scalar tower inside the rational separable closure. -/
theorem numberFieldTowerSeparableClosureBaseScalarTower :
    letI : Algebra K (SeparableClosure ℚ) :=
      numberFieldTowerSeparableClosureBaseAlgebra K L
    IsScalarTower ℚ K (SeparableClosure ℚ) := by
  let : Algebra K (SeparableClosure ℚ) :=
    numberFieldTowerSeparableClosureBaseAlgebra K L
  exact
    IsScalarTower.of_algebraMap_eq'
      (numberFieldTowerLowerEmbedding K L).comp_algebraMap.symm

/-- The chosen top-field embedding realizes the standard
`ℚ → L` scalar tower inside the rational separable closure. -/
theorem numberFieldTowerSeparableClosureTopScalarTower :
    letI : Algebra L (SeparableClosure ℚ) :=
      numberFieldTowerSeparableClosureTopAlgebra L
    IsScalarTower ℚ L (SeparableClosure ℚ) := by
  let : Algebra L (SeparableClosure ℚ) :=
    numberFieldTowerSeparableClosureTopAlgebra L
  exact
    IsScalarTower.of_algebraMap_eq'
      (numberFieldSeparableClosureEmbedding L).comp_algebraMap.symm

/-- With the algebra structure induced by its chosen rational
embedding, the rational separable closure is a genuine Galois
overfield of a number field. -/
theorem numberFieldSeparableClosureTop_isGalois :
    letI : Algebra L (SeparableClosure ℚ) :=
      numberFieldTowerSeparableClosureTopAlgebra L
    IsGalois L (SeparableClosure ℚ) := by
  let : Algebra L (SeparableClosure ℚ) :=
    numberFieldTowerSeparableClosureTopAlgebra L
  let : IsScalarTower ℚ L (SeparableClosure ℚ) :=
    numberFieldTowerSeparableClosureTopScalarTower L
  let : Algebra.IsSeparable L (SeparableClosure ℚ) :=
    Algebra.isSeparable_tower_top_of_isSeparable
      ℚ L (SeparableClosure ℚ)
  let : IsSepClosure L (SeparableClosure ℚ) :=
    ⟨inferInstance, inferInstance⟩
  exact
    IsGalois.of_algEquiv
      (IsSepClosure.equiv L
        (SeparableClosure L) (SeparableClosure ℚ))

/-- The actual cyclotomic `ZHat`-compositum of a number field and the
chosen rational separable closure form the expected scalar tower. -/
theorem
    numberFieldCyclotomicZHatCompositumSeparableClosureScalarTower :
    letI : Algebra L (SeparableClosure ℚ) :=
      numberFieldTowerSeparableClosureTopAlgebra L
    IsScalarTower L
      (numberFieldCyclotomicZHatCompositum L)
      (SeparableClosure ℚ) := by
  let : Algebra L (SeparableClosure ℚ) :=
    numberFieldTowerSeparableClosureTopAlgebra L
  exact IsScalarTower.of_algebraMap_eq' rfl

omit [FiniteDimensional K L] [IsGalois K L] in
/-- The two compatible embeddings make the rational separable closure
an actual scalar tower over `K → L`. -/
theorem numberFieldTowerSeparableClosureScalarTower :
    letI : Algebra K (SeparableClosure ℚ) :=
      numberFieldTowerSeparableClosureBaseAlgebra K L
    letI : Algebra L (SeparableClosure ℚ) :=
      numberFieldTowerSeparableClosureTopAlgebra L
    IsScalarTower K L (SeparableClosure ℚ) := by
  let : Algebra K (SeparableClosure ℚ) :=
    numberFieldTowerSeparableClosureBaseAlgebra K L
  let : Algebra L (SeparableClosure ℚ) :=
    numberFieldTowerSeparableClosureTopAlgebra L
  exact IsScalarTower.of_algebraMap_eq' rfl

omit [FiniteDimensional K L] [IsGalois K L] in
/-- With the compatible lower embedding, the rational separable
closure is a genuine Galois overfield of the original base field. -/
theorem numberFieldTowerSeparableClosure_isGalois :
    letI : Algebra K (SeparableClosure ℚ) :=
      numberFieldTowerSeparableClosureBaseAlgebra K L
    IsGalois K (SeparableClosure ℚ) := by
  let : Algebra K (SeparableClosure ℚ) :=
    numberFieldTowerSeparableClosureBaseAlgebra K L
  exact
    IsGalois.of_algEquiv
      (numberFieldTowerSeparableClosureEquiv K L)

end Reciprocity
end GlobalClassFieldTheory
end
end

section
-- module Solutions.OAIQ244_DUKE.GlobalClassFieldTheory_Reciprocity_FiniteGaloisRealizationFinitePlace
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 400000
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.infinitePlaceComplexificationOverfield_baseSmul _root_.GlobalClassFieldTheory.Reciprocity.infinitePlaceComplexificationOverfield_smul _root_.GlobalClassFieldTheory.Reciprocity.numberFieldTowerBaseSubgroupAbsoluteQuotientFinite _root_.GlobalClassFieldTheory.Reciprocity.numberFieldTowerExtensionQuotientFinite _root_.GlobalClassFieldTheory.Reciprocity.numberFieldTowerExtensionSubgroupNormal _root_.GlobalClassFieldTheory.Reciprocity.rationalComplexification_infinitePlaceOverfield_smul _root_.GlobalClassFieldTheory.Reciprocity.rationalCyclotomicCompletionAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalCyclotomicLocalizedCompletionFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalCyclotomicLocalizedCompletionIsAlgebraic _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.LubinTate.padicCompletedLevelField_algebra _root_.LubinTate.padicCompletedUnramifiedFieldAlgebra _root_.LubinTate.standardLubinTateLevelValuationSubring_moduleFinite _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.LocalClassFieldTheory.normalizationIntegerRingIsIntegralClosure _root_.chosenFinitePlaceCompletionAlgebra _root_.chosenFinitePlaceCompletionContinuousSMul _root_.chosenFinitePlaceCompletionFiniteDimensional _root_.chosenFinitePlaceCompletionLocallyCompactSpace _root_.chosenFinitePlaceExtensionCompletionAlgebra _root_.chosenFinitePlaceExtensionCompletionSMul _root_.chosenFinitePlaceLocalizedFiniteDimensional _root_.chosenFinitePlaceLocalizedIntegerAlgebra _root_.chosenFinitePlaceLocalizedIntegerModuleFinite _root_.chosenFinitePlaceLocalizedIsGalois _root_.chosenFinitePlaceLocalizedIsIntegralClosure _root_.chosenFinitePlaceLocalizedIsNonarchimedeanLocalField _root_.chosenFinitePlaceLocalizedIsUltrametricDist _root_.chosenFinitePlaceLocalizedIsValuativeTopology _root_.chosenFinitePlaceLocalizedLocallyCompactSpace _root_.chosenFinitePlaceLocalizedValuationCompatible _root_.chosenFinitePlaceLocalizedValuationHasExtension _root_.chosenFinitePlaceLocalizedValuationIsNontrivial _root_.chosenFinitePlaceLocalizedValuativeRel _root_.chosenFinitePlaceLocalizedValuativeRelIsNontrivial _root_.chosenFinitePlaceLocalizedValued
attribute [-simp] _root_.GlobalClassFieldTheory.Reciprocity.numberFieldTowerAbstractFieldEquiv_algebraMap _root_.GlobalClassFieldTheory.Reciprocity.rationalCyclotomicGlobalToLocalizedAlgHom_apply _root_.GlobalClassFieldTheory.Reciprocity.rationalCyclotomicGlobalToLocalizedAlgHom_primitiveRoot _root_.GlobalClassFieldTheory.Reciprocity.rationalCyclotomicIdeleClassValuationData_valuationAt_fixed_apply _root_.GlobalClassFieldTheory.Reciprocity.rationalCyclotomicZHatValuation_range _root_.IsDiscreteValuationRing.addVal_ringEquiv _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.OAI.PrimeDegreePackets.ThetaConstruction.schwartzCM_apply _root_.RayClass.primesEquiv_val_eq_natGenerator _root_.chosenFinitePlaceIntegerToLocalizedCompletion_coe _root_.chosenFinitePlaceLocalizedResidueEquiv_apply_mk _root_.doubleCosetExtension_mk _root_.extendAbsoluteValueExtensionFromIntermediate_apply _root_.mem_finitePlaceDecompositionGroup_iff _root_.restrictAbsoluteValueExtensionToIntermediate_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

/-!
# Finite places in the compatible Galois realization

This module extends a chosen finite place of `L` to the common rational
separable closure and compares its decomposition data with the corresponding
places and completions in the original number-field tower.
-/

open scoped NumberField
open NumberField

noncomputable section

namespace GlobalClassFieldTheory
namespace Reciprocity

open ClassFormation
open AlgebraicNumberTheory
open AlgebraicNumberTheory.Valuations
open IsDedekindDomain
open LocalClassFieldTheory
open RamificationTheory

variable
    (K L : Type*) [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]

/-- Extend a specified finite place of the compatible top number
field to the common rational separable closure.

Its restriction to `L` is definitionally the supplied exact extension,
so the resulting decomposition-group restriction lands at the
specified place rather than at an unrelated conjugate. -/
noncomputable def
    numberFieldTowerFinitePlaceExtensionToSeparableClosure
    (v : HeightOneSpectrum (𝓞 K))
    (w : AbsoluteValueExtension
      (NumberField.HeightOneSpectrum.adicAbv K v) L) :
    letI : Algebra K (SeparableClosure ℚ) :=
      numberFieldTowerSeparableClosureBaseAlgebra K L
    letI : Algebra L (SeparableClosure ℚ) :=
      numberFieldTowerSeparableClosureTopAlgebra L
    letI : IsScalarTower K L (SeparableClosure ℚ) :=
      numberFieldTowerSeparableClosureScalarTower K L
    AbsoluteValueExtension
      (NumberField.HeightOneSpectrum.adicAbv K v)
      (SeparableClosure ℚ) := by
  letI : Algebra K (SeparableClosure ℚ) :=
    numberFieldTowerSeparableClosureBaseAlgebra K L
  letI : Algebra L (SeparableClosure ℚ) :=
    numberFieldTowerSeparableClosureTopAlgebra L
  letI : IsScalarTower K L (SeparableClosure ℚ) :=
    numberFieldTowerSeparableClosureScalarTower K L
  letI : IsScalarTower ℚ L (SeparableClosure ℚ) :=
    numberFieldTowerSeparableClosureTopScalarTower L
  letI : Algebra.IsAlgebraic L (SeparableClosure ℚ) :=
    Algebra.IsAlgebraic.tower_top (K := ℚ) L
  exact
    w.extendToAlgebraicallyClosed
      (NumberField.HeightOneSpectrum.adicAbv K v)
      (RayClass.adicAbv_isNontrivial v)

omit [FiniteDimensional K L] [IsGalois K L] in
/-- The compatible separable-closure extension restricts to the
specified finite-place extension on `L`. -/
@[simp]
theorem
    numberFieldTowerFinitePlaceExtensionToSeparableClosure_algebraMap
    (v : HeightOneSpectrum (𝓞 K))
    (w : AbsoluteValueExtension
      (NumberField.HeightOneSpectrum.adicAbv K v) L)
    (x : L) :
    letI : Algebra K (SeparableClosure ℚ) :=
      numberFieldTowerSeparableClosureBaseAlgebra K L
    letI : Algebra L (SeparableClosure ℚ) :=
      numberFieldTowerSeparableClosureTopAlgebra L
    letI : IsScalarTower K L (SeparableClosure ℚ) :=
      numberFieldTowerSeparableClosureScalarTower K L
    (numberFieldTowerFinitePlaceExtensionToSeparableClosure
      K L v w).1
        (algebraMap L (SeparableClosure ℚ) x) =
      w.1 x := by
  let : Algebra K (SeparableClosure ℚ) :=
    numberFieldTowerSeparableClosureBaseAlgebra K L
  let : Algebra L (SeparableClosure ℚ) :=
    numberFieldTowerSeparableClosureTopAlgebra L
  let : IsScalarTower K L (SeparableClosure ℚ) :=
    numberFieldTowerSeparableClosureScalarTower K L
  let : IsScalarTower ℚ L (SeparableClosure ℚ) :=
    numberFieldTowerSeparableClosureTopScalarTower L
  let : Algebra.IsAlgebraic L (SeparableClosure ℚ) :=
    Algebra.IsAlgebraic.tower_top (K := ℚ) L
  exact
    AbsoluteValueExtension.extendToAlgebraicallyClosed_algebraMap
      (NumberField.HeightOneSpectrum.adicAbv K v)
      (RayClass.adicAbv_isNontrivial v) w x

omit [FiniteDimensional K L] [IsGalois K L] in
/-- Restricting the compatible separable-closure absolute value along
the chosen top-field embedding recovers the supplied exact extension. -/
theorem
    numberFieldTowerFinitePlaceExtensionToSeparableClosure_restrict
    (v : HeightOneSpectrum (𝓞 K))
    (w : AbsoluteValueExtension
      (NumberField.HeightOneSpectrum.adicAbv K v) L) :
    letI : Algebra K (SeparableClosure ℚ) :=
      numberFieldTowerSeparableClosureBaseAlgebra K L
    letI : Algebra L (SeparableClosure ℚ) :=
      numberFieldTowerSeparableClosureTopAlgebra L
    letI : IsScalarTower K L (SeparableClosure ℚ) :=
      numberFieldTowerSeparableClosureScalarTower K L
    (numberFieldTowerFinitePlaceExtensionToSeparableClosure
        K L v w).1.comp
        (f := algebraMap L (SeparableClosure ℚ))
        (algebraMap L (SeparableClosure ℚ)).injective =
      w.1 := by
  let : Algebra K (SeparableClosure ℚ) :=
    numberFieldTowerSeparableClosureBaseAlgebra K L
  let : Algebra L (SeparableClosure ℚ) :=
    numberFieldTowerSeparableClosureTopAlgebra L
  let : IsScalarTower K L (SeparableClosure ℚ) :=
    numberFieldTowerSeparableClosureScalarTower K L
  ext x
  exact
    numberFieldTowerFinitePlaceExtensionToSeparableClosure_algebraMap
      K L v w x

end Reciprocity
end GlobalClassFieldTheory
end
end

section
-- module Solutions.OAIQ244_DUKE.GlobalClassFieldTheory_Reciprocity_FiniteGaloisRealizationSubextension
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 400000
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.GlobalClassFields.finiteAbelianSubextensionAbstractRelativeFixedFieldFiniteDimensional _root_.GlobalClassFieldTheory.Reciprocity.numberFieldTowerBaseSubgroupAbsoluteQuotientFinite _root_.GlobalClassFieldTheory.Reciprocity.numberFieldTowerExtensionQuotientFinite _root_.GlobalClassFieldTheory.Reciprocity.numberFieldTowerExtensionSubgroupNormal _root_.KummerTheory.primeCyclotomicBaseFiniteDimensional _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.LubinTate.padicCompletedLevelField_algebra _root_.LubinTate.padicCompletedLevelField_finiteDimensional _root_.LubinTate.padicCompletedUnramifiedFieldAlgebra _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.instTopologicalSpaceLocalAlgebra _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.LocalClassFieldTheory.normalizationIntegerRingIsIntegralClosure _root_.chosenFinitePlaceCompletionAlgebra _root_.chosenFinitePlaceCompletionFiniteDimensional _root_.chosenFinitePlaceLocalizedFiniteDimensional
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

omit [FiniteDimensional K L] [IsGalois K L] in
/-- The compatible embedded absolute Galois subgroup of a number
field is open in the rational absolute Galois group. -/
theorem numberFieldTowerBaseSubgroup_isOpen :
    IsOpen
      ((numberFieldTowerBaseSubgroup K L :
          ClosedSubgroup
            (Gal(SeparableClosure ℚ / ℚ))) :
        Set (Gal(SeparableClosure ℚ / ℚ))) :=
  abstractFiniteClosedSubgroup_isOpen
    ℚ (SeparableClosure ℚ)
    (numberFieldTowerBaseSubgroup K L)
    (numberFieldTowerFiniteAbstractField K L).finite

/-- Under the compatible realization, the finite quotient class of an
absolute automorphism is its genuine restriction to `L`. -/
theorem
    numberFieldTowerExtensionQuotientEquivGaloisGroup_mk_baseSubgroupEquiv
    (σ :
      letI : Algebra K (SeparableClosure ℚ) :=
        numberFieldTowerSeparableClosureBaseAlgebra K L
      Gal(SeparableClosure ℚ / K)) :
    letI : Algebra K (SeparableClosure ℚ) :=
      numberFieldTowerSeparableClosureBaseAlgebra K L
    letI : Algebra L (SeparableClosure ℚ) :=
      numberFieldTowerSeparableClosureTopAlgebra L
    letI : IsScalarTower K L (SeparableClosure ℚ) :=
      numberFieldTowerSeparableClosureScalarTower K L
    letI :=
      numberFieldTowerExtensionSubgroup_normal K L
    numberFieldTowerExtensionQuotientEquivGaloisGroup K L
        (QuotientGroup.mk
          (numberFieldTowerSeparableClosureEquivBaseSubgroup
            K L σ)) =
      AlgEquiv.restrictNormalHom L σ := by
  let j :=
    numberFieldSeparableClosureEmbedding L
  let : Algebra K (SeparableClosure ℚ) :=
    numberFieldTowerSeparableClosureBaseAlgebra K L
  let : Algebra L (SeparableClosure ℚ) :=
    numberFieldTowerSeparableClosureTopAlgebra L
  let : IsScalarTower K L (SeparableClosure ℚ) :=
    numberFieldTowerSeparableClosureScalarTower K L
  let e :=
    numberFieldTowerSeparableClosureEquiv K L
  let :=
    numberFieldTowerExtensionSubgroup_normal K L
  apply AlgEquiv.ext
  intro x
  apply j.injective
  calc
    j
        (numberFieldTowerExtensionQuotientEquivGaloisGroup K L
          (QuotientGroup.mk
            (numberFieldTowerSeparableClosureEquivBaseSubgroup
              K L σ)) x) =
        (numberFieldTowerSeparableClosureEquivBaseSubgroup
          K L σ).1.1 (j x) := by
      convert
        (ambientEmbeddedExtensionQuotientEquivGaloisGroup_mk_apply
          ℚ K L j e
          (numberFieldTowerSeparableClosureEquivBaseSubgroup
            K L σ) x) using 1 <;> rfl
    _ = σ (j x) := rfl
    _ =
        j
          ((AlgEquiv.restrictNormalHom L σ) x) := by
      exact
        (AlgEquiv.restrictNormal_commutes σ L x).symm

end Reciprocity
end GlobalClassFieldTheory
end
end

section
-- module Solutions.OAIQ244_DUKE.GlobalClassFieldTheory_Reciprocity_FiniteGaloisRealization
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 400000
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.GlobalClassFields.ConductorialSubgroup.finiteIndex _root_.GlobalClassFieldTheory.GlobalClassFields.bigHilbertClassFieldNormSubgroup_normal _root_.GlobalClassFieldTheory.GlobalClassFields.finiteAbelianSubextensionAbstractRelativeFixedFieldFiniteDimensional _root_.GlobalClassFieldTheory.GlobalClassFields.finiteAbelianSubextensionAbstractRelativeFixedFieldIsAbelianGalois _root_.GlobalClassFieldTheory.GlobalClassFields.ideleClassNorm_rangeFiniteIndex _root_.GlobalClassFieldTheory.GlobalClassFields.smallHilbertClassFieldNormSubgroupFiniteIndex _root_.GlobalClassFieldTheory.Reciprocity.infinitePlaceComplexificationOverfield_algebra _root_.GlobalClassFieldTheory.Reciprocity.infinitePlaceComplexificationOverfield_baseAlgebra _root_.GlobalClassFieldTheory.Reciprocity.infinitePlaceComplexificationOverfield_baseSmul _root_.GlobalClassFieldTheory.Reciprocity.infinitePlaceComplexificationOverfield_smul _root_.GlobalClassFieldTheory.Reciprocity.ramifiedInfinitePlaceRealFixedField_algebra _root_.GlobalClassFieldTheory.Reciprocity.rationalComplexification_infinitePlaceOverfield_algebra _root_.GlobalClassFieldTheory.Reciprocity.rationalComplexification_infinitePlaceOverfield_smul _root_.KummerTheory.finite_finsupp_nsmulQuotient _root_.KummerTheory.finite_sUnit_nthPowerQuotient _root_.KummerTheory.primeCyclotomicBaseIsGalois _root_.KummerTheory.primeCyclotomicBaseNumberField _root_.LocalClassFieldTheory.finiteUnramifiedNormQuotient _root_.LocalFieldTheory.DiscreteValuationField.finite_padicInt_finPi_nsmulQuotient _root_.LocalFieldTheory.DiscreteValuationField.finite_padicInt_pi_nsmulQuotient_of_coprime _root_.LocalFieldTheory.DiscreteValuationField.finite_valuationSubringUnits_nthPowerQuotient _root_.LocalFieldTheory.finite_multiplicative_nthPowerQuotient _root_.LocalFieldTheory.finite_nsmulAddQuotient_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.LubinTate.padicCompletedLevelField_algebra _root_.LubinTate.padicCompletedLevelField_isGalois _root_.LubinTate.padicCompletedLevelField_padicScalarTower _root_.LubinTate.padicCompletedStandardChangedCompositum_changedFieldAlgebra _root_.LubinTate.padicCompletedUnramifiedFieldAlgebra _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.boundedRealFields_finite _root_.OAI.PrimeDegreePackets.diagonalLogAction _root_.OAI.PrimeDegreePackets.instTopologicalSpaceLocalAlgebra _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.CyclicCohomology.binaryCoefficientFamilyCommGroup _root_.GlobalClassFieldTheory.GlobalClassFields.bigHilbertNormQuotient_finite _root_.GlobalClassFieldTheory.GlobalClassFields.bigHilbertNormSubgroup_finiteIndex _root_.GlobalClassFieldTheory.GlobalClassFields.narrowClassGroup_finite _root_.LocalClassFieldTheory.normalizationIntegerRingIsIntegralClosure _root_.chosenFinitePlaceCompletionAlgebra _root_.chosenFinitePlaceLocalizedIntegerAlgebra _root_.chosenFinitePlaceLocalizedIsGalois _root_.cyclicPrimeDegreeIntermediate_isGalois _root_.cyclicPrimeSubextension_isGalois _root_.relativeUnrestrictedSPlaceFactorCommGroup
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI
attribute [local instance] OAI.starSubalgebraCommCStarAlgebra

set_option autoImplicit false

/-!
# Reciprocity for a realized finite Galois number-field tower

This module equips the compatible fixed-field realization of `L / K` with the
finite-dimensional and number-field instances needed by global class formation,
then transports abstract reciprocity back to the original tower.
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

/-- Fix the canonical class-group structure before forming norm quotients. -/
@[instance_reducible]
noncomputable def realizedTowerIdeleClassCommGroup
    (F : Type) [Field F] [NumberField F] :
    CommGroup (IdeleClassGroup F) :=
  QuotientGroup.Quotient.commGroup (IdeleGroup.principalSubgroup F)

attribute [local instance] realizedTowerIdeleClassCommGroup

theorem realizedTowerIdeleClassIsMulCommutative
    (F : Type) [Field F] [NumberField F] :
    IsMulCommutative (IdeleClassGroup F) :=
  IsMulCommutative.of_comm (fun a b => mul_comm a b)

attribute [local instance] realizedTowerIdeleClassIsMulCommutative

variable
    (K L : Type) [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]

omit [FiniteDimensional K L] [IsGalois K L] in
theorem numberFieldTowerAbstractBaseFiniteDimensional :
    FiniteDimensional ℚ
      (abstractFixedField ℚ (SeparableClosure ℚ)
        (numberFieldTowerBaseSubgroup K L)) :=
  abstractFixedField_finiteDimensional
    ℚ (SeparableClosure ℚ)
    (numberFieldTowerBaseSubgroup K L)
    (numberFieldTowerBaseSubgroupAbsoluteQuotientFinite K L)

theorem numberFieldTowerAbstractRelativeFiniteDimensional :
    FiniteDimensional
      (abstractFixedField ℚ (SeparableClosure ℚ)
        (numberFieldTowerBaseSubgroup K L))
      (abstractRelativeFixedField ℚ (SeparableClosure ℚ)
        (numberFieldTowerTopSubgroup_le_baseSubgroup K L)) :=
  abstractRelativeFixedField_finiteDimensional
    ℚ (SeparableClosure ℚ)
    (numberFieldTowerBaseSubgroup K L)
    (numberFieldTowerTopSubgroup L)
    (numberFieldTowerTopSubgroup_le_baseSubgroup K L)
    (numberFieldTowerBaseSubgroupAbsoluteQuotientFinite K L)
    (numberFieldTowerExtensionQuotientFinite K L)

omit [FiniteDimensional K L] [IsGalois K L] in
theorem numberFieldTowerAbstractScalarTower :
    IsScalarTower ℚ
      (abstractFixedField ℚ (SeparableClosure ℚ)
        (numberFieldTowerBaseSubgroup K L))
      (abstractRelativeFixedField ℚ (SeparableClosure ℚ)
        (numberFieldTowerTopSubgroup_le_baseSubgroup K L)) :=
  IsScalarTower.of_algebraMap_eq' rfl

theorem numberFieldTowerAbstractTopFiniteDimensional :
    FiniteDimensional ℚ
      (abstractRelativeFixedField ℚ (SeparableClosure ℚ)
        (numberFieldTowerTopSubgroup_le_baseSubgroup K L)) := by
  let := numberFieldTowerAbstractBaseFiniteDimensional K L
  let := numberFieldTowerAbstractRelativeFiniteDimensional K L
  let := numberFieldTowerAbstractScalarTower K L
  exact FiniteDimensional.trans ℚ
    (abstractFixedField ℚ (SeparableClosure ℚ)
      (numberFieldTowerBaseSubgroup K L))
    (abstractRelativeFixedField ℚ (SeparableClosure ℚ)
      (numberFieldTowerTopSubgroup_le_baseSubgroup K L))

omit [FiniteDimensional K L] [IsGalois K L] in
theorem numberFieldTowerAbstractBaseNumberField :
    NumberField
      (abstractFixedField ℚ (SeparableClosure ℚ)
        (numberFieldTowerBaseSubgroup K L)) := by
  let := numberFieldTowerAbstractBaseFiniteDimensional K L
  exact NumberField.of_module_finite ℚ _

theorem numberFieldTowerAbstractTopNumberField :
    NumberField
      (abstractRelativeFixedField ℚ (SeparableClosure ℚ)
        (numberFieldTowerTopSubgroup_le_baseSubgroup K L)) := by
  let := numberFieldTowerAbstractTopFiniteDimensional K L
  exact NumberField.of_module_finite ℚ _

@[reducible] noncomputable def numberFieldTowerRestrictedTopAlgebra :
    Algebra
      (abstractFixedField ℚ (SeparableClosure ℚ)
        (numberFieldTowerBaseSubgroup K L))
      ((abstractRelativeFixedField ℚ (SeparableClosure ℚ)
        (numberFieldTowerTopSubgroup_le_baseSubgroup K L)).restrictScalars ℚ) :=
  (IntermediateField.inclusion
    (abstractFixedField_le ℚ (SeparableClosure ℚ)
      (numberFieldTowerTopSubgroup_le_baseSubgroup K L))).toRingHom.toAlgebra

theorem ordinaryIdeleClassNormQuotientCongrOfAlgEquiv_symm_mk
    {K₀ L₀ K₁ L₁ : Type}
    [Field K₀] [NumberField K₀]
    [Field L₀] [NumberField L₀] [Algebra K₀ L₀]
    [Field K₁] [NumberField K₁]
    [Field L₁] [NumberField L₁] [Algebra K₁ L₁]
    (eK : K₀ ≃ₐ[ℚ] K₁)
    (eL : L₀ ≃ₐ[ℚ] L₁)
    (h : ∀ x : K₀,
      eL (algebraMap K₀ L₀ x) =
        algebraMap K₁ L₁ (eK x))
    (c : IdeleClassGroup K₁) :
    (ordinaryIdeleClassNormQuotientCongrOfAlgEquiv eK eL h).symm
        (QuotientGroup.mk'
          (_root_.ideleClassNorm K₁ L₁).range c) =
      QuotientGroup.mk'
        (_root_.ideleClassNorm K₀ L₀).range
        ((ideleClassCongr eK).symm c) := by
  let e := ordinaryIdeleClassNormQuotientCongrOfAlgEquiv eK eL h
  apply e.injective
  rw [e.apply_symm_apply,
    ordinaryIdeleClassNormQuotientCongrOfAlgEquiv_mk,
    MulEquiv.apply_symm_apply]

noncomputable def numberFieldTowerFiniteNormClassPublicValue
    (a : KummerTheory.ambientFixedAddSubgroup
      rationalIdeleClassRepresentation
      (numberFieldTowerBaseSubgroup K L)) :
    Additive
      (IdeleClassGroup K ⧸
        (_root_.ideleClassNorm K L).range) :=
  numberFieldTowerFiniteNormQuotientEquivIdeleClassNormQuotient K L
    (finiteNormClass rationalIdeleClassRepresentation
      (numberFieldTowerBaseSubgroup K L)
      (numberFieldTowerTopSubgroup L)
      (numberFieldTowerTopSubgroup_le_baseSubgroup K L) a)

end Reciprocity
end GlobalClassFieldTheory
end
end

section
-- module Solutions.OAIQ244_DUKE.GlobalClassFieldTheory_Reciprocity_FinitePlaceCyclotomicFrobeniusLift
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.GlobalClassFields.ConductorialSubgroup.finiteIndex _root_.GlobalClassFieldTheory.GlobalClassFields.bigHilbertClassFieldNormSubgroup_normal _root_.GlobalClassFieldTheory.GlobalClassFields.ideleClassNorm_rangeFiniteIndex _root_.GlobalClassFieldTheory.GlobalClassFields.smallHilbertClassFieldNormSubgroupFiniteIndex _root_.GlobalClassFieldTheory.Reciprocity.complexFourthRootField_isCyclotomic _root_.GlobalClassFieldTheory.Reciprocity.infinitePlaceComplexificationOverfield_algebra _root_.GlobalClassFieldTheory.Reciprocity.infinitePlaceComplexificationOverfield_baseAlgebra _root_.GlobalClassFieldTheory.Reciprocity.infinitePlaceComplexificationOverfield_finiteDimensional_over_extension _root_.GlobalClassFieldTheory.Reciprocity.ramifiedInfinitePlaceRealFixedField_algebra _root_.GlobalClassFieldTheory.Reciprocity.rationalComplexificationCyclotomicField_isCMField _root_.GlobalClassFieldTheory.Reciprocity.rationalComplexificationCyclotomicField_isCyclotomicFour _root_.GlobalClassFieldTheory.Reciprocity.rationalComplexification_infinitePlaceOverfield_algebra _root_.GlobalClassFieldTheory.Reciprocity.rationalComplexification_infinitePlaceOverfield_scalarTower _root_.GlobalClassFieldTheory.Reciprocity.rationalComplexification_infinitePlaceOverfield_smul _root_.GlobalClassFieldTheory.Reciprocity.rationalIdeleClassDirectLimitMonoid _root_.GlobalClassFieldTheory.Reciprocity.rationalIntermediateFieldAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalTowerClassGroupCommGroup _root_.GlobalClassFieldTheory.Reciprocity.rationalTowerClassGroupMul _root_.KummerTheory.DiscreteNthRootsSubgroup.instTopologicalSpaceSubtypeUnitsMemSubgroup _root_.KummerTheory.primeCyclotomicBaseFiniteDimensional _root_.KummerTheory.primeCyclotomicBaseNumberField _root_.LocalFieldTheory.DiscreteValuationField.finite_principalUnits_nthPowerKernel _root_.LocalFieldTheory.DiscreteValuationField.finite_residueRootsOfUnityGroup _root_.LocalFieldTheory.DiscreteValuationField.finite_valuationSubringUnits_nthPowerKernel _root_.LocalFieldTheory.DiscreteValuationField.finite_valuationSubringUnits_nthPowerQuotient _root_.LocalFieldTheory.Padic.padicDVR_residueField_finite _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.instIsTopologicalRingLocalAlgebra _root_.OAI.PrimeDegreePackets.instTopologicalSpaceLocalAlgebra _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.labelPrime_fact _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.GlobalClassFieldTheory.GlobalClassFields.bigHilbertNormQuotient_finite _root_.GlobalClassFieldTheory.GlobalClassFields.bigHilbertNormSubgroup_finiteIndex _root_.GlobalClassFieldTheory.Reciprocity.instMonoidClassGroupRatSubtypeSeparableClosureMemIntermediateField _root_.GlobalClassFieldTheory.Reciprocity.rationalAbstractRelativeClassGroupCommGroup _root_.GlobalClassFieldTheory.Reciprocity.rationalAbstractRelativeClassGroupMul _root_.GlobalClassFieldTheory.Reciprocity.rationalAbstractRelativeClassGroupMulOneClass _root_.GlobalClassFieldTheory.Reciprocity.rationalAbstractTowerClassGroupCommGroup _root_.GlobalClassFieldTheory.Reciprocity.rationalAbstractTowerClassGroupMul _root_.GlobalClassFieldTheory.Reciprocity.rationalAbstractTowerClassGroupMulOneClass _root_.GlobalClassFieldTheory.Reciprocity.rationalOrdinaryNormQuotientAdditiveTypeAddCommGroup
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

/-!
# Decomposition-compatible cyclotomic Frobenius lifts

The finite-place reduction in the local--global compatibility theorem
uses automorphisms in a specified decomposition group, not arbitrary
lifts in the ambient absolute Galois group.

This file begins with the source map needed for that construction.
For a normal intermediate field, restriction maps the decomposition
group upstairs onto the decomposition group of the restricted
valuation.  The proof uses the actual valuation-conjugacy correction
in `absoluteValueDecompositionGroup_map_restrictNormalHom`.
-/

open AlgebraicNumberTheory.Valuations
open AlgebraicNumberTheory
open HilbertRamification
open ClassFormation
open NumberField IsDedekindDomain
open scoped NumberField

noncomputable section

namespace GlobalClassFieldTheory
namespace Reciprocity

local instance localInst_r03cd58_1 (p : Nat.Primes) : Fact p.1.Prime :=
  ⟨p.2⟩
local instance rationalCyclotomicFrobeniusLiftPrimePowerNumberField_r03cd58_1
    (p : Nat.Primes) (k : ℕ) :
    NumberField (KummerTheory.rationalCyclotomicLevel
      ⟨p.1 ^ k, pow_pos p.2.pos k⟩) :=
  KummerTheory.rationalCyclotomicLevel_numberField
    ⟨p.1 ^ k, pow_pos p.2.pos k⟩
local instance rationalCyclotomicFrobeniusLiftPrimePowerFiniteDimensional_r03cd58_1
    (p : Nat.Primes) (k : ℕ) :
    FiniteDimensional ℚ (KummerTheory.rationalCyclotomicLevel
      ⟨p.1 ^ k, pow_pos p.2.pos k⟩) :=
  rationalCyclotomicPrincipalPrimeLevelFiniteDimensional
    ⟨p.1 ^ k, pow_pos p.2.pos k⟩
local instance rationalCyclotomicFrobeniusLiftPrimePowerIsAbelianGalois_r03cd58_1
    (p : Nat.Primes) (k : ℕ) :
    IsAbelianGalois ℚ (KummerTheory.rationalCyclotomicLevel
      ⟨p.1 ^ k, pow_pos p.2.pos k⟩) :=
  rationalCyclotomicLevelIsAbelianGalois
    ⟨p.1 ^ k, pow_pos p.2.pos k⟩
noncomputable local instance
    rationalCyclotomicFrobeniusLiftLevelFiniteDimensional_r03cd58_1
    (m : ℕ+) :
    FiniteDimensional ℚ
      (KummerTheory.rationalCyclotomicLevel m) :=
  rationalCyclotomicPrincipalPrimeLevelFiniteDimensional m
noncomputable local instance
    rationalCyclotomicFrobeniusLiftLevelIsAbelianGalois_r03cd58_1
    (m : ℕ+) :
    IsAbelianGalois ℚ
      (KummerTheory.rationalCyclotomicLevel m) :=
  rationalCyclotomicLevelIsAbelianGalois m
variable
    {K L Ω : Type}
    [Field K] [Field L] [Field Ω]
    [Algebra K L] [Algebra L Ω] [Algebra K Ω]
    [IsScalarTower K L Ω] [Normal K L]

/-- Reduction of the full cyclotomic character of a rational one-place
idèle whose component is a power of a principal local component.  The
result is the same power of the genuine chosen local Artin character. -/
theorem
    rationalCyclotomicCharacterPrimeProduct_finitePlaceIdele_principalComponent_toZModPow
    (p q : Nat.Primes) (k d : ℕ) (x : ℚˣ) :
    Units.map (PadicInt.toZModPow k).toMonoidHom
        (KummerTheory.rationalCyclotomicCharacterPrimeProduct
          (infiniteGlobalArtinMonoidHom
            ℚ KummerTheory.rationalCyclotomicField
            (IdeleGroup.finitePlaceIdele
              (RayClass.rationalPrime q)
              ((IdeleGroup.finiteComponent
                (RayClass.rationalPrime q)
                (IdeleGroup.principalIdele ℚ x)) ^ d))) p) =
      (rationalCyclotomicPrincipalFinitePlaceCharacter
        p k x q) ^ d := by
  have hprime :
      RayClass.rationalPrime q =
        ((Rat.HeightOneSpectrum.primesEquiv
          (R := NumberField.RingOfIntegers ℚ)).symm q) := by
    rfl
  rw [
    rationalCyclotomicGlobalArtin_character_toZModPow,
    globalArtinMonoidHom_finitePlaceIdele,
    hprime,
    map_pow,
    map_pow]
  exact
    congrArg (fun u => u ^ d)
      (rationalCyclotomicPrincipalFinitePlaceCharacter_chosenArtin_spec
        p k x q).symm

/-- At the place `p`, the full `p`-adic cyclotomic character of the
one-place idèle obtained from the rational unit `p + 1` is the direct
unit `p + 1`, with the prescribed local-degree power. -/
theorem
    rationalCyclotomicCharacterPrimeProduct_finitePlaceIdele_primeSucc
    (p : Nat.Primes) (d : ℕ) :
    KummerTheory.rationalCyclotomicCharacterPrimeProduct
        (infiniteGlobalArtinMonoidHom
          ℚ KummerTheory.rationalCyclotomicField
          (IdeleGroup.finitePlaceIdele
            (RayClass.rationalPrime p)
            ((IdeleGroup.finiteComponent
              (RayClass.rationalPrime p)
              (IdeleGroup.principalIdele ℚ
                (Units.mk0
                  ((p.1 + 1 : ℕ) : ℚ)
                  (by positivity)))) ^ d))) p =
      (padicNatUnit p (p.1 + 1)
        (Nat.coprime_self_add_right.mpr
          (Nat.coprime_one_right p.1))) ^ d := by
  let x : ℚˣ :=
    Units.mk0
      ((p.1 + 1 : ℕ) : ℚ)
      (by positivity)
  have hx :
      (x : ℚ) =
        ((p.1 + 1 : ℕ) : ℚ) :=
    rfl
  have hprimeUnit :
      (rationalPrimeUnit x p : ℚ) =
        ((p.1 + 1 : ℕ) : ℚ) := by
    rw [rationalPrimeUnit_val,
      hx,
      padicValRat_rationalPrime_succ,
      neg_zero,
      zpow_zero,
      one_mul]
  have hunit :
      padicIntUnitOfRat p
          (rationalPrimeUnit x p : ℚ)
          (rationalPrimeUnit x p).ne_zero
          (padicValRat_rationalPrimeUnit x p) =
        padicNatUnit p (p.1 + 1)
          (Nat.coprime_self_add_right.mpr
            (Nat.coprime_one_right p.1)) := by
    apply Units.ext
    apply Subtype.ext
    rw [padicIntUnitOfRat_coe,
      padicNatUnit_val,
      hprimeUnit]
    exact PadicInt.coe_natCast (p.1 + 1)
  apply Units.ext
  apply PadicInt.ext_of_toZModPow.mp
  intro k
  let hpFact : Fact (Nat.Prime p.1) := ⟨p.2⟩
  have hred :=
    rationalCyclotomicCharacterPrimeProduct_finitePlaceIdele_principalComponent_toZModPow
      p p k d x
  rw [
    rationalCyclotomicPrincipalFinitePlaceCharacter_at_prime p k x,
    hunit] at hred
  have hredVal := congrArg Units.val hred
  simp only [Units.coe_map, Units.val_pow_eq_pow_val] at hredVal
  have htoZModPow (z : ℤ_[p.1]) :
      (PadicInt.toZModPow
          (p := p.1) (k : ℕ)).toMonoidHom z =
        PadicInt.toZModPow (p := p.1) (k : ℕ) z :=
    rfl
  simp only [htoZModPow] at hredVal
  simpa only [x, Units.val_pow_eq_pow_val, map_pow] using hredVal

/-- Away from `p`, the full `p`-adic cyclotomic character of the
rational-prime one-place idèle is inverse arithmetic Frobenius, again
with the prescribed local-degree power. -/
theorem
    rationalCyclotomicCharacterPrimeProduct_finitePlaceIdele_primeAway
    (p q : Nat.Primes) (hqp : q ≠ p) (d : ℕ) :
    KummerTheory.rationalCyclotomicCharacterPrimeProduct
        (infiniteGlobalArtinMonoidHom
          ℚ KummerTheory.rationalCyclotomicField
          (IdeleGroup.finitePlaceIdele
            (RayClass.rationalPrime q)
            ((IdeleGroup.finiteComponent
              (RayClass.rationalPrime q)
              (IdeleGroup.principalIdele ℚ
                (Units.mk0 (q.1 : ℚ)
                  (by exact_mod_cast q.2.ne_zero)))) ^ d))) p =
      ((padicNatUnit p q.1
        ((Nat.coprime_primes p.2 q.2).2
          (fun hpq =>
            hqp (Subtype.ext hpq.symm))))⁻¹) ^ d := by
  let x : ℚˣ :=
    Units.mk0 (q.1 : ℚ)
      (by exact_mod_cast q.2.ne_zero)
  let hcoprime : p.1.Coprime q.1 :=
    (Nat.coprime_primes p.2 q.2).2
      (fun hpq =>
        hqp (Subtype.ext hpq.symm))
  have hx : (x : ℚ) = q.1 := rfl
  apply Units.ext
  apply PadicInt.ext_of_toZModPow.mp
  intro k
  let hpFact : Fact (Nat.Prime p.1) := ⟨p.2⟩
  have hlocal :
      rationalCyclotomicPrincipalFinitePlaceCharacter
          p k x q =
        (ZMod.unitOfCoprime q.1
          (q.2.coprime_iff_not_dvd.mpr
            (rationalPrime_not_dvd_pow_of_ne
              q p hqp k)))⁻¹ := by
    rw [
      rationalCyclotomicPrincipalFinitePlaceCharacter_of_ne
        p q hqp k x,
      hx,
      padicValRat.self q.2.one_lt,
      zpow_neg,
      zpow_one]
  have hred :=
    rationalCyclotomicCharacterPrimeProduct_finitePlaceIdele_principalComponent_toZModPow
      p q k d x
  rw [hlocal] at hred
  have htarget :
      Units.map
          (PadicInt.toZModPow
            (p := p.1) (k : ℕ)).toMonoidHom
          (((padicNatUnit p q.1 hcoprime)⁻¹) ^ d) =
        ((ZMod.unitOfCoprime q.1
          (hcoprime.symm.pow_right k))⁻¹) ^ d := by
    rw [map_pow, map_inv,
      padicNatUnit_toZModPow]
  have hredVal :=
    congrArg Units.val (hred.trans htarget.symm)
  simp only [Units.coe_map, Units.val_pow_eq_pow_val] at hredVal
  have htoZModPow (z : ℤ_[p.1]) :
      (PadicInt.toZModPow
          (p := p.1) (k : ℕ)).toMonoidHom z =
        PadicInt.toZModPow (p := p.1) (k : ℕ) z :=
    rfl
  simp only [htoZModPow] at hredVal
  simpa only [x, hcoprime, Units.val_pow_eq_pow_val,
    Units.val_inv_eq_inv_val] using hredVal

/-- The image of the actual decomposition group has a nonzero
`p`-adic cyclotomic coordinate.

The witness is a genuine one-place idèle over `F`.  Its component is
obtained by extending a rational completion unit to the chosen place:
at residue characteristic `p` we use `p + 1`, and away from `p` we use
the rational residue prime.  The ordinary idèle norm is the corresponding
positive local-degree power.  The direct-unit and inverse-Frobenius
local formulas show that its full `p`-adic cyclotomic character is
non-torsion, so its torsion-free coordinate cannot vanish. -/
theorem
    numberFieldCyclotomicPadicDecompositionCoordinate_range_toAddSubgroup_ne_bot
    (F : Type) [Field F] [NumberField F]
    (v : HeightOneSpectrum (𝓞 F))
    (wC : AbsoluteValueExtension
      (NumberField.HeightOneSpectrum.adicAbv F v)
      (numberFieldCyclotomicZHatCompositum F))
    (p : Nat.Primes) :
    (numberFieldCyclotomicPadicDecompositionCoordinate
        F wC.1 p).range.toAddSubgroup' ≠
      (⊥ : AddSubgroup ℤ_[p.1]) := by
  let q₀ : HeightOneSpectrum (𝓞 ℚ) :=
    _root_.finitePlaceBelow (K := ℚ) v
  let q : Nat.Primes :=
    Rat.HeightOneSpectrum.primesEquiv
      (R := 𝓞 ℚ) q₀
  have hq :
      RayClass.rationalPrime q = q₀ := by
    simpa only [q] using
      (Rat.HeightOneSpectrum.primesEquiv
        (R := 𝓞 ℚ)).symm_apply_apply q₀
  let x : ℚˣ :=
    if q = p then
      Units.mk0
        ((p.1 + 1 : ℕ) : ℚ)
        (by positivity)
    else
      Units.mk0 (q.1 : ℚ)
        (by exact_mod_cast q.2.ne_zero)
  let b : (q₀.adicCompletion ℚ)ˣ :=
    IdeleGroup.finiteComponent q₀
      (IdeleGroup.principalIdele ℚ x)
  let d : ℕ :=
    IdeleGroup.finitePlaceCompletionDegree
      (K := ℚ) (L := F) v
  have hd : 0 < d :=
    IdeleGroup.finitePlaceCompletionDegree_pos
      (K := ℚ) (L := F) v
  let a : IdeleGroup F :=
    IdeleGroup.finitePlaceIdele v
      (IdeleGroup.finitePlaceBaseUnitExtension
        (K := ℚ) (L := F) v b)
  have hnorm :
      IdeleGroup.norm ℚ F a =
        IdeleGroup.finitePlaceIdele q₀ (b ^ d) := by
    exact
      IdeleGroup.norm_finitePlaceIdele_finitePlaceBaseUnitExtension
        (K := ℚ) (L := F) v b
  have hArtin :
      infiniteGlobalArtinMonoidHom F
          (numberFieldCyclotomicZHatCompositum F) a ∈
        absoluteValueDecompositionGroup F wC.1 := by
    exact
      infiniteGlobalArtinMonoidHom_finitePlaceIdele_mem_absoluteValueDecompositionGroup
        v wC
        (IdeleGroup.finitePlaceBaseUnitExtension
          (K := ℚ) (L := F) v b)
  let τ :
      absoluteValueDecompositionGroup F wC.1 :=
    ⟨infiniteGlobalArtinMonoidHom F
        (numberFieldCyclotomicZHatCompositum F) a,
      hArtin⟩
  have hτne :
      numberFieldCyclotomicPadicDecompositionCoordinate
          F wC.1 p τ ≠ 1 := by
    intro hτone
    have hcoordinate :=
      numberFieldCyclotomicPadicDecompositionCoordinate_infiniteGlobalArtin
        F wC.1 p a hArtin
    have hfreeNorm :
        zHatToPadicInt p
            (Multiplicative.toAdd
              (rationalCyclotomicZHatIdeleValue
                (IdeleGroup.norm ℚ F a))) =
          0 := by
      have hone :
          Multiplicative.ofAdd
              (zHatToPadicInt p
                (Multiplicative.toAdd
                  (rationalCyclotomicZHatIdeleValue
                    (IdeleGroup.norm ℚ F a)))) =
            1 :=
        hcoordinate.symm.trans hτone
      exact congrArg Multiplicative.toAdd hone
    rw [hnorm,
      rationalCyclotomicZHatIdeleValue_eq_fullCharacterFreePart]
        at hfreeNorm
    let σQ :=
      infiniteGlobalArtinMonoidHom
        ℚ KummerTheory.rationalCyclotomicField
        (IdeleGroup.finitePlaceIdele q₀ (b ^ d))
    let u : ZHatˣ :=
      KummerTheory.rationalCyclotomicCharacterContinuousMulEquiv σQ
    have hfree :
        zHatToPadicInt p
            (Multiplicative.toAdd
              (KummerTheory.zHatUnitsDecomposition u).1) =
          0 := by
      simpa only [u, σQ] using hfreeNorm
    have hfinite :
        IsOfFinOrder
          (KummerTheory.rationalCyclotomicCharacterPrimeProduct
            σQ p) := by
      have htorsion :=
        KummerTheory.zHatUnit_padicCoordinate_isOfFinOrder_of_freeCoordinate_eq_zero
          u p hfree
      simpa only [
        u,
        KummerTheory.zHatUnitsContinuousMulEquivPrimeProduct_rationalCyclotomicCharacter]
        using htorsion
    by_cases hqp : q = p
    · have hcharacter :
          KummerTheory.rationalCyclotomicCharacterPrimeProduct
              σQ p =
            (padicNatUnit p (p.1 + 1)
              (Nat.coprime_self_add_right.mpr
                (Nat.coprime_one_right p.1))) ^ d := by
        dsimp only [σQ, b, x]
        rw [ite_eq_left hqp, ← hq, hqp]
        exact
          rationalCyclotomicCharacterPrimeProduct_finitePlaceIdele_primeSucc
            p d
      have hpowerFinite :
          IsOfFinOrder
            ((padicNatUnit p (p.1 + 1)
              (Nat.coprime_self_add_right.mpr
                (Nat.coprime_one_right p.1))) ^ d) := by
        rw [← hcharacter]
        exact hfinite
      have hbaseFinite := hpowerFinite.of_pow hd.ne'
      exact
        (padicNatUnit_not_isOfFinOrder_of_one_lt
          p (p.1 + 1)
          (Nat.coprime_self_add_right.mpr
            (Nat.coprime_one_right p.1))
          (Nat.lt_trans p.2.one_lt
            (Nat.lt_succ_self p.1))) hbaseFinite
    · let hcoprime : p.1.Coprime q.1 :=
        (Nat.coprime_primes p.2 q.2).2
          (fun hpq =>
            hqp (Subtype.ext hpq.symm))
      have hcharacter :
          KummerTheory.rationalCyclotomicCharacterPrimeProduct
              σQ p =
            ((padicNatUnit p q.1 hcoprime)⁻¹) ^ d := by
        dsimp only [σQ, b, x]
        rw [ite_eq_right hqp, ← hq]
        simpa only [hcoprime] using
          rationalCyclotomicCharacterPrimeProduct_finitePlaceIdele_primeAway
            p q hqp d
      have hinversePowerFinite :
          IsOfFinOrder
            (((padicNatUnit p q.1 hcoprime)⁻¹) ^ d) := by
        rw [← hcharacter]
        exact hfinite
      have hinverseFinite := hinversePowerFinite.of_pow hd.ne'
      have hbaseFinite := hinverseFinite.of_inv
      exact
        (padicNatUnit_not_isOfFinOrder_of_one_lt
          p q.1 hcoprime q.2.one_lt) hbaseFinite
  intro hbot
  have hmem :
      Multiplicative.toAdd
          (numberFieldCyclotomicPadicDecompositionCoordinate
            F wC.1 p τ) ∈
        (numberFieldCyclotomicPadicDecompositionCoordinate
          F wC.1 p).range.toAddSubgroup' := by
    rw [Subgroup.mem_toAddSubgroup', ofAdd_toAdd]
    exact ⟨τ, rfl⟩
  rw [hbot] at hmem
  exact
    hτne
      (congrArg Multiplicative.ofAdd
        (AddSubgroup.mem_bot.mp hmem))

/-- The actual `p`-adic coordinate of a finite-place decomposition
group has finite index in `ℤ_[p]`.  This is the precise nonvanishing
input used to correct a Frobenius lift inside the restriction kernel. -/
theorem
    numberFieldCyclotomicPadicDecompositionCoordinate_range_index_ne_zero
    (F : Type) [Field F] [NumberField F]
    (v : HeightOneSpectrum (𝓞 F))
    (wC : AbsoluteValueExtension
      (NumberField.HeightOneSpectrum.adicAbv F v)
      (numberFieldCyclotomicZHatCompositum F))
    (p : Nat.Primes) :
    ((numberFieldCyclotomicPadicDecompositionCoordinate
        F wC.1 p).range.toAddSubgroup').index ≠ 0 := by
  let H : AddSubgroup ℤ_[p.1] :=
    (numberFieldCyclotomicPadicDecompositionCoordinate
      F wC.1 p).range.toAddSubgroup'
  have hclosed :
      IsClosed (H : Set ℤ_[p.1]) := by
    change
      IsClosed
        ((numberFieldCyclotomicPadicDecompositionCoordinate
          F wC.1 p).range :
          Set (Multiplicative ℤ_[p.1]))
    exact
      numberFieldCyclotomicPadicDecompositionCoordinate_range_isClosed
        F wC.1 p
  have hne : H ≠ ⊥ :=
    numberFieldCyclotomicPadicDecompositionCoordinate_range_toAddSubgroup_ne_bot
      F v wC p
  have hopen : IsOpen (H : Set ℤ_[p.1]) :=
    PadicInt.addSubgroup_isOpen_of_isClosed_of_ne_bot
      p.1 H hclosed hne
  let : Finite (ℤ_[p.1] ⧸ H) :=
    AddSubgroup.quotient_finite_of_isOpen H hopen
  exact H.index_ne_zero_of_finite

/-- The finite-index conclusion depends only on the valuation
class of the chosen absolute value on the cyclotomic compositum. -/
theorem
    numberFieldCyclotomicPadicDecompositionCoordinate_range_index_ne_zero_of_isEquiv
    (F : Type) [Field F] [NumberField F]
    (v : HeightOneSpectrum (𝓞 F))
    (wC : AbsoluteValue
      (numberFieldCyclotomicZHatCompositum F) ℝ)
    (wC' : AbsoluteValueExtension
      (NumberField.HeightOneSpectrum.adicAbv F v)
      (numberFieldCyclotomicZHatCompositum F))
    (hww' : wC.IsEquiv wC'.1)
    (p : Nat.Primes) :
    ((numberFieldCyclotomicPadicDecompositionCoordinate
        F wC p).range.toAddSubgroup').index ≠ 0 := by
  have hD :
      absoluteValueDecompositionGroup F wC =
        absoluteValueDecompositionGroup F wC'.1 :=
    absoluteValueDecompositionGroup_eq_of_absoluteValue_isEquiv
      wC wC'.1 hww'
  have hrange :
      (numberFieldCyclotomicPadicDecompositionCoordinate
          F wC p).range =
        (numberFieldCyclotomicPadicDecompositionCoordinate
          F wC'.1 p).range := by
    ext y
    constructor
    · rintro ⟨σ, rfl⟩
      let σ' :
          absoluteValueDecompositionGroup F wC'.1 :=
        ⟨σ.1, by
          rw [← hD]
          exact σ.2⟩
      exact ⟨σ', rfl⟩
    · rintro ⟨σ, rfl⟩
      let σ' :
          absoluteValueDecompositionGroup F wC :=
        ⟨σ.1, by
          rw [hD]
          exact σ.2⟩
      exact ⟨σ', rfl⟩
  rw [hrange]
  exact
    numberFieldCyclotomicPadicDecompositionCoordinate_range_index_ne_zero
      F v wC' p

/-- The finite-index conclusion for an arbitrary representative of the
valuation class above `v`.

The hypothesis only compares the restriction of the chosen absolute value
with the normalized `v`-adic absolute value.  We raise the chosen
nonarchimedean absolute value to the unique positive normalizing exponent,
obtaining an exact extension without changing its decomposition group. -/
theorem
    numberFieldCyclotomicPadicDecompositionCoordinate_range_index_ne_zero_of_base_isEquiv
    (F : Type) [Field F] [NumberField F]
    (v : HeightOneSpectrum (𝓞 F))
    (wC : AbsoluteValue
      (numberFieldCyclotomicZHatCompositum F) ℝ)
    (hbase :
      (wC.comp
          (f := algebraMap F
            (numberFieldCyclotomicZHatCompositum F))
          (algebraMap F
            (numberFieldCyclotomicZHatCompositum F)).injective).IsEquiv
        (NumberField.HeightOneSpectrum.adicAbv F v))
    (p : Nat.Primes) :
    ((numberFieldCyclotomicPadicDecompositionCoordinate
        F wC p).range.toAddSubgroup').index ≠ 0 := by
  let vF : AbsoluteValue F ℝ :=
    NumberField.HeightOneSpectrum.adicAbv F v
  let wF : AbsoluteValue F ℝ :=
    wC.comp
      (f := algebraMap F
        (numberFieldCyclotomicZHatCompositum F))
      (algebraMap F
        (numberFieldCyclotomicZHatCompositum F)).injective
  have hvFna : IsNonarchimedean (vF : F → ℝ) :=
    NumberField.HeightOneSpectrum.isNonarchimedean_adicAbv F v
  have hwFna : IsNonarchimedean (wF : F → ℝ) := by
    rw [AbsoluteValue.isNonarchimedean_iff_bounded_nat]
    refine ⟨1, ?_⟩
    intro n
    exact
      (hbase.le_one_iff).2
        hvFna.apply_natCast_le_one
  have hwCna :
      IsNonarchimedean
        (wC :
          numberFieldCyclotomicZHatCompositum F → ℝ) := by
    rw [AbsoluteValue.isNonarchimedean_iff_bounded_nat]
    refine ⟨1, ?_⟩
    intro n
    have hn :
        (n : numberFieldCyclotomicZHatCompositum F) =
          algebraMap F
            (numberFieldCyclotomicZHatCompositum F)
            (n : F) := by
      exact
        (map_natCast
          (algebraMap F
            (numberFieldCyclotomicZHatCompositum F)) n).symm
    rw [hn]
    exact
      hwFna.apply_natCast_le_one
  obtain ⟨c, hc, hpow⟩ :=
    (AbsoluteValue.isEquiv_iff_exists_rpow_eq).1 hbase
  let wC' :
      AbsoluteValueExtension vF
        (numberFieldCyclotomicZHatCompositum F) :=
    ⟨AbsoluteValue.nonarchimedeanRpow
        wC hwCna c hc,
      by
        intro x
        change
          wC
                (algebraMap F
                  (numberFieldCyclotomicZHatCompositum F) x) ^
              c =
            vF x
        exact congrFun hpow x⟩
  have hwwC' : wC.IsEquiv wC'.1 :=
    AbsoluteValue.isEquiv_nonarchimedeanRpow
      wC hwCna c hc
  exact
    numberFieldCyclotomicPadicDecompositionCoordinate_range_index_ne_zero_of_isEquiv
      F v wC wC' hwwC' p

end Reciprocity
end GlobalClassFieldTheory
end
end

section
-- module Solutions.OAIQ244_DUKE.GlobalClassFieldTheory_Reciprocity_LocalGlobalArtinCompatibility_SeparableClosurePadicLift
attribute [-instance] _root_.GlobalClassFieldTheory.Reciprocity.complexFourthRootField_numberField _root_.GlobalClassFieldTheory.Reciprocity.infinitePlaceComplexificationOverfield_algebra _root_.GlobalClassFieldTheory.Reciprocity.infinitePlaceComplexificationOverfield_baseAlgebra _root_.GlobalClassFieldTheory.Reciprocity.infinitePlaceComplexificationOverfield_baseSmul _root_.GlobalClassFieldTheory.Reciprocity.infinitePlaceComplexificationOverfield_numberField _root_.GlobalClassFieldTheory.Reciprocity.infinitePlaceComplexificationOverfield_smul _root_.GlobalClassFieldTheory.Reciprocity.ramifiedInfinitePlaceOverextension_isAbelianGalois _root_.GlobalClassFieldTheory.Reciprocity.ramifiedInfinitePlaceRealFixedField_algebra _root_.GlobalClassFieldTheory.Reciprocity.ramifiedInfinitePlaceRealFixedField_numberField _root_.GlobalClassFieldTheory.Reciprocity.rationalComplexification_infinitePlaceOverfield_algebra _root_.GlobalClassFieldTheory.Reciprocity.rationalComplexification_infinitePlaceOverfield_smul _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.boundedRealFields_numberField _root_.OAI.PrimeDegreePackets.diagonalLogAction _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable
attribute [-simp] _root_.GlobalClassFieldTheory.GlobalClassFields.mem_cyclotomicKummerNormSupportAbove_iff _root_.OAI.PrimeDegreePackets.ThetaConstruction.schwartzCM_apply _root_.RayClass.idealNormExponentMap_apply _root_.RayClass.idealNormLiftedModulusExponent_eq_zero_of_not_mem _root_.RayClass.mem_idealNormLiftedModulus_support_iff
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

/-!
# Separable-closure p-adic lifts for local-global Artin compatibility

This module constructs the finite-place decomposition restriction maps and
the positive p-adic cyclotomic lifts used in the local-global comparison.
-/

open scoped NumberField
open AlgebraicNumberTheory IsDedekindDomain NumberField
open IdeleGroup RelativeIdeleGroup
open AlgebraicNumberTheory.Valuations
open HilbertRamification

noncomputable section

namespace GlobalClassFieldTheory
namespace Reciprocity

variable
    {K L : Type}
    [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsAbelianGalois K L]

attribute [local instance] GlobalClassFieldTheory.Reciprocity.instFactPrimeValNat_solutions_6
attribute [local instance] GlobalClassFieldTheory.Reciprocity.automorphismCyclicFixedFieldNumberField
/-- The centre in `L` of the originally chosen extension of `v` lies
above the cyclic-reduction place.  This identifies the exact upper
place used in the norm--restriction square without making a new
valuation choice. -/
theorem finitePlaceBelow_chosenExtensionCentre_eq_automorphismCyclicFixedPlace
    (v : HeightOneSpectrum (𝓞 K))
    (σ : Gal(L / K)) :
    let M := automorphismCyclicFixedField σ
    finitePlaceBelow (K := M)
        (finitePlaceExtensionCentre
          (K := K) (L := L) v
          (chosenFinitePlaceExtension (L := L) v)) =
      automorphismCyclicFixedPlace v σ := by
  dsimp only
  let M := automorphismCyclicFixedField σ
  let w :=
    chosenFinitePlaceExtension (L := L) v
  let wM :=
    restrictFinitePlaceExtension
      (K := K) (L := L) (E := M) v w
  apply HeightOneSpectrum.ext
  ext x
  change
    algebraMap (𝓞 M) (𝓞 L) x ∈
        finitePlaceExtensionCentreIdeal
          (K := K) (L := L) v w ↔
      x ∈
        finitePlaceExtensionCentreIdeal
          (K := K) (L := M) v wM
  rw [
    mem_finitePlaceExtensionCentreIdeal_iff,
    mem_finitePlaceExtensionCentreIdeal_iff]
  rfl

/-- The exact extension of the normalized finite absolute value at the
cyclic-reduction place whose centre is the original chosen place of
`L`. -/
noncomputable def automorphismCyclicFixedTopExtension
    (v : HeightOneSpectrum (𝓞 K))
    (σ : Gal(L / K)) :
    let M := automorphismCyclicFixedField σ
    AbsoluteValueExtension
      (NumberField.HeightOneSpectrum.adicAbv M
        (automorphismCyclicFixedPlace v σ)) L := by
  dsimp only
  let M := automorphismCyclicFixedField σ
  let W :=
    automorphismCyclicFixedPlace v σ
  let V :
      {V : HeightOneSpectrum (𝓞 L) //
        finitePlaceBelow (K := M) V = W} :=
    ⟨finitePlaceExtensionCentre
        (K := K) (L := L) v
        (chosenFinitePlaceExtension (L := L) v),
      finitePlaceBelow_chosenExtensionCentre_eq_automorphismCyclicFixedPlace
        (K := K) (L := L) v σ⟩
  exact
    (finitePlaceExtensionEquivAbove
      (K := M) (L := L) W).symm V

/-- The chosen top extension above the cyclic fixed place has the same centre
as the original chosen extension over the base field. -/
@[simp]
theorem automorphismCyclicFixedTopExtension_centre
    (v : HeightOneSpectrum (𝓞 K))
    (σ : Gal(L / K)) :
    let M := automorphismCyclicFixedField σ
    finitePlaceExtensionCentre
        (K := M) (L := L)
        (automorphismCyclicFixedPlace v σ)
        (automorphismCyclicFixedTopExtension v σ) =
      finitePlaceExtensionCentre
        (K := K) (L := L) v
        (chosenFinitePlaceExtension (L := L) v) := by
  dsimp only
  let M := automorphismCyclicFixedField σ
  let W :=
    automorphismCyclicFixedPlace v σ
  let V :
      {V : HeightOneSpectrum (𝓞 L) //
        finitePlaceBelow (K := M) V = W} :=
    ⟨finitePlaceExtensionCentre
        (K := K) (L := L) v
        (chosenFinitePlaceExtension (L := L) v),
      finitePlaceBelow_chosenExtensionCentre_eq_automorphismCyclicFixedPlace
        (K := K) (L := L) v σ⟩
  have h :=
    congrArg Subtype.val
      ((finitePlaceExtensionEquivAbove
        (K := M) (L := L) W).apply_symm_apply V)
  simpa only [
    finitePlaceExtensionEquivAbove_coe,
    V, W, id_eq,
    automorphismCyclicFixedTopExtension
  ] using h

/-- A decomposition automorphism remains in the decomposition group at the
chosen place after the cyclic fixed-field reduction.  This is the lightweight
geometric statement underlying the corresponding local Artin range result. -/
theorem automorphismOverCyclicFixedField_mem_chosenFinitePlaceDecompositionGroup
    (v : HeightOneSpectrum (𝓞 K))
    (σ :
      absoluteValueDecompositionGroup K
        (chosenFinitePlaceExtension (L := L) v).1) :
    let M := automorphismCyclicFixedField σ.1
    automorphismOverCyclicFixedField σ.1 ∈
      absoluteValueDecompositionGroup M
        (chosenFinitePlaceExtension
          (L := L) (automorphismCyclicFixedPlace v σ.1)).1 := by
  dsimp only
  let M :=
    automorphismCyclicFixedField σ.1
  let W :=
    automorphismCyclicFixedPlace v σ.1
  let wK :=
    chosenFinitePlaceExtension (L := L) v
  let wM :=
    automorphismCyclicFixedTopExtension v σ.1
  let σM : Gal(L / M) :=
    automorphismOverCyclicFixedField σ.1
  have hrestrict :
      RamificationTheory.HilbertRamification.ValuationSubring.restrictAutomorphismScalars
          (K := K) (M := M) σM =
        σ.1 := by
    apply AlgEquiv.ext
    intro x
    rfl
  have hσM_wK :
      σM ∈
        absoluteValueDecompositionGroup M wK.1 := by
    apply
      (decompositionGroupRestriction_mem_absoluteValueDecompositionGroup_restrictScalars_iff
        (K := K) (M := M) wK.1 σM).mp
    simpa only [hrestrict] using σ.2
  have hequiv :
      wK.1.IsEquiv wM.1 := by
    apply
      finitePlaceExtensions_isEquiv_of_centres_eq
        (F := K) (M := M) v W wK wM
    exact
      (automorphismCyclicFixedTopExtension_centre
        (K := K) (L := L) v σ.1).symm
  have hσM_wM :
      σM ∈
        absoluteValueDecompositionGroup M wM.1 := by
    rw [
      ←
        absoluteValueDecompositionGroup_eq_of_absoluteValue_isEquiv
          (F := M) wK.1 wM.1 hequiv]
    exact hσM_wK
  have hσM_chosen :
      σM ∈
        absoluteValueDecompositionGroup M
          (chosenFinitePlaceExtension (L := L) W).1 := by
    rw [
      ←
        absoluteValueDecompositionGroup_eq_of_exactExtensions_of_isMulCommutative
          (F := M)
          (NumberField.HeightOneSpectrum.adicAbv M W)
          (RayClass.adicAbv_isNontrivial W)
          wM
          (chosenFinitePlaceExtension (L := L) W)]
    exact hσM_wM
  exact hσM_chosen

/-- Restriction from the decomposition group in the common compatible
rational separable closure to the decomposition group at the chosen
finite place of `L`.

The codomain is transported along the proved equality between the
restricted ambient absolute value and the supplied exact extension. -/
noncomputable def finitePlaceSeparableClosureDecompositionRestriction
    (v : HeightOneSpectrum (𝓞 K)) :
    letI : Algebra K (SeparableClosure ℚ) :=
      numberFieldTowerSeparableClosureBaseAlgebra K L
    letI : Algebra L (SeparableClosure ℚ) :=
      numberFieldTowerSeparableClosureTopAlgebra L
    letI : IsScalarTower K L (SeparableClosure ℚ) :=
      numberFieldTowerSeparableClosureScalarTower K L
    let wL :=
      chosenFinitePlaceExtension (L := L) v
    let wΩ :=
      numberFieldTowerFinitePlaceExtensionToSeparableClosure
        K L v wL
    absoluteValueDecompositionGroup K wΩ.1 →*
      absoluteValueDecompositionGroup K wL.1 := by
  letI : Algebra K (SeparableClosure ℚ) :=
    numberFieldTowerSeparableClosureBaseAlgebra K L
  letI : Algebra L (SeparableClosure ℚ) :=
    numberFieldTowerSeparableClosureTopAlgebra L
  letI : IsScalarTower K L (SeparableClosure ℚ) :=
    numberFieldTowerSeparableClosureScalarTower K L
  dsimp only
  let wL :=
    chosenFinitePlaceExtension (L := L) v
  let wΩ :=
    numberFieldTowerFinitePlaceExtensionToSeparableClosure
      K L v wL
  exact
    { toFun := fun τ =>
        ⟨AlgEquiv.restrictNormalHom L τ.1,
          by
            intro x
            change
              wL.1
                  ((AlgEquiv.restrictNormalHom L τ.1) x) < 1 ↔
                wL.1 x < 1
            rw [
              ←
                numberFieldTowerFinitePlaceExtensionToSeparableClosure_algebraMap
                  K L v wL
                    ((AlgEquiv.restrictNormalHom L τ.1) x),
              ←
                numberFieldTowerFinitePlaceExtensionToSeparableClosure_algebraMap
                  K L v wL x]
            have hcomm :
                algebraMap L (SeparableClosure ℚ)
                    ((AlgEquiv.restrictNormalHom L τ.1) x) =
                  τ.1 (algebraMap L (SeparableClosure ℚ) x) := by
              exact AlgEquiv.restrictNormal_commutes τ.1 L x
            rw [hcomm]
            exact τ.2 (algebraMap L (SeparableClosure ℚ) x)⟩
      map_one' := by
        apply Subtype.ext
        exact
          map_one
            (AlgEquiv.restrictNormalHom
              (F := K) (K₁ := SeparableClosure ℚ) L)
      map_mul' := by
        intro τ η
        apply Subtype.ext
        exact
          map_mul
            (AlgEquiv.restrictNormalHom
              (F := K) (K₁ := SeparableClosure ℚ) L)
            τ.1 η.1 }

omit [FiniteDimensional K L] in
/-- On underlying automorphisms, the compatible finite-place
restriction is the ordinary normal-field restriction. -/
@[simp]
theorem finitePlaceSeparableClosureDecompositionRestriction_coe
    (v : HeightOneSpectrum (𝓞 K)) :
    letI : Algebra K (SeparableClosure ℚ) :=
      numberFieldTowerSeparableClosureBaseAlgebra K L
    letI : Algebra L (SeparableClosure ℚ) :=
      numberFieldTowerSeparableClosureTopAlgebra L
    letI : IsScalarTower K L (SeparableClosure ℚ) :=
      numberFieldTowerSeparableClosureScalarTower K L
    ∀ (τ :
      let wΩ :=
        numberFieldTowerFinitePlaceExtensionToSeparableClosure
          K L v (chosenFinitePlaceExtension (L := L) v)
      absoluteValueDecompositionGroup K wΩ.1),
    ((finitePlaceSeparableClosureDecompositionRestriction
        (K := K) (L := L) v) τ :
      Gal(L / K)) =
      AlgEquiv.restrictNormalHom L τ.1 := by
  let : Algebra K (SeparableClosure ℚ) :=
    numberFieldTowerSeparableClosureBaseAlgebra K L
  let : Algebra L (SeparableClosure ℚ) :=
    numberFieldTowerSeparableClosureTopAlgebra L
  let : IsScalarTower K L (SeparableClosure ℚ) :=
    numberFieldTowerSeparableClosureScalarTower K L
  intro τ
  rfl

omit [FiniteDimensional K L] in
/-- The compatible separable-closure restriction is onto the actual
decomposition group at the chosen finite place. -/
theorem finitePlaceSeparableClosureDecompositionRestriction_surjective
    (v : HeightOneSpectrum (𝓞 K)) :
    letI : Algebra K (SeparableClosure ℚ) :=
      numberFieldTowerSeparableClosureBaseAlgebra K L
    letI : Algebra L (SeparableClosure ℚ) :=
      numberFieldTowerSeparableClosureTopAlgebra L
    letI : IsScalarTower K L (SeparableClosure ℚ) :=
      numberFieldTowerSeparableClosureScalarTower K L
    Function.Surjective
      (finitePlaceSeparableClosureDecompositionRestriction
        (K := K) (L := L) v) := by
  let : Algebra K (SeparableClosure ℚ) :=
    numberFieldTowerSeparableClosureBaseAlgebra K L
  let : Algebra L (SeparableClosure ℚ) :=
    numberFieldTowerSeparableClosureTopAlgebra L
  let : IsScalarTower K L (SeparableClosure ℚ) :=
    numberFieldTowerSeparableClosureScalarTower K L
  dsimp only
  let separableClosurePadicLiftBaseIsGalois :
      IsGalois K (SeparableClosure ℚ) :=
    numberFieldTowerSeparableClosure_isGalois K L
  let wL :=
    chosenFinitePlaceExtension (L := L) v
  let wΩ :=
    numberFieldTowerFinitePlaceExtensionToSeparableClosure
      K L v wL
  let r :=
    absoluteValueDecompositionGroupRestrictionHom
      (K := K) (L := L) (Ω := SeparableClosure ℚ) wΩ.1
  have hr : Function.Surjective r :=
    absoluteValueDecompositionGroupRestrictionHom_surjective
      (K := K) (L := L) (Ω := SeparableClosure ℚ)
      (NumberField.HeightOneSpectrum.adicAbv K v)
      (RayClass.adicAbv_isNontrivial v) wΩ
  have hw :
      wΩ.1.comp
          (f := algebraMap L (SeparableClosure ℚ))
          (algebraMap L (SeparableClosure ℚ)).injective =
        wL.1 :=
    numberFieldTowerFinitePlaceExtensionToSeparableClosure_restrict
      K L v wL
  let σToRestricted :
      absoluteValueDecompositionGroup K wL.1 →
      absoluteValueDecompositionGroup K
        (wΩ.1.comp
          (f := algebraMap L (SeparableClosure ℚ))
          (algebraMap L (SeparableClosure ℚ)).injective) :=
    fun σ =>
      ⟨σ.1, by
        simpa only [hw] using σ.2⟩
  intro σ
  obtain ⟨τ, hτ⟩ := hr (σToRestricted σ)
  refine ⟨τ, ?_⟩
  apply Subtype.ext
  change (r τ).1 = (σToRestricted σ).1
  exact congrArg
    (fun ρ :
      absoluteValueDecompositionGroup K
        (wΩ.1.comp
          (f := algebraMap L (SeparableClosure ℚ))
          (algebraMap L (SeparableClosure ℚ)).injective) => ρ.1)
    hτ

/-- Scalar restriction embeds the decomposition group over `L` into
the compatible decomposition group over `K`. -/
noncomputable def
    finitePlaceSeparableClosureTopDecompositionInclusion
    (v : HeightOneSpectrum (𝓞 K)) :
    letI : Algebra K (SeparableClosure ℚ) :=
      numberFieldTowerSeparableClosureBaseAlgebra K L
    letI : Algebra L (SeparableClosure ℚ) :=
      numberFieldTowerSeparableClosureTopAlgebra L
    letI : IsScalarTower K L (SeparableClosure ℚ) :=
      numberFieldTowerSeparableClosureScalarTower K L
    let wΩ :=
      numberFieldTowerFinitePlaceExtensionToSeparableClosure
        K L v (chosenFinitePlaceExtension (L := L) v)
    absoluteValueDecompositionGroup L wΩ.1 →*
      absoluteValueDecompositionGroup K wΩ.1 := by
  letI : Algebra K (SeparableClosure ℚ) :=
    numberFieldTowerSeparableClosureBaseAlgebra K L
  letI : Algebra L (SeparableClosure ℚ) :=
    numberFieldTowerSeparableClosureTopAlgebra L
  letI : IsScalarTower K L (SeparableClosure ℚ) :=
    numberFieldTowerSeparableClosureScalarTower K L
  dsimp only
  let wΩ :=
    numberFieldTowerFinitePlaceExtensionToSeparableClosure
      K L v (chosenFinitePlaceExtension (L := L) v)
  exact
    { toFun := fun τ =>
        ⟨RamificationTheory.HilbertRamification.ValuationSubring.restrictAutomorphismScalars
              (K := K) (M := L) τ.1,
          (decompositionGroupRestriction_mem_absoluteValueDecompositionGroup_restrictScalars_iff
            (K := K) (M := L) wΩ.1 τ.1).2 τ.2⟩
      map_one' := by
        apply Subtype.ext
        rfl
      map_mul' := by
        intro τ η
        apply Subtype.ext
        rfl }

omit [FiniteDimensional K L] in
/-- The image of the top-field decomposition group is exactly the
kernel of restriction to the chosen finite-place decomposition group
of `L`. -/
theorem
    finitePlaceSeparableClosureTopDecompositionInclusion_range
    (v : HeightOneSpectrum (𝓞 K)) :
    letI : Algebra K (SeparableClosure ℚ) :=
      numberFieldTowerSeparableClosureBaseAlgebra K L
    letI : Algebra L (SeparableClosure ℚ) :=
      numberFieldTowerSeparableClosureTopAlgebra L
    letI : IsScalarTower K L (SeparableClosure ℚ) :=
      numberFieldTowerSeparableClosureScalarTower K L
    (finitePlaceSeparableClosureTopDecompositionInclusion
        (K := K) (L := L) v).range =
      (finitePlaceSeparableClosureDecompositionRestriction
        (K := K) (L := L) v).ker := by
  let : Algebra K (SeparableClosure ℚ) :=
    numberFieldTowerSeparableClosureBaseAlgebra K L
  let : Algebra L (SeparableClosure ℚ) :=
    numberFieldTowerSeparableClosureTopAlgebra L
  let : IsScalarTower K L (SeparableClosure ℚ) :=
    numberFieldTowerSeparableClosureScalarTower K L
  let wL :=
    chosenFinitePlaceExtension (L := L) v
  let wΩ :=
    numberFieldTowerFinitePlaceExtensionToSeparableClosure
      K L v wL
  ext τ
  constructor
  · rintro ⟨η, rfl⟩
    rw [MonoidHom.mem_ker]
    apply Subtype.ext
    apply AlgEquiv.ext
    intro x
    simp only [
      finitePlaceSeparableClosureDecompositionRestriction_coe]
    apply (algebraMap L (SeparableClosure ℚ)).injective
    calc
      algebraMap L (SeparableClosure ℚ)
            ((AlgEquiv.restrictNormalHom L
              ((finitePlaceSeparableClosureTopDecompositionInclusion
                (K := K) (L := L) v) η).1) x) =
          ((finitePlaceSeparableClosureTopDecompositionInclusion
              (K := K) (L := L) v) η).1
            (algebraMap L (SeparableClosure ℚ) x) :=
        AlgEquiv.restrictNormal_commutes
          ((finitePlaceSeparableClosureTopDecompositionInclusion
            (K := K) (L := L) v) η).1 L x
      _ = η.1 (algebraMap L (SeparableClosure ℚ) x) := rfl
      _ = algebraMap L (SeparableClosure ℚ) x := η.1.commutes x
      _ = algebraMap L (SeparableClosure ℚ)
            ((1 : Gal(L / K)) x) := rfl
  · intro hτ
    have hrestriction :
        AlgEquiv.restrictNormalHom L τ.1 = 1 := by
      have hτOne := MonoidHom.mem_ker.mp hτ
      have hτVal := congrArg Subtype.val hτOne
      calc
        AlgEquiv.restrictNormalHom L τ.1 =
            ((1 : absoluteValueDecompositionGroup K wL.1).1 :
              Gal(L / K)) := by
          simpa only [
            finitePlaceSeparableClosureDecompositionRestriction_coe] using
              hτVal
        _ = 1 := rfl
    let η : SeparableClosure ℚ ≃ₐ[L] SeparableClosure ℚ :=
      { τ.1.toRingEquiv with
        commutes' := by
          intro x
          have hcomm :=
            AlgEquiv.restrictNormal_commutes τ.1 L x
          have hx :=
            congrArg (fun ρ : Gal(L / K) => ρ x) hrestriction
          change (τ.1.restrictNormal L) x = x at hx
          calc
            τ.1 (algebraMap L (SeparableClosure ℚ) x) =
                algebraMap L (SeparableClosure ℚ)
                  ((τ.1.restrictNormal L) x) := hcomm.symm
            _ = algebraMap L (SeparableClosure ℚ) x :=
              congrArg (algebraMap L (SeparableClosure ℚ)) hx }
    have hη :
        η ∈ absoluteValueDecompositionGroup L wΩ.1 := by
      intro x
      exact τ.2 x
    refine ⟨⟨η, hη⟩, ?_⟩
    apply Subtype.ext
    apply AlgEquiv.ext
    intro x
    rfl

/-- The compatible separable-closure absolute value, regarded as an
exact extension of the chosen absolute value on the top number
field. -/
noncomputable def finitePlaceSeparableClosureTopExtension
    (v : HeightOneSpectrum (𝓞 K)) :
    letI : Algebra K (SeparableClosure ℚ) :=
      numberFieldTowerSeparableClosureBaseAlgebra K L
    letI : Algebra L (SeparableClosure ℚ) :=
      numberFieldTowerSeparableClosureTopAlgebra L
    letI : IsScalarTower K L (SeparableClosure ℚ) :=
      numberFieldTowerSeparableClosureScalarTower K L
    let wL :=
      chosenFinitePlaceExtension (L := L) v
    AbsoluteValueExtension wL.1 (SeparableClosure ℚ) := by
  letI : Algebra K (SeparableClosure ℚ) :=
    numberFieldTowerSeparableClosureBaseAlgebra K L
  letI : Algebra L (SeparableClosure ℚ) :=
    numberFieldTowerSeparableClosureTopAlgebra L
  letI : IsScalarTower K L (SeparableClosure ℚ) :=
    numberFieldTowerSeparableClosureScalarTower K L
  dsimp only
  let wL :=
    chosenFinitePlaceExtension (L := L) v
  let wΩ :=
    numberFieldTowerFinitePlaceExtensionToSeparableClosure
      K L v wL
  refine ⟨wΩ.1, ?_⟩
  intro x
  exact
    numberFieldTowerFinitePlaceExtensionToSeparableClosure_algebraMap
      K L v wL x

/-- Restriction of the compatible separable-closure valuation to the
actual cyclotomic `ZHat`-compositum over the top number field. -/
noncomputable def finitePlaceCyclotomicCompositumExtension
    (v : HeightOneSpectrum (𝓞 K)) :
    let wL :=
      chosenFinitePlaceExtension (L := L) v
    AbsoluteValueExtension wL.1
      (numberFieldCyclotomicZHatCompositum L) := by
  letI : Algebra K (SeparableClosure ℚ) :=
    numberFieldTowerSeparableClosureBaseAlgebra K L
  letI : Algebra L (SeparableClosure ℚ) :=
    numberFieldTowerSeparableClosureTopAlgebra L
  letI : IsScalarTower K L (SeparableClosure ℚ) :=
    numberFieldTowerSeparableClosureScalarTower K L
  letI : IsScalarTower L
      (numberFieldCyclotomicZHatCompositum L)
      (SeparableClosure ℚ) :=
    numberFieldCyclotomicZHatCompositumSeparableClosureScalarTower L
  dsimp only
  let C :=
    numberFieldCyclotomicZHatCompositum L
  let wL :=
    chosenFinitePlaceExtension (L := L) v
  let wΩL :=
    finitePlaceSeparableClosureTopExtension
      (K := K) (L := L) v
  refine
    ⟨wΩL.1.comp
        (f := algebraMap C (SeparableClosure ℚ))
        (algebraMap C (SeparableClosure ℚ)).injective,
      ?_⟩
  intro x
  change
    wΩL.1
        (algebraMap C (SeparableClosure ℚ)
          (algebraMap L C x)) =
      wL.1 x
  rw [← IsScalarTower.algebraMap_apply L C (SeparableClosure ℚ)]
  exact wΩL.2 x

omit [FiniteDimensional K L] in
/-- The restricted cyclotomic-compositum valuation has the same
finite-place class as the normalized valuation at the centre of the
chosen extension on the top field. -/
theorem finitePlaceCyclotomicCompositumExtension_base_isEquiv
    (v : HeightOneSpectrum (𝓞 K)) :
    let wL :=
      chosenFinitePlaceExtension (L := L) v
    let wC :=
      finitePlaceCyclotomicCompositumExtension
        (K := K) (L := L) v
    (wC.1.comp
        (f := algebraMap L
          (numberFieldCyclotomicZHatCompositum L))
        (algebraMap L
          (numberFieldCyclotomicZHatCompositum L)).injective).IsEquiv
      (NumberField.HeightOneSpectrum.adicAbv L
        (finitePlaceExtensionCentre
          (K := K) (L := L) v wL)) := by
  dsimp only
  let C :=
    numberFieldCyclotomicZHatCompositum L
  let wL :=
    chosenFinitePlaceExtension (L := L) v
  let wC :=
    finitePlaceCyclotomicCompositumExtension
      (K := K) (L := L) v
  have hrestrict :
      wC.1.comp
          (f := algebraMap L C)
          (algebraMap L C).injective =
        wL.1 := by
    ext x
    exact wC.2 x
  change
    (wC.1.comp
        (f := algebraMap L C)
        (algebraMap L C).injective).IsEquiv
      (NumberField.HeightOneSpectrum.adicAbv L
        (finitePlaceExtensionCentre
          (K := K) (L := L) v wL))
  rw [hrestrict]
  exact
    finitePlaceExtension_isEquiv_adicAbv
      (K := K) (L := L) v wL

/-- Restriction from the top-field decomposition group in the
compatible separable closure to the decomposition group in the actual
cyclotomic `ZHat`-compositum. -/
noncomputable def
    finitePlaceSeparableClosureTopCyclotomicRestriction
    (v : HeightOneSpectrum (𝓞 K)) :
    letI : Algebra L (SeparableClosure ℚ) :=
      numberFieldTowerSeparableClosureTopAlgebra L
    letI : IsScalarTower L
        (numberFieldCyclotomicZHatCompositum L)
        (SeparableClosure ℚ) :=
      numberFieldCyclotomicZHatCompositumSeparableClosureScalarTower L
    let wΩL :=
      finitePlaceSeparableClosureTopExtension
        (K := K) (L := L) v
    let wC :=
      finitePlaceCyclotomicCompositumExtension
        (K := K) (L := L) v
    absoluteValueDecompositionGroup L wΩL.1 →*
      absoluteValueDecompositionGroup L wC.1 := by
  letI : Algebra L (SeparableClosure ℚ) :=
    numberFieldTowerSeparableClosureTopAlgebra L
  letI : IsScalarTower L
      (numberFieldCyclotomicZHatCompositum L)
      (SeparableClosure ℚ) :=
    numberFieldCyclotomicZHatCompositumSeparableClosureScalarTower L
  dsimp only
  let C :=
    numberFieldCyclotomicZHatCompositum L
  let wΩL :=
    finitePlaceSeparableClosureTopExtension
      (K := K) (L := L) v
  let wC :=
    finitePlaceCyclotomicCompositumExtension
      (K := K) (L := L) v
  have hwC :
      wΩL.1.comp
          (f := algebraMap C (SeparableClosure ℚ))
          (algebraMap C (SeparableClosure ℚ)).injective =
        wC.1 := by
    rfl
  let raw :=
    absoluteValueDecompositionGroupRestrictionHom
      (K := L) (L := C) (Ω := SeparableClosure ℚ)
      wΩL.1
  exact
    { toFun := fun τ =>
        ⟨(raw τ).1, by
          simpa only [hwC] using (raw τ).2⟩
      map_one' := by
        apply Subtype.ext
        exact congrArg Subtype.val (map_one raw)
      map_mul' := by
        intro τ η
        apply Subtype.ext
        exact congrArg Subtype.val (map_mul raw τ η) }

omit [FiniteDimensional K L] in
/-- The top-field decomposition group surjects onto the decomposition
group of the actual cyclotomic `ZHat`-compositum at the restricted
place. -/
theorem
    finitePlaceSeparableClosureTopCyclotomicRestriction_surjective
    (v : HeightOneSpectrum (𝓞 K)) :
    letI : Algebra L (SeparableClosure ℚ) :=
      numberFieldTowerSeparableClosureTopAlgebra L
    letI : IsScalarTower L
        (numberFieldCyclotomicZHatCompositum L)
        (SeparableClosure ℚ) :=
      numberFieldCyclotomicZHatCompositumSeparableClosureScalarTower L
    Function.Surjective
      (finitePlaceSeparableClosureTopCyclotomicRestriction
        (K := K) (L := L) v) := by
  let : Algebra L (SeparableClosure ℚ) :=
    numberFieldTowerSeparableClosureTopAlgebra L
  let : IsScalarTower L
      (numberFieldCyclotomicZHatCompositum L)
      (SeparableClosure ℚ) :=
    numberFieldCyclotomicZHatCompositumSeparableClosureScalarTower L
  dsimp only
  let C :=
    numberFieldCyclotomicZHatCompositum L
  let separableClosurePadicLiftTopIsGalois :
      IsGalois L (SeparableClosure ℚ) :=
    numberFieldSeparableClosureTop_isGalois L
  let wL :=
    chosenFinitePlaceExtension (L := L) v
  let wΩL :=
    finitePlaceSeparableClosureTopExtension
      (K := K) (L := L) v
  let wC :=
    finitePlaceCyclotomicCompositumExtension
      (K := K) (L := L) v
  let raw :=
    absoluteValueDecompositionGroupRestrictionHom
      (K := L) (L := C) (Ω := SeparableClosure ℚ) wΩL.1
  have hraw : Function.Surjective raw :=
    absoluteValueDecompositionGroupRestrictionHom_surjective
      (K := L) (L := C) (Ω := SeparableClosure ℚ)
      wL.1
      (wL.isNontrivial
        (RayClass.adicAbv_isNontrivial v))
      wΩL
  have hwC :
      wΩL.1.comp
          (f := algebraMap C (SeparableClosure ℚ))
          (algebraMap C (SeparableClosure ℚ)).injective =
        wC.1 := by
    rfl
  intro σ
  let σRaw :
      absoluteValueDecompositionGroup L
        (wΩL.1.comp
          (f := algebraMap C (SeparableClosure ℚ))
          (algebraMap C (SeparableClosure ℚ)).injective) :=
    ⟨σ.1, by
      rw [hwC]
      exact σ.2⟩
  obtain ⟨τ, hτ⟩ := hraw σRaw
  refine ⟨τ, ?_⟩
  apply Subtype.ext
  change (raw τ).1 = σRaw.1
  exact congrArg
    (fun ρ :
      absoluteValueDecompositionGroup L
        (wΩL.1.comp
          (f := algebraMap C (SeparableClosure ℚ))
          (algebraMap C (SeparableClosure ℚ)).injective) => ρ.1)
    hτ

end Reciprocity
end GlobalClassFieldTheory
end
end

section
-- module Solutions.OAIQ244_DUKE.GlobalClassFieldTheory_GlobalClassFields_ArithmeticUnramifiedPrimeArtin
attribute [-instance] _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

/-!
# Arithmetic Frobenius at an unramified finite place

The pre-existing local class-formation coordinate has geometric
Frobenius normalization.  This file supplies the canonical prime Artin
element used in the ideal-theoretic formulation: the ordinary normalized
prime idèle maps to arithmetic Frobenius.
-/

open scoped NumberField Classical

noncomputable section

namespace GlobalClassFieldTheory
namespace GlobalClassFields

open NumberField IsDedekindDomain IdeleGroup

variable
    {K L : Type}
    [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    [IsAbelianGalois K L]

/-- The arithmetic Frobenius of the actual chosen completed extension,
transported through its decomposition group into the global Galois group.
The unramifiedness hypothesis concerns this chosen extension, not an
unrelated abstract local field. -/
noncomputable def chosenFinitePlaceArithmeticFrobenius
    (v : HeightOneSpectrum (𝓞 K))
    (hunram :
      _root_.ChosenFinitePlaceIsUnramified
        (K := K) (L := L) v) :
    L ≃ₐ[K] L := by
  let w := chosenFinitePlaceExtension (L := L) v
  exact Reciprocity.finitePlaceLocalToGlobalMonoidHom
    (K := K) (L := L) v w
    (Reciprocity.chosenFinitePlaceLocalArithmeticFrobenius
      (K := K) (L := L) v hunram)

end GlobalClassFields
end GlobalClassFieldTheory
end
end

section
-- module Solutions.OAIQ244_DUKE.GlobalClassFieldTheory_Reciprocity_IdeleClassNormTopology
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 400000
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.GlobalClassFields.bigHilbertClassFieldNormSubgroup_normal _root_.GlobalClassFieldTheory.GlobalClassFields.smallHilbertClassFieldNormSubgroupFiniteIndex _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalClassFieldTheory.finiteGaloisLocalField_integerRing_moduleFinite _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.residueFieldZModAlgebra _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedIntegralAlgebraContextValuationSubringAlgebra _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.LubinTate.padicCompletedLevelField_algebra _root_.LubinTate.padicCompletedUnramifiedFieldAlgebra _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.GlobalClassFieldTheory.GlobalClassFields.bigHilbertNormQuotient_finite _root_.GlobalClassFieldTheory.GlobalClassFields.bigHilbertNormSubgroup_finiteIndex _root_.LocalClassFieldTheory.comparisonIntegerRingIsIntegralClosure _root_.LocalClassFieldTheory.normalizationIntegerRingIsIntegralClosure
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

/-!
# The norm topology and the ordinary idele-class topology

On every actual fixed field inside the rational separable closure, the
canonical fixed-part model identifies each abstract finite norm subgroup
with the range of the corresponding ordinary idele-class norm.  Since the
latter is open, every abstract norm-open subgroup becomes open in the
ordinary idele-class topology after transport to the actual fixed field.
-/

open scoped NumberField

noncomputable section

namespace GlobalClassFieldTheory
namespace Reciprocity

open ClassFormation
open LocalClassFieldTheory

/-- Use the canonical quotient group structure before elaborating additive
norm-subgroup maps. -/
@[instance_reducible]
noncomputable def normTopologyIdeleClassCommGroup
    (F : Type) [Field F] [NumberField F] :
    CommGroup (IdeleClassGroup F) :=
  QuotientGroup.Quotient.commGroup (IdeleGroup.principalSubgroup F)

attribute [local instance] normTopologyIdeleClassCommGroup

end Reciprocity
end GlobalClassFieldTheory
end
end


