-- Prove2me | Definitions.Def_OAIQ244Duke110
-- name    : OAIQ244Duke110
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-14T04:30:54.796529+00:00
-- url     : https://prove2.me/theorems/e356c0d2-f708-4f63-a4e3-7c95106eb611
-- title:
--   Definitions bundle OAIQ244Duke110 of the split of OpenAI, Equidistribution of Prime-Degree Torus Packets with Arbitrary Local Type
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.DukePrimeDegree.prime_degree_packet_measure_equidistribution_unconditional` and `OAI.DukePrimeDegree.prime_degree_packet_measures_tendsto_haar_unconditional`, carved from OpenAI's openai/math development (OpenAI, *Equidistribution of Prime-Degree Torus Packets with Arbitrary Local Type*, OpenAI Math Release, September 24, 2026, result family 15, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 52 declarations of OpenAI's Lean: 12 definitions, 9 instances and 31 theorems. The definitions and types are `GlobalClassFieldTheory.IdealClassFieldTheory.arithmeticIdealArtinGaloisMap`, `GlobalClassFieldTheory.IdealClassFieldTheory.arithmeticIdealClassQuotientEquivGaloisGroup`, `GlobalClassFieldTheory.Reciprocity.abstractFixedFieldInclusionAmbientEmbeddedQuotientMkApplyVal`, `GlobalClassFieldTheory.Reciprocity.abstractFixedFieldInclusionAmbientEmbeddedQuotientMkValue`, `GlobalClassFieldTheory.Reciprocity.abstractFixedFieldInclusionCanonicalExtensionQuotientApplyVal`, `GlobalClassFieldTheory.Reciprocity.abstractFixedFieldInclusionCanonicalExtensionQuotientEquiv`, `GlobalClassFieldTheory.Reciprocity.abstractFixedFieldInclusionCanonicalExtensionQuotientValue`, `GlobalClassFieldTheory.Reciprocity.abstractFixedFieldInclusionEmbeddedExtensionQuotientApplyVal`, `GlobalClassFieldTheory.Reciprocity.abstractFixedFieldInclusionEmbeddedExtensionQuotientValue`, `GlobalClassFieldTheory.Reciprocity.abstractFixedFieldInclusionTransportedCanonicalAbelianizedValue`, `GlobalClassFieldTheory.Reciprocity.finitePlaceGlobalNormResidueFactor`, `GlobalClassFieldTheory.Reciprocity.numberFieldTowerFinitePadicImageDegree`.
--
--   **Sources.** They come from these modules of lean/OAI/NumberTheory, in whole or in part: `GlobalClassFieldTheory_GlobalClassFields_ClosedFiniteIndexClassFieldOriginalField`, `GlobalClassFieldTheory_GlobalClassFields_FiniteAbelianClassFieldContainment`, `GlobalClassFieldTheory_GlobalClassFields_OrdinaryNormClassField`, `GlobalClassFieldTheory_GlobalClassFields_SmallHilbertClassFieldOverOriginalBase`, `GlobalClassFieldTheory_IdealClassFieldTheory_ArithmeticIdealArtin`, `GlobalClassFieldTheory_Reciprocity_CyclotomicUnramifiedLocalGlobalCompatibility`, `GlobalClassFieldTheory_Reciprocity_GlobalNormResidueNaturality`, `GlobalClassFieldTheory_Reciprocity_LocalGlobalArtinCompatibility_Factorization`, `GlobalClassFieldTheory_Reciprocity_LocalGlobalArtinCompatibility_FinitePadicAuxiliaryField`, `GlobalClassFieldTheory_Reciprocity_LocalGlobalArtinCompatibility_FinitePadicCyclicData`.
--
--   **Imports.** It imports the bundles `OAIQ244Duke107` and `OAIQ244Duke108` of this split.
--
--   **Imported by** (directly, in this split): the bundle `OAIQ244Duke112`; the proofs of `ClassFieldTheory.GlobalClassFieldComparison.arithmeticPrimeArtin_eq_arithmeticFrobeniusAt`, `OAI.DukePrimeDegree.hasCyclicRayRealizations_unconditional`, `OAI.DukePrimeDegree.prime_degree_packet_measure_equidistribution_unconditional` and `OAI.DukePrimeDegree.prime_degree_packet_measures_tendsto_haar_unconditional`.
-- source:
--   OpenAI, Equidistribution of Prime-Degree Torus Packets with Arbitrary Local Type, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 15; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Equidistribution-of-Prime-Degree-Torus-Packets-with-Arbitrary-Local-Type-September-24-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/NumberTheory at commit 7ef5c0c

import Mathlib
import Mathlib.Algebra.Algebra.Basic
import Mathlib.Algebra.Algebra.Pi
import Mathlib.Algebra.Algebra.Tower
import Mathlib.Algebra.BigOperators.Finprod
import Mathlib.Algebra.BigOperators.Finsupp.Basic
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
import Mathlib.NumberTheory.RamificationInertia.Unramified
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
import Definitions.Def_OAIQ244Duke107
import Definitions.Def_OAIQ244Duke108

section
-- module Solutions.OAIQ244_DUKE.GlobalClassFieldTheory_GlobalClassFields_OrdinaryNormClassField
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 400000
attribute [-instance] _root_.GlobalClassFieldTheory.GlobalClassFields.bigHilbertClassFieldAlgebraOverOriginal _root_.GlobalClassFieldTheory.GlobalClassFields.bigHilbertClassFieldBaseAlgebraOverOriginal _root_.GlobalClassFieldTheory.GlobalClassFields.bigHilbertClassFieldIsGaloisOverOriginal _root_.GlobalClassFieldTheory.GlobalClassFields.bigHilbertClassFieldNormSubgroupFiniteIndex _root_.GlobalClassFieldTheory.GlobalClassFields.bigHilbertClassFieldNormSubgroup_normal _root_.GlobalClassFieldTheory.GlobalClassFields.bigHilbertClassFieldScalarTowerOverOriginal _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexClassFieldAlgebraOverOriginal _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexClassFieldBaseAlgebraOverOriginal _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexClassFieldScalarTowerOverOriginal _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexNormAmbientFiniteDimensional _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexNormAmbientIsGalois _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexNormAmbientNumberField _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexNormCyclotomicFieldFiniteDimensional _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexNormCyclotomicFieldIsCyclotomicExtension _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexNormCyclotomicFieldIsGalois _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexNormCyclotomicFieldNumberField _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexNormExponentNeZero _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexNormKummerFieldAlgebraOverBase _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexNormKummerFieldFiniteDimensional _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexNormKummerFieldFiniteDimensionalOverBase _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexNormKummerFieldModuleOverBase _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexNormKummerFieldNumberField _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexNormKummerFieldSMulOverBase _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexNormKummerFieldScalarTower _root_.GlobalClassFieldTheory.GlobalClassFields.smallHilbertClassFieldAlgebraOverOriginal _root_.GlobalClassFieldTheory.GlobalClassFields.smallHilbertClassFieldBaseAlgebraOverOriginal _root_.GlobalClassFieldTheory.GlobalClassFields.smallHilbertClassFieldNormSubgroupFiniteIndex _root_.GlobalClassFieldTheory.Reciprocity.abstractFixedFieldCyclotomicCompositum_algebra _root_.GlobalClassFieldTheory.Reciprocity.abstractFixedFieldCyclotomicCompositum_baseScalarTower _root_.GlobalClassFieldTheory.Reciprocity.abstractFixedFieldCyclotomicCompositum_scalarTower _root_.GlobalClassFieldTheory.Reciprocity.abstractFixedFieldCyclotomicFiniteCompositum_baseAlgebra _root_.GlobalClassFieldTheory.Reciprocity.abstractFixedFieldCyclotomicFiniteCompositum_baseScalarTower _root_.GlobalClassFieldTheory.Reciprocity.abstractFixedFieldCyclotomicFiniteGaloisLayer_scalarTower _root_.GlobalClassFieldTheory.Reciprocity.abstractFixedFieldCyclotomicFiniteLayer_baseAlgebra _root_.GlobalClassFieldTheory.Reciprocity.abstractFixedFieldCyclotomicFiniteLayer_baseModule _root_.GlobalClassFieldTheory.Reciprocity.abstractFixedFieldCyclotomicFiniteLayer_baseSMul _root_.GlobalClassFieldTheory.Reciprocity.abstractFixedFieldCyclotomicFiniteLayer_baseScalarTower _root_.GlobalClassFieldTheory.Reciprocity.abstractFixedFieldCyclotomicFiniteLayer_finiteDimensional _root_.GlobalClassFieldTheory.Reciprocity.abstractFixedFieldCyclotomicFiniteLayer_isAbelianGalois _root_.GlobalClassFieldTheory.Reciprocity.abstractFixedFieldCyclotomicFiniteLayer_layerAlgebra _root_.GlobalClassFieldTheory.Reciprocity.abstractFixedFieldCyclotomicFiniteLayer_layerSMul _root_.GlobalClassFieldTheory.Reciprocity.abstractFixedFieldCyclotomicFiniteLayer_layerScalarTower _root_.GlobalClassFieldTheory.Reciprocity.abstractFixedFieldCyclotomicFiniteLayer_numberField _root_.GlobalClassFieldTheory.Reciprocity.infinitePlaceComplexificationOverfield_baseSmul _root_.GlobalClassFieldTheory.Reciprocity.infinitePlaceComplexificationOverfield_smul _root_.GlobalClassFieldTheory.Reciprocity.rationalComplexification_infinitePlaceOverfield_algebra _root_.GlobalClassFieldTheory.Reciprocity.rationalComplexification_infinitePlaceOverfield_smul _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.boundedRealFields_finite _root_.OAI.PrimeDegreePackets.instTopologicalSpaceLocalAlgebra _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.GlobalClassFieldTheory.GlobalClassFields.bigHilbertNormQuotient_finite _root_.GlobalClassFieldTheory.GlobalClassFields.bigHilbertNormSubgroup_finiteIndex _root_.GlobalClassFieldTheory.GlobalClassFields.narrowClassGroup_finite _root_.GlobalClassFieldTheory.Reciprocity.cyclotomicUnramifiedGeometricMaxExtensionNormal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

/-!
# Class fields from ordinary idele-class norm neighbourhoods

An actual finite Galois norm subgroup contained in an ordinary
idele-class subgroup makes the transported subgroup norm-open in the
rational absolute class formation.  Finite abelian classification then
constructs its class field.  The final theorem below transports the
result back to the ordinary idele class group of the actual fixed field,
so its conclusion is an equality of genuine determinant-norm ranges.
-/

open scoped NumberField

noncomputable section

namespace GlobalClassFieldTheory
namespace GlobalClassFields

open ClassFormation
open LocalClassFieldTheory
open Reciprocity

attribute [local instance] ordinaryNormClassFieldIdeleClassCommGroup

variable
    (K L : Type) [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]

/- The fixed-field typeclass data used by the topology comparison are kept
behind named constants.  This prevents every consumer from rebuilding the
same finite-dimensional and number-field proof terms while reducing the
dependent fixed-field type. -/

noncomputable instance ordinaryNormClassFieldExtensionFiniteDimensional
    (H : Subgroup (IdeleClassGroup K))
    (hLH : (_root_.ideleClassNorm K L).range ≤ H) :
    FiniteDimensional (ordinaryNormClassFieldBase K L)
      (ordinaryNormClassFieldExtension K L H hLH) :=
  abstractRelativeFixedField_finiteDimensional
    ℚ (SeparableClosure ℚ)
    (numberFieldTowerBaseSubgroup K L)
    (ordinaryNormClassFieldSubextension K L H hLH).field
    (ordinaryNormClassFieldSubextension K L H hLH).below
    (numberFieldTowerBaseSubgroupAbsoluteQuotientFinite K L)
    (ordinaryNormClassFieldSubextension K L H hLH).finite

noncomputable instance ordinaryNormClassFieldScalarTower
    (H : Subgroup (IdeleClassGroup K))
    (hLH : (_root_.ideleClassNorm K L).range ≤ H) :
    IsScalarTower ℚ (ordinaryNormClassFieldBase K L)
      (ordinaryNormClassFieldExtension K L H hLH) :=
  IsScalarTower.of_algebraMap_eq' (RingHom.ext_rat _ _)

noncomputable instance ordinaryNormClassFieldAbsoluteFiniteDimensional
    (H : Subgroup (IdeleClassGroup K))
    (hLH : (_root_.ideleClassNorm K L).range ≤ H) :
    FiniteDimensional ℚ
      (ordinaryNormClassFieldExtension K L H hLH) :=
  FiniteDimensional.trans ℚ (ordinaryNormClassFieldBase K L)
    (ordinaryNormClassFieldExtension K L H hLH)

noncomputable instance ordinaryNormClassFieldExtensionNumberField
    (H : Subgroup (IdeleClassGroup K))
    (hLH : (_root_.ideleClassNorm K L).range ≤ H) :
    NumberField (ordinaryNormClassFieldExtension K L H hLH) :=
  NumberField.of_module_finite ℚ
    (ordinaryNormClassFieldExtension K L H hLH)

noncomputable instance ordinaryNormClassFieldExtensionIsAbelianGalois
    (H : Subgroup (IdeleClassGroup K))
    (hLH : (_root_.ideleClassNorm K L).range ≤ H) :
    IsAbelianGalois (ordinaryNormClassFieldBase K L)
      (ordinaryNormClassFieldExtension K L H hLH) :=
  finiteAbelianSubextensionAbstractRelativeFixedFieldIsAbelianGalois
    (ordinaryNormClassFieldSubextension K L H hLH)

end GlobalClassFields
end GlobalClassFieldTheory
end
end

section
-- module Solutions.OAIQ244_DUKE.GlobalClassFieldTheory_GlobalClassFields_ClosedFiniteIndexClassFieldOriginalField
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 400000
attribute [-instance] _root_.GlobalClassFieldTheory.GlobalClassFields.bigHilbertClassFieldAlgebraOverOriginal _root_.GlobalClassFieldTheory.GlobalClassFields.bigHilbertClassFieldBaseAlgebraOverOriginal _root_.GlobalClassFieldTheory.GlobalClassFields.bigHilbertClassFieldIsGaloisOverOriginal _root_.GlobalClassFieldTheory.GlobalClassFields.bigHilbertClassFieldNormSubgroupFiniteIndex _root_.GlobalClassFieldTheory.GlobalClassFields.bigHilbertClassFieldNormSubgroup_normal _root_.GlobalClassFieldTheory.GlobalClassFields.bigHilbertClassFieldScalarTowerOverOriginal _root_.GlobalClassFieldTheory.GlobalClassFields.smallHilbertClassFieldAlgebraOverOriginal _root_.GlobalClassFieldTheory.GlobalClassFields.smallHilbertClassFieldBaseAlgebraOverOriginal _root_.GlobalClassFieldTheory.GlobalClassFields.smallHilbertClassFieldNormSubgroupFiniteIndex _root_.GlobalClassFieldTheory.Reciprocity.abstractFixedFieldCyclotomicCompositum_algebra _root_.GlobalClassFieldTheory.Reciprocity.abstractFixedFieldCyclotomicCompositum_baseScalarTower _root_.GlobalClassFieldTheory.Reciprocity.abstractFixedFieldCyclotomicCompositum_scalarTower _root_.GlobalClassFieldTheory.Reciprocity.abstractFixedFieldCyclotomicFiniteCompositum_baseAlgebra _root_.GlobalClassFieldTheory.Reciprocity.abstractFixedFieldCyclotomicFiniteCompositum_baseScalarTower _root_.GlobalClassFieldTheory.Reciprocity.abstractFixedFieldCyclotomicFiniteGaloisLayer_scalarTower _root_.GlobalClassFieldTheory.Reciprocity.abstractFixedFieldCyclotomicFiniteLayer_baseAlgebra _root_.GlobalClassFieldTheory.Reciprocity.abstractFixedFieldCyclotomicFiniteLayer_baseModule _root_.GlobalClassFieldTheory.Reciprocity.abstractFixedFieldCyclotomicFiniteLayer_baseSMul _root_.GlobalClassFieldTheory.Reciprocity.abstractFixedFieldCyclotomicFiniteLayer_baseScalarTower _root_.GlobalClassFieldTheory.Reciprocity.abstractFixedFieldCyclotomicFiniteLayer_finiteDimensional _root_.GlobalClassFieldTheory.Reciprocity.abstractFixedFieldCyclotomicFiniteLayer_isAbelianGalois _root_.GlobalClassFieldTheory.Reciprocity.abstractFixedFieldCyclotomicFiniteLayer_layerAlgebra _root_.GlobalClassFieldTheory.Reciprocity.abstractFixedFieldCyclotomicFiniteLayer_layerSMul _root_.GlobalClassFieldTheory.Reciprocity.abstractFixedFieldCyclotomicFiniteLayer_layerScalarTower _root_.GlobalClassFieldTheory.Reciprocity.abstractFixedFieldCyclotomicFiniteLayer_numberField _root_.GlobalClassFieldTheory.Reciprocity.infinitePlaceComplexificationOverfield_algebra _root_.GlobalClassFieldTheory.Reciprocity.infinitePlaceComplexificationOverfield_baseAlgebra _root_.GlobalClassFieldTheory.Reciprocity.ramifiedInfinitePlaceRealFixedField_algebra _root_.GlobalClassFieldTheory.Reciprocity.rationalComplexification_infinitePlaceOverfield_algebra _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.instTopologicalSpaceLocalAlgebra _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.GlobalClassFieldTheory.GlobalClassFields.bigHilbertNormQuotient_finite _root_.GlobalClassFieldTheory.GlobalClassFields.bigHilbertNormSubgroup_finiteIndex _root_.GlobalClassFieldTheory.Reciprocity.cyclotomicUnramifiedGeometricMaxExtensionNormal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI
attribute [local instance] OAI.starSubalgebraCommCStarAlgebra

set_option autoImplicit false

/-!
# Transport to the original number field

This leaf installs the original-field algebra tower and transports the
canonical norm-range computation back to the original idèle class group.
-/

open scoped Classical IsMulCommutative NumberField

noncomputable section

namespace GlobalClassFieldTheory
namespace GlobalClassFields

open Reciprocity

variable {K : Type} [Field K] [NumberField K]

noncomputable instance closedFiniteIndexClassFieldIsGaloisOverOriginal
    (H : Subgroup (IdeleClassGroup K))
    (hclosed : IsClosed (H : Set (IdeleClassGroup K)))
    [H.FiniteIndex] :
    IsGalois K
      (closedFiniteIndexClassField
        (K := K) H hclosed) := by
  let e :=
    closedFiniteIndexClassFieldBaseEquiv
      (K := K) H hclosed
  apply IsGalois.of_equiv_equiv
    (F := closedFiniteIndexClassFieldBase
      (K := K) H hclosed)
    (E := closedFiniteIndexClassField
      (K := K) H hclosed)
    (f := e.symm.toRingEquiv)
    (g := RingEquiv.refl
      (closedFiniteIndexClassField
        (K := K) H hclosed))
  apply RingHom.ext
  intro x
  calc
    ((algebraMap K
        (closedFiniteIndexClassField
          (K := K) H hclosed)).comp e.symm.toRingEquiv) x =
        algebraMap K
          (closedFiniteIndexClassField
            (K := K) H hclosed) (e.symm x) := rfl
    _ = algebraMap
          (closedFiniteIndexClassFieldBase
            (K := K) H hclosed)
          (closedFiniteIndexClassField
            (K := K) H hclosed)
          (closedFiniteIndexClassFieldBaseEquiv
            (K := K) H hclosed (e.symm x)) :=
      closedFiniteIndexClassField_algebraMap_original
        (K := K) H hclosed (e.symm x)
    _ = algebraMap
          (closedFiniteIndexClassFieldBase
            (K := K) H hclosed)
          (closedFiniteIndexClassField
            (K := K) H hclosed) x := by
      simpa only [e] using
        congrArg
          (algebraMap
            (closedFiniteIndexClassFieldBase
              (K := K) H hclosed)
            (closedFiniteIndexClassField
              (K := K) H hclosed))
          ((closedFiniteIndexClassFieldBaseEquiv
            (K := K) H hclosed).apply_symm_apply x)
    _ = ((RingEquiv.refl
          (closedFiniteIndexClassField
            (K := K) H hclosed)).toRingHom.comp
        (algebraMap
          (closedFiniteIndexClassFieldBase
            (K := K) H hclosed)
          (closedFiniteIndexClassField
            (K := K) H hclosed))) x := rfl

end GlobalClassFields
end GlobalClassFieldTheory
end
end

section
-- module Solutions.OAIQ244_DUKE.GlobalClassFieldTheory_Reciprocity_GlobalNormResidueNaturality
attribute [-instance] _root_.GlobalClassFieldTheory.GlobalClassFields.bigHilbertClassFieldAlgebraOverOriginal _root_.GlobalClassFieldTheory.GlobalClassFields.bigHilbertClassFieldBaseAlgebraOverOriginal _root_.GlobalClassFieldTheory.GlobalClassFields.bigHilbertClassFieldIsGaloisOverOriginal _root_.GlobalClassFieldTheory.GlobalClassFields.bigHilbertClassFieldNormSubgroup_normal _root_.GlobalClassFieldTheory.GlobalClassFields.bigHilbertClassFieldScalarTowerOverOriginal _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexClassFieldAlgebraOverOriginal _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexClassFieldBaseAlgebraOverOriginal _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexClassFieldIsGaloisOverOriginal _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexClassFieldScalarTowerOverOriginal _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexNormAmbientFiniteDimensional _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexNormAmbientIsGalois _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexNormAmbientNumberField _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexNormCyclotomicFieldFiniteDimensional _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexNormCyclotomicFieldIsGalois _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexNormCyclotomicFieldNumberField _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexNormKummerFieldAlgebraOverBase _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexNormKummerFieldFiniteDimensional _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexNormKummerFieldFiniteDimensionalOverBase _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexNormKummerFieldModuleOverBase _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexNormKummerFieldNumberField _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexNormKummerFieldSMulOverBase _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexNormKummerFieldScalarTower _root_.GlobalClassFieldTheory.GlobalClassFields.ordinaryNormClassFieldAbsoluteFiniteDimensional _root_.GlobalClassFieldTheory.GlobalClassFields.ordinaryNormClassFieldBaseFiniteDimensional _root_.GlobalClassFieldTheory.GlobalClassFields.ordinaryNormClassFieldBaseNumberField _root_.GlobalClassFieldTheory.GlobalClassFields.ordinaryNormClassFieldExtensionFiniteDimensional _root_.GlobalClassFieldTheory.GlobalClassFields.ordinaryNormClassFieldExtensionIsAbelianGalois _root_.GlobalClassFieldTheory.GlobalClassFields.ordinaryNormClassFieldExtensionIsGalois _root_.GlobalClassFieldTheory.GlobalClassFields.ordinaryNormClassFieldExtensionNumberField _root_.GlobalClassFieldTheory.GlobalClassFields.ordinaryNormClassFieldScalarTower _root_.GlobalClassFieldTheory.GlobalClassFields.smallHilbertClassFieldAlgebraOverOriginal _root_.GlobalClassFieldTheory.GlobalClassFields.smallHilbertClassFieldBaseAlgebraOverOriginal _root_.GlobalClassFieldTheory.Reciprocity.abstractFixedFieldCyclotomicCompositum_algebra _root_.GlobalClassFieldTheory.Reciprocity.abstractFixedFieldCyclotomicCompositum_baseScalarTower _root_.GlobalClassFieldTheory.Reciprocity.abstractFixedFieldCyclotomicCompositum_scalarTower _root_.GlobalClassFieldTheory.Reciprocity.abstractFixedFieldCyclotomicFiniteCompositum_baseAlgebra _root_.GlobalClassFieldTheory.Reciprocity.abstractFixedFieldCyclotomicFiniteCompositum_baseScalarTower _root_.GlobalClassFieldTheory.Reciprocity.abstractFixedFieldCyclotomicFiniteCompositum_finiteDimensional _root_.GlobalClassFieldTheory.Reciprocity.abstractFixedFieldCyclotomicFiniteCompositum_numberField _root_.GlobalClassFieldTheory.Reciprocity.abstractFixedFieldCyclotomicFiniteGaloisLayer_scalarTower _root_.GlobalClassFieldTheory.Reciprocity.abstractFixedFieldCyclotomicFiniteLayer_baseAlgebra _root_.GlobalClassFieldTheory.Reciprocity.abstractFixedFieldCyclotomicFiniteLayer_baseModule _root_.GlobalClassFieldTheory.Reciprocity.abstractFixedFieldCyclotomicFiniteLayer_baseSMul _root_.GlobalClassFieldTheory.Reciprocity.abstractFixedFieldCyclotomicFiniteLayer_baseScalarTower _root_.GlobalClassFieldTheory.Reciprocity.abstractFixedFieldCyclotomicFiniteLayer_finiteDimensional _root_.GlobalClassFieldTheory.Reciprocity.abstractFixedFieldCyclotomicFiniteLayer_isAbelianGalois _root_.GlobalClassFieldTheory.Reciprocity.abstractFixedFieldCyclotomicFiniteLayer_layerAlgebra _root_.GlobalClassFieldTheory.Reciprocity.abstractFixedFieldCyclotomicFiniteLayer_layerSMul _root_.GlobalClassFieldTheory.Reciprocity.abstractFixedFieldCyclotomicFiniteLayer_layerScalarTower _root_.GlobalClassFieldTheory.Reciprocity.abstractFixedFieldCyclotomicFiniteLayer_numberField _root_.GlobalClassFieldTheory.Reciprocity.complexFourthRootField_finiteDimensional _root_.GlobalClassFieldTheory.Reciprocity.complexFourthRootField_numberField _root_.GlobalClassFieldTheory.Reciprocity.infinitePlaceComplexificationOverfield_algebra _root_.GlobalClassFieldTheory.Reciprocity.infinitePlaceComplexificationOverfield_baseAlgebra _root_.GlobalClassFieldTheory.Reciprocity.infinitePlaceComplexificationOverfield_baseSmul _root_.GlobalClassFieldTheory.Reciprocity.infinitePlaceComplexificationOverfield_finiteDimensional _root_.GlobalClassFieldTheory.Reciprocity.infinitePlaceComplexificationOverfield_numberField _root_.GlobalClassFieldTheory.Reciprocity.infinitePlaceComplexificationOverfield_smul _root_.GlobalClassFieldTheory.Reciprocity.ramifiedInfinitePlaceRealFixedField_algebra _root_.GlobalClassFieldTheory.Reciprocity.ramifiedInfinitePlaceRealFixedField_numberField _root_.GlobalClassFieldTheory.Reciprocity.rationalComplexification_infinitePlaceOverfield_algebra _root_.GlobalClassFieldTheory.Reciprocity.rationalComplexification_infinitePlaceOverfield_smul _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.boundedRealFields_numberField _root_.OAI.PrimeDegreePackets.diagonalLogAction _root_.OAI.PrimeDegreePackets.instTopologicalSpaceLocalAlgebra _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.GlobalClassFieldTheory.Reciprocity.cyclotomicUnramifiedGeometricMaxExtensionNormal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI
attribute [local instance] OAI.starSubalgebraCommCStarAlgebra

set_option autoImplicit false

/-!
# Naturality of the global norm-residue symbol

This file records the same-base restriction specialization of abstract
norm-residue naturality in the rational absolute class formation.  All
closed subgroups remain in one fixed separable-closure ambient, so the
statement is directly usable by fixed-field overextension arguments.
-/

open scoped IsMulCommutative

noncomputable section

namespace GlobalClassFieldTheory
namespace Reciprocity

open ClassFormation
open GlobalClassFields
open KummerTheory
open AlgebraicNumberTheory
open LocalClassFieldTheory
open RamificationTheory

universe u

attribute [local instance] naturalityIdeleClassCommGroup

section AbstractFixedFieldInclusion

local instance ideleClassGroupIsMulCommutative_r7b74b3_1
    {F : Type} [Field F] [NumberField F]
    : IsMulCommutative (IdeleClassGroup F) :=
  ⟨⟨fun a b => mul_comm a b⟩⟩
local instance ideleClassSubgroupNormal_r7b74b3_1
    {F : Type} [Field F] [NumberField F]
    (N : Subgroup (IdeleClassGroup F)) : N.Normal :=
  N.normal_of_isMulCommutative
variable
    (H : FiniteAbstractField
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
    (P : FiniteAbelianSubextension H.field)

attribute [local instance] GlobalClassFieldTheory.Reciprocity.naturalityAbstractFixedFieldBaseQuotientFinite
attribute [local instance] GlobalClassFieldTheory.Reciprocity.naturalityAbstractFixedFieldRelativeQuotientFinite
attribute [local instance] GlobalClassFieldTheory.Reciprocity.naturalityAbstractFixedFieldFiniteDimensional
attribute [local instance] GlobalClassFieldTheory.Reciprocity.naturalityAbstractRelativeFixedFieldFiniteDimensional
attribute [local instance] GlobalClassFieldTheory.Reciprocity.naturalityAbstractFixedFieldRelativeScalarTower
attribute [local instance] GlobalClassFieldTheory.Reciprocity.naturalityAbstractRelativeFixedFieldAbsoluteFiniteDimensional
attribute [local instance] GlobalClassFieldTheory.Reciprocity.naturalityAbstractFixedFieldNumberField
attribute [local instance] GlobalClassFieldTheory.Reciprocity.naturalityAbstractRelativeFixedFieldNumberField
attribute [local instance] GlobalClassFieldTheory.Reciprocity.naturalityAbstractRelativeFixedFieldIsGalois
attribute [local instance] GlobalClassFieldTheory.Reciprocity.naturalityAbstractRelativeFixedFieldIsAbelianGalois
/-- Opaque canonical endpoint for the same quotient, obtained directly from
the abstract fixed-field realization. -/
noncomputable def
    abstractFixedFieldInclusionCanonicalExtensionQuotientEquiv
    (H : FiniteAbstractField
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
    (P : FiniteAbelianSubextension H.field) :
    P.toFiniteGaloisExtension.extensionQuotient ≃*
      Gal(
        (abstractRelativeFixedField
          ℚ (SeparableClosure ℚ) P.below) /
        (abstractFixedField ℚ (SeparableClosure ℚ) H.field)) := by
  exact
    P.toFiniteGaloisExtension.extensionQuotientMulEquiv.trans
      (abstractExtensionQuotientEquivGaloisGroup
        ℚ (SeparableClosure ℚ)
        H.field P.field P.below P.normal)

/-- Pointwise opaque endpoint of the embedded quotient equivalence. -/
noncomputable def
    abstractFixedFieldInclusionEmbeddedExtensionQuotientValue
    (H : FiniteAbstractField
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
    (P : FiniteAbelianSubextension H.field)
    (q : P.toFiniteGaloisExtension.extensionQuotient) :
    Gal(
      (abstractRelativeFixedField
        ℚ (SeparableClosure ℚ) P.below) /
      (abstractFixedField ℚ (SeparableClosure ℚ) H.field)) :=
  abstractFixedFieldInclusionEmbeddedExtensionQuotientEquiv H P q

/-- Pointwise opaque endpoint of the canonical quotient equivalence. -/
noncomputable def
    abstractFixedFieldInclusionCanonicalExtensionQuotientValue
    (H : FiniteAbstractField
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
    (P : FiniteAbelianSubextension H.field)
    (q : P.toFiniteGaloisExtension.extensionQuotient) :
    Gal(
      (abstractRelativeFixedField
        ℚ (SeparableClosure ℚ) P.below) /
      (abstractFixedField ℚ (SeparableClosure ℚ) H.field)) :=
  abstractFixedFieldInclusionCanonicalExtensionQuotientEquiv H P q

/-- Fully applied ambient value of the embedded quotient endpoint. -/
noncomputable def
    abstractFixedFieldInclusionEmbeddedExtensionQuotientApplyVal
    (H : FiniteAbstractField
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
    (P : FiniteAbelianSubextension H.field)
    (q : P.toFiniteGaloisExtension.extensionQuotient)
    (x : abstractRelativeFixedField
      ℚ (SeparableClosure ℚ) P.below) : SeparableClosure ℚ :=
  (abstractFixedFieldInclusionEmbeddedExtensionQuotientValue H P q x :
    SeparableClosure ℚ)

/-- Fully applied ambient value of the canonical quotient endpoint. -/
noncomputable def
    abstractFixedFieldInclusionCanonicalExtensionQuotientApplyVal
    (H : FiniteAbstractField
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
    (P : FiniteAbelianSubextension H.field)
    (q : P.toFiniteGaloisExtension.extensionQuotient)
    (x : abstractRelativeFixedField
      ℚ (SeparableClosure ℚ) P.below) : SeparableClosure ℚ :=
  (abstractFixedFieldInclusionCanonicalExtensionQuotientValue H P q x :
    SeparableClosure ℚ)

/-- The ambient Galois value attached to a representative of the canonical
quotient, packaged behind a literal result type. -/
noncomputable def
    abstractFixedFieldInclusionAmbientEmbeddedQuotientMkValue
    (H : FiniteAbstractField
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
    (P : FiniteAbelianSubextension H.field)
    (σ : H.field.toSubgroup) :
    Gal(
      (abstractRelativeFixedField
        ℚ (SeparableClosure ℚ) P.below) /
      (abstractFixedField ℚ (SeparableClosure ℚ) H.field)) := by
  let F :=
    abstractFixedField ℚ (SeparableClosure ℚ) H.field
  let E :=
    abstractRelativeFixedField
      ℚ (SeparableClosure ℚ) P.below
  let j : E →ₐ[ℚ] SeparableClosure ℚ :=
    E.val.restrictScalars ℚ
  have hBase :
      numberFieldEmbeddedBaseSubgroup F E j = H.field :=
    numberFieldEmbeddedBaseSubgroup_abstractFixedFieldInclusion H P
  letI hAlgebra : Algebra F (SeparableClosure ℚ) :=
    numberFieldEmbeddedSeparableClosureAlgebra F E j
  let eSep :=
    numberFieldEmbeddedSeparableClosureEquiv F E j
  letI hEmbeddedExtensionNormal :
      (CyclicCohomology.extensionSubgroup
        (numberFieldEmbeddedBaseSubgroup F E j)
        (numberFieldEmbeddedTopSubgroup F E j)
        (numberFieldEmbeddedTopSubgroup_le_baseSubgroup F E j)).Normal :=
    numberFieldEmbeddedExtensionSubgroup_normal F E j
  let σEmbedded :
      (numberFieldEmbeddedBaseSubgroup F E j).toSubgroup :=
    (MulEquiv.subgroupCongr
      (congrArg ClosedSubgroup.toSubgroup hBase.symm)) σ
  exact
    ambientEmbeddedExtensionQuotientEquivGaloisGroup
      ℚ F E j eSep (QuotientGroup.mk σEmbedded)

/-- Fully applied ambient value of the packaged representative endpoint. -/
noncomputable def
    abstractFixedFieldInclusionAmbientEmbeddedQuotientMkApplyVal
    (H : FiniteAbstractField
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
    (P : FiniteAbelianSubextension H.field)
    (σ : H.field.toSubgroup)
    (x : abstractRelativeFixedField
      ℚ (SeparableClosure ℚ) P.below) : SeparableClosure ℚ :=
  (abstractFixedFieldInclusionAmbientEmbeddedQuotientMkValue H P σ x :
    SeparableClosure ℚ)

/-- Evaluation of the canonical abstract quotient endpoint on a quotient
representative, again exposed only through its ambient value. -/
theorem
    abstractFixedFieldInclusionCanonicalExtensionQuotientEquiv_mk_val
    (H : FiniteAbstractField
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
    (P : FiniteAbelianSubextension H.field)
    (σ : H.field.toSubgroup)
    (x : abstractRelativeFixedField
      ℚ (SeparableClosure ℚ) P.below) :
    abstractFixedFieldInclusionCanonicalExtensionQuotientApplyVal H P
        (P.toFiniteGaloisExtension.extensionQuotientMk σ) x =
      σ.1.1 (x : SeparableClosure ℚ) := by
  simp only [
    abstractFixedFieldInclusionCanonicalExtensionQuotientApplyVal,
    abstractFixedFieldInclusionCanonicalExtensionQuotientValue,
    abstractFixedFieldInclusionCanonicalExtensionQuotientEquiv,
    MulEquiv.trans_apply,
    FiniteGaloisSubextension.extensionQuotientMk_apply]
  exact
    (abstractExtensionQuotientEquivGaloisGroup_mk_apply_val
      ℚ (SeparableClosure ℚ)
      H.field P.field P.below P.normal σ x).symm

/-- Pointwise opaque value of the canonical abelianization comparison built
from the transported quotient endpoint. -/
noncomputable def
    abstractFixedFieldInclusionTransportedCanonicalAbelianizedValue
    (H : FiniteAbstractField
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
    (P : FiniteAbelianSubextension H.field)
    (z : Additive
      (Abelianization P.toFiniteGaloisExtension.extensionQuotient)) :
    Additive
      (Gal(
        (abstractRelativeFixedField
          ℚ (SeparableClosure ℚ) P.below) /
        (abstractFixedField ℚ (SeparableClosure ℚ) H.field))) :=
  abstractFixedFieldInclusionTransportedCanonicalAbelianizedEquiv H P z

/-- The transported abelianized endpoint agrees pointwise with the canonical
abelianization comparison built from the transported quotient endpoint. -/
theorem
    abstractFixedFieldInclusionTransportedAbelianizedValue_eq_canonical
    (H : FiniteAbstractField
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
    (P : FiniteAbelianSubextension H.field)
    (z : Additive
      (Abelianization P.toFiniteGaloisExtension.extensionQuotient)) :
    abstractFixedFieldInclusionTransportedAbelianizedValue H P z =
      abstractFixedFieldInclusionTransportedCanonicalAbelianizedValue
        H P z := by
  let F :=
    abstractFixedField ℚ (SeparableClosure ℚ) H.field
  let E :=
    abstractRelativeFixedField
      ℚ (SeparableClosure ℚ) P.below
  let j : E →ₐ[ℚ] SeparableClosure ℚ :=
    E.val.restrictScalars ℚ
  let HEmbedded :=
    numberFieldEmbeddedFiniteAbstractField F E j
  let PEmbedded : FiniteGaloisSubextension HEmbedded.field :=
    numberFieldEmbeddedFiniteGaloisSubextension F E j
  have hHEmbedded : HEmbedded = H :=
    numberFieldEmbeddedFiniteAbstractField_abstractFixedFieldInclusion H P
  have hPEmbedded :
      Eq.mp
          (congrArg
            (fun X : FiniteAbstractField
                (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ) =>
              FiniteGaloisSubextension X.field)
            hHEmbedded)
          PEmbedded =
        P.toFiniteGaloisExtension :=
    numberFieldEmbeddedFiniteGaloisSubextension_transport_eq H P
  let qEmbedded : PEmbedded.extensionQuotient ≃* Gal(E / F) :=
    numberFieldEmbeddedExtensionQuotientEquivGaloisGroup F E j
  have hCanonical :
      abstractFixedFieldInclusionTransportedAbelianizedEquiv H P =
        abstractFixedFieldInclusionTransportedCanonicalAbelianizedEquiv
          H P := by
    simpa only [
      abstractFixedFieldInclusionTransportedAbelianizedEquiv,
      abstractFixedFieldInclusionTransportedCanonicalAbelianizedEquiv,
      abstractFixedFieldInclusionTransportedExtensionQuotientEquiv,
      numberFieldEmbeddedAbelianizedExtensionQuotientEquivGaloisGroup,
      qEmbedded] using
      (abelianizedCanonicalEquiv_transportFiniteGalois
        hHEmbedded PEmbedded hPEmbedded qEmbedded)
  exact DFunLike.congr_fun hCanonical z

/-- On the same representative, the intrinsic fixed-field endpoint is the
additive value of the canonical quotient endpoint. -/
theorem
    abstractFixedFieldInclusionCanonicalAbelianizedValue_of
    (H : FiniteAbstractField
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
    (P : FiniteAbelianSubextension H.field)
    (q : P.toFiniteGaloisExtension.extensionQuotient) :
    abstractFixedFieldInclusionCanonicalAbelianizedValue H P
        (Additive.ofMul (Abelianization.of q)) =
      Additive.ofMul
        (abstractFixedFieldInclusionCanonicalExtensionQuotientValue
          H P q) := by
  let hRawQuotientCommGroup :
      CommGroup P.toFiniteGaloisExtension.extensionQuotient :=
    { (inferInstance :
        Group P.toFiniteGaloisExtension.extensionQuotient) with
      mul_comm := P.commutative.is_comm.comm }
  let qAbstractRaw :=
    abstractFixedFieldInclusionCanonicalExtensionQuotientEquiv H P
  change
    MulEquiv.toAdditive
        ((Abelianization.equivOfComm :
          P.toFiniteGaloisExtension.extensionQuotient ≃*
            Abelianization
              P.toFiniteGaloisExtension.extensionQuotient).symm.trans
          qAbstractRaw)
        (Additive.ofMul (Abelianization.of q)) =
      Additive.ofMul (qAbstractRaw q)
  exact commutativeAbelianizationEquiv_apply qAbstractRaw q

end AbstractFixedFieldInclusion

end Reciprocity
end GlobalClassFieldTheory
end
end

section
-- module Solutions.OAIQ244_DUKE.GlobalClassFieldTheory_GlobalClassFields_FiniteAbelianClassFieldContainment
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 400000
attribute [-instance] _root_.GlobalClassFieldTheory.GlobalClassFields.bigHilbertClassFieldAlgebraOverOriginal _root_.GlobalClassFieldTheory.GlobalClassFields.bigHilbertClassFieldBaseAlgebraOverOriginal _root_.GlobalClassFieldTheory.GlobalClassFields.bigHilbertClassFieldIsGaloisOverOriginal _root_.GlobalClassFieldTheory.GlobalClassFields.bigHilbertClassFieldNormSubgroupFiniteIndex _root_.GlobalClassFieldTheory.GlobalClassFields.bigHilbertClassFieldNormSubgroup_normal _root_.GlobalClassFieldTheory.GlobalClassFields.bigHilbertClassFieldScalarTowerOverOriginal _root_.GlobalClassFieldTheory.GlobalClassFields.smallHilbertClassFieldAlgebraOverOriginal _root_.GlobalClassFieldTheory.GlobalClassFields.smallHilbertClassFieldBaseAlgebraOverOriginal _root_.GlobalClassFieldTheory.GlobalClassFields.smallHilbertClassFieldNormSubgroupFiniteIndex _root_.GlobalClassFieldTheory.Reciprocity.abstractFixedFieldCyclotomicCompositum_algebra _root_.GlobalClassFieldTheory.Reciprocity.abstractFixedFieldCyclotomicCompositum_baseScalarTower _root_.GlobalClassFieldTheory.Reciprocity.abstractFixedFieldCyclotomicCompositum_scalarTower _root_.GlobalClassFieldTheory.Reciprocity.abstractFixedFieldCyclotomicFiniteCompositum_baseAlgebra _root_.GlobalClassFieldTheory.Reciprocity.abstractFixedFieldCyclotomicFiniteCompositum_baseScalarTower _root_.GlobalClassFieldTheory.Reciprocity.abstractFixedFieldCyclotomicFiniteGaloisLayer_scalarTower _root_.GlobalClassFieldTheory.Reciprocity.abstractFixedFieldCyclotomicFiniteLayer_baseAlgebra _root_.GlobalClassFieldTheory.Reciprocity.abstractFixedFieldCyclotomicFiniteLayer_baseModule _root_.GlobalClassFieldTheory.Reciprocity.abstractFixedFieldCyclotomicFiniteLayer_baseSMul _root_.GlobalClassFieldTheory.Reciprocity.abstractFixedFieldCyclotomicFiniteLayer_baseScalarTower _root_.GlobalClassFieldTheory.Reciprocity.abstractFixedFieldCyclotomicFiniteLayer_finiteDimensional _root_.GlobalClassFieldTheory.Reciprocity.abstractFixedFieldCyclotomicFiniteLayer_isAbelianGalois _root_.GlobalClassFieldTheory.Reciprocity.abstractFixedFieldCyclotomicFiniteLayer_layerAlgebra _root_.GlobalClassFieldTheory.Reciprocity.abstractFixedFieldCyclotomicFiniteLayer_layerSMul _root_.GlobalClassFieldTheory.Reciprocity.abstractFixedFieldCyclotomicFiniteLayer_layerScalarTower _root_.GlobalClassFieldTheory.Reciprocity.abstractFixedFieldCyclotomicFiniteLayer_numberField _root_.GlobalClassFieldTheory.Reciprocity.infinitePlaceComplexificationOverfield_algebra _root_.GlobalClassFieldTheory.Reciprocity.infinitePlaceComplexificationOverfield_baseAlgebra _root_.GlobalClassFieldTheory.Reciprocity.ramifiedInfinitePlaceRealFixedField_algebra _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.instTopologicalSpaceLocalAlgebra _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.GlobalClassFieldTheory.GlobalClassFields.bigHilbertNormQuotient_finite _root_.GlobalClassFieldTheory.GlobalClassFields.bigHilbertNormSubgroup_finiteIndex _root_.GlobalClassFieldTheory.Reciprocity.cyclotomicUnramifiedGeometricMaxExtensionNormal
attribute [-simp] _root_.GlobalClassFieldTheory.ClassFieldAxiom.hasseNormDiagonal_mk _root_.GlobalClassFieldTheory.GlobalClassFields.ConductorialSubgroup.mem_fullConductorInfinitePart_iff _root_.GlobalClassFieldTheory.GlobalClassFields.bigHilbertClassFieldBaseEquiv_coe _root_.GlobalClassFieldTheory.GlobalClassFields.bigHilbertClassFieldQuotientCongr_mk _root_.GlobalClassFieldTheory.GlobalClassFields.bigHilbertClassFieldQuotientEquivNarrowClassGroup_mk _root_.GlobalClassFieldTheory.GlobalClassFields.bigHilbertClassFieldQuotientToIdeleClassNormQuotient_mk _root_.GlobalClassFieldTheory.GlobalClassFields.bigHilbertClassFieldQuotientToSmallHilbertClassFieldQuotient_mk _root_.GlobalClassFieldTheory.GlobalClassFields.bigHilbertClassField_algebraMap_original _root_.GlobalClassFieldTheory.GlobalClassFields.idealArtinMap_primeToIdealMap _root_.GlobalClassFieldTheory.GlobalClassFields.idealRayProjection_finitePrimeIdele _root_.GlobalClassFieldTheory.GlobalClassFields.narrowFiniteConductorRayClassGroupToIdeleClassNormQuotient_rayPrimeClass _root_.GlobalClassFieldTheory.GlobalClassFields.normQuotientEquivOfNarrowFiniteConductorsEqOfRayClassGroupCardsEqNormQuotientCards_mk _root_.GlobalClassFieldTheory.GlobalClassFields.primeToIdealMap_finitePrimeIdele _root_.GlobalClassFieldTheory.GlobalClassFields.rayClassGroupEquivIdealRayClassGroup_mk_primeTo _root_.GlobalClassFieldTheory.GlobalClassFields.rayClassGroupEquivIdeleQuotient_mk_mk _root_.GlobalClassFieldTheory.GlobalClassFields.realSignToBigHilbertClassFieldQuotient_apply _root_.GlobalClassFieldTheory.GlobalClassFields.realSignToNarrowClassKernel_apply _root_.GlobalClassFieldTheory.GlobalClassFields.smallHilbertClassFieldQuotientCongr_mk _root_.GlobalClassFieldTheory.GlobalClassFields.smallHilbertClassFieldQuotientEquivClassGroup_mk _root_.GlobalClassFieldTheory.GlobalClassFields.smallHilbertClassFieldQuotientToIdeleClassNormQuotient_mk _root_.GlobalClassFieldTheory.GlobalClassFields.smallHilbertClassField_algebraMap_original _root_.GlobalClassFieldTheory.IdealClassFieldTheory.idealArtinGaloisMap_apply _root_.GlobalClassFieldTheory.IdealClassFieldTheory.idealArtinGaloisMap_ker _root_.GlobalClassFieldTheory.IdealClassFieldTheory.idealClassQuotientEquivGaloisGroup_mk _root_.GlobalClassFieldTheory.IdealClassFieldTheory.idealClassQuotientEquivNormQuotient_mk _root_.GlobalClassFieldTheory.IdealClassFieldTheory.rayClassToNormQuotient_mk _root_.GlobalClassFieldTheory.IdealClassFieldTheory.smallHilbertClassFieldIdeleExtensionMap_mk' _root_.GlobalClassFieldTheory.Reciprocity.abstractFixedFieldAbelianizedExtensionQuotientEquivGaloisGroup_of _root_.GlobalClassFieldTheory.Reciprocity.abstractFixedFieldCyclotomicGalEquivZHat_extensionClass _root_.GlobalClassFieldTheory.Reciprocity.abstractFixedFieldCyclotomicGalEquivZHat_quotientClass _root_.GlobalClassFieldTheory.Reciprocity.abstractFixedFieldCyclotomicIdeleClassArtinMonoidHom_mk _root_.GlobalClassFieldTheory.Reciprocity.abstractFixedFieldCyclotomicRestriction_extensionClass _root_.GlobalClassFieldTheory.Reciprocity.abstractFixedFieldCyclotomicRestriction_infiniteGlobalArtinMonoidHom _root_.GlobalClassFieldTheory.Reciprocity.arithmeticGlobalArtinMonoidHom_apply _root_.GlobalClassFieldTheory.Reciprocity.arithmeticGlobalArtinMonoidHom_finitePlaceIdele _root_.GlobalClassFieldTheory.Reciprocity.arithmeticGlobalArtinMonoidHom_infinitePlaceIdele _root_.GlobalClassFieldTheory.Reciprocity.arithmeticGlobalNormResidueAbelianizationMonoidHom_apply _root_.GlobalClassFieldTheory.Reciprocity.arithmeticGlobalNormResidueAbelianizationMonoidHom_ker _root_.GlobalClassFieldTheory.Reciprocity.arithmeticGlobalNormResidueContinuousMulEquiv_apply _root_.GlobalClassFieldTheory.Reciprocity.arithmeticGlobalNormResidueMonoidHom_apply _root_.GlobalClassFieldTheory.Reciprocity.arithmeticGlobalNormResidueMonoidHom_ker _root_.GlobalClassFieldTheory.Reciprocity.arithmeticGlobalReciprocityContinuousMulEquiv_globalNormResidue _root_.GlobalClassFieldTheory.Reciprocity.arithmeticGlobalReciprocityContinuousMulEquiv_symm_mk _root_.GlobalClassFieldTheory.Reciprocity.globalNormClassFromIdele_principalIdele _root_.GlobalClassFieldTheory.Reciprocity.globalNormClassFromIdele_relativeIdeleNorm_eq_one _root_.GlobalClassFieldTheory.Reciprocity.globalNormResidueAbelianizationContinuousMonoidHom_apply _root_.GlobalClassFieldTheory.Reciprocity.globalNormResidueAbelianizationContinuousMulEquiv_apply _root_.GlobalClassFieldTheory.Reciprocity.globalNormResidueAbelianizationIdeleMonoidHom_apply _root_.GlobalClassFieldTheory.Reciprocity.globalNormResidueAbelianizationIdeleMonoidHom_eq_one_iff _root_.GlobalClassFieldTheory.Reciprocity.globalNormResidueAbelianizationIdeleMonoidHom_ker _root_.GlobalClassFieldTheory.Reciprocity.globalNormResidueAbelianizationIdeleMonoidHom_principalIdele _root_.GlobalClassFieldTheory.Reciprocity.globalNormResidueAbelianizationMonoidHom_apply _root_.GlobalClassFieldTheory.Reciprocity.globalNormResidueAbelianizationMonoidHom_eq_one_iff _root_.GlobalClassFieldTheory.Reciprocity.globalNormResidueAbelianizationMonoidHom_ker _root_.GlobalClassFieldTheory.Reciprocity.globalReciprocityAbelianizationContinuousMulEquiv_apply _root_.GlobalClassFieldTheory.Reciprocity.infiniteGlobalArtinMonoidHom_abstractFixedFieldCyclotomic_principalIdele _root_.GlobalClassFieldTheory.Reciprocity.mem_globalArtinFiniteSupport_iff _root_.GlobalClassFieldTheory.Reciprocity.numberFieldTowerFinitePadicAuxiliaryBaseEmbedding_coe _root_.GlobalClassFieldTheory.Reciprocity.numberFieldTowerFinitePadicAuxiliaryTopEmbedding_coe _root_.GlobalClassFieldTheory.Reciprocity.ramifiedInfinitePlaceOverextensionGlobalArtin_principalIdele _root_.GlobalClassFieldTheory.Reciprocity.ramifiedInfinitePlaceOverextensionIdeleClassArtinMonoidHom_ideleClassNorm _root_.GlobalClassFieldTheory.Reciprocity.ramifiedInfinitePlaceOverextensionIdeleClassArtinMonoidHom_mk _root_.GlobalClassFieldTheory.Reciprocity.ramifiedInfinitePlaceOverextensionNormQuotientArtinMonoidHom_mk _root_.GlobalClassFieldTheory.Reciprocity.rationalComplexificationGlobalArtin_principalIdele _root_.IdeleGroup.count_fractionalIdeal _root_.IdeleGroup.fractionalIdeal_finitePrimeIdele _root_.IdeleGroup.idealClass_finitePrimeIdele _root_.OAI.PrimeDegreePackets.ThetaConstruction.schwartzCM_apply _root_.RayClass.signToNarrow_mk
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

/-!
# Containment of finite abelian class fields

For actual finite abelian extensions of a number field, containment is
exactly reverse containment of their genuine idèle-class norm ranges.

The proof first realizes an arbitrary extension in the same rational
separable closure as the class field selected by a closed finite-index
subgroup.  The abstract finite-abelian classification then gives a
literal inclusion of fixing subgroups, which restricts the chosen
ambient embedding to an actual algebra embedding into the selected
class field.  Applying this construction to the norm range of a second
extension yields the intrinsic containment criterion over the original
number field.
-/

open scoped Classical NumberField

noncomputable section

namespace GlobalClassFieldTheory
namespace GlobalClassFields

open ClassFormation
open LocalClassFieldTheory
open NumberField
open RamificationTheory
open Reciprocity

variable {K : Type} [Field K] [NumberField K]

/-- The canonical fixed-field equivalence has the distinguished base
embedding as its underlying map into the rational separable closure. -/
@[simp]
theorem closedFiniteIndexClassFieldBaseEquiv_coe
    (H : Subgroup (IdeleClassGroup K))
    (hclosed : IsClosed (H : Set (IdeleClassGroup K)))
    [H.FiniteIndex]
    (x : K) :
    ((closedFiniteIndexClassFieldBaseEquiv
        (K := K) H hclosed x :
      closedFiniteIndexClassFieldBase
        (K := K) H hclosed) :
      SeparableClosure ℚ) =
      closedFiniteIndexClassFieldBaseEmbedding
        (K := K) H hclosed x := by
  rfl

end GlobalClassFields
end GlobalClassFieldTheory
end
end

section
-- module Solutions.OAIQ244_DUKE.GlobalClassFieldTheory_GlobalClassFields_SmallHilbertClassFieldOverOriginalBase
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 400000
attribute [-instance] _root_.GlobalClassFieldTheory.GlobalClassFields.bigHilbertClassFieldAlgebraOverOriginal _root_.GlobalClassFieldTheory.GlobalClassFields.bigHilbertClassFieldBaseAlgebraOverOriginal _root_.GlobalClassFieldTheory.GlobalClassFields.bigHilbertClassFieldIsGaloisOverOriginal _root_.GlobalClassFieldTheory.GlobalClassFields.bigHilbertClassFieldScalarTowerOverOriginal _root_.GlobalClassFieldTheory.Reciprocity.abstractFixedFieldCyclotomicCompositum_algebra _root_.GlobalClassFieldTheory.Reciprocity.abstractFixedFieldCyclotomicCompositum_baseScalarTower _root_.GlobalClassFieldTheory.Reciprocity.abstractFixedFieldCyclotomicCompositum_scalarTower _root_.GlobalClassFieldTheory.Reciprocity.abstractFixedFieldCyclotomicFiniteCompositum_baseAlgebra _root_.GlobalClassFieldTheory.Reciprocity.abstractFixedFieldCyclotomicFiniteCompositum_baseScalarTower _root_.GlobalClassFieldTheory.Reciprocity.abstractFixedFieldCyclotomicFiniteGaloisLayer_scalarTower _root_.GlobalClassFieldTheory.Reciprocity.abstractFixedFieldCyclotomicFiniteLayer_baseAlgebra _root_.GlobalClassFieldTheory.Reciprocity.abstractFixedFieldCyclotomicFiniteLayer_baseModule _root_.GlobalClassFieldTheory.Reciprocity.abstractFixedFieldCyclotomicFiniteLayer_baseSMul _root_.GlobalClassFieldTheory.Reciprocity.abstractFixedFieldCyclotomicFiniteLayer_baseScalarTower _root_.GlobalClassFieldTheory.Reciprocity.abstractFixedFieldCyclotomicFiniteLayer_finiteDimensional _root_.GlobalClassFieldTheory.Reciprocity.abstractFixedFieldCyclotomicFiniteLayer_isAbelianGalois _root_.GlobalClassFieldTheory.Reciprocity.abstractFixedFieldCyclotomicFiniteLayer_layerAlgebra _root_.GlobalClassFieldTheory.Reciprocity.abstractFixedFieldCyclotomicFiniteLayer_layerSMul _root_.GlobalClassFieldTheory.Reciprocity.abstractFixedFieldCyclotomicFiniteLayer_layerScalarTower _root_.GlobalClassFieldTheory.Reciprocity.abstractFixedFieldCyclotomicFiniteLayer_numberField _root_.GlobalClassFieldTheory.Reciprocity.infinitePlaceComplexificationOverfield_algebra _root_.GlobalClassFieldTheory.Reciprocity.infinitePlaceComplexificationOverfield_baseAlgebra _root_.GlobalClassFieldTheory.Reciprocity.infinitePlaceComplexificationOverfield_baseSmul _root_.GlobalClassFieldTheory.Reciprocity.infinitePlaceComplexificationOverfield_smul _root_.GlobalClassFieldTheory.Reciprocity.ramifiedInfinitePlaceRealFixedField_algebra _root_.GlobalClassFieldTheory.Reciprocity.rationalComplexification_infinitePlaceOverfield_algebra _root_.GlobalClassFieldTheory.Reciprocity.rationalComplexification_infinitePlaceOverfield_smul _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.instTopologicalSpaceLocalAlgebra _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.GlobalClassFieldTheory.GlobalClassFields.bigHilbertNormQuotient_finite _root_.GlobalClassFieldTheory.GlobalClassFields.bigHilbertNormSubgroup_finiteIndex
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI
attribute [local instance] OAI.starSubalgebraCommCStarAlgebra

set_option autoImplicit false

/-!
# The small Hilbert class field over the original number field

The finite class-field construction realizes the small Hilbert class
field over a canonical fixed-field copy of the input number field.
The fixed-field copy is canonically `ℚ`-algebra equivalent to the
original field.  This file uses that equivalence as the actual scalar
map, so the selected Hilbert class field becomes a finite abelian
Galois extension of the original field itself.

This is the scalar structure used by the final extension-of-ideals map
in the principal ideal theorem.
-/

open scoped Classical IsMulCommutative NumberField

noncomputable section

namespace GlobalClassFieldTheory
namespace GlobalClassFields

variable (K : Type) [Field K] [NumberField K]

/-- The original field, its canonical fixed-field copy, and the
selected small Hilbert class field form the literal scalar tower used
by extension of ideals. -/
noncomputable instance smallHilbertClassFieldScalarTowerOverOriginal :
    IsScalarTower K
      (smallHilbertClassFieldBase K)
      (smallHilbertClassField K) :=
  IsScalarTower.of_algebraMap_eq' rfl

/-- The selected small Hilbert class field is Galois over the original
number field, not only over its canonically equivalent fixed-field
copy. -/
noncomputable instance smallHilbertClassFieldIsGaloisOverOriginal :
    IsGalois K (smallHilbertClassField K) := by
  let e :=
    smallHilbertClassFieldBaseEquiv (K := K)
  apply IsGalois.of_equiv_equiv
    (F := smallHilbertClassFieldBase K)
    (E := smallHilbertClassField K)
    (f := e.symm.toRingEquiv)
    (g := RingEquiv.refl (smallHilbertClassField K))
  apply RingHom.ext
  intro x
  calc
    ((algebraMap K (smallHilbertClassField K)).comp
        e.symm.toRingEquiv) x =
        algebraMap K (smallHilbertClassField K) (e.symm x) := rfl
    _ = algebraMap
          (smallHilbertClassFieldBase K)
          (smallHilbertClassField K)
          (smallHilbertClassFieldBaseEquiv (K := K) (e.symm x)) :=
      smallHilbertClassField_algebraMap_original
        (K := K) (e.symm x)
    _ = algebraMap
          (smallHilbertClassFieldBase K)
          (smallHilbertClassField K) x := by
      simpa only [e] using
        congrArg
          (algebraMap
            (smallHilbertClassFieldBase K)
            (smallHilbertClassField K))
          ((smallHilbertClassFieldBaseEquiv
            (K := K)).apply_symm_apply x)
    _ = ((RingEquiv.refl
            (smallHilbertClassField K)).toRingHom.comp
          (algebraMap
            (smallHilbertClassFieldBase K)
            (smallHilbertClassField K))) x := rfl

end GlobalClassFields
end GlobalClassFieldTheory
end
end

section
-- module Solutions.OAIQ244_DUKE.GlobalClassFieldTheory_Reciprocity_CyclotomicUnramifiedLocalGlobalCompatibility
attribute [-instance] _root_.GlobalClassFieldTheory.GlobalClassFields.ConductorialSubgroup.finiteIndex _root_.GlobalClassFieldTheory.GlobalClassFields.bigHilbertClassFieldAlgebraOverOriginal _root_.GlobalClassFieldTheory.GlobalClassFields.bigHilbertClassFieldBaseAlgebraOverOriginal _root_.GlobalClassFieldTheory.GlobalClassFields.bigHilbertClassFieldIsGaloisOverOriginal _root_.GlobalClassFieldTheory.GlobalClassFields.bigHilbertClassFieldNormSubgroupFiniteIndex _root_.GlobalClassFieldTheory.GlobalClassFields.bigHilbertClassFieldNormSubgroup_normal _root_.GlobalClassFieldTheory.GlobalClassFields.bigHilbertClassFieldScalarTowerOverOriginal _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexClassFieldAlgebraOverOriginal _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexClassFieldBaseAlgebraOverOriginal _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexClassFieldIsGaloisOverOriginal _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexClassFieldScalarTowerOverOriginal _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexNormAmbientFiniteDimensional _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexNormAmbientIsGalois _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexNormAmbientNumberField _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexNormCyclotomicFieldFiniteDimensional _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexNormCyclotomicFieldIsCyclotomicExtension _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexNormCyclotomicFieldIsGalois _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexNormCyclotomicFieldNumberField _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexNormExponentNeZero _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexNormKummerFieldAlgebraOverBase _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexNormKummerFieldFiniteDimensional _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexNormKummerFieldFiniteDimensionalOverBase _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexNormKummerFieldModuleOverBase _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexNormKummerFieldNumberField _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexNormKummerFieldSMulOverBase _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexNormKummerFieldScalarTower _root_.GlobalClassFieldTheory.GlobalClassFields.ideleClassNorm_rangeFiniteIndex _root_.GlobalClassFieldTheory.GlobalClassFields.ordinaryNormClassFieldAbsoluteFiniteDimensional _root_.GlobalClassFieldTheory.GlobalClassFields.ordinaryNormClassFieldBaseFiniteDimensional _root_.GlobalClassFieldTheory.GlobalClassFields.ordinaryNormClassFieldBaseNumberField _root_.GlobalClassFieldTheory.GlobalClassFields.ordinaryNormClassFieldExtensionFiniteDimensional _root_.GlobalClassFieldTheory.GlobalClassFields.ordinaryNormClassFieldExtensionIsAbelianGalois _root_.GlobalClassFieldTheory.GlobalClassFields.ordinaryNormClassFieldExtensionIsGalois _root_.GlobalClassFieldTheory.GlobalClassFields.ordinaryNormClassFieldExtensionNumberField _root_.GlobalClassFieldTheory.GlobalClassFields.ordinaryNormClassFieldScalarTower _root_.GlobalClassFieldTheory.GlobalClassFields.smallHilbertClassFieldAlgebraOverOriginal _root_.GlobalClassFieldTheory.GlobalClassFields.smallHilbertClassFieldBaseAlgebraOverOriginal _root_.GlobalClassFieldTheory.GlobalClassFields.smallHilbertClassFieldIsGaloisOverOriginal _root_.GlobalClassFieldTheory.GlobalClassFields.smallHilbertClassFieldNormSubgroupFiniteIndex _root_.GlobalClassFieldTheory.GlobalClassFields.smallHilbertClassFieldScalarTowerOverOriginal _root_.GlobalClassFieldTheory.Reciprocity.complexFourthRootField_numberField _root_.GlobalClassFieldTheory.Reciprocity.infinitePlaceComplexificationOverfield_baseSmul _root_.GlobalClassFieldTheory.Reciprocity.infinitePlaceComplexificationOverfield_numberField _root_.GlobalClassFieldTheory.Reciprocity.infinitePlaceComplexificationOverfield_smul _root_.GlobalClassFieldTheory.Reciprocity.ramifiedInfinitePlaceRealFixedField_numberField _root_.GlobalClassFieldTheory.Reciprocity.rationalComplexification_infinitePlaceOverfield_algebra _root_.GlobalClassFieldTheory.Reciprocity.rationalComplexification_infinitePlaceOverfield_smul _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.boundedRealFields_numberField _root_.OAI.PrimeDegreePackets.diagonalLogAction _root_.OAI.PrimeDegreePackets.instTopologicalSpaceLocalAlgebra _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.GlobalClassFieldTheory.GlobalClassFields.bigHilbertNormQuotient_finite _root_.GlobalClassFieldTheory.GlobalClassFields.bigHilbertNormSubgroup_finiteIndex
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI
attribute [local instance] OAI.starSubalgebraCommCStarAlgebra

set_option autoImplicit false

/-!
# Cyclotomic unramified local--global compatibility

For an unramified finite abelian subextension of an abstract rational
fixed field, the actual global norm-residue homomorphism agrees on every
finite one-place idele class with the chosen local Artin homomorphism.
-/

open scoped IsMulCommutative NumberField

noncomputable section

namespace GlobalClassFieldTheory
namespace Reciprocity

open ClassFormation
open KummerTheory

attribute [local instance]
  rationalSeparableClosureAlgebra
  naturalityAbstractFixedFieldBaseQuotientFinite
  naturalityAbstractFixedFieldRelativeQuotientFinite
  naturalityAbstractFixedFieldFiniteDimensional
  naturalityAbstractRelativeFixedFieldFiniteDimensional
  naturalityAbstractFixedFieldRelativeScalarTower
  naturalityAbstractRelativeFixedFieldAbsoluteFiniteDimensional
  naturalityAbstractFixedFieldNumberField
  naturalityAbstractRelativeFixedFieldNumberField
  naturalityAbstractRelativeFixedFieldIsAbelianGalois

attribute [local instance] GlobalClassFieldTheory.Reciprocity.abstractFixedFieldFiniteIdeleGroupGroup
attribute [local instance] GlobalClassFieldTheory.Reciprocity.abstractFixedFieldIdeleGroupGroup
attribute [local instance] GlobalClassFieldTheory.Reciprocity.abstractFixedFieldIdeleClassGroupGroup
theorem
    abstractFixedFieldCyclotomicFiniteRestriction_comp_infiniteGlobalArtinMonoidHom
    (H : FiniteAbstractField
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
    (L : FiniteAbelianSubextension H.field)
    (hUnramified :
      L.toFiniteGaloisExtension.IsUnramified
        rationalCyclotomicDegreeData) :
    let F :=
      LocalClassFieldTheory.abstractFixedField
        ℚ (SeparableClosure ℚ) H.field
    let E :=
      LocalClassFieldTheory.abstractRelativeFixedField
        ℚ (SeparableClosure ℚ) L.below
    let U :=
      LocalClassFieldTheory.abstractRelativeFixedField
        ℚ (SeparableClosure ℚ)
        (rationalCyclotomicFieldInertia_le H.field)
    letI _ : NumberField F :=
      cyclotomicUnramifiedGeometricBaseNumberField H
    letI _ : NumberField E :=
      cyclotomicUnramifiedGeometricRelativeNumberField H L
    letI _ : Algebra F E := E.algebra'
    letI _ : Algebra F U := U.algebra'
    letI _ : IsAbelianGalois F E :=
      cyclotomicUnramifiedGeometricRelativeIsAbelianGalois H L
    letI _ : IsAbelianGalois F U :=
      cyclotomicUnramifiedGeometricMaximalIsAbelianGalois H
    letI _ : Algebra E U :=
      abstractFixedFieldCyclotomicFiniteUnramifiedInclusionAlgebra
        H L hUnramified
    letI _ : @IsScalarTower F E U
        Algebra.toSMul Algebra.toSMul Algebra.toSMul :=
      IsScalarTower.of_algHom
        (abstractFixedFieldCyclotomicFiniteUnramifiedInclusion
          H L hUnramified)
    (abstractFixedFieldCyclotomicFiniteRestrictionMonoidHom
        H L hUnramified).comp
        (infiniteGlobalArtinMonoidHom F U).toMonoidHom =
      globalArtinMonoidHom (K := F) (L := E) := by
  dsimp only
  let F :=
    LocalClassFieldTheory.abstractFixedField
      ℚ (SeparableClosure ℚ) H.field
  let E :=
    LocalClassFieldTheory.abstractRelativeFixedField
      ℚ (SeparableClosure ℚ) L.below
  let U :=
    LocalClassFieldTheory.abstractRelativeFixedField
      ℚ (SeparableClosure ℚ)
      (rationalCyclotomicFieldInertia_le H.field)
  let fNumberField : NumberField F :=
    cyclotomicUnramifiedGeometricBaseNumberField H
  let eNumberField : NumberField E :=
    cyclotomicUnramifiedGeometricRelativeNumberField H L
  let fEAlgebra : Algebra F E := E.algebra'
  let fUAlgebra : Algebra F U := U.algebra'
  let fEIsAbelianGalois : IsAbelianGalois F E :=
    cyclotomicUnramifiedGeometricRelativeIsAbelianGalois H L
  let fUIsAbelianGalois : IsAbelianGalois F U :=
    cyclotomicUnramifiedGeometricMaximalIsAbelianGalois H
  let eUAlgebra : Algebra E U :=
    abstractFixedFieldCyclotomicFiniteUnramifiedInclusionAlgebra
      H L hUnramified
  let fEUTower : @IsScalarTower F E U
      Algebra.toSMul Algebra.toSMul Algebra.toSMul :=
    IsScalarTower.of_algHom
      (abstractFixedFieldCyclotomicFiniteUnramifiedInclusion
        H L hUnramified)
  calc
    (abstractFixedFieldCyclotomicFiniteRestrictionMonoidHom
        H L hUnramified).comp
        (infiniteGlobalArtinMonoidHom F U).toMonoidHom =
      (AlgEquiv.restrictNormalHom E).comp
        (infiniteGlobalArtinMonoidHom F U).toMonoidHom :=
      congrArg
        (fun f => f.comp
          (infiniteGlobalArtinMonoidHom F U).toMonoidHom)
        (abstractFixedFieldCyclotomicFiniteRestrictionMonoidHom_eq_restrictNormalHom
          H L hUnramified)
    _ = globalArtinMonoidHom (K := F) (L := E) :=
      restrictNormalHom_comp_infiniteGlobalArtinMonoidHom_of_tower
        F E U

theorem
    abstractFixedFieldGlobalNormResidueMonoidHom_eq_cyclotomicRestrictionComp
    (H : FiniteAbstractField
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
    (L : FiniteAbelianSubextension H.field)
    (hUnramified :
      L.toFiniteGaloisExtension.IsUnramified
        rationalCyclotomicDegreeData) :
    let rhs :=
      composeMonoidHom
        (abstractFixedFieldCyclotomicIdeleClassArtinMonoidHom H)
        (abstractFixedFieldCyclotomicFiniteRestrictionMonoidHom
          H L hUnramified)
    abstractFixedFieldGlobalNormResidueMonoidHom H L = rhs := by
  dsimp only
  apply MonoidHom.ext
  intro c
  exact
    abstractFixedFieldGlobalNormResidueMonoidHom_eq_cyclotomicFiniteRestriction
      H L hUnramified c

theorem
    abstractFixedFieldCyclotomicIdeleClassArtinMonoidHom_comp_finitePlaceIdeleClass
    (H : FiniteAbstractField
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
    (v : IsDedekindDomain.HeightOneSpectrum
      (𝓞 (LocalClassFieldTheory.abstractFixedField
        ℚ (SeparableClosure ℚ) H.field))) :
    let F :=
      LocalClassFieldTheory.abstractFixedField
        ℚ (SeparableClosure ℚ) H.field
    let U :=
      LocalClassFieldTheory.abstractRelativeFixedField
        ℚ (SeparableClosure ℚ)
        (rationalCyclotomicFieldInertia_le H.field)
    letI _ : IsAbelianGalois F U :=
      abstractFixedFieldCyclotomic_isAbelianGalois H
    composeMonoidHom
        (IdeleGroup.finitePlaceIdeleClass v)
        (abstractFixedFieldCyclotomicIdeleClassArtinMonoidHom H) =
      composeMonoidHom
        (IdeleGroup.finitePlaceIdele v)
        (infiniteGlobalArtinMonoidHom F U).toMonoidHom := by
  dsimp only
  apply MonoidHom.ext
  intro x
  exact
    abstractFixedFieldCyclotomicIdeleClassArtinMonoidHom_mk
      H (IdeleGroup.finitePlaceIdele v x)

/-- The cyclotomic construction of fixed-field reciprocity satisfies
finite-place local--global compatibility on every finite unramified
abelian subextension. -/
theorem
    abstractFixedFieldGlobalNormResidueMonoidHom_comp_finitePlaceIdeleClass
    (H : FiniteAbstractField
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
    (L : FiniteAbelianSubextension H.field)
    (hUnramified :
      L.toFiniteGaloisExtension.IsUnramified
        rationalCyclotomicDegreeData)
    (v : IsDedekindDomain.HeightOneSpectrum
      (𝓞 (LocalClassFieldTheory.abstractFixedField
        ℚ (SeparableClosure ℚ) H.field))) :
    let F :=
      LocalClassFieldTheory.abstractFixedField
        ℚ (SeparableClosure ℚ) H.field
    let E :=
      LocalClassFieldTheory.abstractRelativeFixedField
        ℚ (SeparableClosure ℚ) L.below
    (abstractFixedFieldGlobalNormResidueMonoidHom H L).comp
        (IdeleGroup.finitePlaceIdeleClass v) =
      chosenFinitePlaceArtinMonoidHom
        (K := F) (L := E) v := by
  dsimp only
  let F :=
    LocalClassFieldTheory.abstractFixedField
      ℚ (SeparableClosure ℚ) H.field
  let E :=
    LocalClassFieldTheory.abstractRelativeFixedField
      ℚ (SeparableClosure ℚ) L.below
  let U :=
    LocalClassFieldTheory.abstractRelativeFixedField
      ℚ (SeparableClosure ℚ)
      (rationalCyclotomicFieldInertia_le H.field)
  let fUIsAbelianGalois : IsAbelianGalois F U :=
    abstractFixedFieldCyclotomic_isAbelianGalois H
  let finiteIdele := IdeleGroup.finitePlaceIdele v
  let finiteIdeleClass := IdeleGroup.finitePlaceIdeleClass v
  let restriction :=
    abstractFixedFieldCyclotomicFiniteRestrictionMonoidHom
      H L hUnramified
  let ideleClassArtin :=
    abstractFixedFieldCyclotomicIdeleClassArtinMonoidHom H
  let infiniteArtin := infiniteGlobalArtinMonoidHom F U
  calc
    (abstractFixedFieldGlobalNormResidueMonoidHom H L).comp
          finiteIdeleClass =
        (restriction.comp ideleClassArtin).comp
          finiteIdeleClass :=
      congrArg
        (fun f => f.comp finiteIdeleClass)
        (abstractFixedFieldGlobalNormResidueMonoidHom_eq_cyclotomicRestrictionComp
          H L hUnramified)
    _ = restriction.comp
          (ideleClassArtin.comp finiteIdeleClass) := rfl
    _ = restriction.comp
          (infiniteArtin.toMonoidHom.comp finiteIdele) :=
      congrArg (fun f => restriction.comp f)
        (abstractFixedFieldCyclotomicIdeleClassArtinMonoidHom_comp_finitePlaceIdeleClass
          H v)
    _ = (restriction.comp infiniteArtin.toMonoidHom).comp
          finiteIdele := rfl
    _ = (globalArtinMonoidHom (K := F) (L := E)).comp
          finiteIdele :=
      congrArg (fun f => f.comp finiteIdele)
        (abstractFixedFieldCyclotomicFiniteRestriction_comp_infiniteGlobalArtinMonoidHom
          H L hUnramified)
    _ = chosenFinitePlaceArtinMonoidHom
          (K := F) (L := E) v :=
      globalArtinMonoidHom_comp_finitePlaceIdele F E v

end Reciprocity
end GlobalClassFieldTheory
end
end

section
-- module Solutions.OAIQ244_DUKE.GlobalClassFieldTheory_Reciprocity_LocalGlobalArtinCompatibility_FinitePadicCyclicData
attribute [-instance] _root_.GlobalClassFieldTheory.GlobalClassFields.bigHilbertClassFieldAlgebraOverOriginal _root_.GlobalClassFieldTheory.GlobalClassFields.bigHilbertClassFieldBaseAlgebraOverOriginal _root_.GlobalClassFieldTheory.GlobalClassFields.bigHilbertClassFieldIsGaloisOverOriginal _root_.GlobalClassFieldTheory.GlobalClassFields.bigHilbertClassFieldNormSubgroup_normal _root_.GlobalClassFieldTheory.GlobalClassFields.bigHilbertClassFieldScalarTowerOverOriginal _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexClassFieldAlgebraOverOriginal _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexClassFieldBaseAlgebraOverOriginal _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexClassFieldIsGaloisOverOriginal _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexClassFieldScalarTowerOverOriginal _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexNormKummerFieldAlgebraOverBase _root_.GlobalClassFieldTheory.GlobalClassFields.finiteAbelianSubextensionAbstractRelativeFixedFieldFiniteDimensional _root_.GlobalClassFieldTheory.GlobalClassFields.ordinaryNormClassFieldAbsoluteFiniteDimensional _root_.GlobalClassFieldTheory.GlobalClassFields.ordinaryNormClassFieldBaseFiniteDimensional _root_.GlobalClassFieldTheory.GlobalClassFields.ordinaryNormClassFieldBaseNumberField _root_.GlobalClassFieldTheory.GlobalClassFields.ordinaryNormClassFieldExtensionFiniteDimensional _root_.GlobalClassFieldTheory.GlobalClassFields.ordinaryNormClassFieldExtensionIsAbelianGalois _root_.GlobalClassFieldTheory.GlobalClassFields.ordinaryNormClassFieldExtensionIsGalois _root_.GlobalClassFieldTheory.GlobalClassFields.ordinaryNormClassFieldExtensionNumberField _root_.GlobalClassFieldTheory.GlobalClassFields.ordinaryNormClassFieldScalarTower _root_.GlobalClassFieldTheory.GlobalClassFields.smallHilbertClassFieldAlgebraOverOriginal _root_.GlobalClassFieldTheory.GlobalClassFields.smallHilbertClassFieldBaseAlgebraOverOriginal _root_.GlobalClassFieldTheory.GlobalClassFields.smallHilbertClassFieldIsGaloisOverOriginal _root_.GlobalClassFieldTheory.GlobalClassFields.smallHilbertClassFieldScalarTowerOverOriginal _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.boundedRealFields_finite _root_.OAI.PrimeDegreePackets.completedMaximalOrderCompactSpace _root_.OAI.PrimeDegreePackets.instTopologicalSpaceLocalAlgebra _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.labelPrime_fact _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.GlobalClassFieldTheory.GlobalClassFields.bigHilbertNormQuotient_finite _root_.GlobalClassFieldTheory.GlobalClassFields.narrowClassGroup_finite _root_.GlobalClassFieldTheory.Reciprocity.cyclotomicUnramifiedGeometricMaxExtensionNormal
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
# Finite p-adic cyclic data for local-global Artin compatibility

This module packages the simultaneous finite-quotient and cyclotomic
coordinates and the corresponding abstract auxiliary subextension.
-/

open scoped IsMulCommutative NumberField
open NumberField
open IdeleGroup RelativeIdeleGroup
open AlgebraicNumberTheory.Valuations
open HilbertRamification
open CyclicCohomology
open KummerTheory ClassFormation

noncomputable section

namespace GlobalClassFieldTheory
namespace Reciprocity

variable
    {K L : Type}
    [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsAbelianGalois K L]

attribute [local instance] GlobalClassFieldTheory.Reciprocity.instFactPrimeValNat_solutions_7
attribute [local instance] GlobalClassFieldTheory.Reciprocity.numberFieldTowerExtensionNormal
attribute [local instance] GlobalClassFieldTheory.Reciprocity.finitePadicTowerExtensionQuotientFinite
attribute [local instance] GlobalClassFieldTheory.Reciprocity.numberFieldTowerExtensionQuotientIsMulCommutative
attribute [local instance] GlobalClassFieldTheory.Reciprocity.numberFieldTowerBaseSubgroupCompactSpace
/-- The `p`-adic degree on the actual simultaneous-coordinate image is
its second projection. -/
noncomputable def numberFieldTowerFinitePadicImageDegree
    (p : Nat.Primes) :
    (numberFieldTowerFinitePadicImage
        (K := K) (L := L) p).toSubgroup →ₜ*
      Multiplicative ℤ_[p.1] := by
  exact
    { toFun := fun z => z.1.2
      map_one' := rfl
      map_mul' := fun _ _ => rfl
      continuous_toFun :=
        continuous_snd.comp continuous_subtype_val }

/-- The kernel of the `p`-adic degree on the simultaneous-coordinate
image is finite: its first projection injects it into the finite
Galois quotient. -/
theorem numberFieldTowerFinitePadicImageDegree_ker_finite
    (p : Nat.Primes) :
    Finite
      (numberFieldTowerFinitePadicImageDegree
        (K := K) (L := L) p).toMonoidHom.ker := by
  let H :=
    numberFieldTowerBaseSubgroup K L
  let N :=
    extensionSubgroup
      H
      (numberFieldTowerTopSubgroup L)
      (numberFieldTowerTopSubgroup_le_baseSubgroup K L)
  let Q := H.toSubgroup ⧸ N
  let degree :=
    numberFieldTowerFinitePadicImageDegree
      (K := K) (L := L) p
  let first :
      degree.toMonoidHom.ker → Q :=
    fun z => z.1.1.1
  apply Finite.of_injective first
  intro x y hxy
  apply Subtype.ext
  apply Subtype.ext
  apply Prod.ext
  · exact hxy
  · have hx : x.1.1.2 = 1 := x.2
    have hy : y.1.1.2 = 1 := y.2
    exact hx.trans hy.symm

/-- The degree projection of the restricted simultaneous coordinate is the
original cyclotomic degree.  Keeping this pointwise boundary avoids unfolding
the closed-image package in downstream proofs. -/
theorem numberFieldTowerFinitePadicImageDegree_rangeRestriction_apply
    (p : Nat.Primes)
    (τ : (numberFieldTowerBaseSubgroup K L).toSubgroup) :
    numberFieldTowerFinitePadicImageDegree
        (K := K) (L := L) p
        (numberFieldTowerFinitePadicRangeRestriction
          (K := K) (L := L) p τ) =
      numberFieldTowerBaseSubgroupPadicCyclotomicDegree
        (K := K) (L := L) p τ :=
  rfl

/-- Restriction to the actual simultaneous-coordinate image is
surjective. -/
theorem numberFieldTowerFinitePadicRangeRestriction_surjective
    (p : Nat.Primes) :
    Function.Surjective
      (numberFieldTowerFinitePadicRangeRestriction
        (K := K) (L := L) p) := by
  exact
    (numberFieldTowerFinitePadicCoordinate
      (K := K) (L := L) p).toMonoidHom.rangeRestrict_surjective

/-- A lift with nontrivial `p`-adic degree generates an open cyclic
preimage in the compatible absolute Galois group. -/
theorem numberFieldTowerFinitePadicCyclicPreimage_isOpen
    (p : Nat.Primes)
    (τ : (numberFieldTowerBaseSubgroup K L).toSubgroup)
    (hτ :
      numberFieldTowerBaseSubgroupPadicCyclotomicDegree
          (K := K) (L := L) p τ ≠
        1) :
    IsOpen
      ((numberFieldTowerFinitePadicCyclicPreimage
          (K := K) (L := L) p τ :
        ClosedSubgroup
          (numberFieldTowerBaseSubgroup K L).toSubgroup) :
        Set (numberFieldTowerBaseSubgroup K L).toSubgroup) := by
  let P :=
    numberFieldTowerFinitePadicImage
      (K := K) (L := L) p
  let rangeRestriction :=
    numberFieldTowerFinitePadicRangeRestriction
      (K := K) (L := L) p
  let degree :=
    numberFieldTowerFinitePadicImageDegree
      (K := K) (L := L) p
  let : CompactSpace P.toSubgroup :=
    isCompact_iff_compactSpace.mp P.isClosed'.isCompact
  let γ : P.toSubgroup :=
    rangeRestriction τ
  let finiteDegreeKernel : Finite degree.toMonoidHom.ker :=
    numberFieldTowerFinitePadicImageDegree_ker_finite
      (K := K) (L := L) p
  have hγ : degree γ ≠ 1 := by
    simpa only [degree, γ, rangeRestriction,
      numberFieldTowerFinitePadicImageDegree_rangeRestriction_apply] using hτ
  have hΓ :
      IsOpen
        ((ClassFormation.padicCyclicClosure γ :
            Subgroup P.toSubgroup) :
          Set P.toSubgroup) :=
    ClassFormation.padicCyclicClosure_isOpen_of_degree_ne_one
      p.1 degree γ hγ
  exact
    hΓ.preimage rangeRestriction.continuous_toFun

/-- For a lift whose finite coordinate is `p`-primary and whose
cyclotomic degree is a positive integer, the `p`-adic degree is
injective on its actual closed cyclic image. -/
theorem numberFieldTowerFinitePadicCyclicImageDegree_injective
    (p : Nat.Primes)
    (τ : (numberFieldTowerBaseSubgroup K L).toSubgroup)
    (n : ℕ) (hn : 0 < n)
    (hdegree :
      numberFieldTowerBaseSubgroupPadicCyclotomicDegree
          (K := K) (L := L) p τ =
        (Multiplicative.ofAdd (1 : ℤ_[p.1])) ^ n)
    (hprimary :
      numberFieldTowerFiniteQuotientCoordinate
          (K := K) (L := L) τ ∈
        CommGroup.primaryComponent
          ((numberFieldTowerBaseSubgroup K L).toSubgroup ⧸
            extensionSubgroup
              (numberFieldTowerBaseSubgroup K L)
              (numberFieldTowerTopSubgroup L)
              (numberFieldTowerTopSubgroup_le_baseSubgroup K L))
          p.1) :
    let P :=
      numberFieldTowerFinitePadicImage
        (K := K) (L := L) p
    let γ : P.toSubgroup :=
      numberFieldTowerFinitePadicRangeRestriction
        (K := K) (L := L) p τ
    Function.Injective
      (((numberFieldTowerFinitePadicImageDegree
          (K := K) (L := L) p).comp
        (continuousSubgroupSubtype
          (ClassFormation.padicCyclicClosure γ).toSubgroup)) :
        ClassFormation.padicCyclicClosure γ →
          Multiplicative ℤ_[p.1]) := by
  dsimp only
  let H :=
    numberFieldTowerBaseSubgroup K L
  let T :=
    numberFieldTowerTopSubgroup L
  let N :=
    extensionSubgroup H T
      (numberFieldTowerTopSubgroup_le_baseSubgroup K L)
  let Q := H.toSubgroup ⧸ N
  let P :=
    numberFieldTowerFinitePadicImage
      (K := K) (L := L) p
  let γ : P.toSubgroup :=
    numberFieldTowerFinitePadicRangeRestriction
      (K := K) (L := L) p τ
  let finiteProjection :
      P.toSubgroup →ₜ* Q :=
    { toFun := fun z => z.1.1
      map_one' := rfl
      map_mul' := fun _ _ => rfl
      continuous_toFun :=
        continuous_fst.comp continuous_subtype_val }
  let degree :=
    numberFieldTowerFinitePadicImageDegree
      (K := K) (L := L) p
  let extensionSubgroupClosed : IsClosed (N : Set H.toSubgroup) :=
    extensionSubgroup_isClosed H T
      (numberFieldTowerTopSubgroup_le_baseSubgroup K L)
  let extensionSubgroupFiniteIndex : N.FiniteIndex :=
    N.finiteIndex_of_finite_quotient
  let quotientDiscreteTopology : DiscreteTopology Q :=
    QuotientGroup.discreteTopology
      (N.isOpen_of_isClosed_of_finiteIndex
        extensionSubgroupClosed)
  obtain ⟨m, hm⟩ := hprimary
  apply
    ClassFormation.padicCyclicClosure_degree_injective_of_primePower_finiteCoordinate
        p.1 finiteProjection degree
        (γ := γ) (m := m) (n := n)
  · intro x y hxy
    apply Subtype.ext
    exact hxy
  · exact hn
  · exact hm
  · exact hdegree

/-- On a positive-degree lift with `p`-primary finite coordinate, the
intersection of its cyclic preimage with the cyclotomic `p`-adic
kernel already fixes `L`. -/
theorem
    numberFieldTowerFinitePadicCyclicPreimage_inf_padicKernel_le_extensionSubgroup
    (p : Nat.Primes)
    (τ : (numberFieldTowerBaseSubgroup K L).toSubgroup)
    (n : ℕ) (hn : 0 < n)
    (hdegree :
      numberFieldTowerBaseSubgroupPadicCyclotomicDegree
          (K := K) (L := L) p τ =
        (Multiplicative.ofAdd (1 : ℤ_[p.1])) ^ n)
    (hprimary :
      numberFieldTowerFiniteQuotientCoordinate
          (K := K) (L := L) τ ∈
        CommGroup.primaryComponent
          ((numberFieldTowerBaseSubgroup K L).toSubgroup ⧸
            extensionSubgroup
              (numberFieldTowerBaseSubgroup K L)
              (numberFieldTowerTopSubgroup L)
              (numberFieldTowerTopSubgroup_le_baseSubgroup K L))
          p.1) :
    (numberFieldTowerFinitePadicCyclicPreimage
          (K := K) (L := L) p τ).toSubgroup ⊓
        (numberFieldTowerBaseSubgroupPadicCyclotomicDegree
          (K := K) (L := L) p).toMonoidHom.ker ≤
      extensionSubgroup
        (numberFieldTowerBaseSubgroup K L)
        (numberFieldTowerTopSubgroup L)
        (numberFieldTowerTopSubgroup_le_baseSubgroup K L) := by
  let H :=
    numberFieldTowerBaseSubgroup K L
  let T :=
    numberFieldTowerTopSubgroup L
  let N :=
    extensionSubgroup H T
      (numberFieldTowerTopSubgroup_le_baseSubgroup K L)
  let P :=
    numberFieldTowerFinitePadicImage
      (K := K) (L := L) p
  let rangeRestriction :=
    numberFieldTowerFinitePadicRangeRestriction
      (K := K) (L := L) p
  let γ : P.toSubgroup :=
    rangeRestriction τ
  let Γ :=
    ClassFormation.padicCyclicClosure γ
  let degree :=
    numberFieldTowerFinitePadicImageDegree
      (K := K) (L := L) p
  have hinjective :=
    numberFieldTowerFinitePadicCyclicImageDegree_injective
      (K := K) (L := L) p τ n hn hdegree hprimary
  intro u hu
  let z : Γ.toSubgroup :=
    ⟨rangeRestriction u, hu.1⟩
  have hz : z = 1 := by
    apply hinjective
    change
      numberFieldTowerBaseSubgroupPadicCyclotomicDegree
          (K := K) (L := L) p u =
        1
    exact hu.2
  have hfinite :
      numberFieldTowerFiniteQuotientCoordinate
          (K := K) (L := L) u =
        1 := by
    have hzfinite :=
      congrArg (fun w : Γ.toSubgroup => w.1.1.1) hz
    exact hzfinite
  exact
    (QuotientGroup.eq_one_iff (N := N) u).mp hfinite

/-- Ambient form of the kernel-intersection statement. -/
theorem
    numberFieldTowerFinitePadicCyclicFixedSubgroup_inf_absolutePadicKernel_le_topSubgroup
    (p : Nat.Primes)
    (τ : (numberFieldTowerBaseSubgroup K L).toSubgroup)
    (n : ℕ) (hn : 0 < n)
    (hdegree :
      numberFieldTowerBaseSubgroupPadicCyclotomicDegree
          (K := K) (L := L) p τ =
        (Multiplicative.ofAdd (1 : ℤ_[p.1])) ^ n)
    (hprimary :
      numberFieldTowerFiniteQuotientCoordinate
          (K := K) (L := L) τ ∈
        CommGroup.primaryComponent
          ((numberFieldTowerBaseSubgroup K L).toSubgroup ⧸
            extensionSubgroup
              (numberFieldTowerBaseSubgroup K L)
              (numberFieldTowerTopSubgroup L)
              (numberFieldTowerTopSubgroup_le_baseSubgroup K L))
          p.1) :
    (numberFieldTowerFinitePadicCyclicFixedSubgroup
          (K := K) (L := L) p τ).toSubgroup ⊓
        (rationalSeparableClosurePadicCyclotomicDegree
          p).toMonoidHom.ker ≤
      (numberFieldTowerTopSubgroup L).toSubgroup := by
  let T :=
    numberFieldTowerTopSubgroup L
  let U :=
    numberFieldTowerFinitePadicCyclicPreimage
      (K := K) (L := L) p τ
  have hrelative :=
    numberFieldTowerFinitePadicCyclicPreimage_inf_padicKernel_le_extensionSubgroup
      (K := K) (L := L) p τ n hn hdegree hprimary
  intro σ hσ
  obtain ⟨u, huU, huσ⟩ := hσ.1
  have huDegree :
      u ∈
        (numberFieldTowerBaseSubgroupPadicCyclotomicDegree
          (K := K) (L := L) p).toMonoidHom.ker := by
    change
      rationalSeparableClosurePadicCyclotomicDegree
          p u.1 =
        1
    calc
      rationalSeparableClosurePadicCyclotomicDegree p u.1 =
          rationalSeparableClosurePadicCyclotomicDegree p σ :=
        congrArg
          (rationalSeparableClosurePadicCyclotomicDegree p) huσ
      _ = 1 := hσ.2
  have huN :=
    hrelative ⟨huU, huDegree⟩
  change σ ∈ T.toSubgroup
  exact huσ ▸ huN

/-- A nonzero-degree cyclic lift cuts out an open subgroup of the
rational absolute Galois group. -/
theorem numberFieldTowerFinitePadicCyclicFixedSubgroup_isOpen
    (p : Nat.Primes)
    (τ : (numberFieldTowerBaseSubgroup K L).toSubgroup)
    (hτ :
      numberFieldTowerBaseSubgroupPadicCyclotomicDegree
          (K := K) (L := L) p τ ≠
        1) :
    IsOpen
      ((numberFieldTowerFinitePadicCyclicFixedSubgroup
          (K := K) (L := L) p τ :
        ClosedSubgroup
          (Gal(SeparableClosure ℚ / ℚ))) :
        Set (Gal(SeparableClosure ℚ / ℚ))) := by
  let H :=
    numberFieldTowerBaseSubgroup K L
  let U :=
    numberFieldTowerFinitePadicCyclicPreimage
      (K := K) (L := L) p τ
  change
    IsOpen
      (Subtype.val '' (U : Set H.toSubgroup))
  exact
    (numberFieldTowerBaseSubgroup_isOpen K L).isOpenMap_subtype_val
      (U : Set H.toSubgroup)
      (numberFieldTowerFinitePadicCyclicPreimage_isOpen
        (K := K) (L := L) p τ hτ)

end Reciprocity
end GlobalClassFieldTheory
end
end

section
-- module Solutions.OAIQ244_DUKE.GlobalClassFieldTheory_Reciprocity_LocalGlobalArtinCompatibility_FinitePadicAuxiliaryField
attribute [-instance] _root_.GlobalClassFieldTheory.GlobalClassFields.bigHilbertClassFieldAlgebraOverOriginal _root_.GlobalClassFieldTheory.GlobalClassFields.bigHilbertClassFieldBaseAlgebraOverOriginal _root_.GlobalClassFieldTheory.GlobalClassFields.bigHilbertClassFieldIsGaloisOverOriginal _root_.GlobalClassFieldTheory.GlobalClassFields.bigHilbertClassFieldNormSubgroup_normal _root_.GlobalClassFieldTheory.GlobalClassFields.bigHilbertClassFieldScalarTowerOverOriginal _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexClassFieldAlgebraOverOriginal _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexClassFieldBaseAlgebraOverOriginal _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexClassFieldIsGaloisOverOriginal _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexClassFieldScalarTowerOverOriginal _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexNormAmbientIsGalois _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexNormCyclotomicFieldIsGalois _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexNormKummerFieldAlgebraOverBase _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexNormKummerFieldModuleOverBase _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexNormKummerFieldSMulOverBase _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexNormKummerFieldScalarTower _root_.GlobalClassFieldTheory.GlobalClassFields.ordinaryNormClassFieldAbsoluteFiniteDimensional _root_.GlobalClassFieldTheory.GlobalClassFields.ordinaryNormClassFieldBaseFiniteDimensional _root_.GlobalClassFieldTheory.GlobalClassFields.ordinaryNormClassFieldBaseNumberField _root_.GlobalClassFieldTheory.GlobalClassFields.ordinaryNormClassFieldExtensionFiniteDimensional _root_.GlobalClassFieldTheory.GlobalClassFields.ordinaryNormClassFieldExtensionIsAbelianGalois _root_.GlobalClassFieldTheory.GlobalClassFields.ordinaryNormClassFieldExtensionIsGalois _root_.GlobalClassFieldTheory.GlobalClassFields.ordinaryNormClassFieldExtensionNumberField _root_.GlobalClassFieldTheory.GlobalClassFields.ordinaryNormClassFieldScalarTower _root_.GlobalClassFieldTheory.GlobalClassFields.smallHilbertClassFieldAlgebraOverOriginal _root_.GlobalClassFieldTheory.GlobalClassFields.smallHilbertClassFieldBaseAlgebraOverOriginal _root_.GlobalClassFieldTheory.GlobalClassFields.smallHilbertClassFieldIsGaloisOverOriginal _root_.GlobalClassFieldTheory.GlobalClassFields.smallHilbertClassFieldScalarTowerOverOriginal _root_.GlobalClassFieldTheory.Reciprocity.infinitePlaceComplexificationOverfield_algebra _root_.GlobalClassFieldTheory.Reciprocity.infinitePlaceComplexificationOverfield_baseAlgebra _root_.GlobalClassFieldTheory.Reciprocity.ramifiedInfinitePlaceRealFixedField_algebra _root_.GlobalClassFieldTheory.Reciprocity.rationalComplexification_infinitePlaceOverfield_algebra _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.diagonalLogAction _root_.OAI.PrimeDegreePackets.instTopologicalSpaceLocalAlgebra _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.labelPrime_fact _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable
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
# The finite p-adic auxiliary field

This module realizes the simultaneous finite/cyclotomic lift as an actual
number field and proves the subgroup and intermediate-field identities
needed by the auxiliary-field argument.
-/

open scoped IsMulCommutative NumberField
open AlgebraicNumberTheory IsDedekindDomain NumberField
open IdeleGroup RelativeIdeleGroup
open AlgebraicNumberTheory.Valuations
open HilbertRamification
open CyclicCohomology
open KummerTheory ClassFormation

noncomputable section

namespace GlobalClassFieldTheory
namespace Reciprocity

open GlobalClassFields

variable
    {K L : Type}
    [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsAbelianGalois K L]

attribute [local instance]
  rationalSeparableClosureAlgebra

attribute [local instance] GlobalClassFieldTheory.Reciprocity.instFactPrimeValNat_solutions_8
attribute [local instance] GlobalClassFieldTheory.Reciprocity.finitePadicAuxiliaryExtensionNormal
local instance finitePadicAuxiliaryExtensionQuotientFinite_r7b74b3_1 :
    Finite
      ((numberFieldTowerBaseSubgroup K L).toSubgroup ⧸
        extensionSubgroup
          (numberFieldTowerBaseSubgroup K L)
          (numberFieldTowerTopSubgroup L)
          (numberFieldTowerTopSubgroup_le_baseSubgroup K L)) :=
  numberFieldTowerExtensionQuotient_finite K L
attribute [local instance] GlobalClassFieldTheory.Reciprocity.finitePadicAuxiliaryExtensionQuotientIsMulCommutative
/-- A nonzero-degree lift produces a genuine number field: its
concrete fixed field is finite over `ℚ`. -/
theorem numberFieldTowerFinitePadicCyclicFixedField_finiteDimensional
    (p : Nat.Primes)
    (τ : (numberFieldTowerBaseSubgroup K L).toSubgroup)
    (hτ :
      numberFieldTowerBaseSubgroupPadicCyclotomicDegree
          (K := K) (L := L) p τ ≠
        1) :
    FiniteDimensional ℚ
      (numberFieldTowerFinitePadicCyclicFixedField
        (K := K) (L := L) p τ) := by
  let S :=
    numberFieldTowerFinitePadicCyclicFixedSubgroup
      (K := K) (L := L) p τ
  let F :=
    numberFieldTowerFinitePadicCyclicFixedField
      (K := K) (L := L) p τ
  apply
    (InfiniteGalois.isOpen_iff_finite
      (K := SeparableClosure ℚ) F).1
  change IsOpen
    (IntermediateField.fixedField S.toSubgroup).fixingSubgroup.carrier
  rw [InfiniteGalois.fixingSubgroup_fixedField S]
  exact
    numberFieldTowerFinitePadicCyclicFixedSubgroup_isOpen
      (K := K) (L := L) p τ hτ

noncomputable instance
    numberFieldTowerFinitePadicAuxiliary_baseAlgebra
    (p : Nat.Primes)
    (τ : (numberFieldTowerBaseSubgroup K L).toSubgroup) :
    Algebra K
      (LocalClassFieldTheory.abstractFixedField
        ℚ (SeparableClosure ℚ)
        (numberFieldTowerFinitePadicCyclicFixedSubgroup
          (K := K) (L := L) p τ)) := by
  exact
    (numberFieldTowerFinitePadicAuxiliaryBaseEmbedding
      (K := K) (L := L) p τ).toRingHom.toAlgebra


/-- Every genuine finite-place decomposition automorphism has a
compatible embedded absolute lift with the same finite quotient class
and positive integral cyclotomic `p`-adic degree. -/
theorem exists_numberFieldTowerFinitePadicLift_of_finitePlace
    (v : HeightOneSpectrum (𝓞 K))
    (p : Nat.Primes)
    (σ :
      absoluteValueDecompositionGroup K
        (chosenFinitePlaceExtension (L := L) v).1) :
    letI _ : Algebra K (SeparableClosure ℚ) :=
      numberFieldTowerSeparableClosureBaseAlgebra K L
    letI _ : Algebra L (SeparableClosure ℚ) :=
      numberFieldTowerSeparableClosureTopAlgebra L
    letI _ : IsScalarTower K L (SeparableClosure ℚ) :=
      numberFieldTowerSeparableClosureScalarTower K L
    ∃ τ : (numberFieldTowerBaseSubgroup K L).toSubgroup,
      numberFieldTowerExtensionQuotientEquivGaloisGroup K L
          (numberFieldTowerFiniteQuotientCoordinate
            (K := K) (L := L) τ) =
        σ.1 ∧
      (numberFieldTowerSeparableClosureEquivBaseSubgroup K L).symm τ ∈
        absoluteValueDecompositionGroup K
          (numberFieldTowerFinitePlaceExtensionToSeparableClosure
            K L v
            (chosenFinitePlaceExtension (L := L) v)).1 ∧
      numberFieldTowerBaseSubgroupPadicCyclotomicDegree
          (K := K) (L := L) p τ ≠
        1 ∧
      ∃ n : ℕ, 0 < n ∧
        numberFieldTowerBaseSubgroupPadicCyclotomicDegree
            (K := K) (L := L) p τ =
          (Multiplicative.ofAdd (1 : ℤ_[p.1])) ^ n := by
  let : Algebra K (SeparableClosure ℚ) :=
    numberFieldTowerSeparableClosureBaseAlgebra K L
  let : Algebra L (SeparableClosure ℚ) :=
    numberFieldTowerSeparableClosureTopAlgebra L
  let : IsScalarTower K L (SeparableClosure ℚ) :=
    numberFieldTowerSeparableClosureScalarTower K L
  obtain ⟨τΩ, hτΩrestrict, n, hn, hτΩdegree⟩ :=
    exists_finitePlaceSeparableClosureLift_with_positivePadicCyclotomicDegree
      (K := K) (L := L) v p σ
  let τ :
      (numberFieldTowerBaseSubgroup K L).toSubgroup :=
    numberFieldTowerSeparableClosureEquivBaseSubgroup
      K L τΩ.1
  have hfinite :
      numberFieldTowerExtensionQuotientEquivGaloisGroup K L
          (numberFieldTowerFiniteQuotientCoordinate
            (K := K) (L := L) τ) =
        σ.1 := by
    change
      numberFieldTowerExtensionQuotientEquivGaloisGroup K L
          (QuotientGroup.mk
            (numberFieldTowerSeparableClosureEquivBaseSubgroup
              K L τΩ.1)) =
        σ.1
    rw [
      numberFieldTowerExtensionQuotientEquivGaloisGroup_mk_baseSubgroupEquiv]
    exact congrArg Subtype.val hτΩrestrict
  have hdegree :
      numberFieldTowerBaseSubgroupPadicCyclotomicDegree
          (K := K) (L := L) p τ =
        (Multiplicative.ofAdd (1 : ℤ_[p.1])) ^ n := by
    exact hτΩdegree
  have hdecomposition :
      (numberFieldTowerSeparableClosureEquivBaseSubgroup K L).symm τ ∈
        absoluteValueDecompositionGroup K
          (numberFieldTowerFinitePlaceExtensionToSeparableClosure
            K L v
            (chosenFinitePlaceExtension (L := L) v)).1 := by
    simpa only [τ, MulEquiv.symm_apply_apply] using τΩ.2
  refine
    ⟨τ, hfinite, hdecomposition, ?_, n, hn, hdegree⟩
  rw [hdegree]
  exact
    PadicInt.multiplicative_positiveNatDegree_ne_one
      p.1 n hn

/-- Generation of the actual finite Galois group transports back
through the compatible finite quotient coordinate. -/
theorem
    numberFieldTowerFiniteQuotientCoordinate_generates_of_galoisGenerator
    (τ : (numberFieldTowerBaseSubgroup K L).toSubgroup)
    (σ : Gal(L / K))
    (hτσ :
      numberFieldTowerExtensionQuotientEquivGaloisGroup K L
          (numberFieldTowerFiniteQuotientCoordinate
            (K := K) (L := L) τ) =
        σ)
    (hσ : Subgroup.closure ({σ} : Set (Gal(L / K))) = ⊤) :
    Subgroup.closure
        ({numberFieldTowerFiniteQuotientCoordinate
            (K := K) (L := L) τ} :
          Set
            ((numberFieldTowerBaseSubgroup K L).toSubgroup ⧸
              extensionSubgroup
                (numberFieldTowerBaseSubgroup K L)
                (numberFieldTowerTopSubgroup L)
                (numberFieldTowerTopSubgroup_le_baseSubgroup K L))) =
      ⊤ := by
  let e :=
    numberFieldTowerExtensionQuotientEquivGaloisGroup K L
  let q :
      (numberFieldTowerFiniteGaloisSubextension
        K L).extensionQuotient :=
    numberFieldTowerFiniteQuotientCoordinate
      (K := K) (L := L) τ
  have hq : e.toMonoidHom q = σ := by
    exact hτσ
  change
    Subgroup.closure
        ({q} :
          Set
            (numberFieldTowerFiniteGaloisSubextension
              K L).extensionQuotient) =
      ⊤
  apply Subgroup.map_injective (f := e.toMonoidHom) e.injective
  rw [MonoidHom.map_closure, Set.image_singleton,
    hq, hσ,
    Subgroup.map_top_of_surjective e.toMonoidHom e.surjective]

/-- If the finite quotient coordinate of a lift generates the whole
finite Galois quotient, then its cyclic preimage together with the
top-field subgroup generates the whole embedded absolute Galois
group. -/
theorem
    numberFieldTowerFinitePadicCyclicPreimage_sup_extensionSubgroup_eq_top
    (p : Nat.Primes)
    (τ : (numberFieldTowerBaseSubgroup K L).toSubgroup)
    (hgenerate :
      Subgroup.closure
          ({numberFieldTowerFiniteQuotientCoordinate
              (K := K) (L := L) τ} :
            Set
              ((numberFieldTowerBaseSubgroup K L).toSubgroup ⧸
                extensionSubgroup
                  (numberFieldTowerBaseSubgroup K L)
                  (numberFieldTowerTopSubgroup L)
                  (numberFieldTowerTopSubgroup_le_baseSubgroup K L))) =
        ⊤) :
    (numberFieldTowerFinitePadicCyclicPreimage
          (K := K) (L := L) p τ).toSubgroup ⊔
        extensionSubgroup
          (numberFieldTowerBaseSubgroup K L)
          (numberFieldTowerTopSubgroup L)
          (numberFieldTowerTopSubgroup_le_baseSubgroup K L) =
      ⊤ := by
  let H :=
    numberFieldTowerBaseSubgroup K L
  let N :=
    extensionSubgroup
      H
      (numberFieldTowerTopSubgroup L)
      (numberFieldTowerTopSubgroup_le_baseSubgroup K L)
  let Q := H.toSubgroup ⧸ N
  let P :=
    numberFieldTowerFinitePadicImage
      (K := K) (L := L) p
  let coordinate :=
    numberFieldTowerFinitePadicCoordinate
      (K := K) (L := L) p
  let rangeRestriction :=
    numberFieldTowerFinitePadicRangeRestriction
      (K := K) (L := L) p
  let γ : P.toSubgroup :=
    rangeRestriction τ
  let Γ :=
    ClassFormation.padicCyclicClosure γ
  let finiteProjection :
      P.toSubgroup →*
        Q :=
    (MonoidHom.fst Q
      (Multiplicative ℤ_[p.1])).comp
        P.toSubgroup.subtype
  have hprojection :
      Γ.toSubgroup.map finiteProjection = ⊤ := by
    apply top_unique
    rw [← hgenerate]
    apply (Subgroup.closure_le _).2
    intro q hq
    rw [Set.mem_singleton_iff] at hq
    subst q
    refine
      ⟨γ,
        (ClassFormation.padicCyclicClosureGenerator γ).2,
        ?_⟩
    rfl
  have hquotientSurjective :
      ∀ q : Q,
        ∃ u : H.toSubgroup,
          u ∈
              (numberFieldTowerFinitePadicCyclicPreimage
                (K := K) (L := L) p τ).toSubgroup ∧
            numberFieldTowerFiniteQuotientCoordinate
                (K := K) (L := L) u =
              q := by
    intro q
    have hq :
        q ∈ Γ.toSubgroup.map finiteProjection := by
      rw [hprojection]
      trivial
    obtain ⟨z, hzΓ, hzq⟩ := hq
    obtain ⟨u, hu⟩ :=
      numberFieldTowerFinitePadicRangeRestriction_surjective
        (K := K) (L := L) p z
    refine ⟨u, ?_, ?_⟩
    · change rangeRestriction u ∈ Γ.toSubgroup
      rw [hu]
      exact hzΓ
    · calc
        numberFieldTowerFiniteQuotientCoordinate
            (K := K) (L := L) u =
            finiteProjection (rangeRestriction u) := rfl
        _ = finiteProjection z := congrArg finiteProjection hu
        _ = q := hzq
  apply top_unique
  intro h _
  obtain ⟨u, huU, huq⟩ :=
    hquotientSurjective
      (numberFieldTowerFiniteQuotientCoordinate
        (K := K) (L := L) h)
  let k : H.toSubgroup :=
    h * u⁻¹
  have hkN : k ∈ N := by
    apply (QuotientGroup.eq_one_iff (N := N) k).mp
    change
      numberFieldTowerFiniteQuotientCoordinate
          (K := K) (L := L) (h * u⁻¹) =
        1
    rw [map_mul, map_inv, huq, mul_inv_cancel]
  have hkSup :
      k ∈
        (numberFieldTowerFinitePadicCyclicPreimage
            (K := K) (L := L) p τ).toSubgroup ⊔
          N :=
    (le_sup_right :
      N ≤
        (numberFieldTowerFinitePadicCyclicPreimage
            (K := K) (L := L) p τ).toSubgroup ⊔ N) hkN
  have huSup :
      u ∈
        (numberFieldTowerFinitePadicCyclicPreimage
            (K := K) (L := L) p τ).toSubgroup ⊔
          N :=
    (le_sup_left :
      (numberFieldTowerFinitePadicCyclicPreimage
          (K := K) (L := L) p τ).toSubgroup ≤
        (numberFieldTowerFinitePadicCyclicPreimage
            (K := K) (L := L) p τ).toSubgroup ⊔ N) huU
  have hku :
      k * u = h := by
    simp only [k, inv_mul_cancel_right]
  rw [← hku]
  exact
    ((numberFieldTowerFinitePadicCyclicPreimage
      (K := K) (L := L) p τ).toSubgroup ⊔ N).mul_mem
      hkSup huSup

/-- Ambient form of the generation statement: the auxiliary cyclic
fixed subgroup together with the subgroup fixing `L` generates the
subgroup fixing `K`. -/
theorem
    numberFieldTowerFinitePadicCyclicFixedSubgroup_sup_topSubgroup
    (p : Nat.Primes)
    (τ : (numberFieldTowerBaseSubgroup K L).toSubgroup)
    (hgenerate :
      Subgroup.closure
          ({numberFieldTowerFiniteQuotientCoordinate
              (K := K) (L := L) τ} :
            Set
              ((numberFieldTowerBaseSubgroup K L).toSubgroup ⧸
                extensionSubgroup
                  (numberFieldTowerBaseSubgroup K L)
                  (numberFieldTowerTopSubgroup L)
                  (numberFieldTowerTopSubgroup_le_baseSubgroup K L))) =
        ⊤) :
    (numberFieldTowerFinitePadicCyclicFixedSubgroup
          (K := K) (L := L) p τ).toSubgroup ⊔
        (numberFieldTowerTopSubgroup L).toSubgroup =
      (numberFieldTowerBaseSubgroup K L).toSubgroup := by
  let H :=
    numberFieldTowerBaseSubgroup K L
  let T :=
    numberFieldTowerTopSubgroup L
  let N :=
    extensionSubgroup
      H T
      (numberFieldTowerTopSubgroup_le_baseSubgroup K L)
  let U :=
    numberFieldTowerFinitePadicCyclicPreimage
      (K := K) (L := L) p τ
  have hrelative :
      U.toSubgroup ⊔ N = ⊤ :=
    numberFieldTowerFinitePadicCyclicPreimage_sup_extensionSubgroup_eq_top
      (K := K) (L := L) p τ hgenerate
  have hNmap :
      N.map H.toSubgroup.subtype =
        T.toSubgroup := by
    exact
      Subgroup.map_subgroupOf_eq_of_le
        (numberFieldTowerTopSubgroup_le_baseSubgroup K L)
  change
    U.toSubgroup.map H.toSubgroup.subtype ⊔
        T.toSubgroup =
      H.toSubgroup
  rw [← hNmap, ← Subgroup.map_sup,
    hrelative, ← MonoidHom.range_eq_map,
    H.toSubgroup.range_subtype]

/-- The concrete auxiliary fixed field is linearly disjoint from `L`
over the compatible embedded copy of `K`. -/
theorem
    numberFieldTowerFinitePadicCyclicFixedField_inf_topField
    (p : Nat.Primes)
    (τ : (numberFieldTowerBaseSubgroup K L).toSubgroup)
    (hgenerate :
      Subgroup.closure
          ({numberFieldTowerFiniteQuotientCoordinate
              (K := K) (L := L) τ} :
            Set
              ((numberFieldTowerBaseSubgroup K L).toSubgroup ⧸
                extensionSubgroup
                  (numberFieldTowerBaseSubgroup K L)
                  (numberFieldTowerTopSubgroup L)
                  (numberFieldTowerTopSubgroup_le_baseSubgroup K L))) =
        ⊤) :
    numberFieldTowerFinitePadicCyclicFixedField
          (K := K) (L := L) p τ ⊓
        numberFieldInRationalSeparableClosure L =
      numberFieldTowerBaseField K L := by
  let S :=
    numberFieldTowerFinitePadicCyclicFixedSubgroup
      (K := K) (L := L) p τ
  let T :=
    numberFieldTowerTopSubgroup L
  let H :=
    numberFieldTowerBaseSubgroup K L
  change
    IntermediateField.fixedField S.toSubgroup ⊓
        numberFieldInRationalSeparableClosure L =
      numberFieldTowerBaseField K L
  rw [
    ← InfiniteGalois.fixedField_fixingSubgroup
      (numberFieldInRationalSeparableClosure L),
    ← InfiniteGalois.fixedField_fixingSubgroup
      (numberFieldTowerBaseField K L)]
  change
    IntermediateField.fixedField S.toSubgroup ⊓
        IntermediateField.fixedField T.toSubgroup =
      IntermediateField.fixedField H.toSubgroup
  rw [
    ← IntermediateField.fixedField_sup_eq_inf,
    numberFieldTowerFinitePadicCyclicFixedSubgroup_sup_topSubgroup
      (K := K) (L := L) p τ hgenerate]

/-- If the finite quotient coordinate is `p`-primary, adjoining the
actual rational `p`-primary cyclotomic field to the auxiliary fixed
field contains the compatible copy of `L`.

This is the field-theoretic conclusion of the simultaneous
finite/cyclotomic lift: the intersection of the two fixing subgroups
already fixes `L`, hence their fixed-field compositum contains `L`. -/
theorem
    numberFieldTowerTopField_le_finitePadicCyclicFixedField_sup_padicCyclotomicField
    (p : Nat.Primes)
    (τ : (numberFieldTowerBaseSubgroup K L).toSubgroup)
    (n : ℕ) (hn : 0 < n)
    (hdegree :
      numberFieldTowerBaseSubgroupPadicCyclotomicDegree
          (K := K) (L := L) p τ =
        (Multiplicative.ofAdd (1 : ℤ_[p.1])) ^ n)
    (hprimary :
      numberFieldTowerFiniteQuotientCoordinate
          (K := K) (L := L) τ ∈
        CommGroup.primaryComponent
          ((numberFieldTowerBaseSubgroup K L).toSubgroup ⧸
            extensionSubgroup
              (numberFieldTowerBaseSubgroup K L)
              (numberFieldTowerTopSubgroup L)
              (numberFieldTowerTopSubgroup_le_baseSubgroup K L))
          p.1) :
    numberFieldInRationalSeparableClosure L ≤
      numberFieldTowerFinitePadicCyclicFixedField
            (K := K) (L := L) p τ ⊔
        rationalCyclotomicPadicField p := by
  let S :=
    numberFieldTowerFinitePadicCyclicFixedSubgroup
      (K := K) (L := L) p τ
  let T :=
    numberFieldTowerTopSubgroup L
  let F :=
    numberFieldTowerFinitePadicCyclicFixedField
      (K := K) (L := L) p τ
  let C : @IntermediateField ℚ (SeparableClosure ℚ) _ _
      rationalSeparableClosureAlgebra :=
    rationalCyclotomicPadicField p
  have hfixing :
      (F ⊔ C).fixingSubgroup ≤
        T.toSubgroup := by
    change
      (IntermediateField.fixedField S.toSubgroup ⊔ C).fixingSubgroup ≤
        T.toSubgroup
    rw [
      IntermediateField.fixingSubgroup_sup,
      InfiniteGalois.fixingSubgroup_fixedField S]
    intro σ hσ
    apply
      numberFieldTowerFinitePadicCyclicFixedSubgroup_inf_absolutePadicKernel_le_topSubgroup
        (K := K) (L := L) p τ n hn hdegree hprimary
    refine ⟨hσ.1, ?_⟩
    let : Algebra ℚ rationalCyclotomicZHatField :=
      rationalCyclotomicZHatField.algebra'
    let : @Normal ℚ rationalCyclotomicZHatField _ _
        rationalCyclotomicZHatField.algebra' :=
      rationalCyclotomicZHatField_normal
    let E :=
      rationalCyclotomicPadicFieldWithinZHat p
    change
      rationalCyclotomicPadicCoordinate p
          (rationalAbsoluteGaloisRestrictionToCyclotomicZHat σ) =
        1
    have hr :
        rationalAbsoluteGaloisRestrictionToCyclotomicZHat σ ∈
          E.fixingSubgroup := by
      rw [IntermediateField.mem_fixingSubgroup_iff]
      intro x hx
      apply Subtype.ext
      have hfix :
          σ x.1 = x.1 :=
        (IntermediateField.mem_fixingSubgroup_iff
          (IntermediateField.lift E) σ).1 hσ.2 x.1
            ((IntermediateField.mem_lift x).2 hx)
      exact
        (AlgEquiv.restrictNormal_commutes
          σ rationalCyclotomicZHatField x).trans hfix
    rw [rationalCyclotomicPadicFieldWithinZHat_fixingSubgroup]
      at hr
    exact hr
  rw [
    ← InfiniteGalois.fixedField_fixingSubgroup
      (numberFieldInRationalSeparableClosure L)]
  change
    IntermediateField.fixedField T.toSubgroup ≤
      F ⊔ C
  rw [
    ← InfiniteGalois.fixedField_fixingSubgroup
      (F ⊔ C)]
  exact
    IntermediateField.fixedField_le hfixing

/-- For a finite-place automorphism generating `Gal(L/K)`, construct
the genuine auxiliary number field used in the cyclotomic reduction.

The field is finite over `ℚ`, contains the compatible copy of `K`, and
has intersection with the compatible copy of `L` exactly equal to that
copy of `K`.  Its defining lift has the prescribed local restriction
and positive integral cyclotomic `p`-adic degree. -/
theorem exists_finitePlaceCyclotomicAuxiliaryFixedField
    (v : HeightOneSpectrum (𝓞 K))
    (p : Nat.Primes)
    (σ :
      absoluteValueDecompositionGroup K
        (chosenFinitePlaceExtension (L := L) v).1)
    (hσ :
      Subgroup.closure
          ({σ.1} : Set (Gal(L / K))) =
        ⊤) :
    letI _ : Algebra K (SeparableClosure ℚ) :=
      numberFieldTowerSeparableClosureBaseAlgebra K L
    letI _ : Algebra L (SeparableClosure ℚ) :=
      numberFieldTowerSeparableClosureTopAlgebra L
    letI _ : IsScalarTower K L (SeparableClosure ℚ) :=
      numberFieldTowerSeparableClosureScalarTower K L
    ∃ τ : (numberFieldTowerBaseSubgroup K L).toSubgroup,
      numberFieldTowerExtensionQuotientEquivGaloisGroup K L
          (numberFieldTowerFiniteQuotientCoordinate
            (K := K) (L := L) τ) =
        σ.1 ∧
      (numberFieldTowerSeparableClosureEquivBaseSubgroup K L).symm τ ∈
        absoluteValueDecompositionGroup K
          (numberFieldTowerFinitePlaceExtensionToSeparableClosure
            K L v
            (chosenFinitePlaceExtension (L := L) v)).1 ∧
      numberFieldTowerBaseSubgroupPadicCyclotomicDegree
          (K := K) (L := L) p τ ≠
        1 ∧
      FiniteDimensional ℚ
        (numberFieldTowerFinitePadicCyclicFixedField
          (K := K) (L := L) p τ) ∧
      numberFieldTowerBaseField K L ≤
        numberFieldTowerFinitePadicCyclicFixedField
          (K := K) (L := L) p τ ∧
      numberFieldTowerFinitePadicCyclicFixedField
            (K := K) (L := L) p τ ⊓
          numberFieldInRationalSeparableClosure L =
        numberFieldTowerBaseField K L ∧
      ∃ n : ℕ, 0 < n ∧
        numberFieldTowerBaseSubgroupPadicCyclotomicDegree
            (K := K) (L := L) p τ =
          (Multiplicative.ofAdd (1 : ℤ_[p.1])) ^ n := by
  let : Algebra K (SeparableClosure ℚ) :=
    numberFieldTowerSeparableClosureBaseAlgebra K L
  let : Algebra L (SeparableClosure ℚ) :=
    numberFieldTowerSeparableClosureTopAlgebra L
  let : IsScalarTower K L (SeparableClosure ℚ) :=
    numberFieldTowerSeparableClosureScalarTower K L
  obtain
      ⟨τ, hτσ, hτdecomposition, hτdegree,
        n, hn, hdegree⟩ :=
    exists_numberFieldTowerFinitePadicLift_of_finitePlace
      (K := K) (L := L) v p σ
  have hgenerate :=
    numberFieldTowerFiniteQuotientCoordinate_generates_of_galoisGenerator
      (K := K) (L := L) τ σ.1 hτσ hσ
  refine
    ⟨τ, hτσ, hτdecomposition, hτdegree,
      numberFieldTowerFinitePadicCyclicFixedField_finiteDimensional
        (K := K) (L := L) p τ hτdegree,
      numberFieldTowerBaseField_le_finitePadicCyclicFixedField
        (K := K) (L := L) p τ,
      numberFieldTowerFinitePadicCyclicFixedField_inf_topField
        (K := K) (L := L) p τ hgenerate,
      n, hn, hdegree⟩

/-- A `p`-primary local generator admits a genuine auxiliary number
field whose compositum with the rational `p`-primary cyclotomic field
contains `L`.

Besides the field containment, the construction records the two
properties needed for descent: the auxiliary field meets `L` exactly
in `K`, and the chosen absolute lift has positive integral
cyclotomic degree. -/
theorem exists_finitePlacePrimaryCyclotomicAuxiliaryFixedField
    (v : HeightOneSpectrum (𝓞 K))
    (p : Nat.Primes)
    (σ :
      absoluteValueDecompositionGroup K
        (chosenFinitePlaceExtension (L := L) v).1)
    (hgenerate :
      Subgroup.closure
          ({σ.1} : Set (Gal(L / K))) =
        ⊤)
    (hprimary :
      σ.1 ∈
        CommGroup.primaryComponent
          (Gal(L / K)) p.1) :
    letI _ : Algebra K (SeparableClosure ℚ) :=
      numberFieldTowerSeparableClosureBaseAlgebra K L
    letI _ : Algebra L (SeparableClosure ℚ) :=
      numberFieldTowerSeparableClosureTopAlgebra L
    letI _ : IsScalarTower K L (SeparableClosure ℚ) :=
      numberFieldTowerSeparableClosureScalarTower K L
    ∃ τ : (numberFieldTowerBaseSubgroup K L).toSubgroup,
      numberFieldTowerExtensionQuotientEquivGaloisGroup K L
          (numberFieldTowerFiniteQuotientCoordinate
            (K := K) (L := L) τ) =
        σ.1 ∧
      (numberFieldTowerSeparableClosureEquivBaseSubgroup K L).symm τ ∈
        absoluteValueDecompositionGroup K
          (numberFieldTowerFinitePlaceExtensionToSeparableClosure
            K L v
            (chosenFinitePlaceExtension (L := L) v)).1 ∧
      numberFieldTowerBaseSubgroupPadicCyclotomicDegree
          (K := K) (L := L) p τ ≠
        1 ∧
      FiniteDimensional ℚ
        (numberFieldTowerFinitePadicCyclicFixedField
          (K := K) (L := L) p τ) ∧
      numberFieldTowerBaseField K L ≤
        numberFieldTowerFinitePadicCyclicFixedField
          (K := K) (L := L) p τ ∧
      numberFieldTowerFinitePadicCyclicFixedField
            (K := K) (L := L) p τ ⊓
          numberFieldInRationalSeparableClosure L =
        numberFieldTowerBaseField K L ∧
      numberFieldInRationalSeparableClosure L ≤
        numberFieldTowerFinitePadicCyclicFixedField
              (K := K) (L := L) p τ ⊔
          rationalCyclotomicPadicField p ∧
      ∃ n : ℕ, 0 < n ∧
        numberFieldTowerBaseSubgroupPadicCyclotomicDegree
            (K := K) (L := L) p τ =
          (Multiplicative.ofAdd (1 : ℤ_[p.1])) ^ n := by
  let : Algebra K (SeparableClosure ℚ) :=
    numberFieldTowerSeparableClosureBaseAlgebra K L
  let : Algebra L (SeparableClosure ℚ) :=
    numberFieldTowerSeparableClosureTopAlgebra L
  let : IsScalarTower K L (SeparableClosure ℚ) :=
    numberFieldTowerSeparableClosureScalarTower K L
  obtain
      ⟨τ, hτσ, hτdecomposition, hτdegree,
        hfinite, hbase, hintersection,
        n, hn, hdegree⟩ :=
    exists_finitePlaceCyclotomicAuxiliaryFixedField
      (K := K) (L := L) v p σ hgenerate
  have hprimaryQuotient :
      numberFieldTowerFiniteQuotientCoordinate
          (K := K) (L := L) τ ∈
        CommGroup.primaryComponent
          ((numberFieldTowerBaseSubgroup K L).toSubgroup ⧸
            extensionSubgroup
              (numberFieldTowerBaseSubgroup K L)
              (numberFieldTowerTopSubgroup L)
              (numberFieldTowerTopSubgroup_le_baseSubgroup K L))
          p.1 := by
    obtain ⟨m, hm⟩ := hprimary
    refine ⟨m, ?_⟩
    let e :=
      numberFieldTowerExtensionQuotientEquivGaloisGroup K L
    let q :=
      numberFieldTowerFiniteQuotientCoordinate
        (K := K) (L := L) τ
    let N : ℕ := p.1 ^ m
    have hq : e q = σ.1 := by
      exact hτσ
    have hmN : σ.1 ^ N = 1 := by
      exact hm
    change q ^ N = 1
    apply e.injective
    calc
      e (q ^ N) = (e q) ^ N := by
        exact map_pow e q N
      _ = σ.1 ^ N := by rw [hq]
      _ = 1 := hmN
      _ = e 1 := (map_one e).symm
  have hcontainment :=
    numberFieldTowerTopField_le_finitePadicCyclicFixedField_sup_padicCyclotomicField
      (K := K) (L := L) p τ n hn hdegree
        hprimaryQuotient
  exact
    ⟨τ, hτσ, hτdecomposition, hτdegree,
      hfinite, hbase, hintersection,
      hcontainment, n, hn, hdegree⟩

end Reciprocity
end GlobalClassFieldTheory
end
end

section
-- module Solutions.OAIQ244_DUKE.GlobalClassFieldTheory_Reciprocity_LocalGlobalArtinCompatibility_Factorization
attribute [-instance] _root_.GlobalClassFieldTheory.GlobalClassFields.ConductorialSubgroup.finiteIndex _root_.GlobalClassFieldTheory.GlobalClassFields.bigHilbertClassFieldAlgebraOverOriginal _root_.GlobalClassFieldTheory.GlobalClassFields.bigHilbertClassFieldBaseAlgebraOverOriginal _root_.GlobalClassFieldTheory.GlobalClassFields.bigHilbertClassFieldIsGaloisOverOriginal _root_.GlobalClassFieldTheory.GlobalClassFields.bigHilbertClassFieldNormSubgroupFiniteIndex _root_.GlobalClassFieldTheory.GlobalClassFields.bigHilbertClassFieldNormSubgroup_normal _root_.GlobalClassFieldTheory.GlobalClassFields.bigHilbertClassFieldScalarTowerOverOriginal _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexClassFieldAlgebraOverOriginal _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexClassFieldBaseAlgebraOverOriginal _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexClassFieldIsGaloisOverOriginal _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexClassFieldScalarTowerOverOriginal _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexNormAmbientFiniteDimensional _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexNormAmbientIsGalois _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexNormAmbientNumberField _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexNormCyclotomicFieldFiniteDimensional _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexNormCyclotomicFieldIsCyclotomicExtension _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexNormCyclotomicFieldIsGalois _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexNormCyclotomicFieldNumberField _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexNormExponentNeZero _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexNormKummerFieldAlgebraOverBase _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexNormKummerFieldFiniteDimensional _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexNormKummerFieldFiniteDimensionalOverBase _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexNormKummerFieldModuleOverBase _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexNormKummerFieldNumberField _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexNormKummerFieldSMulOverBase _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexNormKummerFieldScalarTower _root_.GlobalClassFieldTheory.GlobalClassFields.ideleClassNorm_rangeFiniteIndex _root_.GlobalClassFieldTheory.GlobalClassFields.ordinaryNormClassFieldAbsoluteFiniteDimensional _root_.GlobalClassFieldTheory.GlobalClassFields.ordinaryNormClassFieldExtensionFiniteDimensional _root_.GlobalClassFieldTheory.GlobalClassFields.ordinaryNormClassFieldExtensionIsAbelianGalois _root_.GlobalClassFieldTheory.GlobalClassFields.ordinaryNormClassFieldExtensionIsGalois _root_.GlobalClassFieldTheory.GlobalClassFields.ordinaryNormClassFieldExtensionNumberField _root_.GlobalClassFieldTheory.GlobalClassFields.ordinaryNormClassFieldScalarTower _root_.GlobalClassFieldTheory.GlobalClassFields.smallHilbertClassFieldAlgebraOverOriginal _root_.GlobalClassFieldTheory.GlobalClassFields.smallHilbertClassFieldBaseAlgebraOverOriginal _root_.GlobalClassFieldTheory.GlobalClassFields.smallHilbertClassFieldIsGaloisOverOriginal _root_.GlobalClassFieldTheory.GlobalClassFields.smallHilbertClassFieldNormSubgroupFiniteIndex _root_.GlobalClassFieldTheory.GlobalClassFields.smallHilbertClassFieldScalarTowerOverOriginal _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.GlobalClassFieldTheory.GlobalClassFields.bigHilbertNormQuotient_finite _root_.GlobalClassFieldTheory.GlobalClassFields.bigHilbertNormSubgroup_finiteIndex
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI
attribute [local instance] OAI.starSubalgebraCommCStarAlgebra

set_option autoImplicit false

/-!
# Factorization of the global Artin map through local Artin maps

This module completes the auxiliary-field argument, factors the global
norm-residue map through each local Artin quotient, and proves the
finite-place local-global compatibility theorem.
-/

open scoped IsMulCommutative NumberField
open NumberField
open AlgebraicNumberTheory.Valuations
open HilbertRamification

noncomputable section

namespace GlobalClassFieldTheory
namespace Reciprocity

open ClassFormation
open CyclicCohomology
open KummerTheory

attribute [local instance]
  finitePadicAuxiliaryExtensionQuotientIsMulCommutative

variable
    {K L : Type}
    [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsAbelianGalois K L]

/-- A finite-place element killed by the actual local Artin
homomorphism is also killed by the global norm-residue homomorphism
after insertion as a one-place idele class. -/
theorem globalNormResidueMonoidHom_finitePlaceIdeleClass_eq_one_of_localArtin_eq_one
    (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K))
    (x : (v.adicCompletion K)ˣ)
    (hx :
      chosenFinitePlaceArtinMonoidHom
        (K := K) (L := L) v x = 1) :
    globalNormResidueMonoidHom K L
        (IdeleGroup.finitePlaceIdeleClass v x) = 1 := by
  rw [globalNormResidueMonoidHom_eq_one_iff]
  exact
    finitePlaceIdeleClass_mem_ideleClassNorm_range_of_mem_chosenLocalNorm
      (K := K) (L := L) v x
      ((chosenFinitePlaceArtinMonoidHom_eq_one_iff_chosenLocalNorm
        (K := K) (L := L) v x).1 hx)

/-- The chosen local norm subgroup lies in the kernel of the global
norm-residue homomorphism restricted to the one-place finite idele
class map. -/
theorem chosenFinitePlaceLocalNormSubgroup_le_globalNormResidueKernel
    (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K)) :
    chosenFinitePlaceLocalNormSubgroup
        (K := K) (L := L) v ≤
      ((globalNormResidueMonoidHom K L).comp
        (IdeleGroup.finitePlaceIdeleClass v)).ker := by
  intro x hx
  exact
    globalNormResidueMonoidHom_finitePlaceIdeleClass_eq_one_of_localArtin_eq_one
      (K := K) (L := L) v x
      ((chosenFinitePlaceArtinMonoidHom_eq_one_iff_chosenLocalNorm
        (K := K) (L := L) v x).2 hx)

/-- The global norm-residue symbol at one finite place, factored
through the actual image of the chosen local Artin homomorphism.

The definition uses a preimage only to specify the value.  Its
well-definedness and multiplicativity are consequences of the genuine
one-place norm-kernel theorem above. -/
noncomputable def finitePlaceGlobalNormResidueFactor
    (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K)) :
    (chosenFinitePlaceArtinMonoidHom
        (K := K) (L := L) v).range →*
      (L ≃ₐ[K] L) := by
  let g :
      (v.adicCompletion K)ˣ →* (L ≃ₐ[K] L) :=
    chosenFinitePlaceArtinMonoidHom
      (K := K) (L := L) v
  let f :
      (v.adicCompletion K)ˣ →* (L ≃ₐ[K] L) :=
    (globalNormResidueMonoidHom K L).comp
      (IdeleGroup.finitePlaceIdeleClass v)
  have hker : g.rangeRestrict.ker ≤ f.ker := by
    rw [MonoidHom.ker_rangeRestrict]
    simpa only [g, f, chosenFinitePlaceArtinMonoidHom_ker] using
      chosenFinitePlaceLocalNormSubgroup_le_globalNormResidueKernel
        (K := K) (L := L) v
  exact
    g.rangeRestrict.liftOfSurjective
      g.rangeRestrict_surjective ⟨f, hker⟩

end Reciprocity
end GlobalClassFieldTheory
end
end

section
-- module Solutions.OAIQ244_DUKE.GlobalClassFieldTheory_IdealClassFieldTheory_ArithmeticIdealArtin
attribute [-instance] _root_.GlobalClassFieldTheory.GlobalClassFields.bigHilbertClassFieldAlgebraOverOriginal _root_.GlobalClassFieldTheory.GlobalClassFields.bigHilbertClassFieldBaseAlgebraOverOriginal _root_.GlobalClassFieldTheory.GlobalClassFields.bigHilbertClassFieldIsGaloisOverOriginal _root_.GlobalClassFieldTheory.GlobalClassFields.bigHilbertClassFieldNormSubgroupFiniteIndex _root_.GlobalClassFieldTheory.GlobalClassFields.bigHilbertClassFieldScalarTowerOverOriginal _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexClassFieldAlgebraOverOriginal _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexClassFieldBaseAlgebraOverOriginal _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexClassFieldIsGaloisOverOriginal _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexClassFieldScalarTowerOverOriginal _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexNormAmbientFiniteDimensional _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexNormAmbientIsGalois _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexNormAmbientNumberField _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexNormCyclotomicFieldFiniteDimensional _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexNormCyclotomicFieldIsCyclotomicExtension _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexNormCyclotomicFieldIsGalois _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexNormCyclotomicFieldNumberField _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexNormExponentNeZero _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexNormKummerFieldAlgebraOverBase _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexNormKummerFieldFiniteDimensional _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexNormKummerFieldFiniteDimensionalOverBase _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexNormKummerFieldModuleOverBase _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexNormKummerFieldNumberField _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexNormKummerFieldSMulOverBase _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexNormKummerFieldScalarTower _root_.GlobalClassFieldTheory.GlobalClassFields.ordinaryNormClassFieldAbsoluteFiniteDimensional _root_.GlobalClassFieldTheory.GlobalClassFields.ordinaryNormClassFieldBaseFiniteDimensional _root_.GlobalClassFieldTheory.GlobalClassFields.ordinaryNormClassFieldExtensionFiniteDimensional _root_.GlobalClassFieldTheory.GlobalClassFields.ordinaryNormClassFieldExtensionIsAbelianGalois _root_.GlobalClassFieldTheory.GlobalClassFields.ordinaryNormClassFieldExtensionIsGalois _root_.GlobalClassFieldTheory.GlobalClassFields.ordinaryNormClassFieldExtensionNumberField _root_.GlobalClassFieldTheory.GlobalClassFields.ordinaryNormClassFieldScalarTower _root_.GlobalClassFieldTheory.GlobalClassFields.smallHilbertClassFieldAlgebraOverOriginal _root_.GlobalClassFieldTheory.GlobalClassFields.smallHilbertClassFieldBaseAlgebraOverOriginal _root_.GlobalClassFieldTheory.GlobalClassFields.smallHilbertClassFieldIsGaloisOverOriginal _root_.GlobalClassFieldTheory.GlobalClassFields.smallHilbertClassFieldScalarTowerOverOriginal _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.instTopologicalSpaceLocalAlgebra _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable
attribute [-simp] _root_.GlobalClassFieldTheory.GlobalClassFields.ConductorialSubgroup.mem_fullConductorInfinitePart_iff _root_.GlobalClassFieldTheory.GlobalClassFields.bigHilbertClassFieldBaseEquiv_coe _root_.GlobalClassFieldTheory.GlobalClassFields.bigHilbertClassFieldQuotientCongr_mk _root_.GlobalClassFieldTheory.GlobalClassFields.bigHilbertClassField_algebraMap_original _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexClassFieldBaseEquiv_coe _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexClassField_algebraMap_original _root_.GlobalClassFieldTheory.GlobalClassFields.ideleClassNormQuotientTowerMap_mk _root_.GlobalClassFieldTheory.GlobalClassFields.narrowFiniteConductorRayClassGroupToIdeleClassNormQuotient_rayPrimeClass _root_.GlobalClassFieldTheory.GlobalClassFields.normQuotientEquivOfNarrowFiniteConductorsEqOfRayClassGroupCardsEqNormQuotientCards_mk _root_.GlobalClassFieldTheory.GlobalClassFields.smallHilbertClassFieldQuotientCongr_mk _root_.GlobalClassFieldTheory.GlobalClassFields.smallHilbertClassField_algebraMap_original _root_.GlobalClassFieldTheory.IdealClassFieldTheory.smallHilbertClassFieldIdeleExtensionMap_mk' _root_.OAI.PrimeDegreePackets.ThetaConstruction.schwartzCM_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

/-!
# The ideal Artin map in arithmetic Frobenius normalization

For a defining modulus of a genuine finite abelian class field, this
module composes the ideal ray-class quotient with the topological
arithmetic global norm-residue equivalence.  The resulting map sends an
ordinary prime ideal to arithmetic Frobenius, has the genuine idèle
norm kernel, and induces the canonical ideal class-field isomorphism.
-/

open scoped NumberField Classical

noncomputable section

namespace GlobalClassFieldTheory
namespace IdealClassFieldTheory

open NumberField IsDedekindDomain

variable
    {K L : Type}
    [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    [IsAbelianGalois K L]

attribute [local instance]
  ideleClassSubgroupNormal idealArtinKernelNormal

/-- The genuine Galois-valued ideal Artin map in arithmetic Frobenius
normalization. -/
noncomputable def arithmeticIdealArtinGaloisMap
    (m : RayClass.Modulus K)
    (hm :
      RayClass.Modulus.congruenceSubgroup m ≤
        (_root_.ideleClassNorm K L).range) :
    RayClass.primeToModulusIdeals m →*
      (L ≃ₐ[K] L) :=
  (Reciprocity.arithmeticGlobalNormResidueContinuousMulEquiv
      K L).toMulEquiv.toMonoidHom.comp
    (idealArtinMap m
      ((_root_.ideleClassNorm K L).range) hm)

/-- Evaluating the arithmetic ideal Artin map is evaluation of the ideal
class map followed by arithmetic global reciprocity. -/
@[simp]
theorem arithmeticIdealArtinGaloisMap_apply
    (m : RayClass.Modulus K)
    (hm :
      RayClass.Modulus.congruenceSubgroup m ≤
        (_root_.ideleClassNorm K L).range)
    (a : RayClass.primeToModulusIdeals m) :
    arithmeticIdealArtinGaloisMap
        (K := K) (L := L) m hm a =
      Reciprocity.arithmeticGlobalNormResidueContinuousMulEquiv
        K L
        (idealArtinMap m
          ((_root_.ideleClassNorm K L).range) hm a) :=
  rfl

/-- The arithmetic ideal Artin map is exactly the inverse of the
geometrically normalized map on every ideal. -/
@[simp]
theorem arithmeticIdealArtinGaloisMap_eq_inv_idealArtinGaloisMap
    (m : RayClass.Modulus K)
    (hm :
      RayClass.Modulus.congruenceSubgroup m ≤
        (_root_.ideleClassNorm K L).range)
    (a : RayClass.primeToModulusIdeals m) :
    arithmeticIdealArtinGaloisMap
        (K := K) (L := L) m hm a =
      (idealArtinGaloisMap
        (K := K) (L := L) m hm a)⁻¹ := by
  rw [arithmeticIdealArtinGaloisMap_apply,
    Reciprocity.arithmeticGlobalNormResidueContinuousMulEquiv_apply,
    Reciprocity.globalNormResidueContinuousMulEquiv_apply,
    idealArtinGaloisMap_apply]

/-- Arithmetic normalization leaves the defining ideal group
unchanged. -/
@[simp]
theorem arithmeticIdealArtinGaloisMap_ker
    (m : RayClass.Modulus K)
    (hm :
      RayClass.Modulus.congruenceSubgroup m ≤
        (_root_.ideleClassNorm K L).range) :
    (arithmeticIdealArtinGaloisMap
      (K := K) (L := L) m hm).ker =
      idealArtinKernel m
        ((_root_.ideleClassNorm K L).range) hm := by
  ext a
  let e :=
    Reciprocity.arithmeticGlobalNormResidueContinuousMulEquiv K L
  let x :=
    idealArtinMap m
      ((_root_.ideleClassNorm K L).range) hm a
  change
    e x = 1 ↔ x = 1
  have hOne : e (1 : IdeleClassGroup K) = 1 :=
    e.map_one
  constructor
  · intro h
    exact e.injective (h.trans hOne.symm)
  · intro h
    exact (congrArg e h).trans hOne

/-- The canonical ideal class-field isomorphism in arithmetic
Frobenius normalization. -/
noncomputable def arithmeticIdealClassQuotientEquivGaloisGroup
    (m : RayClass.Modulus K)
    (hm :
      RayClass.Modulus.congruenceSubgroup m ≤
        (_root_.ideleClassNorm K L).range) :
    RayClass.primeToModulusIdeals m ⧸
        idealArtinKernel m
          ((_root_.ideleClassNorm K L).range) hm ≃*
      (L ≃ₐ[K] L) :=
  (idealClassQuotientEquivNormQuotient m
      ((_root_.ideleClassNorm K L).range) hm).trans
    (Reciprocity.arithmeticGlobalNormResidueContinuousMulEquiv
      K L).toMulEquiv

/-- The arithmetic ideal class-field equivalence sends a quotient
representative to its arithmetic ideal Artin symbol. -/
@[simp]
theorem arithmeticIdealClassQuotientEquivGaloisGroup_mk
    (m : RayClass.Modulus K)
    (hm :
      RayClass.Modulus.congruenceSubgroup m ≤
        (_root_.ideleClassNorm K L).range)
    (a : RayClass.primeToModulusIdeals m) :
    arithmeticIdealClassQuotientEquivGaloisGroup
        (K := K) (L := L) m hm
        (QuotientGroup.mk'
          (idealArtinKernel m
            ((_root_.ideleClassNorm K L).range) hm) a) =
      arithmeticIdealArtinGaloisMap
        (K := K) (L := L) m hm a :=
  rfl

end IdealClassFieldTheory
end GlobalClassFieldTheory
end
end


