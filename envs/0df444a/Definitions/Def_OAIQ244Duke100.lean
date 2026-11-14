-- Prove2me | Definitions.Def_OAIQ244Duke100
-- name    : OAIQ244Duke100
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-14T03:08:07.748257+00:00
-- url     : https://prove2.me/theorems/61922dbc-d265-445e-b7f6-58573f664609
-- title:
--   Definitions bundle OAIQ244Duke100 of the split of OpenAI, Equidistribution of Prime-Degree Torus Packets with Arbitrary Local Type
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.DukePrimeDegree.prime_degree_packet_measure_equidistribution_unconditional` and `OAI.DukePrimeDegree.prime_degree_packet_measures_tendsto_haar_unconditional`, carved from OpenAI's openai/math development (OpenAI, *Equidistribution of Prime-Degree Torus Packets with Arbitrary Local Type*, OpenAI Math Release, September 24, 2026, result family 15, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 86 declarations of OpenAI's Lean: 34 definitions, 19 instances and 33 theorems. The definitions and types are `GlobalClassFieldTheory.Reciprocity.abstractFixedFieldCyclotomicFiniteCompositum`, `GlobalClassFieldTheory.Reciprocity.abstractFixedFieldCyclotomicFiniteCompositumBaseEmbedding`, `GlobalClassFieldTheory.Reciprocity.abstractFixedFieldCyclotomicFiniteCompositumEquivFiniteLayer`, `GlobalClassFieldTheory.Reciprocity.abstractFixedFieldCyclotomicFiniteCompositumInclusion`, `GlobalClassFieldTheory.Reciprocity.abstractFixedFieldCyclotomicFiniteCompositumInclusionOverBase`, `GlobalClassFieldTheory.Reciprocity.abstractFixedFieldCyclotomicFiniteCompositumLayerEmbedding`, `GlobalClassFieldTheory.Reciprocity.abstractFixedFieldCyclotomicFiniteGaloisLayer`, `GlobalClassFieldTheory.Reciprocity.abstractFixedFieldCyclotomicFiniteLayer`, `GlobalClassFieldTheory.Reciprocity.abstractFixedFieldCyclotomicFiniteLayerEmbedding`, `GlobalClassFieldTheory.Reciprocity.abstractFixedFieldCyclotomicFiniteLayerInclusion`, `GlobalClassFieldTheory.Reciprocity.abstractFixedFieldCyclotomicRestriction`, `GlobalClassFieldTheory.Reciprocity.cyclotomicAbstractFixedFieldArtinAbstractCoordinate`, `GlobalClassFieldTheory.Reciprocity.cyclotomicAbstractFixedFieldArtinAbstractEndpoint`, `GlobalClassFieldTheory.Reciprocity.cyclotomicAbstractFixedFieldArtinCoordinateAlgebra`, `GlobalClassFieldTheory.Reciprocity.cyclotomicAbstractFixedFieldArtinCoordinateBase`, `GlobalClassFieldTheory.Reciprocity.cyclotomicAbstractFixedFieldArtinCoordinateBaseAlgebra`, `GlobalClassFieldTheory.Reciprocity.cyclotomicAbstractFixedFieldArtinCoordinateBaseSeparableAlgebra`, `GlobalClassFieldTheory.Reciprocity.cyclotomicAbstractFixedFieldArtinCoordinateBridgeData`, `GlobalClassFieldTheory.Reciprocity.cyclotomicAbstractFixedFieldArtinCoordinateLayer`, `GlobalClassFieldTheory.Reciprocity.cyclotomicAbstractFixedFieldArtinCoordinateLayerAlgebra`, `GlobalClassFieldTheory.Reciprocity.cyclotomicAbstractFixedFieldArtinCoordinateLayerBaseAlgebra`, `GlobalClassFieldTheory.Reciprocity.cyclotomicAbstractFixedFieldArtinCoordinateLayerRatAlgebra`, `GlobalClassFieldTheory.Reciprocity.cyclotomicAbstractFixedFieldArtinCoordinateLayerRelativeAlgebra`, `GlobalClassFieldTheory.Reciprocity.cyclotomicAbstractFixedFieldArtinCoordinateLayerSMul`, `GlobalClassFieldTheory.Reciprocity.cyclotomicAbstractFixedFieldArtinCoordinateMap`, `GlobalClassFieldTheory.Reciprocity.cyclotomicAbstractFixedFieldArtinCoordinateMapData`, `GlobalClassFieldTheory.Reciprocity.cyclotomicAbstractFixedFieldArtinCoordinateRelative`, `GlobalClassFieldTheory.Reciprocity.cyclotomicAbstractFixedFieldArtinCoordinateRelativeAlgebra`, `GlobalClassFieldTheory.Reciprocity.cyclotomicAbstractFixedFieldArtinFiniteCoordinate`, `GlobalClassFieldTheory.Reciprocity.cyclotomicAbstractFixedFieldArtinRationalEndpoint`, `GlobalClassFieldTheory.Reciprocity.cyclotomicAbstractFixedFieldArtinRationalEndpointCoordinate`, `GlobalClassFieldTheory.Reciprocity.cyclotomicAbstractFixedFieldArtinRestrictedLayerCoordinate`, `GlobalClassFieldTheory.Reciprocity.numberFieldTowerIdeleClassEquivAmbientFixed`, `GlobalClassFieldTheory.Reciprocity.rationalCyclotomicZHatFieldEmbeddingInAbstractFixedFieldCompositum`.
--
--   **Sources.** They come from these modules of lean/OAI/NumberTheory, in whole or in part: `GlobalClassFieldTheory_Reciprocity_CyclotomicAbstractFixedFieldArtin`, `GlobalClassFieldTheory_Reciprocity_FiniteGaloisRealizationCore`, `GlobalClassFieldTheory_Reciprocity_FiniteGaloisRealizationNormQuotient`.
--
--   **Imports.** It imports the bundles `OAIQ244Duke097` and `OAIQ244Duke098` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ244Duke103` and `OAIQ244Duke120`.
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
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Finsupp
import Mathlib.Data.Finset.Max
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
import Mathlib.NumberTheory.LocalField.Basic
import Mathlib.NumberTheory.NumberField.AdeleRing
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.NumberTheory.NumberField.ClassNumber
import Mathlib.NumberTheory.NumberField.Completion.FinitePlace
import Mathlib.NumberTheory.NumberField.Completion.InfinitePlace
import Mathlib.NumberTheory.NumberField.Completion.LiesOverInstances
import Mathlib.NumberTheory.NumberField.Completion.Ramification
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
import Definitions.Def_OAIQ244Duke097
import Definitions.Def_OAIQ244Duke098

section
-- module Solutions.OAIQ244_DUKE.GlobalClassFieldTheory_Reciprocity_CyclotomicAbstractFixedFieldArtin
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.GlobalClassFields.ConductorialSubgroup.finiteIndex _root_.GlobalClassFieldTheory.GlobalClassFields.bigHilbertClassFieldNormSubgroup_normal _root_.GlobalClassFieldTheory.GlobalClassFields.finiteAbelianSubextensionAbstractRelativeFixedFieldFiniteDimensional _root_.GlobalClassFieldTheory.GlobalClassFields.finiteAbelianSubextensionAbstractRelativeFixedFieldIsAbelianGalois _root_.GlobalClassFieldTheory.GlobalClassFields.ideleClassNorm_rangeFiniteIndex _root_.GlobalClassFieldTheory.GlobalClassFields.smallHilbertClassFieldNormSubgroupFiniteIndex _root_.GlobalClassFieldTheory.Reciprocity.complexFourthRootField_finiteDimensional _root_.GlobalClassFieldTheory.Reciprocity.complexFourthRootField_numberField _root_.GlobalClassFieldTheory.Reciprocity.infinitePlaceComplexificationOverfield_algebra _root_.GlobalClassFieldTheory.Reciprocity.infinitePlaceComplexificationOverfield_baseAlgebra _root_.GlobalClassFieldTheory.Reciprocity.infinitePlaceComplexificationOverfield_baseSmul _root_.GlobalClassFieldTheory.Reciprocity.infinitePlaceComplexificationOverfield_finiteDimensional _root_.GlobalClassFieldTheory.Reciprocity.infinitePlaceComplexificationOverfield_finiteDimensional_over_extension _root_.GlobalClassFieldTheory.Reciprocity.infinitePlaceComplexificationOverfield_numberField _root_.GlobalClassFieldTheory.Reciprocity.infinitePlaceComplexificationOverfield_smul _root_.GlobalClassFieldTheory.Reciprocity.numberFieldTowerBaseFieldAlgebra _root_.GlobalClassFieldTheory.Reciprocity.numberFieldTowerBaseSubgroupAbsoluteQuotientFinite _root_.GlobalClassFieldTheory.Reciprocity.numberFieldTowerExtensionQuotientFinite _root_.GlobalClassFieldTheory.Reciprocity.numberFieldTowerExtensionSubgroupNormal _root_.GlobalClassFieldTheory.Reciprocity.ramifiedInfinitePlaceRealFixedField_algebra _root_.GlobalClassFieldTheory.Reciprocity.ramifiedInfinitePlaceRealFixedField_numberField _root_.GlobalClassFieldTheory.Reciprocity.ramifiedInfinitePlaceRealFixedField_ratScalarTower _root_.KummerTheory.DiscreteNthRootsSubgroup.instTopologicalSpaceSubtypeUnitsMemSubgroup _root_.KummerTheory.primeCyclotomicBaseFiniteDimensional _root_.KummerTheory.primeCyclotomicBaseIsGalois _root_.KummerTheory.primeCyclotomicBaseNumberField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.boundedRealFields_numberField _root_.OAI.PrimeDegreePackets.diagonalLogAction _root_.OAI.PrimeDegreePackets.instTopologicalSpaceLocalAlgebra _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.GlobalClassFieldTheory.GlobalClassFields.bigHilbertNormQuotient_finite _root_.GlobalClassFieldTheory.GlobalClassFields.bigHilbertNormSubgroup_finiteIndex _root_.GlobalClassFieldTheory.Reciprocity.rationalOrdinaryNormQuotientAdditiveTypeAddCommGroup
attribute [-simp] _root_.ClassFormation.FiniteAbelianSubextension.extensionQuotientMk_apply _root_.GlobalClassFieldTheory.ClassFieldAxiom.actualPushoutNormQuotientMap_mk _root_.GlobalClassFieldTheory.ClassFieldAxiom.hasseNormDiagonal_mk _root_.GlobalClassFieldTheory.ClassFieldAxiom.sUnitEquivSupportedPrincipalIdeleSubgroup_coe _root_.GlobalClassFieldTheory.GlobalClassFields.ConductorialSubgroup.ideleClassQuotientEquivOfNarrowFiniteConductorsEqOfRayClassGroupCardsEqQuotientCards_mk _root_.GlobalClassFieldTheory.GlobalClassFields.ConductorialSubgroup.mem_fullConductorInfinitePart_iff _root_.GlobalClassFieldTheory.GlobalClassFields.ConductorialSubgroup.narrowFiniteConductorRayClassGroupEquivQuotientOfCardEq_mk _root_.GlobalClassFieldTheory.GlobalClassFields.ConductorialSubgroup.narrowFiniteConductorRayClassGroupToQuotient_mk _root_.GlobalClassFieldTheory.GlobalClassFields.bigHilbertClassFieldQuotientCongr_mk _root_.GlobalClassFieldTheory.GlobalClassFields.bigHilbertClassFieldQuotientEquivNarrowClassGroup_mk _root_.GlobalClassFieldTheory.GlobalClassFields.bigHilbertClassFieldQuotientToIdeleClassNormQuotient_mk _root_.GlobalClassFieldTheory.GlobalClassFields.bigHilbertClassFieldQuotientToSmallHilbertClassFieldQuotient_mk _root_.GlobalClassFieldTheory.GlobalClassFields.ideleClassNormQuotientTowerMap_mk _root_.GlobalClassFieldTheory.GlobalClassFields.narrowFiniteConductorRayClassGroupToIdeleClassNormQuotient_mk _root_.GlobalClassFieldTheory.GlobalClassFields.normQuotientEquivOfNarrowFiniteConductorsEqOfRayClassGroupCardsEqNormQuotientCards_mk _root_.GlobalClassFieldTheory.GlobalClassFields.realSignToBigHilbertClassFieldQuotient_apply _root_.GlobalClassFieldTheory.GlobalClassFields.realSignToNarrowClassKernel_apply _root_.GlobalClassFieldTheory.GlobalClassFields.smallHilbertClassFieldQuotientCongr_mk _root_.GlobalClassFieldTheory.GlobalClassFields.smallHilbertClassFieldQuotientEquivClassGroup_mk _root_.GlobalClassFieldTheory.GlobalClassFields.smallHilbertClassFieldQuotientToIdeleClassNormQuotient_mk _root_.GlobalClassFieldTheory.IdealClassFieldTheory.smallHilbertClassFieldIdeleExtensionMap_mk' _root_.GlobalClassFieldTheory.Reciprocity.globalNormClassFromIdele_principalIdele _root_.GlobalClassFieldTheory.Reciprocity.globalNormClassFromIdele_relativeIdeleNorm_eq_one _root_.GlobalClassFieldTheory.Reciprocity.mem_globalArtinFiniteSupport_iff _root_.GlobalClassFieldTheory.Reciprocity.numberFieldCyclotomicPadicDecompositionCoordinate_apply _root_.GlobalClassFieldTheory.Reciprocity.numberFieldTowerAbstractFieldEquiv_algebraMap _root_.GlobalClassFieldTheory.Reciprocity.rationalCyclotomicPadicCoordinate_apply _root_.GlobalClassFieldTheory.Reciprocity.rationalFiniteNormQuotientEquivIdeleClassNormQuotient_finiteNormClass _root_.IdeleGroup.count_fractionalIdeal _root_.IdeleGroup.fractionalIdeal_finitePrimeIdele _root_.IdeleGroup.idealClass_finitePrimeIdele _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.OAI.PrimeDegreePackets.ThetaConstruction.schwartzCM_apply _root_.RayClass.signToNarrow_mk
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
# Cyclotomic Artin coordinates over abstract fixed fields

The cyclotomic degree datum on the rational absolute Galois group has
an actual maximal-unramified field over every finite abstract fixed
field.  This file identifies its genuine Galois group with
`Multiplicative ZHat`, using the normalized degree map, and supplies
the abelian Galois structure needed by the actual infinite global
Artin homomorphism.

These constructions are the source side of the comparison between
abstract finite reciprocity and the chosen local-factor product.  No
reciprocity comparison is assumed in their definitions.
-/

open scoped IsMulCommutative NumberField

noncomputable section

namespace GlobalClassFieldTheory
namespace Reciprocity

open ClassFormation
open KummerTheory

attribute [local instance] GlobalClassFieldTheory.Reciprocity.cyclotomicAbstractFixedFieldArtin_separableClosureAlgebra
attribute [local instance] GlobalClassFieldTheory.Reciprocity.cyclotomicAbstractFixedFieldArtin_cyclotomicZHatFieldAlgebra
/-- Quotient-level evaluation of the actual cyclotomic Galois
coordinate. -/
@[simp]
theorem abstractFixedFieldCyclotomicGalEquivZHat_quotientClass
    (H : FiniteAbstractField
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
    (q :
      H.field.toSubgroup ⧸
        rationalCyclotomicDegreeData.fieldInertiaWithin H.field) :
    let hI :=
      rationalCyclotomicFieldInertia_le H.field
    let hnormal :
        (CyclicCohomology.extensionSubgroup H.field
          (rationalCyclotomicDegreeData.fieldInertia H.field)
          hI).Normal := by
      rw [extensionSubgroup_rationalCyclotomicFieldInertia]
      infer_instance
    let qInertia :
        H.field.toSubgroup ⧸
            CyclicCohomology.extensionSubgroup H.field
              (rationalCyclotomicDegreeData.fieldInertia H.field)
              hI ≃*
          H.field.toSubgroup ⧸
            rationalCyclotomicDegreeData.fieldInertiaWithin H.field :=
      QuotientGroup.quotientMulEquivOfEq
        (extensionSubgroup_rationalCyclotomicFieldInertia H.field)
    abstractFixedFieldCyclotomicGalEquivZHat H
        (LocalClassFieldTheory.abstractExtensionQuotientEquivGaloisGroup
          ℚ (SeparableClosure ℚ) H.field
          (rationalCyclotomicDegreeData.fieldInertia H.field)
          hI hnormal
          (qInertia.symm q)) =
      rationalCyclotomicDegreeData.maximalUnramifiedDegreeEquiv
        (H.toFiniteResidueAbstractField
          rationalCyclotomicDegreeData) q := by
  let hI :=
    rationalCyclotomicFieldInertia_le H.field
  let hnormal :
      (CyclicCohomology.extensionSubgroup H.field
        (rationalCyclotomicDegreeData.fieldInertia H.field)
        hI).Normal := by
    rw [extensionSubgroup_rationalCyclotomicFieldInertia]
    infer_instance
  let qField :=
    LocalClassFieldTheory.abstractExtensionQuotientEquivGaloisGroup
      ℚ (SeparableClosure ℚ) H.field
      (rationalCyclotomicDegreeData.fieldInertia H.field)
      hI hnormal
  let qInertia :
      H.field.toSubgroup ⧸
          CyclicCohomology.extensionSubgroup H.field
            (rationalCyclotomicDegreeData.fieldInertia H.field)
            hI ≃*
        H.field.toSubgroup ⧸
          rationalCyclotomicDegreeData.fieldInertiaWithin H.field :=
    QuotientGroup.quotientMulEquivOfEq
      (extensionSubgroup_rationalCyclotomicFieldInertia H.field)
  change
    (rationalCyclotomicDegreeData.maximalUnramifiedDegreeEquiv
      (H.toFiniteResidueAbstractField
        rationalCyclotomicDegreeData))
      (qInertia
        (qField.symm
          (qField (qInertia.symm q)))) =
      rationalCyclotomicDegreeData.maximalUnramifiedDegreeEquiv
        (H.toFiniteResidueAbstractField
          rationalCyclotomicDegreeData) q
  rw [qField.symm_apply_apply, qInertia.apply_symm_apply]

/-- The extension fixed by cyclotomic field inertia is an actual
abelian Galois extension of the lower abstract fixed field. -/
theorem abstractFixedFieldCyclotomic_isAbelianGalois
    (H : FiniteAbstractField
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ)) :
    let hI :=
      rationalCyclotomicFieldInertia_le H.field
    IsAbelianGalois
      (LocalClassFieldTheory.abstractFixedField
        ℚ (SeparableClosure ℚ) H.field)
      (LocalClassFieldTheory.abstractRelativeFixedField
        ℚ (SeparableClosure ℚ) hI) := by
  let hI :=
    rationalCyclotomicFieldInertia_le H.field
  let hnormal :
      (CyclicCohomology.extensionSubgroup H.field
        (rationalCyclotomicDegreeData.fieldInertia H.field)
        hI).Normal := by
    rw [extensionSubgroup_rationalCyclotomicFieldInertia]
    infer_instance
  let : IsGalois
      (LocalClassFieldTheory.abstractFixedField
        ℚ (SeparableClosure ℚ) H.field)
      (LocalClassFieldTheory.abstractRelativeFixedField
        ℚ (SeparableClosure ℚ) hI) :=
    LocalClassFieldTheory.abstractRelativeFixedField_isGalois
      ℚ (SeparableClosure ℚ) H.field
      (rationalCyclotomicDegreeData.fieldInertia H.field)
      hI hnormal
  let e :=
    abstractFixedFieldCyclotomicGalEquivZHat H
  exact
    { is_comm.comm := by
        intro σ τ
        apply e.injective
        simpa only [map_mul] using mul_comm (e σ) (e τ) }

/-- The rational cyclotomic `ZHat`-field embedded in the actual
maximal-unramified compositum of an abstract fixed field. -/
noncomputable def
    rationalCyclotomicZHatFieldEmbeddingInAbstractFixedFieldCompositum
    (H : FiniteAbstractField
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ)) :
    let hI :=
      rationalCyclotomicFieldInertia_le H.field
    rationalCyclotomicZHatField →ₐ[ℚ]
      LocalClassFieldTheory.abstractRelativeFixedField
        ℚ (SeparableClosure ℚ) hI := by
  let hI :=
    rationalCyclotomicFieldInertia_le H.field
  let J :=
    LocalClassFieldTheory.abstractFixedField
      ℚ (SeparableClosure ℚ)
      (rationalCyclotomicDegreeData.fieldInertia H.field)
  have hTJ :
      rationalCyclotomicZHatField ≤ J := by
    change
      rationalCyclotomicZHatField ≤
        LocalClassFieldTheory.abstractFixedField
          ℚ (SeparableClosure ℚ)
          (rationalCyclotomicDegreeData.fieldInertia H.field)
    rw [
      rationalCyclotomicDegreeData_fixedField_fieldInertia]
    exact le_sup_right
  exact IntermediateField.inclusion hTJ

noncomputable instance
    abstractFixedFieldCyclotomicCompositum_algebra
    (H : FiniteAbstractField
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ)) :
    let hI :=
      rationalCyclotomicFieldInertia_le H.field
    Algebra rationalCyclotomicZHatField
      (LocalClassFieldTheory.abstractRelativeFixedField
        ℚ (SeparableClosure ℚ) hI) :=
  ((rationalCyclotomicZHatFieldEmbeddingInAbstractFixedFieldCompositum
    H).toRingHom).toAlgebra

instance abstractFixedFieldCyclotomicCompositum_scalarTower
    (H : FiniteAbstractField
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ)) :
    let hI :=
      rationalCyclotomicFieldInertia_le H.field
    IsScalarTower ℚ rationalCyclotomicZHatField
      (LocalClassFieldTheory.abstractRelativeFixedField
        ℚ (SeparableClosure ℚ) hI) :=
  IsScalarTower.of_algebraMap_eq'
    ((rationalCyclotomicZHatFieldEmbeddingInAbstractFixedFieldCompositum
      H).comp_algebraMap).symm

instance abstractFixedFieldCyclotomicCompositum_baseScalarTower
    (H : FiniteAbstractField
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ)) :
    let hI :=
      rationalCyclotomicFieldInertia_le H.field
    IsScalarTower ℚ
      (LocalClassFieldTheory.abstractFixedField
        ℚ (SeparableClosure ℚ) H.field)
      (LocalClassFieldTheory.abstractRelativeFixedField
        ℚ (SeparableClosure ℚ) hI) := by
  let hI :=
    rationalCyclotomicFieldInertia_le H.field
  apply IsScalarTower.of_algebraMap_eq
  intro x
  apply Subtype.ext
  rfl

/-- Restriction from the actual maximal-unramified compositum of an
abstract fixed field to the rational cyclotomic factor. -/
noncomputable def abstractFixedFieldCyclotomicRestriction
    (H : FiniteAbstractField
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ)) :
    let hI :=
      rationalCyclotomicFieldInertia_le H.field
    Gal(
        LocalClassFieldTheory.abstractRelativeFixedField
          ℚ (SeparableClosure ℚ) hI /
        LocalClassFieldTheory.abstractFixedField
          ℚ (SeparableClosure ℚ) H.field) →*
      Gal(rationalCyclotomicZHatField / ℚ) := by
  let hI :=
    rationalCyclotomicFieldInertia_le H.field
  exact
    IntermediateField.restrictRestrictAlgEquivMapHom
      ℚ rationalCyclotomicZHatField
      (LocalClassFieldTheory.abstractFixedField
        ℚ (SeparableClosure ℚ) H.field)
      (LocalClassFieldTheory.abstractRelativeFixedField
        ℚ (SeparableClosure ℚ) hI)

attribute [local instance] GlobalClassFieldTheory.Reciprocity.cyclotomicAbstractFixedFieldArtin_cyclotomicZHatFieldNormal
@[simp]
theorem abstractFixedFieldCyclotomicRestriction_extensionClass
    (H : FiniteAbstractField
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
    (σ : H.field.toSubgroup) :
    let hI :=
      rationalCyclotomicFieldInertia_le H.field
    let hnormal :
        (CyclicCohomology.extensionSubgroup H.field
          (rationalCyclotomicDegreeData.fieldInertia H.field)
          hI).Normal := by
      rw [extensionSubgroup_rationalCyclotomicFieldInertia]
      infer_instance
    abstractFixedFieldCyclotomicRestriction H
        (LocalClassFieldTheory.abstractExtensionQuotientEquivGaloisGroup
          ℚ (SeparableClosure ℚ) H.field
          (rationalCyclotomicDegreeData.fieldInertia H.field)
          hI hnormal
          (QuotientGroup.mk σ)) =
      AlgEquiv.restrictNormalHom
        rationalCyclotomicZHatField σ.1 := by
  let hI :=
    rationalCyclotomicFieldInertia_le H.field
  let hnormal :
      (CyclicCohomology.extensionSubgroup H.field
        (rationalCyclotomicDegreeData.fieldInertia H.field)
        hI).Normal := by
    rw [extensionSubgroup_rationalCyclotomicFieldInertia]
    infer_instance
  let τ :=
    LocalClassFieldTheory.abstractExtensionQuotientEquivGaloisGroup
      ℚ (SeparableClosure ℚ) H.field
      (rationalCyclotomicDegreeData.fieldInertia H.field)
      hI hnormal
      (QuotientGroup.mk'
        (CyclicCohomology.extensionSubgroup H.field
          (rationalCyclotomicDegreeData.fieldInertia H.field) hI)
        σ)
  apply AlgEquiv.ext
  intro x
  apply Subtype.ext
  let U :=
    LocalClassFieldTheory.abstractRelativeFixedField
      ℚ (SeparableClosure ℚ) hI
  have hrestrict :
      algebraMap rationalCyclotomicZHatField U
          ((abstractFixedFieldCyclotomicRestriction H τ) x) =
        τ (algebraMap rationalCyclotomicZHatField U x) := by
    change
      algebraMap rationalCyclotomicZHatField U
          ((AlgEquiv.restrictNormal
            (MulSemiringAction.toAlgEquiv ℚ U τ)
            rationalCyclotomicZHatField) x) =
        (MulSemiringAction.toAlgEquiv ℚ U τ)
          (algebraMap rationalCyclotomicZHatField U x)
    exact
      AlgEquiv.restrictNormal_commutes
        (MulSemiringAction.toAlgEquiv ℚ U τ)
        rationalCyclotomicZHatField x
  have halgebraMap_eq_embedding
      (z : rationalCyclotomicZHatField) :
      algebraMap rationalCyclotomicZHatField U z =
        (rationalCyclotomicZHatFieldEmbeddingInAbstractFixedFieldCompositum
          H z : U) := by
    rfl
  have hembedding_coe
      (z : rationalCyclotomicZHatField) :
      (((rationalCyclotomicZHatFieldEmbeddingInAbstractFixedFieldCompositum
          H z : U) : SeparableClosure ℚ)) =
        (z : SeparableClosure ℚ) := by
    rfl
  have halgebraMap_coe
      (z : rationalCyclotomicZHatField) :
      ((algebraMap rationalCyclotomicZHatField U z : U) :
          SeparableClosure ℚ) =
        (z : SeparableClosure ℚ) := by
    rw [halgebraMap_eq_embedding]
    exact hembedding_coe z
  have hambient :=
    LocalClassFieldTheory.abstractExtensionQuotientEquivGaloisGroup_mk_apply_val
        ℚ (SeparableClosure ℚ) H.field
        (rationalCyclotomicDegreeData.fieldInertia H.field)
        hI hnormal σ
        (rationalCyclotomicZHatFieldEmbeddingInAbstractFixedFieldCompositum
          H x)
  calc
    (((abstractFixedFieldCyclotomicRestriction H τ) x :
        rationalCyclotomicZHatField) :
        SeparableClosure ℚ) =
        ((τ
          (rationalCyclotomicZHatFieldEmbeddingInAbstractFixedFieldCompositum
            H x) :
          LocalClassFieldTheory.abstractRelativeFixedField
            ℚ (SeparableClosure ℚ) hI) :
          SeparableClosure ℚ) := by
      calc
        (((abstractFixedFieldCyclotomicRestriction H τ) x :
            rationalCyclotomicZHatField) : SeparableClosure ℚ) =
            ((algebraMap rationalCyclotomicZHatField U
              ((abstractFixedFieldCyclotomicRestriction H τ) x) : U) :
              SeparableClosure ℚ) :=
          (halgebraMap_coe
            ((abstractFixedFieldCyclotomicRestriction H τ) x)).symm
        _ = ((τ (algebraMap rationalCyclotomicZHatField U x) : U) :
            SeparableClosure ℚ) :=
          congrArg (fun y : U => (y : SeparableClosure ℚ)) hrestrict
        _ = ((τ
            (rationalCyclotomicZHatFieldEmbeddingInAbstractFixedFieldCompositum
              H x) : U) : SeparableClosure ℚ) := by
          rw [halgebraMap_eq_embedding]
    _ = σ.1 (x : SeparableClosure ℚ) := by
      calc
        ((τ
            (rationalCyclotomicZHatFieldEmbeddingInAbstractFixedFieldCompositum
              H x) : U) : SeparableClosure ℚ) =
            σ.1
              ((rationalCyclotomicZHatFieldEmbeddingInAbstractFixedFieldCompositum
                H x : U) : SeparableClosure ℚ) := by
          simpa only [τ, U] using hambient.symm
        _ = σ.1 (x : SeparableClosure ℚ) := by
          rw [hembedding_coe]
    _ =
        (((AlgEquiv.restrictNormalHom
          rationalCyclotomicZHatField σ.1) x :
          rationalCyclotomicZHatField) :
          SeparableClosure ℚ) := by
      exact
        (AlgEquiv.restrictNormal_commutes
          σ.1 rationalCyclotomicZHatField x).symm

/-- Raw cyclotomic restriction is residue-degree multiplication of
the normalized actual Galois coordinate. -/
theorem
    abstractFixedFieldCyclotomicRestriction_coordinate
    (H : FiniteAbstractField
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
    (τ :
      Gal(
        LocalClassFieldTheory.abstractRelativeFixedField
          ℚ (SeparableClosure ℚ)
          (rationalCyclotomicFieldInertia_le H.field) /
        LocalClassFieldTheory.abstractFixedField
          ℚ (SeparableClosure ℚ) H.field)) :
    Multiplicative.toAdd
        (rationalCyclotomicZHatFieldGalEquivZHat
          (abstractFixedFieldCyclotomicRestriction H τ)) =
      (H.residueDegree rationalCyclotomicDegreeData : ℕ) •
        Multiplicative.toAdd
          (abstractFixedFieldCyclotomicGalEquivZHat H τ) := by
  let hI :=
    rationalCyclotomicFieldInertia_le H.field
  let hnormal :
      (CyclicCohomology.extensionSubgroup H.field
        (rationalCyclotomicDegreeData.fieldInertia H.field)
        hI).Normal := by
    rw [extensionSubgroup_rationalCyclotomicFieldInertia]
    infer_instance
  let qField :=
    LocalClassFieldTheory.abstractExtensionQuotientEquivGaloisGroup
      ℚ (SeparableClosure ℚ) H.field
      (rationalCyclotomicDegreeData.fieldInertia H.field)
      hI hnormal
  obtain ⟨q, rfl⟩ := qField.surjective τ
  refine Quotient.inductionOn' q ?_
  intro σ
  rw [
    abstractFixedFieldCyclotomicRestriction_extensionClass,
    abstractFixedFieldCyclotomicGalEquivZHat_extensionClass]
  exact
    (rationalCyclotomicDegreeData.residueDegree_nsmul_normalizedDegree
        (H.toFiniteResidueAbstractField
          rationalCyclotomicDegreeData) σ).symm

/-- The canonical compositum of an abstract fixed field with a finite
layer of the rational cyclotomic `ZHat`-extension. -/
def abstractFixedFieldCyclotomicFiniteCompositum
    (H : FiniteAbstractField
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
    (E :
      FiniteGaloisIntermediateField
        ℚ rationalCyclotomicZHatField) :
    IntermediateField ℚ (SeparableClosure ℚ) :=
  LocalClassFieldTheory.abstractFixedField
      ℚ (SeparableClosure ℚ) H.field ⊔
    IntermediateField.lift E.toIntermediateField

noncomputable instance
    abstractFixedFieldCyclotomicFiniteCompositum_finiteDimensional
    (H : FiniteAbstractField
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
    (E :
      FiniteGaloisIntermediateField
        ℚ rationalCyclotomicZHatField) :
    FiniteDimensional ℚ
      (abstractFixedFieldCyclotomicFiniteCompositum H E) := by
  let F :=
    LocalClassFieldTheory.abstractFixedField
      ℚ (SeparableClosure ℚ) H.field
  let : FiniteDimensional ℚ F :=
    LocalClassFieldTheory.abstractFixedField_finiteDimensional
      ℚ (SeparableClosure ℚ) H.field H.finite
  let : FiniteDimensional ℚ
      (IntermediateField.lift E.toIntermediateField) :=
    ((IntermediateField.liftAlgEquiv
      E.toIntermediateField).toLinearEquiv).finiteDimensional
  exact IntermediateField.finiteDimensional_sup
    F (IntermediateField.lift E.toIntermediateField)

noncomputable instance
    abstractFixedFieldCyclotomicFiniteCompositum_numberField
    (H : FiniteAbstractField
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
    (E :
      FiniteGaloisIntermediateField
        ℚ rationalCyclotomicZHatField) :
    NumberField
      (abstractFixedFieldCyclotomicFiniteCompositum H E) :=
  NumberField.of_module_finite ℚ
    (abstractFixedFieldCyclotomicFiniteCompositum H E)

/-- The lower abstract fixed field embedded into its finite
cyclotomic compositum. -/
noncomputable def
    abstractFixedFieldCyclotomicFiniteCompositumBaseEmbedding
    (H : FiniteAbstractField
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
    (E :
      FiniteGaloisIntermediateField
        ℚ rationalCyclotomicZHatField) :
    LocalClassFieldTheory.abstractFixedField
        ℚ (SeparableClosure ℚ) H.field →ₐ[ℚ]
      abstractFixedFieldCyclotomicFiniteCompositum H E :=
  IntermediateField.inclusion
    (show
      LocalClassFieldTheory.abstractFixedField
          ℚ (SeparableClosure ℚ) H.field ≤
        abstractFixedFieldCyclotomicFiniteCompositum H E from
      le_sup_left)

/-- The fixed field attached to a finite abstract field is a number
field.  Keeping this as the single file-local instance makes it
available while later theorem binders are elaborated. -/
noncomputable local instance
    abstractFixedFieldCyclotomic_numberField
    (H : FiniteAbstractField
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ)) :
    NumberField
      (LocalClassFieldTheory.abstractFixedField
        ℚ (SeparableClosure ℚ) H.field) := by
  let : FiniteDimensional ℚ
      (LocalClassFieldTheory.abstractFixedField
        ℚ (SeparableClosure ℚ) H.field) :=
    LocalClassFieldTheory.abstractFixedField_finiteDimensional
      ℚ (SeparableClosure ℚ) H.field H.finite
  exact
    NumberField.of_module_finite ℚ
      (LocalClassFieldTheory.abstractFixedField
        ℚ (SeparableClosure ℚ) H.field)

/-- A finite rational cyclotomic layer embedded into its compositum
with the abstract fixed field. -/
noncomputable def
    abstractFixedFieldCyclotomicFiniteCompositumLayerEmbedding
    (H : FiniteAbstractField
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
    (E :
      FiniteGaloisIntermediateField
        ℚ rationalCyclotomicZHatField) :
    E →ₐ[ℚ]
      abstractFixedFieldCyclotomicFiniteCompositum H E :=
  (IntermediateField.inclusion
      (show
        IntermediateField.lift E.toIntermediateField ≤
          abstractFixedFieldCyclotomicFiniteCompositum H E from
        le_sup_right)).comp
    (IntermediateField.liftAlgEquiv E.toIntermediateField).toAlgHom

noncomputable instance
    abstractFixedFieldCyclotomicFiniteCompositum_baseAlgebra
    (H : FiniteAbstractField
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
    (E :
      FiniteGaloisIntermediateField
        ℚ rationalCyclotomicZHatField) :
    Algebra
      (LocalClassFieldTheory.abstractFixedField
        ℚ (SeparableClosure ℚ) H.field)
      (abstractFixedFieldCyclotomicFiniteCompositum H E) :=
  RingHom.toAlgebra
    (AlgHom.toRingHom
      (abstractFixedFieldCyclotomicFiniteCompositumBaseEmbedding H E))

instance
    abstractFixedFieldCyclotomicFiniteCompositum_baseScalarTower
    (H : FiniteAbstractField
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
    (E :
      FiniteGaloisIntermediateField
        ℚ rationalCyclotomicZHatField) :
    IsScalarTower ℚ
      (LocalClassFieldTheory.abstractFixedField
        ℚ (SeparableClosure ℚ) H.field)
      (abstractFixedFieldCyclotomicFiniteCompositum H E) :=
  IsScalarTower.of_algebraMap_eq'
    (AlgHom.comp_algebraMap
      (abstractFixedFieldCyclotomicFiniteCompositumBaseEmbedding H E)).symm

/-- Inclusion of the finite cyclotomic compositum into the actual
maximal-unramified compositum. -/
noncomputable def
    abstractFixedFieldCyclotomicFiniteCompositumInclusion
    (H : FiniteAbstractField
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
    (E :
      FiniteGaloisIntermediateField
        ℚ rationalCyclotomicZHatField) :
    let hI :=
      rationalCyclotomicFieldInertia_le H.field
    abstractFixedFieldCyclotomicFiniteCompositum H E →ₐ[ℚ]
      LocalClassFieldTheory.abstractRelativeFixedField
        ℚ (SeparableClosure ℚ) hI := by
  let hI :=
    rationalCyclotomicFieldInertia_le H.field
  let J :=
    LocalClassFieldTheory.abstractFixedField
      ℚ (SeparableClosure ℚ)
      (rationalCyclotomicDegreeData.fieldInertia H.field)
  have hle :
      abstractFixedFieldCyclotomicFiniteCompositum H E ≤ J := by
    dsimp only [J]
    rw [
      rationalCyclotomicDegreeData_fixedField_fieldInertia H.field]
    exact
      sup_le_sup le_rfl
        (IntermediateField.lift_le E.toIntermediateField)
  exact IntermediateField.inclusion hle

/-- The same finite-compositum inclusion over the lower abstract fixed
field. -/
noncomputable def
    abstractFixedFieldCyclotomicFiniteCompositumInclusionOverBase
    (H : FiniteAbstractField
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
    (E :
      FiniteGaloisIntermediateField
        ℚ rationalCyclotomicZHatField) :
    let hI :=
      rationalCyclotomicFieldInertia_le H.field
    abstractFixedFieldCyclotomicFiniteCompositum H E →ₐ[
      LocalClassFieldTheory.abstractFixedField
        ℚ (SeparableClosure ℚ) H.field]
      LocalClassFieldTheory.abstractRelativeFixedField
        ℚ (SeparableClosure ℚ) hI := by
  let f :=
    abstractFixedFieldCyclotomicFiniteCompositumInclusion H E
  exact
    { f.toRingHom with
      commutes' := by
        intro x
        rfl }

/-- The finite cyclotomic compositum as an intermediate field of the
actual maximal-unramified extension. -/
noncomputable def abstractFixedFieldCyclotomicFiniteLayer
    (H : FiniteAbstractField
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
    (E :
      FiniteGaloisIntermediateField
        ℚ rationalCyclotomicZHatField) :
    let hI :=
      rationalCyclotomicFieldInertia_le H.field
    IntermediateField
      (LocalClassFieldTheory.abstractFixedField
        ℚ (SeparableClosure ℚ) H.field)
      (LocalClassFieldTheory.abstractRelativeFixedField
        ℚ (SeparableClosure ℚ) hI) :=
  (abstractFixedFieldCyclotomicFiniteCompositumInclusionOverBase H E).fieldRange

/-- The base algebra on the finite field range, obtained from the
explicit base embedding followed by the field-range equivalence. -/
noncomputable instance
    abstractFixedFieldCyclotomicFiniteLayer_baseAlgebra
    (H : FiniteAbstractField
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
    (E :
      FiniteGaloisIntermediateField
        ℚ rationalCyclotomicZHatField) :
    Algebra
      (LocalClassFieldTheory.abstractFixedField
        ℚ (SeparableClosure ℚ) H.field)
      (abstractFixedFieldCyclotomicFiniteLayer H E) :=
  RingHom.toAlgebra
    ((AlgHom.toRingHom
      (AlgEquiv.toAlgHom
        (AlgHom.equivFieldRange
          (abstractFixedFieldCyclotomicFiniteCompositumInclusionOverBase
            H E)))).comp
      (AlgHom.toRingHom
        (abstractFixedFieldCyclotomicFiniteCompositumBaseEmbedding H E)))

/-- The scalar action belonging to the canonical base algebra on the
finite field range. -/
noncomputable instance
    abstractFixedFieldCyclotomicFiniteLayer_baseSMul
    (H : FiniteAbstractField
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
    (E :
      FiniteGaloisIntermediateField
        ℚ rationalCyclotomicZHatField) :
    SMul
      (LocalClassFieldTheory.abstractFixedField
        ℚ (SeparableClosure ℚ) H.field)
      (abstractFixedFieldCyclotomicFiniteLayer H E) :=
  Algebra.toSMul
    (self := abstractFixedFieldCyclotomicFiniteLayer_baseAlgebra H E)

/-- The module structure belonging to the canonical base algebra on
the finite field range. -/
noncomputable instance
    abstractFixedFieldCyclotomicFiniteLayer_baseModule
    (H : FiniteAbstractField
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
    (E :
      FiniteGaloisIntermediateField
        ℚ rationalCyclotomicZHatField) :
    Module
      (LocalClassFieldTheory.abstractFixedField
        ℚ (SeparableClosure ℚ) H.field)
      (abstractFixedFieldCyclotomicFiniteLayer H E) :=
  @Algebra.toModule
    (LocalClassFieldTheory.abstractFixedField
      ℚ (SeparableClosure ℚ) H.field)
    (abstractFixedFieldCyclotomicFiniteLayer H E)
    _ _
    (abstractFixedFieldCyclotomicFiniteLayer_baseAlgebra H E)

/-- The field-range equivalence rebuilt over the explicit base
algebras.  Its underlying ring equivalence is the canonical one. -/
noncomputable def
    abstractFixedFieldCyclotomicFiniteCompositumEquivFiniteLayer
    (H : FiniteAbstractField
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
    (E :
      FiniteGaloisIntermediateField
        ℚ rationalCyclotomicZHatField) :
    abstractFixedFieldCyclotomicFiniteCompositum H E ≃ₐ[
      LocalClassFieldTheory.abstractFixedField
        ℚ (SeparableClosure ℚ) H.field]
      abstractFixedFieldCyclotomicFiniteLayer H E :=
  AlgEquiv.ofRingEquiv
    (f :=
      (AlgHom.equivFieldRange
        (abstractFixedFieldCyclotomicFiniteCompositumInclusionOverBase
          H E)).toRingEquiv)
    (fun _ => rfl)

noncomputable instance
    abstractFixedFieldCyclotomicFiniteLayer_finiteDimensional
    (H : FiniteAbstractField
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
    (E :
      FiniteGaloisIntermediateField
        ℚ rationalCyclotomicZHatField) :
    FiniteDimensional
      (LocalClassFieldTheory.abstractFixedField
        ℚ (SeparableClosure ℚ) H.field)
      (abstractFixedFieldCyclotomicFiniteLayer H E) :=
  (abstractFixedFieldCyclotomicFiniteCompositumEquivFiniteLayer
    H E).toLinearEquiv.finiteDimensional

noncomputable instance
    abstractFixedFieldCyclotomicFiniteLayer_numberField
    (H : FiniteAbstractField
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
    (E :
      FiniteGaloisIntermediateField
        ℚ rationalCyclotomicZHatField) :
    NumberField
      (abstractFixedFieldCyclotomicFiniteLayer H E) :=
  NumberField.of_module_finite
    (LocalClassFieldTheory.abstractFixedField
      ℚ (SeparableClosure ℚ) H.field)
    (abstractFixedFieldCyclotomicFiniteLayer H E)

noncomputable instance
    abstractFixedFieldCyclotomicFiniteLayer_isAbelianGalois
    (H : FiniteAbstractField
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
    (E :
      FiniteGaloisIntermediateField
        ℚ rationalCyclotomicZHatField) :
    IsAbelianGalois
      (LocalClassFieldTheory.abstractFixedField
        ℚ (SeparableClosure ℚ) H.field)
      (abstractFixedFieldCyclotomicFiniteLayer H E) := by
  let hI :=
    rationalCyclotomicFieldInertia_le H.field
  let : IsAbelianGalois
      (LocalClassFieldTheory.abstractFixedField
        ℚ (SeparableClosure ℚ) H.field)
      (LocalClassFieldTheory.abstractRelativeFixedField
        ℚ (SeparableClosure ℚ) hI) :=
    abstractFixedFieldCyclotomic_isAbelianGalois H
  exact
    IsAbelianGalois.of_algHom
      ((abstractFixedFieldCyclotomicFiniteCompositumInclusionOverBase
          H E).comp
        (AlgEquiv.toAlgHom
          (AlgEquiv.symm
            (abstractFixedFieldCyclotomicFiniteCompositumEquivFiniteLayer
              H E))))

instance
    abstractFixedFieldCyclotomicFiniteLayer_baseScalarTower
    (H : FiniteAbstractField
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
    (E :
      FiniteGaloisIntermediateField
        ℚ rationalCyclotomicZHatField) :
    IsScalarTower ℚ
      (LocalClassFieldTheory.abstractFixedField
        ℚ (SeparableClosure ℚ) H.field)
      (abstractFixedFieldCyclotomicFiniteLayer H E) := by
  let hI :=
    rationalCyclotomicFieldInertia_le H.field
  apply IsScalarTower.of_algebraMap_eq
  intro x
  apply Subtype.ext
  change
    algebraMap ℚ
        (LocalClassFieldTheory.abstractRelativeFixedField
          ℚ (SeparableClosure ℚ) hI) x =
      algebraMap
        (LocalClassFieldTheory.abstractFixedField
          ℚ (SeparableClosure ℚ) H.field)
        (LocalClassFieldTheory.abstractRelativeFixedField
          ℚ (SeparableClosure ℚ) hI)
        (algebraMap ℚ
          (LocalClassFieldTheory.abstractFixedField
            ℚ (SeparableClosure ℚ) H.field) x)
  exact
    IsScalarTower.algebraMap_apply
      ℚ
      (LocalClassFieldTheory.abstractFixedField
        ℚ (SeparableClosure ℚ) H.field)
      (LocalClassFieldTheory.abstractRelativeFixedField
        ℚ (SeparableClosure ℚ) hI) x

/-- The finite rational layer embedded into its corresponding
intermediate field over the abstract fixed field. -/
noncomputable def
    abstractFixedFieldCyclotomicFiniteLayerEmbedding
    (H : FiniteAbstractField
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
    (E :
      FiniteGaloisIntermediateField
        ℚ rationalCyclotomicZHatField) :
    E →ₐ[ℚ]
      abstractFixedFieldCyclotomicFiniteLayer H E := by
  exact
    (AlgEquiv.toAlgHom
      (AlgEquiv.restrictScalars ℚ
        (abstractFixedFieldCyclotomicFiniteCompositumEquivFiniteLayer
          H E))).comp
      (abstractFixedFieldCyclotomicFiniteCompositumLayerEmbedding H E)

noncomputable instance
    abstractFixedFieldCyclotomicFiniteLayer_layerAlgebra
    (H : FiniteAbstractField
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
    (E :
      FiniteGaloisIntermediateField
        ℚ rationalCyclotomicZHatField) :
    Algebra E
      (abstractFixedFieldCyclotomicFiniteLayer H E) :=
  RingHom.toAlgebra
    (AlgHom.toRingHom
      (abstractFixedFieldCyclotomicFiniteLayerEmbedding H E))

/-- The finite-layer action on its actual image in the relative fixed
field. -/
noncomputable instance
    abstractFixedFieldCyclotomicFiniteLayer_layerSMul
    (H : FiniteAbstractField
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
    (E :
      FiniteGaloisIntermediateField
        ℚ rationalCyclotomicZHatField) :
    SMul E
      (abstractFixedFieldCyclotomicFiniteLayer H E) :=
  Algebra.toSMul
    (self := abstractFixedFieldCyclotomicFiniteLayer_layerAlgebra H E)

instance
    abstractFixedFieldCyclotomicFiniteLayer_layerScalarTower
    (H : FiniteAbstractField
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
    (E :
      FiniteGaloisIntermediateField
        ℚ rationalCyclotomicZHatField) :
    IsScalarTower ℚ E
      (abstractFixedFieldCyclotomicFiniteLayer H E) :=
  IsScalarTower.of_algebraMap_eq'
    (AlgHom.comp_algebraMap
      (abstractFixedFieldCyclotomicFiniteLayerEmbedding H E)).symm

/-- The finite cyclotomic layer as an object of the finite-Galois
inverse system of the actual maximal-unramified extension. -/
@[reducible]
noncomputable def
    abstractFixedFieldCyclotomicFiniteGaloisLayer
    (H : FiniteAbstractField
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
    (E :
      FiniteGaloisIntermediateField
        ℚ rationalCyclotomicZHatField) :
    FiniteGaloisIntermediateField
      (LocalClassFieldTheory.abstractFixedField
        ℚ (SeparableClosure ℚ) H.field)
      (LocalClassFieldTheory.abstractRelativeFixedField
        ℚ (SeparableClosure ℚ)
        (rationalCyclotomicFieldInertia_le H.field)) where
  toIntermediateField :=
    abstractFixedFieldCyclotomicFiniteLayer H E
  finiteDimensional :=
    abstractFixedFieldCyclotomicFiniteLayer_finiteDimensional H E
  isGalois :=
    (abstractFixedFieldCyclotomicFiniteLayer_isAbelianGalois H E).toIsGalois

/-- The finite Galois layer uses its canonical inclusion into the full
relative fixed field for the upper scalar action. -/
instance
    abstractFixedFieldCyclotomicFiniteGaloisLayer_scalarTower
    (H : FiniteAbstractField
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
    (E :
      FiniteGaloisIntermediateField
        ℚ rationalCyclotomicZHatField) :
    IsScalarTower
      (LocalClassFieldTheory.abstractFixedField
        ℚ (SeparableClosure ℚ) H.field)
      (abstractFixedFieldCyclotomicFiniteGaloisLayer H E).toIntermediateField
      (LocalClassFieldTheory.abstractRelativeFixedField
        ℚ (SeparableClosure ℚ)
        (rationalCyclotomicFieldInertia_le H.field)) := by
  let i :
      (abstractFixedFieldCyclotomicFiniteGaloisLayer
          H E).toIntermediateField →ₐ[
        LocalClassFieldTheory.abstractFixedField
          ℚ (SeparableClosure ℚ) H.field]
        LocalClassFieldTheory.abstractRelativeFixedField
          ℚ (SeparableClosure ℚ)
          (rationalCyclotomicFieldInertia_le H.field) :=
    { (abstractFixedFieldCyclotomicFiniteGaloisLayer
          H E).toIntermediateField.val.toRingHom with
      commutes' := by
        intro x
        rfl }
  exact
    IsScalarTower.of_algebraMap_eq'
      (AlgHom.comp_algebraMap i).symm

/-- The canonical inclusion of the finite cyclotomic layer into the
full abstract-fixed-field compositum. -/
noncomputable def
    abstractFixedFieldCyclotomicFiniteLayerInclusion
    (H : FiniteAbstractField
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
    (E :
      FiniteGaloisIntermediateField
        ℚ rationalCyclotomicZHatField) :
    abstractFixedFieldCyclotomicFiniteLayer H E →ₐ[
      LocalClassFieldTheory.abstractFixedField
        ℚ (SeparableClosure ℚ) H.field]
      LocalClassFieldTheory.abstractRelativeFixedField
        ℚ (SeparableClosure ℚ)
        (rationalCyclotomicFieldInertia_le H.field) :=
  IntermediateField.val
    (abstractFixedFieldCyclotomicFiniteLayer H E)

/-- The two embeddings of a finite rational cyclotomic layer into the
full abstract-fixed-field compositum agree. -/
theorem
    abstractFixedFieldCyclotomicFiniteLayerEmbedding_inclusion
    (H : FiniteAbstractField
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
    (E :
      FiniteGaloisIntermediateField
        ℚ rationalCyclotomicZHatField)
    (z : E) :
    abstractFixedFieldCyclotomicFiniteLayerInclusion H E
        (abstractFixedFieldCyclotomicFiniteLayerEmbedding H E z) =
      rationalCyclotomicZHatFieldEmbeddingInAbstractFixedFieldCompositum H
        (z : rationalCyclotomicZHatField) := by
  exact Subtype.ext rfl

/-- Restriction to `E` commutes pointwise with the restriction from the
full rational cyclotomic tower. -/
theorem
    restrictNormalHom_abstractFixedFieldCyclotomicRestriction_apply
    (H : FiniteAbstractField
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
    (E :
      FiniteGaloisIntermediateField
        ℚ rationalCyclotomicZHatField)
    [Normal ℚ E]
    (σ :
      Gal(
        LocalClassFieldTheory.abstractRelativeFixedField
          ℚ (SeparableClosure ℚ)
          (rationalCyclotomicFieldInertia_le H.field) /
        LocalClassFieldTheory.abstractFixedField
          ℚ (SeparableClosure ℚ) H.field))
    (z : E) :
    ((AlgEquiv.restrictNormalHom E
      (abstractFixedFieldCyclotomicRestriction H σ)) z :
        rationalCyclotomicZHatField) =
      (abstractFixedFieldCyclotomicRestriction H σ)
        (z : rationalCyclotomicZHatField) := by
  exact
    AlgEquiv.restrictNormal_commutes
      (abstractFixedFieldCyclotomicRestriction H σ) E z

/-- The raw cyclotomic restriction commutes with the canonical embedding
of the full rational cyclotomic tower. -/
theorem
    abstractFixedFieldCyclotomicRestriction_embedding_apply
    (H : FiniteAbstractField
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
    (σ :
      Gal(
        LocalClassFieldTheory.abstractRelativeFixedField
          ℚ (SeparableClosure ℚ)
          (rationalCyclotomicFieldInertia_le H.field) /
        LocalClassFieldTheory.abstractFixedField
          ℚ (SeparableClosure ℚ) H.field))
    (z : rationalCyclotomicZHatField) :
    rationalCyclotomicZHatFieldEmbeddingInAbstractFixedFieldCompositum H
        (abstractFixedFieldCyclotomicRestriction H σ z) =
      σ
        (rationalCyclotomicZHatFieldEmbeddingInAbstractFixedFieldCompositum
          H z) := by
  let U :=
    LocalClassFieldTheory.abstractRelativeFixedField
      ℚ (SeparableClosure ℚ)
      (rationalCyclotomicFieldInertia_le H.field)
  exact
    AlgEquiv.restrictNormal_commutes
      (MulSemiringAction.toAlgEquiv ℚ U σ)
      rationalCyclotomicZHatField z

/-- Restriction to the finite compositum layer commutes with its
canonical inclusion into the full compositum. -/
theorem
    restrictNormalHom_abstractFixedFieldCyclotomicFiniteLayer_apply
    (H : FiniteAbstractField
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
    (E :
      FiniteGaloisIntermediateField
        ℚ rationalCyclotomicZHatField)
    [Normal
      (LocalClassFieldTheory.abstractFixedField
        ℚ (SeparableClosure ℚ) H.field)
      (abstractFixedFieldCyclotomicFiniteLayer H E)]
    (σ :
      Gal(
        LocalClassFieldTheory.abstractRelativeFixedField
          ℚ (SeparableClosure ℚ)
          (rationalCyclotomicFieldInertia_le H.field) /
        LocalClassFieldTheory.abstractFixedField
          ℚ (SeparableClosure ℚ) H.field))
    (z : abstractFixedFieldCyclotomicFiniteLayer H E) :
    abstractFixedFieldCyclotomicFiniteLayerInclusion H E
        (AlgEquiv.restrictNormalHom
          (abstractFixedFieldCyclotomicFiniteLayer H E) σ z) =
      σ (abstractFixedFieldCyclotomicFiniteLayerInclusion H E z) := by
  let F :=
    LocalClassFieldTheory.abstractFixedField
      ℚ (SeparableClosure ℚ) H.field
  let U :=
    LocalClassFieldTheory.abstractRelativeFixedField
      ℚ (SeparableClosure ℚ)
      (rationalCyclotomicFieldInertia_le H.field)
  let P : IntermediateField F U :=
    abstractFixedFieldCyclotomicFiniteLayer H E
  exact
    AlgEquiv.restrictNormal_commutes
      (MulSemiringAction.toAlgEquiv F U σ) P z

/-- Restricting the finite-compositum action further to `E` commutes
with the explicit embedding of `E` into that finite layer. -/
theorem
    abstractFixedFieldCyclotomicFiniteLayerEmbedding_restrict_apply
    (H : FiniteAbstractField
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
    (E :
      FiniteGaloisIntermediateField
        ℚ rationalCyclotomicZHatField)
    [Normal ℚ E]
    [Normal
      (LocalClassFieldTheory.abstractFixedField
        ℚ (SeparableClosure ℚ) H.field)
      (abstractFixedFieldCyclotomicFiniteLayer H E)]
    (σ :
      Gal(
        LocalClassFieldTheory.abstractRelativeFixedField
          ℚ (SeparableClosure ℚ)
          (rationalCyclotomicFieldInertia_le H.field) /
        LocalClassFieldTheory.abstractFixedField
          ℚ (SeparableClosure ℚ) H.field))
    (z : E) :
    abstractFixedFieldCyclotomicFiniteLayerEmbedding H E
        (IntermediateField.restrictRestrictAlgEquivMapHom
          ℚ E
          (LocalClassFieldTheory.abstractFixedField
            ℚ (SeparableClosure ℚ) H.field)
          (abstractFixedFieldCyclotomicFiniteLayer H E)
          (AlgEquiv.restrictNormalHom
            (abstractFixedFieldCyclotomicFiniteLayer H E) σ) z) =
      (AlgEquiv.restrictNormalHom
        (abstractFixedFieldCyclotomicFiniteLayer H E) σ)
        (abstractFixedFieldCyclotomicFiniteLayerEmbedding H E z) := by
  let F :=
    LocalClassFieldTheory.abstractFixedField
      ℚ (SeparableClosure ℚ) H.field
  let U :=
    LocalClassFieldTheory.abstractRelativeFixedField
      ℚ (SeparableClosure ℚ)
      (rationalCyclotomicFieldInertia_le H.field)
  let P : IntermediateField F U :=
    abstractFixedFieldCyclotomicFiniteLayer H E
  exact
    AlgEquiv.restrictNormal_commutes
      (MulSemiringAction.toAlgEquiv ℚ P
        (AlgEquiv.restrictNormalHom P σ)) E z

/-- The left finite-level restriction, after both canonical embeddings into
the full compositum, is the action of `σ` on the cyclotomic embedding. -/
theorem
    restrictNormalHom_abstractFixedFieldCyclotomicRestriction_left_embedded
    (H : FiniteAbstractField
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
    (E :
      FiniteGaloisIntermediateField
        ℚ rationalCyclotomicZHatField)
    [Normal ℚ E]
    (σ :
      Gal(
        LocalClassFieldTheory.abstractRelativeFixedField
          ℚ (SeparableClosure ℚ)
          (rationalCyclotomicFieldInertia_le H.field) /
        LocalClassFieldTheory.abstractFixedField
          ℚ (SeparableClosure ℚ) H.field))
    (x : E) :
    abstractFixedFieldCyclotomicFiniteLayerInclusion H E
        (abstractFixedFieldCyclotomicFiniteLayerEmbedding H E
          (AlgEquiv.restrictNormalHom E
            (abstractFixedFieldCyclotomicRestriction H σ) x)) =
      σ
        (rationalCyclotomicZHatFieldEmbeddingInAbstractFixedFieldCompositum H
          (x : rationalCyclotomicZHatField)) := by
  calc
    abstractFixedFieldCyclotomicFiniteLayerInclusion H E
          (abstractFixedFieldCyclotomicFiniteLayerEmbedding H E
            (AlgEquiv.restrictNormalHom E
              (abstractFixedFieldCyclotomicRestriction H σ) x)) =
        rationalCyclotomicZHatFieldEmbeddingInAbstractFixedFieldCompositum H
          (((AlgEquiv.restrictNormalHom E
            (abstractFixedFieldCyclotomicRestriction H σ) x) :
              rationalCyclotomicZHatField)) :=
      abstractFixedFieldCyclotomicFiniteLayerEmbedding_inclusion H E _
    _ = rationalCyclotomicZHatFieldEmbeddingInAbstractFixedFieldCompositum H
          (abstractFixedFieldCyclotomicRestriction H σ
            (x : rationalCyclotomicZHatField)) :=
      congrArg
        (rationalCyclotomicZHatFieldEmbeddingInAbstractFixedFieldCompositum H)
        (restrictNormalHom_abstractFixedFieldCyclotomicRestriction_apply
          H E σ x)
    _ = σ
          (rationalCyclotomicZHatFieldEmbeddingInAbstractFixedFieldCompositum
            H (x : rationalCyclotomicZHatField)) :=
      abstractFixedFieldCyclotomicRestriction_embedding_apply
        H σ (x : rationalCyclotomicZHatField)

/-- The right finite-level restriction, after both canonical embeddings into
the full compositum, is the same action of `σ`. -/
theorem
    restrictNormalHom_abstractFixedFieldCyclotomicRestriction_right_embedded
    (H : FiniteAbstractField
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
    (E :
      FiniteGaloisIntermediateField
        ℚ rationalCyclotomicZHatField)
    [Normal ℚ E]
    [Normal
      (LocalClassFieldTheory.abstractFixedField
        ℚ (SeparableClosure ℚ) H.field)
      (abstractFixedFieldCyclotomicFiniteLayer H E)]
    (σ :
      Gal(
        LocalClassFieldTheory.abstractRelativeFixedField
          ℚ (SeparableClosure ℚ)
          (rationalCyclotomicFieldInertia_le H.field) /
        LocalClassFieldTheory.abstractFixedField
          ℚ (SeparableClosure ℚ) H.field))
    (x : E) :
    abstractFixedFieldCyclotomicFiniteLayerInclusion H E
        (abstractFixedFieldCyclotomicFiniteLayerEmbedding H E
          (IntermediateField.restrictRestrictAlgEquivMapHom
            ℚ E
            (LocalClassFieldTheory.abstractFixedField
              ℚ (SeparableClosure ℚ) H.field)
            (abstractFixedFieldCyclotomicFiniteLayer H E)
            (AlgEquiv.restrictNormalHom
              (abstractFixedFieldCyclotomicFiniteLayer H E) σ) x)) =
      σ
        (rationalCyclotomicZHatFieldEmbeddingInAbstractFixedFieldCompositum H
          (x : rationalCyclotomicZHatField)) := by
  calc
    abstractFixedFieldCyclotomicFiniteLayerInclusion H E
          (abstractFixedFieldCyclotomicFiniteLayerEmbedding H E
            (IntermediateField.restrictRestrictAlgEquivMapHom
              ℚ E
              (LocalClassFieldTheory.abstractFixedField
                ℚ (SeparableClosure ℚ) H.field)
              (abstractFixedFieldCyclotomicFiniteLayer H E)
              (AlgEquiv.restrictNormalHom
                (abstractFixedFieldCyclotomicFiniteLayer H E) σ) x)) =
        abstractFixedFieldCyclotomicFiniteLayerInclusion H E
          ((AlgEquiv.restrictNormalHom
            (abstractFixedFieldCyclotomicFiniteLayer H E) σ)
            (abstractFixedFieldCyclotomicFiniteLayerEmbedding H E x)) :=
      congrArg
        (abstractFixedFieldCyclotomicFiniteLayerInclusion H E)
        (abstractFixedFieldCyclotomicFiniteLayerEmbedding_restrict_apply
          H E σ x)
    _ = σ
          (abstractFixedFieldCyclotomicFiniteLayerInclusion H E
            (abstractFixedFieldCyclotomicFiniteLayerEmbedding H E x)) :=
      restrictNormalHom_abstractFixedFieldCyclotomicFiniteLayer_apply
        H E σ (abstractFixedFieldCyclotomicFiniteLayerEmbedding H E x)
    _ = σ
          (rationalCyclotomicZHatFieldEmbeddingInAbstractFixedFieldCompositum
            H (x : rationalCyclotomicZHatField)) :=
      congrArg σ
        (abstractFixedFieldCyclotomicFiniteLayerEmbedding_inclusion H E x)

/-- Pointwise form of finite-layer restriction compatibility. -/
theorem
    restrictNormalHom_abstractFixedFieldCyclotomicRestriction_pointwise
    (H : FiniteAbstractField
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
    (E :
      FiniteGaloisIntermediateField
        ℚ rationalCyclotomicZHatField)
    [Normal ℚ E]
    [Normal
      (LocalClassFieldTheory.abstractFixedField
        ℚ (SeparableClosure ℚ) H.field)
      (abstractFixedFieldCyclotomicFiniteLayer H E)]
    (σ :
      Gal(
        LocalClassFieldTheory.abstractRelativeFixedField
          ℚ (SeparableClosure ℚ)
          (rationalCyclotomicFieldInertia_le H.field) /
        LocalClassFieldTheory.abstractFixedField
          ℚ (SeparableClosure ℚ) H.field))
    (x : E) :
    AlgEquiv.restrictNormalHom E
        (abstractFixedFieldCyclotomicRestriction H σ) x =
      IntermediateField.restrictRestrictAlgEquivMapHom
          ℚ E
          (LocalClassFieldTheory.abstractFixedField
            ℚ (SeparableClosure ℚ) H.field)
          (abstractFixedFieldCyclotomicFiniteLayer H E)
        (AlgEquiv.restrictNormalHom
          (abstractFixedFieldCyclotomicFiniteLayer H E) σ) x := by
  apply
    (abstractFixedFieldCyclotomicFiniteLayerEmbedding H E).injective
  apply
    (abstractFixedFieldCyclotomicFiniteLayerInclusion H E).injective
  exact
    (restrictNormalHom_abstractFixedFieldCyclotomicRestriction_left_embedded
      H E σ x).trans
      (restrictNormalHom_abstractFixedFieldCyclotomicRestriction_right_embedded
        H E σ x).symm

/-- Restricting through a finite layer commutes with restriction from
the full abstract-fixed-field compositum. -/
theorem
    restrictNormalHom_abstractFixedFieldCyclotomicRestriction
    (H : FiniteAbstractField
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
    (E :
      FiniteGaloisIntermediateField
        ℚ rationalCyclotomicZHatField)
    (σ :
      Gal(
        LocalClassFieldTheory.abstractRelativeFixedField
          ℚ (SeparableClosure ℚ)
          (rationalCyclotomicFieldInertia_le H.field) /
        LocalClassFieldTheory.abstractFixedField
          ℚ (SeparableClosure ℚ) H.field)) :
    letI : Normal ℚ E := E.isGalois.to_normal
    AlgEquiv.restrictNormalHom E
        (abstractFixedFieldCyclotomicRestriction H σ) =
      IntermediateField.restrictRestrictAlgEquivMapHom
          ℚ E
          (LocalClassFieldTheory.abstractFixedField
            ℚ (SeparableClosure ℚ) H.field)
          (abstractFixedFieldCyclotomicFiniteLayer H E)
        (AlgEquiv.restrictNormalHom
          (abstractFixedFieldCyclotomicFiniteGaloisLayer H E)
          σ) := by
  let : Normal ℚ E := E.isGalois.to_normal
  let F :=
    LocalClassFieldTheory.abstractFixedField
      ℚ (SeparableClosure ℚ) H.field
  let U :=
    LocalClassFieldTheory.abstractRelativeFixedField
      ℚ (SeparableClosure ℚ)
      (rationalCyclotomicFieldInertia_le H.field)
  let T := rationalCyclotomicZHatField
  let P : IntermediateField F U :=
    abstractFixedFieldCyclotomicFiniteLayer H E
  let : Algebra T U :=
    abstractFixedFieldCyclotomicCompositum_algebra H
  let : IsScalarTower ℚ T U :=
    abstractFixedFieldCyclotomicCompositum_scalarTower H
  let : Algebra E P :=
    abstractFixedFieldCyclotomicFiniteLayer_layerAlgebra H E
  let : IsScalarTower ℚ E P :=
    abstractFixedFieldCyclotomicFiniteLayer_layerScalarTower H E
  let : IsAbelianGalois F P := by
    change IsAbelianGalois F
      (abstractFixedFieldCyclotomicFiniteLayer H E)
    exact
      abstractFixedFieldCyclotomicFiniteLayer_isAbelianGalois H E
  let : Normal F P := IsGalois.to_normal
  apply AlgEquiv.ext
  intro x
  exact
    restrictNormalHom_abstractFixedFieldCyclotomicRestriction_pointwise
      H E σ x

section FiniteCoordinateHelpers

attribute [local instance] GlobalClassFieldTheory.Reciprocity.cyclotomicAbstractFixedFieldArtin_separableClosureAlgebra
attribute [local instance] GlobalClassFieldTheory.Reciprocity.cyclotomicAbstractFixedFieldArtin_cyclotomicZHatFieldNormal
abbrev cyclotomicAbstractFixedFieldArtinCoordinateBase
    (H : FiniteAbstractField
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ)) :=
  LocalClassFieldTheory.abstractFixedField
    ℚ (SeparableClosure ℚ) H.field

abbrev cyclotomicAbstractFixedFieldArtinCoordinateRelative
    (H : FiniteAbstractField
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ)) :=
  LocalClassFieldTheory.abstractRelativeFixedField
    ℚ (SeparableClosure ℚ)
    (rationalCyclotomicFieldInertia_le H.field)

attribute [local instance] GlobalClassFieldTheory.Reciprocity.cyclotomicAbstractFixedFieldArtin_cyclotomicZHatFieldAlgebra
abbrev cyclotomicAbstractFixedFieldArtinCoordinateLayer
    (H : FiniteAbstractField
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
    (E :
      FiniteGaloisIntermediateField
        ℚ rationalCyclotomicZHatField) :
    IntermediateField
      (cyclotomicAbstractFixedFieldArtinCoordinateBase H)
      (cyclotomicAbstractFixedFieldArtinCoordinateRelative H) :=
  abstractFixedFieldCyclotomicFiniteLayer H E

noncomputable local instance
    cyclotomicAbstractFixedFieldArtinCoordinateBaseAlgebra
    (H : FiniteAbstractField
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ)) :
    Algebra ℚ
      (cyclotomicAbstractFixedFieldArtinCoordinateBase H) :=
  (cyclotomicAbstractFixedFieldArtinCoordinateBase H).algebra'

noncomputable local instance
    cyclotomicAbstractFixedFieldArtinCoordinateBaseFiniteDimensional
    (H : FiniteAbstractField
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ)) :
    FiniteDimensional ℚ
      (cyclotomicAbstractFixedFieldArtinCoordinateBase H) :=
  LocalClassFieldTheory.abstractFixedField_finiteDimensional
    ℚ (SeparableClosure ℚ) H.field H.finite

noncomputable local instance
    cyclotomicAbstractFixedFieldArtinCoordinateBaseNumberField
    (H : FiniteAbstractField
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ)) :
    NumberField
      (cyclotomicAbstractFixedFieldArtinCoordinateBase H) :=
  NumberField.of_module_finite ℚ
    (cyclotomicAbstractFixedFieldArtinCoordinateBase H)

noncomputable local instance
    cyclotomicAbstractFixedFieldArtinCoordinateBaseSeparableAlgebra
    (H : FiniteAbstractField
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ)) :
    Algebra
      (cyclotomicAbstractFixedFieldArtinCoordinateBase H)
      (SeparableClosure ℚ) :=
  IntermediateField.toAlgebra
    (cyclotomicAbstractFixedFieldArtinCoordinateBase H)

noncomputable local instance
    cyclotomicAbstractFixedFieldArtinCoordinateRelativeAlgebra
    (H : FiniteAbstractField
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ)) :
    Algebra
      (cyclotomicAbstractFixedFieldArtinCoordinateBase H)
      (cyclotomicAbstractFixedFieldArtinCoordinateRelative H) :=
  (cyclotomicAbstractFixedFieldArtinCoordinateRelative H).algebra'

local instance
    cyclotomicAbstractFixedFieldArtinCoordinateRelativeScalarTower
    (H : FiniteAbstractField
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ)) :
    IsScalarTower ℚ
      (cyclotomicAbstractFixedFieldArtinCoordinateBase H)
      (cyclotomicAbstractFixedFieldArtinCoordinateRelative H) :=
  abstractFixedFieldCyclotomicCompositum_baseScalarTower H

noncomputable local instance
    cyclotomicAbstractFixedFieldArtinCoordinateRelativeIsAbelianGalois
    (H : FiniteAbstractField
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ)) :
    IsAbelianGalois
      (cyclotomicAbstractFixedFieldArtinCoordinateBase H)
      (cyclotomicAbstractFixedFieldArtinCoordinateRelative H) :=
  abstractFixedFieldCyclotomic_isAbelianGalois H

noncomputable local instance
    cyclotomicAbstractFixedFieldArtinCoordinateAlgebra
    (E :
      FiniteGaloisIntermediateField
        ℚ rationalCyclotomicZHatField) :
    Algebra ℚ E :=
  E.toIntermediateField.algebra'

noncomputable local instance
    cyclotomicAbstractFixedFieldArtinCoordinateNumberField
    (E :
      FiniteGaloisIntermediateField
        ℚ rationalCyclotomicZHatField) :
    NumberField E :=
  NumberField.of_module_finite ℚ E

noncomputable local instance
    cyclotomicAbstractFixedFieldArtinCoordinateIsAbelianGalois
    (E :
      FiniteGaloisIntermediateField
        ℚ rationalCyclotomicZHatField) :
    IsAbelianGalois ℚ E :=
  IsAbelianGalois.of_algHom E.toIntermediateField.val

local instance
    cyclotomicAbstractFixedFieldArtinCoordinateNormal
    (E :
      FiniteGaloisIntermediateField
        ℚ rationalCyclotomicZHatField) :
    Normal ℚ E :=
  E.isGalois.to_normal

noncomputable local instance
    cyclotomicAbstractFixedFieldArtinCoordinateLayerBaseAlgebra
    (H : FiniteAbstractField
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
    (E :
      FiniteGaloisIntermediateField
        ℚ rationalCyclotomicZHatField) :
    Algebra
      (cyclotomicAbstractFixedFieldArtinCoordinateBase H)
      (cyclotomicAbstractFixedFieldArtinCoordinateLayer H E) :=
  (abstractFixedFieldCyclotomicFiniteGaloisLayer H E).algebra'

noncomputable local instance
    cyclotomicAbstractFixedFieldArtinCoordinateLayerRatAlgebra
    (H : FiniteAbstractField
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
    (E :
      FiniteGaloisIntermediateField
        ℚ rationalCyclotomicZHatField) :
    Algebra ℚ
      (cyclotomicAbstractFixedFieldArtinCoordinateLayer H E) :=
  DivisionRing.toRatAlgebra

local instance
    cyclotomicAbstractFixedFieldArtinCoordinateLayerBaseScalarTower
    (H : FiniteAbstractField
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
    (E :
      FiniteGaloisIntermediateField
        ℚ rationalCyclotomicZHatField) :
    IsScalarTower ℚ
      (cyclotomicAbstractFixedFieldArtinCoordinateBase H)
      (cyclotomicAbstractFixedFieldArtinCoordinateLayer H E) := by
  let hI := rationalCyclotomicFieldInertia_le H.field
  apply IsScalarTower.of_algebraMap_eq
  intro x
  apply Subtype.ext
  change
    algebraMap ℚ
        (LocalClassFieldTheory.abstractRelativeFixedField
          ℚ (SeparableClosure ℚ) hI) x =
      algebraMap
        (LocalClassFieldTheory.abstractFixedField
          ℚ (SeparableClosure ℚ) H.field)
        (LocalClassFieldTheory.abstractRelativeFixedField
          ℚ (SeparableClosure ℚ) hI)
        (algebraMap ℚ
          (LocalClassFieldTheory.abstractFixedField
            ℚ (SeparableClosure ℚ) H.field) x)
  exact
    IsScalarTower.algebraMap_apply
      ℚ
      (LocalClassFieldTheory.abstractFixedField
        ℚ (SeparableClosure ℚ) H.field)
      (LocalClassFieldTheory.abstractRelativeFixedField
        ℚ (SeparableClosure ℚ) hI) x

noncomputable local instance
    cyclotomicAbstractFixedFieldArtinCoordinateLayerNumberField
    (H : FiniteAbstractField
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
    (E :
      FiniteGaloisIntermediateField
        ℚ rationalCyclotomicZHatField) :
    NumberField
      (abstractFixedFieldCyclotomicFiniteGaloisLayer H E) :=
  abstractFixedFieldCyclotomicFiniteLayer_numberField H E

noncomputable local instance
    cyclotomicAbstractFixedFieldArtinCoordinateLayerAlgebra
    (H : FiniteAbstractField
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
    (E :
      FiniteGaloisIntermediateField
        ℚ rationalCyclotomicZHatField) :
    Algebra E
      (cyclotomicAbstractFixedFieldArtinCoordinateLayer H E) :=
  abstractFixedFieldCyclotomicFiniteLayer_layerAlgebra H E

noncomputable local instance
    cyclotomicAbstractFixedFieldArtinCoordinateLayerSMul
    (H : FiniteAbstractField
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
    (E :
      FiniteGaloisIntermediateField
        ℚ rationalCyclotomicZHatField) :
    SMul E
      (cyclotomicAbstractFixedFieldArtinCoordinateLayer H E) :=
  abstractFixedFieldCyclotomicFiniteLayer_layerSMul H E

local instance
    cyclotomicAbstractFixedFieldArtinCoordinateLayerScalarTower
    (H : FiniteAbstractField
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
    (E :
      FiniteGaloisIntermediateField
        ℚ rationalCyclotomicZHatField) :
    IsScalarTower ℚ E
      (cyclotomicAbstractFixedFieldArtinCoordinateLayer H E) :=
  abstractFixedFieldCyclotomicFiniteLayer_layerScalarTower H E

noncomputable local instance
    cyclotomicAbstractFixedFieldArtinCoordinateLayerRelativeAlgebra
    (H : FiniteAbstractField
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
    (E :
      FiniteGaloisIntermediateField
        ℚ rationalCyclotomicZHatField) :
    Algebra
      (cyclotomicAbstractFixedFieldArtinCoordinateLayer H E)
      (cyclotomicAbstractFixedFieldArtinCoordinateRelative H) :=
  IntermediateField.toAlgebra
    (cyclotomicAbstractFixedFieldArtinCoordinateLayer H E)

local instance
    cyclotomicAbstractFixedFieldArtinCoordinateLayerRelativeScalarTower_rf782b9_1
    (H : FiniteAbstractField
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
    (E :
      FiniteGaloisIntermediateField
        ℚ rationalCyclotomicZHatField) :
    IsScalarTower
      (cyclotomicAbstractFixedFieldArtinCoordinateBase H)
      (cyclotomicAbstractFixedFieldArtinCoordinateLayer H E)
      (cyclotomicAbstractFixedFieldArtinCoordinateRelative H) :=
  abstractFixedFieldCyclotomicFiniteGaloisLayer_scalarTower H E
noncomputable local instance
    cyclotomicAbstractFixedFieldArtinCoordinateLayerIsAbelianGalois
    (H : FiniteAbstractField
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
    (E :
      FiniteGaloisIntermediateField
        ℚ rationalCyclotomicZHatField) :
    IsAbelianGalois
      (cyclotomicAbstractFixedFieldArtinCoordinateBase H)
      (cyclotomicAbstractFixedFieldArtinCoordinateLayer H E) :=
  abstractFixedFieldCyclotomicFiniteLayer_isAbelianGalois H E

/-- The full abstract Artin symbol whose finite coordinates are compared
below.  Naming this endpoint keeps its relative fixed-field data opaque. -/
noncomputable def
    cyclotomicAbstractFixedFieldArtinAbstractEndpoint
    (H : FiniteAbstractField
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
    (a : IdeleGroup
      (cyclotomicAbstractFixedFieldArtinCoordinateBase H)) :
    Gal(rationalCyclotomicZHatField / ℚ) :=
  abstractFixedFieldCyclotomicRestriction H
    (infiniteGlobalArtinMonoidHom
      (cyclotomicAbstractFixedFieldArtinCoordinateBase H)
      (cyclotomicAbstractFixedFieldArtinCoordinateRelative H) a)

/-- The rational norm Artin symbol serving as the other full endpoint. -/
noncomputable def
    cyclotomicAbstractFixedFieldArtinRationalEndpoint
    (H : FiniteAbstractField
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
    (a : IdeleGroup
      (cyclotomicAbstractFixedFieldArtinCoordinateBase H)) :
    Gal(rationalCyclotomicZHatField / ℚ) :=
  rationalCyclotomicZHatGlobalArtin
    (IdeleGroup.norm ℚ
      (cyclotomicAbstractFixedFieldArtinCoordinateBase H) a)

/-- The finite restriction map packaged together with its pointwise Artin
naturality law.  The map is inferred from the generic hom-level theorem, so
no concrete instance tower is compared after the opaque boundary. -/
noncomputable def cyclotomicAbstractFixedFieldArtinCoordinateMapData
    (H : FiniteAbstractField
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
    (E :
      FiniteGaloisIntermediateField
        ℚ rationalCyclotomicZHatField) :
    {f : Gal(abstractFixedFieldCyclotomicFiniteGaloisLayer H E /
        cyclotomicAbstractFixedFieldArtinCoordinateBase H) →*
        Gal(E / ℚ) //
      f.comp
          (@globalArtinMonoidHomOfNumberField
            (cyclotomicAbstractFixedFieldArtinCoordinateBase H)
            (abstractFixedFieldCyclotomicFiniteGaloisLayer H E)
            (inferInstance : Field
              (cyclotomicAbstractFixedFieldArtinCoordinateBase H))
            (cyclotomicAbstractFixedFieldArtinCoordinateBaseNumberField H)
            (inferInstance : Field
              (abstractFixedFieldCyclotomicFiniteGaloisLayer H E))
            (cyclotomicAbstractFixedFieldArtinCoordinateLayerBaseAlgebra H E)
            (cyclotomicAbstractFixedFieldArtinCoordinateLayerIsAbelianGalois H E)
            (cyclotomicAbstractFixedFieldArtinCoordinateLayerNumberField H E)) =
        (globalArtinMonoidHom (K := ℚ) (L := E)).comp
          (IdeleGroup.norm ℚ
            (cyclotomicAbstractFixedFieldArtinCoordinateBase H))} := by
  have hnat :=
    @globalArtinMonoidHomOfNumberField_norm_restriction
      ℚ E
      (cyclotomicAbstractFixedFieldArtinCoordinateBase H)
      (abstractFixedFieldCyclotomicFiniteGaloisLayer H E)
      inferInstance inferInstance
      inferInstance
      (cyclotomicAbstractFixedFieldArtinCoordinateNumberField E)
      (cyclotomicAbstractFixedFieldArtinCoordinateAlgebra E)
      (cyclotomicAbstractFixedFieldArtinCoordinateIsAbelianGalois E)
      inferInstance
      (cyclotomicAbstractFixedFieldArtinCoordinateBaseNumberField H)
      inferInstance
      (cyclotomicAbstractFixedFieldArtinCoordinateBaseAlgebra H)
      (cyclotomicAbstractFixedFieldArtinCoordinateLayerBaseAlgebra H E)
      (cyclotomicAbstractFixedFieldArtinCoordinateLayerRatAlgebra H E)
      (cyclotomicAbstractFixedFieldArtinCoordinateLayerBaseScalarTower H E)
      (cyclotomicAbstractFixedFieldArtinCoordinateLayerAlgebra H E)
      (cyclotomicAbstractFixedFieldArtinCoordinateLayerScalarTower H E)
      (cyclotomicAbstractFixedFieldArtinCoordinateLayerIsAbelianGalois H E)
      (cyclotomicAbstractFixedFieldArtinCoordinateLayerNumberField H E)
  exact
    ⟨(@AlgEquiv.restrictNormalHom
          ℚ inferInstance
          (abstractFixedFieldCyclotomicFiniteGaloisLayer H E)
          inferInstance
          (cyclotomicAbstractFixedFieldArtinCoordinateLayerRatAlgebra H E)
          E inferInstance
          (cyclotomicAbstractFixedFieldArtinCoordinateAlgebra E)
          (cyclotomicAbstractFixedFieldArtinCoordinateLayerAlgebra H E)
          (cyclotomicAbstractFixedFieldArtinCoordinateLayerScalarTower H E)
          (cyclotomicAbstractFixedFieldArtinCoordinateNormal E)).comp
        (@AlgEquiv.restrictScalarsHom
          ℚ
          (cyclotomicAbstractFixedFieldArtinCoordinateBase H)
          (abstractFixedFieldCyclotomicFiniteGaloisLayer H E)
          inferInstance inferInstance inferInstance
          (cyclotomicAbstractFixedFieldArtinCoordinateBaseAlgebra H)
          (cyclotomicAbstractFixedFieldArtinCoordinateLayerBaseAlgebra H E)
          (cyclotomicAbstractFixedFieldArtinCoordinateLayerRatAlgebra H E)
          (cyclotomicAbstractFixedFieldArtinCoordinateLayerBaseScalarTower H E)),
      hnat⟩

/-- The fixed restriction map from the relative finite layer to one rational
cyclotomic coordinate. -/
noncomputable def cyclotomicAbstractFixedFieldArtinCoordinateMap
    (H : FiniteAbstractField
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
    (E :
      FiniteGaloisIntermediateField
        ℚ rationalCyclotomicZHatField) :
    Gal(abstractFixedFieldCyclotomicFiniteGaloisLayer H E /
        cyclotomicAbstractFixedFieldArtinCoordinateBase H) →*
      Gal(E / ℚ) :=
  (cyclotomicAbstractFixedFieldArtinCoordinateMapData H E).1

/-- Naturality of the named coordinate map, kept at the hom level so later
pointwise rewrites match the opaque map without unfolding its data package. -/
theorem cyclotomicAbstractFixedFieldArtinCoordinateMap_naturality
    (H : FiniteAbstractField
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
    (E :
      FiniteGaloisIntermediateField
        ℚ rationalCyclotomicZHatField) :
    (cyclotomicAbstractFixedFieldArtinCoordinateMap H E).comp
        (globalArtinMonoidHom
          (K := cyclotomicAbstractFixedFieldArtinCoordinateBase H)
          (L := abstractFixedFieldCyclotomicFiniteGaloisLayer H E)) =
      (globalArtinMonoidHom (K := ℚ) (L := E)).comp
        (IdeleGroup.norm ℚ
          (cyclotomicAbstractFixedFieldArtinCoordinateBase H)) :=
  (cyclotomicAbstractFixedFieldArtinCoordinateMapData H E).2

/-- Pointwise identification of the named coordinate map with the concrete
two-stage restriction used by the abstract fixed-field comparison. -/
theorem cyclotomicAbstractFixedFieldArtinCoordinateMap_apply
    (H : FiniteAbstractField
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
    (E :
      FiniteGaloisIntermediateField
        ℚ rationalCyclotomicZHatField)
    (σ : Gal(abstractFixedFieldCyclotomicFiniteGaloisLayer H E /
      cyclotomicAbstractFixedFieldArtinCoordinateBase H)) :
    cyclotomicAbstractFixedFieldArtinCoordinateMap H E σ =
      @IntermediateField.restrictRestrictAlgEquivMapHom
        ℚ E
        (cyclotomicAbstractFixedFieldArtinCoordinateBase H)
        (abstractFixedFieldCyclotomicFiniteGaloisLayer H E)
        inferInstance inferInstance inferInstance inferInstance
        (cyclotomicAbstractFixedFieldArtinCoordinateAlgebra E)
        (cyclotomicAbstractFixedFieldArtinCoordinateBaseAlgebra H)
        (cyclotomicAbstractFixedFieldArtinCoordinateLayerRatAlgebra H E)
        (cyclotomicAbstractFixedFieldArtinCoordinateLayerAlgebra H E)
        (cyclotomicAbstractFixedFieldArtinCoordinateLayerBaseAlgebra H E)
        (cyclotomicAbstractFixedFieldArtinCoordinateLayerScalarTower H E)
        (cyclotomicAbstractFixedFieldArtinCoordinateLayerBaseScalarTower H E)
        (cyclotomicAbstractFixedFieldArtinCoordinateNormal E) σ :=
  rfl

/-- The relative projection, common rational finite value, and rational
infinite projection, with both comparison steps packaged by the generic
provider before this concrete tower becomes opaque. -/
noncomputable def
    cyclotomicAbstractFixedFieldArtinCoordinateBridgeData
    (H : FiniteAbstractField
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
    (a : IdeleGroup
      (cyclotomicAbstractFixedFieldArtinCoordinateBase H))
    (E :
      FiniteGaloisIntermediateField
        ℚ rationalCyclotomicZHatField) :=
    @compRestrictNormalHomInfiniteGlobalArtinRationalCyclotomicDataOfNumberField
      (cyclotomicAbstractFixedFieldArtinCoordinateBase H)
      (cyclotomicAbstractFixedFieldArtinCoordinateRelative H)
      (inferInstance : Field
        (cyclotomicAbstractFixedFieldArtinCoordinateBase H))
      (cyclotomicAbstractFixedFieldArtinCoordinateBaseNumberField H)
      (inferInstance : Field
        (cyclotomicAbstractFixedFieldArtinCoordinateRelative H))
      (cyclotomicAbstractFixedFieldArtinCoordinateRelativeAlgebra H)
      (cyclotomicAbstractFixedFieldArtinCoordinateRelativeIsAbelianGalois H)
      a
      (abstractFixedFieldCyclotomicFiniteGaloisLayer H E)
      (cyclotomicAbstractFixedFieldArtinCoordinateLayerNumberField H E)
      E
      (cyclotomicAbstractFixedFieldArtinCoordinateNumberField E)
      (cyclotomicAbstractFixedFieldArtinCoordinateIsAbelianGalois E)
      (cyclotomicAbstractFixedFieldArtinCoordinateMap H E)
      (cyclotomicAbstractFixedFieldArtinCoordinateMap_naturality H E)

/-- The abstract endpoint after projection to one finite coordinate. -/
noncomputable def
    cyclotomicAbstractFixedFieldArtinAbstractCoordinate
    (H : FiniteAbstractField
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
    (a : IdeleGroup
      (cyclotomicAbstractFixedFieldArtinCoordinateBase H))
    (E :
      FiniteGaloisIntermediateField
        ℚ rationalCyclotomicZHatField) :
    Gal(E / ℚ) :=
  AlgEquiv.restrictNormalHom E
    (cyclotomicAbstractFixedFieldArtinAbstractEndpoint H a)

/-- The relative infinite Artin symbol, restricted to a finite layer and
then mapped to the corresponding rational coordinate. -/
noncomputable def
    cyclotomicAbstractFixedFieldArtinRestrictedLayerCoordinate
    (H : FiniteAbstractField
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
    (a : IdeleGroup
      (cyclotomicAbstractFixedFieldArtinCoordinateBase H))
    (E :
      FiniteGaloisIntermediateField
        ℚ rationalCyclotomicZHatField) :
    Gal(E / ℚ) :=
  (cyclotomicAbstractFixedFieldArtinCoordinateBridgeData H a E).1.1

/-- The finite relative Artin symbol mapped to one rational coordinate. -/
noncomputable def
    cyclotomicAbstractFixedFieldArtinFiniteCoordinate
    (H : FiniteAbstractField
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
    (a : IdeleGroup
      (cyclotomicAbstractFixedFieldArtinCoordinateBase H))
    (E :
      FiniteGaloisIntermediateField
        ℚ rationalCyclotomicZHatField) :
    Gal(E / ℚ) :=
  (cyclotomicAbstractFixedFieldArtinCoordinateBridgeData H a E).1.2.1

/-- The rational endpoint after projection to one finite coordinate. -/
noncomputable def
    cyclotomicAbstractFixedFieldArtinRationalEndpointCoordinate
    (H : FiniteAbstractField
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
    (a : IdeleGroup
      (cyclotomicAbstractFixedFieldArtinCoordinateBase H))
    (E :
      FiniteGaloisIntermediateField
        ℚ rationalCyclotomicZHatField) :
    Gal(E / ℚ) :=
  (cyclotomicAbstractFixedFieldArtinCoordinateBridgeData H a E).1.2.2

/-- The abstract restriction map projected to the concrete finite layer. -/
theorem
    cyclotomicAbstractFixedFieldArtinCoordinateRestriction
    (H : FiniteAbstractField
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
    (a : IdeleGroup
      (cyclotomicAbstractFixedFieldArtinCoordinateBase H))
    (E :
      FiniteGaloisIntermediateField
        ℚ rationalCyclotomicZHatField) :
    cyclotomicAbstractFixedFieldArtinAbstractCoordinate H a E =
      cyclotomicAbstractFixedFieldArtinRestrictedLayerCoordinate H a E := by
  calc
    cyclotomicAbstractFixedFieldArtinAbstractCoordinate H a E =
        AlgEquiv.restrictNormalHom E
          (cyclotomicAbstractFixedFieldArtinAbstractEndpoint H a) := rfl
    _ = cyclotomicAbstractFixedFieldArtinCoordinateMap H E
          (AlgEquiv.restrictNormalHom
            (abstractFixedFieldCyclotomicFiniteGaloisLayer H E)
            (infiniteGlobalArtinMonoidHom
              (cyclotomicAbstractFixedFieldArtinCoordinateBase H)
              (cyclotomicAbstractFixedFieldArtinCoordinateRelative H) a)) :=
      (restrictNormalHom_abstractFixedFieldCyclotomicRestriction
          H E
            (infiniteGlobalArtinMonoidHom
              (cyclotomicAbstractFixedFieldArtinCoordinateBase H)
              (cyclotomicAbstractFixedFieldArtinCoordinateRelative H) a)).trans
        (cyclotomicAbstractFixedFieldArtinCoordinateMap_apply H E _).symm
    _ = cyclotomicAbstractFixedFieldArtinRestrictedLayerCoordinate H a E := rfl

/-- Restricting the infinite relative Artin symbol supplies exactly the
finite Artin coordinate. -/
theorem
    cyclotomicAbstractFixedFieldArtinCoordinateLayerProjection
    (H : FiniteAbstractField
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
    (a : IdeleGroup
      (cyclotomicAbstractFixedFieldArtinCoordinateBase H))
    (E :
      FiniteGaloisIntermediateField
        ℚ rationalCyclotomicZHatField) :
    cyclotomicAbstractFixedFieldArtinRestrictedLayerCoordinate H a E =
      cyclotomicAbstractFixedFieldArtinFiniteCoordinate H a E :=
  (cyclotomicAbstractFixedFieldArtinCoordinateBridgeData H a E).2.1

/-- The rational cyclotomic Artin map projected to the same finite
coordinate. -/
theorem
    cyclotomicAbstractFixedFieldArtinCoordinateRationalProjection
    (H : FiniteAbstractField
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
    (a : IdeleGroup
      (cyclotomicAbstractFixedFieldArtinCoordinateBase H))
    (E :
      FiniteGaloisIntermediateField
        ℚ rationalCyclotomicZHatField) :
    cyclotomicAbstractFixedFieldArtinRationalEndpointCoordinate H a E =
      cyclotomicAbstractFixedFieldArtinFiniteCoordinate H a E := by
  exact
    (cyclotomicAbstractFixedFieldArtinCoordinateBridgeData H a E).2.2.symm

/-- Equality of the two full endpoints at one opaque finite coordinate. -/
theorem
    cyclotomicAbstractFixedFieldArtinFiniteCoordinateComparison
    (H : FiniteAbstractField
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
    (a : IdeleGroup
      (cyclotomicAbstractFixedFieldArtinCoordinateBase H))
    (E :
      FiniteGaloisIntermediateField
        ℚ rationalCyclotomicZHatField) :
    AlgEquiv.restrictNormalHom E
        (cyclotomicAbstractFixedFieldArtinAbstractEndpoint H a) =
      AlgEquiv.restrictNormalHom E
        (cyclotomicAbstractFixedFieldArtinRationalEndpoint H a) := by
  change
    cyclotomicAbstractFixedFieldArtinAbstractCoordinate H a E =
      cyclotomicAbstractFixedFieldArtinRationalEndpointCoordinate H a E
  exact
    cyclotomicAbstractFixedFieldArtin_eqTransThree
      (cyclotomicAbstractFixedFieldArtinCoordinateRestriction H a E)
      (cyclotomicAbstractFixedFieldArtinCoordinateLayerProjection H a E)
      (cyclotomicAbstractFixedFieldArtinCoordinateRationalProjection
        H a E).symm

/-- The finite-coordinate comparison assembled in the rational cyclotomic
inverse limit. -/
theorem
    abstractFixedFieldCyclotomicRestriction_infiniteGlobalArtin_inverseLimit
    (H : FiniteAbstractField
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
    (a :
      IdeleGroup
        (cyclotomicAbstractFixedFieldArtinCoordinateBase H)) :
    cyclotomicAbstractFixedFieldArtinAbstractEndpoint H a =
      cyclotomicAbstractFixedFieldArtinRationalEndpoint H a := by
  apply
    (InfiniteGalois.continuousMulEquivToLimit
      ℚ rationalCyclotomicZHatField).injective
  apply Subtype.ext
  funext Eop
  exact
    cyclotomicAbstractFixedFieldArtinFiniteCoordinateComparison
      H a Eop.unop

end FiniteCoordinateHelpers

/-- The actual infinite global Artin map on an abstract fixed field
restricts to the rational cyclotomic Artin map of the ordinary idele
norm. -/
@[simp]
theorem
    abstractFixedFieldCyclotomicRestriction_infiniteGlobalArtinMonoidHom
    (H : FiniteAbstractField
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
    (a :
      IdeleGroup
        (LocalClassFieldTheory.abstractFixedField
          ℚ (SeparableClosure ℚ) H.field)) :
    let F :=
      LocalClassFieldTheory.abstractFixedField
        ℚ (SeparableClosure ℚ) H.field
    letI : FiniteDimensional ℚ F :=
      LocalClassFieldTheory.abstractFixedField_finiteDimensional
        ℚ (SeparableClosure ℚ) H.field H.finite
    letI : NumberField F :=
      NumberField.of_module_finite ℚ F
    let hI :=
      rationalCyclotomicFieldInertia_le H.field
    let U :=
      LocalClassFieldTheory.abstractRelativeFixedField
        ℚ (SeparableClosure ℚ) hI
    letI : IsAbelianGalois F U :=
      abstractFixedFieldCyclotomic_isAbelianGalois H
    abstractFixedFieldCyclotomicRestriction H
        (infiniteGlobalArtinMonoidHom F U a) =
      rationalCyclotomicZHatGlobalArtin
        (IdeleGroup.norm ℚ F a) := by
  exact
    abstractFixedFieldCyclotomicRestriction_infiniteGlobalArtin_inverseLimit
      H a

end Reciprocity
end GlobalClassFieldTheory
end
end

section
-- module Solutions.OAIQ244_DUKE.GlobalClassFieldTheory_Reciprocity_FiniteGaloisRealizationCore
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 400000
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.abstractFixedFieldCyclotomicFiniteCompositum_baseAlgebra _root_.GlobalClassFieldTheory.Reciprocity.abstractFixedFieldCyclotomicFiniteLayer_baseAlgebra _root_.GlobalClassFieldTheory.Reciprocity.abstractFixedFieldCyclotomicFiniteLayer_baseSMul _root_.GlobalClassFieldTheory.Reciprocity.abstractFixedFieldCyclotomicFiniteLayer_layerAlgebra _root_.GlobalClassFieldTheory.Reciprocity.abstractFixedFieldCyclotomicFiniteLayer_layerSMul _root_.GlobalClassFieldTheory.Reciprocity.infinitePlaceComplexificationOverfield_baseSmul _root_.GlobalClassFieldTheory.Reciprocity.infinitePlaceComplexificationOverfield_smul _root_.GlobalClassFieldTheory.Reciprocity.numberFieldTowerBaseSubgroupAbsoluteQuotientFinite _root_.GlobalClassFieldTheory.Reciprocity.numberFieldTowerExtensionQuotientFinite _root_.GlobalClassFieldTheory.Reciprocity.numberFieldTowerExtensionSubgroupNormal _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.LubinTate.padicCompletedLevelField_algebra _root_.LubinTate.padicCompletedUnramifiedFieldAlgebra _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.LocalClassFieldTheory.normalizationIntegerRingIsIntegralClosure _root_.chosenFinitePlaceCompletionAlgebra _root_.chosenFinitePlaceLocalizedIntegerAlgebra
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

instance numberFieldTowerBaseFieldScalarTower :
    IsScalarTower ℚ (numberFieldTowerBaseField K L)
      (numberFieldInRationalSeparableClosure L) :=
  IsScalarTower.of_algebraMap_eq' rfl

end Reciprocity
end GlobalClassFieldTheory
end
end

section
-- module Solutions.OAIQ244_DUKE.GlobalClassFieldTheory_Reciprocity_FiniteGaloisRealizationNormQuotient
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 400000
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.GlobalClassFields.ConductorialSubgroup.finiteIndex _root_.GlobalClassFieldTheory.GlobalClassFields.bigHilbertClassFieldNormSubgroup_normal _root_.GlobalClassFieldTheory.GlobalClassFields.finiteAbelianSubextensionAbstractRelativeFixedFieldFiniteDimensional _root_.GlobalClassFieldTheory.GlobalClassFields.finiteAbelianSubextensionAbstractRelativeFixedFieldIsAbelianGalois _root_.GlobalClassFieldTheory.GlobalClassFields.ideleClassNorm_rangeFiniteIndex _root_.GlobalClassFieldTheory.GlobalClassFields.smallHilbertClassFieldNormSubgroupFiniteIndex _root_.GlobalClassFieldTheory.Reciprocity.abstractFixedFieldCyclotomicCompositum_algebra _root_.GlobalClassFieldTheory.Reciprocity.abstractFixedFieldCyclotomicCompositum_baseScalarTower _root_.GlobalClassFieldTheory.Reciprocity.abstractFixedFieldCyclotomicCompositum_scalarTower _root_.GlobalClassFieldTheory.Reciprocity.abstractFixedFieldCyclotomicFiniteCompositum_baseAlgebra _root_.GlobalClassFieldTheory.Reciprocity.abstractFixedFieldCyclotomicFiniteCompositum_baseScalarTower _root_.GlobalClassFieldTheory.Reciprocity.abstractFixedFieldCyclotomicFiniteCompositum_numberField _root_.GlobalClassFieldTheory.Reciprocity.abstractFixedFieldCyclotomicFiniteGaloisLayer_scalarTower _root_.GlobalClassFieldTheory.Reciprocity.abstractFixedFieldCyclotomicFiniteLayer_baseAlgebra _root_.GlobalClassFieldTheory.Reciprocity.abstractFixedFieldCyclotomicFiniteLayer_baseModule _root_.GlobalClassFieldTheory.Reciprocity.abstractFixedFieldCyclotomicFiniteLayer_baseSMul _root_.GlobalClassFieldTheory.Reciprocity.abstractFixedFieldCyclotomicFiniteLayer_baseScalarTower _root_.GlobalClassFieldTheory.Reciprocity.abstractFixedFieldCyclotomicFiniteLayer_finiteDimensional _root_.GlobalClassFieldTheory.Reciprocity.abstractFixedFieldCyclotomicFiniteLayer_isAbelianGalois _root_.GlobalClassFieldTheory.Reciprocity.abstractFixedFieldCyclotomicFiniteLayer_layerAlgebra _root_.GlobalClassFieldTheory.Reciprocity.abstractFixedFieldCyclotomicFiniteLayer_layerSMul _root_.GlobalClassFieldTheory.Reciprocity.abstractFixedFieldCyclotomicFiniteLayer_layerScalarTower _root_.GlobalClassFieldTheory.Reciprocity.abstractFixedFieldCyclotomicFiniteLayer_numberField _root_.GlobalClassFieldTheory.Reciprocity.complexFourthRootField_numberField _root_.GlobalClassFieldTheory.Reciprocity.infinitePlaceComplexificationOverfield_numberField _root_.GlobalClassFieldTheory.Reciprocity.ramifiedInfinitePlaceRealFixedField_numberField _root_.KummerTheory.finite_finsupp_nsmulQuotient _root_.KummerTheory.finite_sUnit_nthPowerQuotient _root_.KummerTheory.primeCyclotomicBaseNumberField _root_.LocalClassFieldTheory.finiteUnramifiedNormQuotient _root_.LocalFieldTheory.DiscreteValuationField.finite_padicInt_finPi_nsmulQuotient _root_.LocalFieldTheory.DiscreteValuationField.finite_padicInt_pi_nsmulQuotient_of_coprime _root_.LocalFieldTheory.DiscreteValuationField.finite_valuationSubringUnits_nthPowerQuotient _root_.LocalFieldTheory.finite_multiplicative_nthPowerQuotient _root_.LocalFieldTheory.finite_nsmulAddQuotient_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.LubinTate.padicCompletedLevelField_algebra _root_.LubinTate.padicCompletedUnramifiedFieldAlgebra _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.boundedRealFields_finite _root_.OAI.PrimeDegreePackets.boundedRealFields_numberField _root_.OAI.PrimeDegreePackets.instTopologicalSpaceLocalAlgebra _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.CyclicCohomology.binaryCoefficientFamilyCommGroup _root_.GlobalClassFieldTheory.GlobalClassFields.bigHilbertNormQuotient_finite _root_.GlobalClassFieldTheory.GlobalClassFields.bigHilbertNormSubgroup_finiteIndex _root_.GlobalClassFieldTheory.GlobalClassFields.narrowClassGroup_finite _root_.LocalClassFieldTheory.normalizationIntegerRingIsIntegralClosure _root_.chosenFinitePlaceCompletionAlgebra _root_.relativeUnrestrictedSPlaceFactorCommGroup
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

attribute [local instance] towerNormIdeleClassCommGroup

variable
    (K L : Type) [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]

attribute [local instance] towerNormAbstractBaseNumberField

attribute [local instance] towerNormAbstractTopNumberField

attribute [local instance] towerNormAbstractNormQuotientCommGroup

/-- The ordinary idele class group of the original base field,
transported to the fixed part of the rational absolute idele-class
representation used by abstract reciprocity. -/
noncomputable def numberFieldTowerIdeleClassEquivAmbientFixed :
    Additive (IdeleClassGroup K) ≃+
      KummerTheory.ambientFixedAddSubgroup
        rationalIdeleClassRepresentation
        (numberFieldTowerBaseSubgroup K L) := by
  exact
    (MulEquiv.toAdditive
      (ideleClassCongr
        (numberFieldTowerAbstractBaseFieldEquiv K L))).trans
      (rationalAbstractFixedFieldIdeleClassEquivFixed
        (hfinite := numberFieldTowerBaseSubgroupAbsoluteQuotientFinite K L)
        (numberFieldTowerBaseSubgroup K L))

end Reciprocity
end GlobalClassFieldTheory
end
end


