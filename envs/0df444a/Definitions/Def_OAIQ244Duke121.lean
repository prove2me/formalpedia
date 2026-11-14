-- Prove2me | Definitions.Def_OAIQ244Duke121
-- name    : OAIQ244Duke121
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-14T03:42:52.504189+00:00
-- url     : https://prove2.me/theorems/e708d2a8-1379-4943-b688-05c4d82ab8c4
-- title:
--   Definitions bundle OAIQ244Duke121 of the split of OpenAI, Equidistribution of Prime-Degree Torus Packets with Arbitrary Local Type
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.DukePrimeDegree.prime_degree_packet_measure_equidistribution_unconditional` and `OAI.DukePrimeDegree.prime_degree_packet_measures_tendsto_haar_unconditional`, carved from OpenAI's openai/math development (OpenAI, *Equidistribution of Prime-Degree Torus Packets with Arbitrary Local Type*, OpenAI Math Release, September 24, 2026, result family 15, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 27 declarations of OpenAI's Lean: 8 definitions and 19 theorems. The definitions and types are `GlobalClassFieldTheory.Reciprocity.numberFieldEmbeddedActualNormClassRepresentativeValue`, `GlobalClassFieldTheory.Reciprocity.numberFieldEmbeddedExtensionQuotientEquivGaloisGroup`, `GlobalClassFieldTheory.Reciprocity.numberFieldEmbeddedFiniteGaloisSubextension`, `GlobalClassFieldTheory.Reciprocity.numberFieldEmbeddedFiniteNormClassDirectComparisonValue`, `GlobalClassFieldTheory.Reciprocity.numberFieldEmbeddedFiniteNormClassExpectedValue`, `GlobalClassFieldTheory.Reciprocity.numberFieldEmbeddedFiniteNormClassPublicValue`, `GlobalClassFieldTheory.Reciprocity.numberFieldEmbeddedFiniteNormQuotientEquivIdeleClassNormQuotient`, `GlobalClassFieldTheory.Reciprocity.numberFieldEmbeddedIdeleClassEquivAmbientFixed`.
--
--   **Sources.** They come from these modules of lean/OAI/NumberTheory, in whole or in part: `GlobalClassFieldTheory_Reciprocity_AbstractFixedFieldGlobalNormResidue`.
--
--   **Imports.** It imports the bundle `OAIQ244Duke102` of this split.
--
--   **Imported by** (directly, in this split): the bundle `OAIQ244Duke104`.
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
import Definitions.Def_OAIQ244Duke102

section
-- module Solutions.OAIQ244_DUKE.GlobalClassFieldTheory_Reciprocity_AbstractFixedFieldGlobalNormResidue
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 400000
attribute [-instance] _root_.GlobalClassFieldTheory.GlobalClassFields.ConductorialSubgroup.finiteIndex _root_.GlobalClassFieldTheory.GlobalClassFields.bigHilbertClassFieldNormSubgroup_normal _root_.GlobalClassFieldTheory.GlobalClassFields.ideleClassNorm_rangeFiniteIndex _root_.GlobalClassFieldTheory.GlobalClassFields.smallHilbertClassFieldNormSubgroupFiniteIndex _root_.GlobalClassFieldTheory.Reciprocity.abstractFixedFieldCyclotomicCompositum_algebra _root_.GlobalClassFieldTheory.Reciprocity.abstractFixedFieldCyclotomicCompositum_baseScalarTower _root_.GlobalClassFieldTheory.Reciprocity.abstractFixedFieldCyclotomicCompositum_scalarTower _root_.GlobalClassFieldTheory.Reciprocity.abstractFixedFieldCyclotomicFiniteCompositum_baseAlgebra _root_.GlobalClassFieldTheory.Reciprocity.abstractFixedFieldCyclotomicFiniteCompositum_baseScalarTower _root_.GlobalClassFieldTheory.Reciprocity.abstractFixedFieldCyclotomicFiniteCompositum_finiteDimensional _root_.GlobalClassFieldTheory.Reciprocity.abstractFixedFieldCyclotomicFiniteCompositum_numberField _root_.GlobalClassFieldTheory.Reciprocity.abstractFixedFieldCyclotomicFiniteGaloisLayer_scalarTower _root_.GlobalClassFieldTheory.Reciprocity.abstractFixedFieldCyclotomicFiniteLayer_baseAlgebra _root_.GlobalClassFieldTheory.Reciprocity.abstractFixedFieldCyclotomicFiniteLayer_baseModule _root_.GlobalClassFieldTheory.Reciprocity.abstractFixedFieldCyclotomicFiniteLayer_baseSMul _root_.GlobalClassFieldTheory.Reciprocity.abstractFixedFieldCyclotomicFiniteLayer_baseScalarTower _root_.GlobalClassFieldTheory.Reciprocity.abstractFixedFieldCyclotomicFiniteLayer_finiteDimensional _root_.GlobalClassFieldTheory.Reciprocity.abstractFixedFieldCyclotomicFiniteLayer_isAbelianGalois _root_.GlobalClassFieldTheory.Reciprocity.abstractFixedFieldCyclotomicFiniteLayer_layerAlgebra _root_.GlobalClassFieldTheory.Reciprocity.abstractFixedFieldCyclotomicFiniteLayer_layerSMul _root_.GlobalClassFieldTheory.Reciprocity.abstractFixedFieldCyclotomicFiniteLayer_layerScalarTower _root_.GlobalClassFieldTheory.Reciprocity.abstractFixedFieldCyclotomicFiniteLayer_numberField _root_.GlobalClassFieldTheory.Reciprocity.complexFourthRootField_finiteDimensional _root_.GlobalClassFieldTheory.Reciprocity.complexFourthRootField_numberField _root_.GlobalClassFieldTheory.Reciprocity.infinitePlaceComplexificationOverfield_baseSmul _root_.GlobalClassFieldTheory.Reciprocity.infinitePlaceComplexificationOverfield_finiteDimensional _root_.GlobalClassFieldTheory.Reciprocity.infinitePlaceComplexificationOverfield_numberField _root_.GlobalClassFieldTheory.Reciprocity.infinitePlaceComplexificationOverfield_smul _root_.GlobalClassFieldTheory.Reciprocity.ramifiedInfinitePlaceRealFixedField_numberField _root_.GlobalClassFieldTheory.Reciprocity.rationalComplexification_infinitePlaceOverfield_algebra _root_.GlobalClassFieldTheory.Reciprocity.rationalComplexification_infinitePlaceOverfield_smul _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.boundedRealFields_finite _root_.OAI.PrimeDegreePackets.boundedRealFields_numberField _root_.OAI.PrimeDegreePackets.instTopologicalSpaceLocalAlgebra _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.GlobalClassFieldTheory.GlobalClassFields.bigHilbertNormQuotient_finite _root_.GlobalClassFieldTheory.GlobalClassFields.bigHilbertNormSubgroup_finiteIndex _root_.GlobalClassFieldTheory.GlobalClassFields.narrowClassGroup_finite
attribute [-simp] _root_.ClassFormation.FiniteAbelianSubextension.normSubgroupMap_val _root_.ClassFormation.FiniteGaloisSubextension.classFieldCandidate_field _root_.GlobalClassFieldTheory.ClassFieldAxiom.hasseNormDiagonal_mk _root_.GlobalClassFieldTheory.GlobalClassFields.ConductorialSubgroup.ideleClassQuotientEquivOfNarrowFiniteConductorsEqOfRayClassGroupCardsEqQuotientCards_mk _root_.GlobalClassFieldTheory.GlobalClassFields.ConductorialSubgroup.mem_fullConductorInfinitePart_iff _root_.GlobalClassFieldTheory.GlobalClassFields.ConductorialSubgroup.narrowFiniteConductorRayClassGroupEquivQuotientOfCardEq_mk _root_.GlobalClassFieldTheory.GlobalClassFields.ConductorialSubgroup.narrowFiniteConductorRayClassGroupToQuotient_mk _root_.GlobalClassFieldTheory.GlobalClassFields.bigHilbertClassFieldQuotientCongr_mk _root_.GlobalClassFieldTheory.GlobalClassFields.bigHilbertClassFieldQuotientEquivNarrowClassGroup_mk _root_.GlobalClassFieldTheory.GlobalClassFields.bigHilbertClassFieldQuotientToIdeleClassNormQuotient_mk _root_.GlobalClassFieldTheory.GlobalClassFields.bigHilbertClassFieldQuotientToSmallHilbertClassFieldQuotient_mk _root_.GlobalClassFieldTheory.GlobalClassFields.ideleClassNormQuotientTowerMap_mk _root_.GlobalClassFieldTheory.GlobalClassFields.narrowFiniteConductorRayClassGroupToIdeleClassNormQuotient_mk _root_.GlobalClassFieldTheory.GlobalClassFields.normQuotientEquivOfNarrowFiniteConductorsEqOfRayClassGroupCardsEqNormQuotientCards_mk _root_.GlobalClassFieldTheory.GlobalClassFields.realSignToBigHilbertClassFieldQuotient_apply _root_.GlobalClassFieldTheory.GlobalClassFields.realSignToNarrowClassKernel_apply _root_.GlobalClassFieldTheory.GlobalClassFields.smallHilbertClassFieldQuotientCongr_mk _root_.GlobalClassFieldTheory.GlobalClassFields.smallHilbertClassFieldQuotientEquivClassGroup_mk _root_.GlobalClassFieldTheory.GlobalClassFields.smallHilbertClassFieldQuotientToIdeleClassNormQuotient_mk _root_.GlobalClassFieldTheory.IdealClassFieldTheory.smallHilbertClassFieldIdeleExtensionMap_mk' _root_.GlobalClassFieldTheory.Reciprocity.abstractFixedFieldCyclotomicIdeleClassArtinMonoidHom_mk _root_.GlobalClassFieldTheory.Reciprocity.abstractFixedFieldCyclotomicRestriction_infiniteGlobalArtinMonoidHom _root_.GlobalClassFieldTheory.Reciprocity.globalNormClassFromIdele_principalIdele _root_.GlobalClassFieldTheory.Reciprocity.globalNormClassFromIdele_relativeIdeleNorm_eq_one _root_.GlobalClassFieldTheory.Reciprocity.infiniteGlobalArtinMonoidHom_abstractFixedFieldCyclotomic_principalIdele _root_.GlobalClassFieldTheory.Reciprocity.mem_globalArtinFiniteSupport_iff _root_.GlobalClassFieldTheory.Reciprocity.rationalComplexificationGlobalArtin_principalIdele _root_.IdeleGroup.count_fractionalIdeal _root_.IdeleGroup.fractionalIdeal_finitePrimeIdele _root_.IdeleGroup.idealClass_finitePrimeIdele _root_.OAI.PrimeDegreePackets.ThetaConstruction.schwartzCM_apply _root_.RayClass.signToNarrow_mk
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
# Global norm residue on actual fixed fields

An abstract finite abelian subextension of the rational absolute Galois
group determines an actual finite abelian extension between its two
fixed number fields.  This file transports the abstract norm-residue
symbol directly to the ordinary idele-class norm quotient of those
fixed fields.

Keeping this construction in one ambient separable closure is essential
for the norm--restriction diagrams: no independently chosen embedding of
either field is introduced.
-/

open scoped IsMulCommutative NumberField
open NumberField

noncomputable section

namespace GlobalClassFieldTheory
namespace Reciprocity

open ClassFormation
open GlobalClassFields
open KummerTheory
open AlgebraicNumberTheory
open LocalClassFieldTheory
open RamificationTheory

section EmbeddedNumberFieldRealization

attribute [local instance] GlobalClassFieldTheory.Reciprocity.numberFieldEmbeddedIdeleClassGroupIsMulCommutative
attribute [local instance] GlobalClassFieldTheory.Reciprocity.numberFieldEmbeddedIdeleClassSubgroupNormal
variable
    (K L : Type) [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]

/-- The relative subgroup arising from an explicit compatible
number-field embedding is normal. -/
theorem numberFieldEmbeddedExtensionSubgroup_normal
    [FiniteDimensional K L] [IsGalois K L]
    (j : L →ₐ[ℚ] SeparableClosure ℚ) :
    (CyclicCohomology.extensionSubgroup
      (numberFieldEmbeddedBaseSubgroup K L j)
      (numberFieldEmbeddedTopSubgroup K L j)
      (numberFieldEmbeddedTopSubgroup_le_baseSubgroup K L j)).Normal := by
  let i := numberFieldEmbeddedLowerEmbedding K L j
  let hAlgebra : Algebra K (SeparableClosure ℚ) :=
    numberFieldEmbeddedSeparableClosureAlgebra K L j
  let e := numberFieldEmbeddedSeparableClosureEquiv K L j
  change
    (CyclicCohomology.extensionSubgroup
      (closedFixingSubgroup ℚ (SeparableClosure ℚ)
        (AlgHom.fieldRange i))
      (closedFixingSubgroup ℚ (SeparableClosure ℚ)
        (AlgHom.fieldRange j)) _).Normal
  exact ambientEmbeddedExtensionSubgroup_normal ℚ K L j e

/-- The normality witness for an explicitly embedded tower, registered at
the precise subgroup used by the downstream quotient constructions. -/
noncomputable local instance
    numberFieldEmbeddedExtensionSubgroupNormal
    [FiniteDimensional K L] [IsGalois K L]
    (j : L →ₐ[ℚ] SeparableClosure ℚ) :
    (CyclicCohomology.extensionSubgroup
      (numberFieldEmbeddedBaseSubgroup K L j)
      (numberFieldEmbeddedTopSubgroup K L j)
      (numberFieldEmbeddedTopSubgroup_le_baseSubgroup K L j)).Normal :=
  numberFieldEmbeddedExtensionSubgroup_normal K L j

/-- The relative quotient arising from an explicit compatible
number-field embedding is finite. -/
theorem numberFieldEmbeddedExtensionQuotient_finite
    [FiniteDimensional K L] [IsGalois K L]
    (j : L →ₐ[ℚ] SeparableClosure ℚ) :
    Finite
      ((numberFieldEmbeddedBaseSubgroup K L j).toSubgroup ⧸
        CyclicCohomology.extensionSubgroup
          (numberFieldEmbeddedBaseSubgroup K L j)
          (numberFieldEmbeddedTopSubgroup K L j)
          (numberFieldEmbeddedTopSubgroup_le_baseSubgroup K L j)) := by
  let i := numberFieldEmbeddedLowerEmbedding K L j
  let hAlgebra : Algebra K (SeparableClosure ℚ) :=
    numberFieldEmbeddedSeparableClosureAlgebra K L j
  let e := numberFieldEmbeddedSeparableClosureEquiv K L j
  change
    Finite
      ((closedFixingSubgroup ℚ (SeparableClosure ℚ)
          (AlgHom.fieldRange i)).toSubgroup ⧸
        CyclicCohomology.extensionSubgroup
          (closedFixingSubgroup ℚ (SeparableClosure ℚ)
            (AlgHom.fieldRange i))
          (closedFixingSubgroup ℚ (SeparableClosure ℚ)
            (AlgHom.fieldRange j)) _)
  exact ambientEmbeddedExtensionQuotient_finite ℚ K L j e

/-- The relative-index witness for an explicitly embedded tower, registered
at the exact quotient consumed by `FiniteNormQuotient`. -/
noncomputable local instance
    numberFieldEmbeddedExtensionQuotientFinite
    [FiniteDimensional K L] [IsGalois K L]
    (j : L →ₐ[ℚ] SeparableClosure ℚ) :
    Finite
      ((numberFieldEmbeddedBaseSubgroup K L j).toSubgroup ⧸
        CyclicCohomology.extensionSubgroup
          (numberFieldEmbeddedBaseSubgroup K L j)
          (numberFieldEmbeddedTopSubgroup K L j)
          (numberFieldEmbeddedTopSubgroup_le_baseSubgroup K L j)) :=
  numberFieldEmbeddedExtensionQuotient_finite K L j

/-- The absolute-index witness for the lower member of an explicitly embedded
tower, registered at its specialized quotient type. -/
noncomputable local instance
    numberFieldEmbeddedAbsoluteQuotientFinite
    (j : L →ₐ[ℚ] SeparableClosure ℚ) :
    Finite
      ((baseField
        (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ)).toSubgroup ⧸
        CyclicCohomology.extensionSubgroup
          (baseField
            (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
          (numberFieldEmbeddedBaseSubgroup K L j)
          (le_baseField
            (numberFieldEmbeddedBaseSubgroup K L j))) :=
  (numberFieldEmbeddedFiniteAbstractField K L j).finite

/-- The finite Galois subextension determined by an explicitly embedded
number-field tower. -/
noncomputable abbrev numberFieldEmbeddedFiniteGaloisSubextension
    [FiniteDimensional K L] [IsGalois K L]
    (j : L →ₐ[ℚ] SeparableClosure ℚ) :
    FiniteGaloisSubextension
      (numberFieldEmbeddedBaseSubgroup K L j) where
  field := numberFieldEmbeddedTopSubgroup K L j
  below := numberFieldEmbeddedTopSubgroup_le_baseSubgroup K L j
  normal := numberFieldEmbeddedExtensionSubgroup_normal K L j
  finite := numberFieldEmbeddedExtensionQuotient_finite K L j

/-- Shared finite-dimensional data for the fixed field of the lower subgroup
in an explicitly embedded number-field tower. -/
noncomputable local instance
    numberFieldEmbeddedAbstractFixedFieldFiniteDimensional
    (j : L →ₐ[ℚ] SeparableClosure ℚ) :
    FiniteDimensional ℚ
      (abstractFixedField ℚ (SeparableClosure ℚ)
        (numberFieldEmbeddedBaseSubgroup K L j)) :=
  abstractFixedField_finiteDimensional
    ℚ (SeparableClosure ℚ)
    (numberFieldEmbeddedBaseSubgroup K L j)
    (numberFieldEmbeddedAbsoluteQuotientFinite K L j)

/-- Shared relative finite-dimensional data for the two fixed fields of an
explicitly embedded number-field tower. -/
noncomputable local instance
    numberFieldEmbeddedAbstractRelativeFixedFieldFiniteDimensional
    [FiniteDimensional K L] [IsGalois K L]
    (j : L →ₐ[ℚ] SeparableClosure ℚ) :
    FiniteDimensional
      (abstractFixedField ℚ (SeparableClosure ℚ)
        (numberFieldEmbeddedBaseSubgroup K L j))
      (abstractRelativeFixedField ℚ (SeparableClosure ℚ)
        (numberFieldEmbeddedTopSubgroup_le_baseSubgroup K L j)) :=
  abstractRelativeFixedField_finiteDimensional
    ℚ (SeparableClosure ℚ)
    (numberFieldEmbeddedBaseSubgroup K L j)
    (numberFieldEmbeddedTopSubgroup K L j)
    (numberFieldEmbeddedTopSubgroup_le_baseSubgroup K L j)
    (numberFieldEmbeddedAbsoluteQuotientFinite K L j)
    (numberFieldEmbeddedExtensionQuotientFinite K L j)

local instance numberFieldEmbeddedAbstractFixedFieldScalarTower
    (j : L →ₐ[ℚ] SeparableClosure ℚ) :
    IsScalarTower ℚ
      (abstractFixedField ℚ (SeparableClosure ℚ)
        (numberFieldEmbeddedBaseSubgroup K L j))
      (abstractRelativeFixedField ℚ (SeparableClosure ℚ)
        (numberFieldEmbeddedTopSubgroup_le_baseSubgroup K L j)) :=
  IsScalarTower.of_algebraMap_eq' (RingHom.ext_rat _ _)

noncomputable local instance
    numberFieldEmbeddedAbstractRelativeFixedFieldAbsoluteFiniteDimensional
    [FiniteDimensional K L] [IsGalois K L]
    (j : L →ₐ[ℚ] SeparableClosure ℚ) :
    FiniteDimensional ℚ
      (abstractRelativeFixedField ℚ (SeparableClosure ℚ)
        (numberFieldEmbeddedTopSubgroup_le_baseSubgroup K L j)) :=
  FiniteDimensional.trans ℚ
    (abstractFixedField ℚ (SeparableClosure ℚ)
      (numberFieldEmbeddedBaseSubgroup K L j))
    (abstractRelativeFixedField ℚ (SeparableClosure ℚ)
      (numberFieldEmbeddedTopSubgroup_le_baseSubgroup K L j))

noncomputable local instance
    numberFieldEmbeddedAbstractFixedFieldNumberField
    (j : L →ₐ[ℚ] SeparableClosure ℚ) :
    NumberField
      (abstractFixedField ℚ (SeparableClosure ℚ)
        (numberFieldEmbeddedBaseSubgroup K L j)) :=
  NumberField.of_module_finite ℚ
    (abstractFixedField ℚ (SeparableClosure ℚ)
      (numberFieldEmbeddedBaseSubgroup K L j))

noncomputable local instance
    numberFieldEmbeddedAbstractRelativeFixedFieldNumberField
    [FiniteDimensional K L] [IsGalois K L]
    (j : L →ₐ[ℚ] SeparableClosure ℚ) :
    NumberField
      (abstractRelativeFixedField ℚ (SeparableClosure ℚ)
        (numberFieldEmbeddedTopSubgroup_le_baseSubgroup K L j)) :=
  NumberField.of_module_finite ℚ
    (abstractRelativeFixedField ℚ (SeparableClosure ℚ)
      (numberFieldEmbeddedTopSubgroup_le_baseSubgroup K L j))

noncomputable local instance
    numberFieldEmbeddedAbstractRelativeFixedFieldRestrictScalarsFiniteDimensional
    [FiniteDimensional K L] [IsGalois K L]
    (j : L →ₐ[ℚ] SeparableClosure ℚ) :
    FiniteDimensional ℚ
      ((abstractRelativeFixedField ℚ (SeparableClosure ℚ)
        (numberFieldEmbeddedTopSubgroup_le_baseSubgroup K L j)).restrictScalars ℚ) := by
  change FiniteDimensional ℚ
    (abstractRelativeFixedField ℚ (SeparableClosure ℚ)
      (numberFieldEmbeddedTopSubgroup_le_baseSubgroup K L j))
  infer_instance

noncomputable local instance
    numberFieldEmbeddedAbstractRelativeFixedFieldRestrictScalarsNumberField
    [FiniteDimensional K L] [IsGalois K L]
    (j : L →ₐ[ℚ] SeparableClosure ℚ) :
    NumberField
      ((abstractRelativeFixedField ℚ (SeparableClosure ℚ)
        (numberFieldEmbeddedTopSubgroup_le_baseSubgroup K L j)).restrictScalars ℚ) :=
  NumberField.of_module_finite ℚ _

noncomputable local instance
    numberFieldEmbeddedAbstractRelativeFixedFieldRestrictScalarsAlgebra_re9243d_1
    [FiniteDimensional K L] [IsGalois K L]
    (j : L →ₐ[ℚ] SeparableClosure ℚ) :
    Algebra
      (abstractFixedField ℚ (SeparableClosure ℚ)
        (numberFieldEmbeddedBaseSubgroup K L j))
      ((abstractRelativeFixedField ℚ (SeparableClosure ℚ)
        (numberFieldEmbeddedTopSubgroup_le_baseSubgroup K L j)).restrictScalars ℚ) :=
  (IntermediateField.inclusion
    (abstractFixedField_le ℚ (SeparableClosure ℚ)
      (numberFieldEmbeddedTopSubgroup_le_baseSubgroup K L j))).toRingHom.toAlgebra
noncomputable local instance
    numberFieldEmbeddedAbstractRelativeFixedFieldIsGalois_re9243d_1
    [FiniteDimensional K L] [IsGalois K L]
    (j : L →ₐ[ℚ] SeparableClosure ℚ) :
    IsGalois
      (abstractFixedField ℚ (SeparableClosure ℚ)
        (numberFieldEmbeddedBaseSubgroup K L j))
      (abstractRelativeFixedField ℚ (SeparableClosure ℚ)
        (numberFieldEmbeddedTopSubgroup_le_baseSubgroup K L j)) :=
  abstractRelativeFixedField_isGalois
    ℚ (SeparableClosure ℚ)
    (numberFieldEmbeddedBaseSubgroup K L j)
    (numberFieldEmbeddedTopSubgroup K L j)
    (numberFieldEmbeddedTopSubgroup_le_baseSubgroup K L j)
    (numberFieldEmbeddedExtensionSubgroupNormal K L j)
/-- The quotient of the two explicitly embedded fixing subgroups is
the actual relative Galois group. -/
noncomputable def
    numberFieldEmbeddedExtensionQuotientEquivGaloisGroup
    [FiniteDimensional K L] [IsGalois K L]
    (j : L →ₐ[ℚ] SeparableClosure ℚ) :
    (numberFieldEmbeddedFiniteGaloisSubextension K L j).extensionQuotient ≃*
      Gal(L / K) := by
  let i := numberFieldEmbeddedLowerEmbedding K L j
  letI hAlgebra : Algebra K (SeparableClosure ℚ) :=
    numberFieldEmbeddedSeparableClosureAlgebra K L j
  let e := numberFieldEmbeddedSeparableClosureEquiv K L j
  let H₀ :=
    closedFixingSubgroup ℚ (SeparableClosure ℚ)
      (AlgHom.fieldRange i)
  let J₀ :=
    closedFixingSubgroup ℚ (SeparableClosure ℚ)
      (AlgHom.fieldRange j)
  let hJH : J₀.toSubgroup ≤ H₀.toSubgroup := by
    change j.fieldRange.fixingSubgroup ≤ i.fieldRange.fixingSubgroup
    apply i.fieldRange.fixingSubgroup_le
    intro x hx
    rcases hx with ⟨y, rfl⟩
    exact ⟨algebraMap K L y, rfl⟩
  letI : (CyclicCohomology.extensionSubgroup H₀ J₀ hJH).Normal :=
    ambientEmbeddedExtensionSubgroup_normal ℚ K L j e
  change
    (H₀.toSubgroup ⧸
        CyclicCohomology.extensionSubgroup H₀ J₀ hJH) ≃*
      Gal(L / K)
  exact ambientEmbeddedExtensionQuotientEquivGaloisGroup ℚ K L j e

/-- The ordinary idele class group of the explicitly embedded lower
field, transported to the fixed part of the rational absolute
idele-class representation. -/
noncomputable def numberFieldEmbeddedIdeleClassEquivAmbientFixed
    (j : L →ₐ[ℚ] SeparableClosure ℚ) :
    Additive (IdeleClassGroup K) ≃+
      ambientFixedAddSubgroup
        rationalIdeleClassRepresentation
        (numberFieldEmbeddedBaseSubgroup K L j) := by
  let H := numberFieldEmbeddedBaseSubgroup K L j
  exact
    (MulEquiv.toAdditive
      (ideleClassCongr
        (numberFieldEmbeddedAbstractBaseFieldEquiv K L j))).trans
      (rationalAbstractFixedFieldIdeleClassEquivFixed H)

/-- The abstract finite norm quotient of an explicitly embedded tower
is its genuine ordinary idele-class norm quotient. -/
noncomputable def
    numberFieldEmbeddedFiniteNormQuotientEquivIdeleClassNormQuotient
    [FiniteDimensional K L] [IsGalois K L]
    (j : L →ₐ[ℚ] SeparableClosure ℚ) :
    FiniteNormQuotient rationalIdeleClassRepresentation
        (numberFieldEmbeddedBaseSubgroup K L j)
        (numberFieldEmbeddedTopSubgroup K L j)
        (numberFieldEmbeddedTopSubgroup_le_baseSubgroup K L j) ≃+
      Additive
        (IdeleClassGroup K ⧸
          (_root_.ideleClassNorm K L).range) := by
  let hnormal :=
    numberFieldEmbeddedExtensionSubgroupNormal K L j
  let H := numberFieldEmbeddedBaseSubgroup K L j
  let J := numberFieldEmbeddedTopSubgroup K L j
  let hJH :=
    numberFieldEmbeddedTopSubgroup_le_baseSubgroup K L j
  let fixedFieldEquiv :=
    rationalFiniteNormQuotientEquivIdeleClassNormQuotient
      H J hJH hnormal
  let actualFieldEquiv :=
    ordinaryIdeleClassNormQuotientCongrOfAlgEquiv
      (numberFieldEmbeddedAbstractBaseFieldEquiv K L j)
      (numberFieldEmbeddedAbstractTopFieldEquiv K L j)
      (numberFieldEmbeddedAbstractFieldEquiv_algebraMap K L j)
  exact
    fixedFieldEquiv.trans
      (MulEquiv.toAdditive actualFieldEquiv.symm)

theorem numberFieldEmbeddedOrdinaryNormQuotientCongr_symm_mk
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

noncomputable def numberFieldEmbeddedFiniteNormClassPublicValue
    [FiniteDimensional K L] [IsGalois K L]
    (j : L →ₐ[ℚ] SeparableClosure ℚ)
    (a : ambientFixedAddSubgroup rationalIdeleClassRepresentation
      (numberFieldEmbeddedBaseSubgroup K L j)) :
    Additive
      (IdeleClassGroup K ⧸
        (_root_.ideleClassNorm K L).range) :=
    numberFieldEmbeddedFiniteNormQuotientEquivIdeleClassNormQuotient
        K L j
        (finiteNormClass rationalIdeleClassRepresentation
          (numberFieldEmbeddedBaseSubgroup K L j)
          (numberFieldEmbeddedTopSubgroup K L j)
          (numberFieldEmbeddedTopSubgroup_le_baseSubgroup K L j)
          a)

noncomputable def numberFieldEmbeddedFiniteNormClassExpectedValue
    [FiniteDimensional K L] [IsGalois K L]
    (j : L →ₐ[ℚ] SeparableClosure ℚ)
    (a : ambientFixedAddSubgroup rationalIdeleClassRepresentation
      (numberFieldEmbeddedBaseSubgroup K L j)) :
    Additive
      (IdeleClassGroup K ⧸
        (_root_.ideleClassNorm K L).range) :=
  Additive.ofMul
    (QuotientGroup.mk'
      (_root_.ideleClassNorm K L).range
      (Additive.toMul
        ((numberFieldEmbeddedIdeleClassEquivAmbientFixed K L j).symm a)))

noncomputable def
    numberFieldEmbeddedFiniteNormClassDirectComparisonValue
    [FiniteDimensional K L] [IsGalois K L]
    (j : L →ₐ[ℚ] SeparableClosure ℚ)
    (a : ambientFixedAddSubgroup rationalIdeleClassRepresentation
      (numberFieldEmbeddedBaseSubgroup K L j)) :
    Additive
      (IdeleClassGroup K ⧸
        (_root_.ideleClassNorm K L).range) := by
  let hnormal :=
    numberFieldEmbeddedExtensionSubgroupNormal K L j
  let H := numberFieldEmbeddedBaseSubgroup K L j
  let J := numberFieldEmbeddedTopSubgroup K L j
  let hJH :=
    numberFieldEmbeddedTopSubgroup_le_baseSubgroup K L j
  let fixedFieldEquiv :=
    rationalFiniteNormQuotientEquivIdeleClassNormQuotient
      H J hJH hnormal
  let actualFieldEquiv :=
    ordinaryIdeleClassNormQuotientCongrOfAlgEquiv
      (numberFieldEmbeddedAbstractBaseFieldEquiv K L j)
      (numberFieldEmbeddedAbstractTopFieldEquiv K L j)
      (numberFieldEmbeddedAbstractFieldEquiv_algebraMap K L j)
  exact
    MulEquiv.toAdditive actualFieldEquiv.symm
      (fixedFieldEquiv
        (finiteNormClass rationalIdeleClassRepresentation
          H J hJH a))

theorem
    numberFieldEmbeddedFiniteNormClassPublicValue_eq_directComparison
    [FiniteDimensional K L] [IsGalois K L]
    (j : L →ₐ[ℚ] SeparableClosure ℚ)
    (a : ambientFixedAddSubgroup rationalIdeleClassRepresentation
      (numberFieldEmbeddedBaseSubgroup K L j)) :
    numberFieldEmbeddedFiniteNormClassPublicValue K L j a =
      numberFieldEmbeddedFiniteNormClassDirectComparisonValue K L j a := by
  unfold numberFieldEmbeddedFiniteNormClassPublicValue
  unfold numberFieldEmbeddedFiniteNormQuotientEquivIdeleClassNormQuotient
  unfold numberFieldEmbeddedFiniteNormClassDirectComparisonValue
  rfl

noncomputable def numberFieldEmbeddedActualNormClassRepresentativeValue
    [FiniteDimensional K L] [IsGalois K L]
    (j : L →ₐ[ℚ] SeparableClosure ℚ)
    (a : ambientFixedAddSubgroup rationalIdeleClassRepresentation
      (numberFieldEmbeddedBaseSubgroup K L j)) :
    Additive
      (IdeleClassGroup K ⧸
        (_root_.ideleClassNorm K L).range) := by
  let H := numberFieldEmbeddedBaseSubgroup K L j
  let hJH := numberFieldEmbeddedTopSubgroup_le_baseSubgroup K L j
  let F := abstractFixedField ℚ (SeparableClosure ℚ) H
  let E := abstractRelativeFixedField ℚ (SeparableClosure ℚ) hJH
  let actualFieldEquiv :=
    ordinaryIdeleClassNormQuotientCongrOfAlgEquiv
      (numberFieldEmbeddedAbstractBaseFieldEquiv K L j)
      (numberFieldEmbeddedAbstractTopFieldEquiv K L j)
      (numberFieldEmbeddedAbstractFieldEquiv_algebraMap K L j)
  exact
    Additive.ofMul
      (actualFieldEquiv.symm
        (QuotientGroup.mk'
          (_root_.ideleClassNorm F E).range
          (Additive.toMul
            ((rationalAbstractFixedFieldIdeleClassEquivFixed H).symm a))))

theorem
    numberFieldEmbeddedFiniteNormClassDirectComparison_eq_actualValue
    [FiniteDimensional K L] [IsGalois K L]
    (j : L →ₐ[ℚ] SeparableClosure ℚ)
    (a : ambientFixedAddSubgroup rationalIdeleClassRepresentation
      (numberFieldEmbeddedBaseSubgroup K L j)) :
    numberFieldEmbeddedFiniteNormClassDirectComparisonValue K L j a =
      numberFieldEmbeddedActualNormClassRepresentativeValue K L j a := by
  let hnormal := numberFieldEmbeddedExtensionSubgroupNormal K L j
  let H := numberFieldEmbeddedBaseSubgroup K L j
  let J := numberFieldEmbeddedTopSubgroup K L j
  let hJH := numberFieldEmbeddedTopSubgroup_le_baseSubgroup K L j
  let actualFieldEquiv :=
    ordinaryIdeleClassNormQuotientCongrOfAlgEquiv
      (numberFieldEmbeddedAbstractBaseFieldEquiv K L j)
      (numberFieldEmbeddedAbstractTopFieldEquiv K L j)
      (numberFieldEmbeddedAbstractFieldEquiv_algebraMap K L j)
  have hfixed :=
    rationalFiniteNormQuotientEquivIdeleClassNormQuotient_finiteNormClass
      H J hJH hnormal a
  unfold numberFieldEmbeddedFiniteNormClassDirectComparisonValue
  unfold numberFieldEmbeddedActualNormClassRepresentativeValue
  exact congrArg (MulEquiv.toAdditive actualFieldEquiv.symm) hfixed

theorem numberFieldEmbeddedActualNormClassRepresentativeValue_eq_expected
    [FiniteDimensional K L] [IsGalois K L]
    (j : L →ₐ[ℚ] SeparableClosure ℚ)
    (a : ambientFixedAddSubgroup rationalIdeleClassRepresentation
      (numberFieldEmbeddedBaseSubgroup K L j)) :
    numberFieldEmbeddedActualNormClassRepresentativeValue K L j a =
      numberFieldEmbeddedFiniteNormClassExpectedValue K L j a := by
  let H := numberFieldEmbeddedBaseSubgroup K L j
  let hJH := numberFieldEmbeddedTopSubgroup_le_baseSubgroup K L j
  let F := abstractFixedField ℚ (SeparableClosure ℚ) H
  let E := abstractRelativeFixedField ℚ (SeparableClosure ℚ) hJH
  let actualFieldEquiv :=
    ordinaryIdeleClassNormQuotientCongrOfAlgEquiv
      (numberFieldEmbeddedAbstractBaseFieldEquiv K L j)
      (numberFieldEmbeddedAbstractTopFieldEquiv K L j)
      (numberFieldEmbeddedAbstractFieldEquiv_algebraMap K L j)
  let c : IdeleClassGroup F :=
    Additive.toMul
      ((rationalAbstractFixedFieldIdeleClassEquivFixed H).symm a)
  unfold numberFieldEmbeddedActualNormClassRepresentativeValue
  unfold numberFieldEmbeddedFiniteNormClassExpectedValue
  change
    Additive.ofMul
        (actualFieldEquiv.symm
          (QuotientGroup.mk'
            (_root_.ideleClassNorm F E).range c)) =
      Additive.ofMul
        (QuotientGroup.mk'
          (_root_.ideleClassNorm K L).range
          ((ideleClassCongr
            (numberFieldEmbeddedAbstractBaseFieldEquiv K L j)).symm c))
  exact
    congrArg Additive.ofMul
      (numberFieldEmbeddedOrdinaryNormQuotientCongr_symm_mk
        (numberFieldEmbeddedAbstractBaseFieldEquiv K L j)
        (numberFieldEmbeddedAbstractTopFieldEquiv K L j)
        (numberFieldEmbeddedAbstractFieldEquiv_algebraMap K L j) c)

/-- On a finite norm-class representative, the explicit fixed-field
comparison is the genuine ordinary idele-class quotient. -/
@[simp]
theorem
    numberFieldEmbeddedFiniteNormQuotientEquivIdeleClassNormQuotient_finiteNormClass
    [FiniteDimensional K L] [IsGalois K L]
    (j : L →ₐ[ℚ] SeparableClosure ℚ)
    (a : ambientFixedAddSubgroup rationalIdeleClassRepresentation
      (numberFieldEmbeddedBaseSubgroup K L j)) :
    numberFieldEmbeddedFiniteNormQuotientEquivIdeleClassNormQuotient K L j
        (finiteNormClass rationalIdeleClassRepresentation
          (numberFieldEmbeddedBaseSubgroup K L j)
          (numberFieldEmbeddedTopSubgroup K L j)
          (numberFieldEmbeddedTopSubgroup_le_baseSubgroup K L j) a) =
      Additive.ofMul
        (QuotientGroup.mk'
          (_root_.ideleClassNorm K L).range
          (Additive.toMul
            ((numberFieldEmbeddedIdeleClassEquivAmbientFixed K L j).symm a))) := by
  change
    numberFieldEmbeddedFiniteNormClassPublicValue K L j a =
      numberFieldEmbeddedFiniteNormClassExpectedValue K L j a
  exact
    (numberFieldEmbeddedFiniteNormClassPublicValue_eq_directComparison
      K L j a).trans
      ((numberFieldEmbeddedFiniteNormClassDirectComparison_eq_actualValue
        K L j a).trans
        (numberFieldEmbeddedActualNormClassRepresentativeValue_eq_expected
          K L j a))

/-- On an ordinary idele class, the explicit fixed-part realization
followed by the abstract finite norm-class map is the genuine quotient
class modulo the ordinary idele-class norm. -/
@[simp]
theorem
    numberFieldEmbeddedFiniteNormQuotientEquivIdeleClassNormQuotient_ideleClass
    [FiniteDimensional K L] [IsGalois K L]
    (j : L →ₐ[ℚ] SeparableClosure ℚ)
    (c : IdeleClassGroup K) :
    numberFieldEmbeddedFiniteNormQuotientEquivIdeleClassNormQuotient K L j
        (finiteNormClass rationalIdeleClassRepresentation
          (numberFieldEmbeddedBaseSubgroup K L j)
          (numberFieldEmbeddedTopSubgroup K L j)
          (numberFieldEmbeddedTopSubgroup_le_baseSubgroup K L j)
          (numberFieldEmbeddedIdeleClassEquivAmbientFixed
            K L j (Additive.ofMul c))) =
      Additive.ofMul
        (QuotientGroup.mk'
          (_root_.ideleClassNorm K L).range c) := by
  simpa only [AddEquiv.symm_apply_apply, toMul_ofMul] using
    (numberFieldEmbeddedFiniteNormQuotientEquivIdeleClassNormQuotient_finiteNormClass
      K L j
      (numberFieldEmbeddedIdeleClassEquivAmbientFixed
        K L j (Additive.ofMul c)))

end EmbeddedNumberFieldRealization

end Reciprocity
end GlobalClassFieldTheory
end
end


