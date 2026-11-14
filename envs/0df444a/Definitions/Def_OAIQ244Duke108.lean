-- Prove2me | Definitions.Def_OAIQ244Duke108
-- name    : OAIQ244Duke108
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-14T04:25:34.326683+00:00
-- url     : https://prove2.me/theorems/dd8e24e2-6182-4fc3-aa70-66d4fad39b26
-- title:
--   Definitions bundle OAIQ244Duke108 of the split of OpenAI, Equidistribution of Prime-Degree Torus Packets with Arbitrary Local Type
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.DukePrimeDegree.prime_degree_packet_measure_equidistribution_unconditional` and `OAI.DukePrimeDegree.prime_degree_packet_measures_tendsto_haar_unconditional`, carved from OpenAI's openai/math development (OpenAI, *Equidistribution of Prime-Degree Torus Packets with Arbitrary Local Type*, OpenAI Math Release, September 24, 2026, result family 15, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 56 declarations of OpenAI's Lean: 16 definitions, 1 instance and 39 theorems. The definitions and types are `GlobalClassFieldTheory.Reciprocity.abelianizedExtensionQuotientAddEquiv_transportExtension`, `GlobalClassFieldTheory.Reciprocity.abstractFixedFieldCyclotomicFiniteRestrictionMonoidHom`, `GlobalClassFieldTheory.Reciprocity.abstractFixedFieldInclusionCanonicalAbelianizedValue`, `GlobalClassFieldTheory.Reciprocity.abstractFixedFieldInclusionCanonicalNormResidueValue`, `GlobalClassFieldTheory.Reciprocity.abstractFixedFieldInclusionEmbeddedExtensionQuotientEquiv`, `GlobalClassFieldTheory.Reciprocity.abstractFixedFieldInclusionEmbeddedNormResidueValue`, `GlobalClassFieldTheory.Reciprocity.abstractFixedFieldInclusionTransportedAbelianizedEquiv`, `GlobalClassFieldTheory.Reciprocity.abstractFixedFieldInclusionTransportedAbelianizedValue`, `GlobalClassFieldTheory.Reciprocity.abstractFixedFieldInclusionTransportedCanonicalAbelianizedEquiv`, `GlobalClassFieldTheory.Reciprocity.abstractFixedFieldInclusionTransportedExtensionQuotientEquiv`, `GlobalClassFieldTheory.Reciprocity.abstractFixedFieldInclusionTransportedNormResidueValue`, `GlobalClassFieldTheory.Reciprocity.cyclotomicUnramifiedGeometricFiniteQuotientEquiv`, `GlobalClassFieldTheory.Reciprocity.cyclotomicUnramifiedGeometricInertiaQuotientEquiv`, `GlobalClassFieldTheory.Reciprocity.cyclotomicUnramifiedGeometricMaxQuotientEquiv`, `GlobalClassFieldTheory.Reciprocity.ramifiedInfinitePlaceGlobalNormResidueNegOneValue`, `GlobalClassFieldTheory.Reciprocity.rationalFiniteNormResidueValue`.
--
--   **Sources.** They come from these modules of lean/OAI/NumberTheory, in whole or in part: `GlobalClassFieldTheory_Reciprocity_AbstractFixedFieldGlobalNormResidue`, `GlobalClassFieldTheory_Reciprocity_ComplexificationArtin_InfinitePlaceCompatibility`, `GlobalClassFieldTheory_Reciprocity_CyclotomicUnramifiedGeometricRestriction`, `GlobalClassFieldTheory_Reciprocity_CyclotomicUnramifiedLocalGlobalCompatibility`, `GlobalClassFieldTheory_Reciprocity_CyclotomicUnramifiedRestriction`, `GlobalClassFieldTheory_Reciprocity_GlobalNormResidueNaturality`.
--
--   **Imports.** It imports the bundles `OAIQ244Duke104`, `OAIQ244Duke105` and `OAIQ244Duke106` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ244Duke110` and `OAIQ244Duke111`.
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
import Definitions.Def_OAIQ244Duke104
import Definitions.Def_OAIQ244Duke105
import Definitions.Def_OAIQ244Duke106

section
-- module Solutions.OAIQ244_DUKE.GlobalClassFieldTheory_Reciprocity_AbstractFixedFieldGlobalNormResidue
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 400000
attribute [-instance] _root_.GlobalClassFieldTheory.GlobalClassFields.ConductorialSubgroup.finiteIndex _root_.GlobalClassFieldTheory.GlobalClassFields.bigHilbertClassFieldNormSubgroup_normal _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexNormAmbientFiniteDimensional _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexNormAmbientIsGalois _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexNormAmbientNumberField _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexNormCyclotomicFieldFiniteDimensional _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexNormCyclotomicFieldIsCyclotomicExtension _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexNormCyclotomicFieldIsGalois _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexNormCyclotomicFieldNumberField _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexNormExponentNeZero _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexNormKummerFieldAlgebraOverBase _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexNormKummerFieldFiniteDimensional _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexNormKummerFieldFiniteDimensionalOverBase _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexNormKummerFieldModuleOverBase _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexNormKummerFieldNumberField _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexNormKummerFieldSMulOverBase _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexNormKummerFieldScalarTower _root_.GlobalClassFieldTheory.GlobalClassFields.ideleClassNorm_rangeFiniteIndex _root_.GlobalClassFieldTheory.GlobalClassFields.ordinaryNormClassFieldBaseFiniteDimensional _root_.GlobalClassFieldTheory.GlobalClassFields.ordinaryNormClassFieldBaseNumberField _root_.GlobalClassFieldTheory.GlobalClassFields.smallHilbertClassFieldNormSubgroupFiniteIndex _root_.GlobalClassFieldTheory.Reciprocity.abstractFixedFieldCyclotomicCompositum_algebra _root_.GlobalClassFieldTheory.Reciprocity.abstractFixedFieldCyclotomicCompositum_baseScalarTower _root_.GlobalClassFieldTheory.Reciprocity.abstractFixedFieldCyclotomicCompositum_scalarTower _root_.GlobalClassFieldTheory.Reciprocity.abstractFixedFieldCyclotomicFiniteCompositum_baseAlgebra _root_.GlobalClassFieldTheory.Reciprocity.abstractFixedFieldCyclotomicFiniteCompositum_baseScalarTower _root_.GlobalClassFieldTheory.Reciprocity.abstractFixedFieldCyclotomicFiniteCompositum_finiteDimensional _root_.GlobalClassFieldTheory.Reciprocity.abstractFixedFieldCyclotomicFiniteCompositum_numberField _root_.GlobalClassFieldTheory.Reciprocity.abstractFixedFieldCyclotomicFiniteGaloisLayer_scalarTower _root_.GlobalClassFieldTheory.Reciprocity.abstractFixedFieldCyclotomicFiniteLayer_baseAlgebra _root_.GlobalClassFieldTheory.Reciprocity.abstractFixedFieldCyclotomicFiniteLayer_baseModule _root_.GlobalClassFieldTheory.Reciprocity.abstractFixedFieldCyclotomicFiniteLayer_baseSMul _root_.GlobalClassFieldTheory.Reciprocity.abstractFixedFieldCyclotomicFiniteLayer_baseScalarTower _root_.GlobalClassFieldTheory.Reciprocity.abstractFixedFieldCyclotomicFiniteLayer_finiteDimensional _root_.GlobalClassFieldTheory.Reciprocity.abstractFixedFieldCyclotomicFiniteLayer_isAbelianGalois _root_.GlobalClassFieldTheory.Reciprocity.abstractFixedFieldCyclotomicFiniteLayer_layerAlgebra _root_.GlobalClassFieldTheory.Reciprocity.abstractFixedFieldCyclotomicFiniteLayer_layerSMul _root_.GlobalClassFieldTheory.Reciprocity.abstractFixedFieldCyclotomicFiniteLayer_layerScalarTower _root_.GlobalClassFieldTheory.Reciprocity.abstractFixedFieldCyclotomicFiniteLayer_numberField _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.boundedRealFields_finite _root_.OAI.PrimeDegreePackets.instT2SpaceLocalAlgebra _root_.OAI.PrimeDegreePackets.instTopologicalSpaceLocalAlgebra _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.OAI.PrimeDegreePackets.xT2Space _root_.GlobalClassFieldTheory.GlobalClassFields.bigHilbertNormQuotient_finite _root_.GlobalClassFieldTheory.GlobalClassFields.bigHilbertNormSubgroup_finiteIndex _root_.GlobalClassFieldTheory.GlobalClassFields.narrowClassGroup_finite
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

attribute [local instance] GlobalClassFieldTheory.Reciprocity.numberFieldEmbeddedExtensionSubgroupNormal
attribute [local instance] GlobalClassFieldTheory.Reciprocity.numberFieldEmbeddedExtensionQuotientFinite
attribute [local instance] GlobalClassFieldTheory.Reciprocity.numberFieldEmbeddedAbsoluteQuotientFinite
attribute [local instance] GlobalClassFieldTheory.Reciprocity.numberFieldEmbeddedAbstractFixedFieldFiniteDimensional
attribute [local instance] GlobalClassFieldTheory.Reciprocity.numberFieldEmbeddedAbstractRelativeFixedFieldFiniteDimensional
attribute [local instance] GlobalClassFieldTheory.Reciprocity.numberFieldEmbeddedAbstractFixedFieldScalarTower
attribute [local instance] GlobalClassFieldTheory.Reciprocity.numberFieldEmbeddedAbstractRelativeFixedFieldAbsoluteFiniteDimensional
attribute [local instance] GlobalClassFieldTheory.Reciprocity.numberFieldEmbeddedAbstractFixedFieldNumberField
attribute [local instance] GlobalClassFieldTheory.Reciprocity.numberFieldEmbeddedAbstractRelativeFixedFieldNumberField
attribute [local instance] GlobalClassFieldTheory.Reciprocity.numberFieldEmbeddedAbstractRelativeFixedFieldRestrictScalarsFiniteDimensional
attribute [local instance] GlobalClassFieldTheory.Reciprocity.numberFieldEmbeddedAbstractRelativeFixedFieldRestrictScalarsNumberField
noncomputable local instance
    numberFieldEmbeddedAbstractRelativeFixedFieldRestrictScalarsAlgebra_rfd8e8e_1
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
    numberFieldEmbeddedAbstractRelativeFixedFieldIsGalois_rfd8e8e_1
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
variable [FiniteDimensional K L] [IsAbelianGalois K L]

/-- The explicit-embedding norm-residue equivalence on a finite norm class. -/
theorem globalNormResidueEquivOfEmbedding_finiteNormClass
    (j : L →ₐ[ℚ] SeparableClosure ℚ)
    (x : FiniteNormQuotient rationalIdeleClassRepresentation
      (numberFieldEmbeddedBaseSubgroup K L j)
      (numberFieldEmbeddedTopSubgroup K L j)
      (numberFieldEmbeddedTopSubgroup_le_baseSubgroup K L j)) :
    globalNormResidueEquivOfEmbedding K L j
        (numberFieldEmbeddedFiniteNormQuotientEquivIdeleClassNormQuotient
          K L j x) =
      numberFieldEmbeddedAbelianizedExtensionQuotientEquivGaloisGroup K L j
        (rationalCyclotomicDegreeData.normResidueSymbol
          rationalIdeleClassRepresentation
          rationalCyclotomicIdeleClassValuationData
          rationalIdeleClassRepresentation_satisfiesClassFieldAxiom
          (numberFieldEmbeddedFiniteAbstractField K L j)
          (numberFieldEmbeddedFiniteGaloisSubextension K L j) x) := by
  simp only [globalNormResidueEquivOfEmbedding, AddEquiv.trans_apply,
    AddEquiv.symm_apply_apply]
  try rfl

omit [FiniteDimensional K L] [IsAbelianGalois K L] in
/-- The ambient-fixed idèle-class transport for the standard embedding is
the same map as the transport for an explicitly supplied embedding.  This
comparison is kept at the transport boundary, before forming norm quotients
or applying reciprocity. -/
theorem numberFieldTowerIdeleClassEquivAmbientFixed_eq_embedded_standard :
    numberFieldTowerIdeleClassEquivAmbientFixed K L =
      numberFieldEmbeddedIdeleClassEquivAmbientFixed K L
        (numberFieldSeparableClosureEmbedding L) := by
  let j := numberFieldSeparableClosureEmbedding L
  have hBase :
      numberFieldTowerAbstractBaseFieldEquiv K L =
        numberFieldEmbeddedAbstractBaseFieldEquiv K L j := by
    rfl
  unfold numberFieldTowerIdeleClassEquivAmbientFixed
    numberFieldEmbeddedIdeleClassEquivAmbientFixed
  rw [hBase]
  dsimp only
  congr 1

/-- The relative-index witness at the standard embedding (instance search no
longer unifies the general one with this quotient). -/
noncomputable local instance numberFieldStandardExtensionQuotientFinite :
    Finite
      ((numberFieldEmbeddedBaseSubgroup K L
          (numberFieldSeparableClosureEmbedding L)).toSubgroup ⧸
        CyclicCohomology.extensionSubgroup
          (numberFieldEmbeddedBaseSubgroup K L
            (numberFieldSeparableClosureEmbedding L))
          (numberFieldEmbeddedTopSubgroup K L
            (numberFieldSeparableClosureEmbedding L))
          (numberFieldEmbeddedTopSubgroup_le_baseSubgroup K L
            (numberFieldSeparableClosureEmbedding L))) :=
  numberFieldEmbeddedExtensionQuotient_finite K L
    (numberFieldSeparableClosureEmbedding L)

/- At the chosen embedding, both constructions use the same fixed tower and
abstract reciprocity data.  We compare their values on the particular fixed
idele class needed below; the two implementations of the finite norm-quotient
equivalence are deliberately not compared as dependent structures. -/
theorem numberFieldTowerNormResidueValue_eq_embedded_standard
    (c : IdeleClassGroup K) :
    numberFieldTowerAbelianizedExtensionQuotientEquivGaloisGroup K L
        (rationalCyclotomicDegreeData.normResidueSymbol
          rationalIdeleClassRepresentation
          rationalCyclotomicIdeleClassValuationData
          rationalIdeleClassRepresentation_satisfiesClassFieldAxiom
          (numberFieldTowerReciprocityFiniteAbstractField K L)
          (numberFieldTowerFiniteGaloisSubextension K L)
          (finiteNormClass rationalIdeleClassRepresentation
            (numberFieldTowerBaseSubgroup K L)
            (numberFieldTowerTopSubgroup L)
            (numberFieldTowerTopSubgroup_le_baseSubgroup K L)
            (numberFieldTowerIdeleClassEquivAmbientFixed K L (Additive.ofMul c)))) =
      numberFieldEmbeddedAbelianizedExtensionQuotientEquivGaloisGroup
        K L (numberFieldSeparableClosureEmbedding L)
        (rationalCyclotomicDegreeData.normResidueSymbol
          rationalIdeleClassRepresentation
          rationalCyclotomicIdeleClassValuationData
          rationalIdeleClassRepresentation_satisfiesClassFieldAxiom
          (numberFieldEmbeddedFiniteAbstractField K L
            (numberFieldSeparableClosureEmbedding L))
          (numberFieldEmbeddedFiniteGaloisSubextension K L
            (numberFieldSeparableClosureEmbedding L))
          (finiteNormClass rationalIdeleClassRepresentation
            (numberFieldEmbeddedBaseSubgroup K L
              (numberFieldSeparableClosureEmbedding L))
            (numberFieldEmbeddedTopSubgroup K L
              (numberFieldSeparableClosureEmbedding L))
            (numberFieldEmbeddedTopSubgroup_le_baseSubgroup K L
              (numberFieldSeparableClosureEmbedding L))
            (numberFieldEmbeddedIdeleClassEquivAmbientFixed K L
              (numberFieldSeparableClosureEmbedding L) (Additive.ofMul c)))) := by
  have hIdeleClassEquiv :
      numberFieldTowerIdeleClassEquivAmbientFixed K L =
        numberFieldEmbeddedIdeleClassEquivAmbientFixed K L
          (numberFieldSeparableClosureEmbedding L) := by
    exact numberFieldTowerIdeleClassEquivAmbientFixed_eq_embedded_standard K L
  have hFiniteAbstractField :
      numberFieldTowerReciprocityFiniteAbstractField K L =
        numberFieldEmbeddedFiniteAbstractField K L
          (numberFieldSeparableClosureEmbedding L) := by
    rfl
  have hSubextension :
      numberFieldTowerFiniteGaloisSubextension K L =
        numberFieldEmbeddedFiniteGaloisSubextension K L
          (numberFieldSeparableClosureEmbedding L) := by
    rfl
  have hGaloisComparison :
      numberFieldTowerAbelianizedExtensionQuotientEquivGaloisGroup K L =
        numberFieldEmbeddedAbelianizedExtensionQuotientEquivGaloisGroup
          K L (numberFieldSeparableClosureEmbedding L) := by
    rfl
  simp only [← hGaloisComparison]
  cases hFiniteAbstractField
  cases hSubextension
  rw [← hIdeleClassEquiv]
  rfl

/-- At the standard embedding, the two global norm-residue equivalences
agree on the actual norm quotient.  The comparison is extensional: it uses
surjectivity of the quotient map and the established evaluation formulas,
not definitional equality of the two quotient constructions. -/
theorem globalNormResidueEquiv_eq_ofEmbedding_standard :
    globalNormResidueEquiv K L =
      globalNormResidueEquivOfEmbedding K L
        (numberFieldSeparableClosureEmbedding L) := by
  apply AddEquiv.ext
  intro q
  obtain ⟨c, hc⟩ :=
    QuotientGroup.mk'_surjective
      (_root_.ideleClassNorm K L).range (Additive.toMul q)
  have hq :
      Additive.ofMul
          (QuotientGroup.mk' (_root_.ideleClassNorm K L).range c) = q :=
    Additive.toMul.injective hc
  rw [← hq]
  have hTower :=
    numberFieldTowerFiniteNormQuotientEquivIdeleClassNormQuotient_ideleClass
      K L c
  have hEmbedded :=
    numberFieldEmbeddedFiniteNormQuotientEquivIdeleClassNormQuotient_ideleClass
      K L (numberFieldSeparableClosureEmbedding L) c
  conv_lhs =>
    rw [← hTower, globalNormResidueEquiv_finiteNormClass]
  conv_rhs =>
    erw [← hEmbedded, globalNormResidueEquivOfEmbedding_finiteNormClass]
  exact numberFieldTowerNormResidueValue_eq_embedded_standard K L c

end EmbeddedNumberFieldRealization

end Reciprocity
end GlobalClassFieldTheory
end
end

section
-- module Solutions.OAIQ244_DUKE.GlobalClassFieldTheory_Reciprocity_GlobalNormResidueNaturality
attribute [-instance] _root_.GlobalClassFieldTheory.GlobalClassFields.ConductorialSubgroup.finiteIndex _root_.GlobalClassFieldTheory.GlobalClassFields.bigHilbertClassFieldNormSubgroup_normal _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexNormAmbientFiniteDimensional _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexNormAmbientIsGalois _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexNormAmbientNumberField _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexNormCyclotomicFieldFiniteDimensional _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexNormCyclotomicFieldIsCyclotomicExtension _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexNormCyclotomicFieldIsGalois _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexNormCyclotomicFieldNumberField _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexNormExponentNeZero _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexNormKummerFieldAlgebraOverBase _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexNormKummerFieldFiniteDimensional _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexNormKummerFieldFiniteDimensionalOverBase _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexNormKummerFieldModuleOverBase _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexNormKummerFieldNumberField _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexNormKummerFieldSMulOverBase _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexNormKummerFieldScalarTower _root_.GlobalClassFieldTheory.GlobalClassFields.ideleClassNorm_rangeFiniteIndex _root_.GlobalClassFieldTheory.GlobalClassFields.ordinaryNormClassFieldBaseFiniteDimensional _root_.GlobalClassFieldTheory.GlobalClassFields.ordinaryNormClassFieldBaseNumberField _root_.GlobalClassFieldTheory.GlobalClassFields.smallHilbertClassFieldNormSubgroupFiniteIndex _root_.GlobalClassFieldTheory.Reciprocity.abstractFixedFieldCyclotomicCompositum_algebra _root_.GlobalClassFieldTheory.Reciprocity.abstractFixedFieldCyclotomicCompositum_baseScalarTower _root_.GlobalClassFieldTheory.Reciprocity.abstractFixedFieldCyclotomicCompositum_scalarTower _root_.GlobalClassFieldTheory.Reciprocity.abstractFixedFieldCyclotomicFiniteCompositum_baseAlgebra _root_.GlobalClassFieldTheory.Reciprocity.abstractFixedFieldCyclotomicFiniteCompositum_baseScalarTower _root_.GlobalClassFieldTheory.Reciprocity.abstractFixedFieldCyclotomicFiniteCompositum_finiteDimensional _root_.GlobalClassFieldTheory.Reciprocity.abstractFixedFieldCyclotomicFiniteCompositum_numberField _root_.GlobalClassFieldTheory.Reciprocity.abstractFixedFieldCyclotomicFiniteGaloisLayer_scalarTower _root_.GlobalClassFieldTheory.Reciprocity.abstractFixedFieldCyclotomicFiniteLayer_baseAlgebra _root_.GlobalClassFieldTheory.Reciprocity.abstractFixedFieldCyclotomicFiniteLayer_baseModule _root_.GlobalClassFieldTheory.Reciprocity.abstractFixedFieldCyclotomicFiniteLayer_baseSMul _root_.GlobalClassFieldTheory.Reciprocity.abstractFixedFieldCyclotomicFiniteLayer_baseScalarTower _root_.GlobalClassFieldTheory.Reciprocity.abstractFixedFieldCyclotomicFiniteLayer_finiteDimensional _root_.GlobalClassFieldTheory.Reciprocity.abstractFixedFieldCyclotomicFiniteLayer_isAbelianGalois _root_.GlobalClassFieldTheory.Reciprocity.abstractFixedFieldCyclotomicFiniteLayer_layerAlgebra _root_.GlobalClassFieldTheory.Reciprocity.abstractFixedFieldCyclotomicFiniteLayer_layerSMul _root_.GlobalClassFieldTheory.Reciprocity.abstractFixedFieldCyclotomicFiniteLayer_layerScalarTower _root_.GlobalClassFieldTheory.Reciprocity.abstractFixedFieldCyclotomicFiniteLayer_numberField _root_.GlobalClassFieldTheory.Reciprocity.complexFourthRootField_finiteDimensional _root_.GlobalClassFieldTheory.Reciprocity.complexFourthRootField_numberField _root_.GlobalClassFieldTheory.Reciprocity.infinitePlaceComplexificationOverfield_algebra _root_.GlobalClassFieldTheory.Reciprocity.infinitePlaceComplexificationOverfield_baseAlgebra _root_.GlobalClassFieldTheory.Reciprocity.infinitePlaceComplexificationOverfield_baseSmul _root_.GlobalClassFieldTheory.Reciprocity.infinitePlaceComplexificationOverfield_finiteDimensional _root_.GlobalClassFieldTheory.Reciprocity.infinitePlaceComplexificationOverfield_numberField _root_.GlobalClassFieldTheory.Reciprocity.infinitePlaceComplexificationOverfield_smul _root_.GlobalClassFieldTheory.Reciprocity.ramifiedInfinitePlaceRealFixedField_algebra _root_.GlobalClassFieldTheory.Reciprocity.ramifiedInfinitePlaceRealFixedField_numberField _root_.GlobalClassFieldTheory.Reciprocity.rationalComplexification_infinitePlaceOverfield_algebra _root_.GlobalClassFieldTheory.Reciprocity.rationalComplexification_infinitePlaceOverfield_smul _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.boundedRealFields_finite _root_.OAI.PrimeDegreePackets.boundedRealFields_numberField _root_.OAI.PrimeDegreePackets.diagonalLogAction _root_.OAI.PrimeDegreePackets.instT2SpaceLocalAlgebra _root_.OAI.PrimeDegreePackets.instTopologicalSpaceLocalAlgebra _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.OAI.PrimeDegreePackets.xT2Space _root_.GlobalClassFieldTheory.GlobalClassFields.bigHilbertNormQuotient_finite _root_.GlobalClassFieldTheory.GlobalClassFields.bigHilbertNormSubgroup_finiteIndex _root_.GlobalClassFieldTheory.GlobalClassFields.narrowClassGroup_finite
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


local instance ideleClassGroupIsMulCommutative_rfd8e8e_1
    {F : Type} [Field F] [NumberField F]
    : IsMulCommutative (IdeleClassGroup F) :=
  ⟨⟨fun a b => mul_comm a b⟩⟩
local instance ideleClassSubgroupNormal_rfd8e8e_1
    {F : Type} [Field F] [NumberField F]
    (N : Subgroup (IdeleClassGroup F)) : N.Normal :=
  N.normal_of_isMulCommutative
/-- Two finite Galois subextensions with the same underlying closed subgroup
are equal; the remaining structure fields are proof-irrelevant. -/
theorem finiteGaloisSubextension_eq_of_field_eq
    {G : Type u} [Group G] [TopologicalSpace G]
    {K : ClosedSubgroup G}
    (A B : FiniteGaloisSubextension K)
    (h : A.field = B.field) :
    A = B := by
  cases A with
  | mk A hA nA fA =>
      cases B with
      | mk B hB nB fB =>
          dsimp only at h
          cases h
          rfl

/-- Rebase a finite Galois subextension along equality of its bundled base.
The field equality is the only data component; the remaining fields are
proof-irrelevant. -/
theorem finiteGaloisSubextension_transport_eq_of_field_eq
    {G : Type u} [Group G] [TopologicalSpace G]
    {A B : FiniteAbstractField G}
    (hAB : A = B)
    (P : FiniteGaloisSubextension A.field)
    (Q : FiniteGaloisSubextension B.field)
    (hfield : P.field = Q.field) :
    Eq.mp
      (congrArg
        (fun X : FiniteAbstractField G =>
          FiniteGaloisSubextension X.field)
        hAB)
      P = Q := by
  cases hAB
  exact finiteGaloisSubextension_eq_of_field_eq P Q hfield

/-- Rebase an abelianized equivalence along equality of finite Galois
subextensions over a fixed abstract base. -/
def abelianizedExtensionQuotientAddEquiv_transportExtension
    {G : Type u} [Group G] [TopologicalSpace G]
    {K : ClosedSubgroup G}
    {P Q : FiniteGaloisSubextension K}
    (hPQ : P = Q)
    {X : Type} [AddGroup X]
    (e : Additive (Abelianization P.extensionQuotient) ≃+ X) :
    Additive (Abelianization Q.extensionQuotient) ≃+ X := by
  cases hPQ
  exact e

/-- Abelianization commutes with simultaneous transport of the abstract base
and its finite Galois subextension. -/
theorem abelianizedCanonicalEquiv_transportFiniteGalois
    {G : Type u} [Group G] [TopologicalSpace G]
    {A B : FiniteAbstractField G}
    (hAB : A = B)
    (P : FiniteGaloisSubextension A.field)
    {Q : FiniteGaloisSubextension B.field}
    (hPQ :
      Eq.mp
        (congrArg
          (fun Y : FiniteAbstractField G =>
            FiniteGaloisSubextension Y.field)
          hAB)
        P = Q)
    {X : Type} [CommGroup X]
    (e : P.extensionQuotient ≃* X) :
    abelianizedExtensionQuotientAddEquiv_transportExtension hPQ
        (abelianizedExtensionQuotientAddEquiv_transportBase
          hAB P
          (MulEquiv.toAdditive
            (e.abelianizationCongr.trans
              (Abelianization.equivOfComm : X ≃* Abelianization X).symm))) =
      MulEquiv.toAdditive
        (((extensionQuotientMulEquiv_transportFiniteGalois
            hAB P hPQ).trans e).abelianizationCongr.trans
          (Abelianization.equivOfComm : X ≃* Abelianization X).symm) := by
  cases hAB
  cases hPQ
  rfl

/-- Package the entire rational finite norm-residue evaluation so that its
dependent base, extension, quotient and comparison maps move together. -/
def rationalFiniteNormResidueValue
    (K : FiniteAbstractField
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
    (L : FiniteGaloisSubextension K.field)
    {C X : Type} [AddGroup C] [AddGroup X]
    (eIdele : C ≃+
      ambientFixedAddSubgroup rationalIdeleClassRepresentation K.field)
    (eGalois : Additive (Abelianization L.extensionQuotient) ≃+ X)
    (c : C) : X := by
  letI :
      Finite
        (K.field.toSubgroup ⧸
          CyclicCohomology.extensionSubgroup
            K.field L.field L.below) :=
    L.finite
  exact
    eGalois
      (rationalCyclotomicDegreeData.normResidueSymbol
        rationalIdeleClassRepresentation
        rationalCyclotomicIdeleClassValuationData
        rationalIdeleClassRepresentation_satisfiesClassFieldAxiom
        K L
        (finiteNormClass rationalIdeleClassRepresentation
          K.field L.field L.below (eIdele c)))

/-- The packaged norm-residue value is invariant under rebasing the finite
abstract field together with all dependent data. -/
theorem rationalFiniteNormResidueValue_transportBase
    {A B : FiniteAbstractField
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ)}
    (hAB : A = B)
    (P : FiniteGaloisSubextension A.field)
    {C X : Type} [AddGroup C] [AddGroup X]
    (eIdele : C ≃+
      ambientFixedAddSubgroup rationalIdeleClassRepresentation A.field)
    (eGalois : Additive (Abelianization P.extensionQuotient) ≃+ X)
    (c : C) :
    rationalFiniteNormResidueValue A P eIdele eGalois c =
      rationalFiniteNormResidueValue B
        (Eq.mp
          (congrArg
            (fun Y : FiniteAbstractField
                (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ) =>
              FiniteGaloisSubextension Y.field)
            hAB)
          P)
        (Eq.mp
          (congrArg
            (fun Y : FiniteAbstractField
                (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ) =>
              C ≃+ ambientFixedAddSubgroup
                rationalIdeleClassRepresentation Y.field)
            hAB)
          eIdele)
        (abelianizedExtensionQuotientAddEquiv_transportBase
          hAB P eGalois)
        c := by
  cases hAB
  rfl

/-- The packaged norm-residue value is invariant under equality of the finite
Galois subextension. -/
theorem rationalFiniteNormResidueValue_transportExtension
    (K : FiniteAbstractField
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
    {P Q : FiniteGaloisSubextension K.field}
    (hPQ : P = Q)
    {C X : Type} [AddGroup C] [AddGroup X]
    (eIdele : C ≃+
      ambientFixedAddSubgroup rationalIdeleClassRepresentation K.field)
    (eGalois : Additive (Abelianization P.extensionQuotient) ≃+ X)
    (c : C) :
    rationalFiniteNormResidueValue K P eIdele eGalois c =
      rationalFiniteNormResidueValue K Q eIdele
        (abelianizedExtensionQuotientAddEquiv_transportExtension
          hPQ eGalois)
        c := by
  cases hPQ
  rfl

section AbstractFixedFieldInclusion

local instance ideleClassGroupIsMulCommutative_rfd8e8e_2
    {F : Type} [Field F] [NumberField F]
    : IsMulCommutative (IdeleClassGroup F) :=
  ⟨⟨fun a b => mul_comm a b⟩⟩
local instance ideleClassSubgroupNormal_rfd8e8e_2
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
/-- Use the same direct fixed-field Galois witness as the intrinsic
norm-residue construction.  This prevents the dependent Galois-group type
from being synthesized through a second `IsAbelianGalois` instance path. -/
noncomputable local instance
    naturalityAbstractRelativeFixedFieldIsGalois :
    IsGalois
      (abstractFixedField ℚ (SeparableClosure ℚ) H.field)
      (abstractRelativeFixedField
        ℚ (SeparableClosure ℚ) P.below) :=
  abstractRelativeFixedField_isGalois
    ℚ (SeparableClosure ℚ)
    H.field P.field P.below P.normal

attribute [local instance] GlobalClassFieldTheory.Reciprocity.naturalityAbstractRelativeFixedFieldIsAbelianGalois
/-- The lower subgroup obtained from the canonical inclusion of an abstract
fixed-field tower is the original lower closed subgroup. -/
theorem
    numberFieldEmbeddedBaseSubgroup_abstractFixedFieldInclusion
    (H : FiniteAbstractField
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
    (P : FiniteAbelianSubextension H.field) :
    let F :=
      abstractFixedField ℚ (SeparableClosure ℚ) H.field
    let E :=
      abstractRelativeFixedField
        ℚ (SeparableClosure ℚ) P.below
    let j : E →ₐ[ℚ] SeparableClosure ℚ :=
      E.val.restrictScalars ℚ
    numberFieldEmbeddedBaseSubgroup F E j = H.field := by
  dsimp only
  have hi :
      numberFieldEmbeddedLowerEmbedding
          (abstractFixedField ℚ (SeparableClosure ℚ) H.field)
          (abstractRelativeFixedField
            ℚ (SeparableClosure ℚ) P.below)
          ((abstractRelativeFixedField
            ℚ (SeparableClosure ℚ) P.below).val.restrictScalars ℚ) =
        (abstractFixedField
          ℚ (SeparableClosure ℚ) H.field).val := by
    ext x
    rfl
  have hRange :
      (numberFieldEmbeddedLowerEmbedding
        (abstractFixedField ℚ (SeparableClosure ℚ) H.field)
        (abstractRelativeFixedField
          ℚ (SeparableClosure ℚ) P.below)
        ((abstractRelativeFixedField
          ℚ (SeparableClosure ℚ) P.below).val.restrictScalars ℚ)).fieldRange =
        abstractFixedField ℚ (SeparableClosure ℚ) H.field := by
    ext x
    constructor
    · rintro ⟨y, rfl⟩
      change
        numberFieldEmbeddedLowerEmbedding
            (abstractFixedField ℚ (SeparableClosure ℚ) H.field)
            (abstractRelativeFixedField
              ℚ (SeparableClosure ℚ) P.below)
            ((abstractRelativeFixedField
              ℚ (SeparableClosure ℚ) P.below).val.restrictScalars ℚ) y ∈
          abstractFixedField ℚ (SeparableClosure ℚ) H.field
      rw [hi]
      exact y.property
    · intro hx
      refine ⟨⟨x, hx⟩, ?_⟩
      rw [hi]
      rfl
  rw [numberFieldEmbeddedBaseSubgroup, hRange]
  exact
    closedFixingSubgroup_abstractFixedField_eq
      ℚ (SeparableClosure ℚ) H.field

/-- The upper subgroup obtained from the canonical inclusion of an abstract
fixed-field tower is the original upper closed subgroup. -/
theorem
    numberFieldEmbeddedTopSubgroup_abstractFixedFieldInclusion
    (H : FiniteAbstractField
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
    (P : FiniteAbelianSubextension H.field) :
    let F :=
      abstractFixedField ℚ (SeparableClosure ℚ) H.field
    let E :=
      abstractRelativeFixedField
        ℚ (SeparableClosure ℚ) P.below
    let j : E →ₐ[ℚ] SeparableClosure ℚ :=
      E.val.restrictScalars ℚ
    numberFieldEmbeddedTopSubgroup F E j = P.field := by
  dsimp only
  rw [numberFieldEmbeddedTopSubgroup]
  have hjRangeSelf :
      ((abstractRelativeFixedField
        ℚ (SeparableClosure ℚ) P.below).val.restrictScalars ℚ).fieldRange =
        (abstractRelativeFixedField
          ℚ (SeparableClosure ℚ) P.below).restrictScalars ℚ := by
    ext x
    constructor
    · rintro ⟨y, rfl⟩
      exact y.property
    · intro hx
      exact ⟨⟨x, hx⟩, rfl⟩
  have hjRange :
      ((abstractRelativeFixedField
        ℚ (SeparableClosure ℚ) P.below).val.restrictScalars ℚ).fieldRange =
        abstractFixedField ℚ (SeparableClosure ℚ) P.field := by
    exact hjRangeSelf.trans
      (IntermediateField.extendScalars_restrictScalars
        (abstractFixedField_le
          ℚ (SeparableClosure ℚ) P.below))
  rw [hjRange]
  exact
    closedFixingSubgroup_abstractFixedField_eq
      ℚ (SeparableClosure ℚ) P.field

/-- Transport a packaged rational norm-residue value directly from an equal
abstract base to the finite Galois extension underlying `P`.  Keeping the two
dependent transports in their own declaration prevents their elaboration cost
from accumulating in the main fixed-field comparison theorem. -/
theorem rationalFiniteNormResidueValue_transportToAbstractExtension
    {A : FiniteAbstractField
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ)}
    (hAH : A = H)
    (L : FiniteGaloisSubextension A.field)
    (hLP :
      Eq.mp
          (congrArg
            (fun Y : FiniteAbstractField
                (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ) =>
              FiniteGaloisSubextension Y.field)
            hAH)
          L =
        P.toFiniteGaloisExtension)
    {C X : Type} [AddGroup C] [AddGroup X]
    (eIdele : C ≃+
      ambientFixedAddSubgroup rationalIdeleClassRepresentation A.field)
    (eGalois : Additive (Abelianization L.extensionQuotient) ≃+ X)
    (c : C) :
    rationalFiniteNormResidueValue A L eIdele eGalois c =
      rationalFiniteNormResidueValue H P.toFiniteGaloisExtension
        (Eq.mp
          (congrArg
            (fun Y : FiniteAbstractField
                (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ) =>
              C ≃+ ambientFixedAddSubgroup
                rationalIdeleClassRepresentation Y.field)
            hAH)
          eIdele)
        (abelianizedExtensionQuotientAddEquiv_transportExtension hLP
          (abelianizedExtensionQuotientAddEquiv_transportBase
            hAH L eGalois))
        c := by
  calc
    _ = rationalFiniteNormResidueValue H
        (Eq.mp
          (congrArg
            (fun Y : FiniteAbstractField
                (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ) =>
              FiniteGaloisSubextension Y.field)
            hAH)
          L)
        (Eq.mp
          (congrArg
            (fun Y : FiniteAbstractField
                (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ) =>
              C ≃+ ambientFixedAddSubgroup
                rationalIdeleClassRepresentation Y.field)
            hAH)
          eIdele)
        (abelianizedExtensionQuotientAddEquiv_transportBase hAH L eGalois)
        c :=
      rationalFiniteNormResidueValue_transportBase
        (A := A) (B := H) (C := C) (X := X)
        hAH L eIdele eGalois c
    _ = _ :=
      rationalFiniteNormResidueValue_transportExtension
        (K := H)
        (P := Eq.mp
          (congrArg
            (fun Y : FiniteAbstractField
                (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ) =>
              FiniteGaloisSubextension Y.field)
            hAH)
          L)
        (Q := P.toFiniteGaloisExtension) (C := C) (X := X)
        hLP
        (Eq.mp
          (congrArg
            (fun Y : FiniteAbstractField
                (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ) =>
              C ≃+ ambientFixedAddSubgroup
                rationalIdeleClassRepresentation Y.field)
            hAH)
          eIdele)
        (abelianizedExtensionQuotientAddEquiv_transportBase hAH L eGalois)
        c

/-- The finite abstract field reconstructed from the literal fixed-field
inclusion is the original packaged abstract field.  Keeping this structure
equality separate avoids repeatedly rebuilding all of its proof fields. -/
theorem
    numberFieldEmbeddedFiniteAbstractField_abstractFixedFieldInclusion
    (H : FiniteAbstractField
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
    (P : FiniteAbelianSubextension H.field) :
    let F :=
      abstractFixedField ℚ (SeparableClosure ℚ) H.field
    let E :=
      abstractRelativeFixedField
        ℚ (SeparableClosure ℚ) P.below
    let j : E →ₐ[ℚ] SeparableClosure ℚ :=
      E.val.restrictScalars ℚ
    numberFieldEmbeddedFiniteAbstractField F E j = H := by
  dsimp only
  exact FiniteAbstractField.eq_of_field_eq _ _
    (numberFieldEmbeddedBaseSubgroup_abstractFixedFieldInclusion H P)

/-- Transporting the finite Galois subextension reconstructed from the literal
fixed-field inclusion recovers the canonical subextension packaged by `P`.
This is the sole dependent structure equality used by the later quotient
comparisons. -/
theorem
    numberFieldEmbeddedFiniteGaloisSubextension_transport_eq
    (H : FiniteAbstractField
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
    (P : FiniteAbelianSubextension H.field) :
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
    let hHEmbedded : HEmbedded = H :=
      numberFieldEmbeddedFiniteAbstractField_abstractFixedFieldInclusion H P
    Eq.mp
        (congrArg
          (fun X : FiniteAbstractField
              (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ) =>
            FiniteGaloisSubextension X.field)
          hHEmbedded)
        PEmbedded =
      P.toFiniteGaloisExtension := by
  dsimp only
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
  exact finiteGaloisSubextension_transport_eq_of_field_eq
    hHEmbedded PEmbedded P.toFiniteGaloisExtension
    (numberFieldEmbeddedTopSubgroup_abstractFixedFieldInclusion H P)

/-- Opaque endpoint for the extension-quotient comparison supplied by the
literal embedding.  Its domain is already the canonical quotient of `P`, so
no client has to reconstruct the two subgroup transports. -/
noncomputable def
    abstractFixedFieldInclusionEmbeddedExtensionQuotientEquiv
    (H : FiniteAbstractField
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
    (P : FiniteAbelianSubextension H.field) :
    P.toFiniteGaloisExtension.extensionQuotient ≃*
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
  have hTop :
      numberFieldEmbeddedTopSubgroup F E j = P.field :=
    numberFieldEmbeddedTopSubgroup_abstractFixedFieldInclusion H P
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
  exact
    P.toFiniteGaloisExtension.extensionQuotientMulEquiv.trans
      ((extensionQuotientMulEquivOfEq
        hBase.symm hTop.symm P.below
        (numberFieldEmbeddedTopSubgroup_le_baseSubgroup F E j)).trans
      (ambientEmbeddedExtensionQuotientEquivGaloisGroup
        ℚ F E j eSep))

/-- Opaque quotient endpoint obtained by transporting the explicitly embedded
finite Galois subextension back to the canonical package. -/
noncomputable def
    abstractFixedFieldInclusionTransportedExtensionQuotientEquiv
    (H : FiniteAbstractField
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
    (P : FiniteAbelianSubextension H.field) :
    P.toFiniteGaloisExtension.extensionQuotient ≃*
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
  exact
    (extensionQuotientMulEquiv_transportFiniteGalois
      hHEmbedded PEmbedded hPEmbedded).trans
      (numberFieldEmbeddedExtensionQuotientEquivGaloisGroup F E j)

/-- Opaque abelianized equivalence obtained by transporting the explicitly
embedded finite Galois package to the canonical one. -/
noncomputable def
    abstractFixedFieldInclusionTransportedAbelianizedEquiv
    (H : FiniteAbstractField
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
    (P : FiniteAbelianSubextension H.field) :
    Additive
        (Abelianization
          P.toFiniteGaloisExtension.extensionQuotient) ≃+
      Additive
        (Gal(
          (abstractRelativeFixedField
            ℚ (SeparableClosure ℚ) P.below) /
          (abstractFixedField ℚ (SeparableClosure ℚ) H.field))) := by
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
  exact
    abelianizedExtensionQuotientAddEquiv_transportExtension hPEmbedded
      (abelianizedExtensionQuotientAddEquiv_transportBase
        hHEmbedded PEmbedded
        (numberFieldEmbeddedAbelianizedExtensionQuotientEquivGaloisGroup
          F E j))

/-- Canonical abelianization comparison built from the already transported
opaque extension-quotient endpoint. -/
noncomputable def
    abstractFixedFieldInclusionTransportedCanonicalAbelianizedEquiv
    (H : FiniteAbstractField
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
    (P : FiniteAbelianSubextension H.field) :
    Additive
        (Abelianization
          P.toFiniteGaloisExtension.extensionQuotient) ≃+
      Additive
        (Gal(
          (abstractRelativeFixedField
            ℚ (SeparableClosure ℚ) P.below) /
          (abstractFixedField ℚ (SeparableClosure ℚ) H.field))) := by
  let Q :=
    Gal(
      (abstractRelativeFixedField
        ℚ (SeparableClosure ℚ) P.below) /
      (abstractFixedField ℚ (SeparableClosure ℚ) H.field))
  exact
    MulEquiv.toAdditive
      ((MulEquiv.abelianizationCongr
        (abstractFixedFieldInclusionTransportedExtensionQuotientEquiv H P)).trans
          (Abelianization.equivOfComm : Q ≃* Abelianization Q).symm)

/-- Pointwise opaque value of the transported abelianized equivalence. -/
noncomputable def
    abstractFixedFieldInclusionTransportedAbelianizedValue
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
  abstractFixedFieldInclusionTransportedAbelianizedEquiv H P z

/-- Pointwise opaque value of the intrinsic abstract fixed-field
abelianization comparison. -/
noncomputable def
    abstractFixedFieldInclusionCanonicalAbelianizedValue
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
  abstractFixedFieldAbelianizedExtensionQuotientEquivGaloisGroup H P z

/-- Opaque packaged norm-residue value before transporting the explicitly
embedded abstract field and finite Galois package. -/
noncomputable def
    abstractFixedFieldInclusionEmbeddedNormResidueValue
    (H : FiniteAbstractField
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
    (P : FiniteAbelianSubextension H.field)
    (c : Additive
      (IdeleClassGroup
        (abstractFixedField ℚ (SeparableClosure ℚ) H.field))) :
    Additive
      (Gal(
        (abstractRelativeFixedField
          ℚ (SeparableClosure ℚ) P.below) /
        (abstractFixedField ℚ (SeparableClosure ℚ) H.field))) := by
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
  exact
    rationalFiniteNormResidueValue HEmbedded PEmbedded
      (numberFieldEmbeddedIdeleClassEquivAmbientFixed F E j)
      (numberFieldEmbeddedAbelianizedExtensionQuotientEquivGaloisGroup
        F E j)
      c

/-- Opaque packaged value after transporting both dependent structures to
the canonical `H` and `P` endpoints. -/
noncomputable def
    abstractFixedFieldInclusionTransportedNormResidueValue
    (H : FiniteAbstractField
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
    (P : FiniteAbelianSubextension H.field)
    (c : Additive
      (IdeleClassGroup
        (abstractFixedField ℚ (SeparableClosure ℚ) H.field))) :
    Additive
      (Gal(
        (abstractRelativeFixedField
          ℚ (SeparableClosure ℚ) P.below) /
        (abstractFixedField ℚ (SeparableClosure ℚ) H.field))) := by
  let F :=
    abstractFixedField ℚ (SeparableClosure ℚ) H.field
  let E :=
    abstractRelativeFixedField
      ℚ (SeparableClosure ℚ) P.below
  let j : E →ₐ[ℚ] SeparableClosure ℚ :=
    E.val.restrictScalars ℚ
  let HEmbedded :=
    numberFieldEmbeddedFiniteAbstractField F E j
  have hHEmbedded : HEmbedded = H :=
    numberFieldEmbeddedFiniteAbstractField_abstractFixedFieldInclusion H P
  let eIdeleEmbedded :=
    numberFieldEmbeddedIdeleClassEquivAmbientFixed F E j
  let eIdeleOverH :
      Additive (IdeleClassGroup F) ≃+
        ambientFixedAddSubgroup rationalIdeleClassRepresentation H.field :=
    Eq.mp
      (congrArg
        (fun X : FiniteAbstractField
            (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ) =>
          Additive (IdeleClassGroup F) ≃+
            ambientFixedAddSubgroup
              rationalIdeleClassRepresentation X.field)
        hHEmbedded)
      eIdeleEmbedded
  exact
    rationalFiniteNormResidueValue H P.toFiniteGaloisExtension
      eIdeleOverH
      (abstractFixedFieldInclusionTransportedAbelianizedEquiv H P)
      c

/-- Opaque intrinsic packaged norm-residue value at the canonical endpoints. -/
noncomputable def
    abstractFixedFieldInclusionCanonicalNormResidueValue
    (H : FiniteAbstractField
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
    (P : FiniteAbelianSubextension H.field)
    (c : Additive
      (IdeleClassGroup
        (abstractFixedField ℚ (SeparableClosure ℚ) H.field))) :
    Additive
      (Gal(
        (abstractRelativeFixedField
          ℚ (SeparableClosure ℚ) P.below) /
        (abstractFixedField ℚ (SeparableClosure ℚ) H.field))) :=
  rationalFiniteNormResidueValue H P.toFiniteGaloisExtension
    (rationalAbstractFixedFieldIdeleClassEquivFixed H.field)
    (abstractFixedFieldAbelianizedExtensionQuotientEquivGaloisGroup H P)
    c

/-- Simultaneous transport of the embedded abstract field and finite Galois
package sends the embedded norm-residue value to the transported endpoint. -/
theorem
    abstractFixedFieldInclusionEmbeddedNormResidueValue_eq_transported
    (H : FiniteAbstractField
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
    (P : FiniteAbelianSubextension H.field)
    (c : Additive
      (IdeleClassGroup
        (abstractFixedField ℚ (SeparableClosure ℚ) H.field))) :
    abstractFixedFieldInclusionEmbeddedNormResidueValue H P c =
      abstractFixedFieldInclusionTransportedNormResidueValue H P c := by
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
  let eIdeleEmbedded :=
    numberFieldEmbeddedIdeleClassEquivAmbientFixed F E j
  let eGaloisEmbedded :=
    numberFieldEmbeddedAbelianizedExtensionQuotientEquivGaloisGroup F E j
  simpa only [
    abstractFixedFieldInclusionEmbeddedNormResidueValue,
    abstractFixedFieldInclusionTransportedNormResidueValue,
    abstractFixedFieldInclusionTransportedAbelianizedEquiv,
    eIdeleEmbedded,
    eGaloisEmbedded] using
    (rationalFiniteNormResidueValue_transportToAbstractExtension
      (H := H) (P := P)
      (A := HEmbedded)
      (C := Additive (IdeleClassGroup F))
      (X := Additive Gal(E / F))
      hHEmbedded PEmbedded hPEmbedded
      eIdeleEmbedded eGaloisEmbedded c)

end AbstractFixedFieldInclusion

end Reciprocity
end GlobalClassFieldTheory
end
end

section
-- module Solutions.OAIQ244_DUKE.GlobalClassFieldTheory_Reciprocity_ComplexificationArtin_InfinitePlaceCompatibility
attribute [-instance] _root_.GlobalClassFieldTheory.GlobalClassFields.ConductorialSubgroup.finiteIndex _root_.GlobalClassFieldTheory.GlobalClassFields.bigHilbertClassFieldNormSubgroup_normal _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexNormAmbientFiniteDimensional _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexNormAmbientIsGalois _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexNormAmbientNumberField _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexNormCyclotomicFieldFiniteDimensional _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexNormCyclotomicFieldIsCyclotomicExtension _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexNormCyclotomicFieldIsGalois _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexNormCyclotomicFieldNumberField _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexNormExponentNeZero _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexNormKummerFieldAlgebraOverBase _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexNormKummerFieldFiniteDimensional _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexNormKummerFieldFiniteDimensionalOverBase _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexNormKummerFieldModuleOverBase _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexNormKummerFieldNumberField _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexNormKummerFieldSMulOverBase _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexNormKummerFieldScalarTower _root_.GlobalClassFieldTheory.GlobalClassFields.ideleClassNorm_rangeFiniteIndex _root_.GlobalClassFieldTheory.GlobalClassFields.smallHilbertClassFieldNormSubgroupFiniteIndex _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.GlobalClassFieldTheory.GlobalClassFields.bigHilbertNormQuotient_finite _root_.GlobalClassFieldTheory.GlobalClassFields.bigHilbertNormSubgroup_finiteIndex
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI
attribute [local instance] OAI.starSubalgebraCommCStarAlgebra

set_option autoImplicit false

/-!
# Infinite-place local-global Artin compatibility

This module compares the real fixed place and the original ramified place,
then transports the special overextension computation through global
norm-residue naturality.
-/

open scoped Classical IsMulCommutative
open NumberField
open IdeleGroup

noncomputable section

namespace GlobalClassFieldTheory
namespace Reciprocity

section ComplexConjugationOverextension

variable
    {K L : Type}
    [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsAbelianGalois K L]

local instance
    infinitePlaceCompatibilityIdeleClassGroupIsMulCommutative_rfd8e8e_1
    {F : Type} [Field F] [NumberField F] :
    IsMulCommutative (IdeleClassGroup F) :=
  ⟨⟨fun a b => mul_comm a b⟩⟩
/-- The base global norm-residue value at the negative-one class of `v`. -/
noncomputable def ramifiedInfinitePlaceGlobalNormResidueNegOneValue
    (v : InfinitePlace K) :
    Gal(L / K) :=
  globalNormResidueMonoidHom K L
    (IdeleGroup.infinitePlaceIdeleClass v (-1 : v.Completionˣ))

end ComplexConjugationOverextension

end Reciprocity
end GlobalClassFieldTheory
end
end

section
-- module Solutions.OAIQ244_DUKE.GlobalClassFieldTheory_Reciprocity_CyclotomicUnramifiedRestriction
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 400000
attribute [-instance] _root_.GlobalClassFieldTheory.GlobalClassFields.ConductorialSubgroup.finiteIndex _root_.GlobalClassFieldTheory.GlobalClassFields.bigHilbertClassFieldNormSubgroup_normal _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexNormAmbientFiniteDimensional _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexNormAmbientIsGalois _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexNormAmbientNumberField _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexNormCyclotomicFieldFiniteDimensional _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexNormCyclotomicFieldIsCyclotomicExtension _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexNormCyclotomicFieldIsGalois _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexNormCyclotomicFieldNumberField _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexNormExponentNeZero _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexNormKummerFieldAlgebraOverBase _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexNormKummerFieldFiniteDimensional _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexNormKummerFieldFiniteDimensionalOverBase _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexNormKummerFieldModuleOverBase _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexNormKummerFieldNumberField _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexNormKummerFieldSMulOverBase _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexNormKummerFieldScalarTower _root_.GlobalClassFieldTheory.GlobalClassFields.ideleClassNorm_rangeFiniteIndex _root_.GlobalClassFieldTheory.GlobalClassFields.ordinaryNormClassFieldBaseFiniteDimensional _root_.GlobalClassFieldTheory.GlobalClassFields.ordinaryNormClassFieldBaseNumberField _root_.GlobalClassFieldTheory.GlobalClassFields.smallHilbertClassFieldNormSubgroupFiniteIndex _root_.GlobalClassFieldTheory.Reciprocity.complexFourthRootField_numberField _root_.GlobalClassFieldTheory.Reciprocity.infinitePlaceComplexificationOverfield_numberField _root_.GlobalClassFieldTheory.Reciprocity.ramifiedInfinitePlaceRealFixedField_numberField _root_.GlobalClassFieldTheory.Reciprocity.rationalComplexification_infinitePlaceOverfield_algebra _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.boundedRealFields_numberField _root_.OAI.PrimeDegreePackets.instT2SpaceLocalAlgebra _root_.OAI.PrimeDegreePackets.instTopologicalSpaceLocalAlgebra _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.OAI.PrimeDegreePackets.xT2Space _root_.GlobalClassFieldTheory.GlobalClassFields.bigHilbertNormQuotient_finite _root_.GlobalClassFieldTheory.GlobalClassFields.bigHilbertNormSubgroup_finiteIndex
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI
attribute [local instance] OAI.starSubalgebraCommCStarAlgebra

set_option autoImplicit false

/-!
# Finite restriction of cyclotomic fixed-field reciprocity

For an unramified finite abelian subextension of an abstract fixed
number field, this file constructs the genuine restriction from the
cyclotomic maximal-unramified Galois group to the finite Galois group.
It then identifies the restriction of the chosen-local-factor
cyclotomic Artin map with the actual global norm-residue map.
-/

open scoped IsMulCommutative NumberField

noncomputable section

namespace GlobalClassFieldTheory
namespace Reciprocity

open ClassFormation
open KummerTheory

/-- The actual fixed field attached to `H` is a number field.  Keeping
this as one file-local instance makes it available while later idele-class
binders are elaborated. -/
noncomputable local instance
    cyclotomicUnramifiedRestriction_abstractFixedFieldNumberField
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

/-- Genuine restriction from the cyclotomic maximal-unramified
extension of an abstract fixed field to a finite unramified abelian
subextension.  The construction uses the canonical quotient
presentations of both actual Galois groups. -/
noncomputable def abstractFixedFieldCyclotomicFiniteRestrictionMonoidHom
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
    let hI :=
      rationalCyclotomicFieldInertia_le H.field
    let U :=
      LocalClassFieldTheory.abstractRelativeFixedField
        ℚ (SeparableClosure ℚ) hI
    Gal(U / F) →* Gal(E / F) := by
  dsimp only
  let qFinite :
      L.toFiniteGaloisExtension.extensionQuotient ≃*
        Gal(
          LocalClassFieldTheory.abstractRelativeFixedField
            ℚ (SeparableClosure ℚ) L.below /
          LocalClassFieldTheory.abstractFixedField
            ℚ (SeparableClosure ℚ) H.field) :=
    L.toFiniteGaloisExtension.extensionQuotientMulEquiv.trans
      (LocalClassFieldTheory.abstractExtensionQuotientEquivGaloisGroup
        ℚ (SeparableClosure ℚ)
        H.field L.field L.below L.normal)
  let finiteRestriction :=
    DegreeData.finiteUnramifiedRestriction
      rationalCyclotomicDegreeData
      (H.toFiniteResidueAbstractField rationalCyclotomicDegreeData)
      L.toFiniteGaloisExtension hUnramified
  let degreeEquiv :=
    rationalCyclotomicDegreeData.maximalUnramifiedDegreeEquiv
      (H.toFiniteResidueAbstractField rationalCyclotomicDegreeData)
  let galEquiv := abstractFixedFieldCyclotomicGalEquivZHat H
  exact
    @MonoidHom.comp _ _ _ _ _ _ qFinite.toMonoidHom
      (@MonoidHom.comp _ _ _ _ _ _ finiteRestriction
        (@MonoidHom.comp _ _ _ _ _ _
          degreeEquiv.symm.toMonoidHom galEquiv.toMonoidHom))

/-- Evaluate the finite cyclotomic restriction through its quotient coordinates. -/
theorem abstractFixedFieldCyclotomicFiniteRestrictionMonoidHom_apply
    (H : FiniteAbstractField
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
    (L : FiniteAbelianSubextension H.field)
    (hUnramified :
      L.toFiniteGaloisExtension.IsUnramified
        rationalCyclotomicDegreeData)
    (σ : Gal(
      LocalClassFieldTheory.abstractRelativeFixedField
          ℚ (SeparableClosure ℚ)
          (rationalCyclotomicFieldInertia_le H.field) /
        LocalClassFieldTheory.abstractFixedField
          ℚ (SeparableClosure ℚ) H.field)) :
    abstractFixedFieldCyclotomicFiniteRestrictionMonoidHom H L hUnramified σ =
      (L.toFiniteGaloisExtension.extensionQuotientMulEquiv.trans
        (LocalClassFieldTheory.abstractExtensionQuotientEquivGaloisGroup
          ℚ (SeparableClosure ℚ)
          H.field L.field L.below L.normal))
        (DegreeData.finiteUnramifiedRestriction
          rationalCyclotomicDegreeData
          (H.toFiniteResidueAbstractField rationalCyclotomicDegreeData)
          L.toFiniteGaloisExtension hUnramified
          ((rationalCyclotomicDegreeData.maximalUnramifiedDegreeEquiv
            (H.toFiniteResidueAbstractField
              rationalCyclotomicDegreeData)).symm
            (abstractFixedFieldCyclotomicGalEquivZHat H σ))) := by
  rfl

/-- In the canonical `ZHat` coordinate, the genuine cyclotomic Artin
symbol recovers the abstract maximal-unramified quotient class. -/
theorem
    abstractFixedFieldCyclotomicIdeleClassArtin_fixed_coordinate
    (H : FiniteAbstractField
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
    (a :
      ambientFixedAddSubgroup
        rationalIdeleClassRepresentation H.field) :
    (rationalCyclotomicDegreeData.maximalUnramifiedDegreeEquiv
        (H.toFiniteResidueAbstractField
          rationalCyclotomicDegreeData)).symm
        (abstractFixedFieldCyclotomicGalEquivZHat H
          (abstractFixedFieldCyclotomicIdeleClassArtinMonoidHom H
            (Additive.toMul
              ((rationalAbstractFixedFieldIdeleClassEquivFixed H.field
                (hfinite := H.finite)).symm
                a)))) =
      (ClassFormation.ValuationData.maximalUnramifiedNormResidueSymbol
        rationalCyclotomicIdeleClassValuationData H a).toMul := by
  apply
    (rationalCyclotomicDegreeData.maximalUnramifiedDegreeEquiv
      (H.toFiniteResidueAbstractField
        rationalCyclotomicDegreeData)).injective
  refine ((rationalCyclotomicDegreeData.maximalUnramifiedDegreeEquiv
    (H.toFiniteResidueAbstractField rationalCyclotomicDegreeData)).apply_symm_apply
      (abstractFixedFieldCyclotomicGalEquivZHat H
        (abstractFixedFieldCyclotomicIdeleClassArtinMonoidHom H
          (Additive.toMul
            ((rationalAbstractFixedFieldIdeleClassEquivFixed H.field
              (hfinite := H.finite)).symm a))))).trans ?_
  exact (congrArg (abstractFixedFieldCyclotomicGalEquivZHat H)
    (abstractFixedFieldCyclotomicIdeleClassArtin_eq_maximalUnramifiedNormResidue
      H a)).trans
        (abstractFixedFieldCyclotomicGalEquivZHat_quotientClass H
          (ClassFormation.ValuationData.maximalUnramifiedNormResidueSymbol
            rationalCyclotomicIdeleClassValuationData H a).toMul)

/-- On a fixed-part idele class, finite restriction of the genuine
cyclotomic Artin symbol is the finite restriction of the
maximal-unramified norm-residue symbol. -/
theorem
    abstractFixedFieldCyclotomicFiniteRestriction_ideleClassArtin_fixed
    (H : FiniteAbstractField
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
    (L : FiniteAbelianSubextension H.field)
    (hUnramified :
      L.toFiniteGaloisExtension.IsUnramified
        rationalCyclotomicDegreeData)
    (a :
      ambientFixedAddSubgroup
        rationalIdeleClassRepresentation H.field) :
    abstractFixedFieldCyclotomicFiniteRestrictionMonoidHom
        H L hUnramified
        (abstractFixedFieldCyclotomicIdeleClassArtinMonoidHom H
          (Additive.toMul
            ((rationalAbstractFixedFieldIdeleClassEquivFixed H.field
              (hfinite := H.finite)).symm
              a))) =
      (L.extensionQuotientMulEquiv.trans
        (LocalClassFieldTheory.abstractExtensionQuotientEquivGaloisGroup
          ℚ (SeparableClosure ℚ)
          H.field L.field L.below L.normal))
        (DegreeData.finiteUnramifiedRestriction
          rationalCyclotomicDegreeData
          (H.toFiniteResidueAbstractField
            rationalCyclotomicDegreeData)
          L.toFiniteGaloisExtension hUnramified
          (ClassFormation.ValuationData.maximalUnramifiedNormResidueSymbol
            rationalCyclotomicIdeleClassValuationData H a).toMul) := by
  let qFinite :=
    L.toFiniteGaloisExtension.extensionQuotientMulEquiv.trans
      (LocalClassFieldTheory.abstractExtensionQuotientEquivGaloisGroup
        ℚ (SeparableClosure ℚ)
        H.field L.field L.below L.normal)
  let finiteRestriction :=
    DegreeData.finiteUnramifiedRestriction
      rationalCyclotomicDegreeData
      (H.toFiniteResidueAbstractField rationalCyclotomicDegreeData)
      L.toFiniteGaloisExtension hUnramified
  let degreeEquiv :=
    rationalCyclotomicDegreeData.maximalUnramifiedDegreeEquiv
      (H.toFiniteResidueAbstractField rationalCyclotomicDegreeData)
  let galEquiv := abstractFixedFieldCyclotomicGalEquivZHat H
  let c :=
    abstractFixedFieldCyclotomicIdeleClassArtinMonoidHom H
      (Additive.toMul
        ((rationalAbstractFixedFieldIdeleClassEquivFixed H.field
          (hfinite := H.finite)).symm a))
  calc
    abstractFixedFieldCyclotomicFiniteRestrictionMonoidHom
        H L hUnramified c =
      qFinite (finiteRestriction (degreeEquiv.symm (galEquiv c))) := rfl
    _ = qFinite
        (finiteRestriction
          (ClassFormation.ValuationData.maximalUnramifiedNormResidueSymbol
            rationalCyclotomicIdeleClassValuationData H a).toMul) :=
      congrArg (fun q ↦ qFinite (finiteRestriction q))
        (abstractFixedFieldCyclotomicIdeleClassArtin_fixed_coordinate H a)

/-- The actual fixed-field global norm-residue value on a fixed-part
class is the finite restriction of the maximal-unramified cyclotomic
symbol. -/
theorem
    abstractFixedFieldGlobalNormResidueMonoidHom_fixed_eq_finiteUnramifiedRestriction
    (H : FiniteAbstractField
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
    (L : FiniteAbelianSubextension H.field)
    (hUnramified :
      L.toFiniteGaloisExtension.IsUnramified
        rationalCyclotomicDegreeData)
    (a :
      ambientFixedAddSubgroup
        rationalIdeleClassRepresentation H.field) :
    abstractFixedFieldGlobalNormResidueMonoidHom H L
        (Additive.toMul
          ((rationalAbstractFixedFieldIdeleClassEquivFixed H.field
            (hfinite := H.finite)).symm
            a)) =
      (L.extensionQuotientMulEquiv.trans
        (LocalClassFieldTheory.abstractExtensionQuotientEquivGaloisGroup
          ℚ (SeparableClosure ℚ)
          H.field L.field L.below L.normal))
        (DegreeData.finiteUnramifiedRestriction
          rationalCyclotomicDegreeData
          (H.toFiniteResidueAbstractField
            rationalCyclotomicDegreeData)
          L.toFiniteGaloisExtension hUnramified
          (ClassFormation.ValuationData.maximalUnramifiedNormResidueSymbol
            rationalCyclotomicIdeleClassValuationData H a).toMul) := by
  let : Finite
      (H.field.toSubgroup ⧸
        CyclicCohomology.extensionSubgroup H.field L.field L.below) :=
    L.finite
  let : IsMulCommutative L.extensionQuotient :=
    L.commutative
  let q : L.extensionQuotient :=
    DegreeData.finiteUnramifiedRestriction
      rationalCyclotomicDegreeData
      (H.toFiniteResidueAbstractField rationalCyclotomicDegreeData)
      L.toFiniteGaloisExtension hUnramified
      (ClassFormation.ValuationData.maximalUnramifiedNormResidueSymbol
        rationalCyclotomicIdeleClassValuationData H a).toMul
  rw [abstractFixedFieldGlobalNormResidueMonoidHom_fixed_apply]
  change
    Additive.toMul
      (abstractFixedFieldAbelianizedExtensionQuotientEquivGaloisGroup H L
        (rationalCyclotomicDegreeData.normResidueSymbol
          rationalIdeleClassRepresentation
          rationalCyclotomicIdeleClassValuationData
          rationalIdeleClassRepresentation_satisfiesClassFieldAxiom
          H L.toFiniteGaloisExtension
          (finiteNormClass rationalIdeleClassRepresentation
            H.field L.field L.below a))) =
      _
  calc
    _ =
        Additive.toMul
          (abstractFixedFieldAbelianizedExtensionQuotientEquivGaloisGroup H L
            (Additive.ofMul (Abelianization.of q))) :=
      congrArg
        (fun z =>
          Additive.toMul
            (abstractFixedFieldAbelianizedExtensionQuotientEquivGaloisGroup
              H L z))
        (ClassFormation.ValuationData.normResidueSymbol_finiteNormClass_eq_maximalUnramifiedRestriction
          rationalCyclotomicIdeleClassValuationData
          rationalIdeleClassRepresentation_satisfiesClassFieldAxiom
          H L.toFiniteGaloisExtension hUnramified a)
    _ = _ := by
      rw [abstractFixedFieldAbelianizedExtensionQuotientEquivGaloisGroup_of]
      exact toMul_ofMul _

/-- Finite restriction of the genuine cyclotomic chosen-local-factor
Artin map is exactly the actual global norm-residue map for every
finite unramified abelian fixed-field extension. -/
theorem
    abstractFixedFieldGlobalNormResidueMonoidHom_eq_cyclotomicFiniteRestriction
    (H : FiniteAbstractField
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
    (L : FiniteAbelianSubextension H.field)
    (hUnramified :
      L.toFiniteGaloisExtension.IsUnramified
        rationalCyclotomicDegreeData)
    (c :
      IdeleClassGroup
        (LocalClassFieldTheory.abstractFixedField
          ℚ (SeparableClosure ℚ) H.field)) :
    abstractFixedFieldGlobalNormResidueMonoidHom H L c =
      abstractFixedFieldCyclotomicFiniteRestrictionMonoidHom
        H L hUnramified
        (abstractFixedFieldCyclotomicIdeleClassArtinMonoidHom H c) := by
  let e :=
    rationalAbstractFixedFieldIdeleClassEquivFixed H.field
      (hfinite := H.finite)
  let a :
      ambientFixedAddSubgroup
        rationalIdeleClassRepresentation H.field :=
    e (Additive.ofMul c)
  have hc :
      Additive.toMul (e.symm a) = c := by
    apply Additive.ofMul.injective
    change e.symm (e (Additive.ofMul c)) = Additive.ofMul c
    exact e.symm_apply_apply _
  calc
    abstractFixedFieldGlobalNormResidueMonoidHom H L c =
        abstractFixedFieldGlobalNormResidueMonoidHom H L
          (Additive.toMul (e.symm a)) := by rw [hc]
    _ =
        (L.extensionQuotientMulEquiv.trans
          (LocalClassFieldTheory.abstractExtensionQuotientEquivGaloisGroup
            ℚ (SeparableClosure ℚ)
            H.field L.field L.below L.normal))
          (DegreeData.finiteUnramifiedRestriction
            rationalCyclotomicDegreeData
            (H.toFiniteResidueAbstractField
              rationalCyclotomicDegreeData)
            L.toFiniteGaloisExtension hUnramified
            (ClassFormation.ValuationData.maximalUnramifiedNormResidueSymbol
              rationalCyclotomicIdeleClassValuationData H a).toMul) :=
      abstractFixedFieldGlobalNormResidueMonoidHom_fixed_eq_finiteUnramifiedRestriction
        H L hUnramified a
    _ =
        abstractFixedFieldCyclotomicFiniteRestrictionMonoidHom
          H L hUnramified
          (abstractFixedFieldCyclotomicIdeleClassArtinMonoidHom H
            (Additive.toMul (e.symm a))) :=
      (abstractFixedFieldCyclotomicFiniteRestriction_ideleClassArtin_fixed
        H L hUnramified a).symm
    _ =
        abstractFixedFieldCyclotomicFiniteRestrictionMonoidHom
          H L hUnramified
          (abstractFixedFieldCyclotomicIdeleClassArtinMonoidHom H c) :=
      congrArg
        (fun z =>
          abstractFixedFieldCyclotomicFiniteRestrictionMonoidHom
            H L hUnramified
            (abstractFixedFieldCyclotomicIdeleClassArtinMonoidHom H z))
        hc

end Reciprocity
end GlobalClassFieldTheory
end
end

section
-- module Solutions.OAIQ244_DUKE.GlobalClassFieldTheory_Reciprocity_CyclotomicUnramifiedGeometricRestriction
attribute [-instance] _root_.GlobalClassFieldTheory.GlobalClassFields.bigHilbertClassFieldNormSubgroup_normal _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexNormAmbientFiniteDimensional _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexNormAmbientIsGalois _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexNormAmbientNumberField _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexNormCyclotomicFieldFiniteDimensional _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexNormCyclotomicFieldIsGalois _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexNormCyclotomicFieldNumberField _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexNormKummerFieldAlgebraOverBase _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexNormKummerFieldFiniteDimensional _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexNormKummerFieldFiniteDimensionalOverBase _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexNormKummerFieldModuleOverBase _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexNormKummerFieldNumberField _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexNormKummerFieldSMulOverBase _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexNormKummerFieldScalarTower _root_.GlobalClassFieldTheory.GlobalClassFields.ordinaryNormClassFieldBaseFiniteDimensional _root_.GlobalClassFieldTheory.GlobalClassFields.ordinaryNormClassFieldBaseNumberField _root_.GlobalClassFieldTheory.Reciprocity.complexFourthRootField_finiteDimensional _root_.GlobalClassFieldTheory.Reciprocity.infinitePlaceComplexificationOverfield_baseSmul _root_.GlobalClassFieldTheory.Reciprocity.infinitePlaceComplexificationOverfield_finiteDimensional _root_.GlobalClassFieldTheory.Reciprocity.infinitePlaceComplexificationOverfield_smul _root_.GlobalClassFieldTheory.Reciprocity.rationalComplexification_infinitePlaceOverfield_algebra _root_.GlobalClassFieldTheory.Reciprocity.rationalComplexification_infinitePlaceOverfield_smul _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.boundedRealFields_finite _root_.OAI.PrimeDegreePackets.instTopologicalSpaceLocalAlgebra _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.GlobalClassFieldTheory.GlobalClassFields.bigHilbertNormQuotient_finite _root_.GlobalClassFieldTheory.GlobalClassFields.narrowClassGroup_finite
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
# Geometric restriction from the cyclotomic unramified field

An abstractly unramified finite abelian subextension is contained in the
actual cyclotomic maximal-unramified fixed field.  This file realizes that
containment as an algebra tower and proves that the finite restriction
defined on quotient presentations is literally restriction of field
automorphisms.

The field-range form of the finite layer is also bundled in the finite
Galois inverse system.  Consequently the geometric restriction of the
infinite global Artin map is the ordinary finite global Artin map.
-/

open scoped IsMulCommutative NumberField

noncomputable section

namespace GlobalClassFieldTheory
namespace Reciprocity

open ClassFormation
open GlobalClassFields
open KummerTheory
open LocalClassFieldTheory

attribute [local instance] GlobalClassFieldTheory.Reciprocity.cyclotomicUnramifiedGeometricRationalSeparableClosureAlgebra
local instance cyclotomicUnramifiedGeometricBaseQuotientFinite
    (H : FiniteAbstractField
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ)) :
    Finite
      ((baseField
        (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ)).toSubgroup ⧸
        CyclicCohomology.extensionSubgroup
          (baseField
            (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
          H.field (le_baseField H.field)) :=
  H.finite

local instance cyclotomicUnramifiedGeometricRelativeQuotientFinite_rfd8e8e_1
    (H : FiniteAbstractField
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
    (L : FiniteAbelianSubextension H.field) :
    Finite
      (H.field.toSubgroup ⧸
        CyclicCohomology.extensionSubgroup
          H.field L.field L.below) :=
  L.finite
noncomputable local instance
    cyclotomicUnramifiedGeometricBaseFiniteDimensional
    (H : FiniteAbstractField
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ)) :
    FiniteDimensional ℚ
      (abstractFixedField ℚ (SeparableClosure ℚ) H.field) :=
  abstractFixedField_finiteDimensional
    ℚ (SeparableClosure ℚ) H.field H.finite

noncomputable local instance
    cyclotomicUnramifiedGeometricRelativeFiniteDimensional
    (H : FiniteAbstractField
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
    (L : FiniteAbelianSubextension H.field) :
    FiniteDimensional
      (abstractFixedField ℚ (SeparableClosure ℚ) H.field)
      (abstractRelativeFixedField
        ℚ (SeparableClosure ℚ) L.below) :=
  finiteAbelianSubextensionAbstractRelativeFixedFieldFiniteDimensional L

local instance
    cyclotomicUnramifiedGeometricRelativeScalarTower
    (H : FiniteAbstractField
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
    (L : FiniteAbelianSubextension H.field) :
    IsScalarTower ℚ
      (abstractFixedField ℚ (SeparableClosure ℚ) H.field)
      (abstractRelativeFixedField
        ℚ (SeparableClosure ℚ) L.below) :=
  IsScalarTower.of_algebraMap_eq' rfl

noncomputable local instance
    cyclotomicUnramifiedGeometricRelativeAbsoluteFiniteDimensional
    (H : FiniteAbstractField
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
    (L : FiniteAbelianSubextension H.field) :
    FiniteDimensional ℚ
      (abstractRelativeFixedField
        ℚ (SeparableClosure ℚ) L.below) :=
  FiniteDimensional.trans ℚ
    (abstractFixedField ℚ (SeparableClosure ℚ) H.field)
    (abstractRelativeFixedField
      ℚ (SeparableClosure ℚ) L.below)

noncomputable local instance
    cyclotomicUnramifiedGeometricBaseNumberField
    (H : FiniteAbstractField
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ)) :
    NumberField
      (abstractFixedField ℚ (SeparableClosure ℚ) H.field) :=
  NumberField.of_module_finite ℚ
    (abstractFixedField ℚ (SeparableClosure ℚ) H.field)

noncomputable local instance
    cyclotomicUnramifiedGeometricRelativeNumberField
    (H : FiniteAbstractField
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
    (L : FiniteAbelianSubextension H.field) :
    NumberField
      (abstractRelativeFixedField
        ℚ (SeparableClosure ℚ) L.below) :=
  NumberField.of_module_finite ℚ
    (abstractRelativeFixedField
      ℚ (SeparableClosure ℚ) L.below)

noncomputable local instance
    cyclotomicUnramifiedGeometricRelativeIsAbelianGalois
    (H : FiniteAbstractField
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
    (L : FiniteAbelianSubextension H.field) :
    IsAbelianGalois
      (abstractFixedField ℚ (SeparableClosure ℚ) H.field)
      (abstractRelativeFixedField
        ℚ (SeparableClosure ℚ) L.below) :=
  finiteAbelianSubextensionAbstractRelativeFixedFieldIsAbelianGalois L

noncomputable local instance
    cyclotomicUnramifiedGeometricRelativeNormal
    (H : FiniteAbstractField
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
    (L : FiniteAbelianSubextension H.field) :
    Normal
      (abstractFixedField ℚ (SeparableClosure ℚ) H.field)
      (abstractRelativeFixedField
        ℚ (SeparableClosure ℚ) L.below) :=
  (cyclotomicUnramifiedGeometricRelativeIsAbelianGalois
    H L).toIsGalois.to_normal

noncomputable local instance
    cyclotomicUnramifiedGeometricMaximalIsAbelianGalois
    (H : FiniteAbstractField
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ)) :
    IsAbelianGalois
      (abstractFixedField ℚ (SeparableClosure ℚ) H.field)
      (abstractRelativeFixedField
        ℚ (SeparableClosure ℚ)
        (rationalCyclotomicFieldInertia_le H.field)) :=
  abstractFixedFieldCyclotomic_isAbelianGalois H

/-- Normality of the extension subgroup defining the cyclotomic
maximal-unramified layer.  Naming it keeps the quotient equivalence and
its evaluation lemma on the same proof parameter. -/
instance cyclotomicUnramifiedGeometricMaxExtensionNormal
    (H : FiniteAbstractField
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ)) :
    (CyclicCohomology.extensionSubgroup H.field
        (rationalCyclotomicDegreeData.fieldInertia H.field)
        (rationalCyclotomicFieldInertia_le H.field)).Normal :=
  (extensionSubgroup_rationalCyclotomicFieldInertia H.field).symm ▸
    DegreeData.fieldInertiaWithin_normal
      rationalCyclotomicDegreeData H.field

/-- The quotient presentation of the cyclotomic maximal-unramified
Galois group used by geometric restriction. -/
noncomputable abbrev
    cyclotomicUnramifiedGeometricMaxQuotientEquiv
    (H : FiniteAbstractField
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ)) :
    H.field.toSubgroup ⧸
          CyclicCohomology.extensionSubgroup H.field
            (rationalCyclotomicDegreeData.fieldInertia H.field)
            (rationalCyclotomicFieldInertia_le H.field) ≃*
      Gal(
        abstractRelativeFixedField
            ℚ (SeparableClosure ℚ)
            (rationalCyclotomicFieldInertia_le H.field) /
          abstractFixedField ℚ (SeparableClosure ℚ) H.field) :=
  LocalClassFieldTheory.abstractExtensionQuotientEquivGaloisGroup
    ℚ (SeparableClosure ℚ) H.field
    (rationalCyclotomicDegreeData.fieldInertia H.field)
    (rationalCyclotomicFieldInertia_le H.field)
    (cyclotomicUnramifiedGeometricMaxExtensionNormal H)

/-- The equality of the two inertia subgroups, bundled once as the
quotient equivalence used by geometric restriction. -/
noncomputable abbrev
    cyclotomicUnramifiedGeometricInertiaQuotientEquiv
    (H : FiniteAbstractField
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ)) :
    H.field.toSubgroup ⧸
          CyclicCohomology.extensionSubgroup H.field
            (rationalCyclotomicDegreeData.fieldInertia H.field)
            (rationalCyclotomicFieldInertia_le H.field) ≃*
      H.field.toSubgroup ⧸
        rationalCyclotomicDegreeData.fieldInertiaWithin H.field :=
  by
    letI maxExtensionNormal :
        (CyclicCohomology.extensionSubgroup H.field
          (rationalCyclotomicDegreeData.fieldInertia H.field)
          (rationalCyclotomicFieldInertia_le H.field)).Normal :=
      cyclotomicUnramifiedGeometricMaxExtensionNormal H
    exact @QuotientGroup.quotientMulEquivOfEq
      _ _ _ _ maxExtensionNormal
      (DegreeData.fieldInertiaWithin_normal
        rationalCyclotomicDegreeData H.field)
      (extensionSubgroup_rationalCyclotomicFieldInertia H.field)

/-- The quotient presentation of the finite fixed-field Galois group
used throughout the geometric comparison. -/
noncomputable abbrev
    cyclotomicUnramifiedGeometricFiniteQuotientEquiv
    (H : FiniteAbstractField
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
    (L : FiniteAbelianSubextension H.field) :
    L.toFiniteGaloisExtension.extensionQuotient ≃*
      Gal(
        abstractRelativeFixedField
            ℚ (SeparableClosure ℚ) L.below /
          abstractFixedField ℚ (SeparableClosure ℚ) H.field) :=
  L.toFiniteGaloisExtension.extensionQuotientMulEquiv.trans
    (LocalClassFieldTheory.abstractExtensionQuotientEquivGaloisGroup
      ℚ (SeparableClosure ℚ)
      H.field L.field L.below L.normal)

/-- The finite restriction in the geometric quotient coordinate. -/
theorem cyclotomicUnramifiedGeometricRestriction_apply
    (H : FiniteAbstractField
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
    (L : FiniteAbelianSubextension H.field)
    (hUnramified :
      L.toFiniteGaloisExtension.IsUnramified rationalCyclotomicDegreeData)
    (σ : Gal(
      abstractRelativeFixedField ℚ (SeparableClosure ℚ)
          (rationalCyclotomicFieldInertia_le H.field) /
        abstractFixedField ℚ (SeparableClosure ℚ) H.field)) :
    abstractFixedFieldCyclotomicFiniteRestrictionMonoidHom
        H L hUnramified σ =
      (L.toFiniteGaloisExtension.extensionQuotientMulEquiv.trans
        (LocalClassFieldTheory.abstractExtensionQuotientEquivGaloisGroup
          ℚ (SeparableClosure ℚ)
          H.field L.field L.below L.normal))
        (DegreeData.finiteUnramifiedRestriction
          rationalCyclotomicDegreeData
          (H.toFiniteResidueAbstractField rationalCyclotomicDegreeData)
          L.toFiniteGaloisExtension hUnramified
          ((cyclotomicUnramifiedGeometricInertiaQuotientEquiv H)
            ((cyclotomicUnramifiedGeometricMaxQuotientEquiv H).symm σ))) := by
  let qMax := cyclotomicUnramifiedGeometricMaxQuotientEquiv H
  let qInertia := cyclotomicUnramifiedGeometricInertiaQuotientEquiv H
  let degreeEquiv :=
    rationalCyclotomicDegreeData.maximalUnramifiedDegreeEquiv
      (H.toFiniteResidueAbstractField rationalCyclotomicDegreeData)
  let finiteRestriction :=
    DegreeData.finiteUnramifiedRestriction
      rationalCyclotomicDegreeData
      (H.toFiniteResidueAbstractField rationalCyclotomicDegreeData)
      L.toFiniteGaloisExtension hUnramified
  have hCoordinate :=
    abstractFixedFieldCyclotomicGalEquivZHat_quotientClass H
      (qInertia (qMax.symm σ))
  have hCoordinate' :
      abstractFixedFieldCyclotomicGalEquivZHat H σ =
        degreeEquiv (qInertia (qMax.symm σ)) := by
    change
      abstractFixedFieldCyclotomicGalEquivZHat H
          (qMax (qInertia.symm (qInertia (qMax.symm σ)))) =
        degreeEquiv (qInertia (qMax.symm σ)) at hCoordinate
    rw [qInertia.symm_apply_apply] at hCoordinate
    exact (congrArg (abstractFixedFieldCyclotomicGalEquivZHat H)
      (qMax.apply_symm_apply σ)).symm.trans hCoordinate
  have hArg :
      degreeEquiv.symm
          (abstractFixedFieldCyclotomicGalEquivZHat H σ) =
        qInertia (qMax.symm σ) :=
    (congrArg degreeEquiv.symm hCoordinate').trans
      (degreeEquiv.symm_apply_apply _)
  calc
    _ = (L.toFiniteGaloisExtension.extensionQuotientMulEquiv.trans
        (LocalClassFieldTheory.abstractExtensionQuotientEquivGaloisGroup
          ℚ (SeparableClosure ℚ)
          H.field L.field L.below L.normal))
        (finiteRestriction
          (degreeEquiv.symm
            (abstractFixedFieldCyclotomicGalEquivZHat H σ))) :=
      abstractFixedFieldCyclotomicFiniteRestrictionMonoidHom_apply
        H L hUnramified σ
    _ = _ :=
      congrArg
        (fun q =>
          (L.toFiniteGaloisExtension.extensionQuotientMulEquiv.trans
            (LocalClassFieldTheory.abstractExtensionQuotientEquivGaloisGroup
              ℚ (SeparableClosure ℚ)
              H.field L.field L.below L.normal))
            (finiteRestriction q)) hArg

/-- On a representative of the maximal-unramified quotient, finite
restriction is restriction of the corresponding field automorphism. -/
theorem cyclotomicUnramifiedGeometricRestriction_mk
    (H : FiniteAbstractField
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
    (L : FiniteAbelianSubextension H.field)
    (hUnramified :
      L.toFiniteGaloisExtension.IsUnramified rationalCyclotomicDegreeData)
    (τ : H.field.toSubgroup) :
    let F := abstractFixedField ℚ (SeparableClosure ℚ) H.field
    let E := abstractRelativeFixedField ℚ (SeparableClosure ℚ) L.below
    let U := abstractRelativeFixedField ℚ (SeparableClosure ℚ)
      (rationalCyclotomicFieldInertia_le H.field)
    letI _ : Algebra E U :=
      abstractFixedFieldCyclotomicFiniteUnramifiedInclusionAlgebra
        H L hUnramified
    letI _ : @IsScalarTower F E U
        Algebra.toSMul Algebra.toSMul Algebra.toSMul :=
      IsScalarTower.of_algHom
        (abstractFixedFieldCyclotomicFiniteUnramifiedInclusion
          H L hUnramified)
    (cyclotomicUnramifiedGeometricFiniteQuotientEquiv H L)
      (DegreeData.finiteUnramifiedRestriction
        rationalCyclotomicDegreeData
        (H.toFiniteResidueAbstractField rationalCyclotomicDegreeData)
        L.toFiniteGaloisExtension hUnramified
        ((cyclotomicUnramifiedGeometricInertiaQuotientEquiv H)
          (QuotientGroup.mk τ))) =
      AlgEquiv.restrictNormalHom E
        ((cyclotomicUnramifiedGeometricMaxQuotientEquiv H)
          (QuotientGroup.mk τ)) := by
  dsimp only
  let F := abstractFixedField ℚ (SeparableClosure ℚ) H.field
  let E := abstractRelativeFixedField ℚ (SeparableClosure ℚ) L.below
  let hI := rationalCyclotomicFieldInertia_le H.field
  let U := abstractRelativeFixedField ℚ (SeparableClosure ℚ) hI
  let _ : Algebra E U :=
    abstractFixedFieldCyclotomicFiniteUnramifiedInclusionAlgebra
      H L hUnramified
  let _ : @IsScalarTower F E U
      Algebra.toSMul Algebra.toSMul Algebra.toSMul :=
    IsScalarTower.of_algHom
      (abstractFixedFieldCyclotomicFiniteUnramifiedInclusion
        H L hUnramified)
  let qMax := cyclotomicUnramifiedGeometricMaxQuotientEquiv H
  let qInertia := cyclotomicUnramifiedGeometricInertiaQuotientEquiv H
  let qFinite := cyclotomicUnramifiedGeometricFiniteQuotientEquiv H L
  let finiteRestriction :=
    DegreeData.finiteUnramifiedRestriction
      rationalCyclotomicDegreeData
      (H.toFiniteResidueAbstractField rationalCyclotomicDegreeData)
      L.toFiniteGaloisExtension hUnramified
  have hInertia :
      qInertia (QuotientGroup.mk τ) =
        (QuotientGroup.mk τ :
          H.field.toSubgroup ⧸
            rationalCyclotomicDegreeData.fieldInertiaWithin H.field) :=
    QuotientGroup.quotientMulEquivOfEq_mk
      (extensionSubgroup_rationalCyclotomicFieldInertia H.field) τ
  refine (congrArg (fun z => qFinite (finiteRestriction z)) hInertia).trans ?_
  have hFiniteRestriction :=
    DegreeData.finiteUnramifiedRestriction_mk
      rationalCyclotomicDegreeData
      (H.toFiniteResidueAbstractField rationalCyclotomicDegreeData)
      L.toFiniteGaloisExtension hUnramified τ
  refine (congrArg qFinite hFiniteRestriction).trans ?_
  apply AlgEquiv.ext
  intro x
  apply Subtype.ext
  have hE :=
    LocalClassFieldTheory.abstractExtensionQuotientEquivGaloisGroup_mk_apply_val
      ℚ (SeparableClosure ℚ)
      H.field L.field L.below L.normal τ x
  have hU :=
    LocalClassFieldTheory.abstractExtensionQuotientEquivGaloisGroup_mk_apply_val
      ℚ (SeparableClosure ℚ)
      H.field
      (rationalCyclotomicDegreeData.fieldInertia H.field)
      hI (cyclotomicUnramifiedGeometricMaxExtensionNormal H) τ
      (algebraMap E U x)
  change
    τ.1 ((algebraMap E U x : U).1) =
      (qMax (QuotientGroup.mk τ) (algebraMap E U x)).1 at hU
  have hInclusion :
      ((algebraMap E U x : U) : SeparableClosure ℚ) =
        (x : SeparableClosure ℚ) :=
    rfl
  have hτ := congrArg
    (fun y : SeparableClosure ℚ => τ.1 y) hInclusion.symm
  have hRestrict :=
    AlgEquiv.restrictNormal_commutes
      (qMax (QuotientGroup.mk τ)) E x
  have hRestrictVal := congrArg
    (fun y : U => (y : SeparableClosure ℚ)) hRestrict
  exact hE.symm.trans (hτ.trans (hU.trans hRestrictVal.symm))

/-- Geometric restriction on an arbitrary maximal-unramified quotient class. -/
theorem cyclotomicUnramifiedGeometricRestriction_quotient
    (H : FiniteAbstractField
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
    (L : FiniteAbelianSubextension H.field)
    (hUnramified :
      L.toFiniteGaloisExtension.IsUnramified rationalCyclotomicDegreeData)
    (q : H.field.toSubgroup ⧸
      CyclicCohomology.extensionSubgroup H.field
        (rationalCyclotomicDegreeData.fieldInertia H.field)
        (rationalCyclotomicFieldInertia_le H.field)) :
    let F := abstractFixedField ℚ (SeparableClosure ℚ) H.field
    let E := abstractRelativeFixedField ℚ (SeparableClosure ℚ) L.below
    let U := abstractRelativeFixedField ℚ (SeparableClosure ℚ)
      (rationalCyclotomicFieldInertia_le H.field)
    letI _ : Algebra E U :=
      abstractFixedFieldCyclotomicFiniteUnramifiedInclusionAlgebra
        H L hUnramified
    letI _ : @IsScalarTower F E U
        Algebra.toSMul Algebra.toSMul Algebra.toSMul :=
      IsScalarTower.of_algHom
        (abstractFixedFieldCyclotomicFiniteUnramifiedInclusion
          H L hUnramified)
    abstractFixedFieldCyclotomicFiniteRestrictionMonoidHom
        H L hUnramified
        ((cyclotomicUnramifiedGeometricMaxQuotientEquiv H) q) =
      AlgEquiv.restrictNormalHom E
        ((cyclotomicUnramifiedGeometricMaxQuotientEquiv H) q) := by
  dsimp only
  induction q using QuotientGroup.induction_on with
  | _ τ =>
      let qMax := cyclotomicUnramifiedGeometricMaxQuotientEquiv H
      let qInertia := cyclotomicUnramifiedGeometricInertiaQuotientEquiv H
      let qFinite := cyclotomicUnramifiedGeometricFiniteQuotientEquiv H L
      let finiteRestriction :=
        DegreeData.finiteUnramifiedRestriction
          rationalCyclotomicDegreeData
          (H.toFiniteResidueAbstractField rationalCyclotomicDegreeData)
          L.toFiniteGaloisExtension hUnramified
      have hProjection :
          qInertia (qMax.symm (qMax (QuotientGroup.mk τ))) =
            qInertia (QuotientGroup.mk τ) :=
        congrArg qInertia (qMax.symm_apply_apply (QuotientGroup.mk τ))
      exact
        ((cyclotomicUnramifiedGeometricRestriction_apply
            H L hUnramified (qMax (QuotientGroup.mk τ))).trans
          (congrArg (fun z => qFinite (finiteRestriction z)) hProjection)).trans
          (cyclotomicUnramifiedGeometricRestriction_mk H L hUnramified τ)

/-- The quotient-defined restriction to a finite unramified
subextension is the genuine restriction of automorphisms of its
cyclotomic maximal-unramified overfield. -/
theorem
    abstractFixedFieldCyclotomicFiniteRestrictionMonoidHom_eq_restrictNormalHom
    (H : FiniteAbstractField
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
    (L : FiniteAbelianSubextension H.field)
    (hUnramified :
      L.toFiniteGaloisExtension.IsUnramified
        rationalCyclotomicDegreeData) :
    let F :=
      abstractFixedField ℚ (SeparableClosure ℚ) H.field
    let E :=
      abstractRelativeFixedField
        ℚ (SeparableClosure ℚ) L.below
    let U :=
      abstractRelativeFixedField
        ℚ (SeparableClosure ℚ)
        (rationalCyclotomicFieldInertia_le H.field)
    letI _ : Algebra E U :=
      abstractFixedFieldCyclotomicFiniteUnramifiedInclusionAlgebra
        H L hUnramified
    letI _ : @IsScalarTower F E U
        Algebra.toSMul Algebra.toSMul Algebra.toSMul :=
      IsScalarTower.of_algHom
        (abstractFixedFieldCyclotomicFiniteUnramifiedInclusion
          H L hUnramified)
    abstractFixedFieldCyclotomicFiniteRestrictionMonoidHom
        H L hUnramified =
      (AlgEquiv.restrictNormalHom E :
        (U ≃ₐ[F] U) →* (E ≃ₐ[F] E)) := by
  dsimp only
  apply MonoidHom.ext
  intro σ
  have hσ :
      (cyclotomicUnramifiedGeometricMaxQuotientEquiv H)
          ((cyclotomicUnramifiedGeometricMaxQuotientEquiv H).symm σ) = σ :=
    (cyclotomicUnramifiedGeometricMaxQuotientEquiv H).apply_symm_apply σ
  exact hσ ▸
    (cyclotomicUnramifiedGeometricRestriction_quotient
      H L hUnramified
      ((cyclotomicUnramifiedGeometricMaxQuotientEquiv H).symm σ))

end Reciprocity
end GlobalClassFieldTheory
end
end

section
-- module Solutions.OAIQ244_DUKE.GlobalClassFieldTheory_Reciprocity_CyclotomicUnramifiedLocalGlobalCompatibility
attribute [-instance] _root_.GlobalClassFieldTheory.GlobalClassFields.ConductorialSubgroup.finiteIndex _root_.GlobalClassFieldTheory.GlobalClassFields.bigHilbertClassFieldNormSubgroup_normal _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexNormAmbientFiniteDimensional _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexNormAmbientIsGalois _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexNormAmbientNumberField _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexNormCyclotomicFieldFiniteDimensional _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexNormCyclotomicFieldIsCyclotomicExtension _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexNormCyclotomicFieldIsGalois _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexNormCyclotomicFieldNumberField _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexNormExponentNeZero _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexNormKummerFieldAlgebraOverBase _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexNormKummerFieldFiniteDimensional _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexNormKummerFieldFiniteDimensionalOverBase _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexNormKummerFieldModuleOverBase _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexNormKummerFieldNumberField _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexNormKummerFieldSMulOverBase _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexNormKummerFieldScalarTower _root_.GlobalClassFieldTheory.GlobalClassFields.ideleClassNorm_rangeFiniteIndex _root_.GlobalClassFieldTheory.GlobalClassFields.ordinaryNormClassFieldBaseFiniteDimensional _root_.GlobalClassFieldTheory.GlobalClassFields.smallHilbertClassFieldNormSubgroupFiniteIndex _root_.GlobalClassFieldTheory.Reciprocity.infinitePlaceComplexificationOverfield_algebra _root_.GlobalClassFieldTheory.Reciprocity.infinitePlaceComplexificationOverfield_baseAlgebra _root_.GlobalClassFieldTheory.Reciprocity.infinitePlaceComplexificationOverfield_baseSmul _root_.GlobalClassFieldTheory.Reciprocity.infinitePlaceComplexificationOverfield_smul _root_.GlobalClassFieldTheory.Reciprocity.ramifiedInfinitePlaceRealFixedField_algebra _root_.GlobalClassFieldTheory.Reciprocity.rationalComplexification_infinitePlaceOverfield_algebra _root_.GlobalClassFieldTheory.Reciprocity.rationalComplexification_infinitePlaceOverfield_smul _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.diagonalLogAction _root_.OAI.PrimeDegreePackets.instTopologicalSpaceLocalAlgebra _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.GlobalClassFieldTheory.GlobalClassFields.bigHilbertNormQuotient_finite _root_.GlobalClassFieldTheory.GlobalClassFields.bigHilbertNormSubgroup_finiteIndex
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
theorem
    restrictNormalHom_comp_infiniteGlobalArtinMonoidHom_of_tower
    (K E Ω : Type) [Field K] [NumberField K]
    [Field E] [NumberField E] [Algebra K E]
    [IsAbelianGalois K E]
    [Field Ω] [Algebra K Ω] [Algebra E Ω]
    [IsScalarTower K E Ω] [IsAbelianGalois K Ω] :
    (AlgEquiv.restrictNormalHom E).comp
        (infiniteGlobalArtinMonoidHom K Ω).toMonoidHom =
      globalArtinMonoidHom (K := K) (L := E) := by
  apply MonoidHom.ext
  intro a
  let j : E →ₐ[K] Ω := IsScalarTower.toAlgHom K E Ω
  let G : FiniteGaloisIntermediateField K Ω :=
    { toIntermediateField := j.fieldRange
      finiteDimensional :=
        j.equivFieldRange.toLinearEquiv.finiteDimensional
      isGalois := IsGalois.of_algEquiv j.equivFieldRange }
  let _ : FiniteDimensional K G := G.finiteDimensional
  let _ : NumberField G :=
    NumberField.of_module_finite K G
  let _ : IsAbelianGalois K G :=
    IsAbelianGalois.of_algHom G.toIntermediateField.val
  let _ : Algebra E G :=
    j.equivFieldRange.toRingHom.toAlgebra
  let _ : SMul E G := Algebra.toSMul
  let _ : IsScalarTower K E G :=
    IsScalarTower.of_algHom j.equivFieldRange.toAlgHom
  let _ : IsScalarTower K G Ω :=
    IntermediateField.isScalarTower_mid G.toIntermediateField
  let _ : IsScalarTower E G Ω :=
    IsScalarTower.of_algebraMap_eq fun _ => rfl
  have hProjection :
      AlgEquiv.restrictNormalHom G
          (infiniteGlobalArtinMonoidHom K Ω a) =
        globalArtinMonoidHom (K := K) (L := G) a :=
    restrictNormalHom_infiniteGlobalArtinMonoidHom K Ω a G
  calc
    AlgEquiv.restrictNormalHom E
          (infiniteGlobalArtinMonoidHom K Ω a) =
        AlgEquiv.restrictNormalHom E
          (AlgEquiv.restrictNormalHom G
            (infiniteGlobalArtinMonoidHom K Ω a)) :=
      IsScalarTower.AlgEquiv.restrictNormalHom_comp_apply E G
        (infiniteGlobalArtinMonoidHom K Ω a)
    _ = AlgEquiv.restrictNormalHom E
          (globalArtinMonoidHom (K := K) (L := G) a) :=
      congrArg (AlgEquiv.restrictNormalHom E) hProjection
    _ = globalArtinMonoidHom (K := K) (L := E) a :=
      DFunLike.congr_fun
        (globalArtinMonoidHom_restrict_tower
          (K := K) (L := G) (E := E)) a

theorem globalArtinMonoidHom_comp_finitePlaceIdele
    (K E : Type) [Field K] [NumberField K]
    [Field E] [NumberField E] [Algebra K E]
    [IsAbelianGalois K E]
    (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K)) :
    (globalArtinMonoidHom (K := K) (L := E)).comp
        (IdeleGroup.finitePlaceIdele v) =
      chosenFinitePlaceArtinMonoidHom
        (K := K) (L := E) v := by
  apply MonoidHom.ext
  intro x
  exact globalArtinMonoidHom_finitePlaceIdele
    (K := K) (L := E) v x

end Reciprocity
end GlobalClassFieldTheory
end
end


