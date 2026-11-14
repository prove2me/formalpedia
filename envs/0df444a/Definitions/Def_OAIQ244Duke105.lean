-- Prove2me | Definitions.Def_OAIQ244Duke105
-- name    : OAIQ244Duke105
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-14T03:39:59.719056+00:00
-- url     : https://prove2.me/theorems/7001b6c7-5f4c-43f3-8f35-72d6fa235498
-- title:
--   Definitions bundle OAIQ244Duke105 of the split of OpenAI, Equidistribution of Prime-Degree Torus Packets with Arbitrary Local Type
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.DukePrimeDegree.prime_degree_packet_measure_equidistribution_unconditional` and `OAI.DukePrimeDegree.prime_degree_packet_measures_tendsto_haar_unconditional`, carved from OpenAI's openai/math development (OpenAI, *Equidistribution of Prime-Degree Torus Packets with Arbitrary Local Type*, OpenAI Math Release, September 24, 2026, result family 15, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 53 declarations of OpenAI's Lean: 16 definitions, 15 instances and 22 theorems. The definitions and types are `GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexClassFieldNormAmbient`, `GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexNormAmbient`, `GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexNormCyclotomicField`, `GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexNormExponent`, `GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexNormKummerField`, `GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexNormSeed`, `GlobalClassFieldTheory.GlobalClassFields.ordinaryNormClassFieldIdeleClassCommGroup`, `GlobalClassFieldTheory.GlobalClassFields.ordinaryNormOpenSubgroup`, `GlobalClassFieldTheory.Reciprocity.globalNormResidueContinuousMonoidHom`, `GlobalClassFieldTheory.Reciprocity.globalNormResidueContinuousMulEquiv`, `GlobalClassFieldTheory.Reciprocity.globalReciprocityContinuousMulEquiv`, `GlobalClassFieldTheory.Reciprocity.ideleClassNormQuotientContinuousMonoidHom`, `GlobalClassFieldTheory.Reciprocity.ramifiedInfinitePlaceOverextensionIdeleClassArtinMonoidHom`, `GlobalClassFieldTheory.Reciprocity.ramifiedInfinitePlaceOverextensionNormQuotientArtinData`, `GlobalClassFieldTheory.Reciprocity.ramifiedInfinitePlaceOverextensionNormQuotientArtinMonoidHom`, `GlobalClassFieldTheory.Reciprocity.topologicalNormResidueIdeleClassCommGroup`.
--
--   **Sources.** They come from these modules of lean/OAI/NumberTheory, in whole or in part: `GlobalClassFieldTheory_GlobalClassFields_ClosedFiniteIndexClassFieldConstruction`, `GlobalClassFieldTheory_GlobalClassFields_CyclotomicKummerNormDescent`, `GlobalClassFieldTheory_GlobalClassFields_FiniteIndexNormClassField`, `GlobalClassFieldTheory_GlobalClassFields_OrdinaryNormClassField`, `GlobalClassFieldTheory_GlobalClassFields_SUnitKummerNormRealization`, `GlobalClassFieldTheory_Reciprocity_ComplexificationArtin_OverextensionArtin`, `GlobalClassFieldTheory_Reciprocity_FiniteGaloisRealization`, `GlobalClassFieldTheory_Reciprocity_GlobalNormResidue`, `GlobalClassFieldTheory_Reciprocity_LocalGlobalArtinCompatibility_FinitePadicCyclicData`, `GlobalClassFieldTheory_Reciprocity_TopologicalGlobalNormResidue`.
--
--   **Imports.** It imports the bundle `OAIQ244Duke102` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ244Duke107`, `OAIQ244Duke108` and `OAIQ244Duke109`; the statements `GlobalClassFieldTheory.Reciprocity.ramifiedInfinitePlaceOverextensionIdeleClassArtinMonoidHom_eq_globalNormResidue_apply`, `GlobalClassFieldTheory.Reciprocity.ramifiedInfinitePlaceOverextensionNormQuotientArtinMonoidHom_bijective` and `GlobalClassFieldTheory.Reciprocity.ramifiedInfinitePlaceOverextensionNormQuotientArtinMonoidHom_eq_globalNormResidue_apply`; the proofs of `GlobalClassFieldTheory.Reciprocity.globalNormResidueMonoidHom_ramifiedInfinitePlaceOverextension_infinitePlaceIdeleClass`, `GlobalClassFieldTheory.Reciprocity.ramifiedInfinitePlaceOverextensionIdeleClassArtinMonoidHom_eq_globalNormResidue_apply`, `GlobalClassFieldTheory.Reciprocity.ramifiedInfinitePlaceOverextensionNormQuotientArtinMonoidHom_bijective` and `GlobalClassFieldTheory.Reciprocity.ramifiedInfinitePlaceOverextensionNormQuotientArtinMonoidHom_eq_globalNormResidue_apply`.
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
import Definitions.Def_OAIQ244Duke102

section
-- module Solutions.OAIQ244_DUKE.GlobalClassFieldTheory_Reciprocity_FiniteGaloisRealization
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 400000
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.GlobalClassFields.ConductorialSubgroup.finiteIndex _root_.GlobalClassFieldTheory.GlobalClassFields.bigHilbertClassFieldNormSubgroup_normal _root_.GlobalClassFieldTheory.GlobalClassFields.ideleClassNorm_rangeFiniteIndex _root_.GlobalClassFieldTheory.GlobalClassFields.smallHilbertClassFieldNormSubgroupFiniteIndex _root_.GlobalClassFieldTheory.Reciprocity.abstractFixedFieldCyclotomicCompositum_algebra _root_.GlobalClassFieldTheory.Reciprocity.abstractFixedFieldCyclotomicCompositum_baseScalarTower _root_.GlobalClassFieldTheory.Reciprocity.abstractFixedFieldCyclotomicCompositum_scalarTower _root_.GlobalClassFieldTheory.Reciprocity.abstractFixedFieldCyclotomicFiniteCompositum_baseAlgebra _root_.GlobalClassFieldTheory.Reciprocity.abstractFixedFieldCyclotomicFiniteCompositum_baseScalarTower _root_.GlobalClassFieldTheory.Reciprocity.abstractFixedFieldCyclotomicFiniteCompositum_finiteDimensional _root_.GlobalClassFieldTheory.Reciprocity.abstractFixedFieldCyclotomicFiniteCompositum_numberField _root_.GlobalClassFieldTheory.Reciprocity.abstractFixedFieldCyclotomicFiniteGaloisLayer_scalarTower _root_.GlobalClassFieldTheory.Reciprocity.abstractFixedFieldCyclotomicFiniteLayer_baseAlgebra _root_.GlobalClassFieldTheory.Reciprocity.abstractFixedFieldCyclotomicFiniteLayer_baseModule _root_.GlobalClassFieldTheory.Reciprocity.abstractFixedFieldCyclotomicFiniteLayer_baseSMul _root_.GlobalClassFieldTheory.Reciprocity.abstractFixedFieldCyclotomicFiniteLayer_baseScalarTower _root_.GlobalClassFieldTheory.Reciprocity.abstractFixedFieldCyclotomicFiniteLayer_finiteDimensional _root_.GlobalClassFieldTheory.Reciprocity.abstractFixedFieldCyclotomicFiniteLayer_isAbelianGalois _root_.GlobalClassFieldTheory.Reciprocity.abstractFixedFieldCyclotomicFiniteLayer_layerAlgebra _root_.GlobalClassFieldTheory.Reciprocity.abstractFixedFieldCyclotomicFiniteLayer_layerSMul _root_.GlobalClassFieldTheory.Reciprocity.abstractFixedFieldCyclotomicFiniteLayer_layerScalarTower _root_.GlobalClassFieldTheory.Reciprocity.abstractFixedFieldCyclotomicFiniteLayer_numberField _root_.KummerTheory.finite_finsupp_nsmulQuotient _root_.KummerTheory.finite_sUnit_nthPowerQuotient _root_.LocalClassFieldTheory.finiteUnramifiedNormQuotient _root_.LocalFieldTheory.DiscreteValuationField.finite_padicInt_finPi_nsmulQuotient _root_.LocalFieldTheory.DiscreteValuationField.finite_padicInt_pi_nsmulQuotient_of_coprime _root_.LocalFieldTheory.DiscreteValuationField.finite_valuationSubringUnits_nthPowerQuotient _root_.LocalFieldTheory.finite_multiplicative_nthPowerQuotient _root_.LocalFieldTheory.finite_nsmulAddQuotient_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.LubinTate.padicCompletedLevelField_algebra _root_.LubinTate.padicCompletedUnramifiedFieldAlgebra _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.boundedRealFields_finite _root_.OAI.PrimeDegreePackets.instTopologicalSpaceLocalAlgebra _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.CyclicCohomology.binaryCoefficientFamilyCommGroup _root_.GlobalClassFieldTheory.GlobalClassFields.bigHilbertNormQuotient_finite _root_.GlobalClassFieldTheory.GlobalClassFields.bigHilbertNormSubgroup_finiteIndex _root_.GlobalClassFieldTheory.GlobalClassFields.narrowClassGroup_finite _root_.LocalClassFieldTheory.normalizationIntegerRingIsIntegralClosure _root_.chosenFinitePlaceCompletionAlgebra _root_.relativeUnrestrictedSPlaceFactorCommGroup
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

attribute [local instance] realizedTowerIdeleClassCommGroup

attribute [local instance] realizedTowerIdeleClassIsMulCommutative

variable
    (K L : Type) [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]

/-- Under the compatible rational-separable-closure realization of a
finite Galois number-field extension, the abstract finite norm subgroup
is exactly the ordinary idele-class norm subgroup of the original
extension. -/
theorem
    map_numberFieldTowerFiniteNormSubgroup_eq_ordinaryIdeleClassNormRange :
    letI := (numberFieldTowerFiniteAbstractField K L).finite
    letI := numberFieldTowerExtensionSubgroup_normal K L
    letI := numberFieldTowerExtensionQuotient_finite K L
    (finiteNormSubgroup rationalIdeleClassRepresentation
        (numberFieldTowerBaseSubgroup K L)
        (numberFieldTowerTopSubgroup L)
        (numberFieldTowerTopSubgroup_le_baseSubgroup K L)).map
        (numberFieldTowerIdeleClassEquivAmbientFixed
          K L).symm.toAddMonoidHom =
      (_root_.ideleClassNorm K L).range.toAddSubgroup := by
  let E :=
    numberFieldTowerIdeleClassEquivAmbientFixed K L
  let Q :=
    numberFieldTowerFiniteNormQuotientEquivIdeleClassNormQuotient
      K L
  ext c
  constructor
  · rintro ⟨a, ha, rfl⟩
    have haZero :
        finiteNormClass rationalIdeleClassRepresentation
            (numberFieldTowerBaseSubgroup K L)
            (numberFieldTowerTopSubgroup L)
            (numberFieldTowerTopSubgroup_le_baseSubgroup K L) a =
          0 :=
      (finiteNormClass_eq_zero_iff
        rationalIdeleClassRepresentation
        (numberFieldTowerBaseSubgroup K L)
        (numberFieldTowerTopSubgroup L)
        (numberFieldTowerTopSubgroup_le_baseSubgroup K L) a).2 ha
    have hclass :=
      numberFieldTowerFiniteNormQuotientEquivIdeleClassNormQuotient_ideleClass
        K L (Additive.toMul (E.symm a))
    have hmk :
        QuotientGroup.mk'
            (_root_.ideleClassNorm K L).range
            (Additive.toMul (E.symm a)) =
          1 := by
      have hzero :
          (0 : Additive
            (IdeleClassGroup K ⧸
              (_root_.ideleClassNorm K L).range)) =
            Additive.ofMul
              (QuotientGroup.mk'
                (_root_.ideleClassNorm K L).range
                (Additive.toMul (E.symm a))) := by
        simpa only [E, ofMul_toMul,
          AddEquiv.apply_symm_apply, haZero, map_zero] using hclass
      exact congrArg Additive.toMul hzero.symm
    exact
      (QuotientGroup.eq_one_iff
        (Additive.toMul (E.symm a))).1 hmk
  · intro hc
    refine ⟨E c, ?_, E.symm_apply_apply c⟩
    apply
      (finiteNormClass_eq_zero_iff
        rationalIdeleClassRepresentation
        (numberFieldTowerBaseSubgroup K L)
        (numberFieldTowerTopSubgroup L)
        (numberFieldTowerTopSubgroup_le_baseSubgroup K L)
        (E c)).1
    apply Q.injective
    have hmk :
        QuotientGroup.mk'
            (_root_.ideleClassNorm K L).range
            (Additive.toMul c) =
          1 :=
      (QuotientGroup.eq_one_iff
        (Additive.toMul c)).2 hc
    have hclass :=
      numberFieldTowerFiniteNormQuotientEquivIdeleClassNormQuotient_ideleClass
        K L (Additive.toMul c)
    simpa only [E, ofMul_toMul,
      hmk, ofMul_one, map_zero] using hclass

/-- If an ordinary subgroup contains the norm subgroup of a finite Galois
number-field extension, then its transport to the compatible rational
absolute fixed part is open for the genuine norm topology. -/
theorem numberFieldTowerTransport_isNormOpen_of_normRange_le
    (H : Subgroup (IdeleClassGroup K))
    (hLH : (_root_.ideleClassNorm K L).range ≤ H) :
    letI := (numberFieldTowerFiniteAbstractField K L).finite
    IsNormOpen rationalIdeleClassRepresentation
      (numberFieldTowerBaseSubgroup K L)
      ((H.toAddSubgroup).map
        (numberFieldTowerIdeleClassEquivAmbientFixed
          K L).toAddMonoidHom :
        AddSubgroup
          (KummerTheory.ambientFixedAddSubgroup
            rationalIdeleClassRepresentation
            (numberFieldTowerBaseSubgroup K L))) := by
  let E :=
    numberFieldTowerIdeleClassEquivAmbientFixed K L
  rw [normTopology_addSubgroup_isOpen_iff]
  refine
    ⟨numberFieldTowerFiniteGaloisSubextension K L, ?_⟩
  intro a ha
  have hback :
      E.symm a ∈
        (finiteNormSubgroup rationalIdeleClassRepresentation
          (numberFieldTowerBaseSubgroup K L)
          (numberFieldTowerTopSubgroup L)
          (numberFieldTowerTopSubgroup_le_baseSubgroup K L)).map
            E.symm.toAddMonoidHom :=
    ⟨a, ha, rfl⟩
  have hnorm :
      Additive.toMul (E.symm a) ∈
        (_root_.ideleClassNorm K L).range := by
    rw [
      map_numberFieldTowerFiniteNormSubgroup_eq_ordinaryIdeleClassNormRange
        K L] at hback
    exact hback
  exact
    ⟨E.symm a, hLH hnorm, E.apply_symm_apply a⟩

end Reciprocity
end GlobalClassFieldTheory
end
end

section
-- module Solutions.OAIQ244_DUKE.GlobalClassFieldTheory_Reciprocity_GlobalNormResidue
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 400000
attribute [-instance] _root_.GlobalClassFieldTheory.GlobalClassFields.ConductorialSubgroup.finiteIndex _root_.GlobalClassFieldTheory.GlobalClassFields.bigHilbertClassFieldNormSubgroup_normal _root_.GlobalClassFieldTheory.GlobalClassFields.ideleClassNorm_rangeFiniteIndex _root_.GlobalClassFieldTheory.GlobalClassFields.smallHilbertClassFieldNormSubgroupFiniteIndex _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.GlobalClassFieldTheory.GlobalClassFields.bigHilbertNormQuotient_finite _root_.GlobalClassFieldTheory.GlobalClassFields.bigHilbertNormSubgroup_finiteIndex
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI
attribute [local instance] OAI.starSubalgebraCommCStarAlgebra

set_option autoImplicit false

/-!
# The global norm-residue symbol

For a finite abelian Galois extension `L / K`, the rational absolute
idele-class formation realizes the abstract finite norm quotient as the
actual quotient

`C_K / N_{L/K} C_L`.

The concrete cyclotomic valuation supplies the valuation data required
by abstract reciprocity.  Composing the inverse of the fixed-field
comparison, the abstract norm-residue symbol, and the compatible
Galois-group comparison gives the actual equivalence

`C_K / N_{L/K} C_L ≃ Gal(L / K)`.

The homomorphism on `C_K` is obtained from the genuine quotient map.
Consequently it is surjective and its kernel is exactly the range of
the actual ordinary idele-class norm.
-/

open scoped IsMulCommutative NumberField
open NumberField

noncomputable section

namespace GlobalClassFieldTheory
namespace Reciprocity

open ClassFormation
open KummerTheory

attribute [local instance] globalNormResidueIdeleClassCommGroup

attribute [local instance] globalNormResidueIdeleClassIsMulCommutative

variable
    (K L : Type) [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsAbelianGalois K L]

/-- The index of the actual idele-class norm subgroup of a finite
abelian extension is its field degree. -/
theorem ideleClassNorm_index_eq_finrank_abelian :
    (_root_.ideleClassNorm K L).range.index =
      Module.finrank K L := by
  rw [Subgroup.index_eq_card]
  calc
    Nat.card
        (IdeleClassGroup K ⧸
          (_root_.ideleClassNorm K L).range) =
        Nat.card
          (Additive
            (IdeleClassGroup K ⧸
              (_root_.ideleClassNorm K L).range)) :=
      (Nat.card_congr Additive.toMul).symm
    _ = Nat.card (Additive (Gal(L / K))) :=
      Nat.card_congr (globalNormResidueEquiv K L).toEquiv
    _ = Nat.card (Gal(L / K)) :=
      Nat.card_congr Additive.toMul
    _ = Module.finrank K L :=
      IsGalois.card_aut_eq_finrank K L

end Reciprocity
end GlobalClassFieldTheory
end
end

section
-- module Solutions.OAIQ244_DUKE.GlobalClassFieldTheory_GlobalClassFields_SUnitKummerNormRealization
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 400000
attribute [-instance] _root_.GlobalClassFieldTheory.GlobalClassFields.ConductorialSubgroup.finiteIndex _root_.GlobalClassFieldTheory.GlobalClassFields.bigHilbertClassFieldNormSubgroup_normal _root_.GlobalClassFieldTheory.GlobalClassFields.ideleClassNorm_rangeFiniteIndex _root_.GlobalClassFieldTheory.GlobalClassFields.smallHilbertClassFieldNormSubgroupFiniteIndex _root_.GlobalClassFieldTheory.Reciprocity.abstractFixedFieldCyclotomicFiniteLayer_baseModule _root_.GlobalClassFieldTheory.Reciprocity.infinitePlaceComplexificationOverfield_algebra _root_.GlobalClassFieldTheory.Reciprocity.infinitePlaceComplexificationOverfield_baseAlgebra _root_.GlobalClassFieldTheory.Reciprocity.ramifiedInfinitePlaceRealFixedField_algebra _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.diagonalLogAction _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.GlobalClassFieldTheory.GlobalClassFields.bigHilbertNormQuotient_finite _root_.GlobalClassFieldTheory.GlobalClassFields.bigHilbertNormSubgroup_finiteIndex
attribute [-simp] _root_.GlobalClassFieldTheory.ClassFieldAxiom.hasseNormDiagonal_mk _root_.GlobalClassFieldTheory.GlobalClassFields.ConductorialSubgroup.ideleClassQuotientEquivOfNarrowFiniteConductorsEqOfRayClassGroupCardsEqQuotientCards_mk _root_.GlobalClassFieldTheory.GlobalClassFields.ConductorialSubgroup.mem_fullConductorInfinitePart_iff _root_.GlobalClassFieldTheory.GlobalClassFields.ConductorialSubgroup.narrowFiniteConductorRayClassGroupEquivQuotientOfCardEq_mk _root_.GlobalClassFieldTheory.GlobalClassFields.ConductorialSubgroup.narrowFiniteConductorRayClassGroupToQuotient_mk _root_.GlobalClassFieldTheory.GlobalClassFields.bigHilbertClassFieldQuotientCongr_mk _root_.GlobalClassFieldTheory.GlobalClassFields.bigHilbertClassFieldQuotientEquivNarrowClassGroup_mk _root_.GlobalClassFieldTheory.GlobalClassFields.bigHilbertClassFieldQuotientToIdeleClassNormQuotient_mk _root_.GlobalClassFieldTheory.GlobalClassFields.bigHilbertClassFieldQuotientToSmallHilbertClassFieldQuotient_mk _root_.GlobalClassFieldTheory.GlobalClassFields.ideleClassNormQuotientTowerMap_mk _root_.GlobalClassFieldTheory.GlobalClassFields.narrowFiniteConductorRayClassGroupToIdeleClassNormQuotient_mk _root_.GlobalClassFieldTheory.GlobalClassFields.normQuotientEquivOfNarrowFiniteConductorsEqOfRayClassGroupCardsEqNormQuotientCards_mk _root_.GlobalClassFieldTheory.GlobalClassFields.realSignToBigHilbertClassFieldQuotient_apply _root_.GlobalClassFieldTheory.GlobalClassFields.realSignToNarrowClassKernel_apply _root_.GlobalClassFieldTheory.GlobalClassFields.smallHilbertClassFieldQuotientCongr_mk _root_.GlobalClassFieldTheory.GlobalClassFields.smallHilbertClassFieldQuotientEquivClassGroup_mk _root_.GlobalClassFieldTheory.GlobalClassFields.smallHilbertClassFieldQuotientToIdeleClassNormQuotient_mk _root_.GlobalClassFieldTheory.IdealClassFieldTheory.smallHilbertClassFieldIdeleExtensionMap_mk' _root_.GlobalClassFieldTheory.Reciprocity.abstractFixedFieldCyclotomicIdeleClassArtinMonoidHom_mk _root_.GlobalClassFieldTheory.Reciprocity.abstractFixedFieldCyclotomicRestriction_infiniteGlobalArtinMonoidHom _root_.GlobalClassFieldTheory.Reciprocity.globalNormClassFromIdele_principalIdele _root_.GlobalClassFieldTheory.Reciprocity.globalNormClassFromIdele_relativeIdeleNorm_eq_one _root_.GlobalClassFieldTheory.Reciprocity.infiniteGlobalArtinMonoidHom_abstractFixedFieldCyclotomic_principalIdele _root_.GlobalClassFieldTheory.Reciprocity.mem_globalArtinFiniteSupport_iff _root_.GlobalClassFieldTheory.Reciprocity.rationalComplexificationGlobalArtin_principalIdele _root_.IdeleGroup.count_fractionalIdeal _root_.IdeleGroup.fractionalIdeal_finitePrimeIdele _root_.IdeleGroup.idealClass_finitePrimeIdele _root_.OAI.PrimeDegreePackets.ThetaConstruction.schwartzCM_apply _root_.RayClass.signToNarrow_mk
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

/-!
# Exact norm realization by the full S-unit Kummer extension

When the base field contains the required roots of unity, the full
S-unit Kummer extension realizes the canonical power-local-unit
subgroup exactly as its ordinary idele-class norm subgroup.  The forward
inclusion is the local norm theorem, using the actual unramifiedness of
the Kummer extension away from the canonical support.  Equality follows
from the independently computed quotient cardinal and the global
norm-residue index formula.
-/

open scoped NumberField Classical

noncomputable section

namespace GlobalClassFieldTheory
namespace GlobalClassFields

open NumberField IsDedekindDomain
open GlobalClassFieldTheory.ClassFieldAxiom
open KummerTheory

variable {K : Type} [Field K] [NumberField K]

/-- The full S-unit Kummer extension has ordinary idele-class norm range
equal to the canonical power-local-unit subgroup. -/
theorem fullSUnitKummerExtension_ideleClassNormRange_eq_powerLocalUnit
    {Omega : Type} [Field Omega] [Algebra K Omega]
    [IsSepClosure K Omega]
    (n : ℕ+)
    (hn : 1 < (n : ℕ))
    (hmu : (primitiveRoots (n : ℕ) K).Nonempty)
    (seed : Finset (HeightOneSpectrum (𝓞 K))) :
    let S := sUnitKummerNormSupport (K := K) n seed
    let E :=
      KummerTheory.fullSUnitKummerExtension
        (K := K) (Omega := Omega) n S
    letI : FiniteDimensional K E :=
      KummerTheory.fullSUnitKummerExtension_finiteDimensional
        (K := K) (Omega := Omega) n
        (by exact_mod_cast n.ne_zero) hmu S
    letI : IsGalois K E :=
      KummerTheory.fullSUnitKummerExtension_isGalois
        (K := K) (Omega := Omega) n S
    letI : NumberField E :=
      NumberField.of_module_finite K E
    (_root_.ideleClassNorm K E).range =
      ideleClassPowerLocalUnitSubgroup (K := K) n S ∅ := by
  classical
  dsimp only
  let S := sUnitKummerNormSupport (K := K) n seed
  let E :=
    KummerTheory.fullSUnitKummerExtension
      (K := K) (Omega := Omega) n S
  let hnK : ((n : ℕ) : K) ≠ 0 := by
    exact_mod_cast n.ne_zero
  let : FiniteDimensional K E :=
    KummerTheory.fullSUnitKummerExtension_finiteDimensional
      (K := K) (Omega := Omega) n hnK hmu S
  let : IsGalois K E :=
    KummerTheory.fullSUnitKummerExtension_isGalois
      (K := K) (Omega := Omega) n S
  let : NumberField E :=
    NumberField.of_module_finite K E
  let r := totalPlaceCard (K := K) S
  let eG :
      Gal(E/K) ≃*
        (Fin r → Multiplicative (ZMod (n : ℕ))) := by
    simpa only [E, r] using
      (KummerTheory.fullSUnitKummerExtensionGaloisEquivPiZMod
        (K := K) (Omega := Omega) n hnK hmu S)
  let : IsAbelianGalois K E :=
    { is_comm.comm := fun σ τ => by
        apply eG.injective
        simpa only [map_mul] using
          mul_comm (eG σ) (eG τ) }
  have harch :
      Even (n : ℕ) ∨
        ∀ w : InfinitePlace K, ¬ w.IsReal :=
    even_or_no_realInfinitePlace_of_primitiveRoots
      (K := K) n hmu hn
  have hAway :
      ∀ v, v ∉ S ∪ (∅ :
          Finset (HeightOneSpectrum (𝓞 K))) →
        _root_.ChosenFinitePlaceIsUnramified
          (K := K) (L := E) v := by
    intro v hv
    have hvS : v ∉ S := by
      simpa only [Finset.union_empty] using hv
    have hnv :
        v.valuation K ((n : ℕ) : K) = 1 := by
      simpa only [S] using
        valuation_natCast_eq_one_of_not_mem_sUnitKummerNormSupport
          (K := K) n seed hvS
    simpa only [E] using
      (KummerTheory.fullSUnitKummerExtension_chosenFinitePlaceIsUnramified_of_not_mem
        (K := K) (Omega := Omega)
        n hnK hmu S v hvS hnv)
  have hPowerLeRelative :
      ideleClassPowerLocalUnitSubgroup
          (K := K) n S ∅ ≤
        (RelativeIdeleGroup.Cohomology.ideleClassNorm K E).range := by
    apply
      ideleClassPowerLocalUnitSubgroup_le_ideleClassNorm_range
        (K := K) (L := E) n r eG S ∅ harch
    · intro v hv
      simp at hv
    · exact hAway
  have hPowerLe :
      ideleClassPowerLocalUnitSubgroup
          (K := K) n S ∅ ≤
        (_root_.ideleClassNorm K E).range := by
    rw [
      ordinaryIdeleClassNorm_range_eq_relative
        (K := K) (L := E)]
    exact hPowerLeRelative
  have hPowerIndex :
      (ideleClassPowerLocalUnitSubgroup
          (K := K) n S ∅).index =
        Module.finrank K E := by
    rw [Subgroup.index_eq_card]
    simpa only [S, E] using
      (card_ideleClassPowerLocalUnitQuotient_eq_finrank_fullSUnitKummerExtension
        (K := K) (Omega := Omega) n hmu seed)
  have hNormIndex :
      (_root_.ideleClassNorm K E).range.index =
        Module.finrank K E :=
    Reciprocity.ideleClassNorm_index_eq_finrank_abelian K E
  apply
    (LubinTate.subgroup_eq_of_le_of_index_eq_of_ne_zero
      hPowerLe (hPowerIndex.trans hNormIndex.symm)
      (by
        rw [hPowerIndex]
        exact Nat.ne_of_gt Module.finrank_pos)).symm

end GlobalClassFields
end GlobalClassFieldTheory
end
end

section
-- module Solutions.OAIQ244_DUKE.GlobalClassFieldTheory_GlobalClassFields_CyclotomicKummerNormDescent
attribute [-instance] _root_.GlobalClassFieldTheory.GlobalClassFields.ConductorialSubgroup.finiteIndex _root_.GlobalClassFieldTheory.GlobalClassFields.bigHilbertClassFieldNormSubgroup_normal _root_.GlobalClassFieldTheory.GlobalClassFields.ideleClassNorm_rangeFiniteIndex _root_.GlobalClassFieldTheory.GlobalClassFields.smallHilbertClassFieldNormSubgroupFiniteIndex _root_.GlobalClassFieldTheory.Reciprocity.abstractFixedFieldCyclotomicFiniteCompositum_numberField _root_.GlobalClassFieldTheory.Reciprocity.abstractFixedFieldCyclotomicFiniteLayer_baseSMul _root_.GlobalClassFieldTheory.Reciprocity.abstractFixedFieldCyclotomicFiniteLayer_layerSMul _root_.GlobalClassFieldTheory.Reciprocity.abstractFixedFieldCyclotomicFiniteLayer_numberField _root_.GlobalClassFieldTheory.Reciprocity.complexFourthRootField_numberField _root_.GlobalClassFieldTheory.Reciprocity.infinitePlaceComplexificationOverfield_algebra _root_.GlobalClassFieldTheory.Reciprocity.infinitePlaceComplexificationOverfield_baseAlgebra _root_.GlobalClassFieldTheory.Reciprocity.infinitePlaceComplexificationOverfield_baseSmul _root_.GlobalClassFieldTheory.Reciprocity.infinitePlaceComplexificationOverfield_finiteDimensional_over_extension _root_.GlobalClassFieldTheory.Reciprocity.infinitePlaceComplexificationOverfield_numberField _root_.GlobalClassFieldTheory.Reciprocity.infinitePlaceComplexificationOverfield_smul _root_.GlobalClassFieldTheory.Reciprocity.ramifiedInfinitePlaceRealFixedField_algebra _root_.GlobalClassFieldTheory.Reciprocity.ramifiedInfinitePlaceRealFixedField_numberField _root_.GlobalClassFieldTheory.Reciprocity.rationalComplexification_infinitePlaceOverfield_smul _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.boundedRealFields_numberField _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.GlobalClassFieldTheory.GlobalClassFields.bigHilbertNormQuotient_finite _root_.GlobalClassFieldTheory.GlobalClassFields.bigHilbertNormSubgroup_finiteIndex
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

/-!
# Cyclotomic descent for full S-unit Kummer norms

This file implements the roots-of-unity descent in the existence proof of
global class field theory.  Starting from a finite seed of finite places of
`K`, it enlarges the seed just enough that its full inverse image in
`CyclotomicField n K` is a chosen Kummer norm support.  Thus the full
S-unit Kummer extension over the cyclotomic field has its concrete norm
subgroup described by Kummer theory, while the support is still exactly a
full inverse image and hence descends through the cyclotomic norm.

The final normal-closure step turns the resulting finite extension of `K`
into a genuine finite Galois extension without enlarging its norm subgroup.
-/

open scoped Classical NumberField
open NumberField IsDedekindDomain
open KummerTheory

noncomputable section

namespace GlobalClassFieldTheory
namespace GlobalClassFields

open GlobalClassFieldTheory.ClassFieldAxiom

variable {K : Type} [Field K] [NumberField K]

attribute [local instance] GlobalClassFieldTheory.GlobalClassFields.cyclotomicKummerNormDescent_neZero
attribute [local instance] GlobalClassFieldTheory.GlobalClassFields.cyclotomicKummerNormDescent_cyclotomicFiniteDimensional
noncomputable local instance
    cyclotomicKummerNormDescent_cyclotomicIsGalois_r5232e0_1
    (n : ℕ+) :
    IsGalois K (CyclotomicField (n : ℕ) K) :=
  IsCyclotomicExtension.isGalois
    {(n : ℕ)} K (CyclotomicField (n : ℕ) K)
attribute [local instance] GlobalClassFieldTheory.GlobalClassFields.cyclotomicKummerNormDescent_kummerFiniteDimensional
/-- The expensive Kummer norm computation over the cyclotomic base, isolated
before the `K`-to-Kummer-field instance tower is introduced. -/
theorem
    cyclotomicFullSUnitKummerExtension_cyclotomicNormRange
    (n : ℕ+)
    (hn : 1 < (n : ℕ))
    (seed : Finset (HeightOneSpectrum (𝓞 K))) :
    let C := CyclotomicField (n : ℕ) K
    let S' := cyclotomicKummerNormSupportAbove (K := K) n seed
    let E := cyclotomicFullSUnitKummerExtension (K := K) n seed
    letI : NumberField E :=
      cyclotomicKummerNormDescent_kummerNumberField (K := K) n seed
    (_root_.ideleClassNorm C E).range =
      ideleClassPowerLocalUnitSubgroup (K := C) n S' ∅ := by
  classical
  dsimp only
  let C := CyclotomicField (n : ℕ) K
  let S' := cyclotomicKummerNormSupportAbove (K := K) n seed
  let E := cyclotomicFullSUnitKummerExtension (K := K) n seed
  let : NumberField E :=
    cyclotomicKummerNormDescent_kummerNumberField (K := K) n seed
  have hmu : (primitiveRoots (n : ℕ) C).Nonempty :=
    cyclotomicKummerNormDescent_primitiveRoots_nonempty
      (K := K) n
  have hstable :
      sUnitKummerNormSupport (K := C) n S' = S' := by
    simpa only [C, S'] using
      sUnitKummerNormSupport_cyclotomicKummerNormSupportAbove
        (K := K) n seed
  have hNormCanonical :
      (_root_.ideleClassNorm C E).range =
        ideleClassPowerLocalUnitSubgroup (K := C) n
          (sUnitKummerNormSupport (K := C) n S') ∅ := by
    simpa only [C, S', E, cyclotomicFullSUnitKummerExtension] using
      (fullSUnitKummerExtension_ideleClassNormRange_eq_powerLocalUnit
        (K := C) (Omega := SeparableClosure C)
        n hn hmu S')
  exact hNormCanonical.trans
    (congrArg
      (fun T => ideleClassPowerLocalUnitSubgroup (K := C) n T ∅)
      hstable)

attribute [local instance] GlobalClassFieldTheory.GlobalClassFields.cyclotomicKummerNormDescent_kummerAlgebraOverBase
noncomputable local instance
    cyclotomicKummerNormDescent_kummerFiniteDimensionalOverBase_r5232e0_1
    (n : ℕ+)
    (seed : Finset (HeightOneSpectrum (𝓞 K))) :
    FiniteDimensional K
      (cyclotomicFullSUnitKummerExtension (K := K) n seed) :=
  by
    let : IsScalarTower K
        (CyclotomicField (n : ℕ) K)
        (cyclotomicFullSUnitKummerExtension (K := K) n seed) :=
      cyclotomicKummerNormDescent_kummerScalarTower (K := K) n seed
    exact FiniteDimensional.trans K
      (CyclotomicField (n : ℕ) K)
      (cyclotomicFullSUnitKummerExtension (K := K) n seed)
/-- The norm range of the actual cyclotomic full S-unit Kummer extension,
viewed as a finite extension of `K`, lies in the power-local-unit subgroup
on the enlarged base support.  This is the pointwise tower-norm step in the
roots-of-unity descent. -/
theorem
    cyclotomicFullSUnitKummerExtension_ideleClassNormRange_le_powerLocalUnit
    (n : ℕ+)
    (hn : 1 < (n : ℕ))
    (seed : Finset (HeightOneSpectrum (𝓞 K))) :
    let E := cyclotomicFullSUnitKummerExtension (K := K) n seed
    letI : NumberField E :=
      cyclotomicKummerNormDescent_kummerNumberField (K := K) n seed
    (_root_.ideleClassNorm K E).range ≤
      ideleClassPowerLocalUnitSubgroup
        (K := K) n
        (cyclotomicKummerNormSupport (K := K) n seed) ∅ := by
  classical
  dsimp only
  let C := CyclotomicField (n : ℕ) K
  let S := cyclotomicKummerNormSupport (K := K) n seed
  let S' := cyclotomicKummerNormSupportAbove (K := K) n seed
  let E := cyclotomicFullSUnitKummerExtension (K := K) n seed
  let : IsScalarTower K C E :=
    cyclotomicKummerNormDescent_kummerScalarTower (K := K) n seed
  let : NumberField E :=
    cyclotomicKummerNormDescent_kummerNumberField (K := K) n seed
  have hNormC :
      (_root_.ideleClassNorm C E).range =
        ideleClassPowerLocalUnitSubgroup (K := C) n S' ∅ :=
    cyclotomicFullSUnitKummerExtension_cyclotomicNormRange
      (K := K) n hn seed
  have hSupport :
      ∀ W : HeightOneSpectrum (𝓞 C),
        W ∈ S' ↔ finitePlaceBelow (K := K) W ∈ S := by
    intro W
    simpa only [C, S, S'] using
      (mem_cyclotomicKummerNormSupportAbove_iff
        (K := K) n seed W)
  rintro _ ⟨c, rfl⟩
  rw [← ordinaryIdeleClassNorm_tower
    (K := K) (M := C) (L := E) c]
  apply
    (ideleClassNorm_map_powerLocalUnitSubgroup_le_of_supports_above
      (K := K) (L := C) n S S' hSupport)
  refine ⟨_root_.ideleClassNorm C E c, ?_, rfl⟩
  rw [← hNormC]
  exact ⟨c, rfl⟩

/-- Passing to the finite normal closure produces an actual finite Galois
extension of `K` whose norm range is still contained in the prescribed
power-local-unit subgroup.  This is the finite Galois norm neighbourhood
constructed in the roots-of-unity-free case. -/
theorem
    cyclotomicFullSUnitKummerFiniteNormalClosure_ideleClassNormRange_le_powerLocalUnit
    (n : ℕ+)
    (hn : 1 < (n : ℕ))
    (seed : Finset (HeightOneSpectrum (𝓞 K))) :
    let E := cyclotomicFullSUnitKummerExtension (K := K) n seed
    letI : NumberField E :=
      cyclotomicKummerNormDescent_kummerNumberField (K := K) n seed
    let F := finiteNormalClosure K E
    (_root_.ideleClassNorm K F).range ≤
      ideleClassPowerLocalUnitSubgroup
        (K := K) n
        (cyclotomicKummerNormSupport (K := K) n seed) ∅ := by
  classical
  dsimp only
  let E := cyclotomicFullSUnitKummerExtension (K := K) n seed
  let : NumberField E :=
    cyclotomicKummerNormDescent_kummerNumberField (K := K) n seed
  let F := finiteNormalClosure K E
  calc
    (_root_.ideleClassNorm K F).range ≤
        (_root_.ideleClassNorm K E).range := by
      simpa only [F] using
        (finiteNormalClosure_ideleClassNorm_range_le_source
          (K := K) (L := E))
    _ ≤ ideleClassPowerLocalUnitSubgroup
          (K := K) n
          (cyclotomicKummerNormSupport (K := K) n seed) ∅ := by
      simpa only [E] using
        (cyclotomicFullSUnitKummerExtension_ideleClassNormRange_le_powerLocalUnit
          (K := K) n hn seed)

end GlobalClassFields
end GlobalClassFieldTheory
end
end

section
-- module Solutions.OAIQ244_DUKE.GlobalClassFieldTheory_GlobalClassFields_FiniteIndexNormClassField
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 400000
attribute [-instance] _root_.GlobalClassFieldTheory.GlobalClassFields.ConductorialSubgroup.finiteIndex _root_.GlobalClassFieldTheory.GlobalClassFields.bigHilbertClassFieldNormSubgroup_normal _root_.GlobalClassFieldTheory.GlobalClassFields.ideleClassNorm_rangeFiniteIndex _root_.GlobalClassFieldTheory.GlobalClassFields.smallHilbertClassFieldNormSubgroupFiniteIndex _root_.GlobalClassFieldTheory.Reciprocity.abstractFixedFieldCyclotomicFiniteCompositum_numberField _root_.GlobalClassFieldTheory.Reciprocity.abstractFixedFieldCyclotomicFiniteLayer_baseModule _root_.GlobalClassFieldTheory.Reciprocity.abstractFixedFieldCyclotomicFiniteLayer_numberField _root_.GlobalClassFieldTheory.Reciprocity.complexFourthRootField_numberField _root_.GlobalClassFieldTheory.Reciprocity.infinitePlaceComplexificationOverfield_algebra _root_.GlobalClassFieldTheory.Reciprocity.infinitePlaceComplexificationOverfield_baseAlgebra _root_.GlobalClassFieldTheory.Reciprocity.infinitePlaceComplexificationOverfield_numberField _root_.GlobalClassFieldTheory.Reciprocity.ramifiedInfinitePlaceRealFixedField_algebra _root_.GlobalClassFieldTheory.Reciprocity.ramifiedInfinitePlaceRealFixedField_numberField _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.boundedRealFields_finite _root_.OAI.PrimeDegreePackets.boundedRealFields_numberField _root_.OAI.PrimeDegreePackets.diagonalLogAction _root_.OAI.PrimeDegreePackets.instTopologicalSpaceLocalAlgebra _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.GlobalClassFieldTheory.GlobalClassFields.bigHilbertNormQuotient_finite _root_.GlobalClassFieldTheory.GlobalClassFields.bigHilbertNormSubgroup_finiteIndex _root_.GlobalClassFieldTheory.GlobalClassFields.narrowClassGroup_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

/-!
# Class fields of closed finite-index idele-class subgroups

For a closed finite-index subgroup `H` of the idele class group, the
canonical ray modulus inside `H` supplies the finite seed for the full
S-unit Kummer construction.  When `H` is proper, the Kummer exponent is
the index of `H`; when `H` is the whole group, exponent two gives a
uniform finite Galois norm neighbourhood and the required containment is
automatic.

The finite normal closure of the cyclotomic full S-unit Kummer extension
therefore has ordinary idele-class norm range contained in `H`.
Finite-abelian classification applied to that actual norm neighbourhood
then realizes `H`, transported to the canonical embedded copy of the base
field, as an exact determinant-norm subgroup.
-/

open scoped Classical NumberField

noncomputable section

namespace GlobalClassFieldTheory
namespace GlobalClassFields

open NumberField IsDedekindDomain
open GlobalClassFieldTheory.ClassFieldAxiom

variable {K : Type} [Field K] [NumberField K]

/-- The Kummer exponent attached to a closed finite-index idele-class
subgroup.  A proper subgroup uses its exact index.  The top subgroup uses
exponent two, so the same concrete finite Galois construction also covers
the trivial class field case. -/
noncomputable def closedFiniteIndexNormExponent
    (H : Subgroup (IdeleClassGroup K))
    [H.FiniteIndex] :
    ℕ+ :=
  if H = ⊤ then 2
  else
    ⟨H.index,
      Nat.pos_of_ne_zero Subgroup.FiniteIndex.index_ne_zero⟩

/-- For a proper finite-index subgroup, its norm exponent is its index. -/
theorem closedFiniteIndexNormExponent_eq_index
    (H : Subgroup (IdeleClassGroup K))
    [H.FiniteIndex]
    (hH : H ≠ ⊤) :
    closedFiniteIndexNormExponent (K := K) H =
      ⟨H.index,
        Nat.pos_of_ne_zero Subgroup.FiniteIndex.index_ne_zero⟩ := by
  change
    (if H = ⊤ then (2 : ℕ+) else
      H.index.toPNat (Nat.pos_of_ne_zero Subgroup.FiniteIndex.index_ne_zero)) =
      H.index.toPNat (Nat.pos_of_ne_zero Subgroup.FiniteIndex.index_ne_zero)
  exact ite_eq_right hH

/-- The Kummer exponent attached to a finite-index subgroup is always
strictly larger than one. -/
theorem one_lt_closedFiniteIndexNormExponent
    (H : Subgroup (IdeleClassGroup K))
    [H.FiniteIndex] :
    1 < (closedFiniteIndexNormExponent (K := K) H : ℕ) := by
  by_cases hH : H = ⊤
  · have hexponent : closedFiniteIndexNormExponent (K := K) H = (2 : ℕ+) := by
      change
        (if H = ⊤ then (2 : ℕ+) else
          H.index.toPNat (Nat.pos_of_ne_zero Subgroup.FiniteIndex.index_ne_zero)) =
          (2 : ℕ+)
      exact ite_eq_left hH
    have hvalue : (closedFiniteIndexNormExponent (K := K) H : ℕ) = 2 :=
      congrArg PNat.val hexponent
    rw [hvalue]
    decide
  · have hindex : (closedFiniteIndexNormExponent (K := K) H : ℕ) = H.index :=
      congrArg PNat.val (closedFiniteIndexNormExponent_eq_index (K := K) H hH)
    rw [hindex]
    exact Subgroup.one_lt_index_of_ne_top hH

/-- The finite seed used in the norm-neighbourhood construction is the
support of the canonical ray modulus whose congruence subgroup lies in
`H`. -/
noncomputable def closedFiniteIndexNormSeed
    (H : Subgroup (IdeleClassGroup K))
    (hclosed : IsClosed (H : Set (IdeleClassGroup K)))
    [H.FiniteIndex] :
    Finset (HeightOneSpectrum (𝓞 K)) :=
  (RayClass.modulusInsideClosedFiniteIndex H hclosed).finitePart.support

/-- The cyclotomic layer used by the finite-index norm construction. -/
noncomputable abbrev closedFiniteIndexNormCyclotomicField
    (H : Subgroup (IdeleClassGroup K))
    [H.FiniteIndex] : Type :=
  CyclotomicField
    (closedFiniteIndexNormExponent (K := K) H : ℕ) K

instance closedFiniteIndexNormExponentNeZero
    (H : Subgroup (IdeleClassGroup K))
    [H.FiniteIndex] :
    NeZero (closedFiniteIndexNormExponent (K := K) H : ℕ) :=
  ⟨(closedFiniteIndexNormExponent (K := K) H).ne_zero⟩

noncomputable instance
    closedFiniteIndexNormCyclotomicFieldIsCyclotomicExtension
    (H : Subgroup (IdeleClassGroup K)) [H.FiniteIndex] :
    IsCyclotomicExtension
      {(closedFiniteIndexNormExponent (K := K) H : ℕ)} K
      (closedFiniteIndexNormCyclotomicField (K := K) H) := by
  unfold closedFiniteIndexNormCyclotomicField
  exact
    CyclotomicField.isCyclotomicExtension
      (closedFiniteIndexNormExponent (K := K) H : ℕ) K

noncomputable instance
    closedFiniteIndexNormCyclotomicFieldFiniteDimensional
    (H : Subgroup (IdeleClassGroup K)) [H.FiniteIndex] :
    FiniteDimensional K
      (closedFiniteIndexNormCyclotomicField (K := K) H) :=
  IsCyclotomicExtension.finiteDimensional
    {(closedFiniteIndexNormExponent (K := K) H : ℕ)} K
    (closedFiniteIndexNormCyclotomicField (K := K) H)

noncomputable instance closedFiniteIndexNormCyclotomicFieldNumberField
    (H : Subgroup (IdeleClassGroup K)) [H.FiniteIndex] :
    NumberField
      (closedFiniteIndexNormCyclotomicField (K := K) H) :=
  NumberField.of_module_finite K
    (closedFiniteIndexNormCyclotomicField (K := K) H)

noncomputable instance closedFiniteIndexNormCyclotomicFieldIsGalois
    (H : Subgroup (IdeleClassGroup K)) [H.FiniteIndex] :
    IsGalois K
      (closedFiniteIndexNormCyclotomicField (K := K) H) :=
  IsCyclotomicExtension.isGalois
    {(closedFiniteIndexNormExponent (K := K) H : ℕ)} K
    (closedFiniteIndexNormCyclotomicField (K := K) H)

/-- The full S-unit Kummer layer used by the finite-index norm
construction. -/
noncomputable abbrev closedFiniteIndexNormKummerField
    (H : Subgroup (IdeleClassGroup K))
    (hclosed : IsClosed (H : Set (IdeleClassGroup K)))
    [H.FiniteIndex] : Type :=
  cyclotomicFullSUnitKummerExtension
    (K := K) (closedFiniteIndexNormExponent (K := K) H)
    (closedFiniteIndexNormSeed (K := K) H hclosed)

noncomputable instance closedFiniteIndexNormKummerFieldFiniteDimensional
    (H : Subgroup (IdeleClassGroup K))
    (hclosed : IsClosed (H : Set (IdeleClassGroup K)))
    [H.FiniteIndex] :
    FiniteDimensional
      (closedFiniteIndexNormCyclotomicField (K := K) H)
      (closedFiniteIndexNormKummerField (K := K) H hclosed) := by
  unfold closedFiniteIndexNormCyclotomicField
    closedFiniteIndexNormKummerField
  exact
    cyclotomicFullSUnitKummerExtension_finiteDimensional
      (K := K) (closedFiniteIndexNormExponent (K := K) H)
      (closedFiniteIndexNormSeed (K := K) H hclosed)

noncomputable instance closedFiniteIndexNormKummerFieldNumberField
    (H : Subgroup (IdeleClassGroup K))
    (hclosed : IsClosed (H : Set (IdeleClassGroup K)))
    [H.FiniteIndex] :
    NumberField (closedFiniteIndexNormKummerField (K := K) H hclosed) :=
  NumberField.of_module_finite
    (closedFiniteIndexNormCyclotomicField (K := K) H)
    (closedFiniteIndexNormKummerField (K := K) H hclosed)

@[reducible]
noncomputable instance closedFiniteIndexNormKummerFieldAlgebraOverBase
    (H : Subgroup (IdeleClassGroup K))
    (hclosed : IsClosed (H : Set (IdeleClassGroup K)))
    [H.FiniteIndex] :
    Algebra K (closedFiniteIndexNormKummerField (K := K) H hclosed) :=
  ((algebraMap
      (closedFiniteIndexNormCyclotomicField (K := K) H)
      (closedFiniteIndexNormKummerField (K := K) H hclosed)).comp
    (algebraMap K
      (closedFiniteIndexNormCyclotomicField (K := K) H))).toAlgebra

@[reducible]
noncomputable instance closedFiniteIndexNormKummerFieldSMulOverBase
    (H : Subgroup (IdeleClassGroup K))
    (hclosed : IsClosed (H : Set (IdeleClassGroup K)))
    [H.FiniteIndex] :
    SMul K (closedFiniteIndexNormKummerField (K := K) H hclosed) :=
  Algebra.toSMul
    (self := closedFiniteIndexNormKummerFieldAlgebraOverBase H hclosed)

@[reducible]
noncomputable instance closedFiniteIndexNormKummerFieldModuleOverBase
    (H : Subgroup (IdeleClassGroup K))
    (hclosed : IsClosed (H : Set (IdeleClassGroup K)))
    [H.FiniteIndex] :
    Module K (closedFiniteIndexNormKummerField (K := K) H hclosed) :=
  Algebra.toModule

noncomputable instance closedFiniteIndexNormKummerFieldScalarTower
    (H : Subgroup (IdeleClassGroup K))
    (hclosed : IsClosed (H : Set (IdeleClassGroup K)))
    [H.FiniteIndex] :
    IsScalarTower K
      (closedFiniteIndexNormCyclotomicField (K := K) H)
      (closedFiniteIndexNormKummerField (K := K) H hclosed) := by
  exact IsScalarTower.of_algebraMap_eq' rfl

noncomputable instance
    closedFiniteIndexNormKummerFieldFiniteDimensionalOverBase
    (H : Subgroup (IdeleClassGroup K))
    (hclosed : IsClosed (H : Set (IdeleClassGroup K)))
    [H.FiniteIndex] :
    FiniteDimensional K
      (closedFiniteIndexNormKummerField (K := K) H hclosed) :=
  FiniteDimensional.trans K
    (closedFiniteIndexNormCyclotomicField (K := K) H)
    (closedFiniteIndexNormKummerField (K := K) H hclosed)

/-- The finite normal closure which is the actual Galois norm
neighbourhood attached to `H`. -/
noncomputable abbrev closedFiniteIndexNormAmbient
    (H : Subgroup (IdeleClassGroup K))
    (hclosed : IsClosed (H : Set (IdeleClassGroup K)))
    [H.FiniteIndex] : Type :=
  finiteNormalClosure K
    (closedFiniteIndexNormKummerField (K := K) H hclosed)

noncomputable instance closedFiniteIndexNormAmbientFiniteDimensional
    (H : Subgroup (IdeleClassGroup K))
    (hclosed : IsClosed (H : Set (IdeleClassGroup K)))
    [H.FiniteIndex] :
    FiniteDimensional K
      (closedFiniteIndexNormAmbient (K := K) H hclosed) := by
  unfold closedFiniteIndexNormAmbient
  infer_instance

noncomputable instance closedFiniteIndexNormAmbientNumberField
    (H : Subgroup (IdeleClassGroup K))
    (hclosed : IsClosed (H : Set (IdeleClassGroup K)))
    [H.FiniteIndex] :
    NumberField (closedFiniteIndexNormAmbient (K := K) H hclosed) := by
  unfold closedFiniteIndexNormAmbient
  exact
    finiteNormalClosure_numberField K
      (closedFiniteIndexNormKummerField (K := K) H hclosed)

noncomputable instance closedFiniteIndexNormAmbientIsGalois
    (H : Subgroup (IdeleClassGroup K))
    (hclosed : IsClosed (H : Set (IdeleClassGroup K)))
    [H.FiniteIndex] :
    IsGalois K (closedFiniteIndexNormAmbient (K := K) H hclosed) := by
  unfold closedFiniteIndexNormAmbient
  exact
    finiteNormalClosure_isGalois K
      (closedFiniteIndexNormKummerField (K := K) H hclosed)

/-- The finite normal closure of the cyclotomic full S-unit Kummer
extension attached to a closed finite-index subgroup is an actual finite
Galois norm neighbourhood contained in that subgroup. -/
theorem closedFiniteIndexSubgroup_has_finiteGaloisNormNeighborhood
    (H : Subgroup (IdeleClassGroup K))
    (hclosed : IsClosed (H : Set (IdeleClassGroup K)))
    [H.FiniteIndex] :
    (_root_.ideleClassNorm K
      (closedFiniteIndexNormAmbient (K := K) H hclosed)).range ≤ H := by
  classical
  let n := closedFiniteIndexNormExponent (K := K) H
  let seed := closedFiniteIndexNormSeed (K := K) H hclosed
  have hNormPower :
      (_root_.ideleClassNorm K
        (closedFiniteIndexNormAmbient (K := K) H hclosed)).range ≤
        ideleClassPowerLocalUnitSubgroup
          (K := K) n
          (cyclotomicKummerNormSupport (K := K) n seed) ∅ := by
    simpa only [n, seed, closedFiniteIndexNormAmbient,
      closedFiniteIndexNormKummerField,
      closedFiniteIndexNormCyclotomicField] using
      (cyclotomicFullSUnitKummerFiniteNormalClosure_ideleClassNormRange_le_powerLocalUnit
        (K := K) n
        (one_lt_closedFiniteIndexNormExponent (K := K) H) seed)
  have hPower :
      ideleClassPowerLocalUnitSubgroup
          (K := K) n
          (cyclotomicKummerNormSupport (K := K) n seed) ∅ ≤
        H := by
    by_cases hH : H = ⊤
    · simpa only [hH] using
        (le_top :
          ideleClassPowerLocalUnitSubgroup
              (K := K) n
              (cyclotomicKummerNormSupport (K := K) n seed) ∅ ≤
            (⊤ : Subgroup (IdeleClassGroup K)))
    · have hSeed :
          (RayClass.modulusInsideClosedFiniteIndex H hclosed).finitePart.support ⊆
            cyclotomicKummerNormSupport (K := K) n seed := by
        simpa only [seed, closedFiniteIndexNormSeed] using
          (subset_cyclotomicKummerNormSupport
            (K := K) n seed)
      have hIndexPower :=
        ideleClassPowerLocalUnitSubgroup_le_closedFiniteIndexSubgroup
          (K := K) H hclosed
          (cyclotomicKummerNormSupport (K := K) n seed) hSeed
      simpa only [n,
        closedFiniteIndexNormExponent_eq_index (K := K) H hH
      ] using hIndexPower
  exact hNormPower.trans hPower

end GlobalClassFields
end GlobalClassFieldTheory
end
end

section
-- module Solutions.OAIQ244_DUKE.GlobalClassFieldTheory_GlobalClassFields_OrdinaryNormClassField
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 400000
attribute [-instance] _root_.GlobalClassFieldTheory.GlobalClassFields.bigHilbertClassFieldNormSubgroup_normal _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexNormAmbientFiniteDimensional _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexNormAmbientIsGalois _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexNormAmbientNumberField _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexNormCyclotomicFieldFiniteDimensional _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexNormCyclotomicFieldIsCyclotomicExtension _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexNormCyclotomicFieldIsGalois _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexNormCyclotomicFieldNumberField _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexNormExponentNeZero _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexNormKummerFieldAlgebraOverBase _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexNormKummerFieldFiniteDimensional _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexNormKummerFieldFiniteDimensionalOverBase _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexNormKummerFieldModuleOverBase _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexNormKummerFieldNumberField _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexNormKummerFieldSMulOverBase _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexNormKummerFieldScalarTower _root_.GlobalClassFieldTheory.GlobalClassFields.smallHilbertClassFieldNormSubgroupFiniteIndex _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.instTopologicalSpaceLocalAlgebra _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.GlobalClassFieldTheory.GlobalClassFields.bigHilbertNormQuotient_finite _root_.GlobalClassFieldTheory.GlobalClassFields.bigHilbertNormSubgroup_finiteIndex
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

/-- Fix the canonical quotient group before converting fixed-field
equivalences to additive homomorphisms. -/
@[instance_reducible]
noncomputable def ordinaryNormClassFieldIdeleClassCommGroup
    (F : Type) [Field F] [NumberField F] :
    CommGroup (IdeleClassGroup F) :=
  QuotientGroup.Quotient.commGroup (IdeleGroup.principalSubgroup F)

attribute [local instance] ordinaryNormClassFieldIdeleClassCommGroup

variable
    (K L : Type) [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]

/- The fixed-field typeclass data used by the topology comparison are kept
behind named constants.  This prevents every consumer from rebuilding the
same finite-dimensional and number-field proof terms while reducing the
dependent fixed-field type. -/
noncomputable def ordinaryNormOpenSubgroup
    (H : Subgroup (IdeleClassGroup K))
    (hLH : (_root_.ideleClassNorm K L).range ≤ H) :
    ClassFormation.FiniteAbelianSubextension.NormOpenAddSubgroup
      rationalIdeleClassRepresentation
      (numberFieldTowerBaseSubgroup K L) := by
  let f : Additive (IdeleClassGroup K) →+
      KummerTheory.ambientFixedAddSubgroup
        rationalIdeleClassRepresentation (numberFieldTowerBaseSubgroup K L) :=
    (numberFieldTowerIdeleClassEquivAmbientFixed K L).toAddMonoidHom
  refine ⟨H.toAddSubgroup.map f, ?_⟩
  exact numberFieldTowerTransport_isNormOpen_of_normRange_le K L H hLH

end GlobalClassFields
end GlobalClassFieldTheory
end
end

section
-- module Solutions.OAIQ244_DUKE.GlobalClassFieldTheory_GlobalClassFields_ClosedFiniteIndexClassFieldConstruction
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 400000
attribute [-instance] _root_.GlobalClassFieldTheory.GlobalClassFields.bigHilbertClassFieldNormSubgroup_normal _root_.GlobalClassFieldTheory.GlobalClassFields.smallHilbertClassFieldNormSubgroupFiniteIndex _root_.GlobalClassFieldTheory.Reciprocity.infinitePlaceComplexificationOverfield_algebra _root_.GlobalClassFieldTheory.Reciprocity.infinitePlaceComplexificationOverfield_baseAlgebra _root_.GlobalClassFieldTheory.Reciprocity.ramifiedInfinitePlaceRealFixedField_algebra _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.instTopologicalSpaceLocalAlgebra _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.GlobalClassFieldTheory.GlobalClassFields.bigHilbertNormQuotient_finite _root_.GlobalClassFieldTheory.GlobalClassFields.bigHilbertNormSubgroup_finiteIndex
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI
attribute [local instance] OAI.starSubalgebraCommCStarAlgebra

set_option autoImplicit false

/-!
# Construction of a closed finite-index class field

This leaf fixes the finite Galois norm neighbourhood, abstract subextension,
and canonical fixed-field presentation attached to a closed finite-index
idèle-class subgroup. Norm-range and reciprocity statements live in later
leaves so their elaboration environments do not remain resident here.
-/

open scoped Classical IsMulCommutative NumberField

noncomputable section

namespace GlobalClassFieldTheory
namespace GlobalClassFields

open Reciprocity

variable {K : Type} [Field K] [NumberField K]

/-- The concrete finite Galois norm neighbourhood used to construct
the class field of `H`. -/
noncomputable abbrev closedFiniteIndexClassFieldNormAmbient
    (H : Subgroup (IdeleClassGroup K))
    (hclosed : IsClosed (H : Set (IdeleClassGroup K)))
    [H.FiniteIndex] : Type :=
  closedFiniteIndexNormAmbient (K := K) H hclosed

/-- The named norm-neighbourhood containment used by the selected
ordinary class-field construction. -/
theorem closedFiniteIndexClassFieldNormAmbient_normRange_le
    (H : Subgroup (IdeleClassGroup K))
    (hclosed : IsClosed (H : Set (IdeleClassGroup K)))
    [H.FiniteIndex] :
    (_root_.ideleClassNorm K
      (closedFiniteIndexClassFieldNormAmbient
        (K := K) H hclosed)).range ≤ H := by
  simpa only [closedFiniteIndexClassFieldNormAmbient] using
    (closedFiniteIndexSubgroup_has_finiteGaloisNormNeighborhood
      (K := K) H hclosed)

end GlobalClassFields
end GlobalClassFieldTheory
end
end

section
-- module Solutions.OAIQ244_DUKE.GlobalClassFieldTheory_Reciprocity_ComplexificationArtin_OverextensionArtin
attribute [-instance] _root_.GlobalClassFieldTheory.GlobalClassFields.ConductorialSubgroup.finiteIndex _root_.GlobalClassFieldTheory.GlobalClassFields.bigHilbertClassFieldNormSubgroup_normal _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexNormAmbientFiniteDimensional _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexNormAmbientIsGalois _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexNormAmbientNumberField _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexNormCyclotomicFieldFiniteDimensional _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexNormCyclotomicFieldIsCyclotomicExtension _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexNormCyclotomicFieldIsGalois _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexNormCyclotomicFieldNumberField _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexNormExponentNeZero _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexNormKummerFieldAlgebraOverBase _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexNormKummerFieldFiniteDimensional _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexNormKummerFieldFiniteDimensionalOverBase _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexNormKummerFieldModuleOverBase _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexNormKummerFieldNumberField _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexNormKummerFieldSMulOverBase _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexNormKummerFieldScalarTower _root_.GlobalClassFieldTheory.GlobalClassFields.ideleClassNorm_rangeFiniteIndex _root_.GlobalClassFieldTheory.GlobalClassFields.smallHilbertClassFieldNormSubgroupFiniteIndex _root_.GlobalClassFieldTheory.Reciprocity.abstractFixedFieldCyclotomicFiniteCompositum_baseAlgebra _root_.GlobalClassFieldTheory.Reciprocity.abstractFixedFieldCyclotomicFiniteCompositum_numberField _root_.GlobalClassFieldTheory.Reciprocity.abstractFixedFieldCyclotomicFiniteLayer_baseAlgebra _root_.GlobalClassFieldTheory.Reciprocity.abstractFixedFieldCyclotomicFiniteLayer_baseModule _root_.GlobalClassFieldTheory.Reciprocity.abstractFixedFieldCyclotomicFiniteLayer_layerAlgebra _root_.GlobalClassFieldTheory.Reciprocity.abstractFixedFieldCyclotomicFiniteLayer_numberField _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.boundedRealFields_numberField _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.GlobalClassFieldTheory.GlobalClassFields.bigHilbertNormQuotient_finite _root_.GlobalClassFieldTheory.GlobalClassFields.bigHilbertNormSubgroup_finiteIndex
attribute [-simp] _root_.GlobalClassFieldTheory.ClassFieldAxiom.hasseNormDiagonal_mk _root_.GlobalClassFieldTheory.GlobalClassFields.ConductorialSubgroup.ideleClassQuotientEquivOfNarrowFiniteConductorsEqOfRayClassGroupCardsEqQuotientCards_mk _root_.GlobalClassFieldTheory.GlobalClassFields.ConductorialSubgroup.mem_fullConductorInfinitePart_iff _root_.GlobalClassFieldTheory.GlobalClassFields.ConductorialSubgroup.narrowFiniteConductorRayClassGroupEquivQuotientOfCardEq_mk _root_.GlobalClassFieldTheory.GlobalClassFields.ConductorialSubgroup.narrowFiniteConductorRayClassGroupToQuotient_mk _root_.GlobalClassFieldTheory.GlobalClassFields.bigHilbertClassFieldQuotientCongr_mk _root_.GlobalClassFieldTheory.GlobalClassFields.bigHilbertClassFieldQuotientEquivNarrowClassGroup_mk _root_.GlobalClassFieldTheory.GlobalClassFields.bigHilbertClassFieldQuotientToIdeleClassNormQuotient_mk _root_.GlobalClassFieldTheory.GlobalClassFields.bigHilbertClassFieldQuotientToSmallHilbertClassFieldQuotient_mk _root_.GlobalClassFieldTheory.GlobalClassFields.ideleClassNormQuotientTowerMap_mk _root_.GlobalClassFieldTheory.GlobalClassFields.narrowFiniteConductorRayClassGroupToIdeleClassNormQuotient_mk _root_.GlobalClassFieldTheory.GlobalClassFields.normQuotientEquivOfNarrowFiniteConductorsEqOfRayClassGroupCardsEqNormQuotientCards_mk _root_.GlobalClassFieldTheory.GlobalClassFields.realSignToBigHilbertClassFieldQuotient_apply _root_.GlobalClassFieldTheory.GlobalClassFields.realSignToNarrowClassKernel_apply _root_.GlobalClassFieldTheory.GlobalClassFields.smallHilbertClassFieldQuotientCongr_mk _root_.GlobalClassFieldTheory.GlobalClassFields.smallHilbertClassFieldQuotientEquivClassGroup_mk _root_.GlobalClassFieldTheory.GlobalClassFields.smallHilbertClassFieldQuotientToIdeleClassNormQuotient_mk _root_.GlobalClassFieldTheory.IdealClassFieldTheory.smallHilbertClassFieldIdeleExtensionMap_mk' _root_.GlobalClassFieldTheory.Reciprocity.abstractFixedFieldCyclotomicIdeleClassArtinMonoidHom_mk _root_.GlobalClassFieldTheory.Reciprocity.abstractFixedFieldCyclotomicRestriction_infiniteGlobalArtinMonoidHom _root_.GlobalClassFieldTheory.Reciprocity.globalNormClassFromIdele_principalIdele _root_.GlobalClassFieldTheory.Reciprocity.globalNormClassFromIdele_relativeIdeleNorm_eq_one _root_.GlobalClassFieldTheory.Reciprocity.infiniteGlobalArtinMonoidHom_abstractFixedFieldCyclotomic_principalIdele _root_.GlobalClassFieldTheory.Reciprocity.mem_globalArtinFiniteSupport_iff _root_.IdeleGroup.count_fractionalIdeal _root_.IdeleGroup.fractionalIdeal_finitePrimeIdele _root_.IdeleGroup.idealClass_finitePrimeIdele _root_.OAI.PrimeDegreePackets.ThetaConstruction.schwartzCM_apply _root_.RayClass.signToNarrow_mk
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI
attribute [local instance] OAI.starSubalgebraCommCStarAlgebra

set_option autoImplicit false

/-!
# Artin reciprocity on the ramified infinite-place overextension

This module proves principal-idele triviality, descends the chosen Artin
product to the norm quotient, and identifies it with global reciprocity.
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

section

attribute [-instance]
  ramifiedInfinitePlaceRealFixedField_ratScalarTower

local instance
    ramifiedInfinitePlaceOverextensionIdeleClassGroupIsMulCommutative_r5232e0_1
    {F : Type} [Field F] [NumberField F] :
    IsMulCommutative (IdeleClassGroup F) :=
  ⟨⟨fun a b => mul_comm a b⟩⟩
omit [NumberField K] [FiniteDimensional K L] in
/-- The chosen local-factor Artin product on the actual special
overextension `L(i)/K'` is trivial on principal ideles. -/
@[simp]
theorem
    ramifiedInfinitePlaceOverextensionGlobalArtin_principalIdele
    (v : InfinitePlace K)
    (hRamified :
      (chosenInfinitePlaceAbove (L := L) v).IsRamified K)
    (x :
      (ramifiedInfinitePlaceRealFixedField
        (K := K) (L := L) v hRamified)ˣ) :
    globalArtinMonoidHom
        (K :=
          ramifiedInfinitePlaceRealFixedField
            (K := K) (L := L) v hRamified)
        (L :=
          infinitePlaceComplexificationOverfield
            (K := K) (L := L) v)
        (IdeleGroup.principalIdele
          (ramifiedInfinitePlaceRealFixedField
            (K := K) (L := L) v hRamified) x) =
      1 := by
  let :
      IsAbelianGalois ℚ rationalComplexificationCyclotomicField :=
    rationalComplexificationCyclotomicField_isAbelianGalois
  apply
    ramifiedInfinitePlaceOverextensionCyclotomicRestriction_injective
      (K := K) (L := L) v hRamified
  have hdiamond :=
    DFunLike.congr_fun
      (globalArtinMonoidHom_norm_restriction
        (K := ℚ)
        (L := rationalComplexificationCyclotomicField)
        (K' :=
          ramifiedInfinitePlaceRealFixedField
            (K := K) (L := L) v hRamified)
        (L' :=
          infinitePlaceComplexificationOverfield
            (K := K) (L := L) v))
      (IdeleGroup.principalIdele
        (ramifiedInfinitePlaceRealFixedField
          (K := K) (L := L) v hRamified) x)
  change
    ramifiedInfinitePlaceOverextensionCyclotomicRestriction
        (K := K) (L := L) v hRamified
        (globalArtinMonoidHom
          (K :=
            ramifiedInfinitePlaceRealFixedField
              (K := K) (L := L) v hRamified)
          (L :=
            infinitePlaceComplexificationOverfield
              (K := K) (L := L) v)
          (IdeleGroup.principalIdele
            (ramifiedInfinitePlaceRealFixedField
              (K := K) (L := L) v hRamified) x)) =
      globalArtinMonoidHom
        (K := ℚ)
        (L := rationalComplexificationCyclotomicField)
        (IdeleGroup.norm ℚ
          (ramifiedInfinitePlaceRealFixedField
            (K := K) (L := L) v hRamified)
          (IdeleGroup.principalIdele
            (ramifiedInfinitePlaceRealFixedField
              (K := K) (L := L) v hRamified) x)) at hdiamond
  rw [IdeleGroup.norm_principalIdele,
    rationalComplexificationGlobalArtin_principalIdele] at hdiamond
  simpa only [map_one] using hdiamond

/-- The actual local-factor product for the special overextension,
descended through principal ideles of its real fixed field. -/
noncomputable def
    ramifiedInfinitePlaceOverextensionIdeleClassArtinMonoidHom
    (v : InfinitePlace K)
    (hRamified :
      (chosenInfinitePlaceAbove (L := L) v).IsRamified K) :
    IdeleClassGroup
        (ramifiedInfinitePlaceRealFixedField
          (K := K) (L := L) v hRamified) →*
      Gal(
        (infinitePlaceComplexificationOverfield
          (K := K) (L := L) v) /
        (ramifiedInfinitePlaceRealFixedField
          (K := K) (L := L) v hRamified)) :=
  QuotientGroup.lift
    (IdeleGroup.principalSubgroup
      (ramifiedInfinitePlaceRealFixedField
        (K := K) (L := L) v hRamified))
    (globalArtinMonoidHom
      (K :=
        ramifiedInfinitePlaceRealFixedField
          (K := K) (L := L) v hRamified)
      (L :=
        infinitePlaceComplexificationOverfield
          (K := K) (L := L) v))
    (by
      rintro _ ⟨x, rfl⟩
      exact
        ramifiedInfinitePlaceOverextensionGlobalArtin_principalIdele
          (K := K) (L := L) v hRamified x)

omit [NumberField K] [FiniteDimensional K L] in
/-- Evaluation of the descended special-overextension Artin map on
an idele representative is the genuine product of chosen local
symbols. -/
@[simp]
theorem
    ramifiedInfinitePlaceOverextensionIdeleClassArtinMonoidHom_mk
    (v : InfinitePlace K)
    (hRamified :
      (chosenInfinitePlaceAbove (L := L) v).IsRamified K)
    (a :
      IdeleGroup
        (ramifiedInfinitePlaceRealFixedField
          (K := K) (L := L) v hRamified)) :
    ramifiedInfinitePlaceOverextensionIdeleClassArtinMonoidHom
        (K := K) (L := L) v hRamified
        (QuotientGroup.mk'
          (IdeleGroup.principalSubgroup
            (ramifiedInfinitePlaceRealFixedField
              (K := K) (L := L) v hRamified))
          a) =
      globalArtinMonoidHom
        (K :=
          ramifiedInfinitePlaceRealFixedField
            (K := K) (L := L) v hRamified)
        (L :=
          infinitePlaceComplexificationOverfield
            (K := K) (L := L) v)
        a := by
  rw [ramifiedInfinitePlaceOverextensionIdeleClassArtinMonoidHom]
  exact QuotientGroup.lift_mk _ _ _

omit [NumberField K] [FiniteDimensional K L] in
/-- The descended special-overextension Artin map kills every
genuine idele-class norm from its top field. -/
@[simp]
theorem
    ramifiedInfinitePlaceOverextensionIdeleClassArtinMonoidHom_ideleClassNorm
    (v : InfinitePlace K)
    (hRamified :
      (chosenInfinitePlaceAbove (L := L) v).IsRamified K)
    (c :
      IdeleClassGroup
        (infinitePlaceComplexificationOverfield
          (K := K) (L := L) v)) :
    ramifiedInfinitePlaceOverextensionIdeleClassArtinMonoidHom
        (K := K) (L := L) v hRamified
        (_root_.ideleClassNorm
          (ramifiedInfinitePlaceRealFixedField
            (K := K) (L := L) v hRamified)
          (infinitePlaceComplexificationOverfield
            (K := K) (L := L) v)
          c) =
      1 := by
  refine QuotientGroup.induction_on c ?_
  intro a
  change
    ramifiedInfinitePlaceOverextensionIdeleClassArtinMonoidHom
        (K := K) (L := L) v hRamified
        (_root_.ideleClassNorm
          (ramifiedInfinitePlaceRealFixedField
            (K := K) (L := L) v hRamified)
          (infinitePlaceComplexificationOverfield
            (K := K) (L := L) v)
          (QuotientGroup.mk'
            (IdeleGroup.principalSubgroup
              (infinitePlaceComplexificationOverfield
                (K := K) (L := L) v))
            a)) =
      1
  rw [_root_.ideleClassNorm_mk,
    ramifiedInfinitePlaceOverextensionIdeleClassArtinMonoidHom_mk]
  exact
    globalArtinMonoidHom_ideleNorm_eq_one
      (K :=
        ramifiedInfinitePlaceRealFixedField
          (K := K) (L := L) v hRamified)
      (L :=
        infinitePlaceComplexificationOverfield
          (K := K) (L := L) v)
      a

noncomputable def
    ramifiedInfinitePlaceOverextensionNormQuotientArtinData
    (v : InfinitePlace K)
    (hRamified :
      (chosenInfinitePlaceAbove (L := L) v).IsRamified K) :=
  quotientLiftData
    (A :=
      IdeleClassGroup
        (ramifiedInfinitePlaceRealFixedField
          (K := K) (L := L) v hRamified))
    (B :=
      Gal(
        (infinitePlaceComplexificationOverfield
          (K := K) (L := L) v) /
        (ramifiedInfinitePlaceRealFixedField
          (K := K) (L := L) v hRamified)))
    (_root_.ideleClassNorm
      (ramifiedInfinitePlaceRealFixedField
        (K := K) (L := L) v hRamified)
      (infinitePlaceComplexificationOverfield
        (K := K) (L := L) v)).range
    (ramifiedInfinitePlaceOverextensionIdeleClassArtinMonoidHom
      (K := K) (L := L) v hRamified)
    (by
      rintro _ ⟨c, rfl⟩
      exact
        ramifiedInfinitePlaceOverextensionIdeleClassArtinMonoidHom_ideleClassNorm
          (K := K) (L := L) v hRamified c)

/-- The chosen-local-factor Artin map on the actual norm quotient of
the special overextension. -/
noncomputable def
    ramifiedInfinitePlaceOverextensionNormQuotientArtinMonoidHom
    (v : InfinitePlace K)
    (hRamified :
      (chosenInfinitePlaceAbove (L := L) v).IsRamified K) :=
  (ramifiedInfinitePlaceOverextensionNormQuotientArtinData
    (K := K) (L := L) v hRamified).1

omit [NumberField K] [FiniteDimensional K L] in
/-- Evaluation of the norm-quotient Artin map on an idele-class
representative. -/
@[simp]
theorem
    ramifiedInfinitePlaceOverextensionNormQuotientArtinMonoidHom_mk
    (v : InfinitePlace K)
    (hRamified :
      (chosenInfinitePlaceAbove (L := L) v).IsRamified K) :
    ∀ c :
        IdeleClassGroup
          (ramifiedInfinitePlaceRealFixedField
            (K := K) (L := L) v hRamified),
      ramifiedInfinitePlaceOverextensionNormQuotientArtinMonoidHom
          (K := K) (L := L) v hRamified
          (QuotientGroup.mk c) =
        ramifiedInfinitePlaceOverextensionIdeleClassArtinMonoidHom
          (K := K) (L := L) v hRamified c :=
  (ramifiedInfinitePlaceOverextensionNormQuotientArtinData
    (K := K) (L := L) v hRamified).2

end

end ComplexConjugationOverextension

end Reciprocity
end GlobalClassFieldTheory
end
end

section
-- module Solutions.OAIQ244_DUKE.GlobalClassFieldTheory_Reciprocity_LocalGlobalArtinCompatibility_FinitePadicCyclicData
attribute [-instance] _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexNormAmbientIsGalois _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexNormCyclotomicFieldIsGalois _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexNormKummerFieldAlgebraOverBase _root_.GlobalClassFieldTheory.GlobalClassFields.finiteAbelianSubextensionAbstractRelativeFixedFieldFiniteDimensional _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.instTopologicalSpaceLocalAlgebra _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable
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
local instance numberFieldTowerExtensionNormal :
    (extensionSubgroup
      (numberFieldTowerBaseSubgroup K L)
      (numberFieldTowerTopSubgroup L)
      (numberFieldTowerTopSubgroup_le_baseSubgroup K L)).Normal :=
  numberFieldTowerExtensionSubgroup_normal K L

local instance finitePadicTowerExtensionQuotientFinite_r5232e0_1 :
    Finite
      ((numberFieldTowerBaseSubgroup K L).toSubgroup ⧸
        extensionSubgroup
          (numberFieldTowerBaseSubgroup K L)
          (numberFieldTowerTopSubgroup L)
          (numberFieldTowerTopSubgroup_le_baseSubgroup K L)) :=
  numberFieldTowerExtensionQuotient_finite K L
noncomputable local instance numberFieldTowerExtensionQuotientIsMulCommutative_r5232e0_1 :
    IsMulCommutative
      ((numberFieldTowerBaseSubgroup K L).toSubgroup ⧸
        extensionSubgroup
          (numberFieldTowerBaseSubgroup K L)
          (numberFieldTowerTopSubgroup L)
          (numberFieldTowerTopSubgroup_le_baseSubgroup K L)) := by
  let e :
      ((numberFieldTowerBaseSubgroup K L).toSubgroup ⧸
          extensionSubgroup
            (numberFieldTowerBaseSubgroup K L)
            (numberFieldTowerTopSubgroup L)
            (numberFieldTowerTopSubgroup_le_baseSubgroup K L)) ≃*
        Gal(L / K) :=
    numberFieldTowerExtensionQuotientEquivGaloisGroup K L
  exact
    { is_comm :=
        ⟨fun x y => by
          apply e.injective
          rw [map_mul, map_mul]
          exact
            (inferInstance :
              IsMulCommutative (Gal(L / K))).is_comm.comm
                (e x) (e y)⟩ }
local instance numberFieldTowerBaseSubgroupCompactSpace :
    CompactSpace
      (numberFieldTowerBaseSubgroup K L).toSubgroup :=
  isCompact_iff_compactSpace.mp
    (numberFieldTowerBaseSubgroup K L).isClosed'.isCompact

end Reciprocity
end GlobalClassFieldTheory
end
end

section
-- module Solutions.OAIQ244_DUKE.GlobalClassFieldTheory_Reciprocity_TopologicalGlobalNormResidue
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 400000
attribute [-instance] _root_.GlobalClassFieldTheory.GlobalClassFields.bigHilbertClassFieldNormSubgroup_normal _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexNormAmbientFiniteDimensional _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexNormAmbientIsGalois _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexNormAmbientNumberField _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexNormCyclotomicFieldFiniteDimensional _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexNormCyclotomicFieldIsCyclotomicExtension _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexNormCyclotomicFieldIsGalois _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexNormCyclotomicFieldNumberField _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexNormExponentNeZero _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexNormKummerFieldAlgebraOverBase _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexNormKummerFieldFiniteDimensional _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexNormKummerFieldFiniteDimensionalOverBase _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexNormKummerFieldModuleOverBase _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexNormKummerFieldNumberField _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexNormKummerFieldSMulOverBase _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexNormKummerFieldScalarTower _root_.GlobalClassFieldTheory.GlobalClassFields.smallHilbertClassFieldNormSubgroupFiniteIndex _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.instTopologicalSpaceLocalAlgebra _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.GlobalClassFieldTheory.GlobalClassFields.bigHilbertNormQuotient_finite _root_.GlobalClassFieldTheory.GlobalClassFields.bigHilbertNormSubgroup_finiteIndex
attribute [-simp] _root_.GlobalClassFieldTheory.ClassFieldAxiom.hasseNormDiagonal_mk _root_.GlobalClassFieldTheory.GlobalClassFields.ConductorialSubgroup.mem_fullConductorInfinitePart_iff _root_.GlobalClassFieldTheory.GlobalClassFields.bigHilbertClassFieldQuotientCongr_mk _root_.GlobalClassFieldTheory.GlobalClassFields.bigHilbertClassFieldQuotientEquivNarrowClassGroup_mk _root_.GlobalClassFieldTheory.GlobalClassFields.bigHilbertClassFieldQuotientToIdeleClassNormQuotient_mk _root_.GlobalClassFieldTheory.GlobalClassFields.bigHilbertClassFieldQuotientToSmallHilbertClassFieldQuotient_mk _root_.GlobalClassFieldTheory.GlobalClassFields.ideleClassNormQuotientTowerMap_mk _root_.GlobalClassFieldTheory.GlobalClassFields.normQuotientEquivOfNarrowFiniteConductorsEqOfRayClassGroupCardsEqNormQuotientCards_mk _root_.GlobalClassFieldTheory.GlobalClassFields.realSignToBigHilbertClassFieldQuotient_apply _root_.GlobalClassFieldTheory.GlobalClassFields.realSignToNarrowClassKernel_apply _root_.GlobalClassFieldTheory.GlobalClassFields.smallHilbertClassFieldQuotientCongr_mk _root_.GlobalClassFieldTheory.GlobalClassFields.smallHilbertClassFieldQuotientEquivClassGroup_mk _root_.GlobalClassFieldTheory.GlobalClassFields.smallHilbertClassFieldQuotientToIdeleClassNormQuotient_mk _root_.GlobalClassFieldTheory.IdealClassFieldTheory.smallHilbertClassFieldIdeleExtensionMap_mk' _root_.GlobalClassFieldTheory.Reciprocity.abstractFixedFieldCyclotomicIdeleClassArtinMonoidHom_mk _root_.GlobalClassFieldTheory.Reciprocity.abstractFixedFieldCyclotomicRestriction_infiniteGlobalArtinMonoidHom _root_.GlobalClassFieldTheory.Reciprocity.globalNormClassFromIdele_principalIdele _root_.GlobalClassFieldTheory.Reciprocity.globalNormClassFromIdele_relativeIdeleNorm_eq_one _root_.GlobalClassFieldTheory.Reciprocity.infiniteGlobalArtinMonoidHom_abstractFixedFieldCyclotomic_principalIdele _root_.GlobalClassFieldTheory.Reciprocity.mem_globalArtinFiniteSupport_iff _root_.GlobalClassFieldTheory.Reciprocity.ramifiedInfinitePlaceOverextensionGlobalArtin_principalIdele _root_.GlobalClassFieldTheory.Reciprocity.ramifiedInfinitePlaceOverextensionIdeleClassArtinMonoidHom_ideleClassNorm _root_.GlobalClassFieldTheory.Reciprocity.ramifiedInfinitePlaceOverextensionIdeleClassArtinMonoidHom_mk _root_.GlobalClassFieldTheory.Reciprocity.ramifiedInfinitePlaceOverextensionNormQuotientArtinMonoidHom_mk _root_.GlobalClassFieldTheory.Reciprocity.rationalComplexificationGlobalArtin_principalIdele _root_.IdeleGroup.count_fractionalIdeal _root_.IdeleGroup.fractionalIdeal_finitePrimeIdele _root_.IdeleGroup.idealClass_finitePrimeIdele _root_.OAI.PrimeDegreePackets.ThetaConstruction.schwartzCM_apply _root_.RayClass.signToNarrow_mk
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI
attribute [local instance] OAI.starSubalgebraCommCStarAlgebra

set_option autoImplicit false

/-!
# Topological global norm-residue reciprocity

For a finite abelian extension of number fields, the genuine
idele-class norm range is open in the ordinary idele-class topology.
Hence its native quotient topology is discrete.  The finite Krull
Galois group is discrete as well, so the algebraic global norm-residue
equivalence upgrades to a homeomorphic multiplicative equivalence.

This file also bundles the quotient map and the global norm-residue map
as continuous homomorphisms, and proves that forgetting their topology
recovers the previously constructed actual global norm-residue symbol.
-/

open scoped IsMulCommutative NumberField
open NumberField

noncomputable section

namespace GlobalClassFieldTheory
namespace Reciprocity

/-- Fix the canonical class-group dictionary before bundling norm-quotient maps. -/
@[instance_reducible]
noncomputable def topologicalNormResidueIdeleClassCommGroup
    (F : Type) [Field F] [NumberField F] :
    CommGroup (IdeleClassGroup F) :=
  QuotientGroup.Quotient.commGroup (IdeleGroup.principalSubgroup F)

attribute [local instance] topologicalNormResidueIdeleClassCommGroup

theorem topologicalNormResidueIdeleClassIsMulCommutative
    (F : Type) [Field F] [NumberField F] :
    IsMulCommutative (IdeleClassGroup F) :=
  IsMulCommutative.of_comm (fun a b => mul_comm a b)

attribute [local instance] topologicalNormResidueIdeleClassIsMulCommutative

variable
    (K L : Type) [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsAbelianGalois K L]

/-- The native quotient topology on
`C_K / N_{L/K}(C_L)` is discrete because the genuine ordinary
idele-class norm range is open. -/
theorem ideleClassNormQuotient_discreteTopology :
    DiscreteTopology
      (IdeleClassGroup K ⧸
        (_root_.ideleClassNorm K L).range) := by
  apply QuotientGroup.discreteTopology
  exact
    GlobalClassFields.ideleClassNorm_range_isOpen
      (K := K) (L := L)

/-- Global norm-residue reciprocity as a homeomorphic multiplicative
equivalence between the native norm quotient and the finite Krull
Galois group.  Both directions are continuous in their genuine
topologies. -/
noncomputable def globalNormResidueContinuousMulEquiv :
    (IdeleClassGroup K ⧸
        (_root_.ideleClassNorm K L).range) ≃ₜ*
      Gal(L / K) := by
  let : DiscreteTopology
      (IdeleClassGroup K ⧸
        (_root_.ideleClassNorm K L).range) :=
    ideleClassNormQuotient_discreteTopology K L
  let e :
      (IdeleClassGroup K ⧸
          (_root_.ideleClassNorm K L).range) ≃*
        Gal(L / K) :=
    AddEquiv.toMultiplicative
      (globalNormResidueEquiv K L)
  exact
    { e with
      continuous_toFun := continuous_of_discreteTopology
      continuous_invFun := continuous_of_discreteTopology }

/-- Evaluation of the topological norm-residue equivalence is the
existing actual norm-residue equivalence on the same quotient class. -/
@[simp]
theorem globalNormResidueContinuousMulEquiv_apply
    (c :
      IdeleClassGroup K ⧸
        (_root_.ideleClassNorm K L).range) :
    globalNormResidueContinuousMulEquiv K L c =
      Additive.toMul
        (globalNormResidueEquiv K L
          (Additive.ofMul c)) := by
  rfl

/-- Global reciprocity in the direction used by the class-field
correspondence,

`Gal(L / K) ≃ₜ* C_K / N_{L/K}(C_L)`.

This is the inverse of the norm-residue equivalence as a
`ContinuousMulEquiv`, so the Krull topology on the finite Galois group
and the native quotient topology on the idele-class quotient are part
of the public statement. -/
noncomputable def globalReciprocityContinuousMulEquiv :
    Gal(L / K) ≃ₜ*
      (IdeleClassGroup K ⧸
        (_root_.ideleClassNorm K L).range) :=
  (globalNormResidueContinuousMulEquiv K L).symm

/-- Evaluation of topological global reciprocity is the inverse of the
actual norm-residue equivalence, with no additional choice of an
abstract group isomorphism. -/
@[simp]
theorem globalReciprocityContinuousMulEquiv_apply
    (σ : Gal(L / K)) :
    globalReciprocityContinuousMulEquiv K L σ =
      Additive.toMul
        ((globalNormResidueEquiv K L).symm
          (Additive.ofMul σ)) := by
  rfl

/-- The genuine quotient map
`C_K → C_K / N_{L/K}(C_L)`, bundled with continuity for the native
ordinary quotient topology. -/
noncomputable def ideleClassNormQuotientContinuousMonoidHom :
    IdeleClassGroup K →ₜ*
      (IdeleClassGroup K ⧸
        (_root_.ideleClassNorm K L).range) :=
  { QuotientGroup.mk'
      (_root_.ideleClassNorm K L).range with
    continuous_toFun := QuotientGroup.continuous_mk }

/-- The actual global norm-residue map, bundled as a continuous
homomorphism on the ordinary idele-class topology. -/
noncomputable def globalNormResidueContinuousMonoidHom :
    IdeleClassGroup K →ₜ* Gal(L / K) :=
  (ContinuousMonoidHom.toContinuousMonoidHom
      (globalNormResidueContinuousMulEquiv K L)).comp
    (ideleClassNormQuotientContinuousMonoidHom K L)

/-- Evaluation of the continuous global norm-residue map agrees with
the existing actual global norm-residue symbol. -/
@[simp]
theorem globalNormResidueContinuousMonoidHom_apply
    (c : IdeleClassGroup K) :
    globalNormResidueContinuousMonoidHom K L c =
      globalNormResidueMonoidHom K L c := by
  rfl

end Reciprocity
end GlobalClassFieldTheory
end
end


