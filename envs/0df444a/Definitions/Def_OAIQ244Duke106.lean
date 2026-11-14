-- Prove2me | Definitions.Def_OAIQ244Duke106
-- name    : OAIQ244Duke106
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-14T03:36:27.527204+00:00
-- url     : https://prove2.me/theorems/f4079e57-dfe2-4b97-9775-3d9bc1e1ea05
-- title:
--   Definitions bundle OAIQ244Duke106 of the split of OpenAI, Equidistribution of Prime-Degree Torus Packets with Arbitrary Local Type
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.DukePrimeDegree.prime_degree_packet_measure_equidistribution_unconditional` and `OAI.DukePrimeDegree.prime_degree_packet_measures_tendsto_haar_unconditional`, carved from OpenAI's openai/math development (OpenAI, *Equidistribution of Prime-Degree Torus Packets with Arbitrary Local Type*, OpenAI Math Release, September 24, 2026, result family 15, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 53 declarations of OpenAI's Lean: 15 definitions, 2 instances and 36 theorems. The definitions and types are `GlobalClassFieldTheory.GlobalClassFields.ideleClassNormFrobeniusClass`, `GlobalClassFieldTheory.GlobalClassFields.narrowFiniteConductorRayPrimeClass`, `GlobalClassFieldTheory.GlobalClassFields.ordinaryNormClassFieldBase`, `GlobalClassFieldTheory.GlobalClassFields.ordinaryNormClassFieldBaseEquiv`, `GlobalClassFieldTheory.IdealClassFieldTheory.idealArtinGaloisMap`, `GlobalClassFieldTheory.IdealClassFieldTheory.idealArtinKernel`, `GlobalClassFieldTheory.IdealClassFieldTheory.idealArtinMap`, `GlobalClassFieldTheory.IdealClassFieldTheory.idealClassQuotientEquivGaloisGroup`, `GlobalClassFieldTheory.IdealClassFieldTheory.idealClassQuotientEquivNormQuotient`, `GlobalClassFieldTheory.IdealClassFieldTheory.idealRayClassArtinMap`, `GlobalClassFieldTheory.IdealClassFieldTheory.rayClassToNormQuotient`, `GlobalClassFieldTheory.Reciprocity.finitePlaceSeparableClosureCyclotomicRestriction`, `GlobalClassFieldTheory.Reciprocity.finitePlaceSeparableClosurePadicCyclotomicDegree`, `GlobalClassFieldTheory.Reciprocity.numberFieldTowerBaseSubgroupPadicCyclotomicDegree`, `GlobalClassFieldTheory.Reciprocity.rationalSeparableClosurePadicCyclotomicDegree`.
--
--   **Sources.** They come from these modules of lean/OAI/NumberTheory, in whole or in part: `GlobalClassFieldTheory_GlobalClassFields_ConductorFrobenius`, `GlobalClassFieldTheory_GlobalClassFields_HilbertClassFieldPrimeSplitting`, `GlobalClassFieldTheory_GlobalClassFields_OrdinaryNormClassField`, `GlobalClassFieldTheory_GlobalClassFields_RayClassPrimeIdele`, `GlobalClassFieldTheory_IdealClassFieldTheory_IdealArtinMap`, `GlobalClassFieldTheory_IdealClassFieldTheory_IdealArtinQuotient`, `GlobalClassFieldTheory_IdealClassFieldTheory_SmallHilbertSplitting`, `GlobalClassFieldTheory_Reciprocity_ComplexificationArtin_OverextensionArtin`, `GlobalClassFieldTheory_Reciprocity_CyclotomicAbstractFixedFieldArtin`, `GlobalClassFieldTheory_Reciprocity_GlobalNormResidue`, `GlobalClassFieldTheory_Reciprocity_LocalGlobalArtinCompatibility_FinitePadicCyclicData`, `GlobalClassFieldTheory_Reciprocity_LocalGlobalArtinCompatibility_SeparableClosurePadicLift`.
--
--   **Imports.** It imports the bundle `OAIQ244Duke102` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ244Duke107` and `OAIQ244Duke108`; the statement `GlobalClassFieldTheory.Reciprocity.ramifiedInfinitePlaceOverextensionNormQuotientArtinMonoidHom_eq_globalNormResidue_apply`; the proofs of `GlobalClassFieldTheory.Reciprocity.ramifiedInfinitePlaceOverextensionIdeleClassArtinMonoidHom_eq_globalNormResidue_apply`, `GlobalClassFieldTheory.Reciprocity.ramifiedInfinitePlaceOverextensionNormQuotientArtinMonoidHom_bijective` and `GlobalClassFieldTheory.Reciprocity.ramifiedInfinitePlaceOverextensionNormQuotientArtinMonoidHom_eq_globalNormResidue_apply`.
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
-- module Solutions.OAIQ244_DUKE.GlobalClassFieldTheory_Reciprocity_GlobalNormResidue
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 400000
attribute [-instance] _root_.GlobalClassFieldTheory.GlobalClassFields.ConductorialSubgroup.finiteIndex _root_.GlobalClassFieldTheory.GlobalClassFields.bigHilbertClassFieldNormSubgroup_normal _root_.GlobalClassFieldTheory.GlobalClassFields.ideleClassNorm_rangeFiniteIndex _root_.GlobalClassFieldTheory.GlobalClassFields.smallHilbertClassFieldNormSubgroupFiniteIndex _root_.GlobalClassFieldTheory.Reciprocity.abstractFixedFieldCyclotomicCompositum_algebra _root_.GlobalClassFieldTheory.Reciprocity.abstractFixedFieldCyclotomicCompositum_baseScalarTower _root_.GlobalClassFieldTheory.Reciprocity.abstractFixedFieldCyclotomicCompositum_scalarTower _root_.GlobalClassFieldTheory.Reciprocity.abstractFixedFieldCyclotomicFiniteCompositum_baseAlgebra _root_.GlobalClassFieldTheory.Reciprocity.abstractFixedFieldCyclotomicFiniteCompositum_baseScalarTower _root_.GlobalClassFieldTheory.Reciprocity.abstractFixedFieldCyclotomicFiniteCompositum_finiteDimensional _root_.GlobalClassFieldTheory.Reciprocity.abstractFixedFieldCyclotomicFiniteCompositum_numberField _root_.GlobalClassFieldTheory.Reciprocity.abstractFixedFieldCyclotomicFiniteGaloisLayer_scalarTower _root_.GlobalClassFieldTheory.Reciprocity.abstractFixedFieldCyclotomicFiniteLayer_baseAlgebra _root_.GlobalClassFieldTheory.Reciprocity.abstractFixedFieldCyclotomicFiniteLayer_baseModule _root_.GlobalClassFieldTheory.Reciprocity.abstractFixedFieldCyclotomicFiniteLayer_baseSMul _root_.GlobalClassFieldTheory.Reciprocity.abstractFixedFieldCyclotomicFiniteLayer_baseScalarTower _root_.GlobalClassFieldTheory.Reciprocity.abstractFixedFieldCyclotomicFiniteLayer_finiteDimensional _root_.GlobalClassFieldTheory.Reciprocity.abstractFixedFieldCyclotomicFiniteLayer_isAbelianGalois _root_.GlobalClassFieldTheory.Reciprocity.abstractFixedFieldCyclotomicFiniteLayer_layerAlgebra _root_.GlobalClassFieldTheory.Reciprocity.abstractFixedFieldCyclotomicFiniteLayer_layerSMul _root_.GlobalClassFieldTheory.Reciprocity.abstractFixedFieldCyclotomicFiniteLayer_layerScalarTower _root_.GlobalClassFieldTheory.Reciprocity.abstractFixedFieldCyclotomicFiniteLayer_numberField _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.boundedRealFields_finite _root_.OAI.PrimeDegreePackets.instT2SpaceLocalAlgebra _root_.OAI.PrimeDegreePackets.instTopologicalSpaceLocalAlgebra _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.OAI.PrimeDegreePackets.xT2Space _root_.GlobalClassFieldTheory.GlobalClassFields.bigHilbertNormQuotient_finite _root_.GlobalClassFieldTheory.GlobalClassFields.bigHilbertNormSubgroup_finiteIndex _root_.GlobalClassFieldTheory.GlobalClassFields.narrowClassGroup_finite
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

/-- The global norm-residue equivalence on a finite abstract norm class,
after transport to the ordinary idele-class norm quotient. -/
theorem globalNormResidueEquiv_finiteNormClass
    (x : FiniteNormQuotient rationalIdeleClassRepresentation
      (numberFieldTowerBaseSubgroup K L)
      (numberFieldTowerTopSubgroup L)
      (numberFieldTowerTopSubgroup_le_baseSubgroup K L)) :
    globalNormResidueEquiv K L
        (numberFieldTowerFiniteNormQuotientEquivIdeleClassNormQuotient
          K L x) =
      numberFieldTowerAbelianizedExtensionQuotientEquivGaloisGroup K L
        (rationalCyclotomicDegreeData.normResidueSymbol
          rationalIdeleClassRepresentation
          rationalCyclotomicIdeleClassValuationData
          rationalIdeleClassRepresentation_satisfiesClassFieldAxiom
          (numberFieldTowerReciprocityFiniteAbstractField K L)
          (numberFieldTowerFiniteGaloisSubextension K L) x) :=
  (globalNormResidueEquiv_transport_apply K L x).trans
    (numberFieldTowerAbstractNormResidueGaloisEquiv_apply K L x)

end Reciprocity
end GlobalClassFieldTheory
end
end

section
-- module Solutions.OAIQ244_DUKE.GlobalClassFieldTheory_IdealClassFieldTheory_IdealArtinMap
attribute [-instance] _root_.GlobalClassFieldTheory.GlobalClassFields.ConductorialSubgroup.finiteIndex _root_.GlobalClassFieldTheory.GlobalClassFields.bigHilbertClassFieldNormSubgroup_normal _root_.GlobalClassFieldTheory.GlobalClassFields.ideleClassNorm_rangeFiniteIndex _root_.GlobalClassFieldTheory.GlobalClassFields.smallHilbertClassFieldNormSubgroupFiniteIndex _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.GlobalClassFieldTheory.GlobalClassFields.bigHilbertNormQuotient_finite _root_.GlobalClassFieldTheory.GlobalClassFields.bigHilbertNormSubgroup_finiteIndex
attribute [-simp] _root_.GlobalClassFieldTheory.ClassFieldAxiom.hasseNormDiagonal_mk _root_.GlobalClassFieldTheory.GlobalClassFields.ConductorialSubgroup.ideleClassQuotientEquivOfNarrowFiniteConductorsEqOfRayClassGroupCardsEqQuotientCards_mk _root_.GlobalClassFieldTheory.GlobalClassFields.ConductorialSubgroup.mem_fullConductorInfinitePart_iff _root_.GlobalClassFieldTheory.GlobalClassFields.ConductorialSubgroup.narrowFiniteConductorRayClassGroupEquivQuotientOfCardEq_mk _root_.GlobalClassFieldTheory.GlobalClassFields.ConductorialSubgroup.narrowFiniteConductorRayClassGroupToQuotient_mk _root_.GlobalClassFieldTheory.GlobalClassFields.bigHilbertClassFieldQuotientCongr_mk _root_.GlobalClassFieldTheory.GlobalClassFields.bigHilbertClassFieldQuotientEquivNarrowClassGroup_mk _root_.GlobalClassFieldTheory.GlobalClassFields.bigHilbertClassFieldQuotientToIdeleClassNormQuotient_mk _root_.GlobalClassFieldTheory.GlobalClassFields.bigHilbertClassFieldQuotientToSmallHilbertClassFieldQuotient_mk _root_.GlobalClassFieldTheory.GlobalClassFields.ideleClassNormQuotientTowerMap_mk _root_.GlobalClassFieldTheory.GlobalClassFields.narrowFiniteConductorRayClassGroupToIdeleClassNormQuotient_mk _root_.GlobalClassFieldTheory.GlobalClassFields.normQuotientEquivOfNarrowFiniteConductorsEqOfRayClassGroupCardsEqNormQuotientCards_mk _root_.GlobalClassFieldTheory.GlobalClassFields.realSignToBigHilbertClassFieldQuotient_apply _root_.GlobalClassFieldTheory.GlobalClassFields.realSignToNarrowClassKernel_apply _root_.GlobalClassFieldTheory.GlobalClassFields.smallHilbertClassFieldQuotientCongr_mk _root_.GlobalClassFieldTheory.GlobalClassFields.smallHilbertClassFieldQuotientEquivClassGroup_mk _root_.GlobalClassFieldTheory.GlobalClassFields.smallHilbertClassFieldQuotientToIdeleClassNormQuotient_mk _root_.GlobalClassFieldTheory.IdealClassFieldTheory.smallHilbertClassFieldIdeleExtensionMap_mk' _root_.GlobalClassFieldTheory.Reciprocity.abstractFixedFieldCyclotomicIdeleClassArtinMonoidHom_mk _root_.GlobalClassFieldTheory.Reciprocity.abstractFixedFieldCyclotomicRestriction_infiniteGlobalArtinMonoidHom _root_.GlobalClassFieldTheory.Reciprocity.globalNormClassFromIdele_principalIdele _root_.GlobalClassFieldTheory.Reciprocity.globalNormClassFromIdele_relativeIdeleNorm_eq_one _root_.GlobalClassFieldTheory.Reciprocity.infiniteGlobalArtinMonoidHom_abstractFixedFieldCyclotomic_principalIdele _root_.GlobalClassFieldTheory.Reciprocity.mem_globalArtinFiniteSupport_iff _root_.GlobalClassFieldTheory.Reciprocity.rationalComplexificationGlobalArtin_principalIdele _root_.IdeleGroup.fractionalIdeal_finitePrimeIdele _root_.IdeleGroup.idealClass_finitePrimeIdele _root_.OAI.PrimeDegreePackets.ThetaConstruction.schwartzCM_apply _root_.RayClass.signToNarrow_mk
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI
attribute [local instance] OAI.starSubalgebraCommCStarAlgebra

set_option autoImplicit false

/-!
# The ideal-theoretic Artin map

Let `N ≤ C_K` be a class-field norm subgroup and let `m` be a defining
modulus, so `C_K^m ≤ N`.  The idelic quotient map then factors through the
ideal ray class group.  Composing with the projection from ideals prime to
`m` gives the ideal-theoretic Artin map.  This file proves its surjectivity,
identifies its kernel, and records the exact sequence.

The target is kept as the concrete reciprocity quotient `C_K / N`; global
reciprocity identifies this quotient with the corresponding abelian Galois
group.
-/

open scoped NumberField BigOperators NumberField.LiesOver

noncomputable section

namespace GlobalClassFieldTheory
namespace IdealClassFieldTheory

open NumberField

variable {K : Type} [Field K] [NumberField K]

local instance
    idealArtinMap_ideleClassGroupIsMulCommutative :
    IsMulCommutative (IdeleClassGroup K) :=
  ⟨⟨fun a b => mul_comm a b⟩⟩

local instance ideleClassSubgroupNormal
    (N : Subgroup (IdeleClassGroup K)) : N.Normal :=
  N.normal_of_isMulCommutative

/-- The quotient map from the ray class group modulo a defining modulus
to the class-field reciprocity quotient. -/
def rayClassToNormQuotient
    (m : RayClass.Modulus K)
    (N : Subgroup (IdeleClassGroup K))
    (hm : RayClass.Modulus.congruenceSubgroup m ≤ N) :
    RayClass.RayClassGroup m →*
      IdeleClassGroup K ⧸ N :=
  QuotientGroup.map
    (RayClass.Modulus.congruenceSubgroup m) N
    (MonoidHom.id (IdeleClassGroup K)) hm

/-- The ray-class quotient map sends the class of an idele class to its
class modulo the norm subgroup. -/
@[simp]
theorem rayClassToNormQuotient_mk
    (m : RayClass.Modulus K)
    (N : Subgroup (IdeleClassGroup K))
    (hm : RayClass.Modulus.congruenceSubgroup m ≤ N)
    (c : IdeleClassGroup K) :
    rayClassToNormQuotient m N hm
        (QuotientGroup.mk'
          (RayClass.Modulus.congruenceSubgroup m) c) =
      QuotientGroup.mk' N c :=
  rfl

/-- The quotient map attached to a defining modulus is surjective. -/
theorem rayClassToNormQuotient_surjective
    (m : RayClass.Modulus K)
    (N : Subgroup (IdeleClassGroup K))
    (hm : RayClass.Modulus.congruenceSubgroup m ≤ N) :
    Function.Surjective
      (rayClassToNormQuotient m N hm) := by
  intro q
  refine QuotientGroup.induction_on q ?_
  intro c
  exact
    ⟨QuotientGroup.mk'
        (RayClass.Modulus.congruenceSubgroup m) c, rfl⟩

/-- The Artin map on the ideal ray class group, obtained from the
idele-theoretic reciprocity quotient. -/
def idealRayClassArtinMap
    (m : RayClass.Modulus K)
    (N : Subgroup (IdeleClassGroup K))
    (hm : RayClass.Modulus.congruenceSubgroup m ≤ N) :
    RayClass.IdealRayClassGroup m →*
      IdeleClassGroup K ⧸ N :=
  (rayClassToNormQuotient m N hm).comp
    (RayClass.rayClassGroupEquivIdealRayClassGroup m).symm.toMonoidHom

/-- The ideal-ray-class Artin map is surjective. -/
theorem idealRayClassArtinMap_surjective
    (m : RayClass.Modulus K)
    (N : Subgroup (IdeleClassGroup K))
    (hm : RayClass.Modulus.congruenceSubgroup m ≤ N) :
    Function.Surjective
      (idealRayClassArtinMap m N hm) := by
  exact
    (rayClassToNormQuotient_surjective m N hm).comp
      (RayClass.rayClassGroupEquivIdealRayClassGroup m).symm.surjective

/-- The Artin map on fractional ideals prime to `m`. -/
def idealArtinMap
    (m : RayClass.Modulus K)
    (N : Subgroup (IdeleClassGroup K))
    (hm : RayClass.Modulus.congruenceSubgroup m ≤ N) :
    RayClass.primeToModulusIdeals m →*
      IdeleClassGroup K ⧸ N :=
  (idealRayClassArtinMap m N hm).comp
    (QuotientGroup.mk'
      (RayClass.principalRayIdealSubgroup m))

/-- The ideal group `H_m` attached to `N`: precisely the ideals whose
Artin class is trivial. -/
def idealArtinKernel
    (m : RayClass.Modulus K)
    (N : Subgroup (IdeleClassGroup K))
    (hm : RayClass.Modulus.congruenceSubgroup m ≤ N) :
    Subgroup (RayClass.primeToModulusIdeals m) :=
  (idealArtinMap m N hm).ker

/-- The Artin map on ideals is surjective. -/
theorem idealArtinMap_surjective
    (m : RayClass.Modulus K)
    (N : Subgroup (IdeleClassGroup K))
    (hm : RayClass.Modulus.congruenceSubgroup m ≤ N) :
    Function.Surjective (idealArtinMap m N hm) := by
  exact
    (idealRayClassArtinMap_surjective m N hm).comp
      (QuotientGroup.mk'_surjective
        (RayClass.principalRayIdealSubgroup m))

section ActualGaloisArtin

variable
    {L : Type} [Field L] [NumberField L] [Algebra K L]
    [IsAbelianGalois K L]

/-- The ideal-theoretic Artin map with its actual Galois-group target.

For a defining modulus of the genuine norm subgroup
`N_{L/K} C_L`, this is the quotient-valued ideal Artin map followed by
the global norm-residue equivalence
`C_K / N_{L/K} C_L ≃ Gal(L/K)`. -/
noncomputable def idealArtinGaloisMap
    (m : RayClass.Modulus K)
    (hm :
      RayClass.Modulus.congruenceSubgroup m ≤
        (_root_.ideleClassNorm K L).range) :
    RayClass.primeToModulusIdeals m →*
      (L ≃ₐ[K] L) :=
  (AddEquiv.toMultiplicative
      (Reciprocity.globalNormResidueEquiv K L)).toMonoidHom.comp
    (idealArtinMap m
      ((_root_.ideleClassNorm K L).range) hm)

/-- Evaluation of the actual ideal Artin map is the global
norm-residue equivalence applied to the quotient-valued ideal Artin
class. -/
@[simp]
theorem idealArtinGaloisMap_apply
    (m : RayClass.Modulus K)
    (hm :
      RayClass.Modulus.congruenceSubgroup m ≤
        (_root_.ideleClassNorm K L).range)
    (a : RayClass.primeToModulusIdeals m) :
    idealArtinGaloisMap (K := K) (L := L) m hm a =
      Additive.toMul
        (Reciprocity.globalNormResidueEquiv K L
          (Additive.ofMul
            (idealArtinMap m
              ((_root_.ideleClassNorm K L).range) hm a))) :=
  rfl

/-- Passing from the genuine norm quotient to the actual Galois group
does not change the ideal Artin kernel. -/
@[simp]
theorem idealArtinGaloisMap_ker
    (m : RayClass.Modulus K)
    (hm :
      RayClass.Modulus.congruenceSubgroup m ≤
        (_root_.ideleClassNorm K L).range) :
    (idealArtinGaloisMap
        (K := K) (L := L) m hm).ker =
      idealArtinKernel m
        ((_root_.ideleClassNorm K L).range) hm := by
  ext a
  let e :=
    AddEquiv.toMultiplicative
      (Reciprocity.globalNormResidueEquiv K L)
  change
    e
          (idealArtinMap m
            ((_root_.ideleClassNorm K L).range) hm a) =
        1 ↔
      idealArtinMap m
          ((_root_.ideleClassNorm K L).range) hm a =
        1
  exact e.map_eq_one_iff

end ActualGaloisArtin

end IdealClassFieldTheory
end GlobalClassFieldTheory
end
end

section
-- module Solutions.OAIQ244_DUKE.GlobalClassFieldTheory_IdealClassFieldTheory_IdealArtinQuotient
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 400000
attribute [-instance] _root_.GlobalClassFieldTheory.GlobalClassFields.ConductorialSubgroup.finiteIndex _root_.GlobalClassFieldTheory.GlobalClassFields.bigHilbertClassFieldNormSubgroup_normal _root_.GlobalClassFieldTheory.GlobalClassFields.ideleClassNorm_rangeFiniteIndex _root_.GlobalClassFieldTheory.GlobalClassFields.smallHilbertClassFieldNormSubgroupFiniteIndex _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.GlobalClassFieldTheory.GlobalClassFields.bigHilbertNormQuotient_finite _root_.GlobalClassFieldTheory.GlobalClassFields.bigHilbertNormSubgroup_finiteIndex
attribute [-simp] _root_.GlobalClassFieldTheory.ClassFieldAxiom.hasseNormDiagonal_mk _root_.GlobalClassFieldTheory.GlobalClassFields.ConductorialSubgroup.ideleClassQuotientEquivOfNarrowFiniteConductorsEqOfRayClassGroupCardsEqQuotientCards_mk _root_.GlobalClassFieldTheory.GlobalClassFields.ConductorialSubgroup.mem_fullConductorInfinitePart_iff _root_.GlobalClassFieldTheory.GlobalClassFields.ConductorialSubgroup.narrowFiniteConductorRayClassGroupEquivQuotientOfCardEq_mk _root_.GlobalClassFieldTheory.GlobalClassFields.ConductorialSubgroup.narrowFiniteConductorRayClassGroupToQuotient_mk _root_.GlobalClassFieldTheory.GlobalClassFields.bigHilbertClassFieldQuotientCongr_mk _root_.GlobalClassFieldTheory.GlobalClassFields.bigHilbertClassFieldQuotientEquivNarrowClassGroup_mk _root_.GlobalClassFieldTheory.GlobalClassFields.bigHilbertClassFieldQuotientToIdeleClassNormQuotient_mk _root_.GlobalClassFieldTheory.GlobalClassFields.bigHilbertClassFieldQuotientToSmallHilbertClassFieldQuotient_mk _root_.GlobalClassFieldTheory.GlobalClassFields.ideleClassNormQuotientTowerMap_mk _root_.GlobalClassFieldTheory.GlobalClassFields.narrowFiniteConductorRayClassGroupToIdeleClassNormQuotient_mk _root_.GlobalClassFieldTheory.GlobalClassFields.normQuotientEquivOfNarrowFiniteConductorsEqOfRayClassGroupCardsEqNormQuotientCards_mk _root_.GlobalClassFieldTheory.GlobalClassFields.realSignToBigHilbertClassFieldQuotient_apply _root_.GlobalClassFieldTheory.GlobalClassFields.realSignToNarrowClassKernel_apply _root_.GlobalClassFieldTheory.GlobalClassFields.smallHilbertClassFieldQuotientCongr_mk _root_.GlobalClassFieldTheory.GlobalClassFields.smallHilbertClassFieldQuotientEquivClassGroup_mk _root_.GlobalClassFieldTheory.GlobalClassFields.smallHilbertClassFieldQuotientToIdeleClassNormQuotient_mk _root_.GlobalClassFieldTheory.IdealClassFieldTheory.smallHilbertClassFieldIdeleExtensionMap_mk' _root_.GlobalClassFieldTheory.Reciprocity.abstractFixedFieldCyclotomicIdeleClassArtinMonoidHom_mk _root_.GlobalClassFieldTheory.Reciprocity.abstractFixedFieldCyclotomicRestriction_infiniteGlobalArtinMonoidHom _root_.GlobalClassFieldTheory.Reciprocity.globalNormClassFromIdele_principalIdele _root_.GlobalClassFieldTheory.Reciprocity.globalNormClassFromIdele_relativeIdeleNorm_eq_one _root_.GlobalClassFieldTheory.Reciprocity.infiniteGlobalArtinMonoidHom_abstractFixedFieldCyclotomic_principalIdele _root_.GlobalClassFieldTheory.Reciprocity.mem_globalArtinFiniteSupport_iff _root_.GlobalClassFieldTheory.Reciprocity.rationalComplexificationGlobalArtin_principalIdele _root_.IdeleGroup.fractionalIdeal_finitePrimeIdele _root_.IdeleGroup.idealClass_finitePrimeIdele _root_.OAI.PrimeDegreePackets.ThetaConstruction.schwartzCM_apply _root_.RayClass.signToNarrow_mk
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

/-!
# The ideal Artin quotient

For a defining modulus `m`, the ideal-theoretic Artin map is surjective and
has kernel `H_m`.  The first isomorphism theorem therefore identifies
`J_K^m / H_m` with the corresponding idelic norm quotient `C_K / N`.
-/

open scoped NumberField

noncomputable section

namespace GlobalClassFieldTheory
namespace IdealClassFieldTheory

open NumberField

variable {K : Type} [Field K] [NumberField K]

-- Reuse the normality witness embedded in the imported ideal-Artin definitions.
-- Choosing a different generic witness here makes quotient equivalences compare
-- enormous, propositionally equal but non-definitional terms.
attribute [local instance] ideleClassSubgroupNormal

local instance idealArtinKernelNormal
    (m : RayClass.Modulus K)
    (N : Subgroup (IdeleClassGroup K))
    (hm : RayClass.Modulus.congruenceSubgroup m ≤ N) :
    (idealArtinKernel m N hm).Normal := by
  change (idealArtinMap m N hm).ker.Normal
  infer_instance

/-- The ideal class-field isomorphism
`J_K^m / H_m ≃ C_K / N`. -/
noncomputable def idealClassQuotientEquivNormQuotient
    (m : RayClass.Modulus K)
    (N : Subgroup (IdeleClassGroup K))
    (hm : RayClass.Modulus.congruenceSubgroup m ≤ N) :
    RayClass.primeToModulusIdeals m ⧸
        idealArtinKernel m N hm ≃*
      IdeleClassGroup K ⧸ N := by
  have hker :
      idealArtinKernel m N hm =
        (idealArtinMap m N hm).ker :=
    rfl
  exact
    (QuotientGroup.quotientMulEquivOfEq hker).trans
      (QuotientGroup.quotientKerEquivOfSurjective
        (idealArtinMap m N hm)
        (idealArtinMap_surjective m N hm))

/-- The ideal class-field equivalence sends a quotient representative to
its ideal Artin image. -/
@[simp]
theorem idealClassQuotientEquivNormQuotient_mk
    (m : RayClass.Modulus K)
    (N : Subgroup (IdeleClassGroup K))
    (hm : RayClass.Modulus.congruenceSubgroup m ≤ N)
    (a : RayClass.primeToModulusIdeals m) :
    idealClassQuotientEquivNormQuotient m N hm
        (QuotientGroup.mk' (idealArtinKernel m N hm) a) =
      idealArtinMap m N hm a :=
  rfl

section ActualGaloisQuotient

variable
    {L : Type} [Field L] [NumberField L] [Algebra K L]
    [IsAbelianGalois K L]

/-- The ideal class-field isomorphism with the actual Galois group:
`J_K^m / H_m ≃ Gal(L/K)`.

Its first factor is the ideal/idèle norm-quotient comparison, and its
second factor is the genuine global norm-residue equivalence. -/
noncomputable def idealClassQuotientEquivGaloisGroup
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
    (AddEquiv.toMultiplicative
      (Reciprocity.globalNormResidueEquiv K L))

/-- On a representative ideal, the actual ideal class-field
isomorphism evaluates to the genuine Galois-valued ideal Artin map. -/
@[simp]
theorem idealClassQuotientEquivGaloisGroup_mk
    (m : RayClass.Modulus K)
    (hm :
      RayClass.Modulus.congruenceSubgroup m ≤
        (_root_.ideleClassNorm K L).range)
    (a : RayClass.primeToModulusIdeals m) :
    idealClassQuotientEquivGaloisGroup
        (K := K) (L := L) m hm
        (QuotientGroup.mk'
          (idealArtinKernel m
            ((_root_.ideleClassNorm K L).range) hm) a) =
      idealArtinGaloisMap (K := K) (L := L) m hm a :=
  rfl

end ActualGaloisQuotient

end IdealClassFieldTheory
end GlobalClassFieldTheory
end
end

section
-- module Solutions.OAIQ244_DUKE.GlobalClassFieldTheory_IdealClassFieldTheory_SmallHilbertSplitting
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 400000
attribute [-instance] _root_.GlobalClassFieldTheory.GlobalClassFields.ideleClassNorm_rangeFiniteIndex _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.GlobalClassFieldTheory.GlobalClassFields.bigHilbertNormQuotient_finite _root_.GlobalClassFieldTheory.GlobalClassFields.bigHilbertNormSubgroup_finiteIndex
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI
attribute [local instance] OAI.starSubalgebraCommCStarAlgebra

set_option autoImplicit false

/-!
# Splitting in the small Hilbert class field

The small Hilbert class field has reciprocity quotient the ordinary ideal
class group.  Thus the Frobenius class of a finite prime is its ordinary
ideal class, and it is trivial precisely when the prime ideal is principal.
-/

open scoped NumberField

noncomputable section

namespace GlobalClassFieldTheory
namespace IdealClassFieldTheory

open NumberField IsDedekindDomain

/-- Canonical class-group commutativity supplies normality for the quotient. -/
theorem smallHilbertSplittingClassGroupIsMulCommutative
    (F : Type*) [Field F] [NumberField F] :
    IsMulCommutative (IdeleClassGroup F) :=
  IsMulCommutative.of_comm (fun a b => mul_comm a b)

attribute [local instance] smallHilbertSplittingClassGroupIsMulCommutative

end IdealClassFieldTheory
end GlobalClassFieldTheory
end
end

section
-- module Solutions.OAIQ244_DUKE.GlobalClassFieldTheory_GlobalClassFields_HilbertClassFieldPrimeSplitting
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 400000
attribute [-instance] _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI
attribute [local instance] OAI.starSubalgebraCommCStarAlgebra

set_option autoImplicit false

/-!
# Prime splitting for a maximal everywhere-unramified cyclic norm quotient

Suppose a cyclic extension is unramified at every finite and infinite
place and its degree is the ordinary class number.  Its actual
idèle-class norm quotient is then the small-Hilbert reciprocity quotient.
This file transports prime Frobenius classes across that identification
and proves that trivial Frobenius is equivalent to principality of the
prime ideal.
-/

open scoped NumberField

noncomputable section

namespace GlobalClassFieldTheory
namespace GlobalClassFields

open NumberField IsDedekindDomain IdeleGroup

/-- The canonical idèle-class multiplication makes every subgroup normal. -/
theorem hilbertPrimeSplittingClassGroupIsMulCommutative
    (F : Type) [Field F] [NumberField F] :
    IsMulCommutative (IdeleClassGroup F) :=
  IsMulCommutative.of_comm (fun a b => mul_comm a b)

attribute [local instance] hilbertPrimeSplittingClassGroupIsMulCommutative

end GlobalClassFields
end GlobalClassFieldTheory
end
end

section
-- module Solutions.OAIQ244_DUKE.GlobalClassFieldTheory_GlobalClassFields_RayClassPrimeIdele
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 400000
attribute [-instance] _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable
attribute [-simp] _root_.GlobalClassFieldTheory.ClassFieldAxiom.hasseNormDiagonal_mk _root_.GlobalClassFieldTheory.GlobalClassFields.ConductorialSubgroup.mem_fullConductorInfinitePart_iff _root_.GlobalClassFieldTheory.GlobalClassFields.bigHilbertClassFieldQuotientCongr_mk _root_.GlobalClassFieldTheory.GlobalClassFields.ideleClassNormQuotientTowerMap_mk _root_.GlobalClassFieldTheory.GlobalClassFields.normQuotientEquivOfNarrowFiniteConductorsEqOfRayClassGroupCardsEqNormQuotientCards_mk _root_.GlobalClassFieldTheory.GlobalClassFields.smallHilbertClassFieldQuotientCongr_mk _root_.GlobalClassFieldTheory.IdealClassFieldTheory.smallHilbertClassFieldIdeleExtensionMap_mk' _root_.GlobalClassFieldTheory.Reciprocity.abstractFixedFieldCyclotomicIdeleClassArtinMonoidHom_mk _root_.GlobalClassFieldTheory.Reciprocity.abstractFixedFieldCyclotomicRestriction_infiniteGlobalArtinMonoidHom _root_.GlobalClassFieldTheory.Reciprocity.globalNormClassFromIdele_principalIdele _root_.GlobalClassFieldTheory.Reciprocity.globalNormClassFromIdele_relativeIdeleNorm_eq_one _root_.GlobalClassFieldTheory.Reciprocity.infiniteGlobalArtinMonoidHom_abstractFixedFieldCyclotomic_principalIdele _root_.GlobalClassFieldTheory.Reciprocity.mem_globalArtinFiniteSupport_iff _root_.GlobalClassFieldTheory.Reciprocity.rationalComplexificationGlobalArtin_principalIdele _root_.OAI.PrimeDegreePackets.ThetaConstruction.schwartzCM_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI
attribute [local instance] OAI.starSubalgebraCommCStarAlgebra

set_option autoImplicit false

/-!
# Prime idèles and ideal ray classes

A normalized one-place prime idèle is prime to every modulus whose
finite support omits that prime.  Its fractional ideal is the
corresponding prime ideal, so the idelic and ideal-theoretic ray-class
constructions use exactly the same prime representative.
-/

open scoped NumberField

noncomputable section

namespace GlobalClassFieldTheory
namespace GlobalClassFields

open NumberField IsDedekindDomain IdeleGroup

universe u

theorem rayClassPrimeIdeleClassGroupIsMulCommutative
    (F : Type u) [Field F] [NumberField F] :
    IsMulCommutative (IdeleClassGroup F) :=
  IsMulCommutative.of_comm (fun a b => mul_comm a b)

attribute [local instance] rayClassPrimeIdeleClassGroupIsMulCommutative

section GenericPrimeIdele

variable {K : Type u} [Field K] [NumberField K]

/-- A normalized one-place prime idèle is prime to a modulus whenever
the supporting prime does not occur in the modulus. -/
theorem finitePrimeIdele_mem_idelePrimeToModulusSubgroup
    (m : RayClass.Modulus K)
    (v : HeightOneSpectrum (𝓞 K))
    (hv : v ∉ m.finitePart.support) :
    finitePrimeIdele v ∈
      RayClass.idelePrimeToModulusSubgroup m := by
  constructor
  · change
      1 ∈
        m.infiniteCongruenceSubgroup
    exact
      m.infiniteCongruenceSubgroup.one_mem
  · intro w hw
    have hwv : w ≠ v := by
      intro h
      exact hv (h ▸ hw)
    change
      IdeleGroup.finiteComponent w
          (finitePrimeIdele v) ∈
        RayClass.localHigherUnitGroup w (m.finitePart w)
    rw [finitePrimeIdele,
      IdeleGroup.finitePlaceIdele_finiteComponent_of_ne
        v w (FiniteIdeleGroup.chosenLocalOrderSection v 1) hwv]
    exact
      (RayClass.localHigherUnitGroup w (m.finitePart w)).one_mem

/-- The fractional-ideal image of a normalized one-place prime idèle,
viewed as prime to a modulus, is the corresponding prime-to-modulus
prime ideal. -/
@[simp]
theorem primeToIdealMap_finitePrimeIdele
    (m : RayClass.Modulus K)
    (v : HeightOneSpectrum (𝓞 K))
    (hv : v ∉ m.finitePart.support) :
    RayClass.primeToIdealMap m
        ⟨finitePrimeIdele v,
          finitePrimeIdele_mem_idelePrimeToModulusSubgroup
            m v hv⟩ =
      RayClass.primeToModulusIdeal m v hv := by
  apply Subtype.ext
  exact
    fractionalIdeal_finitePrimeIdele v

/-- The ideal-ray projection of a normalized one-place prime idèle is
the ideal ray class of the corresponding prime ideal. -/
@[simp]
theorem idealRayProjection_finitePrimeIdele
    (m : RayClass.Modulus K)
    (v : HeightOneSpectrum (𝓞 K))
    (hv : v ∉ m.finitePart.support) :
    RayClass.idealRayProjection m
        ⟨finitePrimeIdele v,
          finitePrimeIdele_mem_idelePrimeToModulusSubgroup
            m v hv⟩ =
      QuotientGroup.mk'
        (RayClass.principalRayIdealSubgroup m)
        (RayClass.primeToModulusIdeal m v hv) := by
  rw [RayClass.idealRayProjection,
    MonoidHom.comp_apply,
    primeToIdealMap_finitePrimeIdele]

/-- The idèle-class/full-idèle ray-class equivalence evaluates on a
double quotient representative by forgetting the intermediate
principal-idèle quotient. -/
@[simp]
theorem rayClassGroupEquivIdeleQuotient_mk_mk
    (m : RayClass.Modulus K)
    (a : IdeleGroup K) :
    RayClass.rayClassGroupEquivIdeleQuotient m
        (QuotientGroup.mk'
          (RayClass.Modulus.congruenceSubgroup m)
          (QuotientGroup.mk'
            (IdeleGroup.principalSubgroup K) a)) =
      QuotientGroup.mk'
        (RayClass.Modulus.ideleCongruenceSubgroup m ⊔
          IdeleGroup.principalSubgroup K) a := by
  exact
    QuotientGroup.quotientQuotientEquivQuotientAux_mk_mk
      (IdeleGroup.principalSubgroup K)
      (RayClass.Modulus.ideleCongruenceSubgroup m ⊔
        IdeleGroup.principalSubgroup K)
      le_sup_right a

/-- The canonical idelic-to-ideal ray-class equivalence sends a
prime-to-modulus idèle class to the ideal ray class of its fractional
ideal. -/
@[simp]
theorem rayClassGroupEquivIdealRayClassGroup_mk_primeTo
    (m : RayClass.Modulus K)
    (a : RayClass.idelePrimeToModulusSubgroup m) :
    RayClass.rayClassGroupEquivIdealRayClassGroup m
        (QuotientGroup.mk'
          (RayClass.Modulus.congruenceSubgroup m)
          (QuotientGroup.mk'
            (IdeleGroup.principalSubgroup K)
            (a : IdeleGroup K))) =
      RayClass.idealRayProjection m a := by
  change
    RayClass.quotientRaySubgroupEquivIdealRayClassGroup m
        ((RayClass.quotientRaySubgroupEquivIdeleRayQuotient m).symm
          (RayClass.rayClassGroupEquivIdeleQuotient m
            (QuotientGroup.mk'
              (RayClass.Modulus.congruenceSubgroup m)
              (QuotientGroup.mk'
                (IdeleGroup.principalSubgroup K)
                (a : IdeleGroup K))))) =
      RayClass.idealRayProjection m a
  rw [rayClassGroupEquivIdeleQuotient_mk_mk]
  change
    RayClass.quotientRaySubgroupEquivIdealRayClassGroup m
        ((RayClass.quotientRaySubgroupEquivIdeleRayQuotient m).symm
          (RayClass.primeToRayClassProjection m a)) =
      RayClass.idealRayProjection m a
  rw [← RayClass.quotientRaySubgroupEquivIdeleRayQuotient_mk m a,
    MulEquiv.symm_apply_apply,
    RayClass.quotientRaySubgroupEquivIdealRayClassGroup_mk]

end GenericPrimeIdele

variable {K : Type} [Field K] [NumberField K]

/-- The ideal Artin map of the fractional ideal attached to a
prime-to-modulus idèle is its direct class in the idèle-class
quotient.  This is the commuting square between the idelic and
ideal-theoretic ray-class constructions. -/
@[simp]
theorem idealArtinMap_primeToIdealMap
    (m : RayClass.Modulus K)
    (N : Subgroup (IdeleClassGroup K))
    (hm : RayClass.Modulus.congruenceSubgroup m ≤ N)
    (a : RayClass.idelePrimeToModulusSubgroup m) :
    IdealClassFieldTheory.idealArtinMap m N hm
        (RayClass.primeToIdealMap m a) =
      QuotientGroup.mk' N
        (QuotientGroup.mk'
          (IdeleGroup.principalSubgroup K)
          (a : IdeleGroup K)) := by
  let e :=
    RayClass.rayClassGroupEquivIdealRayClassGroup m
  let c : RayClass.RayClassGroup m :=
    QuotientGroup.mk'
      (RayClass.Modulus.congruenceSubgroup m)
      (QuotientGroup.mk'
        (IdeleGroup.principalSubgroup K)
        (a : IdeleGroup K))
  have he :
      e c = RayClass.idealRayProjection m a := by
    exact rayClassGroupEquivIdealRayClassGroup_mk_primeTo m a
  have he' :
      e.symm (RayClass.idealRayProjection m a) = c := by
    rw [← he, e.symm_apply_apply]
  change
    IdealClassFieldTheory.rayClassToNormQuotient m N hm
        (e.symm (RayClass.idealRayProjection m a)) =
      QuotientGroup.mk' N
        (QuotientGroup.mk'
          (IdeleGroup.principalSubgroup K)
          (a : IdeleGroup K))
  rw [he', IdealClassFieldTheory.rayClassToNormQuotient_mk]

end GlobalClassFields
end GlobalClassFieldTheory
end
end

section
-- module Solutions.OAIQ244_DUKE.GlobalClassFieldTheory_GlobalClassFields_ConductorFrobenius
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 400000
attribute [-instance] _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable
attribute [-simp] _root_.GlobalClassFieldTheory.ClassFieldAxiom.hasseNormDiagonal_mk _root_.GlobalClassFieldTheory.GlobalClassFields.ConductorialSubgroup.mem_fullConductorInfinitePart_iff _root_.GlobalClassFieldTheory.GlobalClassFields.bigHilbertClassFieldQuotientCongr_mk _root_.GlobalClassFieldTheory.GlobalClassFields.ideleClassNormQuotientTowerMap_mk _root_.GlobalClassFieldTheory.GlobalClassFields.smallHilbertClassFieldQuotientCongr_mk _root_.GlobalClassFieldTheory.IdealClassFieldTheory.smallHilbertClassFieldIdeleExtensionMap_mk' _root_.GlobalClassFieldTheory.Reciprocity.abstractFixedFieldCyclotomicIdeleClassArtinMonoidHom_mk _root_.GlobalClassFieldTheory.Reciprocity.abstractFixedFieldCyclotomicRestriction_infiniteGlobalArtinMonoidHom _root_.GlobalClassFieldTheory.Reciprocity.globalNormClassFromIdele_principalIdele _root_.GlobalClassFieldTheory.Reciprocity.globalNormClassFromIdele_relativeIdeleNorm_eq_one _root_.GlobalClassFieldTheory.Reciprocity.infiniteGlobalArtinMonoidHom_abstractFixedFieldCyclotomic_principalIdele _root_.GlobalClassFieldTheory.Reciprocity.mem_globalArtinFiniteSupport_iff _root_.GlobalClassFieldTheory.Reciprocity.rationalComplexificationGlobalArtin_principalIdele _root_.OAI.PrimeDegreePackets.ThetaConstruction.schwartzCM_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

/-!
# Prime classes at the narrow finite norm conductor

The one-place idèle of normalized order one defines two compatible
prime classes: one in the ray class group at the exact narrow finite norm
conductor, and one in the actual idele-class norm quotient.  The
canonical narrow-finite-conductor ray-class map sends the former to the latter.

For cyclic extensions the order of the norm-quotient class divides the
extension degree.  Complete splitting forces this class to be trivial;
when the narrow-finite-conductor ray-class presentation is maximal, it also
forces the narrow finite conductor ray prime class itself to be trivial.
-/

open scoped NumberField

noncomputable section

namespace GlobalClassFieldTheory
namespace GlobalClassFields

open NumberField IsDedekindDomain IdeleGroup

variable
    {K L : Type}
    [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]

-- Reuse the normality witness embedded in the imported ideal-Artin maps.
-- Without it, every occurrence of the norm quotient repeats an expensive
-- unsuccessful instance search and builds a non-definitional witness.
attribute [local instance]
  IdealClassFieldTheory.ideleClassSubgroupNormal

/-- The class of the normalized one-place prime idèle in the ray class
group at the exact narrow finite conductor of the actual norm subgroup. -/
def narrowFiniteConductorRayPrimeClass
    (v : HeightOneSpectrum (𝓞 K)) :
    RayClass.RayClassGroup
      (RayClass.Modulus.narrowOfFinite
        (ideleClassNormNarrowFiniteConductor (K := K) (L := L))) :=
  QuotientGroup.mk'
    (RayClass.Modulus.congruenceSubgroup
      (RayClass.Modulus.narrowOfFinite
        (ideleClassNormNarrowFiniteConductor (K := K) (L := L))))
    (QuotientGroup.mk'
      (IdeleGroup.principalSubgroup K)
      (finitePrimeIdele v))

/-- The class of the normalized one-place prime idèle in the actual
idele-class norm quotient. -/
def ideleClassNormFrobeniusClass
    (v : HeightOneSpectrum (𝓞 K)) :
    IdeleClassGroup K ⧸
      (_root_.ideleClassNorm K L).range :=
  QuotientGroup.mk'
    ((_root_.ideleClassNorm K L).range)
    (QuotientGroup.mk'
      (IdeleGroup.principalSubgroup K)
      (finitePrimeIdele v))

/-- The canonical narrow-finite-conductor ray-class map sends the narrow
finite conductor ray prime class to the corresponding actual norm-quotient
Frobenius class. -/
@[simp]
theorem
    narrowFiniteConductorRayClassGroupToIdeleClassNormQuotient_rayPrimeClass
    (v : HeightOneSpectrum (𝓞 K)) :
    narrowFiniteConductorRayClassGroupToIdeleClassNormQuotient
        (K := K) (L := L)
        (narrowFiniteConductorRayPrimeClass
          (K := K) (L := L) v) =
      ideleClassNormFrobeniusClass
        (K := K) (L := L) v :=
  rfl

end GlobalClassFields
end GlobalClassFieldTheory
end
end

section
-- module Solutions.OAIQ244_DUKE.GlobalClassFieldTheory_GlobalClassFields_OrdinaryNormClassField
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 400000
attribute [-instance] _root_.GlobalClassFieldTheory.Reciprocity.abstractFixedFieldCyclotomicCompositum_algebra _root_.GlobalClassFieldTheory.Reciprocity.abstractFixedFieldCyclotomicCompositum_baseScalarTower _root_.GlobalClassFieldTheory.Reciprocity.abstractFixedFieldCyclotomicCompositum_scalarTower _root_.GlobalClassFieldTheory.Reciprocity.abstractFixedFieldCyclotomicFiniteCompositum_baseAlgebra _root_.GlobalClassFieldTheory.Reciprocity.abstractFixedFieldCyclotomicFiniteCompositum_baseScalarTower _root_.GlobalClassFieldTheory.Reciprocity.abstractFixedFieldCyclotomicFiniteGaloisLayer_scalarTower _root_.GlobalClassFieldTheory.Reciprocity.abstractFixedFieldCyclotomicFiniteLayer_baseAlgebra _root_.GlobalClassFieldTheory.Reciprocity.abstractFixedFieldCyclotomicFiniteLayer_baseModule _root_.GlobalClassFieldTheory.Reciprocity.abstractFixedFieldCyclotomicFiniteLayer_baseSMul _root_.GlobalClassFieldTheory.Reciprocity.abstractFixedFieldCyclotomicFiniteLayer_baseScalarTower _root_.GlobalClassFieldTheory.Reciprocity.abstractFixedFieldCyclotomicFiniteLayer_finiteDimensional _root_.GlobalClassFieldTheory.Reciprocity.abstractFixedFieldCyclotomicFiniteLayer_isAbelianGalois _root_.GlobalClassFieldTheory.Reciprocity.abstractFixedFieldCyclotomicFiniteLayer_layerAlgebra _root_.GlobalClassFieldTheory.Reciprocity.abstractFixedFieldCyclotomicFiniteLayer_layerSMul _root_.GlobalClassFieldTheory.Reciprocity.abstractFixedFieldCyclotomicFiniteLayer_layerScalarTower _root_.GlobalClassFieldTheory.Reciprocity.abstractFixedFieldCyclotomicFiniteLayer_numberField _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.boundedRealFields_finite _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.GlobalClassFieldTheory.GlobalClassFields.bigHilbertNormQuotient_finite _root_.GlobalClassFieldTheory.GlobalClassFields.narrowClassGroup_finite
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

variable
    (K L : Type) [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]

/- The fixed-field typeclass data used by the topology comparison are kept
behind named constants.  This prevents every consumer from rebuilding the
same finite-dimensional and number-field proof terms while reducing the
dependent fixed-field type. -/
omit [FiniteDimensional K L] [IsGalois K L] in
theorem numberFieldTowerFixedBaseFiniteDimensionalPackage :
    FiniteDimensional ℚ
      (abstractFixedField ℚ (SeparableClosure ℚ)
        (numberFieldTowerBaseSubgroup K L)) :=
  abstractFixedField_finiteDimensional
    ℚ (SeparableClosure ℚ)
    (numberFieldTowerBaseSubgroup K L)
    (numberFieldTowerBaseSubgroupAbsoluteQuotientFinite K L)

omit [FiniteDimensional K L] [IsGalois K L] in
theorem numberFieldTowerFixedBaseNumberFieldPackage :
    NumberField
      (abstractFixedField ℚ (SeparableClosure ℚ)
        (numberFieldTowerBaseSubgroup K L)) := by
  let hFiniteDimensional : FiniteDimensional ℚ
      (abstractFixedField ℚ (SeparableClosure ℚ)
        (numberFieldTowerBaseSubgroup K L)) :=
    numberFieldTowerFixedBaseFiniteDimensionalPackage K L
  exact
    NumberField.of_module_finite ℚ
      (abstractFixedField ℚ (SeparableClosure ℚ)
        (numberFieldTowerBaseSubgroup K L))

/-- The canonical fixed-field copy of the base used by every ordinary
norm-neighbourhood realization in the ambient extension `L / K`. -/
noncomputable abbrev ordinaryNormClassFieldBase : Type :=
  abstractFixedField ℚ (SeparableClosure ℚ)
    (numberFieldTowerBaseSubgroup K L)

omit [FiniteDimensional K L] [IsGalois K L] in
noncomputable instance ordinaryNormClassFieldBaseFiniteDimensional :
    FiniteDimensional ℚ (ordinaryNormClassFieldBase K L) :=
  numberFieldTowerFixedBaseFiniteDimensionalPackage K L

omit [FiniteDimensional K L] [IsGalois K L] in
noncomputable instance ordinaryNormClassFieldBaseNumberField :
    NumberField (ordinaryNormClassFieldBase K L) :=
  numberFieldTowerFixedBaseNumberFieldPackage K L

/-- The canonical equivalence from the original base to the selected
fixed-field base. -/
noncomputable abbrev ordinaryNormClassFieldBaseEquiv :
    K ≃ₐ[ℚ] ordinaryNormClassFieldBase K L :=
  numberFieldTowerAbstractBaseFieldEquiv K L

end GlobalClassFields
end GlobalClassFieldTheory
end
end

section
-- module Solutions.OAIQ244_DUKE.GlobalClassFieldTheory_Reciprocity_ComplexificationArtin_OverextensionArtin
attribute [-instance] _root_.GlobalClassFieldTheory.GlobalClassFields.ConductorialSubgroup.finiteIndex _root_.GlobalClassFieldTheory.GlobalClassFields.bigHilbertClassFieldNormSubgroup_normal _root_.GlobalClassFieldTheory.GlobalClassFields.ideleClassNorm_rangeFiniteIndex _root_.GlobalClassFieldTheory.GlobalClassFields.smallHilbertClassFieldNormSubgroupFiniteIndex _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.GlobalClassFieldTheory.GlobalClassFields.bigHilbertNormQuotient_finite _root_.GlobalClassFieldTheory.GlobalClassFields.bigHilbertNormSubgroup_finiteIndex
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
    ramifiedInfinitePlaceOverextensionIdeleClassGroupIsMulCommutative
    {F : Type} [Field F] [NumberField F] :
    IsMulCommutative (IdeleClassGroup F) :=
  ⟨⟨fun a b => mul_comm a b⟩⟩

end

end ComplexConjugationOverextension

end Reciprocity
end GlobalClassFieldTheory
end
end

section
-- module Solutions.OAIQ244_DUKE.GlobalClassFieldTheory_Reciprocity_CyclotomicAbstractFixedFieldArtin
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.GlobalClassFields.ConductorialSubgroup.finiteIndex _root_.GlobalClassFieldTheory.GlobalClassFields.bigHilbertClassFieldNormSubgroup_normal _root_.GlobalClassFieldTheory.GlobalClassFields.finiteAbelianSubextensionAbstractRelativeFixedFieldFiniteDimensional _root_.GlobalClassFieldTheory.GlobalClassFields.finiteAbelianSubextensionAbstractRelativeFixedFieldIsAbelianGalois _root_.GlobalClassFieldTheory.GlobalClassFields.ideleClassNorm_rangeFiniteIndex _root_.GlobalClassFieldTheory.GlobalClassFields.ordinaryNormClassFieldBaseFiniteDimensional _root_.GlobalClassFieldTheory.GlobalClassFields.ordinaryNormClassFieldBaseNumberField _root_.GlobalClassFieldTheory.GlobalClassFields.smallHilbertClassFieldNormSubgroupFiniteIndex _root_.GlobalClassFieldTheory.Reciprocity.complexFourthRootField_numberField _root_.GlobalClassFieldTheory.Reciprocity.infinitePlaceComplexificationOverfield_numberField _root_.GlobalClassFieldTheory.Reciprocity.numberFieldTowerBaseFieldAlgebra _root_.GlobalClassFieldTheory.Reciprocity.numberFieldTowerBaseFieldScalarTower _root_.GlobalClassFieldTheory.Reciprocity.numberFieldTowerBaseField_finiteDimensional _root_.GlobalClassFieldTheory.Reciprocity.numberFieldTowerBaseField_numberField _root_.GlobalClassFieldTheory.Reciprocity.numberFieldTowerBaseSubgroupAbsoluteQuotientFinite _root_.GlobalClassFieldTheory.Reciprocity.numberFieldTowerExtensionQuotientFinite _root_.GlobalClassFieldTheory.Reciprocity.numberFieldTowerExtensionSubgroupNormal _root_.GlobalClassFieldTheory.Reciprocity.numberFieldTowerTopField_isGalois _root_.GlobalClassFieldTheory.Reciprocity.ramifiedInfinitePlaceRealFixedField_numberField _root_.GlobalClassFieldTheory.Reciprocity.rationalComplexification_infinitePlaceOverfield_algebra _root_.KummerTheory.primeCyclotomicBaseIsGalois _root_.KummerTheory.primeCyclotomicBaseNumberField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.boundedRealFields_numberField _root_.OAI.PrimeDegreePackets.instTopologicalSpaceLocalAlgebra _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.GlobalClassFieldTheory.GlobalClassFields.bigHilbertNormQuotient_finite _root_.GlobalClassFieldTheory.GlobalClassFields.bigHilbertNormSubgroup_finiteIndex _root_.GlobalClassFieldTheory.Reciprocity.rationalOrdinaryNormQuotientAdditiveTypeAddCommGroup
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
attribute [local instance] GlobalClassFieldTheory.Reciprocity.cyclotomicAbstractFixedFieldArtin_cyclotomicZHatFieldNormal
attribute [local instance] GlobalClassFieldTheory.Reciprocity.abstractFixedFieldCyclotomic_numberField
/-- Representative form of the actual cyclotomic Artin-coordinate
identity after descent of the normalized value to the idele class
group. -/
theorem
    abstractFixedFieldCyclotomicGalEquivZHat_infiniteGlobalArtinMonoidHom_mk
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
    Multiplicative.toAdd
        (abstractFixedFieldCyclotomicGalEquivZHat H
          (infiniteGlobalArtinMonoidHom F U a)) =
      normalizedCyclotomicZHatIdeleClassValueContinuous F
        (Additive.ofMul
          (QuotientGroup.mk'
            (IdeleGroup.principalSubgroup F) a)) := by
  have hSeparableClosureAlgebra :
      cyclotomicAbstractFixedFieldArtin_separableClosureAlgebra =
        rationalSeparableClosureAlgebra :=
    Subsingleton.elim _ _
  cases hSeparableClosureAlgebra
  let F :=
    LocalClassFieldTheory.abstractFixedField
      ℚ (SeparableClosure ℚ) H.field
  let hI :=
    rationalCyclotomicFieldInertia_le H.field
  let U :=
    LocalClassFieldTheory.abstractRelativeFixedField
      ℚ (SeparableClosure ℚ) hI
  let : IsAbelianGalois F U :=
    abstractFixedFieldCyclotomic_isAbelianGalois H
  calc
    Multiplicative.toAdd
        (abstractFixedFieldCyclotomicGalEquivZHat H
          (infiniteGlobalArtinMonoidHom F U a)) =
        normalizedCyclotomicZHatIdeleValue F
          (Additive.ofMul a) :=
      abstractFixedFieldCyclotomicGalEquivZHat_infiniteGlobalArtinMonoidHom
        H a
    _ =
        normalizedCyclotomicZHatIdeleClassValueContinuous F
          (Additive.ofMul
            (QuotientGroup.mk'
              (IdeleGroup.principalSubgroup F) a)) :=
      (normalizedCyclotomicZHatIdeleClassValueContinuous_mk
        (K := F) a).symm

/-- The descended genuine maximal-unramified Artin map is precisely
the normalized cyclotomic idele-class value in the actual Galois
coordinate. -/
theorem
    abstractFixedFieldCyclotomicGalEquivZHat_ideleClassArtinMonoidHom
    (H : FiniteAbstractField
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
    (c :
      IdeleClassGroup
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
    abstractFixedFieldCyclotomicGalEquivZHat H
        (abstractFixedFieldCyclotomicIdeleClassArtinMonoidHom H c) =
      normalizedCyclotomicZHatIdeleClassValueContinuousMul F c := by
  let F :=
    LocalClassFieldTheory.abstractFixedField
      ℚ (SeparableClosure ℚ) H.field
  let : FiniteDimensional ℚ F :=
    LocalClassFieldTheory.abstractFixedField_finiteDimensional
      ℚ (SeparableClosure ℚ) H.field H.finite
  let : NumberField F :=
    NumberField.of_module_finite ℚ F
  have hSeparableClosureAlgebra :
      cyclotomicAbstractFixedFieldArtin_separableClosureAlgebra =
        rationalSeparableClosureAlgebra :=
    Subsingleton.elim _ _
  cases hSeparableClosureAlgebra
  refine Quotient.inductionOn' c ?_
  intro a
  let hI :=
    rationalCyclotomicFieldInertia_le H.field
  let U :=
    LocalClassFieldTheory.abstractRelativeFixedField
      ℚ (SeparableClosure ℚ) hI
  let : IsAbelianGalois F U :=
    abstractFixedFieldCyclotomic_isAbelianGalois H
  calc
    abstractFixedFieldCyclotomicGalEquivZHat H
        (abstractFixedFieldCyclotomicIdeleClassArtinMonoidHom H
          (QuotientGroup.mk'
            (IdeleGroup.principalSubgroup F) a)) =
        abstractFixedFieldCyclotomicGalEquivZHat H
          (infiniteGlobalArtinMonoidHom F U a) :=
      congrArg (abstractFixedFieldCyclotomicGalEquivZHat H)
        (abstractFixedFieldCyclotomicIdeleClassArtinMonoidHom_mk H a)
    _ =
        normalizedCyclotomicZHatIdeleClassValueContinuousMul F
          (QuotientGroup.mk'
            (IdeleGroup.principalSubgroup F) a) := by
      apply Multiplicative.ext
      exact
        abstractFixedFieldCyclotomicGalEquivZHat_infiniteGlobalArtinMonoidHom_mk
          H a

/-- The genuine chosen-local-factor Artin map to the cyclotomic
maximal-unramified extension is the abstract maximal-unramified
norm-residue symbol.  Both sides are characterized here by their
common normalized valuation coordinate, so no finite reciprocity
comparison is assumed. -/
theorem
    abstractFixedFieldCyclotomicIdeleClassArtin_eq_maximalUnramifiedNormResidue
    (H : FiniteAbstractField
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
    (a :
      ambientFixedAddSubgroup
        rationalIdeleClassRepresentation H.field) :
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
    abstractFixedFieldCyclotomicIdeleClassArtinMonoidHom H
        (Additive.toMul
          ((rationalAbstractFixedFieldIdeleClassEquivFixed H.field
              (hfinite := H.finite)).symm
            a)) =
      LocalClassFieldTheory.abstractExtensionQuotientEquivGaloisGroup
        ℚ (SeparableClosure ℚ) H.field
        (rationalCyclotomicDegreeData.fieldInertia H.field)
        hI hnormal
        (qInertia.symm
          (ValuationData.maximalUnramifiedNormResidueSymbol
            rationalCyclotomicIdeleClassValuationData H a).toMul) := by
  let F :=
    LocalClassFieldTheory.abstractFixedField
      ℚ (SeparableClosure ℚ) H.field
  let : FiniteDimensional ℚ F :=
    LocalClassFieldTheory.abstractFixedField_finiteDimensional
      ℚ (SeparableClosure ℚ) H.field H.finite
  let : NumberField F :=
    NumberField.of_module_finite ℚ F
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
  let c : IdeleClassGroup F :=
    Additive.toMul
      ((rationalAbstractFixedFieldIdeleClassEquivFixed H.field
          (hfinite := H.finite)).symm a)
  have hvaluation :
      ((rationalCyclotomicIdeleClassValuationData.valuationAt H a :
          rationalCyclotomicIdeleClassValuationData.valueGroup) : ZHat) =
        normalizedCyclotomicZHatIdeleClassValueContinuous F
          (Additive.ofMul c) := by
    have h :=
      (rationalCyclotomicIdeleClassValuationData_valuationAt_fixed_apply
        H
        ((rationalAbstractFixedFieldIdeleClassEquivFixed H.field
          (hfinite := H.finite)).symm a))
    rw [(rationalAbstractFixedFieldIdeleClassEquivFixed H.field
        (hfinite := H.finite)).apply_symm_apply] at h
    exact h
  have hleft :
      Multiplicative.toAdd
        (abstractFixedFieldCyclotomicGalEquivZHat H
          (abstractFixedFieldCyclotomicIdeleClassArtinMonoidHom H c)) =
        normalizedCyclotomicZHatIdeleClassValueContinuous F
          (Additive.ofMul c) :=
    congrArg Multiplicative.toAdd
      (abstractFixedFieldCyclotomicGalEquivZHat_ideleClassArtinMonoidHom H c)
  have hright :
      ((rationalCyclotomicIdeleClassValuationData.valuationAt H a :
          rationalCyclotomicIdeleClassValuationData.valueGroup) : ZHat) =
        Multiplicative.toAdd
          (abstractFixedFieldCyclotomicGalEquivZHat H
            (LocalClassFieldTheory.abstractExtensionQuotientEquivGaloisGroup
              ℚ (SeparableClosure ℚ) H.field
              (rationalCyclotomicDegreeData.fieldInertia H.field)
              hI hnormal
              (qInertia.symm
                (ValuationData.maximalUnramifiedNormResidueSymbol
                  rationalCyclotomicIdeleClassValuationData H a).toMul))) := by
    rw [abstractFixedFieldCyclotomicGalEquivZHat_quotientClass]
    exact
      (ValuationData.maximalUnramifiedNormResidue_degree
        rationalCyclotomicIdeleClassValuationData H a).symm
  apply (abstractFixedFieldCyclotomicGalEquivZHat H).injective
  apply Multiplicative.ext
  exact hleft.trans (hvaluation.symm.trans hright)

end Reciprocity
end GlobalClassFieldTheory
end
end

section
-- module Solutions.OAIQ244_DUKE.GlobalClassFieldTheory_Reciprocity_LocalGlobalArtinCompatibility_SeparableClosurePadicLift
attribute [-instance] _root_.GlobalClassFieldTheory.GlobalClassFields.finiteAbelianSubextensionAbstractRelativeFixedFieldFiniteDimensional _root_.GlobalClassFieldTheory.GlobalClassFields.ordinaryNormClassFieldBaseFiniteDimensional _root_.GlobalClassFieldTheory.GlobalClassFields.ordinaryNormClassFieldBaseNumberField _root_.GlobalClassFieldTheory.Reciprocity.abstractFixedFieldCyclotomicCompositum_algebra _root_.GlobalClassFieldTheory.Reciprocity.abstractFixedFieldCyclotomicCompositum_scalarTower _root_.GlobalClassFieldTheory.Reciprocity.abstractFixedFieldCyclotomicFiniteCompositum_baseAlgebra _root_.GlobalClassFieldTheory.Reciprocity.abstractFixedFieldCyclotomicFiniteCompositum_baseScalarTower _root_.GlobalClassFieldTheory.Reciprocity.abstractFixedFieldCyclotomicFiniteCompositum_finiteDimensional _root_.GlobalClassFieldTheory.Reciprocity.abstractFixedFieldCyclotomicFiniteCompositum_numberField _root_.GlobalClassFieldTheory.Reciprocity.abstractFixedFieldCyclotomicFiniteGaloisLayer_scalarTower _root_.GlobalClassFieldTheory.Reciprocity.abstractFixedFieldCyclotomicFiniteLayer_baseAlgebra _root_.GlobalClassFieldTheory.Reciprocity.abstractFixedFieldCyclotomicFiniteLayer_baseModule _root_.GlobalClassFieldTheory.Reciprocity.abstractFixedFieldCyclotomicFiniteLayer_baseSMul _root_.GlobalClassFieldTheory.Reciprocity.abstractFixedFieldCyclotomicFiniteLayer_baseScalarTower _root_.GlobalClassFieldTheory.Reciprocity.abstractFixedFieldCyclotomicFiniteLayer_finiteDimensional _root_.GlobalClassFieldTheory.Reciprocity.abstractFixedFieldCyclotomicFiniteLayer_isAbelianGalois _root_.GlobalClassFieldTheory.Reciprocity.abstractFixedFieldCyclotomicFiniteLayer_layerAlgebra _root_.GlobalClassFieldTheory.Reciprocity.abstractFixedFieldCyclotomicFiniteLayer_layerSMul _root_.GlobalClassFieldTheory.Reciprocity.abstractFixedFieldCyclotomicFiniteLayer_layerScalarTower _root_.GlobalClassFieldTheory.Reciprocity.abstractFixedFieldCyclotomicFiniteLayer_numberField _root_.GlobalClassFieldTheory.Reciprocity.infinitePlaceComplexificationOverfield_algebra _root_.GlobalClassFieldTheory.Reciprocity.infinitePlaceComplexificationOverfield_baseAlgebra _root_.GlobalClassFieldTheory.Reciprocity.infinitePlaceComplexificationOverfield_baseSmul _root_.GlobalClassFieldTheory.Reciprocity.infinitePlaceComplexificationOverfield_smul _root_.GlobalClassFieldTheory.Reciprocity.ramifiedInfinitePlaceRealFixedField_algebra _root_.GlobalClassFieldTheory.Reciprocity.ramifiedInfinitePlaceRealFixedField_ratScalarTower _root_.GlobalClassFieldTheory.Reciprocity.rationalComplexification_infinitePlaceOverfield_algebra _root_.GlobalClassFieldTheory.Reciprocity.rationalComplexification_infinitePlaceOverfield_smul _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.instIsTopologicalRingLocalAlgebra _root_.OAI.PrimeDegreePackets.instTopologicalSpaceLocalAlgebra _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.labelPrime_fact _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable
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
/-- Evaluation of the compatible finite quotient on an arbitrary
ambient representative is the action of that representative on the
chosen embedded copy of the top field. -/
theorem numberFieldTowerExtensionQuotientEquivGaloisGroup_mk_apply
    (τ : (numberFieldTowerBaseSubgroup K L).toSubgroup)
    (x : L) :
    numberFieldSeparableClosureEmbedding L
        (numberFieldTowerExtensionQuotientEquivGaloisGroup K L
          ((numberFieldTowerFiniteGaloisSubextension K L).extensionQuotientMk
            τ) x) =
      τ.1 (numberFieldSeparableClosureEmbedding L x) := by
  let : Algebra K (SeparableClosure ℚ) :=
    numberFieldTowerSeparableClosureBaseAlgebra K L
  let : Algebra L (SeparableClosure ℚ) :=
    numberFieldTowerSeparableClosureTopAlgebra L
  let : IsScalarTower K L (SeparableClosure ℚ) :=
    numberFieldTowerSeparableClosureScalarTower K L
  let : IsScalarTower ℚ K (SeparableClosure ℚ) :=
    numberFieldTowerSeparableClosureBaseScalarTower K L
  let j :=
    numberFieldSeparableClosureEmbedding L
  let e :=
    numberFieldTowerSeparableClosureEquiv K L
  let quotientNormal := numberFieldTowerExtensionSubgroup_normal K L
  convert
    (LocalClassFieldTheory.ambientEmbeddedExtensionQuotientEquivGaloisGroup_mk_apply
      ℚ K L j e τ x) using 1 <;> rfl

attribute [local instance] GlobalClassFieldTheory.Reciprocity.automorphismCyclicFixedFieldNumberField
/-- Restriction of the compatible separable-closure decomposition
group to the actual rational cyclotomic `ZHat`-field. -/
noncomputable def finitePlaceSeparableClosureCyclotomicRestriction
    (v : HeightOneSpectrum (𝓞 K)) :
    letI : Algebra K (SeparableClosure ℚ) :=
      numberFieldTowerSeparableClosureBaseAlgebra K L
    letI : Algebra L (SeparableClosure ℚ) :=
      numberFieldTowerSeparableClosureTopAlgebra L
    letI : IsScalarTower K L (SeparableClosure ℚ) :=
      numberFieldTowerSeparableClosureScalarTower K L
    letI : IsScalarTower ℚ K (SeparableClosure ℚ) :=
      numberFieldTowerSeparableClosureBaseScalarTower K L
    let wΩ :=
      numberFieldTowerFinitePlaceExtensionToSeparableClosure
        K L v (chosenFinitePlaceExtension (L := L) v)
    absoluteValueDecompositionGroup K wΩ.1 →*
      Gal(rationalCyclotomicZHatField / ℚ) :=
  by
    letI : Algebra K (SeparableClosure ℚ) :=
      numberFieldTowerSeparableClosureBaseAlgebra K L
    letI : Algebra L (SeparableClosure ℚ) :=
      numberFieldTowerSeparableClosureTopAlgebra L
    letI : IsScalarTower K L (SeparableClosure ℚ) :=
      numberFieldTowerSeparableClosureScalarTower K L
    letI : IsScalarTower ℚ K (SeparableClosure ℚ) :=
      numberFieldTowerSeparableClosureBaseScalarTower K L
    letI : Normal ℚ rationalCyclotomicZHatField :=
      rationalCyclotomicZHatField_normal
    exact
      (AlgEquiv.restrictNormalHom
          rationalCyclotomicZHatField).comp
        ((AlgEquiv.restrictScalarsHom ℚ).comp
          (absoluteValueDecompositionGroup K
            (numberFieldTowerFinitePlaceExtensionToSeparableClosure
              K L v
                (chosenFinitePlaceExtension (L := L) v)).1).subtype)

/-- The genuine `p`-adic cyclotomic degree on the compatible
separable-closure decomposition group. -/
noncomputable def finitePlaceSeparableClosurePadicCyclotomicDegree
    (v : HeightOneSpectrum (𝓞 K))
    (p : Nat.Primes) :
    letI : Algebra K (SeparableClosure ℚ) :=
      numberFieldTowerSeparableClosureBaseAlgebra K L
    letI : Algebra L (SeparableClosure ℚ) :=
      numberFieldTowerSeparableClosureTopAlgebra L
    letI : IsScalarTower K L (SeparableClosure ℚ) :=
      numberFieldTowerSeparableClosureScalarTower K L
    letI : IsScalarTower ℚ K (SeparableClosure ℚ) :=
      numberFieldTowerSeparableClosureBaseScalarTower K L
    let wΩ :=
      numberFieldTowerFinitePlaceExtensionToSeparableClosure
        K L v (chosenFinitePlaceExtension (L := L) v)
    absoluteValueDecompositionGroup K wΩ.1 →*
      Multiplicative ℤ_[p.1] :=
  by
    letI : Algebra K (SeparableClosure ℚ) :=
      numberFieldTowerSeparableClosureBaseAlgebra K L
    letI : Algebra L (SeparableClosure ℚ) :=
      numberFieldTowerSeparableClosureTopAlgebra L
    letI : IsScalarTower K L (SeparableClosure ℚ) :=
      numberFieldTowerSeparableClosureScalarTower K L
    letI : IsScalarTower ℚ K (SeparableClosure ℚ) :=
      numberFieldTowerSeparableClosureBaseScalarTower K L
    exact
      (rationalCyclotomicPadicCoordinate p).toMonoidHom.comp
        (finitePlaceSeparableClosureCyclotomicRestriction
          (K := K) (L := L) v)

omit [FiniteDimensional K L] in
/-- Restricting first to the top cyclotomic compositum gives the same
`p`-adic degree as restricting directly from the common separable
closure to the rational cyclotomic field. -/
theorem
    finitePlaceSeparableClosureTopCyclotomicRestriction_padicDegree
    (v : HeightOneSpectrum (𝓞 K))
    (p : Nat.Primes) :
    letI : Algebra K (SeparableClosure ℚ) :=
      numberFieldTowerSeparableClosureBaseAlgebra K L
    letI : Algebra L (SeparableClosure ℚ) :=
      numberFieldTowerSeparableClosureTopAlgebra L
    letI : IsScalarTower K L (SeparableClosure ℚ) :=
      numberFieldTowerSeparableClosureScalarTower K L
    letI : IsScalarTower ℚ K (SeparableClosure ℚ) :=
      numberFieldTowerSeparableClosureBaseScalarTower K L
    letI : IsScalarTower L
        (numberFieldCyclotomicZHatCompositum L)
        (SeparableClosure ℚ) :=
      numberFieldCyclotomicZHatCompositumSeparableClosureScalarTower L
    (finitePlaceSeparableClosurePadicCyclotomicDegree
        (K := K) (L := L) v p).comp
        (finitePlaceSeparableClosureTopDecompositionInclusion
          (K := K) (L := L) v) =
      (numberFieldCyclotomicPadicDecompositionCoordinate L
        (finitePlaceCyclotomicCompositumExtension
          (K := K) (L := L) v).1 p).toMonoidHom.comp
        (finitePlaceSeparableClosureTopCyclotomicRestriction
          (K := K) (L := L) v) := by
  let : Algebra K (SeparableClosure ℚ) :=
    numberFieldTowerSeparableClosureBaseAlgebra K L
  let : Algebra L (SeparableClosure ℚ) :=
    numberFieldTowerSeparableClosureTopAlgebra L
  let : IsScalarTower K L (SeparableClosure ℚ) :=
    numberFieldTowerSeparableClosureScalarTower K L
  let : IsScalarTower ℚ K (SeparableClosure ℚ) :=
    numberFieldTowerSeparableClosureBaseScalarTower K L
  let : IsScalarTower L
      (numberFieldCyclotomicZHatCompositum L)
      (SeparableClosure ℚ) :=
    numberFieldCyclotomicZHatCompositumSeparableClosureScalarTower L
  let C :=
    numberFieldCyclotomicZHatCompositum L
  let T :=
    rationalCyclotomicZHatField
  let : Algebra T C :=
    rationalCyclotomicZHatCompositum_algebra L
  let : IsScalarTower ℚ T C :=
    rationalCyclotomicZHatCompositum_scalarTower L
  let : Normal ℚ T :=
    rationalCyclotomicZHatField_normal
  let : Normal L C :=
    IsGalois.to_normal
  apply MonoidHom.ext
  intro τ
  apply congrArg (rationalCyclotomicPadicCoordinate p)
  apply AlgEquiv.ext
  intro x
  let τK : SeparableClosure ℚ ≃ₐ[K] SeparableClosure ℚ :=
    RamificationTheory.HilbertRamification.ValuationSubring.restrictAutomorphismScalars
      (K := K) (M := L) τ.1
  let τQ : SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ :=
    τK.restrictScalars ℚ
  let τC : C ≃ₐ[L] C :=
    AlgEquiv.restrictNormalHom C τ.1
  change
    AlgEquiv.restrictNormalHom T τQ x =
      numberFieldCyclotomicZHatCompositumRestriction L τC x
  have hTC (z : T) :
      algebraMap C (SeparableClosure ℚ) (algebraMap T C z) =
        algebraMap T (SeparableClosure ℚ) z := by
    rfl
  have hC :
      algebraMap T C
          (numberFieldCyclotomicZHatCompositumRestriction L τC x) =
        τC (algebraMap T C x) := by
    change
      algebraMap T C
          ((AlgEquiv.restrictNormal
            (MulSemiringAction.toAlgEquiv ℚ C τC) T) x) =
        (MulSemiringAction.toAlgEquiv ℚ C τC)
          (algebraMap T C x)
    exact
      AlgEquiv.restrictNormal_commutes
        (MulSemiringAction.toAlgEquiv ℚ C τC) T x
  have hΩC :
      algebraMap C (SeparableClosure ℚ) (τC (algebraMap T C x)) =
        τ.1
          (algebraMap C (SeparableClosure ℚ)
            (algebraMap T C x)) := by
    exact
      AlgEquiv.restrictNormal_commutes τ.1 C
        (algebraMap T C x)
  apply (algebraMap T (SeparableClosure ℚ)).injective
  calc
    algebraMap T (SeparableClosure ℚ)
          (AlgEquiv.restrictNormalHom T τQ x) =
        τQ (algebraMap T (SeparableClosure ℚ) x) :=
      AlgEquiv.restrictNormal_commutes τQ T x
    _ = τ.1 (algebraMap T (SeparableClosure ℚ) x) := rfl
    _ = τ.1
          (algebraMap C (SeparableClosure ℚ)
            (algebraMap T C x)) :=
      congrArg τ.1 (hTC x).symm
    _ = algebraMap C (SeparableClosure ℚ)
          (τC (algebraMap T C x)) := hΩC.symm
    _ = algebraMap C (SeparableClosure ℚ)
          (algebraMap T C
            (numberFieldCyclotomicZHatCompositumRestriction L τC x)) :=
      congrArg (algebraMap C (SeparableClosure ℚ)) hC.symm
    _ = algebraMap T (SeparableClosure ℚ)
          (numberFieldCyclotomicZHatCompositumRestriction L τC x) :=
      hTC _

omit [FiniteDimensional K L] in
/-- The `p`-adic degrees contributed by the top-field decomposition
group are exactly those visible in the actual cyclotomic compositum at
the restricted place. -/
theorem
    finitePlaceSeparableClosureTop_padicDegree_range
    (v : HeightOneSpectrum (𝓞 K))
    (p : Nat.Primes) :
    letI : Algebra K (SeparableClosure ℚ) :=
      numberFieldTowerSeparableClosureBaseAlgebra K L
    letI : Algebra L (SeparableClosure ℚ) :=
      numberFieldTowerSeparableClosureTopAlgebra L
    letI : IsScalarTower K L (SeparableClosure ℚ) :=
      numberFieldTowerSeparableClosureScalarTower K L
    letI : IsScalarTower ℚ K (SeparableClosure ℚ) :=
      numberFieldTowerSeparableClosureBaseScalarTower K L
    letI : IsScalarTower L
        (numberFieldCyclotomicZHatCompositum L)
        (SeparableClosure ℚ) :=
      numberFieldCyclotomicZHatCompositumSeparableClosureScalarTower L
    ((finitePlaceSeparableClosurePadicCyclotomicDegree
        (K := K) (L := L) v p).comp
        (finitePlaceSeparableClosureTopDecompositionInclusion
          (K := K) (L := L) v)).range =
      (numberFieldCyclotomicPadicDecompositionCoordinate L
        (finitePlaceCyclotomicCompositumExtension
          (K := K) (L := L) v).1 p).toMonoidHom.range := by
  let : Algebra K (SeparableClosure ℚ) :=
    numberFieldTowerSeparableClosureBaseAlgebra K L
  let : Algebra L (SeparableClosure ℚ) :=
    numberFieldTowerSeparableClosureTopAlgebra L
  let : IsScalarTower K L (SeparableClosure ℚ) :=
    numberFieldTowerSeparableClosureScalarTower K L
  let : IsScalarTower ℚ K (SeparableClosure ℚ) :=
    numberFieldTowerSeparableClosureBaseScalarTower K L
  let : IsScalarTower L
      (numberFieldCyclotomicZHatCompositum L)
      (SeparableClosure ℚ) :=
    numberFieldCyclotomicZHatCompositumSeparableClosureScalarTower L
  rw [
    finitePlaceSeparableClosureTopCyclotomicRestriction_padicDegree
      (K := K) (L := L) v p]
  apply le_antisymm
  · rintro y ⟨τ, rfl⟩
    exact
      ⟨finitePlaceSeparableClosureTopCyclotomicRestriction
          (K := K) (L := L) v τ,
        rfl⟩
  · rintro y ⟨σ, rfl⟩
    obtain ⟨τ, hτ⟩ :=
      finitePlaceSeparableClosureTopCyclotomicRestriction_surjective
        (K := K) (L := L) v σ
    refine ⟨τ, ?_⟩
    exact congrArg
      (numberFieldCyclotomicPadicDecompositionCoordinate L
        (finitePlaceCyclotomicCompositumExtension
          (K := K) (L := L) v).1 p)
      hτ

omit [FiniteDimensional K L] in
/-- The `p`-adic degrees contributed by the kernel of finite-place
restriction are exactly the degrees coming from the decomposition
group over the top field. -/
theorem
    finitePlaceSeparableClosureRestrictionKernel_padicDegree_range
    (v : HeightOneSpectrum (𝓞 K))
    (p : Nat.Primes) :
    letI : Algebra K (SeparableClosure ℚ) :=
      numberFieldTowerSeparableClosureBaseAlgebra K L
    letI : Algebra L (SeparableClosure ℚ) :=
      numberFieldTowerSeparableClosureTopAlgebra L
    letI : IsScalarTower K L (SeparableClosure ℚ) :=
      numberFieldTowerSeparableClosureScalarTower K L
    letI : IsScalarTower ℚ K (SeparableClosure ℚ) :=
      numberFieldTowerSeparableClosureBaseScalarTower K L
    letI : IsScalarTower L
        (numberFieldCyclotomicZHatCompositum L)
        (SeparableClosure ℚ) :=
      numberFieldCyclotomicZHatCompositumSeparableClosureScalarTower L
    let restriction :=
      finitePlaceSeparableClosureDecompositionRestriction
        (K := K) (L := L) v
    let inclusion :=
      finitePlaceSeparableClosureTopDecompositionInclusion
        (K := K) (L := L) v
    let degree :=
      finitePlaceSeparableClosurePadicCyclotomicDegree
        (K := K) (L := L) v p
    (restriction.ker.map degree).toAddSubgroup' =
      (degree.comp inclusion).range.toAddSubgroup' := by
  let : Algebra K (SeparableClosure ℚ) :=
    numberFieldTowerSeparableClosureBaseAlgebra K L
  let : Algebra L (SeparableClosure ℚ) :=
    numberFieldTowerSeparableClosureTopAlgebra L
  let : IsScalarTower K L (SeparableClosure ℚ) :=
    numberFieldTowerSeparableClosureScalarTower K L
  let : IsScalarTower ℚ K (SeparableClosure ℚ) :=
    numberFieldTowerSeparableClosureBaseScalarTower K L
  let : IsScalarTower L
      (numberFieldCyclotomicZHatCompositum L)
      (SeparableClosure ℚ) :=
    numberFieldCyclotomicZHatCompositumSeparableClosureScalarTower L
  dsimp only
  let restriction :=
    finitePlaceSeparableClosureDecompositionRestriction
      (K := K) (L := L) v
  let inclusion :=
    finitePlaceSeparableClosureTopDecompositionInclusion
      (K := K) (L := L) v
  let degree :=
    finitePlaceSeparableClosurePadicCyclotomicDegree
      (K := K) (L := L) v p
  rw [
    ←
      finitePlaceSeparableClosureTopDecompositionInclusion_range
        (K := K) (L := L) v,
    MonoidHom.range_comp]

omit [FiniteDimensional K L] in
/-- The `p`-adic cyclotomic degrees contributed by the genuine kernel
of finite-place restriction form a closed additive subgroup of
`ℤ_p`. -/
theorem
    finitePlaceSeparableClosureRestrictionKernel_padicDegree_isClosed
    (v : HeightOneSpectrum (𝓞 K))
    (p : Nat.Primes) :
    letI : Algebra K (SeparableClosure ℚ) :=
      numberFieldTowerSeparableClosureBaseAlgebra K L
    letI : Algebra L (SeparableClosure ℚ) :=
      numberFieldTowerSeparableClosureTopAlgebra L
    letI : IsScalarTower K L (SeparableClosure ℚ) :=
      numberFieldTowerSeparableClosureScalarTower K L
    letI : IsScalarTower ℚ K (SeparableClosure ℚ) :=
      numberFieldTowerSeparableClosureBaseScalarTower K L
    letI : IsScalarTower L
        (numberFieldCyclotomicZHatCompositum L)
        (SeparableClosure ℚ) :=
      numberFieldCyclotomicZHatCompositumSeparableClosureScalarTower L
    let restriction :=
      finitePlaceSeparableClosureDecompositionRestriction
        (K := K) (L := L) v
    let degree :=
      finitePlaceSeparableClosurePadicCyclotomicDegree
        (K := K) (L := L) v p
    IsClosed
      ((((restriction.ker.map degree).toAddSubgroup' :
          AddSubgroup ℤ_[p.1]) :
        Set ℤ_[p.1])) := by
  let : Algebra K (SeparableClosure ℚ) :=
    numberFieldTowerSeparableClosureBaseAlgebra K L
  let : Algebra L (SeparableClosure ℚ) :=
    numberFieldTowerSeparableClosureTopAlgebra L
  let : IsScalarTower K L (SeparableClosure ℚ) :=
    numberFieldTowerSeparableClosureScalarTower K L
  let : IsScalarTower ℚ K (SeparableClosure ℚ) :=
    numberFieldTowerSeparableClosureBaseScalarTower K L
  let : IsScalarTower L
      (numberFieldCyclotomicZHatCompositum L)
      (SeparableClosure ℚ) :=
    numberFieldCyclotomicZHatCompositumSeparableClosureScalarTower L
  dsimp only
  rw [
    finitePlaceSeparableClosureRestrictionKernel_padicDegree_range
      (K := K) (L := L) v p,
    finitePlaceSeparableClosureTop_padicDegree_range
      (K := K) (L := L) v p]
  change
    IsClosed
      ((fun z : ℤ_[p.1] => Multiplicative.ofAdd z) ⁻¹'
        ((numberFieldCyclotomicPadicDecompositionCoordinate L
          (finitePlaceCyclotomicCompositumExtension
            (K := K) (L := L) v).1 p).range :
          Set (Multiplicative ℤ_[p.1])))
  exact
    (numberFieldCyclotomicPadicDecompositionCoordinate_range_isClosed
      L
      (finitePlaceCyclotomicCompositumExtension
        (K := K) (L := L) v).1 p).preimage
      continuous_ofAdd

omit [FiniteDimensional K L] in
/-- The `p`-adic cyclotomic degrees contributed by the genuine kernel
of finite-place restriction form an open subgroup of `ℤ_p`.

The point is that the valuation on the actual cyclotomic compositum
need only represent the normalized finite-place class.  The
finite-index theorem for that valuation class and closedness of the
kernel image give openness. -/
theorem
    finitePlaceSeparableClosureRestrictionKernel_padicDegree_isOpen
    (v : HeightOneSpectrum (𝓞 K))
    (p : Nat.Primes) :
    letI : Algebra K (SeparableClosure ℚ) :=
      numberFieldTowerSeparableClosureBaseAlgebra K L
    letI : Algebra L (SeparableClosure ℚ) :=
      numberFieldTowerSeparableClosureTopAlgebra L
    letI : IsScalarTower K L (SeparableClosure ℚ) :=
      numberFieldTowerSeparableClosureScalarTower K L
    letI : IsScalarTower ℚ K (SeparableClosure ℚ) :=
      numberFieldTowerSeparableClosureBaseScalarTower K L
    letI : IsScalarTower L
        (numberFieldCyclotomicZHatCompositum L)
        (SeparableClosure ℚ) :=
      numberFieldCyclotomicZHatCompositumSeparableClosureScalarTower L
    let restriction :=
      finitePlaceSeparableClosureDecompositionRestriction
        (K := K) (L := L) v
    let degree :=
      finitePlaceSeparableClosurePadicCyclotomicDegree
        (K := K) (L := L) v p
    IsOpen
      ((((restriction.ker.map degree).toAddSubgroup' :
          AddSubgroup ℤ_[p.1]) :
        Set ℤ_[p.1])) := by
  let : Algebra K (SeparableClosure ℚ) :=
    numberFieldTowerSeparableClosureBaseAlgebra K L
  let : Algebra L (SeparableClosure ℚ) :=
    numberFieldTowerSeparableClosureTopAlgebra L
  let : IsScalarTower K L (SeparableClosure ℚ) :=
    numberFieldTowerSeparableClosureScalarTower K L
  let : IsScalarTower ℚ K (SeparableClosure ℚ) :=
    numberFieldTowerSeparableClosureBaseScalarTower K L
  let : IsScalarTower L
      (numberFieldCyclotomicZHatCompositum L)
      (SeparableClosure ℚ) :=
    numberFieldCyclotomicZHatCompositumSeparableClosureScalarTower L
  dsimp only
  have hclosed :=
    finitePlaceSeparableClosureRestrictionKernel_padicDegree_isClosed
      (K := K) (L := L) v p
  dsimp only at hclosed
  rw [
    finitePlaceSeparableClosureRestrictionKernel_padicDegree_range
      (K := K) (L := L) v p,
    finitePlaceSeparableClosureTop_padicDegree_range
      (K := K) (L := L) v p] at hclosed ⊢
  let H : AddSubgroup ℤ_[p.1] :=
    (numberFieldCyclotomicPadicDecompositionCoordinate L
      (finitePlaceCyclotomicCompositumExtension
        (K := K) (L := L) v).1 p).range.toAddSubgroup'
  change IsClosed (H : Set ℤ_[p.1]) at hclosed
  have hindex : H.index ≠ 0 := by
    exact
      numberFieldCyclotomicPadicDecompositionCoordinate_range_index_ne_zero_of_base_isEquiv
        L
        (finitePlaceExtensionCentre
          (K := K) (L := L) v
          (chosenFinitePlaceExtension (L := L) v))
        (finitePlaceCyclotomicCompositumExtension
          (K := K) (L := L) v).1
        (finitePlaceCyclotomicCompositumExtension_base_isEquiv
          (K := K) (L := L) v)
        p
  let finiteIndexH : H.FiniteIndex := ⟨hindex⟩
  exact AddSubgroup.isOpen_of_isClosed_of_finiteIndex H hclosed

omit [FiniteDimensional K L] in
/-- Every actual finite-place decomposition automorphism has a lift to
the compatible separable closure whose genuine cyclotomic `p`-adic
degree is a positive integer.

The lift is corrected only inside the decomposition group over `L`, so
its prescribed restriction to `L` is unchanged. -/
theorem
    exists_finitePlaceSeparableClosureLift_with_positivePadicCyclotomicDegree
    (v : HeightOneSpectrum (𝓞 K))
    (p : Nat.Primes)
    (σ :
      absoluteValueDecompositionGroup K
        (chosenFinitePlaceExtension (L := L) v).1) :
    letI : Algebra K (SeparableClosure ℚ) :=
      numberFieldTowerSeparableClosureBaseAlgebra K L
    letI : Algebra L (SeparableClosure ℚ) :=
      numberFieldTowerSeparableClosureTopAlgebra L
    letI : IsScalarTower K L (SeparableClosure ℚ) :=
      numberFieldTowerSeparableClosureScalarTower K L
    letI : IsScalarTower ℚ K (SeparableClosure ℚ) :=
      numberFieldTowerSeparableClosureBaseScalarTower K L
    letI : IsScalarTower L
        (numberFieldCyclotomicZHatCompositum L)
        (SeparableClosure ℚ) :=
      numberFieldCyclotomicZHatCompositumSeparableClosureScalarTower L
    let wΩ :=
      numberFieldTowerFinitePlaceExtensionToSeparableClosure
        K L v (chosenFinitePlaceExtension (L := L) v)
    ∃ τ : absoluteValueDecompositionGroup K wΩ.1,
      finitePlaceSeparableClosureDecompositionRestriction
          (K := K) (L := L) v τ =
        σ ∧
      ∃ n : ℕ, 0 < n ∧
        finitePlaceSeparableClosurePadicCyclotomicDegree
            (K := K) (L := L) v p τ =
          (Multiplicative.ofAdd (1 : ℤ_[p.1])) ^ n := by
  let : Algebra K (SeparableClosure ℚ) :=
    numberFieldTowerSeparableClosureBaseAlgebra K L
  let : Algebra L (SeparableClosure ℚ) :=
    numberFieldTowerSeparableClosureTopAlgebra L
  let : IsScalarTower K L (SeparableClosure ℚ) :=
    numberFieldTowerSeparableClosureScalarTower K L
  let : IsScalarTower ℚ K (SeparableClosure ℚ) :=
    numberFieldTowerSeparableClosureBaseScalarTower K L
  let : IsScalarTower L
      (numberFieldCyclotomicZHatCompositum L)
      (SeparableClosure ℚ) :=
    numberFieldCyclotomicZHatCompositumSeparableClosureScalarTower L
  dsimp only
  exact
    exists_positivePadicDegree_lift_of_surjective
      p
      (finitePlaceSeparableClosureDecompositionRestriction
        (K := K) (L := L) v)
      (finitePlaceSeparableClosureDecompositionRestriction_surjective
        (K := K) (L := L) v)
      (finitePlaceSeparableClosurePadicCyclotomicDegree
        (K := K) (L := L) v p)
      (finitePlaceSeparableClosureRestrictionKernel_padicDegree_isOpen
        (K := K) (L := L) v p)
      σ

end Reciprocity
end GlobalClassFieldTheory
end
end

section
-- module Solutions.OAIQ244_DUKE.GlobalClassFieldTheory_Reciprocity_LocalGlobalArtinCompatibility_FinitePadicCyclicData
attribute [-instance] _root_.GlobalClassFieldTheory.GlobalClassFields.finiteAbelianSubextensionAbstractRelativeFixedFieldFiniteDimensional _root_.GlobalClassFieldTheory.GlobalClassFields.ordinaryNormClassFieldBaseFiniteDimensional _root_.GlobalClassFieldTheory.GlobalClassFields.ordinaryNormClassFieldBaseNumberField _root_.GlobalClassFieldTheory.Reciprocity.abstractFixedFieldCyclotomicCompositum_algebra _root_.GlobalClassFieldTheory.Reciprocity.abstractFixedFieldCyclotomicCompositum_scalarTower _root_.GlobalClassFieldTheory.Reciprocity.abstractFixedFieldCyclotomicFiniteCompositum_baseAlgebra _root_.GlobalClassFieldTheory.Reciprocity.abstractFixedFieldCyclotomicFiniteCompositum_baseScalarTower _root_.GlobalClassFieldTheory.Reciprocity.abstractFixedFieldCyclotomicFiniteCompositum_finiteDimensional _root_.GlobalClassFieldTheory.Reciprocity.abstractFixedFieldCyclotomicFiniteCompositum_numberField _root_.GlobalClassFieldTheory.Reciprocity.abstractFixedFieldCyclotomicFiniteGaloisLayer_scalarTower _root_.GlobalClassFieldTheory.Reciprocity.abstractFixedFieldCyclotomicFiniteLayer_baseAlgebra _root_.GlobalClassFieldTheory.Reciprocity.abstractFixedFieldCyclotomicFiniteLayer_baseModule _root_.GlobalClassFieldTheory.Reciprocity.abstractFixedFieldCyclotomicFiniteLayer_baseSMul _root_.GlobalClassFieldTheory.Reciprocity.abstractFixedFieldCyclotomicFiniteLayer_baseScalarTower _root_.GlobalClassFieldTheory.Reciprocity.abstractFixedFieldCyclotomicFiniteLayer_finiteDimensional _root_.GlobalClassFieldTheory.Reciprocity.abstractFixedFieldCyclotomicFiniteLayer_isAbelianGalois _root_.GlobalClassFieldTheory.Reciprocity.abstractFixedFieldCyclotomicFiniteLayer_layerAlgebra _root_.GlobalClassFieldTheory.Reciprocity.abstractFixedFieldCyclotomicFiniteLayer_layerSMul _root_.GlobalClassFieldTheory.Reciprocity.abstractFixedFieldCyclotomicFiniteLayer_layerScalarTower _root_.GlobalClassFieldTheory.Reciprocity.abstractFixedFieldCyclotomicFiniteLayer_numberField _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.instTopologicalSpaceLocalAlgebra _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.labelPrime_fact _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable
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
local instance numberFieldTowerExtensionNormal_r40a3be_1 :
    (extensionSubgroup
      (numberFieldTowerBaseSubgroup K L)
      (numberFieldTowerTopSubgroup L)
      (numberFieldTowerTopSubgroup_le_baseSubgroup K L)).Normal :=
  numberFieldTowerExtensionSubgroup_normal K L
local instance finitePadicTowerExtensionQuotientFinite :
    Finite
      ((numberFieldTowerBaseSubgroup K L).toSubgroup ⧸
        extensionSubgroup
          (numberFieldTowerBaseSubgroup K L)
          (numberFieldTowerTopSubgroup L)
          (numberFieldTowerTopSubgroup_le_baseSubgroup K L)) :=
  numberFieldTowerExtensionQuotient_finite K L

noncomputable local instance numberFieldTowerExtensionQuotientIsMulCommutative_r40a3be_1 :
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
local instance numberFieldTowerBaseSubgroupCompactSpace_r40a3be_1 :
    CompactSpace
      (numberFieldTowerBaseSubgroup K L).toSubgroup :=
  isCompact_iff_compactSpace.mp
    (numberFieldTowerBaseSubgroup K L).isClosed'.isCompact
/-- The genuine `p`-adic cyclotomic degree on the rational absolute
Galois group. -/
noncomputable def rationalSeparableClosurePadicCyclotomicDegree
    (p : Nat.Primes) :
    Gal(SeparableClosure ℚ / ℚ) →ₜ*
      Multiplicative ℤ_[p.1] :=
  (rationalCyclotomicPadicCoordinate p).comp
    rationalAbsoluteGaloisRestrictionToCyclotomicZHat

/-- The genuine rational cyclotomic `p`-adic degree restricted to the
compatible embedded copy of the absolute Galois group of `K`. -/
noncomputable def numberFieldTowerBaseSubgroupPadicCyclotomicDegree
    (p : Nat.Primes) :
    (numberFieldTowerBaseSubgroup K L).toSubgroup →ₜ*
      Multiplicative ℤ_[p.1] :=
  (rationalSeparableClosurePadicCyclotomicDegree p).comp
    (continuousSubgroupSubtype
      (numberFieldTowerBaseSubgroup K L).toSubgroup)

end Reciprocity
end GlobalClassFieldTheory
end
end


