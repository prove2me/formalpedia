-- Prove2me | Definitions.Def_OAIQ244Duke097
-- name    : OAIQ244Duke097
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-14T02:35:13.435394+00:00
-- url     : https://prove2.me/theorems/5c2d488a-1c89-4057-bdca-0b9a34317b09
-- title:
--   Definitions bundle OAIQ244Duke097 of the split of OpenAI, Equidistribution of Prime-Degree Torus Packets with Arbitrary Local Type
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.DukePrimeDegree.prime_degree_packet_measure_equidistribution_unconditional` and `OAI.DukePrimeDegree.prime_degree_packet_measures_tendsto_haar_unconditional`, carved from OpenAI's openai/math development (OpenAI, *Equidistribution of Prime-Degree Torus Packets with Arbitrary Local Type*, OpenAI Math Release, September 24, 2026, result family 15, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 67 declarations of OpenAI's Lean: 10 definitions and 57 theorems. The definitions and types are `GlobalClassFieldTheory.Reciprocity.abstractFixedFieldCyclotomicGalEquivZHat`, `GlobalClassFieldTheory.Reciprocity.cyclotomicValuationIdeleClassCommGroup`, `GlobalClassFieldTheory.Reciprocity.normalizedCyclotomicZHatIdeleClassValueContinuous`, `GlobalClassFieldTheory.Reciprocity.normalizedCyclotomicZHatIdeleClassValueContinuousMul`, `GlobalClassFieldTheory.Reciprocity.rationalCyclotomicArtinLocalExponent`, `GlobalClassFieldTheory.Reciprocity.rationalCyclotomicIdeleClassValuationData`, `GlobalClassFieldTheory.Reciprocity.rationalCyclotomicZHatIdeleClassNormComposite`, `GlobalClassFieldTheory.Reciprocity.rationalCyclotomicZHatIdeleClassValueContinuous`, `GlobalClassFieldTheory.Reciprocity.rationalCyclotomicZHatIdeleClassValueContinuousMul`, `GlobalClassFieldTheory.Reciprocity.rationalCyclotomicZHatValuation`.
--
--   **Sources.** They come from these modules of lean/OAI/NumberTheory, in whole or in part: `GlobalClassFieldTheory_Reciprocity_ComplexificationArtin_RationalComplexification`, `GlobalClassFieldTheory_Reciprocity_CyclotomicAbstractFixedFieldArtin`, `GlobalClassFieldTheory_Reciprocity_CyclotomicIdeleClassValuation`, `GlobalClassFieldTheory_Reciprocity_FinitePlaceCyclotomicFrobeniusLift`, `GlobalClassFieldTheory_Reciprocity_RationalCyclotomicFinitePlaceArtin`, `GlobalClassFieldTheory_Reciprocity_RationalCyclotomicPrincipalAwayProduct`, `GlobalClassFieldTheory_Reciprocity_RationalCyclotomicPrincipalPrimeFactor`, `GlobalClassFieldTheory_Reciprocity_RationalCyclotomicPrincipalProduct`.
--
--   **Imports.** It imports the bundles `OAIQ244Duke095` and `OAIQ244Duke096` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ244Duke100` and `OAIQ244Duke101`.
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
import Mathlib.NumberTheory.NumberField.CMField
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
import Definitions.Def_OAIQ244Duke095
import Definitions.Def_OAIQ244Duke096

section
-- module Solutions.OAIQ244_DUKE.GlobalClassFieldTheory_Reciprocity_RationalCyclotomicFinitePlaceArtin
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.GlobalClassFields.ConductorialSubgroup.finiteIndex _root_.GlobalClassFieldTheory.GlobalClassFields.bigHilbertClassFieldNormSubgroup_normal _root_.GlobalClassFieldTheory.GlobalClassFields.ideleClassNorm_rangeFiniteIndex _root_.GlobalClassFieldTheory.GlobalClassFields.smallHilbertClassFieldNormSubgroupFiniteIndex _root_.GlobalClassFieldTheory.Reciprocity.complexFourthRootField_finiteDimensional _root_.GlobalClassFieldTheory.Reciprocity.complexFourthRootField_isCyclotomic _root_.GlobalClassFieldTheory.Reciprocity.complexFourthRootField_numberField _root_.GlobalClassFieldTheory.Reciprocity.infinitePlaceComplexificationOverfield_algebra _root_.GlobalClassFieldTheory.Reciprocity.infinitePlaceComplexificationOverfield_baseAlgebra _root_.GlobalClassFieldTheory.Reciprocity.infinitePlaceComplexificationOverfield_finiteDimensional _root_.GlobalClassFieldTheory.Reciprocity.infinitePlaceComplexificationOverfield_numberField _root_.GlobalClassFieldTheory.Reciprocity.numberFieldCyclotomicZHatCompositum_algebra _root_.GlobalClassFieldTheory.Reciprocity.numberFieldCyclotomicZHatFiniteCompositum_algebra _root_.GlobalClassFieldTheory.Reciprocity.numberFieldCyclotomicZHatFiniteCompositum_finiteDimensional _root_.GlobalClassFieldTheory.Reciprocity.numberFieldCyclotomicZHatFiniteCompositum_numberField _root_.GlobalClassFieldTheory.Reciprocity.numberFieldCyclotomicZHatFiniteLayerInCompositum_finiteDimensional _root_.GlobalClassFieldTheory.Reciprocity.numberFieldCyclotomicZHatFiniteLayerInCompositum_numberField _root_.GlobalClassFieldTheory.Reciprocity.numberFieldCyclotomicZHatIntersection_finiteDimensional _root_.GlobalClassFieldTheory.Reciprocity.numberFieldCyclotomicZHatIntersection_numberField _root_.GlobalClassFieldTheory.Reciprocity.ramifiedInfinitePlaceRealFixedField_algebra _root_.GlobalClassFieldTheory.Reciprocity.ramifiedInfinitePlaceRealFixedField_numberField _root_.GlobalClassFieldTheory.Reciprocity.rationalComplexificationCyclotomicField_isCMField _root_.GlobalClassFieldTheory.Reciprocity.rationalComplexificationCyclotomicField_isCyclotomicFour _root_.GlobalClassFieldTheory.Reciprocity.rationalCyclotomicZHatField_isAbelianGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalIdeleClassDirectLimitMonoid _root_.GlobalClassFieldTheory.Reciprocity.rationalIntermediateFieldAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalIntermediateFieldNumberField _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.GlobalClassFieldTheory.Reciprocity.rationalTowerClassGroupCommGroup _root_.GlobalClassFieldTheory.Reciprocity.rationalTowerClassGroupMul _root_.KummerTheory.DiscreteNthRootsSubgroup.instTopologicalSpaceSubtypeUnitsMemSubgroup _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.KummerTheory.primeCyclotomicBaseFiniteDimensional _root_.KummerTheory.primeCyclotomicBaseIsGalois _root_.KummerTheory.primeCyclotomicBaseNumberField _root_.KummerTheory.rationalCyclotomicField_hasEnoughRootsOfUnity _root_.KummerTheory.rationalCyclotomicTorsionFixedField_isAbelianGalois _root_.KummerTheory.rationalCyclotomicTorsionFixedField_isGalois _root_.KummerTheory.rationalCyclotomicTorsionFixedField_isIntegral _root_.KummerTheory.rationalCyclotomicTorsionFixedField_normal _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.residueFieldZModAlgebra _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.boundedRealFields_numberField _root_.OAI.PrimeDegreePackets.instTopologicalSpaceLocalAlgebra _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.CyclicCohomology.binaryCoefficientFamilyCommGroup _root_.GlobalClassFieldTheory.GlobalClassFields.bigHilbertNormQuotient_finite _root_.GlobalClassFieldTheory.GlobalClassFields.bigHilbertNormSubgroup_finiteIndex _root_.GlobalClassFieldTheory.Reciprocity.instNumberFieldSubtypeSeparableClosureRatMemIntermediateFieldAbstractFixedFieldOfFiniteQuotientAlgEquivSubgroupBaseFieldExtensionSubgroup _root_.GlobalClassFieldTheory.Reciprocity.instMonoidClassGroupRatSubtypeSeparableClosureMemIntermediateField _root_.GlobalClassFieldTheory.Reciprocity.rationalAbstractRelativeClassGroupCommGroup _root_.GlobalClassFieldTheory.Reciprocity.rationalAbstractRelativeClassGroupMul _root_.GlobalClassFieldTheory.Reciprocity.rationalAbstractRelativeClassGroupMulOneClass _root_.GlobalClassFieldTheory.Reciprocity.rationalAbstractTowerClassGroupCommGroup _root_.GlobalClassFieldTheory.Reciprocity.rationalAbstractTowerClassGroupMul _root_.GlobalClassFieldTheory.Reciprocity.rationalAbstractTowerClassGroupMulOneClass _root_.cyclicPrimeDegreeIntermediate_isGalois _root_.relativeUnrestrictedSPlaceFactorCommGroup
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

/-!
# Finite-place Artin symbols in rational cyclotomic levels

At a rational prime away from the cyclotomic level, the chosen completed
extension is unramified.  Its normalized local Artin map is therefore the
arithmetic Frobenius raised to the local valuation.  The genuine primitive
root in the localized cyclotomic level identifies the image of arithmetic
Frobenius under the global cyclotomic character with the residue prime.
-/

open scoped Classical NNReal NumberField ValuativeRel
open NumberField IsDedekindDomain

noncomputable section

namespace GlobalClassFieldTheory
namespace Reciprocity

open AlgebraicNumberTheory.Valuations
open HilbertRamification
open LocalClassFieldTheory
open LocalFieldTheory
open LocalFieldTheory.DiscreteValuationField
open LocalFieldTheory.DiscreteValuationField.Examples.Qp
open LubinTate

/-! Named compatibility witnesses used by the ramified-prime and ray-norm
modules.  They are not installed as a duplicate module-level instance family;
the canonical instances above already provide the same data. -/

attribute [local instance] GlobalClassFieldTheory.Reciprocity.rationalFinitePlaceCompletionRatAlgebra
attribute [local instance] GlobalClassFieldTheory.Reciprocity.instFactPrimeValNat_solutions_2
attribute [local instance] GlobalClassFieldTheory.Reciprocity.instNeZeroNatVal_solutions
attribute [local instance] GlobalClassFieldTheory.Reciprocity.rationalCyclotomicLevelFiniteDimensional
attribute [local instance] GlobalClassFieldTheory.Reciprocity.rationalCyclotomicLevelIsAbelianGalois
attribute [local instance] GlobalClassFieldTheory.Reciprocity.rationalFinitePlaceBaseNontriviallyNormedField
attribute [local instance] GlobalClassFieldTheory.Reciprocity.rationalFinitePlaceBaseLocallyCompactSpace
attribute [local instance] GlobalClassFieldTheory.Reciprocity.rationalFinitePlaceBaseIsUltrametricDist
attribute [local instance] GlobalClassFieldTheory.Reciprocity.rationalFinitePlaceBaseValued
attribute [local instance] GlobalClassFieldTheory.Reciprocity.rationalFinitePlaceBaseValuativeRel
attribute [local instance] GlobalClassFieldTheory.Reciprocity.rationalFinitePlaceBaseValuationIsNontrivial
attribute [local instance] GlobalClassFieldTheory.Reciprocity.rationalFinitePlaceBaseValuationCompatible
attribute [local instance] GlobalClassFieldTheory.Reciprocity.rationalFinitePlaceBaseValuativeRelIsNontrivial
noncomputable local instance rationalFinitePlaceBaseIsValuativeTopology_rded382_1
    (q : Nat.Primes) :
    IsValuativeTopology
      (HeightOneSpectrum.adicAbv ℚ
        (RayClass.rationalPrime q)).Completion :=
  isValuativeTopology_of_valued_ofValuation
    (HeightOneSpectrum.adicAbv ℚ
      (RayClass.rationalPrime q)).Completion ℝ≥0
attribute [local instance] GlobalClassFieldTheory.Reciprocity.rationalFinitePlaceBaseIsNonarchimedeanLocalField
attribute [local instance] GlobalClassFieldTheory.Reciprocity.rationalCyclotomicArtinExtensionAlgebra
attribute [local instance] GlobalClassFieldTheory.Reciprocity.rationalCyclotomicArtinExtensionSMul
attribute [local instance] GlobalClassFieldTheory.Reciprocity.rationalCyclotomicArtinCompletionAlgebra
attribute [local instance] GlobalClassFieldTheory.Reciprocity.rationalCyclotomicArtinLocalizedAlgebra
attribute [local instance] GlobalClassFieldTheory.Reciprocity.rationalCyclotomicArtinLocalizedGlobalAlgebra
attribute [local instance] GlobalClassFieldTheory.Reciprocity.rationalCyclotomicArtinLocalizedGlobalSMul
attribute [local instance] GlobalClassFieldTheory.Reciprocity.rationalCyclotomicArtinLocalizedScalarTower
attribute [local instance] GlobalClassFieldTheory.Reciprocity.rationalCyclotomicArtinLocalizedFiniteDimensional
attribute [local instance] GlobalClassFieldTheory.Reciprocity.rationalCyclotomicArtinLocalizedIsAbelianGalois
attribute [local instance] GlobalClassFieldTheory.Reciprocity.rationalCyclotomicArtinLocalizedIsSeparable
attribute [local instance] GlobalClassFieldTheory.Reciprocity.rationalCyclotomicArtinLocalizedIsCyclotomic
attribute [local instance] GlobalClassFieldTheory.Reciprocity.rationalCyclotomicArtinExtensionFiniteDimensional
attribute [local instance] GlobalClassFieldTheory.Reciprocity.rationalCyclotomicArtinExtensionContinuousSMul
attribute [local instance] GlobalClassFieldTheory.Reciprocity.rationalCyclotomicArtinExtensionLocallyCompact
attribute [local instance] GlobalClassFieldTheory.Reciprocity.rationalCyclotomicArtinLocalizedLocallyCompact
noncomputable local instance
    rationalCyclotomicArtinLocalizedIsUltrametricDist_rded382_1
    (m : ℕ+) (q : Nat.Primes) :
    IsUltrametricDist
      (rationalCyclotomicArtinLocalizedField m q) :=
  localizedCompletionIsUltrametricDist
    (rationalCyclotomicArtinBaseAbv q)
    (rationalCyclotomicArtinExtension m q)
    (HeightOneSpectrum.isNonarchimedean_adicAbv
      ℚ (rationalCyclotomicArtinPlace q))
attribute [local instance] GlobalClassFieldTheory.Reciprocity.rationalCyclotomicArtinLocalizedValued
attribute [local instance] GlobalClassFieldTheory.Reciprocity.rationalCyclotomicArtinLocalizedValuativeRel
attribute [local instance] GlobalClassFieldTheory.Reciprocity.rationalCyclotomicArtinLocalizedValuationCompatible
attribute [local instance] GlobalClassFieldTheory.Reciprocity.rationalCyclotomicArtinLocalizedValuationHasExtension
attribute [local instance] GlobalClassFieldTheory.Reciprocity.rationalCyclotomicArtinLocalizedValuationIsNontrivial
attribute [local instance] GlobalClassFieldTheory.Reciprocity.rationalCyclotomicArtinLocalizedValuativeRelIsNontrivial
attribute [local instance] GlobalClassFieldTheory.Reciprocity.rationalCyclotomicArtinLocalizedIsValuativeTopology
attribute [local instance] GlobalClassFieldTheory.Reciprocity.rationalCyclotomicArtinLocalizedIsNonarchimedeanLocalField
attribute [local instance] GlobalClassFieldTheory.Reciprocity.rationalCyclotomicArtinLocalizedIntegerAlgebra
attribute [local instance] GlobalClassFieldTheory.Reciprocity.rationalCyclotomicArtinLocalizedIsIntegralClosure
attribute [local instance] GlobalClassFieldTheory.Reciprocity.rationalCyclotomicArtinLocalizedIntegerModuleFinite
/-- The normalized valuation of the canonical completion input used by the
rational finite-place Artin map.  This named endpoint keeps the completion
instances out of downstream theorem statements. -/
noncomputable def rationalCyclotomicArtinLocalExponent
    (q : Nat.Primes)
    (x : ((RayClass.rationalPrime q).adicCompletion ℚ)ˣ) : ℤ :=
  IsNonarchimedeanLocalField.valuationMap
    (rationalCyclotomicArtinBaseAbv q).Completion
    (Additive.ofMul (rationalCyclotomicArtinLocalInput q x))

theorem
    rationalCyclotomicFinitePlaceMappedLocalArtin_eq_frobenius_zpow_of
    (m : ℕ+) (q : Nat.Primes)
    (hAbelian :
      IsAbelianGalois
        (rationalCyclotomicArtinBaseAbv q).Completion
        (rationalCyclotomicArtinLocalizedField m q))
    (hUnramified :
      IsNonarchimedeanLocalField.IsUnramifiedValuedExtension
        (rationalCyclotomicArtinBaseAbv q).Completion
        (rationalCyclotomicArtinLocalizedField m q))
    (x : ((RayClass.rationalPrime q).adicCompletion ℚ)ˣ) :
    rationalCyclotomicArtinLocalToGlobalMonoidHom m q
        (LocalClassFieldTheory.abelianLocalArtinMonoidHom
          (rationalCyclotomicArtinBaseAbv q).Completion
          (rationalCyclotomicArtinLocalizedField m q)
          (rationalCyclotomicArtinLocalInput q x)) =
      (rationalCyclotomicArtinGlobalFrobeniusOf
        m q hUnramified) ^
        rationalCyclotomicArtinLocalExponent q x := by
  let := hAbelian
  let := hUnramified
  change
    rationalCyclotomicArtinLocalToGlobalMonoidHom m q
        (LocalClassFieldTheory.abelianLocalArtinMonoidHom
          (rationalCyclotomicArtinBaseAbv q).Completion
          (rationalCyclotomicArtinLocalizedField m q)
          (rationalCyclotomicArtinLocalInput q x)) =
      (rationalCyclotomicArtinLocalToGlobalMonoidHom m q
        (arithmeticFrobeniusOfUnramifiedValuation
          (rationalCyclotomicArtinBaseAbv q).Completion
          (rationalCyclotomicArtinLocalizedField m q))) ^
        rationalCyclotomicArtinLocalExponent q x
  exact
    mappedAbelianLocalArtin_eq_frobenius_zpow
      (F := (rationalCyclotomicArtinBaseAbv q).Completion)
      (E := rationalCyclotomicArtinLocalizedField m q)
      (rationalCyclotomicArtinLocalToGlobalMonoidHom m q)
      (rationalCyclotomicArtinLocalInput q x)

theorem
    rationalCyclotomicFinitePlaceMappedLocalArtin_eq_frobenius_zpow
    (m : ℕ+) (q : Nat.Primes)
    (hq : ¬ q.1 ∣ (m : ℕ))
    (x : ((RayClass.rationalPrime q).adicCompletion ℚ)ˣ) :
    rationalCyclotomicArtinLocalToGlobalMonoidHom m q
        (rationalCyclotomicArtinLocalArtin m q x) =
      (rationalCyclotomicChosenArithmeticFrobenius m q hq) ^
        rationalCyclotomicArtinLocalExponent q x := by
  change
    rationalCyclotomicArtinLocalToGlobalMonoidHom m q
        (rationalCyclotomicArtinLocalArtin m q x) =
      (rationalCyclotomicArtinGlobalFrobeniusOf m q
        (rationalCyclotomicArtinUnramified m q hq)) ^
        rationalCyclotomicArtinLocalExponent q x
  calc
    rationalCyclotomicArtinLocalToGlobalMonoidHom m q
          (rationalCyclotomicArtinLocalArtin m q x) =
        rationalCyclotomicArtinLocalToGlobalMonoidHom m q
          (LocalClassFieldTheory.abelianLocalArtinMonoidHom
            (rationalCyclotomicArtinBaseAbv q).Completion
            (rationalCyclotomicArtinLocalizedField m q)
            (rationalCyclotomicArtinLocalInput q x)) :=
      congrArg
        (fun σ =>
          rationalCyclotomicArtinLocalToGlobalMonoidHom m q σ)
        (rationalCyclotomicArtinLocalArtin_eq m q x)
    _ =
        (rationalCyclotomicArtinGlobalFrobeniusOf m q
          (rationalCyclotomicArtinUnramified m q hq)) ^
          rationalCyclotomicArtinLocalExponent q x :=
      rationalCyclotomicFinitePlaceMappedLocalArtin_eq_frobenius_zpow_of
        m q (rationalCyclotomicArtinLocalizedIsAbelianGalois m q)
        (rationalCyclotomicArtinUnramified m q hq) x

/-- The chosen local Artin symbol is the chosen global Frobenius lift raised
to the normalized local valuation. -/
theorem
    chosenFinitePlaceArtin_eq_chosenArithmeticFrobenius_zpow
    (m : ℕ+) (q : Nat.Primes)
    (hq : ¬ q.1 ∣ (m : ℕ))
    (x : ((RayClass.rationalPrime q).adicCompletion ℚ)ˣ) :
    chosenFinitePlaceArtinMonoidHom
        (K := ℚ) (L := rationalCyclotomicArtinLevel m)
        (rationalCyclotomicArtinPlace q) x =
      (rationalCyclotomicChosenArithmeticFrobenius m q hq) ^
        rationalCyclotomicArtinLocalExponent q x := by
  change
    finitePlaceArtinMonoidHomOfExtension
        (K := ℚ) (L := rationalCyclotomicArtinLevel m)
        (rationalCyclotomicArtinPlace q)
        (rationalCyclotomicArtinExtension m q) x =
      (rationalCyclotomicChosenArithmeticFrobenius m q hq) ^
        rationalCyclotomicArtinLocalExponent q x
  have hFactor :
      finitePlaceArtinMonoidHomOfExtension
          (K := ℚ) (L := rationalCyclotomicArtinLevel m)
          (rationalCyclotomicArtinPlace q)
          (rationalCyclotomicArtinExtension m q) x =
        rationalCyclotomicArtinLocalToGlobalMonoidHom m q
          (rationalCyclotomicArtinLocalArtin m q x) := by
    change
      finitePlaceArtinMonoidHomOfExtension
          (K := ℚ) (L := rationalCyclotomicArtinLevel m)
          (rationalCyclotomicArtinPlace q)
          (rationalCyclotomicArtinExtension m q) x =
        finitePlaceLocalToGlobalMonoidHom
          (K := ℚ) (L := rationalCyclotomicArtinLevel m)
          (rationalCyclotomicArtinPlace q)
          (rationalCyclotomicArtinExtension m q)
          (finitePlaceLocalArtinMonoidHom
            (K := ℚ) (L := rationalCyclotomicArtinLevel m)
            (rationalCyclotomicArtinPlace q)
            (rationalCyclotomicArtinExtension m q) x)
    exact
      congrArg
        (fun φ :
          ((rationalCyclotomicArtinPlace q).adicCompletion ℚ)ˣ →*
            (rationalCyclotomicArtinLevel m ≃ₐ[ℚ]
              rationalCyclotomicArtinLevel m) => φ x)
        (finitePlaceArtinMonoidHomOfExtension_factor
          (K := ℚ) (L := rationalCyclotomicArtinLevel m)
          (rationalCyclotomicArtinPlace q)
          (rationalCyclotomicArtinExtension m q))
  exact
    hFactor.trans
      (rationalCyclotomicFinitePlaceMappedLocalArtin_eq_frobenius_zpow
        m q hq x)

/-- At a rational prime not dividing the level, the cyclotomic character
of the chosen finite-place Artin symbol is the residue prime raised to the
normalized local valuation. -/
theorem galEquivZMod_chosenFinitePlaceArtinMonoidHom_of_not_dvd
    (m : ℕ+) (q : Nat.Primes)
    (hq : ¬ q.1 ∣ (m : ℕ))
    (x : ((RayClass.rationalPrime q).adicCompletion ℚ)ˣ) :
    let v : HeightOneSpectrum (𝓞 ℚ) :=
      RayClass.rationalPrime q
    let L := KummerTheory.rationalCyclotomicLevel m
    let vQ := HeightOneSpectrum.adicAbv ℚ v
    let localInput :=
      (finitePlaceCompletionUnitsContinuousMulEquiv v).symm x
    let localExponent :=
      LocalFieldTheory.IsNonarchimedeanLocalField.valuationMap
        vQ.Completion (Additive.ofMul localInput)
    IsCyclotomicExtension.Rat.galEquivZMod
        (m : ℕ) L
        (chosenFinitePlaceArtinMonoidHom
          (K := ℚ)
          (L := L) v x) =
      (ZMod.unitOfCoprime q.1
        (q.2.coprime_iff_not_dvd.mpr hq)) ^ localExponent := by
  dsimp only
  rw [chosenFinitePlaceArtin_eq_chosenArithmeticFrobenius_zpow
      m q hq x, map_zpow,
    galEquivZMod_chosenArithmeticFrobenius m q hq]
  rfl

/-- For a rational principal idele, the unramified finite-place
cyclotomic Artin symbol at `q` is `q` raised to the negative usual
`q`-adic exponent. -/
theorem
    galEquivZMod_chosenFinitePlaceArtinMonoidHom_principal_of_not_dvd
    (m : ℕ+) (q : Nat.Primes)
    (hq : ¬ q.1 ∣ (m : ℕ)) (x : ℚˣ) :
    IsCyclotomicExtension.Rat.galEquivZMod
        (m : ℕ)
        (KummerTheory.rationalCyclotomicLevel m)
        (chosenFinitePlaceArtinMonoidHom
          (K := ℚ)
          (L := KummerTheory.rationalCyclotomicLevel m)
          (RayClass.rationalPrime q)
          (IdeleGroup.finiteComponent
            (RayClass.rationalPrime q)
            (IdeleGroup.principalIdele ℚ x))) =
      (ZMod.unitOfCoprime q.1
        (q.2.coprime_iff_not_dvd.mpr hq)) ^
          (-padicValRat q.1 (x : ℚ)) := by
  rw [
    galEquivZMod_chosenFinitePlaceArtinMonoidHom_of_not_dvd
      m q hq,
    rationalPrincipalFiniteComponent_valuationMap]

end Reciprocity
end GlobalClassFieldTheory
end
end

section
-- module Solutions.OAIQ244_DUKE.GlobalClassFieldTheory_Reciprocity_RationalCyclotomicPrincipalAwayProduct
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.GlobalClassFields.ConductorialSubgroup.finiteIndex _root_.GlobalClassFieldTheory.GlobalClassFields.bigHilbertClassFieldNormSubgroup_normal _root_.GlobalClassFieldTheory.GlobalClassFields.ideleClassNorm_rangeFiniteIndex _root_.GlobalClassFieldTheory.GlobalClassFields.smallHilbertClassFieldNormSubgroupFiniteIndex _root_.GlobalClassFieldTheory.Reciprocity.complexFourthRootField_finiteDimensional _root_.GlobalClassFieldTheory.Reciprocity.complexFourthRootField_isCyclotomic _root_.GlobalClassFieldTheory.Reciprocity.complexFourthRootField_numberField _root_.GlobalClassFieldTheory.Reciprocity.infinitePlaceComplexificationOverfield_finiteDimensional _root_.GlobalClassFieldTheory.Reciprocity.infinitePlaceComplexificationOverfield_numberField _root_.GlobalClassFieldTheory.Reciprocity.numberFieldCyclotomicZHatFiniteCompositum_finiteDimensional _root_.GlobalClassFieldTheory.Reciprocity.numberFieldCyclotomicZHatFiniteCompositum_numberField _root_.GlobalClassFieldTheory.Reciprocity.numberFieldCyclotomicZHatFiniteLayerInCompositum_numberField _root_.GlobalClassFieldTheory.Reciprocity.numberFieldCyclotomicZHatIntersection_finiteDimensional _root_.GlobalClassFieldTheory.Reciprocity.numberFieldCyclotomicZHatIntersection_numberField _root_.GlobalClassFieldTheory.Reciprocity.ramifiedInfinitePlaceRealFixedField_numberField _root_.GlobalClassFieldTheory.Reciprocity.rationalComplexificationCyclotomicField_isCMField _root_.GlobalClassFieldTheory.Reciprocity.rationalComplexificationCyclotomicField_isCyclotomicFour _root_.GlobalClassFieldTheory.Reciprocity.rationalCyclotomicZHatField_isAbelianGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalIdeleClassDirectLimitMonoid _root_.GlobalClassFieldTheory.Reciprocity.rationalIntermediateFieldAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalIntermediateFieldNumberField _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.GlobalClassFieldTheory.Reciprocity.rationalTowerClassGroupCommGroup _root_.GlobalClassFieldTheory.Reciprocity.rationalTowerClassGroupMul _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.KummerTheory.nthRootsSubgroupFintype _root_.KummerTheory.primeCyclotomicBaseFiniteDimensional _root_.KummerTheory.primeCyclotomicBaseIsGalois _root_.KummerTheory.primeCyclotomicBaseNumberField _root_.KummerTheory.rationalCyclotomicField_hasEnoughRootsOfUnity _root_.KummerTheory.rationalCyclotomicTorsionFixedField_isAbelianGalois _root_.KummerTheory.rationalCyclotomicTorsionFixedField_isGalois _root_.KummerTheory.rationalCyclotomicTorsionFixedField_isIntegral _root_.KummerTheory.rationalCyclotomicTorsionFixedField_normal _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.residueFieldZModAlgebra _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.boundedRealFields_numberField _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.labelPrime_fact _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.CyclicCohomology.binaryCoefficientFamilyCommGroup _root_.GlobalClassFieldTheory.GlobalClassFields.bigHilbertNormQuotient_finite _root_.GlobalClassFieldTheory.GlobalClassFields.bigHilbertNormSubgroup_finiteIndex _root_.GlobalClassFieldTheory.Reciprocity.instNumberFieldSubtypeSeparableClosureRatMemIntermediateFieldAbstractFixedFieldOfFiniteQuotientAlgEquivSubgroupBaseFieldExtensionSubgroup _root_.GlobalClassFieldTheory.Reciprocity.instMonoidClassGroupRatSubtypeSeparableClosureMemIntermediateField _root_.GlobalClassFieldTheory.Reciprocity.rationalAbstractRelativeClassGroupCommGroup _root_.GlobalClassFieldTheory.Reciprocity.rationalAbstractRelativeClassGroupMul _root_.GlobalClassFieldTheory.Reciprocity.rationalAbstractRelativeClassGroupMulOneClass _root_.GlobalClassFieldTheory.Reciprocity.rationalAbstractTowerClassGroupCommGroup _root_.GlobalClassFieldTheory.Reciprocity.rationalAbstractTowerClassGroupMul _root_.GlobalClassFieldTheory.Reciprocity.rationalAbstractTowerClassGroupMulOneClass _root_.relativeUnrestrictedSPlaceFactorCommGroup
attribute [-simp] _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.OAI.PrimeDegreePackets.ThetaConstruction.schwartzCM_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

/-!
# Away-from-p factors of a rational cyclotomic principal idele

For the cyclotomic level `p ^ k`, this file reindexes the actual chosen
finite-place Artin characters over rational primes.  Away from `p`, the
unramified formula makes the multiplicative support lie in the ordinary
finite prime factorization support of the principal rational number.

The final theorem separates the genuine `p`-factor from the explicit
away-from-`p` finite product.  The construction also applies to `k = 0`.
-/

open scoped Classical NumberField
open NumberField IsDedekindDomain

noncomputable section

namespace GlobalClassFieldTheory
namespace Reciprocity

open Function

attribute [local instance] GlobalClassFieldTheory.Reciprocity.instFactPrimeValNat_solutions_3
local instance instNeZeroNatVal_solutions_1_rded382_1 (m : ℕ+) : NeZero (m : ℕ) :=
  ⟨m.ne_zero⟩
attribute [local instance] GlobalClassFieldTheory.Reciprocity.rationalCyclotomicPrincipalPrimePowerNumberField
attribute [local instance] GlobalClassFieldTheory.Reciprocity.rationalCyclotomicPrincipalPrimePowerFiniteDimensional
attribute [local instance] GlobalClassFieldTheory.Reciprocity.rationalCyclotomicPrincipalPrimePowerIsGalois
attribute [local instance] GlobalClassFieldTheory.Reciprocity.rationalCyclotomicPrincipalPrimePowerIsAbelianGalois
noncomputable local instance
    rationalCyclotomicPrincipalLevelFiniteDimensional_rded382_1
    (m : ℕ+) :
    FiniteDimensional ℚ
      (KummerTheory.rationalCyclotomicLevel m) :=
  rationalCyclotomicPrincipalPrimeLevelFiniteDimensional m
noncomputable local instance
    rationalCyclotomicPrincipalLevelIsAbelianGalois_rded382_1
    (m : ℕ+) :
    IsAbelianGalois ℚ
      (KummerTheory.rationalCyclotomicLevel m) :=
  rationalCyclotomicPrincipalPrimeLevelIsAbelianGalois m
/-- At every positive `p`-power level, the finite-place character at `p`
is the direct reduction of the rational `p`-adic unit. -/
theorem rationalCyclotomicPrincipalFinitePlaceCharacter_at_prime_succ_formula
    (p : Nat.Primes) (n : ℕ) (x : ℚˣ) :
    rationalCyclotomicPrincipalFinitePlaceCharacter p (n + 1) x p =
      Units.map
        (PadicInt.toZModPow (p := p.1) (n + 1)).toMonoidHom
        (padicIntUnitOfRat p
          (rationalPrimeUnit x p : ℚ)
          (rationalPrimeUnit x p).ne_zero
          (padicValRat_rationalPrimeUnit x p)) := by
  have hwChosen :
      chosenFinitePlaceExtension
          (L := KummerTheory.rationalCyclotomicLevel
            ⟨p.1 ^ (n + 1), pow_pos p.2.pos (n + 1)⟩)
          ((Rat.HeightOneSpectrum.primesEquiv
            (R := 𝓞 ℚ)).symm p) =
        rationalCyclotomicChosenFinitePlaceExtension
          ⟨p.1 ^ (n + 1), pow_pos p.2.pos (n + 1)⟩
          ((Rat.HeightOneSpectrum.primesEquiv
            (R := 𝓞 ℚ)).symm p) := rfl
  let localArtin : Gal(KummerTheory.rationalCyclotomicLevel
      ⟨p.1 ^ (n + 1), pow_pos p.2.pos (n + 1)⟩ / ℚ) :=
    finitePlaceLocalToGlobalMonoidHom
      (K := ℚ)
      (L := KummerTheory.rationalCyclotomicLevel
        ⟨p.1 ^ (n + 1), pow_pos p.2.pos (n + 1)⟩)
      ((Rat.HeightOneSpectrum.primesEquiv (R := 𝓞 ℚ)).symm p)
      (rationalCyclotomicChosenFinitePlaceExtension
        ⟨p.1 ^ (n + 1), pow_pos p.2.pos (n + 1)⟩
        ((Rat.HeightOneSpectrum.primesEquiv (R := 𝓞 ℚ)).symm p))
      (finitePlaceLocalArtinMonoidHom
        (K := ℚ)
        (L := KummerTheory.rationalCyclotomicLevel
          ⟨p.1 ^ (n + 1), pow_pos p.2.pos (n + 1)⟩)
        ((Rat.HeightOneSpectrum.primesEquiv (R := 𝓞 ℚ)).symm p)
        (rationalCyclotomicChosenFinitePlaceExtension
          ⟨p.1 ^ (n + 1), pow_pos p.2.pos (n + 1)⟩
          ((Rat.HeightOneSpectrum.primesEquiv (R := 𝓞 ℚ)).symm p))
        (IdeleGroup.finiteComponent
          ((Rat.HeightOneSpectrum.primesEquiv (R := 𝓞 ℚ)).symm p)
          (IdeleGroup.principalIdele ℚ x)))
  let chosenArtin : Gal(KummerTheory.rationalCyclotomicLevel
      ⟨p.1 ^ (n + 1), pow_pos p.2.pos (n + 1)⟩ / ℚ) :=
    chosenFinitePlaceArtinMonoidHom
      (K := ℚ)
      (L := KummerTheory.rationalCyclotomicLevel
        ⟨p.1 ^ (n + 1), pow_pos p.2.pos (n + 1)⟩)
      ((Rat.HeightOneSpectrum.primesEquiv (R := 𝓞 ℚ)).symm p)
      (IdeleGroup.finiteComponent
        ((Rat.HeightOneSpectrum.primesEquiv (R := 𝓞 ℚ)).symm p)
        (IdeleGroup.principalIdele ℚ x))
  have hSpec :
      rationalCyclotomicPrincipalHeightOneArtinInput
          p (n + 1) x
          ((Rat.HeightOneSpectrum.primesEquiv
            (R := 𝓞 ℚ)).symm p) =
        chosenArtin := by
    dsimp only [chosenArtin]
    exact rationalCyclotomicPrincipalHeightOneArtinInput_spec
      p (n + 1) x
      ((Rat.HeightOneSpectrum.primesEquiv (R := 𝓞 ℚ)).symm p)
  have hFactor : chosenArtin = localArtin := by
    dsimp only [chosenArtin, localArtin]
    exact chosenFinitePlaceArtinMonoidHom_apply_factor_of_extension_eq
      (K := ℚ)
      (L := KummerTheory.rationalCyclotomicLevel
        ⟨p.1 ^ (n + 1), pow_pos p.2.pos (n + 1)⟩)
      ((Rat.HeightOneSpectrum.primesEquiv (R := 𝓞 ℚ)).symm p)
      (rationalCyclotomicChosenFinitePlaceExtension
        ⟨p.1 ^ (n + 1), pow_pos p.2.pos (n + 1)⟩
        ((Rat.HeightOneSpectrum.primesEquiv (R := 𝓞 ℚ)).symm p))
      hwChosen
      (IdeleGroup.finiteComponent
        ((Rat.HeightOneSpectrum.primesEquiv (R := 𝓞 ℚ)).symm p)
        (IdeleGroup.principalIdele ℚ x))
  have hLocal :
      localArtin = rationalCyclotomicPrincipalPrimeChosenArtin p n x := by
    dsimp only [localArtin]
    simp only [rationalCyclotomicPrincipalPrimeChosenArtin,
      rationalCyclotomicPrincipalPrimeModulus, RayClass.rationalPrime]
    rfl
  have hInput := hSpec.trans (hFactor.trans hLocal)
  have hCharacter := congrArg
    (fun sigma : Gal(
        KummerTheory.rationalCyclotomicLevel
          ⟨p.1 ^ (n + 1), pow_pos p.2.pos (n + 1)⟩ / ℚ) =>
      IsCyclotomicExtension.Rat.galEquivZMod
        (p.1 ^ (n + 1))
        (KummerTheory.rationalCyclotomicLevel
          ⟨p.1 ^ (n + 1), pow_pos p.2.pos (n + 1)⟩)
        (hK :=
          KummerTheory.rationalCyclotomicLevel_isCyclotomicExtension
            ⟨p.1 ^ (n + 1), pow_pos p.2.pos (n + 1)⟩)
        sigma)
    hInput
  calc
    rationalCyclotomicPrincipalFinitePlaceCharacter p (n + 1) x p = _ := by
      rw [rationalCyclotomicPrincipalFinitePlaceCharacter_spec,
        rationalCyclotomicPrincipalHeightOneCharacter]
    _ = _ := hCharacter
    _ = Units.map
        (PadicInt.toZModPow (p := p.1) (n + 1)).toMonoidHom
        (padicIntUnitOfRat p
          (rationalPrimeUnit x p : ℚ)
          (rationalPrimeUnit x p).ne_zero
          (padicValRat_rationalPrimeUnit x p)) :=
      galEquivZMod_chosenFinitePlaceArtinMonoidHom_principal_at_prime p n x

/-- Away from `p`, the chosen finite-place character is the inverse
Frobenius power determined by the rational `q`-adic valuation. -/
theorem rationalCyclotomicPrincipalFinitePlaceCharacter_of_ne
    (p q : Nat.Primes) (hqp : q ≠ p)
    (k : ℕ) (x : ℚˣ) :
    rationalCyclotomicPrincipalFinitePlaceCharacter p k x q =
      (ZMod.unitOfCoprime q.1
        (q.2.coprime_iff_not_dvd.mpr
          (rationalPrime_not_dvd_pow_of_ne q p hqp k))) ^
        (-padicValRat q.1 (x : ℚ)) := by
  have hprime :
      RayClass.rationalPrime q =
        ((Rat.HeightOneSpectrum.primesEquiv
          (R := 𝓞 ℚ)).symm q) := by
    change
      (Rat.HeightOneSpectrum.primesEquiv
          (R := 𝓞 ℚ)).symm q =
        (Rat.HeightOneSpectrum.primesEquiv
          (R := 𝓞 ℚ)).symm q
    rfl
  rw [rationalCyclotomicPrincipalFinitePlaceCharacter_spec,
    rationalCyclotomicPrincipalHeightOneCharacter_spec, ← hprime]
  exact
    galEquivZMod_chosenFinitePlaceArtinMonoidHom_principal_of_not_dvd
      ⟨p.1 ^ k, pow_pos p.2.pos k⟩ q
      (rationalPrime_not_dvd_pow_of_ne q p hqp k) x

/-- A chosen finite-place Artin character outside the rational
prime-factorization support is genuinely trivial. -/
@[simp]
theorem
    rationalCyclotomicPrincipalFinitePlaceCharacter_eq_one_of_not_mem_support
    (p : Nat.Primes) (k : ℕ) (x : ℚˣ) (q : Nat.Primes)
    (hq :
      q ∉ rationalPrimeFactorizationPrimeSupport x p) :
    rationalCyclotomicPrincipalFinitePlaceCharacter p k x q = 1 := by
  have hqp : q ≠ p := by
    intro h
    subst q
    exact hq
      (mem_rationalPrimeFactorizationPrimeSupport x p)
  rw [rationalCyclotomicPrincipalFinitePlaceCharacter_of_ne
      p q hqp k x,
    padicValRat_eq_zero_of_not_mem_rationalPrimeFactorizationPrimeSupport
      x p q hq]
  simp only [neg_zero, zpow_zero]

/-- The actual rational principal finite-place characters have finite
multiplicative support, contained in the ordinary rational prime
factorization support. -/
theorem
    rationalCyclotomicPrincipalFinitePlaceCharacters_hasFiniteMulSupport
    (p : Nat.Primes) (k : ℕ) (x : ℚˣ) :
    HasFiniteMulSupport
      (rationalCyclotomicPrincipalFinitePlaceCharacter p k x) := by
  rw [HasFiniteMulSupport]
  apply
    (rationalPrimeFactorizationPrimeSupport x p).finite_toSet.subset
  intro q hq
  by_contra hqSupport
  exact hq
    (rationalCyclotomicPrincipalFinitePlaceCharacter_eq_one_of_not_mem_support
      p k x q hqSupport)

/-- The off-`p` finprod of the genuine chosen Artin characters is the
explicit finite product over the erased rational prime-factorization
support. -/
theorem
    rationalCyclotomicPrincipalAwayFinitePlaceCharacter_finprod_eq_factorizationProduct
    (p : Nat.Primes) (k : ℕ) (x : ℚˣ) :
    (∏ᶠ (q : Nat.Primes) (_ : q ≠ p),
      rationalCyclotomicPrincipalFinitePlaceCharacter p k x q) =
      ∏ q :
          ↥((rationalPrimeFactorizationPrimeSupport x p).erase p),
        (ZMod.unitOfCoprime q.1.1
          (q.1.2.coprime_iff_not_dvd.mpr
            (rationalPrime_not_dvd_pow_of_ne
              q.1 p (Finset.ne_of_mem_erase q.2) k))) ^
          (-padicValRat q.1.1 (x : ℚ)) := by
  let f : Nat.Primes → (ZMod (p.1 ^ k))ˣ :=
    rationalCyclotomicPrincipalFinitePlaceCharacter p k x
  have hfinprod :
      (∏ᶠ (q : Nat.Primes) (_ : q ≠ p), f q) =
        ∏ q ∈
            (rationalPrimeFactorizationPrimeSupport x p).erase p,
          f q := by
    apply finprod_cond_eq_prod_of_cond_iff
    intro q hq
    constructor
    · intro hqp
      rw [Finset.mem_erase]
      refine ⟨hqp, ?_⟩
      by_contra hqSupport
      exact hq
        (rationalCyclotomicPrincipalFinitePlaceCharacter_eq_one_of_not_mem_support
          p k x q hqSupport)
    · intro hqSupport
      exact (Finset.mem_erase.mp hqSupport).1
  calc
    (∏ᶠ (q : Nat.Primes) (_ : q ≠ p),
        rationalCyclotomicPrincipalFinitePlaceCharacter p k x q) =
        ∏ q ∈
            (rationalPrimeFactorizationPrimeSupport x p).erase p,
          f q := hfinprod
    _ =
        ∏ q :
            ↥((rationalPrimeFactorizationPrimeSupport x p).erase p),
          f q.1 := by
      exact
        (Finset.prod_coe_sort
          ((rationalPrimeFactorizationPrimeSupport x p).erase p)
          f).symm
    _ =
        ∏ q :
            ↥((rationalPrimeFactorizationPrimeSupport x p).erase p),
          (ZMod.unitOfCoprime q.1.1
            (q.1.2.coprime_iff_not_dvd.mpr
              (rationalPrime_not_dvd_pow_of_ne
                q.1 p (Finset.ne_of_mem_erase q.2) k))) ^
            (-padicValRat q.1.1 (x : ℚ)) := by
      apply Finset.prod_congr rfl
      intro q _
      change rationalCyclotomicPrincipalFinitePlaceCharacter p k x q.1 = _
      exact rationalCyclotomicPrincipalFinitePlaceCharacter_of_ne
        p q.1 (Finset.ne_of_mem_erase q.2) k x

/-- The direct rational `p`-unit character times the explicit inverse
away-from-`p` factorization product is the reduced rational sign. -/
theorem
    rationalPrimeUnitCharacter_mul_principalAwayFactorizationProduct_eq_sign
    (p : Nat.Primes) (k : ℕ) (x : ℚˣ) :
    Units.map (PadicInt.toZModPow k).toMonoidHom
          (padicIntUnitOfRat p (rationalPrimeUnit x p : ℚ)
            (rationalPrimeUnit x p).ne_zero
            (padicValRat_rationalPrimeUnit x p)) *
        ∏ q :
            ↥((rationalPrimeFactorizationPrimeSupport x p).erase p),
          (ZMod.unitOfCoprime q.1.1
            (q.1.2.coprime_iff_not_dvd.mpr
              (rationalPrime_not_dvd_pow_of_ne
                q.1 p (Finset.ne_of_mem_erase q.2) k))) ^
            (-padicValRat q.1.1 (x : ℚ)) =
      Units.map (PadicInt.toZModPow k).toMonoidHom
        (rationalSignPadicUnit x p) := by
  exact
    padicIntUnitOfRat_rationalPrimeUnit_mul_primeSupportInverseFactors_toZModPow
      x p k

theorem
    rationalCyclotomicPrincipalFinitePlaceCharacter_prime_mul_away_eq_namedFinprod
    (p : Nat.Primes) (k : ℕ) (x : ℚˣ) :
    rationalCyclotomicPrincipalFinitePlaceCharacter p k x p *
        (∏ᶠ (q : Nat.Primes) (_ : q ≠ p),
          rationalCyclotomicPrincipalFinitePlaceCharacter p k x q) =
      rationalCyclotomicPrincipalHeightOneCharacterFinprod p k x := by
  rw [mul_finprod_cond_ne p
    (rationalCyclotomicPrincipalFinitePlaceCharacters_hasFiniteMulSupport
      p k x)]
  calc
    (∏ᶠ q : Nat.Primes,
        rationalCyclotomicPrincipalFinitePlaceCharacter p k x q) =
        ∏ᶠ q : Nat.Primes,
          rationalCyclotomicPrincipalHeightOneCharacter p k x
            ((Rat.HeightOneSpectrum.primesEquiv
              (R := 𝓞 ℚ)).symm q) := by
      apply finprod_congr
      intro q
      exact rationalCyclotomicPrincipalFinitePlaceCharacter_spec p k x q
    _ = ∏ᶠ v : HeightOneSpectrum (𝓞 ℚ),
          rationalCyclotomicPrincipalHeightOneCharacter p k x v :=
      finprod_comp_equiv
        (Rat.HeightOneSpectrum.primesEquiv
          (R := 𝓞 ℚ)).symm
    _ = rationalCyclotomicPrincipalHeightOneCharacterFinprod p k x :=
      (rationalCyclotomicPrincipalHeightOneCharacterFinprod_eq_finprod
        p k x).symm

/-- Reindexing by `Rat.HeightOneSpectrum.primesEquiv` and separating the
distinguished prime identifies the height-one finprod with its genuine
`p`-factor times the off-`p` prime finprod. -/
theorem
    rationalCyclotomicPrincipalFinitePlaceCharacter_prime_mul_away_finprod
    (p : Nat.Primes) (k : ℕ) (x : ℚˣ) :
    rationalCyclotomicPrincipalFinitePlaceCharacter p k x p *
        (∏ᶠ (q : Nat.Primes) (_ : q ≠ p),
          rationalCyclotomicPrincipalFinitePlaceCharacter p k x q) =
      ∏ᶠ v : HeightOneSpectrum (𝓞 ℚ),
        IsCyclotomicExtension.Rat.galEquivZMod
          (p.1 ^ k)
          (KummerTheory.rationalCyclotomicLevel
            ⟨p.1 ^ k, pow_pos p.2.pos k⟩)
          (hK :=
            KummerTheory.rationalCyclotomicLevel_isCyclotomicExtension
              ⟨p.1 ^ k, pow_pos p.2.pos k⟩)
          (chosenFinitePlaceArtinMonoidHom
            (K := ℚ)
            (L :=
              KummerTheory.rationalCyclotomicLevel
                ⟨p.1 ^ k, pow_pos p.2.pos k⟩)
            v
            (IdeleGroup.finiteComponent v
              (IdeleGroup.principalIdele ℚ x))) := by
  exact
    (rationalCyclotomicPrincipalFinitePlaceCharacter_prime_mul_away_eq_namedFinprod
      p k x).trans
      (rationalCyclotomicPrincipalHeightOneCharacterFinprod_spec p k x)

/-- Exact source for the final principal-product calculation: the
height-one chosen Artin finprod is the genuine `p`-factor times the
explicit away-from-`p` rational factorization product. -/
theorem
    rationalCyclotomicPrincipalFinitePlaceCharacter_prime_mul_factorizationProduct
    (p : Nat.Primes) (k : ℕ) (x : ℚˣ) :
    rationalCyclotomicPrincipalFinitePlaceCharacter p k x p *
        (∏ q :
            ↥((rationalPrimeFactorizationPrimeSupport x p).erase p),
          (ZMod.unitOfCoprime q.1.1
            (q.1.2.coprime_iff_not_dvd.mpr
              (rationalPrime_not_dvd_pow_of_ne
                q.1 p (Finset.ne_of_mem_erase q.2) k))) ^
            (-padicValRat q.1.1 (x : ℚ))) =
      ∏ᶠ v : HeightOneSpectrum (𝓞 ℚ),
        IsCyclotomicExtension.Rat.galEquivZMod
          (p.1 ^ k)
          (KummerTheory.rationalCyclotomicLevel
            ⟨p.1 ^ k, pow_pos p.2.pos k⟩)
          (hK :=
            KummerTheory.rationalCyclotomicLevel_isCyclotomicExtension
              ⟨p.1 ^ k, pow_pos p.2.pos k⟩)
          (chosenFinitePlaceArtinMonoidHom
            (K := ℚ)
            (L :=
              KummerTheory.rationalCyclotomicLevel
                ⟨p.1 ^ k, pow_pos p.2.pos k⟩)
            v
            (IdeleGroup.finiteComponent v
              (IdeleGroup.principalIdele ℚ x))) := by
  rw [
    ←
      rationalCyclotomicPrincipalAwayFinitePlaceCharacter_finprod_eq_factorizationProduct
        p k x]
  exact
    rationalCyclotomicPrincipalFinitePlaceCharacter_prime_mul_away_finprod
      p k x

end Reciprocity
end GlobalClassFieldTheory
end
end

section
-- module Solutions.OAIQ244_DUKE.GlobalClassFieldTheory_Reciprocity_RationalCyclotomicPrincipalPrimeFactor
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 400000
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalIdeleClassDirectLimitMonoid _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.GlobalClassFieldTheory.Reciprocity.instMonoidClassGroupRatSubtypeSeparableClosureMemIntermediateField _root_.GlobalClassFieldTheory.Reciprocity.rationalAbstractRelativeClassGroupMulOneClass _root_.GlobalClassFieldTheory.Reciprocity.rationalAbstractTowerClassGroupMulOneClass
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

/-!
# The ramified prime factor of a rational cyclotomic principal idele

The level-zero factor is trivial.  At every positive level, the finite-place
character specification reduces the claim to the ramified chosen-Artin formula
proved in `RationalCyclotomicFinitePlaceArtin`.
-/

open scoped Classical

noncomputable section

namespace GlobalClassFieldTheory
namespace Reciprocity

local instance instFactPrimeValNat_solutions_4_rded382_1 (p : Nat.Primes) : Fact p.1.Prime :=
  ⟨p.2⟩
/-- The chosen finite-place factor at the ramified prime `p` is the direct
reduction of the rational `p`-adic unit. -/
theorem rationalCyclotomicPrincipalFinitePlaceCharacter_at_prime
    (p : Nat.Primes) (k : ℕ) (x : ℚˣ) :
    rationalCyclotomicPrincipalFinitePlaceCharacter p k x p =
      Units.map (PadicInt.toZModPow k).toMonoidHom
        (padicIntUnitOfRat p
          (rationalPrimeUnit x p : ℚ)
          (rationalPrimeUnit x p).ne_zero
          (padicValRat_rationalPrimeUnit x p)) := by
  cases k with
  | zero =>
      apply Units.ext
      change (_ : ZMod 1) = _
      exact Subsingleton.elim _ _
  | succ n =>
      exact
        rationalCyclotomicPrincipalFinitePlaceCharacter_at_prime_succ_formula
          p n x

end Reciprocity
end GlobalClassFieldTheory
end
end

section
-- module Solutions.OAIQ244_DUKE.GlobalClassFieldTheory_Reciprocity_RationalCyclotomicPrincipalProduct
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.GlobalClassFields.ConductorialSubgroup.finiteIndex _root_.GlobalClassFieldTheory.GlobalClassFields.bigHilbertClassFieldNormSubgroup_normal _root_.GlobalClassFieldTheory.GlobalClassFields.ideleClassNorm_rangeFiniteIndex _root_.GlobalClassFieldTheory.GlobalClassFields.smallHilbertClassFieldNormSubgroupFiniteIndex _root_.GlobalClassFieldTheory.Reciprocity.complexFourthRootField_finiteDimensional _root_.GlobalClassFieldTheory.Reciprocity.complexFourthRootField_isCyclotomic _root_.GlobalClassFieldTheory.Reciprocity.complexFourthRootField_numberField _root_.GlobalClassFieldTheory.Reciprocity.infinitePlaceComplexificationOverfield_finiteDimensional _root_.GlobalClassFieldTheory.Reciprocity.infinitePlaceComplexificationOverfield_numberField _root_.GlobalClassFieldTheory.Reciprocity.ramifiedInfinitePlaceRealFixedField_numberField _root_.GlobalClassFieldTheory.Reciprocity.rationalComplexificationCyclotomicField_isCMField _root_.GlobalClassFieldTheory.Reciprocity.rationalComplexificationCyclotomicField_isCyclotomicFour _root_.GlobalClassFieldTheory.Reciprocity.rationalIdeleClassDirectLimitMonoid _root_.GlobalClassFieldTheory.Reciprocity.rationalIntermediateFieldAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalIntermediateFieldNumberField _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalTowerClassGroupCommGroup _root_.GlobalClassFieldTheory.Reciprocity.rationalTowerClassGroupMul _root_.KummerTheory.nthRootsSubgroupFintype _root_.KummerTheory.primeCyclotomicBaseFiniteDimensional _root_.KummerTheory.primeCyclotomicBaseNumberField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.boundedRealFields_numberField _root_.OAI.PrimeDegreePackets.instTopologicalSpaceLocalAlgebra _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.labelPrime_fact _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.GlobalClassFieldTheory.GlobalClassFields.bigHilbertNormQuotient_finite _root_.GlobalClassFieldTheory.GlobalClassFields.bigHilbertNormSubgroup_finiteIndex _root_.GlobalClassFieldTheory.Reciprocity.instNumberFieldSubtypeSeparableClosureRatMemIntermediateFieldAbstractFixedFieldOfFiniteQuotientAlgEquivSubgroupBaseFieldExtensionSubgroup _root_.GlobalClassFieldTheory.Reciprocity.instMonoidClassGroupRatSubtypeSeparableClosureMemIntermediateField _root_.GlobalClassFieldTheory.Reciprocity.rationalAbstractRelativeClassGroupCommGroup _root_.GlobalClassFieldTheory.Reciprocity.rationalAbstractRelativeClassGroupMul _root_.GlobalClassFieldTheory.Reciprocity.rationalAbstractRelativeClassGroupMulOneClass _root_.GlobalClassFieldTheory.Reciprocity.rationalAbstractTowerClassGroupCommGroup _root_.GlobalClassFieldTheory.Reciprocity.rationalAbstractTowerClassGroupMul _root_.GlobalClassFieldTheory.Reciprocity.rationalAbstractTowerClassGroupMulOneClass
attribute [-simp] _root_.ClassFormation.DegreeData.finiteUnramifiedDegreeHom_mk _root_.ClassFormation.DegreeData.maximalUnramifiedFrobeniusPower_one _root_.ClassFormation.ValuationData.maximalUnramifiedNormResidue_degree _root_.GlobalClassFieldTheory.ClassFieldAxiom.actualPushoutNormQuotientMap_mk _root_.GlobalClassFieldTheory.ClassFieldAxiom.hasseNormDiagonal_mk _root_.GlobalClassFieldTheory.ClassFieldAxiom.sUnitEquivSupportedPrincipalIdeleSubgroup_coe _root_.GlobalClassFieldTheory.GlobalClassFields.ConductorialSubgroup.ideleClassQuotientEquivOfNarrowFiniteConductorsEqOfRayClassGroupCardsEqQuotientCards_mk _root_.GlobalClassFieldTheory.GlobalClassFields.ConductorialSubgroup.mem_fullConductorInfinitePart_iff _root_.GlobalClassFieldTheory.GlobalClassFields.ConductorialSubgroup.narrowFiniteConductorRayClassGroupEquivQuotientOfCardEq_mk _root_.GlobalClassFieldTheory.GlobalClassFields.ConductorialSubgroup.narrowFiniteConductorRayClassGroupToQuotient_mk _root_.GlobalClassFieldTheory.GlobalClassFields.bigHilbertClassFieldQuotientCongr_mk _root_.GlobalClassFieldTheory.GlobalClassFields.bigHilbertClassFieldQuotientEquivNarrowClassGroup_mk _root_.GlobalClassFieldTheory.GlobalClassFields.bigHilbertClassFieldQuotientToIdeleClassNormQuotient_mk _root_.GlobalClassFieldTheory.GlobalClassFields.bigHilbertClassFieldQuotientToSmallHilbertClassFieldQuotient_mk _root_.GlobalClassFieldTheory.GlobalClassFields.ideleClassNormQuotientTowerMap_mk _root_.GlobalClassFieldTheory.GlobalClassFields.narrowFiniteConductorRayClassGroupToIdeleClassNormQuotient_mk _root_.GlobalClassFieldTheory.GlobalClassFields.normQuotientEquivOfNarrowFiniteConductorsEqOfRayClassGroupCardsEqNormQuotientCards_mk _root_.GlobalClassFieldTheory.GlobalClassFields.realSignToBigHilbertClassFieldQuotient_apply _root_.GlobalClassFieldTheory.GlobalClassFields.realSignToNarrowClassKernel_apply _root_.GlobalClassFieldTheory.GlobalClassFields.smallHilbertClassFieldQuotientCongr_mk _root_.GlobalClassFieldTheory.GlobalClassFields.smallHilbertClassFieldQuotientEquivClassGroup_mk _root_.GlobalClassFieldTheory.GlobalClassFields.smallHilbertClassFieldQuotientToIdeleClassNormQuotient_mk _root_.GlobalClassFieldTheory.IdealClassFieldTheory.smallHilbertClassFieldIdeleExtensionMap_mk' _root_.GlobalClassFieldTheory.Reciprocity.cyclotomicZHatNormCompositeContinuous_apply _root_.GlobalClassFieldTheory.Reciprocity.cyclotomicZHatNormCompositeInMulNatRangeContinuous_apply _root_.GlobalClassFieldTheory.Reciprocity.globalNormClassFromIdele_principalIdele _root_.GlobalClassFieldTheory.Reciprocity.globalNormClassFromIdele_relativeIdeleNorm_eq_one _root_.GlobalClassFieldTheory.Reciprocity.mem_globalArtinFiniteSupport_iff _root_.GlobalClassFieldTheory.Reciprocity.normalizedCyclotomicZHatIdeleValueContinuousMul_apply _root_.GlobalClassFieldTheory.Reciprocity.normalizedCyclotomicZHatIdeleValueContinuous_apply _root_.GlobalClassFieldTheory.Reciprocity.rationalAbstractFixedFieldIdeleClassEquivFixed_coe _root_.GlobalClassFieldTheory.Reciprocity.rationalCyclotomicPadicCoordinate_apply _root_.GlobalClassFieldTheory.Reciprocity.rationalCyclotomicZHatIdeleValueContinuousAdd_apply _root_.GlobalClassFieldTheory.Reciprocity.rationalCyclotomicZHatIdeleValueReduction_apply _root_.GlobalClassFieldTheory.Reciprocity.rationalIntermediateIdeleClassEquivGaloisFixed_coe _root_.IdeleClassGroup.normOneNorm_apply _root_.IdeleGroup.count_fractionalIdeal _root_.IdeleGroup.fractionalIdeal_finitePrimeIdele _root_.IdeleGroup.idealClass_finitePrimeIdele _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.OAI.PrimeDegreePackets.ThetaConstruction.schwartzCM_apply _root_.RayClass.signToNarrow_mk
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

/-!
# The rational cyclotomic principal-idele product formula

The ramified local factor at `p` is the direct `p`-adic unit character.
Every other finite local factor is the inverse Frobenius power prescribed
by the rational prime factorization.  Their product is the image of the
rational sign and therefore has square one.  Prime-power detection in the
torsion-free rational `ZHat`-extension removes this final sign ambiguity
and proves that every rational principal idele has trivial value.
-/

open scoped Classical NumberField
open NumberField IsDedekindDomain

noncomputable section

namespace GlobalClassFieldTheory
namespace Reciprocity

attribute [local instance] GlobalClassFieldTheory.Reciprocity.instFactPrimeValNat_solutions_5
attribute [local instance] GlobalClassFieldTheory.Reciprocity.rationalCyclotomicPrincipalProductPrimePowerNumberField
attribute [local instance] GlobalClassFieldTheory.Reciprocity.rationalCyclotomicPrincipalProductPrimePowerFiniteDimensional
attribute [local instance] GlobalClassFieldTheory.Reciprocity.rationalCyclotomicPrincipalProductPrimePowerIsAbelianGalois
noncomputable local instance
    rationalCyclotomicPrincipalProductLevelFiniteDimensional_rded382_1
    (m : ℕ+) :
    FiniteDimensional ℚ
      (KummerTheory.rationalCyclotomicLevel m) :=
  rationalCyclotomicPrincipalPrimeLevelFiniteDimensional m
noncomputable local instance
    rationalCyclotomicPrincipalProductLevelIsAbelianGalois_rded382_1
    (m : ℕ+) :
    IsAbelianGalois ℚ
      (KummerTheory.rationalCyclotomicLevel m) :=
  rationalCyclotomicPrincipalPrimeLevelIsAbelianGalois m
/-- The finite product of the genuine chosen local Artin characters of a
rational principal idele is the reduction of its rational sign. -/
theorem rationalCyclotomicPrincipalFinitePlaceProduct_eq_sign
    (p : Nat.Primes) (k : ℕ) (x : ℚˣ) :
    (∏ᶠ v : HeightOneSpectrum (𝓞 ℚ),
        IsCyclotomicExtension.Rat.galEquivZMod
          (p.1 ^ k)
          (KummerTheory.rationalCyclotomicLevel
            ⟨p.1 ^ k, pow_pos p.2.pos k⟩)
          (hK :=
            KummerTheory.rationalCyclotomicLevel_isCyclotomicExtension
              ⟨p.1 ^ k, pow_pos p.2.pos k⟩)
          (chosenFinitePlaceArtinMonoidHom
            (K := ℚ)
            (L :=
              KummerTheory.rationalCyclotomicLevel
                ⟨p.1 ^ k, pow_pos p.2.pos k⟩)
            v
            (IdeleGroup.finiteComponent v
              (IdeleGroup.principalIdele ℚ x)))) =
      Units.map (PadicInt.toZModPow k).toMonoidHom
        (rationalSignPadicUnit x p) := by
  exact
    (rationalCyclotomicPrincipalFinitePlaceCharacter_prime_mul_factorizationProduct
      p k x).symm.trans
      ((congrArg (fun u => u * _)
        (rationalCyclotomicPrincipalFinitePlaceCharacter_at_prime
          p k x)).trans
        (rationalPrimeUnitCharacter_mul_principalAwayFactorizationProduct_eq_sign
          p k x))

/-- At every prime-power cyclotomic coordinate, the global Artin
character of the finite part of a rational principal idele is exactly the
reduced rational sign. -/
theorem
    rationalCyclotomicGlobalArtin_character_toZModPow_principalFinitePart_eq_sign
    (p : Nat.Primes) (k : ℕ) (x : ℚˣ) :
    Units.map (PadicInt.toZModPow k).toMonoidHom
        (KummerTheory.rationalCyclotomicCharacterPrimeProduct
          (infiniteGlobalArtinMonoidHom
            ℚ KummerTheory.rationalCyclotomicField
            (rationalIdeleFinitePart
              (IdeleGroup.principalIdele ℚ x))) p) =
      Units.map (PadicInt.toZModPow k).toMonoidHom
        (rationalSignPadicUnit x p) := by
  exact
    (rationalCyclotomicGlobalArtin_character_toZModPow_finitePart_eq_finprod
      (IdeleGroup.principalIdele ℚ x) p k).trans
      (rationalCyclotomicPrincipalFinitePlaceProduct_eq_sign p k x)

/-- Every prime-power reduction of the finite principal cyclotomic
character has square one. -/
theorem
    rationalCyclotomicGlobalArtin_character_toZModPow_principalFinitePart_sq
    (p : Nat.Primes) (k : ℕ) (x : ℚˣ) :
    Units.map (PadicInt.toZModPow k).toMonoidHom
          (KummerTheory.rationalCyclotomicCharacterPrimeProduct
            (infiniteGlobalArtinMonoidHom
              ℚ KummerTheory.rationalCyclotomicField
              (rationalIdeleFinitePart
                (IdeleGroup.principalIdele ℚ x))) p) ^ 2 =
      1 := by
  exact
    (congrArg (fun u => u ^ 2)
      (rationalCyclotomicGlobalArtin_character_toZModPow_principalFinitePart_eq_sign
        p k x)).trans
      (rationalSignPadicUnit_toZModPow_sq x p k)

/-- The finite part of every rational principal idele has trivial value
in the actual rational cyclotomic `ZHat`-extension. -/
theorem rationalCyclotomicZHatIdeleValue_principalFinitePart_eq_one
    (x : ℚˣ) :
    rationalCyclotomicZHatIdeleValue
        (rationalIdeleFinitePart
          (IdeleGroup.principalIdele ℚ x)) =
      1 := by
  apply
    rationalCyclotomicZHatIdeleValue_eq_one_of_character_reductions
  intro p k
  exact
    rationalCyclotomicGlobalArtin_character_toZModPow_principalFinitePart_sq
      p k x

/-- The rational cyclotomic value kills every rational principal idele. -/
@[simp]
theorem rationalCyclotomicZHatIdeleValue_principalIdele_eq_one
    (x : ℚˣ) :
    rationalCyclotomicZHatIdeleValue
        (IdeleGroup.principalIdele ℚ x) =
      1 := by
  exact
    (rationalCyclotomicZHatIdeleValue_principalIdele_eq_finitePart x).trans
      (rationalCyclotomicZHatIdeleValue_principalFinitePart_eq_one x)

/-- The normalized cyclotomic `ZHat`-valuation kills principal ideles over
every number field.  This is the unconditional principal-idele endpoint
needed for descent to the idele class group. -/
@[simp]
theorem normalizedCyclotomicZHatIdeleValue_principalIdele_eq_zero
    (K : Type) [Field K] [NumberField K] (x : Kˣ) :
    normalizedCyclotomicZHatIdeleValue K
        (Additive.ofMul
          (IdeleGroup.principalIdele K x)) =
      0 := by
  exact
    (normalizedCyclotomicZHatIdeleValue_principalIdele_eq_zero_iff_finitePart
      K x).2
      (rationalCyclotomicZHatIdeleValue_principalFinitePart_eq_one
        (Units.map (Algebra.norm ℚ) x))

end Reciprocity
end GlobalClassFieldTheory
end
end

section
-- module Solutions.OAIQ244_DUKE.GlobalClassFieldTheory_Reciprocity_ComplexificationArtin_RationalComplexification
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.GlobalClassFields.ConductorialSubgroup.finiteIndex _root_.GlobalClassFieldTheory.GlobalClassFields.bigHilbertClassFieldNormSubgroup_normal _root_.GlobalClassFieldTheory.GlobalClassFields.ideleClassNorm_rangeFiniteIndex _root_.GlobalClassFieldTheory.GlobalClassFields.smallHilbertClassFieldNormSubgroupFiniteIndex _root_.GlobalClassFieldTheory.Reciprocity.infinitePlaceComplexificationOverfield_finiteDimensional _root_.GlobalClassFieldTheory.Reciprocity.infinitePlaceComplexificationOverfield_finiteDimensional_over_extension _root_.GlobalClassFieldTheory.Reciprocity.infinitePlaceComplexificationOverfield_numberField _root_.GlobalClassFieldTheory.Reciprocity.ramifiedInfinitePlaceOverextension_isAbelianGalois _root_.GlobalClassFieldTheory.Reciprocity.ramifiedInfinitePlaceRealFixedField_algebra _root_.GlobalClassFieldTheory.Reciprocity.ramifiedInfinitePlaceRealFixedField_numberField _root_.GlobalClassFieldTheory.Reciprocity.ramifiedInfinitePlaceRealFixedField_ratScalarTower _root_.GlobalClassFieldTheory.Reciprocity.ramifiedInfinitePlaceRealFixedField_scalarTower _root_.GlobalClassFieldTheory.Reciprocity.rationalIdeleClassDirectLimitMonoid _root_.GlobalClassFieldTheory.Reciprocity.rationalIntermediateFieldAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalIntermediateFieldNumberField _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalTowerClassGroupCommGroup _root_.GlobalClassFieldTheory.Reciprocity.rationalTowerClassGroupMul _root_.KummerTheory.primeCyclotomicBaseFiniteDimensional _root_.KummerTheory.primeCyclotomicBaseIsGalois _root_.KummerTheory.primeCyclotomicBaseNumberField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.boundedRealFields_numberField _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.GlobalClassFieldTheory.GlobalClassFields.bigHilbertNormQuotient_finite _root_.GlobalClassFieldTheory.GlobalClassFields.bigHilbertNormSubgroup_finiteIndex _root_.GlobalClassFieldTheory.Reciprocity.instNumberFieldSubtypeSeparableClosureRatMemIntermediateFieldAbstractFixedFieldOfFiniteQuotientAlgEquivSubgroupBaseFieldExtensionSubgroup _root_.GlobalClassFieldTheory.Reciprocity.instMonoidClassGroupRatSubtypeSeparableClosureMemIntermediateField _root_.GlobalClassFieldTheory.Reciprocity.rationalAbstractRelativeClassGroupCommGroup _root_.GlobalClassFieldTheory.Reciprocity.rationalAbstractRelativeClassGroupMul _root_.GlobalClassFieldTheory.Reciprocity.rationalAbstractRelativeClassGroupMulOneClass _root_.GlobalClassFieldTheory.Reciprocity.rationalAbstractTowerClassGroupCommGroup _root_.GlobalClassFieldTheory.Reciprocity.rationalAbstractTowerClassGroupMul _root_.GlobalClassFieldTheory.Reciprocity.rationalAbstractTowerClassGroupMulOneClass
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

local instance rationalComplexificationPrimeFact_rded382_1 :
    Fact rationalComplexificationPrime.1.Prime :=
  ⟨rationalComplexificationPrime.2⟩
attribute [local instance] GlobalClassFieldTheory.Reciprocity.rationalComplexificationPrimeSquareNeZero
attribute [local instance] GlobalClassFieldTheory.Reciprocity.rationalComplexificationCyclotomicField_finiteDimensional
attribute [local instance] GlobalClassFieldTheory.Reciprocity.rationalComplexificationCyclotomicField_numberField
attribute [local instance] GlobalClassFieldTheory.Reciprocity.rationalComplexificationCyclotomicField_isAbelianGalois
/-- The real coordinate of the infinite component of a rational principal
idele is the original rational number. -/
theorem
    rationalPrincipalInfiniteComponent_realCoordinate
    (x : ℚˣ) :
    InfinitePlace.Completion.ringEquivRealOfIsReal
        Rat.isReal_infinitePlace
        ((IdeleGroup.infiniteComponent
          Rat.infinitePlace
          (IdeleGroup.principalIdele ℚ x) :
            Rat.infinitePlace.Completionˣ) :
          Rat.infinitePlace.Completion) =
      (x : ℚ) := by
  rw [InfinitePlace.Completion.ringEquivRealOfIsReal_apply]
  rw [IdeleGroup.infiniteComponent_principalIdele]
  rw [InfinitePlace.Completion.extensionEmbeddingOfIsReal_coe]
  simp only [WithAbs.equiv_apply, eq_ratCast]

/-- A rational principal idele with positive numerator has trivial
infinite Artin factor in the rational complexification. -/
theorem
    rationalComplexificationPrincipalInfiniteArtin_eq_one_of_num_pos
    (x : ℚˣ) (hx : 0 < (x : ℚ).num) :
    chosenInfinitePlaceArtinMonoidHom
        (K := ℚ)
        (L := rationalComplexificationCyclotomicField)
        Rat.infinitePlace
        (IdeleGroup.infiniteComponent
          Rat.infinitePlace
          (IdeleGroup.principalIdele ℚ x)) =
      1 := by
  apply
    chosenInfinitePlaceArtinMonoidHom_eq_one_of_real_pos
      (K := ℚ)
      (L := rationalComplexificationCyclotomicField)
      Rat.infinitePlace Rat.isReal_infinitePlace
  rw [rationalPrincipalInfiniteComponent_realCoordinate]
  exact_mod_cast Rat.num_pos.mp hx

/-- A rational principal idele with negative numerator has nontrivial
infinite Artin factor in the rational complexification. -/
theorem
    rationalComplexificationPrincipalInfiniteArtin_ne_one_of_num_neg
    (x : ℚˣ) (hx : (x : ℚ).num < 0) :
    chosenInfinitePlaceArtinMonoidHom
        (K := ℚ)
        (L := rationalComplexificationCyclotomicField)
        Rat.infinitePlace
        (IdeleGroup.infiniteComponent
          Rat.infinitePlace
          (IdeleGroup.principalIdele ℚ x)) ≠
      1 := by
  let E := rationalComplexificationCyclotomicField
  let v := Rat.infinitePlace
  let w := chosenInfinitePlaceAbove (L := E) v
  have hw :
      w.comap (algebraMap ℚ E) = v :=
    chosenInfinitePlaceAbove_comap (L := E) v
  let : w.1.LiesOver v.1 :=
    ⟨congrArg (fun q : InfinitePlace ℚ => q.1) hw⟩
  intro htrivial
  have hnorm :
      IdeleGroup.infiniteComponent v
          (IdeleGroup.principalIdele ℚ x) ∈
        infiniteTensorNormSubgroup
          (K := ℚ) (L := E) v := by
    rw [← chosenInfinitePlaceArtinMonoidHom_ker
      (K := ℚ) (L := E) v]
    exact htrivial
  rw [infiniteTensorNormSubgroup_eq_localNormSubgroup
    (K := ℚ) (L := E) v w hw] at hnorm
  obtain ⟨z, hz⟩ := hnorm
  have hpositive :=
    infinitePlace_normUnits_real_complex_pos
      (K := ℚ) v w hw
      Rat.isReal_infinitePlace
      rationalComplexification_chosenInfinitePlace_isRamified.isComplex
      z
  rw [hz] at hpositive
  rw [rationalPrincipalInfiniteComponent_realCoordinate] at hpositive
  have hxReal : (((x : ℚ) : ℝ) ≤ 0) := by
    exact_mod_cast (Rat.num_neg.mp hx).le
  exact (not_lt_of_ge hxReal) hpositive

/-- The finite-place Artin product of a rational principal idele in
the fourth-root character is its rational sign unit. -/
theorem rationalComplexificationFiniteArtin_character
    (x : ℚˣ) :
    rationalComplexificationCharacter
        (∏ᶠ v : HeightOneSpectrum (𝓞 ℚ),
          chosenFinitePlaceArtinMonoidHom
            (K := ℚ)
            (L := rationalComplexificationCyclotomicField)
            v
            (IdeleGroup.finiteComponent v
              (IdeleGroup.principalIdele ℚ x))) =
      Units.map (PadicInt.toZModPow 2).toMonoidHom
        (rationalSignPadicUnit x rationalComplexificationPrime) := by
  have hmap :=
    MonoidHom.map_finprod
      rationalComplexificationCharacter.toMonoidHom
      (finitePlaceArtinFactors_hasFiniteMulSupport
        (K := ℚ)
        (L := rationalComplexificationCyclotomicField)
        (IdeleGroup.principalIdele ℚ x))
  calc
    rationalComplexificationCharacter
          (∏ᶠ v : HeightOneSpectrum (𝓞 ℚ),
            chosenFinitePlaceArtinMonoidHom
              (K := ℚ)
              (L := rationalComplexificationCyclotomicField)
              v
              (IdeleGroup.finiteComponent v
                (IdeleGroup.principalIdele ℚ x))) =
        ∏ᶠ v : HeightOneSpectrum (𝓞 ℚ),
          rationalComplexificationCharacter
            (chosenFinitePlaceArtinMonoidHom
              (K := ℚ)
              (L := rationalComplexificationCyclotomicField)
              v
              (IdeleGroup.finiteComponent v
                (IdeleGroup.principalIdele ℚ x))) :=
      hmap
    _ = _ := by
      rw [← rationalCyclotomicPrincipalFinitePlaceProduct_eq_sign
        rationalComplexificationPrime 2 x]
      apply finprod_congr
      intro v
      rw [rationalComplexificationCharacter_apply]

end Reciprocity
end GlobalClassFieldTheory
end
end

section
-- module Solutions.OAIQ244_DUKE.GlobalClassFieldTheory_Reciprocity_CyclotomicIdeleClassValuation
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.GlobalClassFields.ConductorialSubgroup.finiteIndex _root_.GlobalClassFieldTheory.GlobalClassFields.bigHilbertClassFieldNormSubgroup_normal _root_.GlobalClassFieldTheory.GlobalClassFields.finiteAbelianSubextensionAbstractRelativeFixedFieldFiniteDimensional _root_.GlobalClassFieldTheory.GlobalClassFields.finiteAbelianSubextensionAbstractRelativeFixedFieldIsAbelianGalois _root_.GlobalClassFieldTheory.GlobalClassFields.ideleClassNorm_rangeFiniteIndex _root_.GlobalClassFieldTheory.GlobalClassFields.smallHilbertClassFieldNormSubgroupFiniteIndex _root_.GlobalClassFieldTheory.Reciprocity.complexFourthRootField_numberField _root_.GlobalClassFieldTheory.Reciprocity.infinitePlaceComplexificationOverfield_numberField _root_.GlobalClassFieldTheory.Reciprocity.ramifiedInfinitePlaceRealFixedField_numberField _root_.KummerTheory.DiscreteNthRootsSubgroup.instTopologicalSpaceSubtypeUnitsMemSubgroup _root_.KummerTheory.finite_finsupp_nsmulQuotient _root_.KummerTheory.finite_sUnit_nthPowerQuotient _root_.KummerTheory.primeCyclotomicBaseIsGalois _root_.KummerTheory.primeCyclotomicBaseNumberField _root_.LocalFieldTheory.DiscreteValuationField.finite_padicInt_finPi_nsmulQuotient _root_.LocalFieldTheory.DiscreteValuationField.finite_padicInt_pi_nsmulQuotient_of_coprime _root_.LocalFieldTheory.DiscreteValuationField.finite_valuationSubringUnits_nthPowerQuotient _root_.LocalFieldTheory.finite_multiplicative_nthPowerQuotient _root_.LocalFieldTheory.finite_nsmulAddQuotient_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.boundedRealFields_finite _root_.OAI.PrimeDegreePackets.boundedRealFields_numberField _root_.OAI.PrimeDegreePackets.completedMaximalOrderCompactSpace _root_.OAI.PrimeDegreePackets.instT2SpaceLocalAlgebra _root_.OAI.PrimeDegreePackets.instTopologicalSpaceLocalAlgebra _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.OAI.PrimeDegreePackets.xT2Space _root_.GlobalClassFieldTheory.GlobalClassFields.bigHilbertNormQuotient_finite _root_.GlobalClassFieldTheory.GlobalClassFields.bigHilbertNormSubgroup_finiteIndex _root_.GlobalClassFieldTheory.GlobalClassFields.narrowClassGroup_finite _root_.cyclicPrimeDegreeIntermediate_isGalois
attribute [-simp] _root_.ClassFormation.DegreeData.finiteUnramifiedDegreeHom_mk _root_.ClassFormation.DegreeData.maximalUnramifiedFrobeniusPower_one _root_.ClassFormation.FiniteAbelianSubextension.normSubgroupMap_val _root_.ClassFormation.FiniteGaloisSubextension.classFieldCandidate_field _root_.ClassFormation.ValuationData.maximalUnramifiedNormResidue_degree _root_.ClassFormation.mem_normFilterBasis_iff _root_.GlobalClassFieldTheory.ClassFieldAxiom.actualPushoutNormQuotientMap_mk _root_.GlobalClassFieldTheory.ClassFieldAxiom.hasseNormDiagonal_mk _root_.GlobalClassFieldTheory.ClassFieldAxiom.sUnitEquivSupportedPrincipalIdeleSubgroup_coe _root_.GlobalClassFieldTheory.GlobalClassFields.ConductorialSubgroup.ideleClassQuotientEquivOfNarrowFiniteConductorsEqOfRayClassGroupCardsEqQuotientCards_mk _root_.GlobalClassFieldTheory.GlobalClassFields.ConductorialSubgroup.mem_fullConductorInfinitePart_iff _root_.GlobalClassFieldTheory.GlobalClassFields.ConductorialSubgroup.narrowFiniteConductorRayClassGroupEquivQuotientOfCardEq_mk _root_.GlobalClassFieldTheory.GlobalClassFields.ConductorialSubgroup.narrowFiniteConductorRayClassGroupToQuotient_mk _root_.GlobalClassFieldTheory.GlobalClassFields.bigHilbertClassFieldQuotientCongr_mk _root_.GlobalClassFieldTheory.GlobalClassFields.bigHilbertClassFieldQuotientEquivNarrowClassGroup_mk _root_.GlobalClassFieldTheory.GlobalClassFields.bigHilbertClassFieldQuotientToIdeleClassNormQuotient_mk _root_.GlobalClassFieldTheory.GlobalClassFields.bigHilbertClassFieldQuotientToSmallHilbertClassFieldQuotient_mk _root_.GlobalClassFieldTheory.GlobalClassFields.ideleClassNormQuotientTowerMap_mk _root_.GlobalClassFieldTheory.GlobalClassFields.narrowFiniteConductorRayClassGroupToIdeleClassNormQuotient_mk _root_.GlobalClassFieldTheory.GlobalClassFields.normQuotientEquivOfNarrowFiniteConductorsEqOfRayClassGroupCardsEqNormQuotientCards_mk _root_.GlobalClassFieldTheory.GlobalClassFields.realSignToBigHilbertClassFieldQuotient_apply _root_.GlobalClassFieldTheory.GlobalClassFields.realSignToNarrowClassKernel_apply _root_.GlobalClassFieldTheory.GlobalClassFields.smallHilbertClassFieldQuotientCongr_mk _root_.GlobalClassFieldTheory.GlobalClassFields.smallHilbertClassFieldQuotientEquivClassGroup_mk _root_.GlobalClassFieldTheory.GlobalClassFields.smallHilbertClassFieldQuotientToIdeleClassNormQuotient_mk _root_.GlobalClassFieldTheory.IdealClassFieldTheory.smallHilbertClassFieldIdeleExtensionMap_mk' _root_.GlobalClassFieldTheory.Reciprocity.globalNormClassFromIdele_principalIdele _root_.GlobalClassFieldTheory.Reciprocity.globalNormClassFromIdele_relativeIdeleNorm_eq_one _root_.GlobalClassFieldTheory.Reciprocity.mem_globalArtinFiniteSupport_iff _root_.GlobalClassFieldTheory.Reciprocity.rationalCyclotomicPadicCoordinate_apply _root_.IdeleGroup.count_fractionalIdeal _root_.IdeleGroup.fractionalIdeal_finitePrimeIdele _root_.IdeleGroup.idealClass_finitePrimeIdele _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.OAI.PrimeDegreePackets.ThetaConstruction.schwartzCM_apply _root_.RayClass.signToNarrow_mk
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

/-!
# The cyclotomic valuation on idele classes

The cyclotomic idele value is trivial on principal ideles, so it descends
to the ordinary idele class group.  Its restriction to the compact
norm-one idele class group still has dense image in `ZHat`; compactness
therefore upgrades density to surjectivity.

For a number field `K`, the defining normalization gives the exact
identity

`f_K v_K(c) = v_ℚ(N_{K/ℚ} c)`.

Surjectivity of `v_K` then identifies the image of the actual
idele-class norm with `f_K ZHat`.  For the actual fixed field attached
to a finite abstract field, the already constructed cyclotomic
base-change theorem identifies `f_K` with the residue degree.  This
supplies the norm-range field of the concrete henselian valuation data.
-/

open scoped NumberField

noncomputable section

namespace GlobalClassFieldTheory
namespace Reciprocity

open ClassFormation
open KummerTheory

/-- Fix the canonical source-group dictionary before constructing the value maps
and their additive ranges. -/
@[instance_reducible]
noncomputable def cyclotomicValuationIdeleClassCommGroup
    (F : Type) [Field F] [NumberField F] :
    CommGroup (IdeleClassGroup F) :=
  QuotientGroup.Quotient.commGroup (IdeleGroup.principalSubgroup F)

attribute [local instance] cyclotomicValuationIdeleClassCommGroup

/-- Principal rational ideles lie in the kernel of the cyclotomic value. -/
theorem rationalCyclotomicZHatIdeleValue_principalSubgroup_le_ker :
    IdeleGroup.principalSubgroup ℚ ≤
      rationalCyclotomicZHatIdeleValue.toMonoidHom.ker := by
  rintro _ ⟨x, rfl⟩
  exact rationalCyclotomicZHatIdeleValue_principalIdele_eq_one x

/-- The rational cyclotomic value descended continuously through
`C_ℚ = I_ℚ / ℚˣ`. -/
noncomputable def rationalCyclotomicZHatIdeleClassValueContinuousMul :
    IdeleClassGroup ℚ →ₜ* Multiplicative ZHat :=
  ideleClassContinuousQuotientLift
    (IdeleGroup.principalSubgroup ℚ)
    rationalCyclotomicZHatIdeleValue
    rationalCyclotomicZHatIdeleValue_principalSubgroup_le_ker

/-- Evaluation of the descended rational value on an idele class
represented by an idele. -/
@[simp]
theorem rationalCyclotomicZHatIdeleClassValueContinuousMul_mk
    (a : IdeleGroup ℚ) :
    rationalCyclotomicZHatIdeleClassValueContinuousMul
        (QuotientGroup.mk'
          (IdeleGroup.principalSubgroup ℚ) a) =
      rationalCyclotomicZHatIdeleValue a :=
  ideleClassContinuousQuotientLift_mk
    (IdeleGroup.principalSubgroup ℚ)
    rationalCyclotomicZHatIdeleValue
    rationalCyclotomicZHatIdeleValue_principalSubgroup_le_ker a

/-- The rational cyclotomic value on idele classes, in continuous
additive notation. -/
noncomputable def rationalCyclotomicZHatIdeleClassValueContinuous :
    Additive (IdeleClassGroup ℚ) →ₜ+ ZHat where
  __ := MonoidHom.toAdditiveLeft
    rationalCyclotomicZHatIdeleClassValueContinuousMul.toMonoidHom
  continuous_toFun := continuous_toAdd.comp
    (rationalCyclotomicZHatIdeleClassValueContinuousMul.continuous_toFun.comp
      continuous_toMul)

/-- Evaluation of the additive rational class value on a representative. -/
@[simp]
theorem rationalCyclotomicZHatIdeleClassValueContinuous_mk
    (a : IdeleGroup ℚ) :
    rationalCyclotomicZHatIdeleClassValueContinuous
        (Additive.ofMul
          (QuotientGroup.mk'
            (IdeleGroup.principalSubgroup ℚ) a)) =
      Multiplicative.toAdd
        (rationalCyclotomicZHatIdeleValue a) := by
  change
    Multiplicative.toAdd
        (rationalCyclotomicZHatIdeleClassValueContinuousMul
          (QuotientGroup.mk'
            (IdeleGroup.principalSubgroup ℚ) a)) =
      Multiplicative.toAdd
        (rationalCyclotomicZHatIdeleValue a)
  rw [rationalCyclotomicZHatIdeleClassValueContinuousMul_mk]

variable (K : Type) [Field K] [NumberField K]

/-- Principal ideles lie in the kernel of the normalized cyclotomic value. -/
theorem
    normalizedCyclotomicZHatIdeleValue_principalSubgroup_le_ker :
    IdeleGroup.principalSubgroup K ≤
      (normalizedCyclotomicZHatIdeleValueContinuousMul K).toMonoidHom.ker := by
  rintro _ ⟨x, rfl⟩
  change
    normalizedCyclotomicZHatIdeleValue K
        (Additive.ofMul (IdeleGroup.principalIdele K x)) =
      0
  exact normalizedCyclotomicZHatIdeleValue_principalIdele_eq_zero K x

/-- The normalized cyclotomic value descended continuously through
`C_K = I_K / Kˣ`. -/
noncomputable def normalizedCyclotomicZHatIdeleClassValueContinuousMul :
    IdeleClassGroup K →ₜ* Multiplicative ZHat :=
  ideleClassContinuousQuotientLift
    (IdeleGroup.principalSubgroup K)
    (normalizedCyclotomicZHatIdeleValueContinuousMul K)
    (normalizedCyclotomicZHatIdeleValue_principalSubgroup_le_ker K)

/-- Evaluation of the normalized class value on an idele representative. -/
@[simp]
theorem normalizedCyclotomicZHatIdeleClassValueContinuousMul_mk
    (a : IdeleGroup K) :
    normalizedCyclotomicZHatIdeleClassValueContinuousMul K
        (QuotientGroup.mk'
          (IdeleGroup.principalSubgroup K) a) =
      Multiplicative.ofAdd
        (normalizedCyclotomicZHatIdeleValue K
          (Additive.ofMul a)) := by
  exact
    ideleClassContinuousQuotientLift_mk
      (IdeleGroup.principalSubgroup K)
      (normalizedCyclotomicZHatIdeleValueContinuousMul K)
      (normalizedCyclotomicZHatIdeleValue_principalSubgroup_le_ker K) a

/-- The normalized cyclotomic value on idele classes, in continuous
additive notation. -/
noncomputable def normalizedCyclotomicZHatIdeleClassValueContinuous :
    Additive (IdeleClassGroup K) →ₜ+ ZHat where
  __ := MonoidHom.toAdditiveLeft
    (normalizedCyclotomicZHatIdeleClassValueContinuousMul K).toMonoidHom
  continuous_toFun := continuous_toAdd.comp
    ((normalizedCyclotomicZHatIdeleClassValueContinuousMul K).continuous_toFun.comp
      continuous_toMul)

/-- Evaluation of the normalized additive class value on a representative. -/
@[simp]
theorem normalizedCyclotomicZHatIdeleClassValueContinuous_mk
    (a : IdeleGroup K) :
    normalizedCyclotomicZHatIdeleClassValueContinuous K
        (Additive.ofMul
          (QuotientGroup.mk'
            (IdeleGroup.principalSubgroup K) a)) =
      normalizedCyclotomicZHatIdeleValue K
        (Additive.ofMul a) := by
  change
    Multiplicative.toAdd
        (normalizedCyclotomicZHatIdeleClassValueContinuousMul K
          (QuotientGroup.mk'
            (IdeleGroup.principalSubgroup K) a)) =
      normalizedCyclotomicZHatIdeleValue K
        (Additive.ofMul a)
  rw [normalizedCyclotomicZHatIdeleClassValueContinuousMul_mk]
  rfl

/-- The descended rational class value has dense image already on the
compact norm-one idele class group. -/
theorem
    rationalCyclotomicZHatIdeleClassValue_normOne_denseRange :
    DenseRange
      (fun c : IdeleClassGroup.normOneSubgroup (K := ℚ) =>
        rationalCyclotomicZHatIdeleClassValueContinuous
          (Additive.ofMul (c : IdeleClassGroup ℚ))) := by
  have hToAdd :
      Function.Surjective
        (Multiplicative.toAdd :
          Multiplicative ZHat → ZHat) :=
    fun z => ⟨Multiplicative.ofAdd z, rfl⟩
  have hidele :
      DenseRange
        (fun b : IdeleGroup.normOneSubgroup (K := ℚ) =>
          Multiplicative.toAdd
            (rationalCyclotomicZHatIdeleValue
              (b : IdeleGroup ℚ))) :=
    hToAdd.denseRange.comp
      rationalCyclotomicZHatIdeleValue_normOne_denseRange
      continuous_toAdd
  apply hidele.mono
  rintro z ⟨b, rfl⟩
  let c : IdeleClassGroup.normOneSubgroup (K := ℚ) :=
    ⟨QuotientGroup.mk'
        (IdeleGroup.principalSubgroup ℚ)
        (b : IdeleGroup ℚ),
      (IdeleClassGroup.mk_mem_normOneSubgroup_iff
        (b : IdeleGroup ℚ)).2 b.2⟩
  refine ⟨c, ?_⟩
  simp only [c,
    rationalCyclotomicZHatIdeleClassValueContinuous_mk]

/-- Compactness upgrades the dense rational norm-one image to
surjectivity. -/
theorem
    rationalCyclotomicZHatIdeleClassValue_normOne_surjective :
    Function.Surjective
      (fun c : IdeleClassGroup.normOneSubgroup (K := ℚ) =>
        rationalCyclotomicZHatIdeleClassValueContinuous
          (Additive.ofMul (c : IdeleClassGroup ℚ))) := by
  let f :=
    fun c : IdeleClassGroup.normOneSubgroup (K := ℚ) =>
      rationalCyclotomicZHatIdeleClassValueContinuous
        (Additive.ofMul (c : IdeleClassGroup ℚ))
  have hf : Continuous f := by
    exact
      (rationalCyclotomicZHatIdeleClassValueContinuous.continuous_toFun).comp
        (continuous_ofMul.comp continuous_subtype_val)
  have hclosed : IsClosed (Set.range f) :=
    (isCompact_range hf).isClosed
  have hdense : DenseRange f := by
    simpa only [f] using
      rationalCyclotomicZHatIdeleClassValue_normOne_denseRange
  intro z
  have hz : z ∈ closure (Set.range f) := by
    rw [hdense.closure_range]
    trivial
  rwa [hclosed.closure_eq] at hz

/-- The rational cyclotomic idele-class value is surjective. -/
theorem rationalCyclotomicZHatIdeleClassValue_surjective :
    Function.Surjective
      rationalCyclotomicZHatIdeleClassValueContinuous := by
  intro z
  obtain ⟨c, hc⟩ :=
    rationalCyclotomicZHatIdeleClassValue_normOne_surjective z
  exact ⟨Additive.ofMul (c : IdeleClassGroup ℚ), hc⟩

/-- The normalized class value has dense image already on the compact
norm-one idele class group. -/
theorem normalizedCyclotomicZHatIdeleClassValue_normOne_denseRange :
    DenseRange
      (fun c : IdeleClassGroup.normOneSubgroup (K := K) =>
        normalizedCyclotomicZHatIdeleClassValueContinuous K
          (Additive.ofMul (c : IdeleClassGroup K))) := by
  apply
    (normalizedCyclotomicZHatIdeleValue_normOne_denseRange K).mono
  rintro z ⟨b, rfl⟩
  let c : IdeleClassGroup.normOneSubgroup (K := K) :=
    ⟨QuotientGroup.mk'
        (IdeleGroup.principalSubgroup K)
        (b : IdeleGroup K),
      (IdeleClassGroup.mk_mem_normOneSubgroup_iff
        (b : IdeleGroup K)).2 b.2⟩
  refine ⟨c, ?_⟩
  simp only [c,
    normalizedCyclotomicZHatIdeleClassValueContinuous_mk]

/-- Compactness upgrades the dense normalized norm-one image to
surjectivity. -/
theorem normalizedCyclotomicZHatIdeleClassValue_normOne_surjective :
    Function.Surjective
      (fun c : IdeleClassGroup.normOneSubgroup (K := K) =>
        normalizedCyclotomicZHatIdeleClassValueContinuous K
          (Additive.ofMul (c : IdeleClassGroup K))) := by
  let f :=
    fun c : IdeleClassGroup.normOneSubgroup (K := K) =>
      normalizedCyclotomicZHatIdeleClassValueContinuous K
        (Additive.ofMul (c : IdeleClassGroup K))
  have hf : Continuous f := by
    exact
      (normalizedCyclotomicZHatIdeleClassValueContinuous K).continuous_toFun.comp
        (continuous_ofMul.comp continuous_subtype_val)
  have hclosed : IsClosed (Set.range f) :=
    (isCompact_range hf).isClosed
  have hdense : Dense (Set.range f) := by
    change DenseRange f
    simpa only [f] using
      (normalizedCyclotomicZHatIdeleClassValue_normOne_denseRange K)
  intro z
  have hz : z ∈ closure (Set.range f) := by
    rw [hdense.closure_eq]
    trivial
  rwa [hclosed.closure_eq] at hz

/-- The normalized cyclotomic idele-class value is surjective. -/
theorem normalizedCyclotomicZHatIdeleClassValue_surjective :
    Function.Surjective
      (normalizedCyclotomicZHatIdeleClassValueContinuous K) := by
  intro z
  obtain ⟨c, hc⟩ :=
    normalizedCyclotomicZHatIdeleClassValue_normOne_surjective K z
  exact ⟨Additive.ofMul (c : IdeleClassGroup K), hc⟩

/-- The normalized cyclotomic class value has full value group. -/
@[simp]
theorem normalizedCyclotomicZHatIdeleClassValue_range :
    (normalizedCyclotomicZHatIdeleClassValueContinuous K).toAddMonoidHom.range =
      (⊤ : AddSubgroup ZHat) :=
  AddMonoidHom.range_eq_top_of_surjective
    (normalizedCyclotomicZHatIdeleClassValueContinuous K).toAddMonoidHom
    (normalizedCyclotomicZHatIdeleClassValue_surjective K)

/-- The rational cyclotomic class value has full value group. -/
@[simp]
theorem rationalCyclotomicZHatIdeleClassValue_range :
    rationalCyclotomicZHatIdeleClassValueContinuous.toAddMonoidHom.range =
      (⊤ : AddSubgroup ZHat) :=
  AddMonoidHom.range_eq_top_of_surjective
    rationalCyclotomicZHatIdeleClassValueContinuous.toAddMonoidHom
    rationalCyclotomicZHatIdeleClassValue_surjective

/-- The defining normalized-value identity after descent to idele
classes:

`f_K v_K(c) = v_ℚ(N_{K/ℚ} c)`. -/
theorem
    cyclotomicZHatIntersectionDegree_nsmul_normalizedIdeleClassValue
    (c : Additive (IdeleClassGroup K)) :
    cyclotomicZHatIntersectionDegree K •
        normalizedCyclotomicZHatIdeleClassValueContinuous K c =
      rationalCyclotomicZHatIdeleClassValueContinuous
        (Additive.ofMul
          (_root_.ideleClassNorm ℚ K
            (Additive.toMul c))) := by
  obtain ⟨a, ha⟩ :=
    QuotientGroup.mk'_surjective
      (IdeleGroup.principalSubgroup K) (Additive.toMul c)
  have hc :
      c =
        Additive.ofMul
          (QuotientGroup.mk'
            (IdeleGroup.principalSubgroup K) a) := by
    apply Additive.ext
    exact ha.symm
  rw [hc, normalizedCyclotomicZHatIdeleClassValueContinuous_mk,
    toMul_ofMul,
    _root_.ideleClassNorm_mk,
    rationalCyclotomicZHatIdeleClassValueContinuous_mk]
  simpa only [cyclotomicZHatNormComposite_apply] using
    (cyclotomicZHatIntersectionDegree_nsmul_normalizedIdeleValue
      K (Additive.ofMul a))

/-- The rational cyclotomic value after the actual class norm
`N_{K/ℚ} : C_K → C_ℚ`. -/
noncomputable def rationalCyclotomicZHatIdeleClassNormComposite :
    Additive (IdeleClassGroup K) →+ ZHat :=
  (rationalCyclotomicZHatIdeleClassValueContinuous.toAddMonoidHom).comp
      (MonoidHom.toAdditive (_root_.ideleClassNorm ℚ K))

/-- Evaluation of the rational class-norm composite. -/
@[simp]
theorem rationalCyclotomicZHatIdeleClassNormComposite_apply
    (c : Additive (IdeleClassGroup K)) :
    rationalCyclotomicZHatIdeleClassNormComposite K c =
      rationalCyclotomicZHatIdeleClassValueContinuous
        (Additive.ofMul
          (_root_.ideleClassNorm ℚ K
            (Additive.toMul c))) :=
  rfl

/-- Exact image of the actual idele-class norm under the rational
cyclotomic value. -/
theorem rationalCyclotomicZHatIdeleClassNormComposite_range :
    (rationalCyclotomicZHatIdeleClassNormComposite K).range =
      nsmulImage (⊤ : AddSubgroup ZHat)
        (cyclotomicZHatIntersectionDegree K) := by
  ext z
  constructor
  · rintro ⟨c, rfl⟩
    rw [mem_nsmulImage_iff]
    refine
      ⟨normalizedCyclotomicZHatIdeleClassValueContinuous K c,
        AddSubgroup.mem_top _, ?_⟩
    simpa only [
      rationalCyclotomicZHatIdeleClassNormComposite_apply] using
      (cyclotomicZHatIntersectionDegree_nsmul_normalizedIdeleClassValue
        K c)
  · rw [mem_nsmulImage_iff]
    rintro ⟨x, _hx, hx⟩
    obtain ⟨c, hc⟩ :=
      normalizedCyclotomicZHatIdeleClassValue_surjective K x
    refine ⟨c, ?_⟩
    calc
      rationalCyclotomicZHatIdeleClassNormComposite K c =
          cyclotomicZHatIntersectionDegree K •
            normalizedCyclotomicZHatIdeleClassValueContinuous K c := by
        simpa only [
          rationalCyclotomicZHatIdeleClassNormComposite_apply] using
          (cyclotomicZHatIntersectionDegree_nsmul_normalizedIdeleClassValue
            K c).symm
      _ =
          cyclotomicZHatIntersectionDegree K • x := by
        rw [hc]
      _ = z := hx

/-- The rational cyclotomic class valuation transported to the
distinguished base fixed part of the absolute idele-class
representation. -/
noncomputable def rationalCyclotomicZHatValuation :
    KummerTheory.ambientFixedAddSubgroup
        rationalIdeleClassRepresentation
        (ClassFormation.baseField
          (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ)) →+
      ZHat :=
  (rationalCyclotomicZHatIdeleClassValueContinuous.toAddMonoidHom).comp
      rationalIdeleClassEquivBaseFixed.symm.toAddMonoidHom

/-- The transported rational cyclotomic valuation is surjective. -/
theorem rationalCyclotomicZHatValuation_surjective :
    Function.Surjective rationalCyclotomicZHatValuation := by
  intro z
  obtain ⟨c, hc⟩ :=
    rationalCyclotomicZHatIdeleClassValue_surjective z
  refine ⟨rationalIdeleClassEquivBaseFixed c, ?_⟩
  change
    rationalCyclotomicZHatIdeleClassValueContinuous
        (rationalIdeleClassEquivBaseFixed.symm
          (rationalIdeleClassEquivBaseFixed c)) =
      z
  rw [rationalIdeleClassEquivBaseFixed.symm_apply_apply]
  exact hc

/-- The value group of the transported rational valuation is all of
`ZHat`. -/
@[simp]
theorem rationalCyclotomicZHatValuation_range :
    rationalCyclotomicZHatValuation.range =
      (⊤ : AddSubgroup ZHat) :=
  AddMonoidHom.range_eq_top_of_surjective
    rationalCyclotomicZHatValuation
    rationalCyclotomicZHatValuation_surjective

/-- Every integral profinite value belongs to the transported rational
cyclotomic valuation range. -/
theorem rationalCyclotomicZHatValuation_integer_mem_range
    (m : ℤ) :
    (Int.castRingHom ZHat) m ∈
      rationalCyclotomicZHatValuation.range := by
  rw [rationalCyclotomicZHatValuation_range]
  exact AddSubgroup.mem_top _

/-- The canonical quotient map for the transported rational cyclotomic
valuation is bijective at every positive level. -/
theorem
    rationalCyclotomicZHatValuation_canonicalValueQuotientMap_bijective
    (n : ℕ) (hn : 0 < n) :
    Function.Bijective
      (canonicalValueQuotientMap
        rationalCyclotomicZHatValuation.range n hn) := by
  rw [rationalCyclotomicZHatValuation_range]
  exact canonicalValueQuotientMap_top_bijective n hn

section AbstractFixedFieldNormRange

variable
    (H : FiniteAbstractField
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))

local instance rationalCyclotomicFiniteAbstractFieldQuotientFinite :
    Finite
      ((ClassFormation.baseField
        (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ)).toSubgroup ⧸
        CyclicCohomology.extensionSubgroup
          (ClassFormation.baseField
            (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
          H.field (ClassFormation.le_baseField H.field)) :=
  H.finite

theorem rationalAbstractFixedFieldFiniteDimensional :
    FiniteDimensional ℚ
      (LocalClassFieldTheory.abstractFixedField
        ℚ (SeparableClosure ℚ) H.field) :=
  LocalClassFieldTheory.abstractFixedField_finiteDimensional
    ℚ (SeparableClosure ℚ) H.field H.finite

/-- Use the rational algebra structure expected by the imported finite-layer
API throughout this block.  Fixing it before the first finite-layer binder
keeps the parameter and every restriction target definitionally aligned. -/
noncomputable local instance
    cyclotomicIdeleClassValuation_rationalCyclotomicZHatFieldAlgebra_rded382_1 :
    Algebra ℚ rationalCyclotomicZHatField :=
  DivisionRing.toRatAlgebra
theorem rationalAbstractFixedFieldNumberField :
    NumberField
      (LocalClassFieldTheory.abstractFixedField
        ℚ (SeparableClosure ℚ) H.field) := by
  let : FiniteDimensional ℚ
      (LocalClassFieldTheory.abstractFixedField
        ℚ (SeparableClosure ℚ) H.field) :=
    rationalAbstractFixedFieldFiniteDimensional H
  exact NumberField.of_module_finite ℚ
    (LocalClassFieldTheory.abstractFixedField
      ℚ (SeparableClosure ℚ) H.field)

/-- For the actual number field fixed by a finite abstract field, the
actual idele-class norm has cyclotomic image equal to the
residue-degree multiples of `ZHat`. -/
theorem
    rationalCyclotomicZHatIdeleClassNormComposite_abstractFixedField_range :
    let F :=
      LocalClassFieldTheory.abstractFixedField
        ℚ (SeparableClosure ℚ) H.field
    let : FiniteDimensional ℚ F :=
      rationalAbstractFixedFieldFiniteDimensional H
    let : NumberField F :=
      rationalAbstractFixedFieldNumberField H
    (rationalCyclotomicZHatIdeleClassNormComposite F).range =
      nsmulImage (⊤ : AddSubgroup ZHat)
        (H.residueDegree rationalCyclotomicDegreeData : ℕ) := by
  intro F hfinite hnumberField
  clear hfinite
  have hdegree :=
    cyclotomicZHatIntersectionDegree_abstractFixedField_eq_residueDegree H
  rw [rationalCyclotomicZHatIdeleClassNormComposite_range]
  exact
    congrArg
      (fun n : ℕ => nsmulImage (⊤ : AddSubgroup ZHat) n)
      hdegree

/-- Exact norm-range identity after transport from the actual
fixed-field idele class group to the abstract fixed part. -/
theorem rationalCyclotomicZHatValuation_normToBase_range :
    (rationalCyclotomicZHatValuation.comp
      (normToBase rationalIdeleClassRepresentation H.field)).range =
      nsmulImage rationalCyclotomicZHatValuation.range
        (H.residueDegree rationalCyclotomicDegreeData : ℕ) := by
  let F :=
    LocalClassFieldTheory.abstractFixedField
      ℚ (SeparableClosure ℚ) H.field
  let : NumberField F :=
    rationalAbstractFixedFieldNumberField H
  let eF :=
    rationalAbstractFixedFieldIdeleClassEquivFixed H.field
  have heval
      (c : Additive (IdeleClassGroup F)) :
      (rationalCyclotomicZHatValuation.comp
          (normToBase rationalIdeleClassRepresentation H.field))
          (eF c) =
        rationalCyclotomicZHatIdeleClassNormComposite F c := by
    change
      rationalCyclotomicZHatIdeleClassValueContinuous
          (rationalIdeleClassEquivBaseFixed.symm
            (normToBase rationalIdeleClassRepresentation H.field
              (eF c))) =
        rationalCyclotomicZHatIdeleClassValueContinuous
          (Additive.ofMul
            (_root_.ideleClassNorm ℚ F
              (Additive.toMul c)))
    exact congrArg
      rationalCyclotomicZHatIdeleClassValueContinuous
      (rationalAbstractFixedFieldNormToBase_eq_ordinaryIdeleClassNorm
        H c)
  have htransport :
      (rationalCyclotomicZHatValuation.comp
        (normToBase rationalIdeleClassRepresentation H.field)).range =
        (rationalCyclotomicZHatIdeleClassNormComposite F).range := by
    ext z
    constructor
    · rintro ⟨a, rfl⟩
      obtain ⟨c, rfl⟩ := eF.surjective a
      exact ⟨c, (heval c).symm⟩
    · rintro ⟨c, rfl⟩
      exact ⟨eF c, heval c⟩
  calc
    (rationalCyclotomicZHatValuation.comp
        (normToBase rationalIdeleClassRepresentation H.field)).range =
        (rationalCyclotomicZHatIdeleClassNormComposite F).range :=
      htransport
    _ =
        nsmulImage (⊤ : AddSubgroup ZHat)
          (H.residueDegree rationalCyclotomicDegreeData : ℕ) := by
      simpa only [F] using
        (rationalCyclotomicZHatIdeleClassNormComposite_abstractFixedField_range
          H)
    _ =
        nsmulImage rationalCyclotomicZHatValuation.range
          (H.residueDegree rationalCyclotomicDegreeData : ℕ) := by
      rw [rationalCyclotomicZHatValuation_range]

end AbstractFixedFieldNormRange

/-- The concrete henselian valuation data on the absolute rational
idele-class representation, with cyclotomic degree data. -/
noncomputable def rationalCyclotomicIdeleClassValuationData :
    ValuationData
      rationalCyclotomicDegreeData
      rationalIdeleClassRepresentation where
  toAddMonoidHom :=
    rationalCyclotomicZHatValuation
  integers_mem :=
    rationalCyclotomicZHatValuation_integer_mem_range
  canonical_value_quotient_bijective :=
    rationalCyclotomicZHatValuation_canonicalValueQuotientMap_bijective
  norm_range := by
    intro H
    exact rationalCyclotomicZHatValuation_normToBase_range H

/-- Use the rational algebra structure expected by the imported finite-layer
API throughout this block.  Fixing it before the first finite-layer binder
keeps the parameter and every restriction target definitionally aligned. -/
noncomputable local instance
    cyclotomicIdeleClassValuation_rationalCyclotomicZHatFieldAlgebra_rded382_2 :
    Algebra ℚ rationalCyclotomicZHatField :=
  DivisionRing.toRatAlgebra
/-- Transporting an actual fixed-field idele class into the rational
absolute representation and then taking the base norm gives its
ordinary idele-class norm cyclotomic value. -/
theorem rationalCyclotomicZHatValuation_normToBase_fixed_apply
    (H : FiniteAbstractField
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
    (c : Additive
      (IdeleClassGroup
        (LocalClassFieldTheory.abstractFixedField
          ℚ (SeparableClosure ℚ) H.field))) :
    rationalCyclotomicZHatValuation
        (normToBase rationalIdeleClassRepresentation H.field
          (rationalAbstractFixedFieldIdeleClassEquivFixed H.field c)) =
      rationalCyclotomicZHatIdeleClassNormComposite
        (LocalClassFieldTheory.abstractFixedField
          ℚ (SeparableClosure ℚ) H.field) c := by
  let F :=
    LocalClassFieldTheory.abstractFixedField
      ℚ (SeparableClosure ℚ) H.field
  let : NumberField F :=
    rationalAbstractFixedFieldNumberField H
  change
    rationalCyclotomicZHatIdeleClassValueContinuous
        (rationalIdeleClassEquivBaseFixed.symm
          (normToBase rationalIdeleClassRepresentation H.field
            (rationalAbstractFixedFieldIdeleClassEquivFixed H.field c))) =
      rationalCyclotomicZHatIdeleClassValueContinuous
        (Additive.ofMul
          (_root_.ideleClassNorm ℚ F
            (Additive.toMul c)))
  exact congrArg
    rationalCyclotomicZHatIdeleClassValueContinuous
    (rationalAbstractFixedFieldNormToBase_eq_ordinaryIdeleClassNorm
      H c)

/-- Under the genuine fixed-field idele-class comparison, the
valuation used by abstract reciprocity is exactly the normalized
cyclotomic idele-class value of that fixed field. -/
@[simp]
theorem
    rationalCyclotomicIdeleClassValuationData_valuationAt_fixed_apply
    (H : FiniteAbstractField
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
    (c : Additive
      (IdeleClassGroup
        (LocalClassFieldTheory.abstractFixedField
          ℚ (SeparableClosure ℚ) H.field))) :
    ((rationalCyclotomicIdeleClassValuationData.valuationAt H
        (rationalAbstractFixedFieldIdeleClassEquivFixed H.field c) :
          rationalCyclotomicIdeleClassValuationData.valueGroup) :
        ZHat) =
      normalizedCyclotomicZHatIdeleClassValueContinuous
        (LocalClassFieldTheory.abstractFixedField
          ℚ (SeparableClosure ℚ) H.field) c := by
  have hdegree :=
    cyclotomicZHatIntersectionDegree_abstractFixedField_eq_residueDegree
      H
  let F :=
    LocalClassFieldTheory.abstractFixedField
      ℚ (SeparableClosure ℚ) H.field
  let : NumberField F :=
    rationalAbstractFixedFieldNumberField H
  apply
    zHatMulNat_injective
      (H.residueDegree rationalCyclotomicDegreeData).pos
  calc
    (H.residueDegree rationalCyclotomicDegreeData : ℕ) •
          ((rationalCyclotomicIdeleClassValuationData.valuationAt H
              (rationalAbstractFixedFieldIdeleClassEquivFixed H.field c) :
                rationalCyclotomicIdeleClassValuationData.valueGroup) :
            ZHat) =
        rationalCyclotomicIdeleClassValuationData.normCompositeAt H
          (rationalAbstractFixedFieldIdeleClassEquivFixed H.field c) := by
      exact
        rationalCyclotomicIdeleClassValuationData.residueDegree_nsmul_dividedAt
          H
          (rationalAbstractFixedFieldIdeleClassEquivFixed H.field c)
    _ =
        rationalCyclotomicZHatIdeleClassNormComposite F c :=
      rationalCyclotomicZHatValuation_normToBase_fixed_apply H c
    _ =
        cyclotomicZHatIntersectionDegree F •
          normalizedCyclotomicZHatIdeleClassValueContinuous F c := by
      simpa only [
        rationalCyclotomicZHatIdeleClassNormComposite_apply] using
        (cyclotomicZHatIntersectionDegree_nsmul_normalizedIdeleClassValue
          F c).symm
    _ =
        (H.residueDegree rationalCyclotomicDegreeData : ℕ) •
          normalizedCyclotomicZHatIdeleClassValueContinuous F c := by
      exact
        congrArg
          (fun n : ℕ =>
            n • normalizedCyclotomicZHatIdeleClassValueContinuous F c)
          hdegree

end Reciprocity
end GlobalClassFieldTheory
end
end

section
-- module Solutions.OAIQ244_DUKE.GlobalClassFieldTheory_Reciprocity_CyclotomicAbstractFixedFieldArtin
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.GlobalClassFields.bigHilbertClassFieldNormSubgroup_normal _root_.GlobalClassFieldTheory.GlobalClassFields.finiteAbelianSubextensionAbstractRelativeFixedFieldFiniteDimensional _root_.GlobalClassFieldTheory.GlobalClassFields.finiteAbelianSubextensionAbstractRelativeFixedFieldIsAbelianGalois _root_.KummerTheory.DiscreteNthRootsSubgroup.instTopologicalSpaceSubtypeUnitsMemSubgroup _root_.KummerTheory.primeCyclotomicBaseIsGalois _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.instTopologicalSpaceLocalAlgebra _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable
attribute [-simp] _root_.ClassFormation.FiniteAbelianSubextension.extensionQuotientMk_apply _root_.GlobalClassFieldTheory.Reciprocity.rationalCyclotomicPadicCoordinate_apply _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.OAI.PrimeDegreePackets.ThetaConstruction.schwartzCM_apply
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
/-- Cyclotomic field inertia is contained in the original abstract
field subgroup. -/
theorem rationalCyclotomicFieldInertia_le
    (H : ClosedSubgroup
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ)) :
    (rationalCyclotomicDegreeData.fieldInertia H).toSubgroup ≤
      H.toSubgroup := by
  intro σ hσ
  exact hσ.1

/-- Viewing cyclotomic field inertia inside its ambient field subgroup
gives exactly the kernel of normalized degree. -/
theorem extensionSubgroup_rationalCyclotomicFieldInertia
    (H : ClosedSubgroup
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ)) :
    CyclicCohomology.extensionSubgroup H
        (rationalCyclotomicDegreeData.fieldInertia H)
        (rationalCyclotomicFieldInertia_le H) =
      rationalCyclotomicDegreeData.fieldInertiaWithin H := by
  ext σ
  rw [
    mem_extensionSubgroup_iff,
    rationalCyclotomicDegreeData.mem_fieldInertiaWithin_iff,
    rationalCyclotomicDegreeData.mem_fieldInertia_iff]
  exact and_iff_right σ.2

/-- The actual Galois group of the cyclotomic maximal-unramified
extension of an abstract fixed field, in its normalized `ZHat`
coordinate. -/
noncomputable def abstractFixedFieldCyclotomicGalEquivZHat
    (H : FiniteAbstractField
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ)) :
    let hI :=
      rationalCyclotomicFieldInertia_le H.field
    Gal(
        LocalClassFieldTheory.abstractRelativeFixedField
          ℚ (SeparableClosure ℚ) hI /
        LocalClassFieldTheory.abstractFixedField
          ℚ (SeparableClosure ℚ) H.field) ≃*
      Multiplicative ZHat := by
  let hI :=
    rationalCyclotomicFieldInertia_le H.field
  let hnormal :
      (CyclicCohomology.extensionSubgroup H.field
        (rationalCyclotomicDegreeData.fieldInertia H.field)
        hI).Normal := by
    rw [extensionSubgroup_rationalCyclotomicFieldInertia]
    infer_instance
  let qField :
      H.field.toSubgroup ⧸
          CyclicCohomology.extensionSubgroup H.field
            (rationalCyclotomicDegreeData.fieldInertia H.field)
            hI ≃*
        Gal(
          LocalClassFieldTheory.abstractRelativeFixedField
            ℚ (SeparableClosure ℚ) hI /
          LocalClassFieldTheory.abstractFixedField
            ℚ (SeparableClosure ℚ) H.field) :=
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
  exact
    qField.symm.trans
      (qInertia.trans
        (rationalCyclotomicDegreeData.maximalUnramifiedDegreeEquiv
          (H.toFiniteResidueAbstractField
            rationalCyclotomicDegreeData)))

/-- On an absolute-Galois representative fixing the lower field, the
actual cyclotomic Galois coordinate is its normalized degree. -/
@[simp]
theorem abstractFixedFieldCyclotomicGalEquivZHat_extensionClass
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
    abstractFixedFieldCyclotomicGalEquivZHat H
        (LocalClassFieldTheory.abstractExtensionQuotientEquivGaloisGroup
          ℚ (SeparableClosure ℚ) H.field
          (rationalCyclotomicDegreeData.fieldInertia H.field)
          hI hnormal
          (QuotientGroup.mk σ)) =
      rationalCyclotomicDegreeData.normalizedDegree
        (H.toFiniteResidueAbstractField
          rationalCyclotomicDegreeData) σ := by
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
  change
    (rationalCyclotomicDegreeData.maximalUnramifiedDegreeEquiv
      (H.toFiniteResidueAbstractField
        rationalCyclotomicDegreeData))
      (QuotientGroup.quotientMulEquivOfEq
        (extensionSubgroup_rationalCyclotomicFieldInertia H.field)
        (qField.symm (qField (QuotientGroup.mk σ)))) =
      rationalCyclotomicDegreeData.normalizedDegree
        (H.toFiniteResidueAbstractField
          rationalCyclotomicDegreeData) σ
  rw [qField.symm_apply_apply]
  rfl

end Reciprocity
end GlobalClassFieldTheory
end
end

section
-- module Solutions.OAIQ244_DUKE.GlobalClassFieldTheory_Reciprocity_FinitePlaceCyclotomicFrobeniusLift
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalIntermediateFieldAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.KummerTheory.primeCyclotomicBaseIsGalois _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.instTopologicalSpaceLocalAlgebra _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable
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

local instance localInst_rded382_1 (p : Nat.Primes) : Fact p.1.Prime :=
  ⟨p.2⟩
local instance rationalCyclotomicFrobeniusLiftPrimePowerNumberField_rded382_1
    (p : Nat.Primes) (k : ℕ) :
    NumberField (KummerTheory.rationalCyclotomicLevel
      ⟨p.1 ^ k, pow_pos p.2.pos k⟩) :=
  KummerTheory.rationalCyclotomicLevel_numberField
    ⟨p.1 ^ k, pow_pos p.2.pos k⟩
local instance rationalCyclotomicFrobeniusLiftPrimePowerFiniteDimensional_rded382_1
    (p : Nat.Primes) (k : ℕ) :
    FiniteDimensional ℚ (KummerTheory.rationalCyclotomicLevel
      ⟨p.1 ^ k, pow_pos p.2.pos k⟩) :=
  rationalCyclotomicPrincipalPrimeLevelFiniteDimensional
    ⟨p.1 ^ k, pow_pos p.2.pos k⟩
local instance rationalCyclotomicFrobeniusLiftPrimePowerIsAbelianGalois_rded382_1
    (p : Nat.Primes) (k : ℕ) :
    IsAbelianGalois ℚ (KummerTheory.rationalCyclotomicLevel
      ⟨p.1 ^ k, pow_pos p.2.pos k⟩) :=
  rationalCyclotomicLevelIsAbelianGalois
    ⟨p.1 ^ k, pow_pos p.2.pos k⟩
noncomputable local instance
    rationalCyclotomicFrobeniusLiftLevelFiniteDimensional_rded382_1
    (m : ℕ+) :
    FiniteDimensional ℚ
      (KummerTheory.rationalCyclotomicLevel m) :=
  rationalCyclotomicPrincipalPrimeLevelFiniteDimensional m
noncomputable local instance
    rationalCyclotomicFrobeniusLiftLevelIsAbelianGalois_rded382_1
    (m : ℕ+) :
    IsAbelianGalois ℚ
      (KummerTheory.rationalCyclotomicLevel m) :=
  rationalCyclotomicLevelIsAbelianGalois m
variable
    {K L Ω : Type}
    [Field K] [Field L] [Field Ω]
    [Algebra K L] [Algebra L Ω] [Algebra K Ω]
    [IsScalarTower K L Ω] [Normal K L]

/-- The fixing subgroup of the internal `p`-primary field is exactly
the kernel of the `p`-adic cyclotomic coordinate. -/
theorem rationalCyclotomicPadicFieldWithinZHat_fixingSubgroup
    (p : Nat.Primes) :
    (rationalCyclotomicPadicFieldWithinZHat p).fixingSubgroup =
      (rationalCyclotomicPadicKernel p).toSubgroup := by
  exact
    InfiniteGalois.fixingSubgroup_fixedField
      (rationalCyclotomicPadicKernel p)

end Reciprocity
end GlobalClassFieldTheory
end
end


