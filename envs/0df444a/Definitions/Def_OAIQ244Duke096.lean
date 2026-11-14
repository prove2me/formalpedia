-- Prove2me | Definitions.Def_OAIQ244Duke096
-- name    : OAIQ244Duke096
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-14T02:11:31.453442+00:00
-- url     : https://prove2.me/theorems/39517503-a435-4e80-94cc-d270b07b0798
-- title:
--   Definitions bundle OAIQ244Duke096 of the split of OpenAI, Equidistribution of Prime-Degree Torus Packets with Arbitrary Local Type
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.DukePrimeDegree.prime_degree_packet_measure_equidistribution_unconditional` and `OAI.DukePrimeDegree.prime_degree_packet_measures_tendsto_haar_unconditional`, carved from OpenAI's openai/math development (OpenAI, *Equidistribution of Prime-Degree Torus Packets with Arbitrary Local Type*, OpenAI Math Release, September 24, 2026, result family 15, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 17 declarations of OpenAI's Lean: 3 definitions and 14 theorems. The definitions and types are `GlobalClassFieldTheory.Reciprocity.rationalCyclotomicArtinLocalArtin`, `GlobalClassFieldTheory.Reciprocity.rationalCyclotomicPadicFieldWithinZHat`, `GlobalClassFieldTheory.Reciprocity.rationalCyclotomicPadicKernel`.
--
--   **Sources.** They come from these modules of lean/OAI/NumberTheory, in whole or in part: `GlobalClassFieldTheory_Reciprocity_ComplexificationArtin_RationalComplexification`, `GlobalClassFieldTheory_Reciprocity_CyclotomicIdeleValue`, `GlobalClassFieldTheory_Reciprocity_CyclotomicPrincipalIdele`, `GlobalClassFieldTheory_Reciprocity_FinitePlaceCyclotomicFrobeniusLift`, `GlobalClassFieldTheory_Reciprocity_IdeleClassDirectLimitNormQuotient`, `GlobalClassFieldTheory_Reciprocity_RationalCyclotomicFinitePlaceArtin`, `GlobalClassFieldTheory_Reciprocity_RationalCyclotomicZHatRigidity`.
--
--   **Imports.** It imports the bundles `OAIQ244Duke094` and `OAIQ244Duke118` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ244Duke097`, `OAIQ244Duke099` and `OAIQ244Duke119`.
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
import Definitions.Def_OAIQ244Duke094
import Definitions.Def_OAIQ244Duke118

section
-- module Solutions.OAIQ244_DUKE.GlobalClassFieldTheory_Reciprocity_RationalCyclotomicFinitePlaceArtin
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.complexFourthRootField_finiteDimensional _root_.GlobalClassFieldTheory.Reciprocity.complexFourthRootField_isCyclotomic _root_.GlobalClassFieldTheory.Reciprocity.complexFourthRootField_numberField _root_.GlobalClassFieldTheory.Reciprocity.infinitePlaceComplexificationOverfield_algebra _root_.GlobalClassFieldTheory.Reciprocity.infinitePlaceComplexificationOverfield_baseAlgebra _root_.GlobalClassFieldTheory.Reciprocity.infinitePlaceComplexificationOverfield_finiteDimensional _root_.GlobalClassFieldTheory.Reciprocity.infinitePlaceComplexificationOverfield_numberField _root_.GlobalClassFieldTheory.Reciprocity.numberFieldCyclotomicZHatCompositum_algebra _root_.GlobalClassFieldTheory.Reciprocity.numberFieldCyclotomicZHatFiniteCompositum_algebra _root_.GlobalClassFieldTheory.Reciprocity.numberFieldCyclotomicZHatFiniteCompositum_finiteDimensional _root_.GlobalClassFieldTheory.Reciprocity.numberFieldCyclotomicZHatFiniteCompositum_numberField _root_.GlobalClassFieldTheory.Reciprocity.numberFieldCyclotomicZHatFiniteLayerInCompositum_finiteDimensional _root_.GlobalClassFieldTheory.Reciprocity.numberFieldCyclotomicZHatFiniteLayerInCompositum_numberField _root_.GlobalClassFieldTheory.Reciprocity.numberFieldCyclotomicZHatIntersection_finiteDimensional _root_.GlobalClassFieldTheory.Reciprocity.numberFieldCyclotomicZHatIntersection_numberField _root_.GlobalClassFieldTheory.Reciprocity.ramifiedInfinitePlaceRealFixedField_algebra _root_.GlobalClassFieldTheory.Reciprocity.ramifiedInfinitePlaceRealFixedField_numberField _root_.GlobalClassFieldTheory.Reciprocity.rationalComplexificationCyclotomicField_isCMField _root_.GlobalClassFieldTheory.Reciprocity.rationalComplexificationCyclotomicField_isCyclotomicFour _root_.GlobalClassFieldTheory.Reciprocity.rationalCyclotomicZHatField_isAbelianGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalIdeleClassDirectLimitMonoid _root_.GlobalClassFieldTheory.Reciprocity.rationalIdeleClassDirectLimitSMul _root_.GlobalClassFieldTheory.Reciprocity.rationalIntermediateFieldAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalIntermediateFieldNumberField _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.GlobalClassFieldTheory.Reciprocity.rationalTowerClassGroupMul _root_.KummerTheory.DiscreteNthRootsSubgroup.instTopologicalSpaceSubtypeUnitsMemSubgroup _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.KummerTheory.primeCyclotomicBaseFiniteDimensional _root_.KummerTheory.primeCyclotomicBaseIsGalois _root_.KummerTheory.primeCyclotomicBaseNumberField _root_.KummerTheory.rationalCyclotomicField_hasEnoughRootsOfUnity _root_.KummerTheory.rationalCyclotomicTorsionFixedField_isAbelianGalois _root_.KummerTheory.rationalCyclotomicTorsionFixedField_isGalois _root_.KummerTheory.rationalCyclotomicTorsionFixedField_isIntegral _root_.KummerTheory.rationalCyclotomicTorsionFixedField_normal _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.residueFieldZModAlgebra _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.boundedRealFields_numberField _root_.OAI.PrimeDegreePackets.instIsTopologicalRingLocalAlgebra _root_.OAI.PrimeDegreePackets.instTopologicalSpaceLocalAlgebra _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.GlobalClassFieldTheory.Reciprocity.instNumberFieldSubtypeSeparableClosureRatMemIntermediateFieldAbstractFixedFieldOfFiniteQuotientAlgEquivSubgroupBaseFieldExtensionSubgroup _root_.GlobalClassFieldTheory.Reciprocity.instMonoidClassGroupRatSubtypeSeparableClosureMemIntermediateField _root_.GlobalClassFieldTheory.Reciprocity.instSMulAlgEquivRatSeparableClosureClassGroupSubtypeMemIntermediateField _root_.GlobalClassFieldTheory.Reciprocity.rationalAbstractRelativeClassGroupMul _root_.GlobalClassFieldTheory.Reciprocity.rationalAbstractRelativeClassGroupMulOneClass _root_.GlobalClassFieldTheory.Reciprocity.rationalAbstractTowerClassGroupMul _root_.GlobalClassFieldTheory.Reciprocity.rationalAbstractTowerClassGroupMulOneClass _root_.cyclicPrimeDegreeIntermediate_isGalois
attribute [-simp] _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.OAI.PrimeDegreePackets.ThetaConstruction.schwartzCM_apply
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
noncomputable local instance rationalFinitePlaceBaseIsValuativeTopology_r253b09_1
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
    rationalCyclotomicArtinLocalizedIsUltrametricDist_r253b09_1
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
noncomputable abbrev rationalCyclotomicArtinLocalArtin
    (m : ℕ+) (q : Nat.Primes)
    (x : ((RayClass.rationalPrime q).adicCompletion ℚ)ˣ) :
    rationalCyclotomicArtinLocalizedField m q ≃ₐ[
      (rationalCyclotomicArtinBaseAbv q).Completion]
      rationalCyclotomicArtinLocalizedField m q :=
  finitePlaceLocalArtinMonoidHom
    (K := ℚ) (L := rationalCyclotomicArtinLevel m)
    (rationalCyclotomicArtinPlace q)
    (rationalCyclotomicArtinExtension m q) x

theorem rationalCyclotomicArtinLocalArtin_eq
    (m : ℕ+) (q : Nat.Primes)
    (x : ((RayClass.rationalPrime q).adicCompletion ℚ)ˣ) :
    rationalCyclotomicArtinLocalArtin m q x =
      @LocalClassFieldTheory.abelianLocalArtinMonoidHom
        (rationalCyclotomicArtinBaseAbv q).Completion
        (rationalCyclotomicArtinLocalizedField m q)
        (inferInstance : Field
          (rationalCyclotomicArtinBaseAbv q).Completion)
        (inferInstance : Field
          (rationalCyclotomicArtinLocalizedField m q))
        (finitePlaceLocalArtinLocalizedAlgebra
          (K := ℚ) (L := rationalCyclotomicArtinLevel m)
          (rationalCyclotomicArtinPlace q)
          (rationalCyclotomicArtinExtension m q))
        (finitePlaceLocalArtinCompletionValuativeRel
          (K := ℚ) (rationalCyclotomicArtinPlace q))
        (inferInstance : TopologicalSpace
          (rationalCyclotomicArtinBaseAbv q).Completion)
        (finitePlaceLocalArtinCompletionIsNonarchimedeanLocalField
          (K := ℚ) (rationalCyclotomicArtinPlace q))
        (finitePlaceLocalArtinFiniteDimensional
          (K := ℚ) (L := rationalCyclotomicArtinLevel m)
          (rationalCyclotomicArtinPlace q)
          (rationalCyclotomicArtinExtension m q))
        (finitePlaceLocalArtinIsAbelianGalois
          (K := ℚ) (L := rationalCyclotomicArtinLevel m)
          (rationalCyclotomicArtinPlace q)
          (rationalCyclotomicArtinExtension m q)
          (inferInstance : FiniteDimensional ℚ
            (rationalCyclotomicArtinLevel m)))
        (finitePlaceLocalArtinInput
          (K := ℚ) (rationalCyclotomicArtinPlace q) x) := by
  rfl

theorem rationalCyclotomicArtinResidueFieldCard
    (q : Nat.Primes) :
    Nat.card 𝓀[(rationalCyclotomicArtinBaseAbv q).Completion] = q.1 := by
  simpa [rationalCyclotomicArtinPlace,
    rationalCyclotomicArtinBaseAbv] using
    rationalFinitePlaceCompletion_residueField_card
      (rationalCyclotomicArtinPlace q)

theorem rationalCyclotomicArtinLocalFrobenius_apply_root
    (m : ℕ+) (q : Nat.Primes)
    (hq : ¬ q.1 ∣ (m : ℕ)) :
    rationalCyclotomicArtinLocalFrobenius m q hq
        (rationalCyclotomicLocalizedPrimitiveRoot
          m (rationalCyclotomicArtinPlace q)) =
      (rationalCyclotomicLocalizedPrimitiveRoot
        m (rationalCyclotomicArtinPlace q)) ^ q.1 := by
  let := rationalCyclotomicArtinUnramified m q hq
  have hRoot :
      IsPrimitiveRoot
        (rationalCyclotomicLocalizedPrimitiveRoot
          m (rationalCyclotomicArtinPlace q)) (m : ℕ) :=
    rationalCyclotomicLocalizedPrimitiveRoot_isPrimitiveRoot
      m (rationalCyclotomicArtinPlace q)
  have hCoprime :
      (Nat.card
        𝓀[(rationalCyclotomicArtinBaseAbv q).Completion]).Coprime
          (m : ℕ) := by
    rw [rationalCyclotomicArtinResidueFieldCard q]
    exact q.2.coprime_iff_not_dvd.mpr hq
  exact
    (arithmeticFrobeniusOfUnramifiedValuation_apply_primitiveRoot
      (rationalCyclotomicArtinBaseAbv q).Completion
      (rationalCyclotomicArtinLocalizedField m q)
      hRoot hCoprime).trans
      (congrArg
        (fun n : ℕ => (rationalCyclotomicLocalizedPrimitiveRoot
          m (rationalCyclotomicArtinPlace q)) ^ n)
        (rationalCyclotomicArtinResidueFieldCard q))

theorem rationalCyclotomicChosenArithmeticFrobenius_apply_root
    (m : ℕ+) (q : Nat.Primes)
    (hq : ¬ q.1 ∣ (m : ℕ)) :
    rationalCyclotomicChosenArithmeticFrobenius m q hq
        (rationalCyclotomicLevelPrimitiveRoot m) =
      rationalCyclotomicLevelPrimitiveRoot m ^ q.1 := by
  apply
    (AbsoluteValue.toAlgebraicLocalization
      (rationalCyclotomicArtinBaseAbv q)
      (rationalCyclotomicArtinExtension m q).1
      (rationalCyclotomicArtinExtension m q).2).injective
  have hLocalization :
      AbsoluteValue.toAlgebraicLocalization
        (rationalCyclotomicArtinBaseAbv q)
        (rationalCyclotomicArtinExtension m q).1
        (rationalCyclotomicArtinExtension m q).2
        (rationalCyclotomicChosenArithmeticFrobenius m q hq
          (rationalCyclotomicLevelPrimitiveRoot m)) =
      rationalCyclotomicArtinLocalFrobenius m q hq
        (AbsoluteValue.toAlgebraicLocalization
          (rationalCyclotomicArtinBaseAbv q)
          (rationalCyclotomicArtinExtension m q).1
          (rationalCyclotomicArtinExtension m q).2
          (rationalCyclotomicLevelPrimitiveRoot m)) :=
    rationalCyclotomicChosenArithmeticFrobenius_localization m q hq
  have hPrimitiveRoot :
      rationalCyclotomicArtinLocalFrobenius m q hq
        (AbsoluteValue.toAlgebraicLocalization
          (rationalCyclotomicArtinBaseAbv q)
          (rationalCyclotomicArtinExtension m q).1
          (rationalCyclotomicArtinExtension m q).2
          (rationalCyclotomicLevelPrimitiveRoot m)) =
      rationalCyclotomicArtinLocalFrobenius m q hq
        (rationalCyclotomicLocalizedPrimitiveRoot
          m (rationalCyclotomicArtinPlace q)) :=
    congrArg
      (rationalCyclotomicArtinLocalFrobenius m q hq)
      (rationalCyclotomicArtinPrimitiveRoot_localization m q)
  have hLocalFrobenius :
      rationalCyclotomicArtinLocalFrobenius m q hq
          (rationalCyclotomicLocalizedPrimitiveRoot
            m (rationalCyclotomicArtinPlace q)) =
        (rationalCyclotomicLocalizedPrimitiveRoot
          m (rationalCyclotomicArtinPlace q)) ^ q.1 :=
    rationalCyclotomicArtinLocalFrobenius_apply_root m q hq
  have hPower :
      (rationalCyclotomicLocalizedPrimitiveRoot
          m (rationalCyclotomicArtinPlace q)) ^ q.1 =
        rationalCyclotomicGlobalToLocalizedAlgHom
          m (rationalCyclotomicArtinPlace q)
          (rationalCyclotomicLevelPrimitiveRoot m ^ q.1) :=
    rationalCyclotomicArtinLocalizedRoot_pow m q
  have hAlgebraicLocalization :
      rationalCyclotomicGlobalToLocalizedAlgHom
          m (rationalCyclotomicArtinPlace q)
          (rationalCyclotomicLevelPrimitiveRoot m ^ q.1) =
        AbsoluteValue.toAlgebraicLocalization
          (rationalCyclotomicArtinBaseAbv q)
          (rationalCyclotomicArtinExtension m q).1
          (rationalCyclotomicArtinExtension m q).2
          (rationalCyclotomicLevelPrimitiveRoot m ^ q.1) :=
    rationalCyclotomicGlobalToLocalizedAlgHom_apply
      m (rationalCyclotomicArtinPlace q)
      (rationalCyclotomicLevelPrimitiveRoot m ^ q.1)
  exact
    Eq.trans hLocalization
      (Eq.trans hPrimitiveRoot
        (Eq.trans hLocalFrobenius
          (Eq.trans hPower hAlgebraicLocalization)))

/-- The cyclotomic character sends the chosen arithmetic Frobenius lift to
the residue prime. -/
theorem galEquivZMod_chosenArithmeticFrobenius
    (m : ℕ+) (q : Nat.Primes)
    (hq : ¬ q.1 ∣ (m : ℕ)) :
    IsCyclotomicExtension.Rat.galEquivZMod
        (m : ℕ) (KummerTheory.rationalCyclotomicLevel m)
        (rationalCyclotomicChosenArithmeticFrobenius m q hq) =
      ZMod.unitOfCoprime q.1
        (q.2.coprime_iff_not_dvd.mpr hq) := by
  exact
    rationalCyclotomicLevel_galEquivZMod_eq_unitOfCoprime
      m q hq (rationalCyclotomicChosenArithmeticFrobenius m q hq)
      (rationalCyclotomicChosenArithmeticFrobenius_apply_root m q hq)

end Reciprocity
end GlobalClassFieldTheory
end
end

section
-- module Solutions.OAIQ244_DUKE.GlobalClassFieldTheory_Reciprocity_CyclotomicIdeleValue
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 400000
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.GlobalClassFields.ConductorialSubgroup.finiteIndex _root_.GlobalClassFieldTheory.GlobalClassFields.bigHilbertClassFieldNormSubgroup_normal _root_.GlobalClassFieldTheory.GlobalClassFields.ideleClassNorm_rangeFiniteIndex _root_.GlobalClassFieldTheory.GlobalClassFields.smallHilbertClassFieldNormSubgroupFiniteIndex _root_.GlobalClassFieldTheory.Reciprocity.rationalIdeleClassDirectLimitMonoid _root_.GlobalClassFieldTheory.Reciprocity.rationalIntermediateFieldAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalTowerClassGroupMul _root_.KummerTheory.primeCyclotomicBaseNumberField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.LubinTate.padicCompletedLevelField_algebra _root_.LubinTate.padicCompletedUnramifiedFieldAlgebra _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.instTopologicalSpaceLocalAlgebra _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.GlobalClassFieldTheory.GlobalClassFields.bigHilbertNormQuotient_finite _root_.GlobalClassFieldTheory.GlobalClassFields.bigHilbertNormSubgroup_finiteIndex _root_.GlobalClassFieldTheory.Reciprocity.instMonoidClassGroupRatSubtypeSeparableClosureMemIntermediateField _root_.GlobalClassFieldTheory.Reciprocity.rationalAbstractRelativeClassGroupMul _root_.GlobalClassFieldTheory.Reciprocity.rationalAbstractRelativeClassGroupMulOneClass _root_.GlobalClassFieldTheory.Reciprocity.rationalAbstractTowerClassGroupMul _root_.GlobalClassFieldTheory.Reciprocity.rationalAbstractTowerClassGroupMulOneClass _root_.LocalClassFieldTheory.normalizationIntegerRingIsIntegralClosure
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

/-!
# The normalized cyclotomic idele value

For a number field `K`, the actual cyclotomic `ZHat`-extension is the
compositum of the embedded copy of `K` with the rational cyclotomic
`ZHat`-extension.  Its normalization factor is the actual intersection degree

`f_K = [K ∩ ℚ̃ : ℚ]`,

constructed in `CyclotomicZHatBaseChange`.

This file first constructs the idele-level map

`(1 / f_K) v_ℚ ∘ N_{K/ℚ} : I_K → ZHat`.

The factor `f_K` is removed only after proving that the unnormalized
value lies in the actual subgroup `f_K ZHat`.  This file stops at that
idele-level construction.  Descent from `I_K` to `C_K`, together with
the resulting integer-value and norm-range identities, requires the
genuine cyclotomic principal-idele formula and is the next
source-producing frontier; no quotient projection or abstract valuation
hypothesis is substituted for it here.
-/

noncomputable section

open scoped Topology

namespace GlobalClassFieldTheory
namespace Reciprocity

open ClassFormation

/-- The norm-one rational ideles already have dense image in the actual
cyclotomic `ZHat` coordinate.  This is the compact source used for
surjectivity after descent to the idele class group. -/
theorem rationalCyclotomicZHatIdeleValue_normOne_denseRange :
    DenseRange
      (fun b : IdeleGroup.normOneSubgroup (K := ℚ) =>
        rationalCyclotomicZHatIdeleValue b) := by
  change
    DenseRange
      (fun b : IdeleGroup.normOneSubgroup (K := ℚ) =>
        rationalCyclotomicZHatFieldGalEquivZHat
          (rationalCyclotomicZHatGlobalArtin b))
  exact
    rationalCyclotomicZHatFieldGalEquivZHat.surjective.denseRange.comp
      rationalCyclotomicZHatGlobalArtin_normOne_denseRange
      rationalCyclotomicZHatFieldGalEquivZHat.continuous

end Reciprocity
end GlobalClassFieldTheory
end
end

section
-- module Solutions.OAIQ244_DUKE.GlobalClassFieldTheory_Reciprocity_CyclotomicPrincipalIdele
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.GlobalClassFields.ConductorialSubgroup.finiteIndex _root_.GlobalClassFieldTheory.GlobalClassFields.bigHilbertClassFieldNormSubgroup_normal _root_.GlobalClassFieldTheory.GlobalClassFields.ideleClassNorm_rangeFiniteIndex _root_.GlobalClassFieldTheory.GlobalClassFields.smallHilbertClassFieldNormSubgroupFiniteIndex _root_.GlobalClassFieldTheory.Reciprocity.infinitePlaceBaseFourthRootField_isAbelianGalois _root_.GlobalClassFieldTheory.Reciprocity.infinitePlaceComplexificationOverfield_algebra _root_.GlobalClassFieldTheory.Reciprocity.infinitePlaceComplexificationOverfield_baseAlgebra _root_.GlobalClassFieldTheory.Reciprocity.infinitePlaceComplexificationOverfield_baseSmul _root_.GlobalClassFieldTheory.Reciprocity.infinitePlaceComplexificationOverfield_smul _root_.GlobalClassFieldTheory.Reciprocity.infinitePlaceEmbeddedExtensionField_isAbelianGalois _root_.GlobalClassFieldTheory.Reciprocity.ramifiedInfinitePlaceRealFixedField_algebra _root_.GlobalClassFieldTheory.Reciprocity.rationalComplexificationCyclotomicField_isCMField _root_.GlobalClassFieldTheory.Reciprocity.rationalComplexificationCyclotomicField_isCyclotomicFour _root_.GlobalClassFieldTheory.Reciprocity.rationalCyclotomicCompletionAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalCyclotomicLocalizedCompletionFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalCyclotomicLocalizedCompletionIsAlgebraic _root_.GlobalClassFieldTheory.Reciprocity.rationalIdeleClassDirectLimitMonoid _root_.GlobalClassFieldTheory.Reciprocity.rationalIdeleClassDirectLimitSMul _root_.GlobalClassFieldTheory.Reciprocity.rationalIntermediateFieldAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalTowerClassGroupMul _root_.KummerTheory.DiscreteNthRootsSubgroup.instTopologicalSpaceSubtypeUnitsMemSubgroup _root_.KummerTheory.primeCyclotomicBaseFiniteDimensional _root_.KummerTheory.primeCyclotomicBaseIsGalois _root_.KummerTheory.primeCyclotomicBaseNumberField _root_.LocalFieldTheory.DiscreteValuationField.finite_principalUnits_nthPowerKernel _root_.LocalFieldTheory.DiscreteValuationField.finite_residueRootsOfUnityGroup _root_.LocalFieldTheory.DiscreteValuationField.finite_valuationSubringUnits_nthPowerKernel _root_.LocalFieldTheory.DiscreteValuationField.finite_valuationSubringUnits_nthPowerQuotient _root_.LocalFieldTheory.Padic.padicDVR_residueField_finite _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.LubinTate.padicCompletedChangedUniformizerFixedField_finiteDimensional _root_.LubinTate.padicCompletedChangedUniformizerFixedField_isAbelianGalois _root_.LubinTate.padicCompletedChangedUniformizerFixedField_isNonarchimedeanLocalField _root_.LubinTate.padicCompletedChangedUniformizerFixedField_nontriviallyNormedField _root_.LubinTate.padicCompletedChangedUniformizerFixedField_valuativeRel _root_.LubinTate.padicCompletedLevelField_algebra _root_.LubinTate.padicCompletedLevelField_finiteDimensional _root_.LubinTate.padicCompletedLevelField_isGalois _root_.LubinTate.padicCompletedLevelField_padicScalarTower _root_.LubinTate.padicCompletedStandardChangedCompositum_changedFieldAlgebra _root_.LubinTate.padicCompletedStandardChangedCompositum_changedFieldScalarTower _root_.LubinTate.padicCompletedStandardChangedCompositum_finiteDimensional _root_.LubinTate.padicCompletedStandardChangedCompositum_finiteDimensional_over_changedField _root_.LubinTate.padicCompletedStandardChangedCompositum_integerRing_isIntegralClosure _root_.LubinTate.padicCompletedStandardChangedCompositum_isAbelianGalois _root_.LubinTate.padicCompletedStandardChangedCompositum_isGalois_over_changedField _root_.LubinTate.padicCompletedStandardChangedCompositum_isNonarchimedeanLocalField _root_.LubinTate.padicCompletedStandardChangedCompositum_localCompleteDVFValuation_hasExtension _root_.LubinTate.padicCompletedStandardChangedCompositum_nontriviallyNormedField _root_.LubinTate.padicCompletedStandardChangedCompositum_relative_isAbelianGalois _root_.LubinTate.padicCompletedStandardChangedCompositum_valuationSubring_isIntegralClosure _root_.LubinTate.padicCompletedStandardChangedCompositum_valuation_hasExtension _root_.LubinTate.padicCompletedStandardChangedCompositum_valuativeRel _root_.LubinTate.padicCompletedUnramifiedFieldAlgebra _root_.LubinTate.standardLubinTateLevelCompleteDVF_hasExtensionInstance _root_.LubinTate.standardLubinTateLevelField_galFinite _root_.LubinTate.standardLubinTateLevelField_isAbelianGalois _root_.LubinTate.standardLubinTateLevelField_isMulCommutative _root_.LubinTate.standardLubinTateLevelValuationSubring_moduleFinite _root_.LubinTate.standardLubinTateUnitParameter_commGroup _root_.LubinTate.standardLubinTateUnitParameter_finite _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.diagonalLogAction _root_.OAI.PrimeDegreePackets.instTopologicalSpaceLocalAlgebra _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.labelPrime_fact _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.RamificationTheory.HilbertRamification.Higher.lowerRamificationGroup.instNormal _root_.GlobalClassFieldTheory.GlobalClassFields.bigHilbertNormQuotient_finite _root_.GlobalClassFieldTheory.GlobalClassFields.bigHilbertNormSubgroup_finiteIndex _root_.GlobalClassFieldTheory.Reciprocity.instMonoidClassGroupRatSubtypeSeparableClosureMemIntermediateField _root_.GlobalClassFieldTheory.Reciprocity.instSMulAlgEquivRatSeparableClosureClassGroupSubtypeMemIntermediateField _root_.GlobalClassFieldTheory.Reciprocity.rationalAbstractRelativeClassGroupMul _root_.GlobalClassFieldTheory.Reciprocity.rationalAbstractRelativeClassGroupMulOneClass _root_.GlobalClassFieldTheory.Reciprocity.rationalAbstractTowerClassGroupMul _root_.GlobalClassFieldTheory.Reciprocity.rationalAbstractTowerClassGroupMulOneClass _root_.LocalClassFieldTheory.normalizationIntegerRingIsIntegralClosure _root_.RamificationTheory.HilbertRamification.CompleteDVF.decompositionGroupMulSemiringAction _root_.RamificationTheory.HilbertRamification.CompleteDVF.decompositionGroupResidueFieldMulSemiringAction _root_.cyclicPrimeDegreeIntermediate_isGalois
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI
attribute [local instance] OAI.starSubalgebraCommCStarAlgebra

set_option autoImplicit false

/-!
# Principal ideles and the rational cyclotomic value

This file isolates the part of the rational principal-idele product
formula which follows from the existing archimedean reciprocity API.
Every rational idele is split into its archimedean and finite parts.
The archimedean part has Artin image of order at most two at every
finite layer; the actual Galois group of the rational `ZHat`-extension
is torsion-free, so its image in that extension is trivial.

Consequently the rational cyclotomic value of a principal idele is
exactly the value of its finite part.  At every finite cyclotomic layer
that remaining value is the genuine finite product of the chosen local
Artin maps.  Proving that product trivial requires a pointwise
compatibility theorem between the chosen finite-place Artin map and
the explicit cyclotomic action; no such compatibility is assumed here.
-/

open scoped BigOperators Classical NumberField IsMulCommutative
open NumberField IsDedekindDomain ClassFormation

noncomputable section

namespace GlobalClassFieldTheory
namespace Reciprocity

attribute [local instance] GlobalClassFieldTheory.Reciprocity.rationalCyclotomicPrimePowerNumberField
attribute [local instance] GlobalClassFieldTheory.Reciprocity.rationalCyclotomicPrimePowerIsGalois
attribute [local instance] GlobalClassFieldTheory.Reciprocity.rationalCyclotomicPrimePowerIsAbelianGalois
local instance localInst_r253b09_1 (p : Nat.Primes) : Fact p.1.Prime :=
  ⟨p.2⟩
noncomputable local instance
    cyclotomicPrincipalLevelIsAbelianGalois_r253b09_1
    (m : ℕ+) :
    IsAbelianGalois ℚ
      (KummerTheory.rationalCyclotomicLevel m) := by
  have : IsGalois ℚ
      (KummerTheory.rationalCyclotomicLevel m) :=
    inferInstance
  let e :=
    IsCyclotomicExtension.Rat.galEquivZMod
      (m : ℕ) (KummerTheory.rationalCyclotomicLevel m)
  exact
    { is_comm.comm σ τ := by
        apply e.injective
        simp only [map_mul]
        exact mul_comm _ _ }
/-- Restriction to the lifted torsion-free cyclotomic field commutes with its
canonical inclusion into the full rational cyclotomic field.  Keeping this
pointwise compatibility separate prevents the finite-coordinate Artin
comparison below from accumulating the cost of unfolding the lift. -/
theorem rationalCyclotomicFullRestrictionToZHat_commutes
    (σ : KummerTheory.rationalCyclotomicField ≃ₐ[ℚ]
      KummerTheory.rationalCyclotomicField)
    (x : rationalCyclotomicZHatField) :
    (IntermediateField.inclusion
        (IntermediateField.lift_le
          KummerTheory.rationalCyclotomicTorsionFixedField))
        (rationalCyclotomicFullRestrictionToZHat σ x) =
      σ
        ((IntermediateField.inclusion
          (IntermediateField.lift_le
            KummerTheory.rationalCyclotomicTorsionFixedField)) x) := by
  let T := KummerTheory.rationalCyclotomicTorsionFixedField
  let hTZ : IntermediateField.lift T ≤
      KummerTheory.rationalCyclotomicField :=
    IntermediateField.lift_le T
  let φ := IntermediateField.liftAlgEquiv T
  let _ : Normal ℚ T := by
    dsimp only [T]
    exact KummerTheory.rationalCyclotomicTorsionFixedField_normal
  let rσ : T ≃ₐ[ℚ] T :=
    AlgEquiv.restrictNormalHom T σ
  change
    (IntermediateField.inclusion hTZ) (φ.autCongr rσ x) =
      σ ((IntermediateField.inclusion hTZ) x)
  have hlift (y : T) :
      (IntermediateField.inclusion hTZ) (φ y) = y.1 := by
    apply Subtype.ext
    rfl
  have hinv :
      ((φ.symm x : T) : KummerTheory.rationalCyclotomicField) =
        (IntermediateField.inclusion hTZ) x := by
    apply Subtype.ext
    rfl
  calc
    (IntermediateField.inclusion hTZ) (φ.autCongr rσ x) =
        (IntermediateField.inclusion hTZ) (φ (rσ (φ.symm x))) := by
      rfl
    _ = (rσ (φ.symm x) : T) := hlift _
    _ = σ ((φ.symm x : T) :
          KummerTheory.rationalCyclotomicField) := by
      exact AlgEquiv.restrictNormalHom_apply T σ (φ.symm x)
    _ = σ ((IntermediateField.inclusion hTZ) x) :=
      congrArg σ hinv

/-- The infinite Artin automorphism of the actual rational
`ZHat`-field is the restriction of the infinite Artin automorphism of
the full rational cyclotomic field.  The statement uses the genuine
torsion-fixed subfield and its actual lift inside `SeparableClosure ℚ`. -/
theorem rationalCyclotomicZHatGlobalArtin_eq_fullRestriction
    (a : IdeleGroup ℚ) :
    rationalCyclotomicZHatGlobalArtin a =
      rationalCyclotomicFullRestrictionToZHat
        (infiniteGlobalArtinMonoidHom
          ℚ KummerTheory.rationalCyclotomicField a) := by
  let hfull :
      rationalCyclotomicZHatField ≤
        KummerTheory.rationalCyclotomicField :=
    IntermediateField.lift_le
      KummerTheory.rationalCyclotomicTorsionFixedField
  let i :
      rationalCyclotomicZHatField →ₐ[ℚ]
        KummerTheory.rationalCyclotomicField :=
    IntermediateField.inclusion hfull
  apply
    (InfiniteGalois.continuousMulEquivToLimit
      ℚ rationalCyclotomicZHatField).injective
  apply Subtype.ext
  funext Eop
  let E := Eop.unop
  let hENumberField : NumberField E :=
    NumberField.of_module_finite ℚ E
  let hEAbelian : IsAbelianGalois ℚ E :=
    IsAbelianGalois.of_algHom
      (E : IntermediateField ℚ
        rationalCyclotomicZHatField).val
  let : NumberField E := hENumberField
  let : IsAbelianGalois ℚ E := hEAbelian
  let σ : KummerTheory.rationalCyclotomicField ≃ₐ[ℚ]
      KummerTheory.rationalCyclotomicField :=
    infiniteGlobalArtinMonoidHom
      ℚ KummerTheory.rationalCyclotomicField a
  let j : E →ₐ[ℚ] KummerTheory.rationalCyclotomicField :=
    i.comp
      (E : IntermediateField ℚ
        rationalCyclotomicZHatField).val
  let algZHatFull : Algebra rationalCyclotomicZHatField
      KummerTheory.rationalCyclotomicField :=
    i.toRingHom.toAlgebra
  let _ : SMul rationalCyclotomicZHatField
      KummerTheory.rationalCyclotomicField :=
    @Algebra.toSMul rationalCyclotomicZHatField
      KummerTheory.rationalCyclotomicField _ _ algZHatFull
  let _ : Algebra rationalCyclotomicZHatField
      KummerTheory.rationalCyclotomicField :=
    algZHatFull
  let _ : IsScalarTower ℚ rationalCyclotomicZHatField
      KummerTheory.rationalCyclotomicField :=
    IsScalarTower.of_algHom i
  let algEFull : Algebra E
      KummerTheory.rationalCyclotomicField :=
    j.toRingHom.toAlgebra
  let _ : SMul E KummerTheory.rationalCyclotomicField :=
    @Algebra.toSMul E
      KummerTheory.rationalCyclotomicField _ _ algEFull
  let _ : Algebra E KummerTheory.rationalCyclotomicField :=
    algEFull
  let _ : IsScalarTower ℚ E
      KummerTheory.rationalCyclotomicField :=
    IsScalarTower.of_algHom j
  let _ : IsScalarTower E rationalCyclotomicZHatField
      KummerTheory.rationalCyclotomicField :=
    IsScalarTower.of_algebraMap_eq fun _ => rfl
  have htransport :
      AlgEquiv.restrictNormalHom E
          (rationalCyclotomicFullRestrictionToZHat σ) =
        AlgEquiv.restrictNormalHom E σ := by
    apply restrictNormalHom_eq_of_commuting_square
      ℚ E rationalCyclotomicZHatField
        KummerTheory.rationalCyclotomicField
    intro x
    exact rationalCyclotomicFullRestrictionToZHat_commutes σ x
  have hfullArtin :
      AlgEquiv.restrictNormalHom E σ =
        globalArtinMonoidHom (K := ℚ) (L := E) a :=
    restrictNormalHom_infiniteGlobalArtinMonoidHom_of_scalarTower
      ℚ E KummerTheory.rationalCyclotomicField a
  change
    AlgEquiv.restrictNormalHom E
        (rationalCyclotomicZHatGlobalArtin a) =
      AlgEquiv.restrictNormalHom E
        (rationalCyclotomicFullRestrictionToZHat
          (infiniteGlobalArtinMonoidHom
            ℚ KummerTheory.rationalCyclotomicField a))
  calc
    AlgEquiv.restrictNormalHom E
          (rationalCyclotomicZHatGlobalArtin a) =
        globalArtinMonoidHom (K := ℚ) (L := E) a :=
      restrictNormalHom_rationalCyclotomicZHatGlobalArtin a E
    _ = AlgEquiv.restrictNormalHom E σ :=
      hfullArtin.symm
    _ = AlgEquiv.restrictNormalHom E
          (rationalCyclotomicFullRestrictionToZHat σ) :=
      htransport.symm

/-- The rational cyclotomic idele value is the genuine torsion-free
factor of the full cyclotomic character of its infinite Artin symbol. -/
theorem rationalCyclotomicZHatIdeleValue_eq_fullCharacterFreePart
    (a : IdeleGroup ℚ) :
    rationalCyclotomicZHatIdeleValue a =
      (KummerTheory.zHatUnitsDecomposition
        (KummerTheory.rationalCyclotomicCharacterContinuousMulEquiv
          (infiniteGlobalArtinMonoidHom
            ℚ KummerTheory.rationalCyclotomicField a))).1 := by
  rw [rationalCyclotomicZHatIdeleValue_apply,
    rationalCyclotomicZHatGlobalArtin_eq_fullRestriction,
    rationalCyclotomicZHatFieldGalEquivZHat_fullRestriction]

end Reciprocity
end GlobalClassFieldTheory
end
end

section
-- module Solutions.OAIQ244_DUKE.GlobalClassFieldTheory_Reciprocity_RationalCyclotomicZHatRigidity
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 400000
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.GlobalClassFields.ConductorialSubgroup.finiteIndex _root_.GlobalClassFieldTheory.GlobalClassFields.bigHilbertClassFieldNormSubgroup_normal _root_.GlobalClassFieldTheory.GlobalClassFields.ideleClassNorm_rangeFiniteIndex _root_.GlobalClassFieldTheory.GlobalClassFields.smallHilbertClassFieldNormSubgroupFiniteIndex _root_.GlobalClassFieldTheory.Reciprocity.rationalComplexificationCyclotomicField_isCMField _root_.GlobalClassFieldTheory.Reciprocity.rationalComplexificationCyclotomicField_isCyclotomicFour _root_.GlobalClassFieldTheory.Reciprocity.rationalCyclotomicCompletionAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalCyclotomicLocalizedCompletionFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalCyclotomicLocalizedCompletionIsAlgebraic _root_.GlobalClassFieldTheory.Reciprocity.rationalIdeleClassDirectLimitMonoid _root_.GlobalClassFieldTheory.Reciprocity.rationalIntermediateFieldAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalTowerClassGroupCommGroup _root_.GlobalClassFieldTheory.Reciprocity.rationalTowerClassGroupMul _root_.KummerTheory.primeCyclotomicBaseNumberField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.LubinTate.padicCompletedLevelField_algebra _root_.LubinTate.padicCompletedUnramifiedFieldAlgebra _root_.LubinTate.standardLubinTateLevelField_isMulCommutative _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.instTopologicalSpaceLocalAlgebra _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.GlobalClassFieldTheory.GlobalClassFields.bigHilbertNormQuotient_finite _root_.GlobalClassFieldTheory.GlobalClassFields.bigHilbertNormSubgroup_finiteIndex _root_.GlobalClassFieldTheory.Reciprocity.instMonoidClassGroupRatSubtypeSeparableClosureMemIntermediateField _root_.GlobalClassFieldTheory.Reciprocity.rationalAbstractRelativeClassGroupCommGroup _root_.GlobalClassFieldTheory.Reciprocity.rationalAbstractRelativeClassGroupMul _root_.GlobalClassFieldTheory.Reciprocity.rationalAbstractRelativeClassGroupMulOneClass _root_.GlobalClassFieldTheory.Reciprocity.rationalAbstractTowerClassGroupCommGroup _root_.GlobalClassFieldTheory.Reciprocity.rationalAbstractTowerClassGroupMul _root_.GlobalClassFieldTheory.Reciprocity.rationalAbstractTowerClassGroupMulOneClass _root_.LocalClassFieldTheory.normalizationIntegerRingIsIntegralClosure
attribute [-simp] _root_.ClassFormation.DegreeData.finiteUnramifiedDegreeHom_mk _root_.ClassFormation.DegreeData.maximalUnramifiedFrobeniusPower_one _root_.ClassFormation.ValuationData.maximalUnramifiedNormResidue_degree _root_.GlobalClassFieldTheory.ClassFieldAxiom.actualPushoutNormQuotientMap_mk _root_.GlobalClassFieldTheory.ClassFieldAxiom.hasseNormDiagonal_mk _root_.GlobalClassFieldTheory.ClassFieldAxiom.sUnitEquivSupportedPrincipalIdeleSubgroup_coe _root_.GlobalClassFieldTheory.GlobalClassFields.ConductorialSubgroup.ideleClassQuotientEquivOfNarrowFiniteConductorsEqOfRayClassGroupCardsEqQuotientCards_mk _root_.GlobalClassFieldTheory.GlobalClassFields.ConductorialSubgroup.mem_fullConductorInfinitePart_iff _root_.GlobalClassFieldTheory.GlobalClassFields.ConductorialSubgroup.narrowFiniteConductorRayClassGroupEquivQuotientOfCardEq_mk _root_.GlobalClassFieldTheory.GlobalClassFields.ConductorialSubgroup.narrowFiniteConductorRayClassGroupToQuotient_mk _root_.GlobalClassFieldTheory.GlobalClassFields.bigHilbertClassFieldQuotientCongr_mk _root_.GlobalClassFieldTheory.GlobalClassFields.bigHilbertClassFieldQuotientEquivNarrowClassGroup_mk _root_.GlobalClassFieldTheory.GlobalClassFields.bigHilbertClassFieldQuotientToIdeleClassNormQuotient_mk _root_.GlobalClassFieldTheory.GlobalClassFields.bigHilbertClassFieldQuotientToSmallHilbertClassFieldQuotient_mk _root_.GlobalClassFieldTheory.GlobalClassFields.ideleClassNormQuotientTowerMap_mk _root_.GlobalClassFieldTheory.GlobalClassFields.narrowFiniteConductorRayClassGroupToIdeleClassNormQuotient_mk _root_.GlobalClassFieldTheory.GlobalClassFields.normQuotientEquivOfNarrowFiniteConductorsEqOfRayClassGroupCardsEqNormQuotientCards_mk _root_.GlobalClassFieldTheory.GlobalClassFields.realSignToBigHilbertClassFieldQuotient_apply _root_.GlobalClassFieldTheory.GlobalClassFields.realSignToNarrowClassKernel_apply _root_.GlobalClassFieldTheory.GlobalClassFields.smallHilbertClassFieldQuotientCongr_mk _root_.GlobalClassFieldTheory.GlobalClassFields.smallHilbertClassFieldQuotientEquivClassGroup_mk _root_.GlobalClassFieldTheory.GlobalClassFields.smallHilbertClassFieldQuotientToIdeleClassNormQuotient_mk _root_.GlobalClassFieldTheory.IdealClassFieldTheory.smallHilbertClassFieldIdeleExtensionMap_mk' _root_.GlobalClassFieldTheory.Reciprocity.cyclotomicZHatNormCompositeContinuous_apply _root_.GlobalClassFieldTheory.Reciprocity.cyclotomicZHatNormCompositeInMulNatRangeContinuous_apply _root_.GlobalClassFieldTheory.Reciprocity.globalNormClassFromIdele_principalIdele _root_.GlobalClassFieldTheory.Reciprocity.globalNormClassFromIdele_relativeIdeleNorm_eq_one _root_.GlobalClassFieldTheory.Reciprocity.mem_globalArtinFiniteSupport_iff _root_.GlobalClassFieldTheory.Reciprocity.normalizedCyclotomicZHatIdeleValueContinuousMul_apply _root_.GlobalClassFieldTheory.Reciprocity.normalizedCyclotomicZHatIdeleValueContinuous_apply _root_.GlobalClassFieldTheory.Reciprocity.numberFieldCyclotomicPadicDecompositionCoordinate_apply _root_.GlobalClassFieldTheory.Reciprocity.rationalAbstractFixedFieldIdeleClassEquivFixed_coe _root_.GlobalClassFieldTheory.Reciprocity.rationalCyclotomicGlobalToLocalizedAlgHom_apply _root_.GlobalClassFieldTheory.Reciprocity.rationalCyclotomicGlobalToLocalizedAlgHom_primitiveRoot _root_.GlobalClassFieldTheory.Reciprocity.rationalCyclotomicPadicCoordinate_apply _root_.GlobalClassFieldTheory.Reciprocity.rationalCyclotomicZHatIdeleValueContinuousAdd_apply _root_.GlobalClassFieldTheory.Reciprocity.rationalCyclotomicZHatIdeleValueReduction_apply _root_.GlobalClassFieldTheory.Reciprocity.rationalIntermediateIdeleClassEquivGaloisFixed_coe _root_.IdeleClassGroup.normOneNorm_apply _root_.IdeleGroup.count_fractionalIdeal _root_.IdeleGroup.fractionalIdeal_finitePrimeIdele _root_.IdeleGroup.idealClass_finitePrimeIdele _root_.IsDiscreteValuationRing.addVal_ringEquiv _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.OAI.PrimeDegreePackets.ThetaConstruction.schwartzCM_apply _root_.RayClass.primesEquiv_val_eq_natGenerator _root_.RayClass.signToNarrow_mk
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI
attribute [local instance] OAI.starSubalgebraCommCStarAlgebra

set_option autoImplicit false

/-!
# Prime-power detection for the rational cyclotomic `ZHat`-Artin map

Prime-power reductions of the genuine cyclotomic character detect the
full rational cyclotomic automorphism.  Restricting that automorphism
through actual finite cyclotomic levels then detects every finite
coordinate of the rational cyclotomic `ZHat`-extension.
-/

open scoped Classical NumberField IsMulCommutative
open NumberField ClassFormation

noncomputable section

namespace GlobalClassFieldTheory
namespace Reciprocity

local instance localInst_r253b09_2 (p : Nat.Primes) : Fact p.1.Prime :=
  ⟨p.2⟩
/-- If all prime-power character reductions of the full cyclotomic
global Artin symbol have square one, then the corresponding Artin symbol
in the actual rational `ZHat`-extension has square one. -/
theorem
    rationalCyclotomicZHatGlobalArtin_sq_eq_one_of_character_reductions
    (a : IdeleGroup ℚ)
    (h :
      ∀ (p : Nat.Primes) (k : ℕ),
        Units.map (PadicInt.toZModPow k).toMonoidHom
              (KummerTheory.rationalCyclotomicCharacterPrimeProduct
                (infiniteGlobalArtinMonoidHom
                  ℚ KummerTheory.rationalCyclotomicField a) p) ^ 2 =
          1) :
    rationalCyclotomicZHatGlobalArtin a ^ 2 = 1 := by
  let σ :
      KummerTheory.rationalCyclotomicField ≃ₐ[ℚ]
        KummerTheory.rationalCyclotomicField :=
    infiniteGlobalArtinMonoidHom
      ℚ KummerTheory.rationalCyclotomicField a
  have hσ : σ ^ 2 = 1 :=
    rationalCyclotomicAutomorphism_sq_eq_one_of_character_reductions
      σ h
  rw [rationalCyclotomicZHatGlobalArtin_eq_fullRestriction]
  change (rationalCyclotomicFullRestrictionToZHat σ) ^ 2 = 1
  rw [← map_pow, hσ, map_one]
/-- Prime-power square-one identities force the rational cyclotomic
idele value itself to be trivial.  Torsion-freeness of `ZHat` removes
the residual order-two ambiguity. -/
theorem
    rationalCyclotomicZHatIdeleValue_eq_one_of_character_reductions
    (a : IdeleGroup ℚ)
    (h :
      ∀ (p : Nat.Primes) (k : ℕ),
        Units.map (PadicInt.toZModPow k).toMonoidHom
              (KummerTheory.rationalCyclotomicCharacterPrimeProduct
                (infiniteGlobalArtinMonoidHom
                  ℚ KummerTheory.rationalCyclotomicField a) p) ^ 2 =
          1) :
    rationalCyclotomicZHatIdeleValue a = 1 := by
  have hArtin :
      rationalCyclotomicZHatGlobalArtin a ^ 2 = 1 :=
    rationalCyclotomicZHatGlobalArtin_sq_eq_one_of_character_reductions
      a h
  have hValue :
      rationalCyclotomicZHatIdeleValue a ^ 2 = 1 := by
    rw [rationalCyclotomicZHatIdeleValue_apply,
      ← map_pow, hArtin, map_one]
  exact
    (pow_left_injective
      (M := Multiplicative ZHat)
      (n := 2) (by norm_num))
        (by simpa using hValue)

end Reciprocity
end GlobalClassFieldTheory
end
end

section
-- module Solutions.OAIQ244_DUKE.GlobalClassFieldTheory_Reciprocity_ComplexificationArtin_RationalComplexification
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.infinitePlaceComplexificationOverfield_numberField _root_.GlobalClassFieldTheory.Reciprocity.ramifiedInfinitePlaceRealFixedField_numberField _root_.GlobalClassFieldTheory.Reciprocity.rationalIdeleClassDirectLimitMonoid _root_.GlobalClassFieldTheory.Reciprocity.rationalIntermediateFieldAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalIntermediateFieldNumberField _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalTowerClassGroupMul _root_.KummerTheory.primeCyclotomicBaseNumberField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.boundedRealFields_numberField _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.GlobalClassFieldTheory.Reciprocity.instNumberFieldSubtypeSeparableClosureRatMemIntermediateFieldAbstractFixedFieldOfFiniteQuotientAlgEquivSubgroupBaseFieldExtensionSubgroup _root_.GlobalClassFieldTheory.Reciprocity.instMonoidClassGroupRatSubtypeSeparableClosureMemIntermediateField _root_.GlobalClassFieldTheory.Reciprocity.rationalAbstractRelativeClassGroupMul _root_.GlobalClassFieldTheory.Reciprocity.rationalAbstractRelativeClassGroupMulOneClass _root_.GlobalClassFieldTheory.Reciprocity.rationalAbstractTowerClassGroupMul _root_.GlobalClassFieldTheory.Reciprocity.rationalAbstractTowerClassGroupMulOneClass
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

local instance rationalComplexificationPrimeFact_r253b09_1 :
    Fact rationalComplexificationPrime.1.Prime :=
  ⟨rationalComplexificationPrime.2⟩
attribute [local instance] GlobalClassFieldTheory.Reciprocity.rationalComplexificationPrimeSquareNeZero
attribute [local instance] GlobalClassFieldTheory.Reciprocity.rationalComplexificationCyclotomicField_finiteDimensional
attribute [local instance] GlobalClassFieldTheory.Reciprocity.rationalComplexificationCyclotomicField_numberField
attribute [local instance] GlobalClassFieldTheory.Reciprocity.rationalComplexificationCyclotomicField_isAbelianGalois
theorem rationalComplexificationCharacter_apply
    (σ : rationalComplexificationCyclotomicField ≃ₐ[ℚ]
      rationalComplexificationCyclotomicField) :
    rationalComplexificationCharacter σ =
      IsCyclotomicExtension.Rat.galEquivZMod
        (rationalComplexificationPrime.1 ^ 2)
        rationalComplexificationCyclotomicField
        (hK :=
          KummerTheory.rationalCyclotomicLevel_isCyclotomicExtension
            rationalComplexificationCyclotomicOrder) σ :=
  rfl

end Reciprocity
end GlobalClassFieldTheory
end
end

section
-- module Solutions.OAIQ244_DUKE.GlobalClassFieldTheory_Reciprocity_FinitePlaceCyclotomicFrobeniusLift
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalIdeleClassDirectLimitMonoid _root_.GlobalClassFieldTheory.Reciprocity.rationalIntermediateFieldAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.instTopologicalSpaceLocalAlgebra _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.labelPrime_fact _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.OAI.PrimeDegreePackets.xMetrizable _root_.GlobalClassFieldTheory.Reciprocity.instMonoidClassGroupRatSubtypeSeparableClosureMemIntermediateField _root_.GlobalClassFieldTheory.Reciprocity.rationalAbstractRelativeClassGroupMulOneClass _root_.GlobalClassFieldTheory.Reciprocity.rationalAbstractTowerClassGroupMulOneClass
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

local instance localInst_r253b09_3 (p : Nat.Primes) : Fact p.1.Prime :=
  ⟨p.2⟩
local instance rationalCyclotomicFrobeniusLiftPrimePowerNumberField_r253b09_1
    (p : Nat.Primes) (k : ℕ) :
    NumberField (KummerTheory.rationalCyclotomicLevel
      ⟨p.1 ^ k, pow_pos p.2.pos k⟩) :=
  KummerTheory.rationalCyclotomicLevel_numberField
    ⟨p.1 ^ k, pow_pos p.2.pos k⟩
local instance rationalCyclotomicFrobeniusLiftPrimePowerFiniteDimensional_r253b09_1
    (p : Nat.Primes) (k : ℕ) :
    FiniteDimensional ℚ (KummerTheory.rationalCyclotomicLevel
      ⟨p.1 ^ k, pow_pos p.2.pos k⟩) :=
  rationalCyclotomicPrincipalPrimeLevelFiniteDimensional
    ⟨p.1 ^ k, pow_pos p.2.pos k⟩
local instance rationalCyclotomicFrobeniusLiftPrimePowerIsAbelianGalois_r253b09_1
    (p : Nat.Primes) (k : ℕ) :
    IsAbelianGalois ℚ (KummerTheory.rationalCyclotomicLevel
      ⟨p.1 ^ k, pow_pos p.2.pos k⟩) :=
  rationalCyclotomicLevelIsAbelianGalois
    ⟨p.1 ^ k, pow_pos p.2.pos k⟩
noncomputable local instance
    rationalCyclotomicFrobeniusLiftLevelFiniteDimensional_r253b09_1
    (m : ℕ+) :
    FiniteDimensional ℚ
      (KummerTheory.rationalCyclotomicLevel m) :=
  rationalCyclotomicPrincipalPrimeLevelFiniteDimensional m
noncomputable local instance
    rationalCyclotomicFrobeniusLiftLevelIsAbelianGalois_r253b09_1
    (m : ℕ+) :
    IsAbelianGalois ℚ
      (KummerTheory.rationalCyclotomicLevel m) :=
  rationalCyclotomicLevelIsAbelianGalois m
variable
    {K L Ω : Type}
    [Field K] [Field L] [Field Ω]
    [Algebra K L] [Algebra L Ω] [Algebra K Ω]
    [IsScalarTower K L Ω] [Normal K L]

/-- The closed subgroup fixing the `p`-primary cyclotomic direction. -/
noncomputable def rationalCyclotomicPadicKernel
    (p : Nat.Primes) :
    ClosedSubgroup
      (rationalCyclotomicZHatField ≃ₐ[ℚ]
        rationalCyclotomicZHatField) where
  toSubgroup :=
    (rationalCyclotomicPadicCoordinate p).toMonoidHom.ker
  isClosed' := by
    change
      IsClosed
        ((rationalCyclotomicPadicCoordinate p) ⁻¹'
          ({1} : Set (Multiplicative ℤ_[p.1])))
    exact
      isClosed_singleton.preimage
        (rationalCyclotomicPadicCoordinate p).continuous_toFun

/-- The `p`-primary cyclotomic field inside the rational cyclotomic
`ZHat`-extension.  Its defining subgroup is the kernel of the actual
coordinate to `ℤ_p`. -/
abbrev rationalCyclotomicPadicFieldWithinZHat
    (p : Nat.Primes) :
    IntermediateField ℚ rationalCyclotomicZHatField :=
  IntermediateField.fixedField
    (rationalCyclotomicPadicKernel p).toSubgroup

end Reciprocity
end GlobalClassFieldTheory
end
end

section
-- module Solutions.OAIQ244_DUKE.GlobalClassFieldTheory_Reciprocity_IdeleClassDirectLimitNormQuotient
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.GlobalClassFields.ConductorialSubgroup.finiteIndex _root_.GlobalClassFieldTheory.GlobalClassFields.bigHilbertClassFieldNormSubgroup_normal _root_.GlobalClassFieldTheory.GlobalClassFields.finiteAbelianSubextensionAbstractRelativeFixedFieldFiniteDimensional _root_.GlobalClassFieldTheory.GlobalClassFields.finiteAbelianSubextensionAbstractRelativeFixedFieldIsAbelianGalois _root_.GlobalClassFieldTheory.GlobalClassFields.ideleClassNorm_rangeFiniteIndex _root_.GlobalClassFieldTheory.GlobalClassFields.smallHilbertClassFieldNormSubgroupFiniteIndex _root_.GlobalClassFieldTheory.Reciprocity.complexFourthRootField_numberField _root_.GlobalClassFieldTheory.Reciprocity.infinitePlaceComplexificationOverfield_baseSmul _root_.GlobalClassFieldTheory.Reciprocity.infinitePlaceComplexificationOverfield_numberField _root_.GlobalClassFieldTheory.Reciprocity.infinitePlaceComplexificationOverfield_smul _root_.GlobalClassFieldTheory.Reciprocity.numberFieldCyclotomicZHatFiniteCompositum_numberField _root_.GlobalClassFieldTheory.Reciprocity.numberFieldCyclotomicZHatFiniteLayerInCompositum_numberField _root_.GlobalClassFieldTheory.Reciprocity.numberFieldCyclotomicZHatIntersection_numberField _root_.GlobalClassFieldTheory.Reciprocity.ramifiedInfinitePlaceRealFixedField_numberField _root_.GlobalClassFieldTheory.Reciprocity.rationalCyclotomicZHatCompositum_algebra _root_.GlobalClassFieldTheory.Reciprocity.rationalCyclotomicZHatFiniteLayerCompositum_algebra _root_.GlobalClassFieldTheory.Reciprocity.rationalCyclotomicZHatFiniteLayerCompositum_smul _root_.GlobalClassFieldTheory.Reciprocity.rationalCyclotomicZHatFiniteLayerInCompositum_algebra _root_.GlobalClassFieldTheory.Reciprocity.rationalCyclotomicZHatFiniteLayerInCompositum_smul _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.KummerTheory.primeCyclotomicBaseIsGalois _root_.KummerTheory.primeCyclotomicBaseNumberField _root_.KummerTheory.rationalCyclotomicLevel_numberField _root_.LocalClassFieldTheory.finiteGaloisLocalField_integerRing_moduleFinite _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.residueFieldZModAlgebra _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedIntegralAlgebraContextValuationSubringAlgebra _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedIntegralAlgebraContextValuationSubringTower _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedQPadicContextValuationSubringTower _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.LubinTate.compatibleGroupFamiliesGroup _root_.LubinTate.padicCompletedLevelField_algebra _root_.LubinTate.padicCompletedLevelField_isGalois _root_.LubinTate.padicCompletedLevelField_padicScalarTower _root_.LubinTate.padicCompletedUnramifiedFieldAlgebra _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.boundedRealFields_numberField _root_.OAI.PrimeDegreePackets.instTopologicalSpaceLocalAlgebra _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.CyclicCohomology.binaryCoefficientFamilyCommGroup _root_.GlobalClassFieldTheory.GlobalClassFields.bigHilbertNormQuotient_finite _root_.GlobalClassFieldTheory.GlobalClassFields.bigHilbertNormSubgroup_finiteIndex _root_.LocalClassFieldTheory.comparisonIntegerRingIsIntegralClosure _root_.LocalClassFieldTheory.normalizationIntegerRingIsIntegralClosure _root_.chosenFinitePlaceCompletionAlgebra _root_.chosenFinitePlaceLocalizedIntegerAlgebra _root_.chosenFinitePlaceLocalizedIsGalois _root_.cyclicPrimeDegreeIntermediate_isGalois _root_.cyclicPrimeSubextension_isGalois _root_.relativeUnrestrictedSPlaceFactorCommGroup
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI
attribute [local instance] OAI.starSubalgebraCommCStarAlgebra

set_option autoImplicit false

/-!
# Finite norm quotients for rational fixed fields

The abstract finite norm subgroup and quotient are identified with the
ordinary idele-class norm range and quotient of the actual fixed-field extension.
-/

noncomputable section

namespace GlobalClassFieldTheory
namespace Reciprocity

open ClassFormation
open LocalClassFieldTheory
open CyclicCohomology

attribute [local instance] GlobalClassFieldTheory.Reciprocity.rationalNormQuotientIdeleClassGroupIsMulCommutative
attribute [local instance] GlobalClassFieldTheory.Reciprocity.rationalNormQuotientIdeleClassSubgroupNormal
theorem rationalRelativeFixedFieldNormCohomologyComparison_eq
    (K L : ClosedSubgroup
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
    (hLK : L.toSubgroup ≤ K.toSubgroup)
    (hnormal : (extensionSubgroup K L hLK).Normal)
    [hKfinite : Finite
      ((baseField
        (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ)).toSubgroup ⧸
        extensionSubgroup
          (baseField
            (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
          K (le_baseField K))]
    [hfinite : Finite
      (K.toSubgroup ⧸ extensionSubgroup K L hLK)]
    (c : rationalRelativeFixedFieldIdeleClassAdditiveType
      (hKfinite := hKfinite) (hfinite := hfinite)
      K L hLK) :
    (rationalRelativeFixedFieldNormCohomologyComparison
      K L hLK hnormal c).1 =
      (rationalRelativeFixedFieldNormCohomologyComparison
        K L hLK hnormal c).2 := by
  let F := abstractFixedField ℚ (SeparableClosure ℚ) K
  let E := abstractRelativeFixedField ℚ (SeparableClosure ℚ) hLK
  let _ := hnormal
  let _ : FiniteDimensional ℚ F :=
    abstractFixedField_finiteDimensional
      ℚ (SeparableClosure ℚ) K hKfinite
  let _ : FiniteDimensional F E :=
    abstractRelativeFixedField_finiteDimensional
      ℚ (SeparableClosure ℚ) K L hLK hKfinite hfinite
  let _ : IsScalarTower ℚ F E :=
    IsScalarTower.of_algebraMap_eq' (RingHom.ext_rat _ _)
  let _ : FiniteDimensional ℚ E := FiniteDimensional.trans ℚ F E
  let _ : NumberField F := NumberField.of_module_finite ℚ F
  let _ : NumberField E := NumberField.of_module_finite ℚ E
  let _ : IsGalois F E :=
    abstractRelativeFixedField_isGalois
      ℚ (SeparableClosure ℚ) K L hLK hnormal
  let eUpper :=
    rationalAbstractRelativeFixedFieldIdeleClassEquivFixed K L hLK
  let comparison :=
    rationalRelativeFixedFieldNormPreimageComparison
      K L hLK hnormal c
  change
    (rationalAbstractFixedFieldIdeleClassEquivFixed K).symm
        (relativeNorm rationalIdeleClassRepresentation
          K L hLK (eUpper c)) =
      Additive.ofMul
        (RelativeIdeleGroup.Cohomology.ideleClassNorm F E
          (Additive.toMul comparison.2))
  have htransport : comparison.1 = comparison.2 :=
    rationalRelativeFixedFieldNormPreimageComparison_eq
      K L hLK hnormal c
  have hnorm :=
    rationalAbstractFixedFieldIdeleClassEquivFixed_relativeNorm
      K L hLK hnormal (eUpper c)
  change
    (rationalAbstractFixedFieldIdeleClassEquivFixed K).symm
        (relativeNorm rationalIdeleClassRepresentation
          K L hLK (eUpper c)) =
      Additive.ofMul
        (RelativeIdeleGroup.Cohomology.ideleClassNorm F E
          (Additive.toMul comparison.1))
    at hnorm
  rw [htransport] at hnorm
  exact hnorm

/-- For a finite Galois pair of abstract fixed fields, the direct upper
fixed-part comparison intertwines the class-formation relative norm with
the ordinary idele-class norm. -/
theorem
    rationalAbstractRelativeFixedFieldIdeleClassEquivFixed_relativeNorm
    (K L : ClosedSubgroup
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
    (hLK : L.toSubgroup ≤ K.toSubgroup)
    (hnormal : (extensionSubgroup K L hLK).Normal)
    [hKfinite : Finite
      ((baseField
        (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ)).toSubgroup ⧸
        extensionSubgroup
          (baseField
            (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
          K (le_baseField K))]
    [hfinite : Finite
      (K.toSubgroup ⧸ extensionSubgroup K L hLK)]
    (c : rationalRelativeFixedFieldIdeleClassAdditiveType
      (hKfinite := hKfinite) (hfinite := hfinite)
      K L hLK) :
    let comparison := rationalRelativeFixedFieldNormComparison
      (hKfinite := hKfinite) (hfinite := hfinite) K L hLK hnormal c
    comparison.1 = comparison.2 := by
  let _ := hnormal
  let F :=
    abstractFixedField ℚ (SeparableClosure ℚ) K
  let E :=
    abstractRelativeFixedField ℚ (SeparableClosure ℚ) hLK
  let _ : FiniteDimensional ℚ F :=
    abstractFixedField_finiteDimensional
      ℚ (SeparableClosure ℚ) K hKfinite
  let _ : FiniteDimensional F E :=
    abstractRelativeFixedField_finiteDimensional
      ℚ (SeparableClosure ℚ) K L hLK hKfinite hfinite
  let _ : IsScalarTower ℚ F E :=
    IsScalarTower.of_algebraMap_eq' (RingHom.ext_rat _ _)
  let _ : FiniteDimensional ℚ E :=
    FiniteDimensional.trans ℚ F E
  let _ : NumberField F :=
    NumberField.of_module_finite ℚ F
  let _ : NumberField E :=
    NumberField.of_module_finite ℚ E
  let _ : IsGalois F E :=
    abstractRelativeFixedField_isGalois
      ℚ (SeparableClosure ℚ) K L hLK hnormal
  change
    relativeNorm rationalIdeleClassRepresentation K L hLK
        (rationalAbstractRelativeFixedFieldIdeleClassEquivFixed
          K L hLK c) =
      rationalAbstractFixedFieldIdeleClassEquivFixed K
        (Additive.ofMul
          (_root_.ideleClassNorm F E (Additive.toMul c)))
  let eUpper :=
    rationalAbstractRelativeFixedFieldIdeleClassEquivFixed
      K L hLK
  let comparison :=
    rationalRelativeFixedFieldNormPreimageComparison
      K L hLK hnormal c
  let dF : RelativeIdeleGroup.ClassGroup F E :=
    Additive.toMul comparison.2
  have hcohom :=
    rationalRelativeFixedFieldNormCohomologyComparison_eq
      K L hLK hnormal c
  change
    (rationalAbstractFixedFieldIdeleClassEquivFixed K).symm
        (relativeNorm rationalIdeleClassRepresentation
          K L hLK (eUpper c)) =
      Additive.ofMul
        (RelativeIdeleGroup.Cohomology.ideleClassNorm F E
          dF)
    at hcohom
  have hbridge := rationalTowerRelativeClass_norm F E c
  change
    RelativeIdeleGroup.Cohomology.ideleClassNorm F E dF =
      _root_.ideleClassNorm F E (Additive.toMul c) at hbridge
  calc
    relativeNorm rationalIdeleClassRepresentation K L hLK (eUpper c) =
        rationalAbstractFixedFieldIdeleClassEquivFixed K
          ((rationalAbstractFixedFieldIdeleClassEquivFixed K).symm
            (relativeNorm rationalIdeleClassRepresentation
              K L hLK (eUpper c))) :=
      ((rationalAbstractFixedFieldIdeleClassEquivFixed K).apply_symm_apply _).symm
    _ = rationalAbstractFixedFieldIdeleClassEquivFixed K
          (Additive.ofMul
            (_root_.ideleClassNorm F E (Additive.toMul c))) :=
      congrArg (rationalAbstractFixedFieldIdeleClassEquivFixed K)
        (hcohom.trans (congrArg Additive.ofMul hbridge))

end Reciprocity
end GlobalClassFieldTheory
end
end


