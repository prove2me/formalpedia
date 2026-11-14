-- Prove2me | Definitions.Def_OAIQ244Duke077
-- name    : OAIQ244Duke077
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-13T23:09:48.702209+00:00
-- url     : https://prove2.me/theorems/c970ff19-ab4e-433f-8d53-a2cabfa023cb
-- title:
--   Definitions bundle OAIQ244Duke077 of the split of OpenAI, Equidistribution of Prime-Degree Torus Packets with Arbitrary Local Type
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.DukePrimeDegree.prime_degree_packet_measure_equidistribution_unconditional` and `OAI.DukePrimeDegree.prime_degree_packet_measures_tendsto_haar_unconditional`, carved from OpenAI's openai/math development (OpenAI, *Equidistribution of Prime-Degree Torus Packets with Arbitrary Local Type*, OpenAI Math Release, September 24, 2026, result family 15, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 74 declarations of OpenAI's Lean: 9 definitions, 2 instances and 63 theorems. The definitions and types are `GlobalClassFieldTheory.Reciprocity.rationalCyclotomicArtinLocalizedGlobalAlgebra`, `GlobalClassFieldTheory.Reciprocity.rationalCyclotomicArtinLocalizedGlobalSMul`, `GlobalClassFieldTheory.Reciprocity.rationalCyclotomicPrincipalPrimeLevel`, `GlobalClassFieldTheory.Reciprocity.rationalFinitePlaceCompletionAlgEquivPadic`, `KummerTheory.ProfiniteUnitDecomposition.Internal.finiteFreeSplit`, `KummerTheory.zHatUnitsDecomposition`, `LocalClassFieldTheory.localAbstractPrimeFieldUnit`, `LubinTate.padicCompletedMultiplicativePrimitivePointUnitAction`, `LubinTate.padicCompletedMultiplicativeUnitEndomorphism`.
--
--   **Sources.** They come from these modules of lean/OAI/NumberTheory, in whole or in part: `GlobalClassFieldTheory_Reciprocity_RationalCyclotomicFinitePlaceArtin`, `Kummer_Concrete_Cyclotomic_ProfiniteUnitDecomposition_Decomposition`, `Kummer_Concrete_Cyclotomic_ProfiniteUnitDecomposition_FiniteFree`, `Kummer_Concrete_Cyclotomic_ProfiniteUnitDecomposition_FreeCoordinate`, `LocalClassFieldTheory_Finite_LocalReciprocity_UnramifiedNormalization`, `LocalField_DiscreteValuationField_PadicValuationComparison`, `LubinTate_Padic_ChangedUniformizerIntertwiner_CompletedSeries`, `LubinTate_Padic_ChangedUniformizerIntertwiner_DefectCorrection`, `LubinTate_Padic_ChangedUniformizerIntertwiner_IntertwinerConstruction`, `LubinTate_Padic_ChangedUniformizerIntertwiner_ScalarEndomorphisms`, `LubinTate_Padic_CompletedLevel`, `LubinTate_Padic_CompletedPrimitiveIrreducible`, `LubinTate_Padic_CompletedUnramifiedField`, `LubinTate_Padic_CompletedUnramifiedFrobeniusFixed`, `LubinTate_Padic_MultiplicativeEvaluation_CompletedCoefficientEvaluation`, `LubinTate_Padic_MultiplicativeEvaluation_CompletedPrimitivePoint`, `LubinTate_Padic_MultiplicativeEvaluation_CompletedScalarEndomorphism`.
--
--   **Imports.** It imports the bundles `OAIQ244Duke070` and `OAIQ244Duke071` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ244Duke082`, `OAIQ244Duke083` and `OAIQ244Duke114`.
-- source:
--   OpenAI, Equidistribution of Prime-Degree Torus Packets with Arbitrary Local Type, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 15; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Equidistribution-of-Prime-Degree-Torus-Packets-with-Arbitrary-Local-Type-September-24-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/NumberTheory at commit 7ef5c0c

import Mathlib
import Mathlib.Algebra.Algebra.Basic
import Mathlib.Algebra.Algebra.Pi
import Mathlib.Algebra.Algebra.Tower
import Mathlib.Algebra.BigOperators.Finprod
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Category.ModuleCat.Basic
import Mathlib.Algebra.CharP.Algebra
import Mathlib.Algebra.CharP.Lemmas
import Mathlib.Algebra.CharP.Subring
import Mathlib.Algebra.EuclideanDomain.Basic
import Mathlib.Algebra.Exact.Basic
import Mathlib.Algebra.Group.Action.Basic
import Mathlib.Algebra.Group.Hom.Basic
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
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
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
import Definitions.Def_OAIQ244Duke070
import Definitions.Def_OAIQ244Duke071

section
-- module Solutions.OAIQ244_DUKE.LocalClassFieldTheory_Finite_LocalReciprocity_UnramifiedNormalization
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.infinitePlaceComplexificationOverfield_algebra _root_.GlobalClassFieldTheory.Reciprocity.infinitePlaceComplexificationOverfield_baseAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.KummerTheory.primeCyclotomicBaseIsGalois _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.residueFieldZModAlgebra _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedIntegralAlgebraContextValuationSubringAlgebra _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedIntegralAlgebraContextValuationSubringTower _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedQPadicContextValuationSubringTower _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.LubinTate.padicCompletedLevelField_algebra _root_.LubinTate.padicCompletedLevelField_isGalois _root_.LubinTate.padicCompletedUnramifiedFieldAlgebra _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.instTopologicalSpaceLocalAlgebra _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.RayClass.approximationCompletionTopologicalSpace _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.adicCompletionProperSpace _root_.chosenFinitePlaceCompletionAlgebra _root_.chosenFinitePlaceLocalizedIsGalois _root_.cyclicPrimeDegreeIntermediate_isGalois _root_.cyclicPrimeSubextension_isGalois _root_.finiteLocalUnitsOpen _root_.finiteNormalClosure_isGalois _root_.infiniteAdeleRingT2Space _root_.relativeAdeleRingIntermediateAlgebra _root_.relativeAdeleRingTopIntermediateAlgebra
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI
attribute [local instance] OAI.starSubalgebraCommCStarAlgebra

set_option autoImplicit false

/-!
# Canonical unramified normalization

The canonical local norm-residue symbol is identified with the field-facing
unramified Artin map. An element of normalized valuation one maps to arithmetic
Frobenius, both algebraically and in the topological abelianization.
-/

noncomputable section

namespace LocalClassFieldTheory

open scoped IsMulCommutative ValuativeRel
open LocalFieldTheory RamificationTheory CyclicCohomology KummerTheory
open ClassFormation

section BasePrime

variable (K : Type) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]

/-- The concrete base-field unit represented by the canonical prime element
of the local henselian valuation. -/
noncomputable def localAbstractPrimeFieldUnit : Kˣ :=
  Additive.toMul
    ((baseUnitsEquivGaloisAmbientFixed K (SeparableClosure K)).symm
      ((localHenselianValuation K).chosenPrimeElement
        (intrinsicFiniteAbstractBase K)))

end BasePrime

end LocalClassFieldTheory
end
end

section
-- module Solutions.OAIQ244_DUKE.LocalField_DiscreteValuationField_PadicValuationComparison
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalClassFieldTheory.finiteGaloisLocalField_integerRing_moduleFinite _root_.LocalClassFieldTheory.localSeparableValuationHasExtension _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.residueFieldZModAlgebra _root_.LocalFieldTheory.DiscreteValuationField.finite_principalUnits_nthPowerKernel _root_.LocalFieldTheory.DiscreteValuationField.finite_residueRootsOfUnityGroup _root_.LocalFieldTheory.DiscreteValuationField.finite_valuationSubringUnits_nthPowerKernel _root_.LocalFieldTheory.DiscreteValuationField.finite_valuationSubringUnits_nthPowerQuotient _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.LubinTate.padicCompletedLevelCompleteDVF_hasExtensionInstance _root_.LubinTate.standardLubinTateLevelCompleteDVF_hasExtensionInstance _root_.LubinTate.standardLubinTateLevelField_galFinite _root_.LubinTate.standardLubinTateLevelField_isAbelianGalois _root_.LubinTate.standardLubinTateLevelField_isMulCommutative _root_.LubinTate.standardLubinTateLevelValuationSubring_moduleFinite _root_.LubinTate.standardLubinTateUnitParameter_commGroup _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.instTopologicalSpaceLocalAlgebra _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionResidueField.instField _root_.RayClass.approximationCompletionTopologicalSpace _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.LocalClassFieldTheory.localAbsoluteValuationHasExtension _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.LocalClassFieldTheory.comparisonIntegerRingIsIntegralClosure _root_.LocalClassFieldTheory.normalizationIntegerRingIsIntegralClosure _root_.RamificationTheory.HilbertRamification.CompleteDVF.decompositionGroupMulSemiringAction _root_.RamificationTheory.HilbertRamification.CompleteDVF.decompositionGroupResidueFieldMulSemiringAction _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.chosenFinitePlaceBaseIsNonarchimedeanLocalField _root_.chosenFinitePlaceBaseValuativeRel _root_.finiteLocalUnitsOpen _root_.infiniteAdeleRingT2Space
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

/-- Conversely, any valuation extension of the valuation selected by
`padicLocalField p` is also an extension of the canonical complete-DVF
valuation on `ℚ_[p]`. -/
theorem localCompleteDVFValuation_hasExtension_of_padicLocalField
    (p : ℕ) [Fact p.Prime]
    {E : Type u} [Field E] [Algebra ℚ_[p] E]
    {Gamma : Type v} [LinearOrderedCommGroupWithZero Gamma]
    (wE : _root_.Valuation E Gamma)
    [(padicLocalField p).toCompleteDVF.valuation.HasExtension wE] :
    (LocalFieldTheory.localCompleteDVF ℚ_[p]).valuation.HasExtension wE :=
  ValuationTheory.DiscreteValuationField.ValuedExtension.hasExtension_of_isEquiv_base
    (localCompleteDVF_valuation_isEquiv_padicLocalField p)

end Qp
end Examples
end DiscreteValuationField
end LocalFieldTheory
end
end

section
-- module Solutions.OAIQ244_DUKE.LubinTate_Padic_CompletedUnramifiedField
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 400000
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalClassFieldTheory.finiteGaloisLocalField_integerRing_moduleFinite _root_.LocalClassFieldTheory.localSeparableValuationHasExtension _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.AdicPrincipalUnits.instAddCommGroup _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.AdicPrincipalUnits.instTopologicalSpace _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.DiscretePrincipalUnitQuotient.instAddCommGroup _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.DiscretePrincipalUnitQuotient.instDiscreteTopology _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.DiscretePrincipalUnitQuotient.instTopologicalSpace _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitInverseLimitCarrierPadicModule _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitInverseLimitCarrierPadicSMul _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitQuotientCarrierPadicModule _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitQuotientCarrier_finite _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.PrincipalUnitProdiscreteLimit.instAddCommGroup _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.PrincipalUnitProdiscreteLimit.instTopologicalSpace _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.adicPrincipalUnitsContinuousAdd _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.adicPrincipalUnitsContinuousSMul _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.adicPrincipalUnitsPadicModule _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.adicPrincipalUnitsT2Space _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.discretePrincipalUnitQuotientFinite _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.discretePrincipalUnitQuotientPadicModule _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitPadicModule _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitPadicSMul _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitProdiscreteLimitContinuousAdd _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitProdiscreteLimitContinuousSMul _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitProdiscreteLimitPadicModule _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitProdiscreteLimitT2Space _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.residueFieldZModAlgebra _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedIntegralAlgebraContextFieldAlgebra _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedIntegralAlgebraContextQPadic _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedIntegralAlgebraContextQPadicTower _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedIntegralAlgebraContextValuationSubringAlgebra _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedIntegralAlgebraContextValuationSubringTower _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedIntegralLatticeContextAlgebra _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedIntegralLatticeContextModuleFinite _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedIntegralLatticeContextModuleFree _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedMaximalIdealPowContextModuleFinite _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedMaximalIdealPowContextModuleFree _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedQPadicContextAlgebra _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedQPadicContextFact _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedQPadicContextFiniteDimensional _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedQPadicContextValuationExtension _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedQPadicContextValuationSubringTower _root_.LocalFieldTheory.DiscreteValuationField.finite_principalUnits_nthPowerKernel _root_.LocalFieldTheory.DiscreteValuationField.finite_residueRootsOfUnityGroup _root_.LocalFieldTheory.DiscreteValuationField.finite_valuationSubringUnits_nthPowerKernel _root_.LocalFieldTheory.DiscreteValuationField.finite_valuationSubringUnits_nthPowerQuotient _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.LubinTate.Valuations.exponentialValuationSubringIsLocalRing _root_.LubinTate.padicCompletedLevelCompleteDVF_hasExtensionInstance _root_.LubinTate.padicCompletedLevelField_algebra _root_.LubinTate.padicCompletedLevelField_finiteDimensional _root_.LubinTate.padicCompletedLevelField_isGalois _root_.LubinTate.standardLubinTateLevelCompleteDVF_hasExtensionInstance _root_.LubinTate.standardLubinTateLevelField_galFinite _root_.LubinTate.standardLubinTateLevelField_isAbelianGalois _root_.LubinTate.standardLubinTateLevelField_isMulCommutative _root_.LubinTate.standardLubinTateLevelValuationSubring_moduleFinite _root_.LubinTate.standardLubinTateUnitParameter_commGroup _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RamificationTheory.HilbertRamification.Higher.lowerRamificationGroup.instNormal _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionFixedSubring.instIsLocalRing _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionResidueField.instField _root_.RamificationTheory.HilbertRamification.ValuationSubring.selectedResidueField.instAlgebra _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.LocalClassFieldTheory.localAbsoluteValuationHasExtension _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.LocalClassFieldTheory.comparisonIntegerRingIsIntegralClosure _root_.LocalClassFieldTheory.normalizationIntegerRingIsIntegralClosure _root_.RamificationTheory.HilbertRamification.CompleteDVF.decompositionGroupMulSemiringAction _root_.RamificationTheory.HilbertRamification.CompleteDVF.decompositionGroupResidueFieldMulSemiringAction _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.chosenFinitePlaceCompletionAlgebra _root_.finiteLocalUnitsOpen _root_.infiniteAdeleRingT2Space _root_.relativeAdeleRingIntermediateAlgebra _root_.relativeAdeleRingTopIntermediateAlgebra
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

/-!
# The p-adic completed-unramified coefficient field

The coefficient ring used by the mixed-characteristic changed-uniformizer
construction is

`W(AlgebraicClosure (ZMod p))`.

Its fraction field is the completed maximal-unramified coefficient field.
This file equips that existing mathlib fraction field with its canonical
`ℚ_[p]`-algebra structure.  Mathlib's fraction-field Frobenius then becomes
an actual `ℚ_[p]`-algebra automorphism.  No second Witt ring, p-adic field,
or Frobenius is introduced.
-/

noncomputable section

namespace LubinTate

open Filter
open LocalFieldTheory.DiscreteValuationField
open LocalFieldTheory.DiscreteValuationField.Examples.Qp
open ValuationTheory.DiscreteValuationField
open scoped Topology Valued WithZero

/-- The canonical valuation on the completed-unramified coefficient field
extends the p-adic valuation.  This is obtained from the actual local map of
valuation rings, rather than postulated as part of the completed field
structure. -/
theorem padicCompletedUnramifiedValuation_hasExtension
    (p : ℕ) [Fact p.Prime] :
    (padicLocalField p).toCompleteDVF.valuation.HasExtension
      (padicCompletedUnramifiedCompleteDVF p).valuation := by
  let f := padicCompletedUnramifiedIntegerMap p
  let : IsLocalHom f := by
    apply ((IsLocalRing.local_hom_TFAE f).out (3-1) (1-1)).mp
    rw [padicCompletedUnramifiedIntegerMap_map_maximalIdeal]
  exact
    ValuationTheory.DiscreteValuationField.ValuedExtension.valuation_hasExtension_of_local_valuationSubring_map
        (padicLocalField p).toCompleteDVF
        (padicCompletedUnramifiedCompleteDVF p)
        f
        (padicCompletedUnramifiedIntegerMap_coe p)

end LubinTate

end
end

section
-- module Solutions.OAIQ244_DUKE.LubinTate_Padic_CompletedLevel
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 400000
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalClassFieldTheory.finiteGaloisLocalField_integerRing_moduleFinite _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.residueFieldZModAlgebra _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedIntegralAlgebraContextValuationSubringAlgebra _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionResidueField.instField _root_.RamificationTheory.HilbertRamification.ValuationSubring.selectedResidueField.instAlgebra _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.LocalClassFieldTheory.comparisonIntegerRingIsIntegralClosure _root_.LocalClassFieldTheory.normalizationIntegerRingIsIntegralClosure _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.chosenFinitePlaceCompletionAlgebra _root_.finiteLocalUnitsOpen _root_.infiniteAdeleRingT2Space _root_.relativeAdeleRingIntermediateAlgebra _root_.relativeAdeleRingTopIntermediateAlgebra
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

/-!
# Completed p-adic Lubin--Tate levels

For the completed maximal-unramified coefficient field

`E = Frac(W(AlgebraicClosure (ZMod p)))`,

this file base-changes the standard primitive Lubin--Tate polynomial from
`ℚ_[p]` to `E` and takes its actual splitting field.  The complete discrete
valuation on that finite separable extension is selected from the integral
closure of the canonical Witt valuation ring.  This is the mixed-
characteristic evaluation field needed by the changed-uniformizer descent.

The integral polynomial, splitting field, and valuations below are the
existing mathlib/LCFT objects.  No parallel p-adic field, integer ring, or
completion is introduced.
-/

noncomputable section

open Filter
open scoped Polynomial
open scoped PowerSeries
open scoped PowerSeries.WithPiTopology

namespace LubinTate

open LocalFieldTheory.DiscreteValuationField
open LocalFieldTheory.DiscreteValuationField.Examples.Qp
open ValuationTheory.DiscreteValuationField
open ValuationTheory.DiscreteValuationField.ValuedExtension

/-- The completed primitive polynomial splits over the completed level. -/
theorem padicCompletedPrimitivePolynomial_splits
    (p : ℕ) [Fact p.Prime] (n : ℕ) :
    ((padicCompletedPrimitivePolynomial p n).map
      (algebraMap (padicCompletedUnramifiedField p)
        (padicCompletedLevelField p n))).Splits :=
  Polynomial.SplittingField.splits
    (padicCompletedPrimitivePolynomial p n)

/-- The roots of the completed primitive polynomial generate its splitting
field. -/
theorem padicCompletedPrimitivePolynomial_adjoin_rootSet
    (p : ℕ) [Fact p.Prime] (n : ℕ) :
    Algebra.adjoin (padicCompletedUnramifiedField p)
        ((padicCompletedPrimitivePolynomial p n).rootSet
          (padicCompletedLevelField p n) :
          Set (padicCompletedLevelField p n)) =
      ⊤ :=
  Polynomial.SplittingField.adjoin_rootSet
    (padicCompletedPrimitivePolynomial p n)

end LubinTate

end
end

section
-- module Solutions.OAIQ244_DUKE.LubinTate_Padic_CompletedPrimitiveIrreducible
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 400000
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_isCompleteDiscrete _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalClassFieldTheory.finiteGaloisLocalField_integerRing_moduleFinite _root_.LocalClassFieldTheory.localSeparableValuationHasExtension _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.AdicPrincipalUnits.instAddCommGroup _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.AdicPrincipalUnits.instTopologicalSpace _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.DiscretePrincipalUnitQuotient.instAddCommGroup _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.DiscretePrincipalUnitQuotient.instDiscreteTopology _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.DiscretePrincipalUnitQuotient.instTopologicalSpace _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitInverseLimitCarrierPadicModule _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitInverseLimitCarrierPadicSMul _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitQuotientCarrierPadicModule _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitQuotientCarrier_finite _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.PrincipalUnitProdiscreteLimit.instAddCommGroup _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.PrincipalUnitProdiscreteLimit.instTopologicalSpace _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.adicPrincipalUnitsContinuousAdd _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.adicPrincipalUnitsContinuousSMul _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.adicPrincipalUnitsPadicModule _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.adicPrincipalUnitsT2Space _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.discretePrincipalUnitQuotientFinite _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.discretePrincipalUnitQuotientPadicModule _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitPadicModule _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitPadicSMul _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitProdiscreteLimitContinuousAdd _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitProdiscreteLimitContinuousSMul _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitProdiscreteLimitPadicModule _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitProdiscreteLimitT2Space _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.residueFieldZModAlgebra _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedIntegralAlgebraContextFieldAlgebra _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedIntegralAlgebraContextQPadic _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedIntegralAlgebraContextQPadicTower _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedIntegralAlgebraContextValuationSubringAlgebra _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedIntegralAlgebraContextValuationSubringTower _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedIntegralLatticeContextAlgebra _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedIntegralLatticeContextModuleFinite _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedIntegralLatticeContextModuleFree _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedMaximalIdealPowContextModuleFinite _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedMaximalIdealPowContextModuleFree _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedQPadicContextAlgebra _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedQPadicContextFact _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedQPadicContextFiniteDimensional _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedQPadicContextValuationExtension _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedQPadicContextValuationSubringTower _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedWithZeroValuationContextIntegralAlgebra _root_.LocalFieldTheory.DiscreteValuationField.finite_principalUnits_nthPowerKernel _root_.LocalFieldTheory.DiscreteValuationField.finite_residueRootsOfUnityGroup _root_.LocalFieldTheory.DiscreteValuationField.finite_valuationSubringUnits_nthPowerKernel _root_.LocalFieldTheory.DiscreteValuationField.finite_valuationSubringUnits_nthPowerQuotient _root_.LocalFieldTheory.Padic.padicDVR_residueField_finite _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.LubinTate.Valuations.exponentialValuationSubringIsLocalRing _root_.LubinTate.standardLubinTateLevelField_galFinite _root_.LubinTate.standardLubinTateLevelField_isAbelianGalois _root_.LubinTate.standardLubinTateLevelField_isMulCommutative _root_.LubinTate.standardLubinTateUnitParameter_commGroup _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RamificationTheory.HilbertRamification.Higher.lowerRamificationGroup.instNormal _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionFixedMaximalIdeal.instIsMaximal _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionFixedSubring.instIsLocalRing _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionResidueField.instField _root_.RamificationTheory.HilbertRamification.ValuationSubring.selectedResidueField.instAlgebra _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.LocalClassFieldTheory.localAbsoluteValuationHasExtension _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.LocalClassFieldTheory.comparisonIntegerRingIsIntegralClosure _root_.LocalClassFieldTheory.normalizationIntegerRingIsIntegralClosure _root_.RamificationTheory.HilbertRamification.CompleteDVF.decompositionGroupMulSemiringAction _root_.RamificationTheory.HilbertRamification.CompleteDVF.decompositionGroupResidueFieldMulSemiringAction _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.chosenFinitePlaceCompletionAlgebra _root_.chosenFinitePlaceLocalizedIntegerAlgebra _root_.finiteLocalUnitsOpen _root_.infiniteAdeleRingT2Space _root_.relativeAdeleRingIntermediateAlgebra _root_.relativeAdeleRingTopIntermediateAlgebra
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

/-!
# Irreducibility of the completed p-adic primitive polynomial

The standard multiplicative Lubin--Tate primitive polynomial remains
Eisenstein after extending its integer coefficients to the valuation ring of
the completed maximal unramified field.  In particular it remains
irreducible over the completed-unramified fraction field.
-/

noncomputable section

open scoped Polynomial

namespace LubinTate

open LocalFieldTheory.DiscreteValuationField
open LocalFieldTheory.DiscreteValuationField.Examples.Qp
open ValuationTheory.DiscreteValuationField

/-- The image of the canonical p-adic uniformizer is a uniformizer of the
completed-unramified coefficient field. -/
theorem padicCompletedUnramifiedIntegerMap_isUniformizer
    (p : ℕ) [Fact p.Prime] :
    let π :=
      padicIntEquivValuationSubring p (p : ℤ_[p])
    (padicCompletedUnramifiedCompleteDVF p).valuation.IsUniformizer
      ((padicCompletedUnramifiedIntegerMap p π :
        (padicCompletedUnramifiedCompleteDVF p).valuationSubring) :
          padicCompletedUnramifiedField p) := by
  let F := padicLocalField p
  let base := F.toCompleteDVF
  let target := padicCompletedUnramifiedCompleteDVF p
  let π : (padicLocalField p).valuationSubring :=
    padicIntEquivValuationSubring p (p : ℤ_[p])
  let πE : target.valuationSubring :=
    padicCompletedUnramifiedIntegerMap p π
  have hπ : base.valuation.IsUniformizer (π : ℚ_[p]) := by
    simpa only [F, base, π] using
      padicMultiplicativeLubinTateSeries_isUniformizer p
  obtain ⟨ϖ, hϖ⟩ := target.exists_uniformizer
  apply hϖ.of_associated
  rw [← Ideal.span_singleton_eq_span_singleton]
  calc
    Ideal.span ({ϖ} : Set target.valuationSubring) =
        target.maximalIdeal :=
      (target.maximalIdeal_eq_span_uniformizer hϖ).symm
    _ =
        Ideal.map (padicCompletedUnramifiedIntegerMap p)
          base.maximalIdeal := by
      simpa only [F, base, target] using
        (padicCompletedUnramifiedIntegerMap_map_maximalIdeal p).symm
    _ =
        Ideal.map (padicCompletedUnramifiedIntegerMap p)
          (Ideal.span
            ({π} : Set (padicLocalField p).valuationSubring)) := by
      exact congrArg (Ideal.map (padicCompletedUnramifiedIntegerMap p))
        (base.maximalIdeal_eq_span_uniformizer hπ)
    _ = Ideal.span ({πE} : Set target.valuationSubring) := by
      rw [Ideal.map_span, Set.image_singleton]

/-- The completed integral primitive polynomial has the same positive degree
as the original finite multiplicative Lubin--Tate polynomial. -/
theorem padicCompletedPrimitivePolynomialInteger_natDegree
    (p : ℕ) [Fact p.Prime] (n : ℕ) :
    (padicCompletedPrimitivePolynomialInteger p n).natDegree =
      (p - 1) * p ^ n := by
  exact ((padicCompletedPrimitivePolynomialInteger_monic p n).natDegree_map
    (algebraMap
      (padicCompletedUnramifiedCompleteDVF p).valuationSubring
      (padicCompletedUnramifiedField p))).symm.trans
    ((congrArg Polynomial.natDegree
      (padicCompletedPrimitivePolynomialInteger_map p n)).trans
      (padicCompletedPrimitivePolynomial_natDegree p n))

/-- The completed integral primitive polynomial is genuinely Eisenstein at
the maximal ideal of the completed-unramified valuation ring. -/
theorem padicCompletedPrimitivePolynomialInteger_isEisensteinAt
    (p : ℕ) [Fact p.Prime] (n : ℕ) :
    (padicCompletedPrimitivePolynomialInteger p n).IsEisensteinAt
      (padicCompletedUnramifiedCompleteDVF p).maximalIdeal := by
  let target := padicCompletedUnramifiedCompleteDVF p
  let π : (padicLocalField p).valuationSubring :=
    padicIntEquivValuationSubring p (p : ℤ_[p])
  let πE : target.valuationSubring :=
    padicCompletedUnramifiedIntegerMap p π
  have hmonic :
      (padicCompletedPrimitivePolynomialInteger p n).Monic :=
    padicCompletedPrimitivePolynomialInteger_monic p n
  refine hmonic.isEisensteinAt_of_mem_of_notMem
    (IsLocalRing.maximalIdeal.isMaximal target.valuationSubring).ne_top
    ?_ ?_
  · intro i hi
    exact
      (padicCompletedPrimitivePolynomialInteger_isWeaklyEisensteinAt
        p n).mem hi
  · have hπE :
        target.valuation.IsUniformizer
          (πE : padicCompletedUnramifiedField p) := by
      simpa only [target, π, πE] using
        padicCompletedUnramifiedIntegerMap_isUniformizer p
    have hnotMem :
        πE ∉ target.maximalIdeal ^ 2 :=
      target.uniformizer_not_mem_maximalIdeal_sq hπE
    change ((standardLubinTatePrimitivePolynomial (padicLocalField p) π n).map
      (padicCompletedUnramifiedIntegerMap p)).coeff 0 ∉ target.maximalIdeal ^ 2
    rw [Polynomial.coeff_map, standardLubinTatePrimitivePolynomial_coeff_zero]
    exact hnotMem

/-- The completed integral primitive polynomial is irreducible in the
completed-unramified valuation ring. -/
theorem padicCompletedPrimitivePolynomialInteger_irreducible
    (p : ℕ) [Fact p.Prime] (n : ℕ) :
    Irreducible (padicCompletedPrimitivePolynomialInteger p n) := by
  apply
    (padicCompletedPrimitivePolynomialInteger_isEisensteinAt p n).irreducible
      (IsLocalRing.maximalIdeal.isMaximal
        (padicCompletedUnramifiedCompleteDVF p).valuationSubring).isPrime
      (padicCompletedPrimitivePolynomialInteger_monic p n).isPrimitive
  rw [padicCompletedPrimitivePolynomialInteger_natDegree]
  exact Nat.mul_pos
    (Nat.sub_pos_of_lt (Fact.out : p.Prime).one_lt)
    (Nat.pow_pos (Fact.out : p.Prime).pos)

/-- The primitive polynomial remains irreducible over the completed maximal
unramified p-adic field. -/
theorem padicCompletedPrimitivePolynomial_irreducible
    (p : ℕ) [Fact p.Prime] (n : ℕ) :
    Irreducible (padicCompletedPrimitivePolynomial p n) := by
  have hmap :
      Irreducible
        ((padicCompletedPrimitivePolynomialInteger p n).map
          (algebraMap
            (padicCompletedUnramifiedCompleteDVF p).valuationSubring
            (padicCompletedUnramifiedField p))) :=
    (Polynomial.Monic.irreducible_iff_irreducible_map_fraction_map
      (padicCompletedPrimitivePolynomialInteger_monic p n)).mp
      (padicCompletedPrimitivePolynomialInteger_irreducible p n)
  rwa [padicCompletedPrimitivePolynomialInteger_map] at hmap

end LubinTate

end
end

section
-- module Solutions.OAIQ244_DUKE.LubinTate_Padic_ChangedUniformizerIntertwiner_CompletedSeries
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 400000
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_isCompleteDiscrete _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalClassFieldTheory.finiteGaloisLocalField_integerRing_moduleFinite _root_.LocalClassFieldTheory.localSeparableValuationHasExtension _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.AdicPrincipalUnits.instAddCommGroup _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.AdicPrincipalUnits.instTopologicalSpace _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.DiscretePrincipalUnitQuotient.instAddCommGroup _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.DiscretePrincipalUnitQuotient.instDiscreteTopology _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.DiscretePrincipalUnitQuotient.instTopologicalSpace _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitInverseLimitCarrierPadicModule _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitInverseLimitCarrierPadicSMul _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitQuotientCarrierPadicModule _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitQuotientCarrier_finite _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.PrincipalUnitProdiscreteLimit.instAddCommGroup _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.PrincipalUnitProdiscreteLimit.instTopologicalSpace _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.adicPrincipalUnitsContinuousAdd _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.adicPrincipalUnitsContinuousSMul _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.adicPrincipalUnitsPadicModule _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.adicPrincipalUnitsT2Space _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.discretePrincipalUnitQuotientFinite _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.discretePrincipalUnitQuotientPadicModule _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitPadicModule _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitPadicSMul _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitProdiscreteLimitContinuousAdd _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitProdiscreteLimitContinuousSMul _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitProdiscreteLimitPadicModule _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitProdiscreteLimitT2Space _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.residueFieldZModAlgebra _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedIntegralAlgebraContextFieldAlgebra _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedIntegralAlgebraContextQPadic _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedIntegralAlgebraContextQPadicTower _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedIntegralAlgebraContextValuationSubringAlgebra _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedIntegralAlgebraContextValuationSubringTower _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedIntegralLatticeContextAlgebra _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedIntegralLatticeContextModuleFinite _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedIntegralLatticeContextModuleFree _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedMaximalIdealPowContextModuleFinite _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedMaximalIdealPowContextModuleFree _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedQPadicContextAlgebra _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedQPadicContextFact _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedQPadicContextFiniteDimensional _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedQPadicContextValuationExtension _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedQPadicContextValuationSubringTower _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedWithZeroValuationContextIntegralAlgebra _root_.LocalFieldTheory.DiscreteValuationField.finite_principalUnits_nthPowerKernel _root_.LocalFieldTheory.DiscreteValuationField.finite_residueRootsOfUnityGroup _root_.LocalFieldTheory.DiscreteValuationField.finite_valuationSubringUnits_nthPowerKernel _root_.LocalFieldTheory.DiscreteValuationField.finite_valuationSubringUnits_nthPowerQuotient _root_.LocalFieldTheory.Padic.padicDVR_residueField_finite _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.LubinTate.padicCompletedLevelCompleteDVF_hasExtensionInstance _root_.LubinTate.padicCompletedLevelField_algebra _root_.LubinTate.padicCompletedLevelField_finiteDimensional _root_.LubinTate.padicCompletedLevelField_isGalois _root_.LubinTate.standardLubinTateLevelField_galFinite _root_.LubinTate.standardLubinTateLevelField_isAbelianGalois _root_.LubinTate.standardLubinTateLevelField_isMulCommutative _root_.LubinTate.standardLubinTateUnitParameter_commGroup _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RamificationTheory.HilbertRamification.Higher.lowerRamificationGroup.instNormal _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionResidueField.instField _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.LocalClassFieldTheory.localAbsoluteValuationHasExtension _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.LocalClassFieldTheory.comparisonIntegerRingIsIntegralClosure _root_.LocalClassFieldTheory.normalizationIntegerRingIsIntegralClosure _root_.RamificationTheory.HilbertRamification.CompleteDVF.decompositionGroupMulSemiringAction _root_.RamificationTheory.HilbertRamification.CompleteDVF.decompositionGroupResidueFieldMulSemiringAction _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen _root_.infiniteAdeleRingT2Space
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

/-!
# Completed p-adic Lubin--Tate series

This module extends the multiplicative and changed-standard Lubin--Tate series to the completed unramified Witt ring and records their coefficients and residue reductions.
-/

noncomputable section

namespace LubinTate

open LocalFieldTheory.DiscreteValuationField
open LocalFieldTheory.DiscreteValuationField.Examples.Qp
open SameUniformizer

theorem padicCompletedChangedStandardSeries_constantCoeff
    (p : ℕ) [Fact p.Prime]
    (u : (padicLocalField p).valuationSubringˣ) :
    PowerSeries.constantCoeff
        (padicCompletedChangedStandardSeries p u) = 0 := by
  rw [← PowerSeries.coeff_zero_eq_constantCoeff,
    padicCompletedChangedStandardSeries,
    PowerSeries.coeff_map,
    PowerSeries.coeff_zero_eq_constantCoeff_apply,
    LubinTateSeries.constantCoeff_eq_zero,
    map_zero]

end LubinTate

end
end

section
-- module Solutions.OAIQ244_DUKE.LubinTate_Padic_ChangedUniformizerIntertwiner_DefectCorrection
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalClassFieldTheory.finiteGaloisLocalField_integerRing_moduleFinite _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitInverseLimitCarrierPadicModule _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitInverseLimitCarrierPadicSMul _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitQuotientCarrierPadicModule _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitQuotientCarrier_finite _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.adicPrincipalUnitsContinuousAdd _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.adicPrincipalUnitsContinuousSMul _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.adicPrincipalUnitsPadicModule _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.discretePrincipalUnitQuotientFinite _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.discretePrincipalUnitQuotientPadicModule _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitPadicModule _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitPadicSMul _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitProdiscreteLimitContinuousAdd _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitProdiscreteLimitContinuousSMul _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitProdiscreteLimitPadicModule _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.residueFieldZModAlgebra _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedIntegralAlgebraContextFieldAlgebra _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedIntegralAlgebraContextQPadic _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedIntegralAlgebraContextQPadicTower _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedIntegralAlgebraContextValuationSubringAlgebra _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedIntegralAlgebraContextValuationSubringTower _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedIntegralLatticeContextAlgebra _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedIntegralLatticeContextModuleFinite _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedIntegralLatticeContextModuleFree _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedMaximalIdealPowContextModuleFinite _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedMaximalIdealPowContextModuleFree _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedQPadicContextAlgebra _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedQPadicContextFact _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedQPadicContextFiniteDimensional _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedQPadicContextValuationExtension _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedQPadicContextValuationSubringTower _root_.LocalFieldTheory.DiscreteValuationField.finite_principalUnits_nthPowerKernel _root_.LocalFieldTheory.DiscreteValuationField.finite_residueRootsOfUnityGroup _root_.LocalFieldTheory.DiscreteValuationField.finite_valuationSubringUnits_nthPowerKernel _root_.LocalFieldTheory.DiscreteValuationField.finite_valuationSubringUnits_nthPowerQuotient _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.LubinTate.padicCompletedLevelCompleteDVF_hasExtensionInstance _root_.LubinTate.padicCompletedLevelField_algebra _root_.LubinTate.padicCompletedLevelField_finiteDimensional _root_.LubinTate.padicCompletedLevelField_isGalois _root_.LubinTate.standardLubinTateLevelField_galFinite _root_.LubinTate.standardLubinTateLevelField_isAbelianGalois _root_.LubinTate.standardLubinTateLevelField_isMulCommutative _root_.LubinTate.standardLubinTateUnitParameter_commGroup _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RamificationTheory.HilbertRamification.Higher.lowerRamificationGroup.instNormal _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionResidueField.instField _root_.RamificationTheory.HilbertRamification.ValuationSubring.selectedResidueField.instAlgebra _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.LocalClassFieldTheory.comparisonIntegerRingIsIntegralClosure _root_.LocalClassFieldTheory.normalizationIntegerRingIsIntegralClosure _root_.RamificationTheory.HilbertRamification.CompleteDVF.decompositionGroupMulSemiringAction _root_.RamificationTheory.HilbertRamification.CompleteDVF.decompositionGroupResidueFieldMulSemiringAction _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.chosenFinitePlaceCompletionAlgebra _root_.finiteLocalUnitsOpen _root_.infiniteAdeleRingT2Space _root_.relativeAdeleRingIntermediateAlgebra _root_.relativeAdeleRingTopIntermediateAlgebra
attribute [-simp] _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.GlobalClassFieldTheory.Reciprocity.rationalPrimeUnitValuationSubringUnit_coe _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.EqualCharacteristicLaurent.coeffHom_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.EqualCharacteristicLaurent.powerSeriesEvalHom_C _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.EqualCharacteristicLaurent.powerSeriesEvalHom_X _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.EqualCharacteristicLaurent.powerSeriesEvalSubringHom_C _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.EqualCharacteristicLaurent.powerSeriesEvalSubringHom_X _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.AdicPrincipalUnits.addEquiv_map_smul _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.AdicPrincipalUnits.val_of _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.DiscretePrincipalUnitQuotient.addEquiv_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.DiscretePrincipalUnitQuotient.addEquiv_map_smul _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.DiscretePrincipalUnitQuotient.addEquiv_of _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.DiscretePrincipalUnitQuotient.addEquiv_symm_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.DiscretePrincipalUnitQuotient.val_transition _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.adicPrincipalUnitsHomeomorphUnderlying_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.iwasawaGlobalInverseLimitCarrier_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitAddEquivInverseLimitCarrier_map_smul _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitAddHomeomorphInverseLimitCarrier_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitInverseLimitCarrierEval_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitInverseLimitCarrierPadic_smul_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitMulEquivInverseLimitCarrier_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitPadic_smul_carrier_coordinate _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitProdiscreteLimitHomeomorphUnderlying_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitQuotientCarrierPadicScalar_eq_smul _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitQuotientCarrierToFull_mk _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitQuotientCarrierTransition_mk _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.uniformizerHigherUnitQuotientEquiv_mk _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.PrincipalUnitProdiscreteLimit.addEquiv_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.PrincipalUnitProdiscreteLimit.addEquiv_map_smul _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.PrincipalUnitProdiscreteLimit.addEquiv_symm_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.PrincipalUnitProdiscreteLimit.coordinate_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.PrincipalUnitProdiscreteLimit.coordinate_smul _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.adicPrincipalUnitsAddEquivProdiscreteLimit_map_smul _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.adicPrincipalUnitsContinuousAddEquivUnderlyingOfWithZeroValuation_map_smul _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.adicPrincipalUnitsHomeomorphProdiscreteLimit_to_addEquiv _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.iwasawaDegreeTerm_zero _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.iwasawaGn_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.iwasawaPartialProduct_zero_input _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.iwasawaSeedAtLevel_val _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.iwasawaSeedIdeal_val _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.iwasawaSeed_val _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitPadic_natCast_smul _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitPadic_nsmul_eq_pow _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitPadic_smul_def _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitSuccQuotAddEquivResidue_iwasawaSeed _root_.LocalFieldTheory.DiscreteValuationField.LocalField.higherPrincipalUnitAddToFirst_smul _root_.LocalFieldTheory.DiscreteValuationField.LocalField.laurentSeriesEquivLaurentImageSubfield_apply_coe _root_.LocalFieldTheory.DiscreteValuationField.LocalField.padicIntToValuationSubring_coe _root_.LocalFieldTheory.DiscreteValuationField.LocalField.ratCastToQpadicClosureSubfield_apply _root_.LocalFieldTheory.DiscreteValuationField.LocalField.ratCastWithValToQpadicClosureSubfield_apply _root_.LocalFieldTheory.DiscreteValuationField.MultiplicativeIntegerValuation.fieldUnitDecompositionLogHomWithUniformizerValue_apply _root_.LocalFieldTheory.DiscreteValuationField.MultiplicativeIntegerValuation.fieldUnitDecompositionLogHomWithUniformizerValue_principal _root_.LocalFieldTheory.DiscreteValuationField.MultiplicativeIntegerValuation.fieldUnitDecompositionLogHomWithUniformizerValue_root _root_.LocalFieldTheory.DiscreteValuationField.MultiplicativeIntegerValuation.fieldUnitDecompositionLogHomWithUniformizerValue_uniformizer _root_.LocalFieldTheory.DiscreteValuationField.MultiplicativeIntegerValuation.fieldUnitLogHomWithUniformizerValue_apply _root_.LocalFieldTheory.DiscreteValuationField.MultiplicativeIntegerValuation.principalUnitExpSeriesHomOfMaximalIdealPow_apply _root_.LocalFieldTheory.DiscreteValuationField.MultiplicativeIntegerValuation.principalUnitLogSeriesHomOfWithZeroValuationScaled_apply_toAdd _root_.LocalFieldTheory.Padic.integerRingEquivPadicDVRValuationSubring_coe _root_.LocalFieldTheory.localIntegerValuationSubringEquiv_apply_coe _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.LocalFieldTheory.residueField_algebraMap_residue _root_.LubinTate.SameUniformizer.coeff_recursiveIntertwiner _root_.LubinTate.SameUniformizer.constantCoeff_inVariable _root_.LubinTate.SameUniformizer.intertwinerApproximation_zero _root_.LubinTate.SameUniformizer.standardLubinTateEndomorphism_coeff_one _root_.LubinTate.padicChangedUniformizerIntertwiner_coeff _root_.LubinTate.padicChangedUniformizerIntertwiner_coeff_one _root_.LubinTate.padicCompletedChangedStandardScalarEndomorphism_coeff_one _root_.LubinTate.padicCompletedChangedStandardScalarEndomorphism_one _root_.LubinTate.padicCompletedLevelPadicIntegerCoefficientHom_coe _root_.LubinTate.padicCompletedLevelPowerSeriesEval_C _root_.LubinTate.padicCompletedLevelPowerSeriesEval_X _root_.LubinTate.padicCompletedLevelPowerSeriesEval_coe _root_.LubinTate.padicCompletedLevelWittCoefficientHom_apply _root_.LubinTate.padicCompletedMultiplicativeScalarEndomorphismValue_one _root_.LubinTate.padicCompletedMultiplicativeScalarEndomorphism_coeff_one _root_.LubinTate.padicCompletedPrimitiveRootInteger_coe _root_.LubinTate.padicCompletedStandardScalarEndomorphismValue_one _root_.LubinTate.padicCompletedStandardScalarEndomorphism_one _root_.LubinTate.padicStandardToMultiplicativeIntertwiner_coeff_one _root_.LubinTate.standardLubinTateEndomorphismEvalAt_one _root_.LubinTate.standardLubinTateEndomorphismEvalAt_zero _root_.LubinTate.standardLubinTateEndomorphismValue_one _root_.LubinTate.standardLubinTateEndomorphismValue_zero _root_.LubinTate.standardLubinTateLevelCoefficientHom_apply _root_.LubinTate.standardLubinTateLevelPowerSeriesEval_C _root_.LubinTate.standardLubinTateLevelPowerSeriesEval_X _root_.LubinTate.standardLubinTateLevelPowerSeriesEval_coe _root_.LubinTate.standardLubinTatePrimitiveLevelAction_coe _root_.LubinTate.standardLubinTatePrimitivePointIntegerAction_one _root_.LubinTate.standardLubinTatePrimitivePointIterateInteger_zero _root_.LubinTate.standardLubinTatePrimitiveRootAction_one _root_.LubinTate.standardLubinTateUnitParameterAlgEquiv_apply_gen _root_.LubinTate.standardLubinTateUnitParameterAlgHom_apply_gen _root_.LubinTate.standardLubinTateUnitParameterChosenRepresentative_spec _root_.LubinTate.standardLubinTateUnitParameterEquivGal_apply _root_.LubinTate.standardLubinTateUnitParameterEquivGal_inv_class_apply_gen _root_.LubinTate.standardLubinTateUnitParameterLevelRoot_coe _root_.LubinTate.standardLubinTateUnitParameterLevelRoot_one _root_.LubinTate.standardLubinTateUnitParameterRoot_class _root_.LubinTate.standardLubinTateUnitParameterToGalHom_apply _root_.OAI.PrimeDegreePackets.ThetaConstruction.schwartzCM_apply _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteResidueActionOfHenselianDVF_apply _root_.RamificationTheory.HilbertRamification.CompleteDVF.decompositionResidueAction_algebraMap _root_.RamificationTheory.HilbertRamification.CompleteDVF.decompositionResidueAction_apply _root_.RamificationTheory.HilbertRamification.CompleteDVF.residueAction_apply _root_.RamificationTheory.HilbertRamification.Higher.dvfUniformizerQuotientUnit_mul_uniformizer _root_.RamificationTheory.HilbertRamification.Higher.dvfUniformizerRepresentativeHom_apply _root_.RamificationTheory.HilbertRamification.Higher.dvfValuationSubringUnitAut_apply _root_.RamificationTheory.HilbertRamification.Higher.intrinsicRamificationNumberOfUniqueExtension_one _root_.RamificationTheory.HilbertRamification.Higher.lowerRamificationGroup_neg_one _root_.RamificationTheory.HilbertRamification.Higher.mem_dvfHigherPrincipalUnitGroup_iff _root_.RamificationTheory.HilbertRamification.Higher.mem_lowerRamificationGroup_iff _root_.RamificationTheory.HilbertRamification.Higher.mem_valuationSubringDisplacementSubalgebraOfUniqueExtension_iff _root_.RamificationTheory.HilbertRamification.Higher.ramificationNumberDepthOfUniqueExtension_depth _root_.RamificationTheory.HilbertRamification.Higher.ramificationNumberOfUniqueExtension_one _root_.RamificationTheory.HilbertRamification.Higher.realRamificationIdeal_nat _root_.RamificationTheory.HilbertRamification.Higher.realRamificationIdeal_neg_one _root_.RamificationTheory.HilbertRamification.Higher.uniformizerGradedHom_mk _root_.RamificationTheory.HilbertRamification.Higher.valuationSubringAutOfUniqueExtension_apply_coe _root_.RamificationTheory.HilbertRamification.Higher.valuationSubringAutOfUniqueExtension_apply_inv_apply _root_.RamificationTheory.HilbertRamification.Higher.valuationSubringAutOfUniqueExtension_mul_apply _root_.RamificationTheory.HilbertRamification.Higher.valuationSubringAutOfUniqueExtension_one_apply _root_.RayClass.primesEquiv_val_eq_natGenerator _root_.LubinTate.standardLubinTateLevelAutomorphismIntegerRingEquiv_apply _root_.LubinTate.padicMultiplicativeLevelAutomorphismIntegerRingEquiv_apply _root_.infinitePlace_mult_smul
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

/-!
# Changed-uniformizer defect correction

This module computes how a degreewise correction changes the semilinear substitution defect and constructs the unique coefficient that kills that defect.
-/

noncomputable section

namespace LubinTate

open LocalFieldTheory.DiscreteValuationField
open LocalFieldTheory.DiscreteValuationField.Examples.Qp
open SameUniformizer

theorem padicChangedUniformizer_coeff_pow_add_monomial
    (p : ℕ) [Fact p.Prime]
    (H : PowerSeries (padicCompletedUnramifiedWittRing p))
    (hH : PowerSeries.constantCoeff H = 0)
    (m : ℕ) (hm : 2 ≤ m)
    (c : padicCompletedUnramifiedWittRing p) :
    PowerSeries.coeff m
        ((H + PowerSeries.monomial m c) ^ p) =
      PowerSeries.coeff m (H ^ p) := by
  let N := PowerSeries.monomial m c
  let A := H + N
  have hm0 : m ≠ 0 := by omega
  have hNconstant : PowerSeries.constantCoeff N = 0 := by
    rw [← PowerSeries.coeff_zero_eq_constantCoeff,
      PowerSeries.coeff_monomial, ite_eq_right (Ne.symm hm0)]
  have hAconstant : PowerSeries.constantCoeff A = 0 := by
    simp [A, hH, hNconstant]
  let Q :=
    ∑ i ∈ Finset.range p, A ^ i * H ^ (p - 1 - i)
  have hQ :
      ((p - 1 : ℕ) : ℕ∞) ≤ Q.order := by
    classical
    have hterm : ∀ i ∈ Finset.range p,
        ((p - 1 : ℕ) : ℕ∞) ≤
          (A ^ i * H ^ (p - 1 - i)).order := by
      intro i hi
      have hi' : i < p := Finset.mem_range.mp hi
      calc
        ((p - 1 : ℕ) : ℕ∞) =
            (i : ℕ∞) + ((p - 1 - i : ℕ) : ℕ∞) := by
          norm_cast
          omega
        _ ≤ (A ^ i).order + (H ^ (p - 1 - i)).order :=
          add_le_add
            (PowerSeries.le_order_pow_of_constantCoeff_eq_zero
              i hAconstant)
            (PowerSeries.le_order_pow_of_constantCoeff_eq_zero
              (p - 1 - i) hH)
        _ ≤ (A ^ i * H ^ (p - 1 - i)).order :=
          PowerSeries.le_order_mul _ _
    have hsum (s : Finset ℕ)
        (hs : ∀ i ∈ s,
          ((p - 1 : ℕ) : ℕ∞) ≤
            (A ^ i * H ^ (p - 1 - i)).order) :
        ((p - 1 : ℕ) : ℕ∞) ≤
          (∑ i ∈ s, A ^ i * H ^ (p - 1 - i)).order := by
      induction s using Finset.induction_on with
      | empty => simp
      | @insert i s hi ih =>
          rw [Finset.sum_insert hi]
          exact
            (le_min
              (hs i (Finset.mem_insert_self i s))
              (ih fun j hj =>
                hs j (Finset.mem_insert_of_mem hj))).trans
            (PowerSeries.min_order_le_order_add _ _)
    simpa only [Q] using hsum (Finset.range p) hterm
  have hNorder : (m : ℕ∞) ≤ N.order := by
    apply PowerSeries.nat_le_order
    intro i hi
    rw [PowerSeries.coeff_monomial, ite_eq_right]
    exact Nat.ne_of_lt hi
  have hfactor :
      (A - H) * Q = A ^ p - H ^ p := by
    exact (Commute.all A H).mul_geom_sum₂ p
  have horder :
      ((m + (p - 1) : ℕ) : ℕ∞) ≤
        (A ^ p - H ^ p).order := by
    calc
      ((m + (p - 1) : ℕ) : ℕ∞) =
          (m : ℕ∞) + ((p - 1 : ℕ) : ℕ∞) := by
        norm_cast
      _ ≤ (A - H).order + Q.order := by
        apply add_le_add
        · simpa [A, N] using hNorder
        · exact hQ
      _ ≤ ((A - H) * Q).order :=
        PowerSeries.le_order_mul _ _
      _ = (A ^ p - H ^ p).order := by
        rw [hfactor]
  have hpTwo : 2 ≤ p := (Fact.out : p.Prime).two_le
  have hltNat : m < m + (p - 1) := by omega
  have hlt :
      (m : ℕ∞) < (A ^ p - H ^ p).order := by
    have hcast :
        (m : ℕ∞) < ((m + (p - 1) : ℕ) : ℕ∞) := by
      exact_mod_cast hltNat
    exact hcast.trans_le horder
  have hcoeff :=
    PowerSeries.coeff_of_lt_order m hlt
  rw [map_sub, sub_eq_zero] at hcoeff
  exact hcoeff

theorem padicChangedUniformizer_coeff_subst_changed_add_monomial
    (p : ℕ) [Fact p.Prime]
    (u : (padicLocalField p).valuationSubringˣ)
    (H : PowerSeries (padicCompletedUnramifiedWittRing p))
    (hH : PowerSeries.constantCoeff H = 0)
    (m : ℕ) (hm : 2 ≤ m)
    (c : padicCompletedUnramifiedWittRing p) :
    PowerSeries.coeff m
        (PowerSeries.subst
          (H + PowerSeries.monomial m c)
          (padicCompletedChangedStandardSeries p u)) =
      PowerSeries.coeff m
          (PowerSeries.subst H
            (padicCompletedChangedStandardSeries p u)) +
        ((padicValuationUnitToCompletedUnramifiedWittUnit p u) :
            padicCompletedUnramifiedWittRing p) *
          (p : padicCompletedUnramifiedWittRing p) * c := by
  let a : padicCompletedUnramifiedWittRing p :=
    (padicValuationUnitToCompletedUnramifiedWittUnit p u :
      padicCompletedUnramifiedWittRing p) * (p : padicCompletedUnramifiedWittRing p)
  let N := PowerSeries.monomial m c
  let A := H + N
  have hHsubst : PowerSeries.HasSubst H :=
    PowerSeries.HasSubst.of_constantCoeff_zero' hH
  have hm0 : m ≠ 0 := by omega
  have hNconstant : PowerSeries.constantCoeff N = 0 := by
    rw [← PowerSeries.coeff_zero_eq_constantCoeff,
      PowerSeries.coeff_monomial, ite_eq_right (Ne.symm hm0)]
  have hAsubst : PowerSeries.HasSubst A :=
    PowerSeries.HasSubst.of_constantCoeff_zero' (by
      change PowerSeries.constantCoeff H +
          PowerSeries.constantCoeff N = 0
      rw [hH, hNconstant, zero_add])
  rw [padicCompletedChangedStandardSeries_eq,
    PowerSeries.subst_add hAsubst,
    PowerSeries.subst_mul hAsubst,
    PowerSeries.subst_C,
    PowerSeries.subst_X hAsubst,
    PowerSeries.subst_pow hAsubst,
    PowerSeries.subst_X hAsubst,
    PowerSeries.subst_add hHsubst,
    PowerSeries.subst_mul hHsubst,
    PowerSeries.subst_C,
    PowerSeries.subst_X hHsubst,
    PowerSeries.subst_pow hHsubst,
    PowerSeries.subst_X hHsubst]
  change
    PowerSeries.coeff m (PowerSeries.C a * A + A ^ p) =
      PowerSeries.coeff m (PowerSeries.C a * H + H ^ p) + a * c
  rw [map_add, map_add, PowerSeries.coeff_C_mul,
    PowerSeries.coeff_C_mul]
  change
    a * PowerSeries.coeff m A + PowerSeries.coeff m (A ^ p) =
      a * PowerSeries.coeff m H + PowerSeries.coeff m (H ^ p) +
        a * c
  rw [show PowerSeries.coeff m A =
      PowerSeries.coeff m H + c by
    simp [A, N],
    padicChangedUniformizer_coeff_pow_add_monomial p H hH m hm c]
  ring

/-- Adding a monomial in degree `m` changes the degree-`m` defect by the
explicit Frobenius-linear correction term. -/
theorem padicChangedUniformizerDefect_coeff_add_monomial
    (p : ℕ) [Fact p.Prime]
    (u : (padicLocalField p).valuationSubringˣ)
    (H : PowerSeries (padicCompletedUnramifiedWittRing p))
    (hH : PowerSeries.constantCoeff H = 0)
    (m : ℕ) (hm : 2 ≤ m)
    (c : padicCompletedUnramifiedWittRing p) :
    PowerSeries.coeff m
        (padicChangedUniformizerDefect p u
          (H + PowerSeries.monomial m c)) =
      PowerSeries.coeff m
          (padicChangedUniformizerDefect p u H) +
        (p : padicCompletedUnramifiedWittRing p) ^ m *
          WittVector.frobenius c -
        ((padicValuationUnitToCompletedUnramifiedWittUnit p u) :
            padicCompletedUnramifiedWittRing p) *
          (p : padicCompletedUnramifiedWittRing p) * c := by
  rw [padicChangedUniformizerDefect, map_sub,
    padicChangedUniformizer_coeff_subst_frobenius_add_monomial,
    padicChangedUniformizer_coeff_subst_changed_add_monomial
      p u H hH m hm c]
  rw [padicChangedUniformizerDefect, map_sub]
  ring

end LubinTate

end
end

section
-- module Solutions.OAIQ244_DUKE.LubinTate_Padic_ChangedUniformizerIntertwiner_IntertwinerConstruction
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 400000
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalClassFieldTheory.finiteGaloisLocalField_integerRing_moduleFinite _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitInverseLimitCarrierPadicModule _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitInverseLimitCarrierPadicSMul _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitQuotientCarrierPadicModule _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitQuotientCarrier_finite _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.adicPrincipalUnitsContinuousAdd _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.adicPrincipalUnitsContinuousSMul _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.adicPrincipalUnitsPadicModule _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.discretePrincipalUnitQuotientFinite _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.discretePrincipalUnitQuotientPadicModule _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitPadicModule _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitPadicSMul _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitProdiscreteLimitContinuousAdd _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitProdiscreteLimitContinuousSMul _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitProdiscreteLimitPadicModule _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.residueFieldZModAlgebra _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedIntegralAlgebraContextFieldAlgebra _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedIntegralAlgebraContextQPadic _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedIntegralAlgebraContextQPadicTower _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedIntegralAlgebraContextValuationSubringAlgebra _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedIntegralAlgebraContextValuationSubringTower _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedIntegralLatticeContextAlgebra _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedIntegralLatticeContextModuleFinite _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedIntegralLatticeContextModuleFree _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedMaximalIdealPowContextModuleFinite _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedMaximalIdealPowContextModuleFree _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedQPadicContextAlgebra _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedQPadicContextFact _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedQPadicContextFiniteDimensional _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedQPadicContextValuationExtension _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedQPadicContextValuationSubringTower _root_.LocalFieldTheory.DiscreteValuationField.finite_principalUnits_nthPowerKernel _root_.LocalFieldTheory.DiscreteValuationField.finite_residueRootsOfUnityGroup _root_.LocalFieldTheory.DiscreteValuationField.finite_valuationSubringUnits_nthPowerKernel _root_.LocalFieldTheory.DiscreteValuationField.finite_valuationSubringUnits_nthPowerQuotient _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.LubinTate.padicCompletedLevelCompleteDVF_hasExtensionInstance _root_.LubinTate.padicCompletedLevelField_algebra _root_.LubinTate.padicCompletedLevelField_finiteDimensional _root_.LubinTate.padicCompletedLevelField_isGalois _root_.LubinTate.standardLubinTateLevelField_galFinite _root_.LubinTate.standardLubinTateLevelField_isAbelianGalois _root_.LubinTate.standardLubinTateLevelField_isMulCommutative _root_.LubinTate.standardLubinTateUnitParameter_commGroup _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RamificationTheory.HilbertRamification.Higher.lowerRamificationGroup.instNormal _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionResidueField.instField _root_.RamificationTheory.HilbertRamification.ValuationSubring.selectedResidueField.instAlgebra _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.LocalClassFieldTheory.comparisonIntegerRingIsIntegralClosure _root_.LocalClassFieldTheory.normalizationIntegerRingIsIntegralClosure _root_.RamificationTheory.HilbertRamification.CompleteDVF.decompositionGroupMulSemiringAction _root_.RamificationTheory.HilbertRamification.CompleteDVF.decompositionGroupResidueFieldMulSemiringAction _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.chosenFinitePlaceCompletionAlgebra _root_.finiteLocalUnitsOpen _root_.infiniteAdeleRingT2Space _root_.relativeAdeleRingIntermediateAlgebra _root_.relativeAdeleRingTopIntermediateAlgebra
attribute [-simp] _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.GlobalClassFieldTheory.Reciprocity.rationalPrimeUnitValuationSubringUnit_coe _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.EqualCharacteristicLaurent.coeffHom_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.EqualCharacteristicLaurent.powerSeriesEvalHom_C _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.EqualCharacteristicLaurent.powerSeriesEvalHom_X _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.EqualCharacteristicLaurent.powerSeriesEvalSubringHom_C _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.EqualCharacteristicLaurent.powerSeriesEvalSubringHom_X _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.AdicPrincipalUnits.addEquiv_map_smul _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.AdicPrincipalUnits.val_of _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.DiscretePrincipalUnitQuotient.addEquiv_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.DiscretePrincipalUnitQuotient.addEquiv_map_smul _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.DiscretePrincipalUnitQuotient.addEquiv_of _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.DiscretePrincipalUnitQuotient.addEquiv_symm_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.DiscretePrincipalUnitQuotient.val_transition _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.adicPrincipalUnitsHomeomorphUnderlying_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.iwasawaGlobalInverseLimitCarrier_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitAddEquivInverseLimitCarrier_map_smul _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitAddHomeomorphInverseLimitCarrier_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitInverseLimitCarrierEval_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitInverseLimitCarrierPadic_smul_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitMulEquivInverseLimitCarrier_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitPadic_smul_carrier_coordinate _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitProdiscreteLimitHomeomorphUnderlying_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitQuotientCarrierPadicScalar_eq_smul _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitQuotientCarrierToFull_mk _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitQuotientCarrierTransition_mk _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.uniformizerHigherUnitQuotientEquiv_mk _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.PrincipalUnitProdiscreteLimit.addEquiv_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.PrincipalUnitProdiscreteLimit.addEquiv_map_smul _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.PrincipalUnitProdiscreteLimit.addEquiv_symm_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.PrincipalUnitProdiscreteLimit.coordinate_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.PrincipalUnitProdiscreteLimit.coordinate_smul _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.adicPrincipalUnitsAddEquivProdiscreteLimit_map_smul _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.adicPrincipalUnitsContinuousAddEquivUnderlyingOfWithZeroValuation_map_smul _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.adicPrincipalUnitsHomeomorphProdiscreteLimit_to_addEquiv _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.iwasawaDegreeTerm_zero _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.iwasawaGn_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.iwasawaPartialProduct_zero_input _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.iwasawaSeedAtLevel_val _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.iwasawaSeedIdeal_val _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.iwasawaSeed_val _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitPadic_natCast_smul _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitPadic_nsmul_eq_pow _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitPadic_smul_def _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitSuccQuotAddEquivResidue_iwasawaSeed _root_.LocalFieldTheory.DiscreteValuationField.LocalField.higherPrincipalUnitAddToFirst_smul _root_.LocalFieldTheory.DiscreteValuationField.LocalField.laurentSeriesEquivLaurentImageSubfield_apply_coe _root_.LocalFieldTheory.DiscreteValuationField.LocalField.padicIntToValuationSubring_coe _root_.LocalFieldTheory.DiscreteValuationField.LocalField.ratCastToQpadicClosureSubfield_apply _root_.LocalFieldTheory.DiscreteValuationField.LocalField.ratCastWithValToQpadicClosureSubfield_apply _root_.LocalFieldTheory.DiscreteValuationField.MultiplicativeIntegerValuation.fieldUnitDecompositionLogHomWithUniformizerValue_apply _root_.LocalFieldTheory.DiscreteValuationField.MultiplicativeIntegerValuation.fieldUnitDecompositionLogHomWithUniformizerValue_principal _root_.LocalFieldTheory.DiscreteValuationField.MultiplicativeIntegerValuation.fieldUnitDecompositionLogHomWithUniformizerValue_root _root_.LocalFieldTheory.DiscreteValuationField.MultiplicativeIntegerValuation.fieldUnitDecompositionLogHomWithUniformizerValue_uniformizer _root_.LocalFieldTheory.DiscreteValuationField.MultiplicativeIntegerValuation.fieldUnitLogHomWithUniformizerValue_apply _root_.LocalFieldTheory.DiscreteValuationField.MultiplicativeIntegerValuation.principalUnitExpSeriesHomOfMaximalIdealPow_apply _root_.LocalFieldTheory.DiscreteValuationField.MultiplicativeIntegerValuation.principalUnitLogSeriesHomOfWithZeroValuationScaled_apply_toAdd _root_.LocalFieldTheory.Padic.integerRingEquivPadicDVRValuationSubring_coe _root_.LocalFieldTheory.localIntegerValuationSubringEquiv_apply_coe _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.LocalFieldTheory.residueField_algebraMap_residue _root_.LubinTate.SameUniformizer.coeff_recursiveIntertwiner _root_.LubinTate.SameUniformizer.constantCoeff_inVariable _root_.LubinTate.SameUniformizer.intertwinerApproximation_zero _root_.LubinTate.SameUniformizer.standardLubinTateEndomorphism_coeff_one _root_.LubinTate.padicCompletedChangedStandardScalarEndomorphism_coeff_one _root_.LubinTate.padicCompletedChangedStandardScalarEndomorphism_one _root_.LubinTate.padicCompletedLevelPadicIntegerCoefficientHom_coe _root_.LubinTate.padicCompletedLevelPowerSeriesEval_C _root_.LubinTate.padicCompletedLevelPowerSeriesEval_X _root_.LubinTate.padicCompletedLevelPowerSeriesEval_coe _root_.LubinTate.padicCompletedLevelWittCoefficientHom_apply _root_.LubinTate.padicCompletedMultiplicativeScalarEndomorphismValue_one _root_.LubinTate.padicCompletedMultiplicativeScalarEndomorphism_coeff_one _root_.LubinTate.padicCompletedPrimitiveRootInteger_coe _root_.LubinTate.padicCompletedStandardScalarEndomorphismValue_one _root_.LubinTate.padicCompletedStandardScalarEndomorphism_one _root_.LubinTate.padicStandardToMultiplicativeIntertwiner_coeff_one _root_.LubinTate.standardLubinTateEndomorphismEvalAt_one _root_.LubinTate.standardLubinTateEndomorphismEvalAt_zero _root_.LubinTate.standardLubinTateEndomorphismValue_one _root_.LubinTate.standardLubinTateEndomorphismValue_zero _root_.LubinTate.standardLubinTateLevelCoefficientHom_apply _root_.LubinTate.standardLubinTateLevelPowerSeriesEval_C _root_.LubinTate.standardLubinTateLevelPowerSeriesEval_X _root_.LubinTate.standardLubinTateLevelPowerSeriesEval_coe _root_.LubinTate.standardLubinTatePrimitiveLevelAction_coe _root_.LubinTate.standardLubinTatePrimitivePointIntegerAction_one _root_.LubinTate.standardLubinTatePrimitivePointIterateInteger_zero _root_.LubinTate.standardLubinTatePrimitiveRootAction_one _root_.LubinTate.standardLubinTateUnitParameterAlgEquiv_apply_gen _root_.LubinTate.standardLubinTateUnitParameterAlgHom_apply_gen _root_.LubinTate.standardLubinTateUnitParameterChosenRepresentative_spec _root_.LubinTate.standardLubinTateUnitParameterEquivGal_apply _root_.LubinTate.standardLubinTateUnitParameterEquivGal_inv_class_apply_gen _root_.LubinTate.standardLubinTateUnitParameterLevelRoot_coe _root_.LubinTate.standardLubinTateUnitParameterLevelRoot_one _root_.LubinTate.standardLubinTateUnitParameterRoot_class _root_.LubinTate.standardLubinTateUnitParameterToGalHom_apply _root_.OAI.PrimeDegreePackets.ThetaConstruction.schwartzCM_apply _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteResidueActionOfHenselianDVF_apply _root_.RamificationTheory.HilbertRamification.CompleteDVF.decompositionResidueAction_algebraMap _root_.RamificationTheory.HilbertRamification.CompleteDVF.decompositionResidueAction_apply _root_.RamificationTheory.HilbertRamification.CompleteDVF.residueAction_apply _root_.RamificationTheory.HilbertRamification.Higher.dvfUniformizerQuotientUnit_mul_uniformizer _root_.RamificationTheory.HilbertRamification.Higher.dvfUniformizerRepresentativeHom_apply _root_.RamificationTheory.HilbertRamification.Higher.dvfValuationSubringUnitAut_apply _root_.RamificationTheory.HilbertRamification.Higher.intrinsicRamificationNumberOfUniqueExtension_one _root_.RamificationTheory.HilbertRamification.Higher.lowerRamificationGroup_neg_one _root_.RamificationTheory.HilbertRamification.Higher.mem_dvfHigherPrincipalUnitGroup_iff _root_.RamificationTheory.HilbertRamification.Higher.mem_lowerRamificationGroup_iff _root_.RamificationTheory.HilbertRamification.Higher.mem_valuationSubringDisplacementSubalgebraOfUniqueExtension_iff _root_.RamificationTheory.HilbertRamification.Higher.ramificationNumberDepthOfUniqueExtension_depth _root_.RamificationTheory.HilbertRamification.Higher.ramificationNumberOfUniqueExtension_one _root_.RamificationTheory.HilbertRamification.Higher.realRamificationIdeal_nat _root_.RamificationTheory.HilbertRamification.Higher.realRamificationIdeal_neg_one _root_.RamificationTheory.HilbertRamification.Higher.uniformizerGradedHom_mk _root_.RamificationTheory.HilbertRamification.Higher.valuationSubringAutOfUniqueExtension_apply_coe _root_.RamificationTheory.HilbertRamification.Higher.valuationSubringAutOfUniqueExtension_apply_inv_apply _root_.RamificationTheory.HilbertRamification.Higher.valuationSubringAutOfUniqueExtension_mul_apply _root_.RamificationTheory.HilbertRamification.Higher.valuationSubringAutOfUniqueExtension_one_apply _root_.RayClass.primesEquiv_val_eq_natGenerator _root_.LubinTate.standardLubinTateLevelAutomorphismIntegerRingEquiv_apply _root_.LubinTate.padicMultiplicativeLevelAutomorphismIntegerRingEquiv_apply _root_.infinitePlace_mult_smul
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

/-!
# Changed-uniformizer intertwiner construction

This module builds compatible finite-degree approximations, assembles the changed-uniformizer intertwiner, proves its functional equation, and establishes uniqueness.
-/

noncomputable section

namespace LubinTate

open LocalFieldTheory.DiscreteValuationField
open LocalFieldTheory.DiscreteValuationField.Examples.Qp
open SameUniformizer

theorem padicChangedUniformizerDefect_coeff_zero
    (p : ℕ) [Fact p.Prime]
    (u : (padicLocalField p).valuationSubringˣ) :
    PowerSeries.coeff 0
        (padicChangedUniformizerDefect p u
          (padicChangedUniformizerIntertwiner p u)) = 0 := by
  let H := padicChangedUniformizerIntertwiner p u
  have hH := padicChangedUniformizerIntertwiner_constantCoeff p u
  have hM := padicCompletedMultiplicativeSeries_constantCoeff p
  have hE := padicCompletedChangedStandardSeries_constantCoeff p u
  have hΦ :
      PowerSeries.constantCoeff
          (PowerSeries.map WittVector.frobenius H) = 0 :=
    padicChangedUniformizerFrobenius_constantCoeff_eq_zero p H hH
  rw [PowerSeries.coeff_zero_eq_constantCoeff_apply,
    padicChangedUniformizerDefect, map_sub]
  change
    MvPowerSeries.constantCoeff
        (PowerSeries.subst
          (padicCompletedMultiplicativeSeries p)
          (PowerSeries.map WittVector.frobenius H)) -
      MvPowerSeries.constantCoeff
        (PowerSeries.subst H
          (padicCompletedChangedStandardSeries p u)) = 0
  rw [PowerSeries.constantCoeff_subst_eq_zero hM
      (PowerSeries.map WittVector.frobenius H) hΦ,
    PowerSeries.constantCoeff_subst_eq_zero hH
      (padicCompletedChangedStandardSeries p u) hE,
    sub_zero]

/-- A zero-constant-coefficient solution of the changed-uniformizer
functional equation is determined by its linear coefficient. -/
theorem padicChangedUniformizerIntertwiner_unique
    (p : ℕ) [Fact p.Prime]
    (u : (padicLocalField p).valuationSubringˣ)
    {H H' : PowerSeries (padicCompletedUnramifiedWittRing p)}
    (hHconstant : PowerSeries.constantCoeff H = 0)
    (hH'constant : PowerSeries.constantCoeff H' = 0)
    (hlinear :
      PowerSeries.coeff 1 H = PowerSeries.coeff 1 H')
    (hH :
      PowerSeries.subst H
          (padicCompletedChangedStandardSeries p u) =
        PowerSeries.subst
          (padicCompletedMultiplicativeSeries p)
          (PowerSeries.map WittVector.frobenius H))
    (hH' :
      PowerSeries.subst H'
          (padicCompletedChangedStandardSeries p u) =
        PowerSeries.subst
          (padicCompletedMultiplicativeSeries p)
          (PowerSeries.map WittVector.frobenius H')) :
    H = H' := by
  have hHdefect :
      padicChangedUniformizerDefect p u H = 0 := by
    rw [padicChangedUniformizerDefect, hH, sub_self]
  have hH'defect :
      padicChangedUniformizerDefect p u H' = 0 := by
    rw [padicChangedUniformizerDefect, hH', sub_self]
  apply PowerSeries.ext
  intro m
  induction m using Nat.strongRecOn with
  | ind m ih =>
      by_cases hm0 : m = 0
      · subst m
        simp only [PowerSeries.coeff_zero_eq_constantCoeff_apply,
          hHconstant, hH'constant]
      by_cases hm1 : m = 1
      · subst m
        exact hlinear
      have hm : 2 ≤ m := by omega
      let c : padicCompletedUnramifiedWittRing p :=
        PowerSeries.coeff m H - PowerSeries.coeff m H'
      let A : PowerSeries (padicCompletedUnramifiedWittRing p) :=
        H' + PowerSeries.monomial m c
      have hAconstant : PowerSeries.constantCoeff A = 0 := by
        change PowerSeries.constantCoeff H' +
            PowerSeries.constantCoeff (PowerSeries.monomial m c) = 0
        rw [hH'constant,
          ← PowerSeries.coeff_zero_eq_constantCoeff,
          PowerSeries.coeff_monomial, ite_eq_right (Ne.symm hm0),
          zero_add]
      have hcoeff :
          ∀ q : ℕ, q ≤ m →
            PowerSeries.coeff q H = PowerSeries.coeff q A := by
        intro q hqm
        by_cases hq : q = m
        · subst q
          change PowerSeries.coeff m H =
            PowerSeries.coeff m H' +
              PowerSeries.coeff m (PowerSeries.monomial m c)
          rw [PowerSeries.coeff_monomial, ite_eq_left rfl]
          dsimp only [c]
          ring
        · have hqLt : q < m := lt_of_le_of_ne hqm hq
          change PowerSeries.coeff q H =
            PowerSeries.coeff q H' +
              PowerSeries.coeff q (PowerSeries.monomial m c)
          rw [PowerSeries.coeff_monomial, ite_eq_right hq]
          simp only [add_zero]
          exact ih q hqLt
      have hdefectA :
          PowerSeries.coeff m
              (padicChangedUniformizerDefect p u A) =
            0 := by
        calc
          PowerSeries.coeff m
              (padicChangedUniformizerDefect p u A) =
              PowerSeries.coeff m
                (padicChangedUniformizerDefect p u H) := by
            symm
            exact
              padicChangedUniformizerDefect_coeff_eq_of_coeff_eq_le
                p u hHconstant hAconstant m hcoeff
          _ = 0 := by rw [hHdefect, map_zero]
      have hcHomogeneous :
          (p : padicCompletedUnramifiedWittRing p) ^ m *
                WittVector.frobenius c -
              ((padicValuationUnitToCompletedUnramifiedWittUnit p u) :
                  padicCompletedUnramifiedWittRing p) *
                (p : padicCompletedUnramifiedWittRing p) * c =
            0 := by
        have hformula :=
          padicChangedUniformizerDefect_coeff_add_monomial
            p u H' hH'constant m hm c
        change
          PowerSeries.coeff m
              (padicChangedUniformizerDefect p u A) =
            PowerSeries.coeff m
                (padicChangedUniformizerDefect p u H') +
              (p : padicCompletedUnramifiedWittRing p) ^ m *
                WittVector.frobenius c -
              ((padicValuationUnitToCompletedUnramifiedWittUnit p u) :
                  padicCompletedUnramifiedWittRing p) *
                (p : padicCompletedUnramifiedWittRing p) * c at hformula
        rw [hdefectA, hH'defect, map_zero,
          zero_add] at hformula
        exact hformula.symm
      let V : (padicCompletedUnramifiedWittRing p)ˣ :=
        padicValuationUnitToCompletedUnramifiedWittUnit p u
      have hpne : (p : padicCompletedUnramifiedWittRing p) ≠ 0 :=
        WittVector.p_nonzero p (AlgebraicClosure (ZMod p))
      have hpow :
          (p : padicCompletedUnramifiedWittRing p) ^ m =
            (p : padicCompletedUnramifiedWittRing p) ^ (m - 1) *
              (p : padicCompletedUnramifiedWittRing p) := by
        calc
          (p : padicCompletedUnramifiedWittRing p) ^ m =
              (p : padicCompletedUnramifiedWittRing p) ^ ((m - 1) + 1) := by
            congr 1
            omega
          _ = (p : padicCompletedUnramifiedWittRing p) ^ (m - 1) *
              (p : padicCompletedUnramifiedWittRing p) := by
            rw [pow_succ]
      have hpCancel :
          (p : padicCompletedUnramifiedWittRing p) ^ (m - 1) *
                WittVector.frobenius c =
            (V : padicCompletedUnramifiedWittRing p) * c := by
        apply mul_left_cancel₀ hpne
        have heq := sub_eq_zero.mp hcHomogeneous
        change
          (p : padicCompletedUnramifiedWittRing p) *
              ((p : padicCompletedUnramifiedWittRing p) ^ (m - 1) *
                WittVector.frobenius c) =
            (p : padicCompletedUnramifiedWittRing p) *
              ((V : padicCompletedUnramifiedWittRing p) * c)
        calc
          (p : padicCompletedUnramifiedWittRing p) *
                ((p : padicCompletedUnramifiedWittRing p) ^ (m - 1) *
                  WittVector.frobenius c) =
              (p : padicCompletedUnramifiedWittRing p) ^ m *
                WittVector.frobenius c := by
            rw [hpow]
            ring
          _ =
              (V : padicCompletedUnramifiedWittRing p) *
                (p : padicCompletedUnramifiedWittRing p) * c :=
            heq
          _ =
              (p : padicCompletedUnramifiedWittRing p) *
                ((V : padicCompletedUnramifiedWittRing p) * c) := by
            ring
      have hcFixed :
          c =
            ((V⁻¹ : (padicCompletedUnramifiedWittRing p)ˣ) :
                padicCompletedUnramifiedWittRing p) *
              (p : padicCompletedUnramifiedWittRing p) ^ (m - 1) *
              WittVector.frobenius c := by
        calc
          c =
              ((V⁻¹ : (padicCompletedUnramifiedWittRing p)ˣ) :
                  padicCompletedUnramifiedWittRing p) *
                ((V : padicCompletedUnramifiedWittRing p) * c) := by
            simp
          _ =
              ((V⁻¹ : (padicCompletedUnramifiedWittRing p)ˣ) :
                  padicCompletedUnramifiedWittRing p) *
                ((p : padicCompletedUnramifiedWittRing p) ^ (m - 1) *
                  WittVector.frobenius c) := by
            rw [← hpCancel]
          _ =
              ((V⁻¹ : (padicCompletedUnramifiedWittRing p)ˣ) :
                  padicCompletedUnramifiedWittRing p) *
                (p : padicCompletedUnramifiedWittRing p) ^ (m - 1) *
                WittVector.frobenius c := by
            ring
      have hunique :=
        existsUnique_padicChangedUniformizerCoefficient p u m hm 0
      have hcSolution :
          c =
            0 +
              ((V⁻¹ : (padicCompletedUnramifiedWittRing p)ˣ) :
                  padicCompletedUnramifiedWittRing p) *
                (p : padicCompletedUnramifiedWittRing p) ^ (m - 1) *
                WittVector.frobenius c := by
        simpa only [zero_add] using hcFixed
      have hzeroSolution :
          (0 : padicCompletedUnramifiedWittRing p) =
            0 +
              ((V⁻¹ : (padicCompletedUnramifiedWittRing p)ˣ) :
                  padicCompletedUnramifiedWittRing p) *
                (p : padicCompletedUnramifiedWittRing p) ^ (m - 1) *
                WittVector.frobenius 0 := by
        simp
      have hcZero : c = 0 :=
        hunique.unique hcSolution hzeroSolution
      exact sub_eq_zero.mp (by simpa only [c] using hcZero)

end LubinTate

end
end

section
-- module Solutions.OAIQ244_DUKE.LubinTate_Padic_ChangedUniformizerIntertwiner_ScalarEndomorphisms
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 400000
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_isCompleteDiscrete _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalClassFieldTheory.finiteGaloisLocalField_integerRing_moduleFinite _root_.LocalClassFieldTheory.localDecompositionResidueFintype _root_.LocalClassFieldTheory.localSeparableValuationHasExtension _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.AdicPrincipalUnits.instAddCommGroup _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.AdicPrincipalUnits.instTopologicalSpace _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.DiscretePrincipalUnitQuotient.instAddCommGroup _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.DiscretePrincipalUnitQuotient.instDiscreteTopology _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.DiscretePrincipalUnitQuotient.instTopologicalSpace _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitInverseLimitCarrierPadicModule _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitInverseLimitCarrierPadicSMul _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitQuotientCarrierPadicModule _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitQuotientCarrier_finite _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.PrincipalUnitProdiscreteLimit.instAddCommGroup _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.PrincipalUnitProdiscreteLimit.instTopologicalSpace _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.adicPrincipalUnitsContinuousAdd _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.adicPrincipalUnitsContinuousSMul _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.adicPrincipalUnitsPadicModule _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.adicPrincipalUnitsT2Space _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.discretePrincipalUnitQuotientFinite _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.discretePrincipalUnitQuotientPadicModule _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitPadicModule _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitPadicSMul _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitProdiscreteLimitContinuousAdd _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitProdiscreteLimitContinuousSMul _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitProdiscreteLimitPadicModule _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitProdiscreteLimitT2Space _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.residueFieldZModAlgebra _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedIntegralAlgebraContextFieldAlgebra _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedIntegralAlgebraContextQPadic _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedIntegralAlgebraContextQPadicTower _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedIntegralAlgebraContextValuationSubringAlgebra _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedIntegralAlgebraContextValuationSubringTower _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedIntegralLatticeContextAlgebra _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedIntegralLatticeContextModuleFinite _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedIntegralLatticeContextModuleFree _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedMaximalIdealPowContextModuleFinite _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedMaximalIdealPowContextModuleFree _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedQPadicContextAlgebra _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedQPadicContextFact _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedQPadicContextFiniteDimensional _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedQPadicContextValuationExtension _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedQPadicContextValuationSubringTower _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedWithZeroValuationContextIntegralAlgebra _root_.LocalFieldTheory.DiscreteValuationField.finite_principalUnits_nthPowerKernel _root_.LocalFieldTheory.DiscreteValuationField.finite_residueRootsOfUnityGroup _root_.LocalFieldTheory.DiscreteValuationField.finite_valuationSubringUnits_nthPowerKernel _root_.LocalFieldTheory.DiscreteValuationField.finite_valuationSubringUnits_nthPowerQuotient _root_.LocalFieldTheory.Padic.padicDVR_residueField_finite _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.LubinTate.padicCompletedLevelCompleteDVF_hasExtensionInstance _root_.LubinTate.padicCompletedLevelField_algebra _root_.LubinTate.padicCompletedLevelField_finiteDimensional _root_.LubinTate.padicCompletedLevelField_isGalois _root_.LubinTate.standardLubinTateLevelField_galFinite _root_.LubinTate.standardLubinTateLevelField_isAbelianGalois _root_.LubinTate.standardLubinTateLevelField_isMulCommutative _root_.LubinTate.standardLubinTateUnitParameter_commGroup _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RamificationTheory.HilbertRamification.Higher.lowerRamificationGroup.instNormal _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionResidueField.instField _root_.RamificationTheory.HilbertRamification.ValuationSubring.selectedResidueField.instAlgebra _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.LocalClassFieldTheory.localAbsoluteValuationHasExtension _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.LocalClassFieldTheory.comparisonIntegerRingIsIntegralClosure _root_.LocalClassFieldTheory.normalizationIntegerRingIsIntegralClosure _root_.RamificationTheory.HilbertRamification.CompleteDVF.decompositionGroupMulSemiringAction _root_.RamificationTheory.HilbertRamification.CompleteDVF.decompositionGroupResidueFieldMulSemiringAction _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.chosenFinitePlaceCompletionAlgebra _root_.finiteLocalUnitsOpen _root_.infiniteAdeleRingT2Space _root_.relativeAdeleRingIntermediateAlgebra _root_.relativeAdeleRingTopIntermediateAlgebra
attribute [-simp] _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.GlobalClassFieldTheory.Reciprocity.rationalPrimeUnitValuationSubringUnit_coe _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.EqualCharacteristicLaurent.coeffHom_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.EqualCharacteristicLaurent.powerSeriesEvalHom_C _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.EqualCharacteristicLaurent.powerSeriesEvalHom_X _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.EqualCharacteristicLaurent.powerSeriesEvalSubringHom_C _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.EqualCharacteristicLaurent.powerSeriesEvalSubringHom_X _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.AdicPrincipalUnits.addEquiv_map_smul _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.AdicPrincipalUnits.of_val _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.AdicPrincipalUnits.val_of _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.DiscretePrincipalUnitQuotient.addEquiv_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.DiscretePrincipalUnitQuotient.addEquiv_map_smul _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.DiscretePrincipalUnitQuotient.addEquiv_of _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.DiscretePrincipalUnitQuotient.addEquiv_symm_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.DiscretePrincipalUnitQuotient.of_val _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.DiscretePrincipalUnitQuotient.val_of _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.DiscretePrincipalUnitQuotient.val_transition _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.adicPrincipalUnitsHomeomorphUnderlying_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.iwasawaGlobalInverseLimitCarrier_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitAddEquivInverseLimitCarrier_map_smul _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitAddHomeomorphInverseLimitCarrier_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitInverseLimitCarrierEval_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitInverseLimitCarrierPadic_smul_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitMulEquivInverseLimitCarrier_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitPadic_smul_carrier_coordinate _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitProdiscreteLimitHomeomorphUnderlying_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitQuotientCarrierPadicScalar_eq_smul _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitQuotientCarrierToFull_mk _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitQuotientCarrierTransition_mk _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.uniformizerHigherUnitQuotientEquiv_mk _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.PrincipalUnitProdiscreteLimit.addEquiv_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.PrincipalUnitProdiscreteLimit.addEquiv_map_smul _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.PrincipalUnitProdiscreteLimit.addEquiv_symm_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.PrincipalUnitProdiscreteLimit.coordinate_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.PrincipalUnitProdiscreteLimit.coordinate_smul _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.PrincipalUnitProdiscreteLimit.of_val _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.PrincipalUnitProdiscreteLimit.val_of _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.adicPrincipalUnitsAddEquivProdiscreteLimit_map_smul _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.adicPrincipalUnitsContinuousAddEquivUnderlyingOfWithZeroValuation_map_smul _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.adicPrincipalUnitsHomeomorphProdiscreteLimit_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.adicPrincipalUnitsHomeomorphProdiscreteLimit_to_addEquiv _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.iwasawaDegreeTerm_zero _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.iwasawaGn_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.iwasawaPartialProduct_zero_input _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.iwasawaSeedAtLevel_val _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.iwasawaSeedIdeal_val _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.iwasawaSeed_val _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitPadic_natCast_smul _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitPadic_nsmul_eq_pow _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitPadic_smul_def _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitSuccQuotAddEquivResidue_iwasawaSeed _root_.LocalFieldTheory.DiscreteValuationField.LocalField.higherPrincipalUnitAddToFirst_smul _root_.LocalFieldTheory.DiscreteValuationField.LocalField.laurentSeriesEquivLaurentImageSubfield_apply_coe _root_.LocalFieldTheory.DiscreteValuationField.LocalField.padicIntToValuationSubring_coe _root_.LocalFieldTheory.DiscreteValuationField.LocalField.ratCastToQpadicClosureSubfield_apply _root_.LocalFieldTheory.DiscreteValuationField.LocalField.ratCastWithValToQpadicClosureSubfield_apply _root_.LocalFieldTheory.DiscreteValuationField.MultiplicativeIntegerValuation.fieldUnitDecompositionLogHomWithUniformizerValue_apply _root_.LocalFieldTheory.DiscreteValuationField.MultiplicativeIntegerValuation.fieldUnitDecompositionLogHomWithUniformizerValue_principal _root_.LocalFieldTheory.DiscreteValuationField.MultiplicativeIntegerValuation.fieldUnitDecompositionLogHomWithUniformizerValue_root _root_.LocalFieldTheory.DiscreteValuationField.MultiplicativeIntegerValuation.fieldUnitDecompositionLogHomWithUniformizerValue_uniformizer _root_.LocalFieldTheory.DiscreteValuationField.MultiplicativeIntegerValuation.fieldUnitLogHomWithUniformizerValue_apply _root_.LocalFieldTheory.DiscreteValuationField.MultiplicativeIntegerValuation.principalUnitExpSeriesHomOfMaximalIdealPow_apply _root_.LocalFieldTheory.DiscreteValuationField.MultiplicativeIntegerValuation.principalUnitLogSeriesHomOfWithZeroValuationScaled_apply_toAdd _root_.LocalFieldTheory.Padic.integerRingEquivPadicDVRValuationSubring_coe _root_.LocalFieldTheory.localIntegerValuationSubringEquiv_apply_coe _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.LocalFieldTheory.residueField_algebraMap_residue _root_.LubinTate.padicCompletedLevelPadicIntegerCoefficientHom_coe _root_.LubinTate.padicCompletedLevelPowerSeriesEval_C _root_.LubinTate.padicCompletedLevelPowerSeriesEval_X _root_.LubinTate.padicCompletedLevelPowerSeriesEval_coe _root_.LubinTate.padicCompletedLevelWittCoefficientHom_apply _root_.LubinTate.padicCompletedMultiplicativeScalarEndomorphismValue_one _root_.LubinTate.padicCompletedPrimitiveRootInteger_coe _root_.LubinTate.padicCompletedStandardScalarEndomorphismValue_one _root_.LubinTate.padicCompletedStandardScalarEndomorphism_one _root_.LubinTate.padicStandardToMultiplicativeIntertwiner_coeff_one _root_.LubinTate.standardLubinTatePrimitivePointIterateInteger_zero _root_.LubinTate.standardLubinTateUnitParameterAlgEquiv_apply_gen _root_.LubinTate.standardLubinTateUnitParameterAlgHom_apply_gen _root_.LubinTate.standardLubinTateUnitParameterChosenRepresentative_spec _root_.LubinTate.standardLubinTateUnitParameterEquivGal_apply _root_.LubinTate.standardLubinTateUnitParameterEquivGal_inv_class_apply_gen _root_.LubinTate.standardLubinTateUnitParameterLevelRoot_coe _root_.LubinTate.standardLubinTateUnitParameterLevelRoot_one _root_.LubinTate.standardLubinTateUnitParameterRoot_class _root_.LubinTate.standardLubinTateUnitParameterToGalHom_apply _root_.OAI.PrimeDegreePackets.ThetaConstruction.schwartzCM_apply _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteResidueActionOfHenselianDVF_apply _root_.RamificationTheory.HilbertRamification.CompleteDVF.decompositionResidueAction_algebraMap _root_.RamificationTheory.HilbertRamification.CompleteDVF.decompositionResidueAction_apply _root_.RamificationTheory.HilbertRamification.CompleteDVF.galEquivDecompositionGroup_coe _root_.RamificationTheory.HilbertRamification.CompleteDVF.residueAction_apply _root_.RamificationTheory.HilbertRamification.Higher.dvfUniformizerQuotientUnit_mul_uniformizer _root_.RamificationTheory.HilbertRamification.Higher.dvfUniformizerRepresentativeHom_apply _root_.RamificationTheory.HilbertRamification.Higher.dvfValuationSubringUnitAut_apply _root_.RamificationTheory.HilbertRamification.Higher.intrinsicRamificationNumberOfUniqueExtension_one _root_.RamificationTheory.HilbertRamification.Higher.lowerRamificationGroup_neg_one _root_.RamificationTheory.HilbertRamification.Higher.mem_dvfHigherPrincipalUnitGroup_iff _root_.RamificationTheory.HilbertRamification.Higher.mem_lowerRamificationGroup_iff _root_.RamificationTheory.HilbertRamification.Higher.mem_valuationSubringDisplacementSubalgebraOfUniqueExtension_iff _root_.RamificationTheory.HilbertRamification.Higher.ramificationNumberDepthOfUniqueExtension_depth _root_.RamificationTheory.HilbertRamification.Higher.ramificationNumberOfUniqueExtension_one _root_.RamificationTheory.HilbertRamification.Higher.realRamificationIdeal_nat _root_.RamificationTheory.HilbertRamification.Higher.realRamificationIdeal_neg_one _root_.RamificationTheory.HilbertRamification.Higher.uniformizerGradedHom_mk _root_.RamificationTheory.HilbertRamification.Higher.valuationSubringAutOfUniqueExtension_apply_coe _root_.RamificationTheory.HilbertRamification.Higher.valuationSubringAutOfUniqueExtension_apply_inv_apply _root_.RamificationTheory.HilbertRamification.Higher.valuationSubringAutOfUniqueExtension_mul_apply _root_.RamificationTheory.HilbertRamification.Higher.valuationSubringAutOfUniqueExtension_one_apply _root_.RayClass.primesEquiv_val_eq_natGenerator _root_.LubinTate.standardLubinTateLevelAutomorphismIntegerRingEquiv_apply _root_.LubinTate.padicMultiplicativeLevelAutomorphismIntegerRingEquiv_apply _root_.infinitePlace_mult_smul
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

/-!
# Completed scalar endomorphisms

This module constructs the completed multiplicative and changed-standard scalar endomorphisms and proves their linear terms, composition laws, Frobenius invariance, and substitution commutation.
-/

noncomputable section

namespace LubinTate

open LocalFieldTheory.DiscreteValuationField
open LocalFieldTheory.DiscreteValuationField.Examples.Qp
open SameUniformizer

theorem
    padicCompletedChangedStandardScalarEndomorphism_constantCoeff
    (p : ℕ) [Fact p.Prime]
    (u : (padicLocalField p).valuationSubringˣ)
    (a : (padicLocalField p).valuationSubring) :
    PowerSeries.constantCoeff
        (padicCompletedChangedStandardScalarEndomorphism p u a) = 0 := by
  have hconstant :=
    (standardLubinTateEndomorphism_hasLinearTerm
      (standardLubinTateChangedUniformizer_isUniformizer
        (padicMultiplicativeLubinTateSeries_isUniformizer p) u)
      a).constantCoeff_eq_zero
  change
    padicValuationSubringToCompletedUnramifiedWittRing p
        (PowerSeries.constantCoeff
          (standardLubinTateEndomorphism
            (standardLubinTateChangedUniformizer_isUniformizer
              (padicMultiplicativeLubinTateSeries_isUniformizer p) u)
            a)) = 0
  rw [PowerSeries.constantCoeff_eq, hconstant, map_zero]

theorem padicMultiplicativeScalarEndomorphism_commutes
    (p : ℕ) [Fact p.Prime]
    (a : (padicLocalField p).valuationSubring) :
    PowerSeries.subst
        (recursiveIntertwiner
          (padicMultiplicativeLubinTateSeries_isUniformizer p)
          (padicMultiplicativeLubinTateSeries p)
          (padicMultiplicativeLubinTateSeries p)
          (fun _ : Unit => a))
        (padicMultiplicativeLubinTateSeries p).toPowerSeries =
      PowerSeries.subst
        (padicMultiplicativeLubinTateSeries p).toPowerSeries
        (recursiveIntertwiner
          (padicMultiplicativeLubinTateSeries_isUniformizer p)
          (padicMultiplicativeLubinTateSeries p)
          (padicMultiplicativeLubinTateSeries p)
          (fun _ : Unit => a)) := by
  have h :=
    recursiveIntertwiner_intertwines
      (padicMultiplicativeLubinTateSeries_isUniformizer p)
      (padicMultiplicativeLubinTateSeries p)
      (padicMultiplicativeLubinTateSeries p)
      (fun _ : Unit => a)
  calc
    _ =
        MvPowerSeries.subst
          (fun i : Unit =>
            inVariable (padicMultiplicativeLubinTateSeries p) i)
          (recursiveIntertwiner
            (padicMultiplicativeLubinTateSeries_isUniformizer p)
            (padicMultiplicativeLubinTateSeries p)
            (padicMultiplicativeLubinTateSeries p)
            (fun _ : Unit => a)) :=
      h
    _ = _ := by
      rw [PowerSeries.subst_def]
      congr 1
      funext i
      cases i
      exact
        PowerSeries.X_subst
          (padicMultiplicativeLubinTateSeries p).toPowerSeries

theorem padicChangedStandardScalarEndomorphism_commutes
    (p : ℕ) [Fact p.Prime]
    (u : (padicLocalField p).valuationSubringˣ)
    (a : (padicLocalField p).valuationSubring) :
    PowerSeries.subst
        (standardLubinTateEndomorphism
          (standardLubinTateChangedUniformizer_isUniformizer
            (padicMultiplicativeLubinTateSeries_isUniformizer p) u)
          a)
        (standardLubinTateSeries
          (standardLubinTateChangedUniformizer_isUniformizer
            (padicMultiplicativeLubinTateSeries_isUniformizer p) u)).toPowerSeries =
      PowerSeries.subst
        (standardLubinTateSeries
          (standardLubinTateChangedUniformizer_isUniformizer
            (padicMultiplicativeLubinTateSeries_isUniformizer p) u)).toPowerSeries
        (standardLubinTateEndomorphism
          (standardLubinTateChangedUniformizer_isUniformizer
            (padicMultiplicativeLubinTateSeries_isUniformizer p) u)
          a) := by
  let hπ :=
    standardLubinTateChangedUniformizer_isUniformizer
      (padicMultiplicativeLubinTateSeries_isUniformizer p) u
  have h :=
    standardLubinTateEndomorphism_intertwines hπ a
  calc
    _ =
        MvPowerSeries.subst
          (fun i : Unit => inVariable (standardLubinTateSeries hπ) i)
          (standardLubinTateEndomorphism hπ a) :=
      h
    _ = _ := by
      rw [PowerSeries.subst_def]
      congr 1
      funext i
      cases i
      exact PowerSeries.X_subst (standardLubinTateSeries hπ).toPowerSeries

/-- A completed multiplicative scalar endomorphism commutes with the
completed multiplicative Lubin--Tate series under substitution. -/
theorem padicCompletedMultiplicativeScalarEndomorphism_commutes
    (p : ℕ) [Fact p.Prime]
    (a : (padicLocalField p).valuationSubring) :
    PowerSeries.subst
        (padicCompletedMultiplicativeScalarEndomorphism p a)
        (padicCompletedMultiplicativeSeries p) =
      PowerSeries.subst
        (padicCompletedMultiplicativeSeries p)
        (padicCompletedMultiplicativeScalarEndomorphism p a) := by
  have hscalar :
      PowerSeries.HasSubst
        (recursiveIntertwiner
          (padicMultiplicativeLubinTateSeries_isUniformizer p)
          (padicMultiplicativeLubinTateSeries p)
          (padicMultiplicativeLubinTateSeries p)
          (fun _ : Unit => a)) :=
    (recursiveIntertwiner_hasLinearTerm
      (padicMultiplicativeLubinTateSeries_isUniformizer p)
      (padicMultiplicativeLubinTateSeries p)
      (padicMultiplicativeLubinTateSeries p)
      (fun _ : Unit => a)).hasSubst
  have hseries :
      PowerSeries.HasSubst
        (padicMultiplicativeLubinTateSeries p).toPowerSeries :=
    PowerSeries.HasSubst.of_constantCoeff_zero'
      (padicMultiplicativeLubinTateSeries p).constantCoeff_eq_zero
  have h :=
    congrArg
      (PowerSeries.map
        (padicValuationSubringToCompletedUnramifiedWittRing p))
      (padicMultiplicativeScalarEndomorphism_commutes p a)
  change MvPowerSeries.map _ _ = MvPowerSeries.map _ _ at h
  rw [PowerSeries.map_subst hscalar,
    PowerSeries.map_subst hseries] at h
  change
    PowerSeries.subst (PowerSeries.map _ _) (PowerSeries.map _ _) =
      PowerSeries.subst (PowerSeries.map _ _) (PowerSeries.map _ _) at h
  simpa only [padicCompletedMultiplicativeScalarEndomorphism,
    padicCompletedMultiplicativeSeries] using h

/-- A completed changed-standard scalar endomorphism commutes with the
completed changed-standard series under substitution. -/
theorem padicCompletedChangedStandardScalarEndomorphism_commutes
    (p : ℕ) [Fact p.Prime]
    (u : (padicLocalField p).valuationSubringˣ)
    (a : (padicLocalField p).valuationSubring) :
    PowerSeries.subst
        (padicCompletedChangedStandardScalarEndomorphism p u a)
        (padicCompletedChangedStandardSeries p u) =
      PowerSeries.subst
        (padicCompletedChangedStandardSeries p u)
        (padicCompletedChangedStandardScalarEndomorphism p u a) := by
  let hπ :=
    standardLubinTateChangedUniformizer_isUniformizer
      (padicMultiplicativeLubinTateSeries_isUniformizer p) u
  have hscalar :
      PowerSeries.HasSubst
        (standardLubinTateEndomorphism hπ a) :=
    (standardLubinTateEndomorphism_hasLinearTerm hπ a).hasSubst
  have hseries :
      PowerSeries.HasSubst
        (standardLubinTateSeries hπ).toPowerSeries :=
    PowerSeries.HasSubst.of_constantCoeff_zero'
      (standardLubinTateSeries hπ).constantCoeff_eq_zero
  have h :=
    congrArg
      (PowerSeries.map
        (padicValuationSubringToCompletedUnramifiedWittRing p))
      (padicChangedStandardScalarEndomorphism_commutes p u a)
  change MvPowerSeries.map _ _ = MvPowerSeries.map _ _ at h
  rw [PowerSeries.map_subst hscalar,
    PowerSeries.map_subst hseries] at h
  change
    PowerSeries.subst (PowerSeries.map _ _) (PowerSeries.map _ _) =
      PowerSeries.subst (PowerSeries.map _ _) (PowerSeries.map _ _) at h
  simpa only [padicCompletedChangedStandardScalarEndomorphism,
    padicCompletedChangedStandardSeries] using h

/-- Completed multiplicative scalar endomorphisms are fixed by coefficientwise
Witt-vector Frobenius. -/
theorem padicCompletedMultiplicativeScalarEndomorphism_frobenius
    (p : ℕ) [Fact p.Prime]
    (a : (padicLocalField p).valuationSubring) :
    PowerSeries.map WittVector.frobenius
        (padicCompletedMultiplicativeScalarEndomorphism p a) =
      padicCompletedMultiplicativeScalarEndomorphism p a := by
  apply PowerSeries.ext
  intro n
  simp [padicCompletedMultiplicativeScalarEndomorphism,
    PowerSeries.coeff_map,
    padicValuationSubringToCompletedUnramifiedWittRing_frobenius]

/-- Completed changed-standard scalar endomorphisms are fixed by
coefficientwise Witt-vector Frobenius. -/
theorem padicCompletedChangedStandardScalarEndomorphism_frobenius
    (p : ℕ) [Fact p.Prime]
    (u : (padicLocalField p).valuationSubringˣ)
    (a : (padicLocalField p).valuationSubring) :
    PowerSeries.map WittVector.frobenius
        (padicCompletedChangedStandardScalarEndomorphism p u a) =
      padicCompletedChangedStandardScalarEndomorphism p u a := by
  apply PowerSeries.ext
  intro n
  simp [padicCompletedChangedStandardScalarEndomorphism,
    PowerSeries.coeff_map,
    padicValuationSubringToCompletedUnramifiedWittRing_frobenius]

/-- The completed multiplicative series is fixed by coefficientwise
Witt-vector Frobenius. -/
theorem padicCompletedMultiplicativeSeries_frobenius
    (p : ℕ) [Fact p.Prime] :
    PowerSeries.map WittVector.frobenius
        (padicCompletedMultiplicativeSeries p) =
      padicCompletedMultiplicativeSeries p := by
  apply PowerSeries.ext
  intro n
  simp [padicCompletedMultiplicativeSeries]

/-- The completed changed-standard series is fixed by coefficientwise
Witt-vector Frobenius. -/
theorem padicCompletedChangedStandardSeries_frobenius
    (p : ℕ) [Fact p.Prime]
    (u : (padicLocalField p).valuationSubringˣ) :
    PowerSeries.map WittVector.frobenius
        (padicCompletedChangedStandardSeries p u) =
      padicCompletedChangedStandardSeries p u := by
  apply PowerSeries.ext
  intro n
  simp [padicCompletedChangedStandardSeries,
    PowerSeries.coeff_map,
    padicValuationSubringToCompletedUnramifiedWittRing_frobenius]

theorem
    padicCompletedChangedStandardScalarEndomorphism_hasLinearTerm
    (p : ℕ) [Fact p.Prime]
    (u : (padicLocalField p).valuationSubringˣ)
    (a : (padicLocalField p).valuationSubring) :
    HasLinearTerm
        (padicCompletedChangedStandardScalarEndomorphism p u a)
        (fun _ : Unit =>
          padicValuationSubringToCompletedUnramifiedWittRing p a) :=
  powerSeries_hasLinearTerm_of_constantCoeff_coeff_one
    (padicCompletedChangedStandardScalarEndomorphism p u a)
    (padicValuationSubringToCompletedUnramifiedWittRing p a)
    (padicCompletedChangedStandardScalarEndomorphism_constantCoeff p u a)
    (padicCompletedChangedStandardScalarEndomorphism_coeff_one p u a)

/-- Every completed changed-standard scalar endomorphism admits formal
substitution. -/
theorem padicCompletedChangedStandardScalarEndomorphism_hasSubst
    (p : ℕ) [Fact p.Prime]
    (u : (padicLocalField p).valuationSubringˣ)
    (a : (padicLocalField p).valuationSubring) :
    PowerSeries.HasSubst
      (padicCompletedChangedStandardScalarEndomorphism p u a) :=
  (padicCompletedChangedStandardScalarEndomorphism_hasLinearTerm
    p u a).hasSubst

/-- The changed uniformizer itself acts by the defining completed changed
standard Lubin--Tate series. -/
theorem padicCompletedChangedStandardScalarEndomorphism_uniformizer
    (p : ℕ) [Fact p.Prime]
    (u : (padicLocalField p).valuationSubringˣ) :
    padicCompletedChangedStandardScalarEndomorphism p u
        (standardLubinTateChangedUniformizer
          (padicLocalField p)
          (padicIntEquivValuationSubring p (p : ℤ_[p])) u) =
      padicCompletedChangedStandardSeries p u := by
  rw [padicCompletedChangedStandardScalarEndomorphism,
    padicCompletedChangedStandardSeries,
    SameUniformizer.standardLubinTateEndomorphism_uniformizer]

/-- Multiplication of changed-standard scalars is composition after
completed coefficient extension. -/
theorem padicCompletedChangedStandardScalarEndomorphism_mul
    (p : ℕ) [Fact p.Prime]
    (u : (padicLocalField p).valuationSubringˣ)
    (a b : (padicLocalField p).valuationSubring) :
    padicCompletedChangedStandardScalarEndomorphism p u (a * b) =
      PowerSeries.subst
        (padicCompletedChangedStandardScalarEndomorphism p u b)
        (padicCompletedChangedStandardScalarEndomorphism p u a) := by
  let hπ :=
    standardLubinTateChangedUniformizer_isUniformizer
      (padicMultiplicativeLubinTateSeries_isUniformizer p) u
  have h :=
    congrArg
      (PowerSeries.map
        (padicValuationSubringToCompletedUnramifiedWittRing p))
      (standardLubinTateEndomorphism_mul hπ a b)
  change MvPowerSeries.map _ _ = MvPowerSeries.map _ _ at h
  rw [PowerSeries.map_subst
    (standardLubinTateEndomorphism_hasLinearTerm hπ b).hasSubst] at h
  change
    PowerSeries.map _ _ =
      PowerSeries.subst (PowerSeries.map _ _) (PowerSeries.map _ _) at h
  simpa only [padicCompletedChangedStandardScalarEndomorphism] using h

end LubinTate

end
end

section
-- module Solutions.OAIQ244_DUKE.LubinTate_Padic_MultiplicativeEvaluation_CompletedCoefficientEvaluation
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 400000
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_isCompleteDiscrete _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalClassFieldTheory.finiteGaloisLocalField_integerRing_moduleFinite _root_.LocalClassFieldTheory.localDecompositionResidueFinite _root_.LocalClassFieldTheory.localSeparableValuationHasExtension _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.AdicPrincipalUnits.instAddCommGroup _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.AdicPrincipalUnits.instTopologicalSpace _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.DiscretePrincipalUnitQuotient.instAddCommGroup _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.DiscretePrincipalUnitQuotient.instDiscreteTopology _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.DiscretePrincipalUnitQuotient.instTopologicalSpace _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitInverseLimitCarrierPadicModule _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitInverseLimitCarrierPadicSMul _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitQuotientCarrierPadicModule _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitQuotientCarrier_finite _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.PrincipalUnitProdiscreteLimit.instAddCommGroup _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.PrincipalUnitProdiscreteLimit.instTopologicalSpace _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.adicPrincipalUnitsContinuousAdd _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.adicPrincipalUnitsContinuousSMul _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.adicPrincipalUnitsPadicModule _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.adicPrincipalUnitsT2Space _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.discretePrincipalUnitQuotientFinite _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.discretePrincipalUnitQuotientPadicModule _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitPadicModule _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitPadicSMul _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitProdiscreteLimitContinuousAdd _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitProdiscreteLimitContinuousSMul _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitProdiscreteLimitPadicModule _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitProdiscreteLimitT2Space _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.residueFieldZModAlgebra _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedIntegralAlgebraContextFieldAlgebra _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedIntegralAlgebraContextQPadic _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedIntegralAlgebraContextQPadicTower _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedIntegralAlgebraContextValuationSubringAlgebra _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedIntegralAlgebraContextValuationSubringTower _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedIntegralLatticeContextAlgebra _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedIntegralLatticeContextModuleFinite _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedIntegralLatticeContextModuleFree _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedMaximalIdealPowContextModuleFinite _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedMaximalIdealPowContextModuleFree _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedQPadicContextAlgebra _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedQPadicContextFact _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedQPadicContextFiniteDimensional _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedQPadicContextValuationExtension _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedQPadicContextValuationSubringTower _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedWithZeroValuationContextIntegralAlgebra _root_.LocalFieldTheory.DiscreteValuationField.finite_principalUnits_nthPowerKernel _root_.LocalFieldTheory.DiscreteValuationField.finite_residueRootsOfUnityGroup _root_.LocalFieldTheory.DiscreteValuationField.finite_valuationSubringUnits_nthPowerKernel _root_.LocalFieldTheory.DiscreteValuationField.finite_valuationSubringUnits_nthPowerQuotient _root_.LocalFieldTheory.Padic.padicDVR_residueField_finite _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.Padic.padicUnitFiniteFactor_finite _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.LubinTate.standardLubinTateLevelField_galFinite _root_.LubinTate.standardLubinTateLevelField_isAbelianGalois _root_.LubinTate.standardLubinTateLevelField_isMulCommutative _root_.LubinTate.standardLubinTateUnitParameter_commGroup _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.boundedRealFields_finite _root_.OAI.PrimeDegreePackets.instTopologicalSpaceLocalAlgebra _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RamificationTheory.HilbertRamification.Higher.lowerRamificationGroup.instNormal _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionResidueField.instField _root_.RamificationTheory.HilbertRamification.ValuationSubring.selectedResidueField.instAlgebra _root_.RayClass.approximationCompletionTopologicalSpace _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.LocalClassFieldTheory.localAbsoluteValuationHasExtension _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.LocalClassFieldTheory.comparisonIntegerRingIsIntegralClosure _root_.LocalClassFieldTheory.normalizationIntegerRingIsIntegralClosure _root_.RamificationTheory.HilbertRamification.CompleteDVF.decompositionGroupMulSemiringAction _root_.RamificationTheory.HilbertRamification.CompleteDVF.decompositionGroupResidueFieldMulSemiringAction _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.chosenFinitePlaceCompletionAlgebra _root_.chosenFinitePlaceLocalizedIntegerAlgebra _root_.finiteLocalUnitsOpen _root_.infiniteAdeleRingT2Space _root_.relativeAdeleRingIntermediateAlgebra _root_.relativeAdeleRingTopIntermediateAlgebra
attribute [-simp] _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.GlobalClassFieldTheory.Reciprocity.rationalPrimeUnitValuationSubringUnit_coe _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.EqualCharacteristicLaurent.coeffHom_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.EqualCharacteristicLaurent.powerSeriesEvalHom_C _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.EqualCharacteristicLaurent.powerSeriesEvalHom_X _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.EqualCharacteristicLaurent.powerSeriesEvalSubringHom_C _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.EqualCharacteristicLaurent.powerSeriesEvalSubringHom_X _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.AdicPrincipalUnits.addEquiv_map_smul _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.AdicPrincipalUnits.of_val _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.AdicPrincipalUnits.val_of _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.DiscretePrincipalUnitQuotient.addEquiv_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.DiscretePrincipalUnitQuotient.addEquiv_map_smul _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.DiscretePrincipalUnitQuotient.addEquiv_of _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.DiscretePrincipalUnitQuotient.addEquiv_symm_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.DiscretePrincipalUnitQuotient.of_val _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.DiscretePrincipalUnitQuotient.val_of _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.DiscretePrincipalUnitQuotient.val_transition _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.adicPrincipalUnitsHomeomorphUnderlying_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.iwasawaGlobalInverseLimitCarrier_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitAddEquivInverseLimitCarrier_map_smul _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitAddHomeomorphInverseLimitCarrier_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitInverseLimitCarrierEval_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitInverseLimitCarrierPadic_smul_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitMulEquivInverseLimitCarrier_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitPadic_smul_carrier_coordinate _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitProdiscreteLimitHomeomorphUnderlying_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitQuotientCarrierPadicScalar_eq_smul _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitQuotientCarrierToFull_mk _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitQuotientCarrierTransition_mk _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.uniformizerHigherUnitQuotientEquiv_mk _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.PrincipalUnitProdiscreteLimit.addEquiv_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.PrincipalUnitProdiscreteLimit.addEquiv_map_smul _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.PrincipalUnitProdiscreteLimit.addEquiv_symm_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.PrincipalUnitProdiscreteLimit.coordinate_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.PrincipalUnitProdiscreteLimit.coordinate_smul _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.PrincipalUnitProdiscreteLimit.of_val _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.PrincipalUnitProdiscreteLimit.val_of _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.adicPrincipalUnitsAddEquivProdiscreteLimit_map_smul _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.adicPrincipalUnitsContinuousAddEquivUnderlyingOfWithZeroValuation_map_smul _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.adicPrincipalUnitsHomeomorphProdiscreteLimit_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.adicPrincipalUnitsHomeomorphProdiscreteLimit_to_addEquiv _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.iwasawaDegreeTerm_zero _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.iwasawaGn_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.iwasawaPartialProduct_zero_input _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.iwasawaSeedAtLevel_val _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.iwasawaSeedIdeal_val _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.iwasawaSeed_val _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitPadic_natCast_smul _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitPadic_nsmul_eq_pow _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitPadic_smul_def _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitSuccQuotAddEquivResidue_iwasawaSeed _root_.LocalFieldTheory.DiscreteValuationField.LocalField.higherPrincipalUnitAddToFirst_smul _root_.LocalFieldTheory.DiscreteValuationField.LocalField.laurentSeriesEquivLaurentImageSubfield_apply_coe _root_.LocalFieldTheory.DiscreteValuationField.LocalField.padicIntToValuationSubring_coe _root_.LocalFieldTheory.DiscreteValuationField.LocalField.ratCastToQpadicClosureSubfield_apply _root_.LocalFieldTheory.DiscreteValuationField.LocalField.ratCastWithValToQpadicClosureSubfield_apply _root_.LocalFieldTheory.DiscreteValuationField.MultiplicativeIntegerValuation.fieldUnitDecompositionLogHomWithUniformizerValue_apply _root_.LocalFieldTheory.DiscreteValuationField.MultiplicativeIntegerValuation.fieldUnitDecompositionLogHomWithUniformizerValue_principal _root_.LocalFieldTheory.DiscreteValuationField.MultiplicativeIntegerValuation.fieldUnitDecompositionLogHomWithUniformizerValue_root _root_.LocalFieldTheory.DiscreteValuationField.MultiplicativeIntegerValuation.fieldUnitDecompositionLogHomWithUniformizerValue_uniformizer _root_.LocalFieldTheory.DiscreteValuationField.MultiplicativeIntegerValuation.fieldUnitLogHomWithUniformizerValue_apply _root_.LocalFieldTheory.DiscreteValuationField.MultiplicativeIntegerValuation.principalUnitExpSeriesHomOfMaximalIdealPow_apply _root_.LocalFieldTheory.DiscreteValuationField.MultiplicativeIntegerValuation.principalUnitLogSeriesHomOfWithZeroValuationScaled_apply_toAdd _root_.LocalFieldTheory.Padic.integerRingEquivPadicDVRValuationSubring_coe _root_.LocalFieldTheory.localIntegerValuationSubringEquiv_apply_coe _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.LocalFieldTheory.residueField_algebraMap_residue _root_.LubinTate.SameUniformizer.coeff_recursiveIntertwiner _root_.LubinTate.SameUniformizer.constantCoeff_inVariable _root_.LubinTate.SameUniformizer.intertwinerApproximation_zero _root_.LubinTate.SameUniformizer.standardLubinTateEndomorphism_coeff_one _root_.LubinTate.padicChangedUniformizerIntertwiner_coeff _root_.LubinTate.padicChangedUniformizerIntertwiner_coeff_one _root_.LubinTate.padicCompletedChangedStandardScalarEndomorphism_coeff_one _root_.LubinTate.padicCompletedChangedStandardScalarEndomorphism_one _root_.LubinTate.padicCompletedMultiplicativeScalarEndomorphismValue_one _root_.LubinTate.padicCompletedMultiplicativeScalarEndomorphism_coeff_one _root_.LubinTate.padicCompletedStandardScalarEndomorphismValue_one _root_.LubinTate.padicCompletedStandardScalarEndomorphism_one _root_.LubinTate.padicStandardToMultiplicativeIntertwiner_coeff_one _root_.LubinTate.standardLubinTateBaseUniformizerUnit_coe _root_.LubinTate.standardLubinTateChangedUniformizerUnit_coe _root_.LubinTate.standardLubinTateEndomorphismEvalAt_one _root_.LubinTate.standardLubinTateEndomorphismEvalAt_zero _root_.LubinTate.standardLubinTateEndomorphismValue_one _root_.LubinTate.standardLubinTateEndomorphismValue_zero _root_.LubinTate.standardLubinTateLevelCoefficientHom_apply _root_.LubinTate.standardLubinTateLevelPowerSeriesEval_C _root_.LubinTate.standardLubinTateLevelPowerSeriesEval_X _root_.LubinTate.standardLubinTateLevelPowerSeriesEval_coe _root_.LubinTate.standardLubinTatePrimitiveLevelAction_coe _root_.LubinTate.standardLubinTatePrimitivePointIntegerAction_one _root_.LubinTate.standardLubinTatePrimitivePointIterateInteger_zero _root_.LubinTate.standardLubinTatePrimitivePolynomialOverField_coeff_zero _root_.LubinTate.standardLubinTatePrimitiveRootAction_one _root_.LubinTate.standardLubinTateUnitFactorFieldUnit_coe _root_.LubinTate.standardLubinTateUnitParameterAlgEquiv_apply_gen _root_.LubinTate.standardLubinTateUnitParameterAlgHom_apply_gen _root_.LubinTate.standardLubinTateUnitParameterChosenRepresentative_spec _root_.LubinTate.standardLubinTateUnitParameterEquivGal_apply _root_.LubinTate.standardLubinTateUnitParameterEquivGal_inv_class_apply_gen _root_.LubinTate.standardLubinTateUnitParameterLevelRoot_coe _root_.LubinTate.standardLubinTateUnitParameterLevelRoot_one _root_.LubinTate.standardLubinTateUnitParameterRoot_class _root_.LubinTate.standardLubinTateUnitParameterToGalHom_apply _root_.OAI.PrimeDegreePackets.ThetaConstruction.schwartzCM_apply _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteResidueActionOfHenselianDVF_apply _root_.RamificationTheory.HilbertRamification.CompleteDVF.decompositionResidueAction_algebraMap _root_.RamificationTheory.HilbertRamification.CompleteDVF.decompositionResidueAction_apply _root_.RamificationTheory.HilbertRamification.CompleteDVF.galEquivDecompositionGroup_coe _root_.RamificationTheory.HilbertRamification.CompleteDVF.residueAction_apply _root_.RamificationTheory.HilbertRamification.Higher.dvfUniformizerQuotientUnit_mul_uniformizer _root_.RamificationTheory.HilbertRamification.Higher.dvfUniformizerRepresentativeHom_apply _root_.RamificationTheory.HilbertRamification.Higher.dvfValuationSubringUnitAut_apply _root_.RamificationTheory.HilbertRamification.Higher.intrinsicRamificationNumberOfUniqueExtension_one _root_.RamificationTheory.HilbertRamification.Higher.lowerRamificationGroup_neg_one _root_.RamificationTheory.HilbertRamification.Higher.mem_dvfHigherPrincipalUnitGroup_iff _root_.RamificationTheory.HilbertRamification.Higher.mem_lowerRamificationGroup_iff _root_.RamificationTheory.HilbertRamification.Higher.mem_valuationSubringDisplacementSubalgebraOfUniqueExtension_iff _root_.RamificationTheory.HilbertRamification.Higher.ramificationNumberDepthOfUniqueExtension_depth _root_.RamificationTheory.HilbertRamification.Higher.ramificationNumberOfUniqueExtension_one _root_.RamificationTheory.HilbertRamification.Higher.realRamificationIdeal_nat _root_.RamificationTheory.HilbertRamification.Higher.realRamificationIdeal_neg_one _root_.RamificationTheory.HilbertRamification.Higher.uniformizerGradedHom_mk _root_.RamificationTheory.HilbertRamification.Higher.valuationSubringAutOfUniqueExtension_apply_coe _root_.RamificationTheory.HilbertRamification.Higher.valuationSubringAutOfUniqueExtension_apply_inv_apply _root_.RamificationTheory.HilbertRamification.Higher.valuationSubringAutOfUniqueExtension_mul_apply _root_.RamificationTheory.HilbertRamification.Higher.valuationSubringAutOfUniqueExtension_one_apply _root_.RayClass.primesEquiv_val_eq_natGenerator _root_.LubinTate.standardLubinTateLevelAutomorphismIntegerRingEquiv_apply _root_.LubinTate.padicMultiplicativeLevelAutomorphismIntegerRingEquiv_apply _root_.infinitePlace_mult_smul
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

/-!
# Coefficient maps and analytic evaluation on completed p-adic levels

This module equips completed Lubin--Tate levels with the direct p-adic
coefficient maps used by polynomial and power-series evaluation.  It also
establishes the exact completed primitive-point torsion relations and the
general injectivity criterion for evaluation with unit linear coefficient.
-/

noncomputable section

namespace LubinTate

open LocalFieldTheory.DiscreteValuationField
open LocalFieldTheory.DiscreteValuationField.CompleteDVF
open LocalFieldTheory.DiscreteValuationField.Examples.Qp
open ValuationTheory.DiscreteValuationField
open SameUniformizer

/-- The discrete Witt-vector coefficient uniformity used for completed evaluation. -/
noncomputable local instance (priority := 50)
    padicCompletedMultiplicativeWittUniformSpace_rb59fe0_1
    (p : ℕ) [Fact p.Prime] :
    UniformSpace (padicCompletedUnramifiedWittRing p) :=
  ⊥
attribute [local instance] LubinTate.padicCompletedMultiplicativeTargetWithIdeal
attribute [local instance] LubinTate.padicCompletedMultiplicativeTargetCompleteSpace
attribute [local instance] LubinTate.padicCompletedMultiplicativeTargetT2Space
/-- The completed Lubin--Tate level as an algebra over the original p-adic
base field, through the completed unramified coefficient field. -/
noncomputable instance padicCompletedLevelField_padicAlgebra
    (p : ℕ) [Fact p.Prime] (n : ℕ) :
    Algebra ℚ_[p] (padicCompletedLevelField p n) :=
  ((algebraMap (padicCompletedUnramifiedField p)
      (padicCompletedLevelField p n)).comp
    (algebraMap ℚ_[p] (padicCompletedUnramifiedField p))).toAlgebra

instance padicCompletedLevelField_padicScalarTower
    (p : ℕ) [Fact p.Prime] (n : ℕ) :
    IsScalarTower ℚ_[p] (padicCompletedUnramifiedField p)
      (padicCompletedLevelField p n) :=
  IsScalarTower.of_algebraMap_eq' rfl

/-- Polynomial evaluation through the integral coefficient map agrees,
after coercion, with evaluation through the field coefficient map. -/
theorem padicCompletedLevelPadicIntegerPolynomialEval_coe
    (p : ℕ) [Fact p.Prime] (n : ℕ)
    (x : (padicCompletedLevelCompleteDVF p n).valuationSubring)
    (P : Polynomial (padicLocalField p).valuationSubring) :
    ((Polynomial.eval₂
        (padicCompletedLevelPadicIntegerCoefficientHom p n) x P :
          (padicCompletedLevelCompleteDVF p n).valuationSubring) :
        padicCompletedLevelField p n) =
      Polynomial.eval₂
        (padicCompletedLevelPadicFieldCoefficientHom p n)
        (x : padicCompletedLevelField p n) P := by
  let target := padicCompletedLevelCompleteDVF p n
  let i : target.valuationSubring →+*
      padicCompletedLevelField p n :=
    target.valuation.valuationSubring.subtype
  have hcomp :
      i.comp (padicCompletedLevelPadicIntegerCoefficientHom p n) =
        padicCompletedLevelPadicFieldCoefficientHom p n := by
    ext a
    exact padicCompletedLevelPadicIntegerCoefficientHom_coe p n a
  change
    i (Polynomial.eval₂
        (padicCompletedLevelPadicIntegerCoefficientHom p n) x P) =
      Polynomial.eval₂
        (padicCompletedLevelPadicFieldCoefficientHom p n) (i x) P
  rw [Polynomial.hom_eval₂, hcomp]

theorem padicCompletedPrimitiveRoot_standardPrimitivePolynomial
    (p : ℕ) [Fact p.Prime] (n : ℕ) :
    Polynomial.eval₂
        (padicCompletedLevelPadicFieldCoefficientHom p n)
        (padicCompletedPrimitiveRoot p n)
        (standardLubinTatePrimitivePolynomial
          (padicLocalField p)
          (padicIntEquivValuationSubring p (p : ℤ_[p])) n) =
      0 := by
  have hroot := padicCompletedPrimitiveRoot_isRoot p n
  simpa [Polynomial.IsRoot, padicCompletedPrimitivePolynomial,
    standardLubinTatePrimitivePolynomialOverField,
    padicCompletedLevelPadicFieldCoefficientHom,
    Polynomial.eval_map, Polynomial.eval₂_map] using hroot

/-- The chosen primitive point in the completed level is killed by the
`n + 1`-fold standard p-adic Lubin--Tate iterate. -/
theorem padicCompletedPrimitiveRoot_iterate_succ_eq_zero
    (p : ℕ) [Fact p.Prime] (n : ℕ) :
    Polynomial.eval₂
        (padicCompletedLevelPadicFieldCoefficientHom p n)
        (padicCompletedPrimitiveRoot p n)
        (standardLubinTatePolynomialIterate
          (padicLocalField p)
          (padicIntEquivValuationSubring p (p : ℤ_[p])) (n + 1)) =
      0 := by
  let F := padicLocalField p
  let π : (padicLocalField p).valuationSubring :=
    padicIntEquivValuationSubring p (p : ℤ_[p])
  let φ := padicCompletedLevelPadicFieldCoefficientHom p n
  let x := padicCompletedPrimitiveRoot p n
  have hfactor :=
    congrArg (Polynomial.eval₂ φ x)
      (standardLubinTatePolynomialIterate_succ_factor F π n)
  rw [Polynomial.eval₂_mul,
    padicCompletedPrimitiveRoot_standardPrimitivePolynomial p n,
    mul_zero] at hfactor
  simpa only [F, π, φ, x] using hfactor

/-- The chosen completed primitive point is not killed one level early. -/
theorem padicCompletedPrimitiveRoot_iterate_ne_zero
    (p : ℕ) [Fact p.Prime] (n : ℕ) :
    Polynomial.eval₂
        (padicCompletedLevelPadicFieldCoefficientHom p n)
        (padicCompletedPrimitiveRoot p n)
        (standardLubinTatePolynomialIterate
          (padicLocalField p)
          (padicIntEquivValuationSubring p (p : ℤ_[p])) n) ≠
      0 := by
  let F := padicLocalField p
  let π : (padicLocalField p).valuationSubring :=
    padicIntEquivValuationSubring p (p : ℤ_[p])
  let E := padicCompletedUnramifiedField p
  let L := padicCompletedLevelField p n
  let φK : ℚ_[p] →+* L :=
    (algebraMap E L).comp (algebraMap ℚ_[p] E)
  let φO : F.valuationSubring →+* L :=
    φK.comp (algebraMap F.valuationSubring ℚ_[p])
  let x := padicCompletedPrimitiveRoot p n
  intro hzero
  have hroot := padicCompletedPrimitiveRoot_isRoot p n
  have hrootField :
      Polynomial.eval₂ φK x
          (standardLubinTatePrimitivePolynomialOverField F π n) =
        0 := by
    simpa [Polynomial.IsRoot, padicCompletedPrimitivePolynomial,
      Polynomial.eval_map, Polynomial.eval₂_map, F, π, E, L, φK, x] using
        hroot
  have hequation :
      Polynomial.eval₂ φO x
            (standardLubinTatePolynomialIterate F π n) ^
          (Nat.card F.residueField - 1) +
        φK (π : ℚ_[p]) =
      0 := by
    calc
      _ =
          Polynomial.eval₂ φK x
            (standardLubinTatePrimitivePolynomialOverField F π n) := by
        symm
        exact
          standardLubinTatePrimitivePolynomialOverField_eval₂
            F π φK n x
      _ = 0 := hrootField
  have hzero' :
      Polynomial.eval₂ φO x
          (standardLubinTatePolynomialIterate F π n) =
        0 := by
    simpa only [φO, φK, F, π, E, L, x,
      padicCompletedLevelPadicFieldCoefficientHom] using hzero
  rw [hzero', zero_pow, zero_add] at hequation
  · apply (padicMultiplicativeLubinTateSeries_isUniformizer p).ne_zero
    apply φK.injective
    simpa only [F, π, map_zero] using hequation
  · exact Nat.sub_ne_zero_of_lt
      (Finite.one_lt_card : 1 < Nat.card F.residueField)

/-- Integral form of the exact completed primitive-point torsion
relation at level `n + 1`. -/
theorem padicCompletedPrimitiveRootInteger_iterate_succ_eq_zero
    (p : ℕ) [Fact p.Prime] (n : ℕ) :
    Polynomial.eval₂
        (padicCompletedLevelPadicIntegerCoefficientHom p n)
        (padicCompletedPrimitiveRootInteger p n)
        (standardLubinTatePolynomialIterate
          (padicLocalField p)
          (padicIntEquivValuationSubring p (p : ℤ_[p])) (n + 1)) =
      0 := by
  apply Subtype.ext
  change
    ((Polynomial.eval₂
        (padicCompletedLevelPadicIntegerCoefficientHom p n)
        (padicCompletedPrimitiveRootInteger p n)
        (standardLubinTatePolynomialIterate
          (padicLocalField p)
          (padicIntEquivValuationSubring p (p : ℤ_[p])) (n + 1)) :
      (padicCompletedLevelCompleteDVF p n).valuationSubring) :
        padicCompletedLevelField p n) =
      0
  rw [padicCompletedLevelPadicIntegerPolynomialEval_coe]
  exact padicCompletedPrimitiveRoot_iterate_succ_eq_zero p n

/-- The integral completed primitive point is not killed by the
level-`n` standard iterate. -/
theorem padicCompletedPrimitiveRootInteger_iterate_ne_zero
    (p : ℕ) [Fact p.Prime] (n : ℕ) :
    Polynomial.eval₂
        (padicCompletedLevelPadicIntegerCoefficientHom p n)
        (padicCompletedPrimitiveRootInteger p n)
        (standardLubinTatePolynomialIterate
          (padicLocalField p)
          (padicIntEquivValuationSubring p (p : ℤ_[p])) n) ≠
      0 := by
  intro hzero
  apply padicCompletedPrimitiveRoot_iterate_ne_zero p n
  have hcoe := congrArg
    (fun z : (padicCompletedLevelCompleteDVF p n).valuationSubring =>
      (z : padicCompletedLevelField p n)) hzero
  simpa [map_zero,
    padicCompletedLevelPadicIntegerPolynomialEval_coe,
    padicCompletedPrimitiveRootInteger_coe] using hcoe

/-- Completed-level power-series evaluation is independent of the proof
that its evaluation point is topologically nilpotent. -/
theorem padicCompletedLevelPowerSeriesEval_congr_point
    (p : ℕ) [Fact p.Prime] (n : ℕ)
    {x y : (padicCompletedLevelCompleteDVF p n).valuationSubring}
    (hx : PowerSeries.HasEval x) (hy : PowerSeries.HasEval y)
    (hxy : x = y)
    (f : PowerSeries (padicCompletedUnramifiedWittRing p)) :
    padicCompletedLevelPowerSeriesEval p n x hx f =
      padicCompletedLevelPowerSeriesEval p n y hy f := by
  subst y
  rfl

end LubinTate

end
end

section
-- module Solutions.OAIQ244_DUKE.LubinTate_Padic_MultiplicativeEvaluation_CompletedScalarEndomorphism
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 400000
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_isCompleteDiscrete _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalClassFieldTheory.finiteGaloisLocalField_integerRing_moduleFinite _root_.LocalClassFieldTheory.localDecompositionResidueFintype _root_.LocalClassFieldTheory.localSeparableValuationHasExtension _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.AdicPrincipalUnits.instAddCommGroup _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.AdicPrincipalUnits.instTopologicalSpace _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.DiscretePrincipalUnitQuotient.instAddCommGroup _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.DiscretePrincipalUnitQuotient.instDiscreteTopology _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.DiscretePrincipalUnitQuotient.instTopologicalSpace _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitInverseLimitCarrierPadicModule _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitInverseLimitCarrierPadicSMul _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitQuotientCarrierPadicModule _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitQuotientCarrier_finite _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.PrincipalUnitProdiscreteLimit.instAddCommGroup _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.PrincipalUnitProdiscreteLimit.instTopologicalSpace _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.adicPrincipalUnitsContinuousAdd _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.adicPrincipalUnitsContinuousSMul _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.adicPrincipalUnitsPadicModule _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.adicPrincipalUnitsT2Space _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.discretePrincipalUnitQuotientFinite _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.discretePrincipalUnitQuotientPadicModule _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitPadicModule _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitPadicSMul _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitProdiscreteLimitContinuousAdd _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitProdiscreteLimitContinuousSMul _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitProdiscreteLimitPadicModule _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitProdiscreteLimitT2Space _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.residueFieldZModAlgebra _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedIntegralAlgebraContextFieldAlgebra _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedIntegralAlgebraContextQPadic _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedIntegralAlgebraContextQPadicTower _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedIntegralAlgebraContextValuationSubringAlgebra _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedIntegralAlgebraContextValuationSubringTower _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedIntegralLatticeContextAlgebra _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedIntegralLatticeContextModuleFinite _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedIntegralLatticeContextModuleFree _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedMaximalIdealPowContextModuleFinite _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedMaximalIdealPowContextModuleFree _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedQPadicContextAlgebra _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedQPadicContextFact _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedQPadicContextFiniteDimensional _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedQPadicContextValuationExtension _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedQPadicContextValuationSubringTower _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedWithZeroValuationContextIntegralAlgebra _root_.LocalFieldTheory.DiscreteValuationField.finite_principalUnits_nthPowerKernel _root_.LocalFieldTheory.DiscreteValuationField.finite_residueRootsOfUnityGroup _root_.LocalFieldTheory.DiscreteValuationField.finite_valuationSubringUnits_nthPowerKernel _root_.LocalFieldTheory.DiscreteValuationField.finite_valuationSubringUnits_nthPowerQuotient _root_.LocalFieldTheory.Padic.padicDVR_residueField_finite _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.LubinTate.standardLubinTateLevelField_galFinite _root_.LubinTate.standardLubinTateLevelField_isAbelianGalois _root_.LubinTate.standardLubinTateLevelField_isMulCommutative _root_.LubinTate.standardLubinTateUnitParameter_commGroup _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.instTopologicalSpaceLocalAlgebra _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RamificationTheory.HilbertRamification.Higher.lowerRamificationGroup.instNormal _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionResidueField.instField _root_.RamificationTheory.HilbertRamification.ValuationSubring.selectedResidueField.instAlgebra _root_.RayClass.approximationCompletionTopologicalSpace _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.LocalClassFieldTheory.localAbsoluteValuationHasExtension _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.LocalClassFieldTheory.comparisonIntegerRingIsIntegralClosure _root_.LocalClassFieldTheory.normalizationIntegerRingIsIntegralClosure _root_.RamificationTheory.HilbertRamification.CompleteDVF.decompositionGroupMulSemiringAction _root_.RamificationTheory.HilbertRamification.CompleteDVF.decompositionGroupResidueFieldMulSemiringAction _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.chosenFinitePlaceCompletionAlgebra _root_.finiteLocalUnitsOpen _root_.infiniteAdeleRingT2Space _root_.relativeAdeleRingIntermediateAlgebra _root_.relativeAdeleRingTopIntermediateAlgebra
attribute [-simp] _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.GlobalClassFieldTheory.Reciprocity.rationalPrimeUnitValuationSubringUnit_coe _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.EqualCharacteristicLaurent.coeffHom_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.EqualCharacteristicLaurent.powerSeriesEvalHom_C _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.EqualCharacteristicLaurent.powerSeriesEvalHom_X _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.EqualCharacteristicLaurent.powerSeriesEvalSubringHom_C _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.EqualCharacteristicLaurent.powerSeriesEvalSubringHom_X _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.AdicPrincipalUnits.addEquiv_map_smul _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.AdicPrincipalUnits.val_of _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.DiscretePrincipalUnitQuotient.addEquiv_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.DiscretePrincipalUnitQuotient.addEquiv_map_smul _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.DiscretePrincipalUnitQuotient.addEquiv_of _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.DiscretePrincipalUnitQuotient.addEquiv_symm_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.DiscretePrincipalUnitQuotient.val_transition _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.adicPrincipalUnitsHomeomorphUnderlying_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.iwasawaGlobalInverseLimitCarrier_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitAddEquivInverseLimitCarrier_map_smul _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitAddHomeomorphInverseLimitCarrier_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitInverseLimitCarrierEval_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitInverseLimitCarrierPadic_smul_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitMulEquivInverseLimitCarrier_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitPadic_smul_carrier_coordinate _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitProdiscreteLimitHomeomorphUnderlying_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitQuotientCarrierPadicScalar_eq_smul _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitQuotientCarrierToFull_mk _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitQuotientCarrierTransition_mk _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.uniformizerHigherUnitQuotientEquiv_mk _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.PrincipalUnitProdiscreteLimit.addEquiv_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.PrincipalUnitProdiscreteLimit.addEquiv_map_smul _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.PrincipalUnitProdiscreteLimit.addEquiv_symm_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.PrincipalUnitProdiscreteLimit.coordinate_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.PrincipalUnitProdiscreteLimit.coordinate_smul _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.adicPrincipalUnitsAddEquivProdiscreteLimit_map_smul _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.adicPrincipalUnitsContinuousAddEquivUnderlyingOfWithZeroValuation_map_smul _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.adicPrincipalUnitsHomeomorphProdiscreteLimit_to_addEquiv _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.iwasawaDegreeTerm_zero _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.iwasawaGn_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.iwasawaPartialProduct_zero_input _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.iwasawaSeedAtLevel_val _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.iwasawaSeedIdeal_val _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.iwasawaSeed_val _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitPadic_natCast_smul _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitPadic_nsmul_eq_pow _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitPadic_smul_def _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitSuccQuotAddEquivResidue_iwasawaSeed _root_.LocalFieldTheory.DiscreteValuationField.LocalField.higherPrincipalUnitAddToFirst_smul _root_.LocalFieldTheory.DiscreteValuationField.LocalField.laurentSeriesEquivLaurentImageSubfield_apply_coe _root_.LocalFieldTheory.DiscreteValuationField.LocalField.padicIntToValuationSubring_coe _root_.LocalFieldTheory.DiscreteValuationField.LocalField.ratCastToQpadicClosureSubfield_apply _root_.LocalFieldTheory.DiscreteValuationField.LocalField.ratCastWithValToQpadicClosureSubfield_apply _root_.LocalFieldTheory.DiscreteValuationField.MultiplicativeIntegerValuation.fieldUnitDecompositionLogHomWithUniformizerValue_apply _root_.LocalFieldTheory.DiscreteValuationField.MultiplicativeIntegerValuation.fieldUnitDecompositionLogHomWithUniformizerValue_principal _root_.LocalFieldTheory.DiscreteValuationField.MultiplicativeIntegerValuation.fieldUnitDecompositionLogHomWithUniformizerValue_root _root_.LocalFieldTheory.DiscreteValuationField.MultiplicativeIntegerValuation.fieldUnitDecompositionLogHomWithUniformizerValue_uniformizer _root_.LocalFieldTheory.DiscreteValuationField.MultiplicativeIntegerValuation.fieldUnitLogHomWithUniformizerValue_apply _root_.LocalFieldTheory.DiscreteValuationField.MultiplicativeIntegerValuation.principalUnitExpSeriesHomOfMaximalIdealPow_apply _root_.LocalFieldTheory.DiscreteValuationField.MultiplicativeIntegerValuation.principalUnitLogSeriesHomOfWithZeroValuationScaled_apply_toAdd _root_.LocalFieldTheory.Padic.integerRingEquivPadicDVRValuationSubring_coe _root_.LocalFieldTheory.localIntegerValuationSubringEquiv_apply_coe _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.LocalFieldTheory.residueField_algebraMap_residue _root_.LubinTate.standardLubinTatePrimitivePointIterateInteger_zero _root_.LubinTate.standardLubinTateUnitParameterAlgEquiv_apply_gen _root_.LubinTate.standardLubinTateUnitParameterAlgHom_apply_gen _root_.LubinTate.standardLubinTateUnitParameterChosenRepresentative_spec _root_.LubinTate.standardLubinTateUnitParameterEquivGal_apply _root_.LubinTate.standardLubinTateUnitParameterEquivGal_inv_class_apply_gen _root_.LubinTate.standardLubinTateUnitParameterLevelRoot_coe _root_.LubinTate.standardLubinTateUnitParameterLevelRoot_one _root_.LubinTate.standardLubinTateUnitParameterRoot_class _root_.LubinTate.standardLubinTateUnitParameterToGalHom_apply _root_.OAI.PrimeDegreePackets.ThetaConstruction.schwartzCM_apply _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteResidueActionOfHenselianDVF_apply _root_.RamificationTheory.HilbertRamification.CompleteDVF.decompositionResidueAction_algebraMap _root_.RamificationTheory.HilbertRamification.CompleteDVF.decompositionResidueAction_apply _root_.RamificationTheory.HilbertRamification.CompleteDVF.residueAction_apply _root_.RamificationTheory.HilbertRamification.Higher.dvfUniformizerQuotientUnit_mul_uniformizer _root_.RamificationTheory.HilbertRamification.Higher.dvfUniformizerRepresentativeHom_apply _root_.RamificationTheory.HilbertRamification.Higher.dvfValuationSubringUnitAut_apply _root_.RamificationTheory.HilbertRamification.Higher.intrinsicRamificationNumberOfUniqueExtension_one _root_.RamificationTheory.HilbertRamification.Higher.lowerRamificationGroup_neg_one _root_.RamificationTheory.HilbertRamification.Higher.mem_dvfHigherPrincipalUnitGroup_iff _root_.RamificationTheory.HilbertRamification.Higher.mem_lowerRamificationGroup_iff _root_.RamificationTheory.HilbertRamification.Higher.mem_valuationSubringDisplacementSubalgebraOfUniqueExtension_iff _root_.RamificationTheory.HilbertRamification.Higher.ramificationNumberDepthOfUniqueExtension_depth _root_.RamificationTheory.HilbertRamification.Higher.ramificationNumberOfUniqueExtension_one _root_.RamificationTheory.HilbertRamification.Higher.realRamificationIdeal_nat _root_.RamificationTheory.HilbertRamification.Higher.realRamificationIdeal_neg_one _root_.RamificationTheory.HilbertRamification.Higher.uniformizerGradedHom_mk _root_.RamificationTheory.HilbertRamification.Higher.valuationSubringAutOfUniqueExtension_apply_coe _root_.RamificationTheory.HilbertRamification.Higher.valuationSubringAutOfUniqueExtension_apply_inv_apply _root_.RamificationTheory.HilbertRamification.Higher.valuationSubringAutOfUniqueExtension_mul_apply _root_.RamificationTheory.HilbertRamification.Higher.valuationSubringAutOfUniqueExtension_one_apply _root_.RayClass.primesEquiv_val_eq_natGenerator _root_.LubinTate.standardLubinTateLevelAutomorphismIntegerRingEquiv_apply _root_.LubinTate.padicMultiplicativeLevelAutomorphismIntegerRingEquiv_apply _root_.infinitePlace_mult_smul
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

/-!
# Completed standard and multiplicative scalar endomorphisms

This module extends the standard-to-multiplicative comparison and scalar
endomorphisms to the completed unramified Witt ring.  It proves the genuine
composition, torsion, and injectivity identities for their analytic actions.
-/

noncomputable section

namespace LubinTate

open LocalFieldTheory.DiscreteValuationField
open LocalFieldTheory.DiscreteValuationField.CompleteDVF
open LocalFieldTheory.DiscreteValuationField.Examples.Qp
open ValuationTheory.DiscreteValuationField
open SameUniformizer

attribute [local instance]
  padicCompletedMultiplicativeTargetWithIdeal
  padicCompletedMultiplicativeTargetCompleteSpace
  padicCompletedMultiplicativeTargetT2Space

/-- Witt Frobenius fixes the completed standard-to-multiplicative
intertwiner because all of its coefficients descend from the p-adic
valuation ring. -/
theorem padicCompletedStandardToMultiplicativeIntertwiner_frobenius
    (p : ℕ) [Fact p.Prime] :
    PowerSeries.map WittVector.frobenius
        (padicCompletedStandardToMultiplicativeIntertwiner p) =
      padicCompletedStandardToMultiplicativeIntertwiner p := by
  apply PowerSeries.ext
  intro m
  simp [padicCompletedStandardToMultiplicativeIntertwiner,
    PowerSeries.coeff_map,
    padicValuationSubringToCompletedUnramifiedWittRing_frobenius]

/-- Evaluation of the completed standard-to-multiplicative comparison is
injective on topologically nilpotent completed-level integers. -/
theorem padicCompletedStandardToMultiplicativeIntertwiner_eval_injective
    (p : ℕ) [Fact p.Prime] (n : ℕ)
    {x y : (padicCompletedLevelCompleteDVF p n).valuationSubring}
    (hx : PowerSeries.HasEval x) (hy : PowerSeries.HasEval y)
    (hxy :
      padicCompletedLevelPowerSeriesEval p n x hx
          (padicCompletedStandardToMultiplicativeIntertwiner p) =
        padicCompletedLevelPowerSeriesEval p n y hy
          (padicCompletedStandardToMultiplicativeIntertwiner p)) :
    x = y := by
  apply
    padicCompletedLevelPowerSeriesEval_injective_of_unitLinearCoefficient
      p n (padicCompletedStandardToMultiplicativeIntertwiner p)
      (padicCompletedStandardToMultiplicativeIntertwiner_constantCoeff p)
      ?_ hx hy hxy
  rw [padicCompletedStandardToMultiplicativeIntertwiner,
    PowerSeries.coeff_map,
    padicStandardToMultiplicativeIntertwiner_coeff_one,
    map_one]
  exact isUnit_one

/-- Completed standard scalar endomorphisms have zero constant
coefficient. -/
theorem padicCompletedStandardScalarEndomorphism_constantCoeff
    (p : ℕ) [Fact p.Prime]
    (a : (padicLocalField p).valuationSubring) :
    PowerSeries.constantCoeff
        (padicCompletedStandardScalarEndomorphism p a) =
      0 := by
  have hconstant :=
    (standardLubinTateEndomorphism_hasLinearTerm
      (padicMultiplicativeLubinTateSeries_isUniformizer p) a
      ).constantCoeff_eq_zero
  change
    padicValuationSubringToCompletedUnramifiedWittRing p
        (PowerSeries.constantCoeff
          (standardLubinTateEndomorphism
            (padicMultiplicativeLubinTateSeries_isUniformizer p) a)) =
      0
  rw [PowerSeries.constantCoeff_eq, hconstant, map_zero]

/-- Completed standard scalar endomorphisms support formal substitution. -/
theorem padicCompletedStandardScalarEndomorphism_hasSubst
    (p : ℕ) [Fact p.Prime]
    (a : (padicLocalField p).valuationSubring) :
    PowerSeries.HasSubst
      (padicCompletedStandardScalarEndomorphism p a) :=
  PowerSeries.HasSubst.of_constantCoeff_zero'
    (padicCompletedStandardScalarEndomorphism_constantCoeff p a)

/-- Multiplication of standard p-adic scalars is composition after
completed coefficient extension. -/
theorem padicCompletedStandardScalarEndomorphism_mul
    (p : ℕ) [Fact p.Prime]
    (a b : (padicLocalField p).valuationSubring) :
    padicCompletedStandardScalarEndomorphism p (a * b) =
      PowerSeries.subst
        (padicCompletedStandardScalarEndomorphism p b)
        (padicCompletedStandardScalarEndomorphism p a) := by
  let f :=
    padicValuationSubringToCompletedUnramifiedWittRing p
  let hπ := padicMultiplicativeLubinTateSeries_isUniformizer p
  let A := standardLubinTateEndomorphism hπ a
  let B := standardLubinTateEndomorphism hπ b
  calc
    padicCompletedStandardScalarEndomorphism p (a * b) =
        PowerSeries.map f (PowerSeries.subst B A) := by
      exact congrArg (PowerSeries.map f)
        (standardLubinTateEndomorphism_mul hπ a b)
    _ =
        PowerSeries.subst (PowerSeries.map f B)
          (PowerSeries.map f A) := by
      change
        MvPowerSeries.map f (PowerSeries.subst B A) =
          PowerSeries.subst (PowerSeries.map f B)
            (PowerSeries.map f A)
      exact
        PowerSeries.map_subst
          (standardLubinTateEndomorphism_hasLinearTerm hπ b
            ).hasSubst A
    _ =
        PowerSeries.subst
          (padicCompletedStandardScalarEndomorphism p b)
          (padicCompletedStandardScalarEndomorphism p a) := by
      rfl

/-- The completed standard-to-multiplicative comparison intertwines the
actual completed scalar endomorphisms. -/
theorem
    padicCompletedStandardToMultiplicativeIntertwiner_endomorphism
    (p : ℕ) [Fact p.Prime]
    (a : (padicLocalField p).valuationSubring) :
    PowerSeries.subst
        (padicCompletedStandardScalarEndomorphism p a)
        (padicCompletedStandardToMultiplicativeIntertwiner p) =
      PowerSeries.subst
        (padicCompletedStandardToMultiplicativeIntertwiner p)
        (padicCompletedMultiplicativeScalarEndomorphism p a) := by
  let f :=
    padicValuationSubringToCompletedUnramifiedWittRing p
  let hπ := padicMultiplicativeLubinTateSeries_isUniformizer p
  let S := standardLubinTateEndomorphism hπ a
  let H := padicStandardToMultiplicativeIntertwiner p
  let M :=
    recursiveIntertwiner hπ
      (padicMultiplicativeLubinTateSeries p)
      (padicMultiplicativeLubinTateSeries p)
      (fun _ : Unit => a)
  calc
    PowerSeries.subst
        (padicCompletedStandardScalarEndomorphism p a)
        (padicCompletedStandardToMultiplicativeIntertwiner p) =
        PowerSeries.map f (PowerSeries.subst S H) := by
      change
        PowerSeries.subst (PowerSeries.map f S)
            (PowerSeries.map f H) =
          PowerSeries.map f (PowerSeries.subst S H)
      symm
      change
        MvPowerSeries.map f (PowerSeries.subst S H) =
          PowerSeries.subst (PowerSeries.map f S)
            (PowerSeries.map f H)
      exact
        PowerSeries.map_subst
          (standardLubinTateEndomorphism_hasLinearTerm hπ a
            ).hasSubst H
    _ = PowerSeries.map f (PowerSeries.subst H M) := by
      rw [padicStandardToMultiplicativeIntertwiner_endomorphism]
    _ =
        PowerSeries.subst
          (padicCompletedStandardToMultiplicativeIntertwiner p)
          (padicCompletedMultiplicativeScalarEndomorphism p a) := by
      change
        MvPowerSeries.map f (PowerSeries.subst H M) =
          PowerSeries.subst (PowerSeries.map f H)
            (PowerSeries.map f M)
      exact
        PowerSeries.map_subst
          (padicStandardToMultiplicativeIntertwiner_hasSubst p) M

/-- A completed standard scalar value remains a convergent evaluation
point. -/
theorem padicCompletedStandardScalarEndomorphismValue_hasEval
    (p : ℕ) [Fact p.Prime] (n : ℕ)
    (x : (padicCompletedLevelCompleteDVF p n).valuationSubring)
    (hx : PowerSeries.HasEval x)
    (a : (padicLocalField p).valuationSubring) :
    PowerSeries.HasEval
      (padicCompletedStandardScalarEndomorphismValue p n x hx a) :=
  padicCompletedLevelPowerSeriesEval_hasEval p n x hx
    (padicCompletedStandardScalarEndomorphism p a)
    (padicCompletedStandardScalarEndomorphism_hasSubst p a)

/-- Multiplication of standard scalars is composition of their completed
analytic actions. -/
theorem padicCompletedStandardScalarEndomorphismValue_mul
    (p : ℕ) [Fact p.Prime] (n : ℕ)
    (x : (padicCompletedLevelCompleteDVF p n).valuationSubring)
    (hx : PowerSeries.HasEval x)
    (a b : (padicLocalField p).valuationSubring) :
    padicCompletedStandardScalarEndomorphismValue p n x hx (a * b) =
      padicCompletedStandardScalarEndomorphismValue p n
        (padicCompletedStandardScalarEndomorphismValue p n x hx b)
        (padicCompletedStandardScalarEndomorphismValue_hasEval
          p n x hx b) a := by
  rw [padicCompletedStandardScalarEndomorphismValue,
    padicCompletedStandardScalarEndomorphism_mul]
  exact
    padicCompletedLevelPowerSeriesEval_subst p n x hx
      (padicCompletedStandardScalarEndomorphism p b)
      (padicCompletedStandardScalarEndomorphism p a)
      (padicCompletedStandardScalarEndomorphism_hasSubst p b)
      (padicCompletedStandardScalarEndomorphismValue_hasEval
        p n x hx b)

/-- The standard uniformizer acts by the defining standard Lubin--Tate
series after completed coefficient extension. -/
theorem padicCompletedStandardScalarEndomorphism_uniformizer
    (p : ℕ) [Fact p.Prime] :
    padicCompletedStandardScalarEndomorphism p
        (padicIntEquivValuationSubring p (p : ℤ_[p])) =
      PowerSeries.map
        (padicValuationSubringToCompletedUnramifiedWittRing p)
        (standardLubinTateSeries
          (padicMultiplicativeLubinTateSeries_isUniformizer p)
          ).toPowerSeries := by
  exact congrArg
    (PowerSeries.map (padicValuationSubringToCompletedUnramifiedWittRing p))
    (SameUniformizer.standardLubinTateEndomorphism_uniformizer
      (padicMultiplicativeLubinTateSeries_isUniformizer p))

/-- Every completed standard scalar endomorphism fixes the zero point. -/
theorem padicCompletedStandardScalarEndomorphismValue_zero
    (p : ℕ) [Fact p.Prime] (n : ℕ)
    (a : (padicLocalField p).valuationSubring) :
    padicCompletedStandardScalarEndomorphismValue p n
        0 PowerSeries.HasEval.zero a =
      0 := by
  obtain ⟨B, hB⟩ :
      (PowerSeries.X :
          PowerSeries (padicCompletedUnramifiedWittRing p)) ∣
        padicCompletedStandardScalarEndomorphism p a := by
    rw [PowerSeries.X_dvd_iff]
    exact padicCompletedStandardScalarEndomorphism_constantCoeff p a
  rw [padicCompletedStandardScalarEndomorphismValue,
    hB, map_mul, padicCompletedLevelPowerSeriesEval_X, zero_mul]

/-- Evaluating a coefficient-extended polynomial as a completed power
series agrees with integral polynomial evaluation. -/
theorem padicCompletedLevelPowerSeriesEval_map_polynomial
    (p : ℕ) [Fact p.Prime] (n : ℕ)
    (x : (padicCompletedLevelCompleteDVF p n).valuationSubring)
    (hx : PowerSeries.HasEval x)
    (P : Polynomial (padicLocalField p).valuationSubring) :
    padicCompletedLevelPowerSeriesEval p n x hx
        (PowerSeries.map
          (padicValuationSubringToCompletedUnramifiedWittRing p)
          (P : PowerSeries (padicLocalField p).valuationSubring)) =
      Polynomial.eval₂
        (padicCompletedLevelPadicIntegerCoefficientHom p n) x P := by
  rw [← Polynomial.polynomial_map_coe,
    padicCompletedLevelPowerSeriesEval_coe,
    Polynomial.eval₂_map]
  rfl

/-- Evaluating the scalar `π ^ r` on any completed-level nilpotent point
is evaluation of the `r`-fold standard division-polynomial iterate. -/
theorem padicCompletedStandardScalarEndomorphismValue_uniformizer_pow
    (p : ℕ) [Fact p.Prime] (n : ℕ)
    (x : (padicCompletedLevelCompleteDVF p n).valuationSubring)
    (hx : PowerSeries.HasEval x) (r : ℕ) :
    padicCompletedStandardScalarEndomorphismValue p n x hx
        ((padicIntEquivValuationSubring p (p : ℤ_[p])) ^ r) =
      Polynomial.eval₂
        (padicCompletedLevelPadicIntegerCoefficientHom p n) x
        (standardLubinTatePolynomialIterate
          (padicLocalField p)
          (padicIntEquivValuationSubring p (p : ℤ_[p])) r) := by
  let hπ := padicMultiplicativeLubinTateSeries_isUniformizer p
  let π : (padicLocalField p).valuationSubring :=
    padicIntEquivValuationSubring p (p : ℤ_[p])
  change
    padicCompletedStandardScalarEndomorphismValue p n x hx (π ^ r) =
      Polynomial.eval₂
        (padicCompletedLevelPadicIntegerCoefficientHom p n) x
        (standardLubinTatePolynomialIterate
          (padicLocalField p) π r)
  induction r with
  | zero =>
      rw [pow_zero,
        padicCompletedStandardScalarEndomorphismValue_one,
        standardLubinTatePolynomialIterate_zero,
        Polynomial.eval₂_X]
  | succ r ih =>
      rw [pow_succ',
        padicCompletedStandardScalarEndomorphismValue_mul]
      rw [padicCompletedStandardScalarEndomorphismValue,
        padicCompletedStandardScalarEndomorphism_uniformizer,
        ← standardLubinTatePolynomial_toPowerSeries_eq_series hπ,
        padicCompletedLevelPowerSeriesEval_map_polynomial,
        ih,
        standardLubinTatePolynomialIterate_succ,
        Polynomial.eval₂_comp]

/-- Every completed multiplicative scalar endomorphism fixes the zero
point. -/
theorem padicCompletedMultiplicativeScalarEndomorphismValue_zero
    (p : ℕ) [Fact p.Prime] (n : ℕ)
    (a : (padicLocalField p).valuationSubring) :
    padicCompletedMultiplicativeScalarEndomorphismValue p n
        0 PowerSeries.HasEval.zero a =
      0 := by
  obtain ⟨B, hB⟩ :
      (PowerSeries.X :
          PowerSeries (padicCompletedUnramifiedWittRing p)) ∣
        padicCompletedMultiplicativeScalarEndomorphism p a := by
    rw [PowerSeries.X_dvd_iff]
    exact
      padicCompletedMultiplicativeScalarEndomorphism_constantCoeff p a
  rw [padicCompletedMultiplicativeScalarEndomorphismValue,
    hB, map_mul, padicCompletedLevelPowerSeriesEval_X, zero_mul]

/-- Acting first by the inverse of a p-adic unit and then by the unit
itself recovers every topologically nilpotent completed-level integer. -/
theorem
    padicCompletedMultiplicativeScalarEndomorphismValue_unit_after_inverse
    (p : ℕ) [Fact p.Prime] (n : ℕ)
    (x : (padicCompletedLevelCompleteDVF p n).valuationSubring)
    (hx : PowerSeries.HasEval x)
    (u : (padicLocalField p).valuationSubringˣ) :
    padicCompletedMultiplicativeScalarEndomorphismValue p n
        (padicCompletedMultiplicativeScalarEndomorphismValue p n x hx
          ((u⁻¹ : (padicLocalField p).valuationSubringˣ) :
            (padicLocalField p).valuationSubring))
        (padicCompletedMultiplicativeScalarEndomorphismValue_hasEval
          p n x hx
          ((u⁻¹ : (padicLocalField p).valuationSubringˣ) :
            (padicLocalField p).valuationSubring))
        (u : (padicLocalField p).valuationSubring) =
      x := by
  calc
    _ =
        padicCompletedMultiplicativeScalarEndomorphismValue p n x hx
          ((u : (padicLocalField p).valuationSubring) *
            ((u⁻¹ : (padicLocalField p).valuationSubringˣ) :
              (padicLocalField p).valuationSubring)) :=
      (padicCompletedMultiplicativeScalarEndomorphismValue_mul
        p n x hx
          (u : (padicLocalField p).valuationSubring)
          ((u⁻¹ : (padicLocalField p).valuationSubringˣ) :
            (padicLocalField p).valuationSubring)).symm
    _ = x := by
      rw [show
        (u : (padicLocalField p).valuationSubring) *
            ((u⁻¹ : (padicLocalField p).valuationSubringˣ) :
              (padicLocalField p).valuationSubring) = 1 by
          simp,
        padicCompletedMultiplicativeScalarEndomorphismValue_one]

/-- Completed analytic evaluation of the standard-to-multiplicative
comparison carries every standard scalar action to the actual
multiplicative scalar action. -/
theorem
    padicCompletedStandardToMultiplicativeIntertwiner_eval_endomorphism
    (p : ℕ) [Fact p.Prime] (n : ℕ)
    (x : (padicCompletedLevelCompleteDVF p n).valuationSubring)
    (hx : PowerSeries.HasEval x)
    (a : (padicLocalField p).valuationSubring) :
    padicCompletedLevelPowerSeriesEval p n
        (padicCompletedStandardScalarEndomorphismValue p n x hx a)
        (padicCompletedStandardScalarEndomorphismValue_hasEval
          p n x hx a)
        (padicCompletedStandardToMultiplicativeIntertwiner p) =
      padicCompletedMultiplicativeScalarEndomorphismValue p n
        (padicCompletedLevelPowerSeriesEval p n x hx
          (padicCompletedStandardToMultiplicativeIntertwiner p))
        (padicCompletedLevelPowerSeriesEval_hasEval p n x hx
          (padicCompletedStandardToMultiplicativeIntertwiner p)
          (padicCompletedStandardToMultiplicativeIntertwiner_hasSubst p))
        a := by
  let S := padicCompletedStandardScalarEndomorphism p a
  let H := padicCompletedStandardToMultiplicativeIntertwiner p
  let M := padicCompletedMultiplicativeScalarEndomorphism p a
  let xS := padicCompletedStandardScalarEndomorphismValue p n x hx a
  let xH := padicCompletedLevelPowerSeriesEval p n x hx H
  let hxS : PowerSeries.HasEval xS :=
    padicCompletedStandardScalarEndomorphismValue_hasEval p n x hx a
  let hxH : PowerSeries.HasEval xH :=
    padicCompletedLevelPowerSeriesEval_hasEval p n x hx H
      (padicCompletedStandardToMultiplicativeIntertwiner_hasSubst p)
  calc
    padicCompletedLevelPowerSeriesEval p n xS hxS H =
        padicCompletedLevelPowerSeriesEval p n x hx
          (PowerSeries.subst S H) := by
      exact
        (padicCompletedLevelPowerSeriesEval_subst p n x hx
          S H (padicCompletedStandardScalarEndomorphism_hasSubst p a)
          hxS).symm
    _ =
        padicCompletedLevelPowerSeriesEval p n x hx
          (PowerSeries.subst H M) := by
      rw [
        padicCompletedStandardToMultiplicativeIntertwiner_endomorphism]
    _ =
        padicCompletedLevelPowerSeriesEval p n xH hxH M := by
      exact
        padicCompletedLevelPowerSeriesEval_subst p n x hx
          H M
          (padicCompletedStandardToMultiplicativeIntertwiner_hasSubst p)
          hxH

/-- A p-adic unit scalar acts injectively through the completed standard
Lubin--Tate endomorphism on all topologically nilpotent completed-level
integers. -/
theorem
    padicCompletedStandardScalarEndomorphismValue_unit_injective
    (p : ℕ) [Fact p.Prime] (n : ℕ)
    (u : (padicLocalField p).valuationSubringˣ)
    {x y : (padicCompletedLevelCompleteDVF p n).valuationSubring}
    (hx : PowerSeries.HasEval x) (hy : PowerSeries.HasEval y)
    (hxy :
      padicCompletedStandardScalarEndomorphismValue p n x hx
          (u : (padicLocalField p).valuationSubring) =
        padicCompletedStandardScalarEndomorphismValue p n y hy
          (u : (padicLocalField p).valuationSubring)) :
    x = y := by
  let H := padicCompletedStandardToMultiplicativeIntertwiner p
  let xH := padicCompletedLevelPowerSeriesEval p n x hx H
  let yH := padicCompletedLevelPowerSeriesEval p n y hy H
  let hxH : PowerSeries.HasEval xH :=
    padicCompletedLevelPowerSeriesEval_hasEval p n x hx H
      (padicCompletedStandardToMultiplicativeIntertwiner_hasSubst p)
  let hyH : PowerSeries.HasEval yH :=
    padicCompletedLevelPowerSeriesEval_hasEval p n y hy H
      (padicCompletedStandardToMultiplicativeIntertwiner_hasSubst p)
  have hmult :
      padicCompletedMultiplicativeScalarEndomorphismValue p n xH hxH
          (u : (padicLocalField p).valuationSubring) =
        padicCompletedMultiplicativeScalarEndomorphismValue p n yH hyH
          (u : (padicLocalField p).valuationSubring) := by
    calc
      _ =
          padicCompletedLevelPowerSeriesEval p n
            (padicCompletedStandardScalarEndomorphismValue
              p n x hx (u : (padicLocalField p).valuationSubring))
            (padicCompletedStandardScalarEndomorphismValue_hasEval
              p n x hx (u : (padicLocalField p).valuationSubring))
            H := by
        symm
        exact
          padicCompletedStandardToMultiplicativeIntertwiner_eval_endomorphism
            p n x hx (u : (padicLocalField p).valuationSubring)
      _ =
          padicCompletedLevelPowerSeriesEval p n
            (padicCompletedStandardScalarEndomorphismValue
              p n y hy (u : (padicLocalField p).valuationSubring))
            (padicCompletedStandardScalarEndomorphismValue_hasEval
              p n y hy (u : (padicLocalField p).valuationSubring))
            H := by
        exact
          padicCompletedLevelPowerSeriesEval_congr_point p n
            (padicCompletedStandardScalarEndomorphismValue_hasEval
              p n x hx (u : (padicLocalField p).valuationSubring))
            (padicCompletedStandardScalarEndomorphismValue_hasEval
              p n y hy (u : (padicLocalField p).valuationSubring))
            hxy H
      _ =
          padicCompletedMultiplicativeScalarEndomorphismValue p n yH hyH
            (u : (padicLocalField p).valuationSubring) :=
        padicCompletedStandardToMultiplicativeIntertwiner_eval_endomorphism
          p n y hy (u : (padicLocalField p).valuationSubring)
  have hH : xH = yH := by
    exact
      padicCompletedMultiplicativeScalarEndomorphismValue_unit_injective
        p n u hxH hyH hmult
  exact
    padicCompletedStandardToMultiplicativeIntertwiner_eval_injective
      p n hx hy hH

/-- The completed standard-to-multiplicative comparison evaluates to zero
at the zero point. -/
theorem padicCompletedStandardToMultiplicativeIntertwiner_eval_zero
    (p : ℕ) [Fact p.Prime] (n : ℕ) :
    padicCompletedLevelPowerSeriesEval p n
        0 PowerSeries.HasEval.zero
        (padicCompletedStandardToMultiplicativeIntertwiner p) =
      0 := by
  obtain ⟨B, hB⟩ :
      (PowerSeries.X :
          PowerSeries (padicCompletedUnramifiedWittRing p)) ∣
        padicCompletedStandardToMultiplicativeIntertwiner p := by
    rw [PowerSeries.X_dvd_iff]
    exact
      padicCompletedStandardToMultiplicativeIntertwiner_constantCoeff p
  rw [hB, map_mul,
    padicCompletedLevelPowerSeriesEval_X, zero_mul]

end LubinTate

end
end

section
-- module Solutions.OAIQ244_DUKE.LubinTate_Padic_MultiplicativeEvaluation_CompletedPrimitivePoint
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 400000
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalClassFieldTheory.finiteGaloisLocalField_integerRing_moduleFinite _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitInverseLimitCarrierPadicModule _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitInverseLimitCarrierPadicSMul _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitQuotientCarrierPadicModule _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitQuotientCarrier_finite _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.adicPrincipalUnitsContinuousAdd _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.adicPrincipalUnitsContinuousSMul _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.adicPrincipalUnitsPadicModule _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.discretePrincipalUnitQuotientFinite _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.discretePrincipalUnitQuotientPadicModule _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitPadicModule _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitPadicSMul _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitProdiscreteLimitContinuousAdd _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitProdiscreteLimitContinuousSMul _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitProdiscreteLimitPadicModule _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.residueFieldZModAlgebra _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedIntegralAlgebraContextFieldAlgebra _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedIntegralAlgebraContextQPadic _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedIntegralAlgebraContextQPadicTower _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedIntegralAlgebraContextValuationSubringAlgebra _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedIntegralAlgebraContextValuationSubringTower _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedIntegralLatticeContextAlgebra _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedIntegralLatticeContextModuleFinite _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedIntegralLatticeContextModuleFree _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedMaximalIdealPowContextModuleFinite _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedMaximalIdealPowContextModuleFree _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedQPadicContextAlgebra _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedQPadicContextFact _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedQPadicContextFiniteDimensional _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedQPadicContextValuationExtension _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedQPadicContextValuationSubringTower _root_.LocalFieldTheory.DiscreteValuationField.finite_principalUnits_nthPowerKernel _root_.LocalFieldTheory.DiscreteValuationField.finite_residueRootsOfUnityGroup _root_.LocalFieldTheory.DiscreteValuationField.finite_valuationSubringUnits_nthPowerKernel _root_.LocalFieldTheory.DiscreteValuationField.finite_valuationSubringUnits_nthPowerQuotient _root_.LocalFieldTheory.Padic.padicDVR_residueField_finite _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.LubinTate.standardLubinTateLevelField_galFinite _root_.LubinTate.standardLubinTateLevelField_isAbelianGalois _root_.LubinTate.standardLubinTateLevelField_isMulCommutative _root_.LubinTate.standardLubinTateUnitParameter_commGroup _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.instTopologicalSpaceLocalAlgebra _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RamificationTheory.HilbertRamification.Higher.lowerRamificationGroup.instNormal _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionResidueField.instField _root_.RayClass.approximationCompletionTopologicalSpace _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.LocalClassFieldTheory.comparisonIntegerRingIsIntegralClosure _root_.LocalClassFieldTheory.normalizationIntegerRingIsIntegralClosure _root_.RamificationTheory.HilbertRamification.CompleteDVF.decompositionGroupMulSemiringAction _root_.RamificationTheory.HilbertRamification.CompleteDVF.decompositionGroupResidueFieldMulSemiringAction _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen _root_.infiniteAdeleRingT2Space
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

/-!
# The completed multiplicative primitive point

This module evaluates the completed multiplicative comparison at the chosen
completed standard primitive point.  It proves the exact standard and
changed-uniformizer torsion bounds and constructs the actual unit action on
that point.
-/

noncomputable section

namespace LubinTate

open LocalFieldTheory.DiscreteValuationField
open LocalFieldTheory.DiscreteValuationField.CompleteDVF
open LocalFieldTheory.DiscreteValuationField.Examples.Qp
open ValuationTheory.DiscreteValuationField
open SameUniformizer

attribute [local instance]
  padicCompletedMultiplicativeTargetWithIdeal
  padicCompletedMultiplicativeTargetCompleteSpace
  padicCompletedMultiplicativeTargetT2Space

/-- The actual completed multiplicative primitive point is killed by the
scalar endomorphism for `π ^ (n + 1)`. -/
theorem
    padicCompletedMultiplicativePrimitivePoint_uniformizer_pow_succ_eq_zero
    (p : ℕ) [Fact p.Prime] (n : ℕ) :
    padicCompletedMultiplicativeScalarEndomorphismValue p n
        (padicCompletedMultiplicativePrimitivePoint p n)
        (padicCompletedMultiplicativePrimitivePoint_hasEval p n)
        ((padicIntEquivValuationSubring p (p : ℤ_[p])) ^ (n + 1)) =
      0 := by
  let π : (padicLocalField p).valuationSubring :=
    padicIntEquivValuationSubring p (p : ℤ_[p])
  change
    padicCompletedMultiplicativeScalarEndomorphismValue p n
        (padicCompletedMultiplicativePrimitivePoint p n)
        (padicCompletedMultiplicativePrimitivePoint_hasEval p n)
        (π ^ (n + 1)) =
      0
  have hbridge :=
    padicCompletedStandardToMultiplicativeIntertwiner_eval_endomorphism
      p n
      (padicCompletedPrimitiveRootInteger p n)
      (padicCompletedPrimitiveRootInteger_hasEval p n)
      (π ^ (n + 1))
  have hstandardPoint :
      padicCompletedStandardScalarEndomorphismValue p n
          (padicCompletedPrimitiveRootInteger p n)
          (padicCompletedPrimitiveRootInteger_hasEval p n)
          (π ^ (n + 1)) =
        0 := by
    have hUniformizer :=
      padicCompletedStandardScalarEndomorphismValue_uniformizer_pow
        p n
        (padicCompletedPrimitiveRootInteger p n)
        (padicCompletedPrimitiveRootInteger_hasEval p n)
        (n + 1)
    change
      padicCompletedStandardScalarEndomorphismValue p n
          (padicCompletedPrimitiveRootInteger p n)
          (padicCompletedPrimitiveRootInteger_hasEval p n)
          (π ^ (n + 1)) =
        Polynomial.eval₂
          (padicCompletedLevelPadicIntegerCoefficientHom p n)
          (padicCompletedPrimitiveRootInteger p n)
          (standardLubinTatePolynomialIterate
            (padicLocalField p) π (n + 1)) at hUniformizer
    rw [hUniformizer]
    exact padicCompletedPrimitiveRootInteger_iterate_succ_eq_zero p n
  have hleftZero :
      padicCompletedLevelPowerSeriesEval p n
          (padicCompletedStandardScalarEndomorphismValue p n
            (padicCompletedPrimitiveRootInteger p n)
            (padicCompletedPrimitiveRootInteger_hasEval p n)
            (π ^ (n + 1)))
          (padicCompletedStandardScalarEndomorphismValue_hasEval p n
            (padicCompletedPrimitiveRootInteger p n)
            (padicCompletedPrimitiveRootInteger_hasEval p n)
            (π ^ (n + 1)))
          (padicCompletedStandardToMultiplicativeIntertwiner p) =
        0 := by
    calc
      _ =
          padicCompletedLevelPowerSeriesEval p n
            0 PowerSeries.HasEval.zero
            (padicCompletedStandardToMultiplicativeIntertwiner p) :=
        padicCompletedLevelPowerSeriesEval_congr_point p n
          (padicCompletedStandardScalarEndomorphismValue_hasEval p n
            (padicCompletedPrimitiveRootInteger p n)
            (padicCompletedPrimitiveRootInteger_hasEval p n)
            (π ^ (n + 1)))
          PowerSeries.HasEval.zero hstandardPoint
          (padicCompletedStandardToMultiplicativeIntertwiner p)
      _ = 0 :=
        padicCompletedStandardToMultiplicativeIntertwiner_eval_zero p n
  exact hbridge.symm.trans hleftZero

/-- The actual completed multiplicative primitive point is not killed by
the scalar endomorphism for `π ^ n`. -/
theorem
    padicCompletedMultiplicativePrimitivePoint_uniformizer_pow_ne_zero
    (p : ℕ) [Fact p.Prime] (n : ℕ) :
    padicCompletedMultiplicativeScalarEndomorphismValue p n
        (padicCompletedMultiplicativePrimitivePoint p n)
        (padicCompletedMultiplicativePrimitivePoint_hasEval p n)
        ((padicIntEquivValuationSubring p (p : ℤ_[p])) ^ n) ≠
      0 := by
  let π : (padicLocalField p).valuationSubring :=
    padicIntEquivValuationSubring p (p : ℤ_[p])
  change
    padicCompletedMultiplicativeScalarEndomorphismValue p n
        (padicCompletedMultiplicativePrimitivePoint p n)
        (padicCompletedMultiplicativePrimitivePoint_hasEval p n)
        (π ^ n) ≠
      0
  intro hzero
  let lambda := padicCompletedPrimitiveRootInteger p n
  let hlambda := padicCompletedPrimitiveRootInteger_hasEval p n
  let lambdaN :=
    padicCompletedStandardScalarEndomorphismValue
      p n lambda hlambda (π ^ n)
  let hlambdaN : PowerSeries.HasEval lambdaN :=
    padicCompletedStandardScalarEndomorphismValue_hasEval
      p n lambda hlambda (π ^ n)
  have hbridge :=
    padicCompletedStandardToMultiplicativeIntertwiner_eval_endomorphism
      p n lambda hlambda (π ^ n)
  have hleftZero :
      padicCompletedLevelPowerSeriesEval p n lambdaN hlambdaN
          (padicCompletedStandardToMultiplicativeIntertwiner p) =
        0 := by
    exact hbridge.trans hzero
  have hlambdaNZero : lambdaN = 0 := by
    apply
      padicCompletedStandardToMultiplicativeIntertwiner_eval_injective
        p n hlambdaN PowerSeries.HasEval.zero
    exact hleftZero.trans
      (padicCompletedStandardToMultiplicativeIntertwiner_eval_zero
        p n).symm
  apply padicCompletedPrimitiveRootInteger_iterate_ne_zero p n
  rw [←
    padicCompletedStandardScalarEndomorphismValue_uniformizer_pow
      p n lambda hlambda n]
  exact hlambdaNZero

/-- The completed multiplicative primitive point is killed by the
`n + 1`-st power of the scalar `u p` defining the changed uniformizer. -/
theorem
    padicCompletedMultiplicativePrimitivePoint_changedUniformizer_pow_succ_eq_zero
    (p : ℕ) [Fact p.Prime]
    (u : (padicLocalField p).valuationSubringˣ) (n : ℕ) :
    padicCompletedMultiplicativeScalarEndomorphismValue p n
        (padicCompletedMultiplicativePrimitivePoint p n)
        (padicCompletedMultiplicativePrimitivePoint_hasEval p n)
        ((standardLubinTateChangedUniformizer
          (padicLocalField p)
          (padicIntEquivValuationSubring p (p : ℤ_[p])) u) ^ (n + 1)) =
      0 := by
  let π : (padicLocalField p).valuationSubring :=
    padicIntEquivValuationSubring p (p : ℤ_[p])
  let x := padicCompletedMultiplicativePrimitivePoint p n
  let hx := padicCompletedMultiplicativePrimitivePoint_hasEval p n
  let xπ :=
    padicCompletedMultiplicativeScalarEndomorphismValue
      p n x hx (π ^ (n + 1))
  let hxπ : PowerSeries.HasEval xπ :=
    padicCompletedMultiplicativeScalarEndomorphismValue_hasEval
      p n x hx (π ^ (n + 1))
  have hxπZero : xπ = 0 := by
    change
      padicCompletedMultiplicativeScalarEndomorphismValue p n
          (padicCompletedMultiplicativePrimitivePoint p n)
          (padicCompletedMultiplicativePrimitivePoint_hasEval p n)
          ((padicIntEquivValuationSubring p (p : ℤ_[p])) ^
            (n + 1)) =
        0
    exact
      padicCompletedMultiplicativePrimitivePoint_uniformizer_pow_succ_eq_zero
        p n
  change
    padicCompletedMultiplicativeScalarEndomorphismValue p n
        x hx
        ((standardLubinTateChangedUniformizer
          (padicLocalField p) π u) ^ (n + 1)) =
      0
  calc
    _ =
        padicCompletedMultiplicativeScalarEndomorphismValue p n
          xπ hxπ
          ((u : (padicLocalField p).valuationSubring) ^ (n + 1)) := by
      rw [standardLubinTateChangedUniformizer_eq_unit_mul, mul_pow]
      simpa only [xπ, hxπ] using
        (padicCompletedMultiplicativeScalarEndomorphismValue_mul
          p n x hx
          ((u : (padicLocalField p).valuationSubring) ^ (n + 1))
          (π ^ (n + 1)))
    _ =
        padicCompletedMultiplicativeScalarEndomorphismValue p n
          0 PowerSeries.HasEval.zero
          ((u : (padicLocalField p).valuationSubring) ^ (n + 1)) := by
      exact
        padicCompletedLevelPowerSeriesEval_congr_point p n
          hxπ PowerSeries.HasEval.zero hxπZero
          (padicCompletedMultiplicativeScalarEndomorphism p
            ((u : (padicLocalField p).valuationSubring) ^ (n + 1)))
    _ = 0 :=
      padicCompletedMultiplicativeScalarEndomorphismValue_zero p n _

/-- The completed multiplicative primitive point is not killed one level
early by the scalar `u p`. -/
theorem
    padicCompletedMultiplicativePrimitivePoint_changedUniformizer_pow_ne_zero
    (p : ℕ) [Fact p.Prime]
    (u : (padicLocalField p).valuationSubringˣ) (n : ℕ) :
    padicCompletedMultiplicativeScalarEndomorphismValue p n
        (padicCompletedMultiplicativePrimitivePoint p n)
        (padicCompletedMultiplicativePrimitivePoint_hasEval p n)
        ((standardLubinTateChangedUniformizer
          (padicLocalField p)
          (padicIntEquivValuationSubring p (p : ℤ_[p])) u) ^ n) ≠
      0 := by
  let π : (padicLocalField p).valuationSubring :=
    padicIntEquivValuationSubring p (p : ℤ_[p])
  intro hzero
  let x := padicCompletedMultiplicativePrimitivePoint p n
  let hx := padicCompletedMultiplicativePrimitivePoint_hasEval p n
  let xπ :=
    padicCompletedMultiplicativeScalarEndomorphismValue
      p n x hx (π ^ n)
  let hxπ : PowerSeries.HasEval xπ :=
    padicCompletedMultiplicativeScalarEndomorphismValue_hasEval
      p n x hx (π ^ n)
  change
    padicCompletedMultiplicativeScalarEndomorphismValue p n x hx
        ((standardLubinTateChangedUniformizer
          (padicLocalField p) π u) ^ n) =
      0 at hzero
  have hdecomp :
      padicCompletedMultiplicativeScalarEndomorphismValue p n
          x hx
          ((standardLubinTateChangedUniformizer
            (padicLocalField p) π u) ^ n) =
        padicCompletedMultiplicativeScalarEndomorphismValue p n
          xπ hxπ
          ((u : (padicLocalField p).valuationSubring) ^ n) := by
    rw [standardLubinTateChangedUniformizer_eq_unit_mul, mul_pow]
    simpa only [xπ, hxπ] using
      (padicCompletedMultiplicativeScalarEndomorphismValue_mul
        p n x hx
        ((u : (padicLocalField p).valuationSubring) ^ n)
        (π ^ n))
  have hunitZero :
      padicCompletedMultiplicativeScalarEndomorphismValue p n
          xπ hxπ
          ((u : (padicLocalField p).valuationSubring) ^ n) =
        0 :=
    hdecomp.symm.trans hzero
  have hunitZero' :
      padicCompletedMultiplicativeScalarEndomorphismValue p n
          xπ hxπ
          (((u ^ n : (padicLocalField p).valuationSubringˣ) :
            (padicLocalField p).valuationSubring)) =
        0 := by
    simpa only [Units.val_pow_eq_pow_val] using hunitZero
  have hxπZero : xπ = 0 := by
    apply
      padicCompletedMultiplicativeScalarEndomorphismValue_unit_injective
        p n (u ^ n) hxπ PowerSeries.HasEval.zero
    exact hunitZero'.trans
      (padicCompletedMultiplicativeScalarEndomorphismValue_zero p n
        ((u ^ n : (padicLocalField p).valuationSubringˣ) :
          (padicLocalField p).valuationSubring)).symm
  apply
    padicCompletedMultiplicativePrimitivePoint_uniformizer_pow_ne_zero
      p n
  change xπ = 0
  exact hxπZero

/-- The multiplicative scalar endomorphism attached to a `p`-adic unit,
with coefficients extended to the completed unramified Witt ring. -/
noncomputable def padicCompletedMultiplicativeUnitEndomorphism
    (p : ℕ) [Fact p.Prime]
    (u : (padicLocalField p).valuationSubringˣ) :
    PowerSeries (padicCompletedUnramifiedWittRing p) :=
  padicCompletedMultiplicativeScalarEndomorphism p
    (u : (padicLocalField p).valuationSubring)

/-- The completed multiplicative unit endomorphism admits formal
substitution. -/
theorem padicCompletedMultiplicativeUnitEndomorphism_hasSubst
    (p : ℕ) [Fact p.Prime]
    (u : (padicLocalField p).valuationSubringˣ) :
    PowerSeries.HasSubst
      (padicCompletedMultiplicativeUnitEndomorphism p u) :=
  by
    simpa only [padicCompletedMultiplicativeUnitEndomorphism] using
      padicCompletedMultiplicativeScalarEndomorphism_hasSubst p
        (u : (padicLocalField p).valuationSubring)

/-- The action of a completed multiplicative unit endomorphism on the
completed multiplicative primitive point. -/
noncomputable def padicCompletedMultiplicativePrimitivePointUnitAction
    (p : ℕ) [Fact p.Prime]
    (u : (padicLocalField p).valuationSubringˣ) (n : ℕ) :
    (padicCompletedLevelCompleteDVF p n).valuationSubring :=
  padicCompletedLevelPowerSeriesEval p n
    (padicCompletedMultiplicativePrimitivePoint p n)
    (padicCompletedMultiplicativePrimitivePoint_hasEval p n)
    (padicCompletedMultiplicativeUnitEndomorphism p u)

/-- The unit translate of the completed multiplicative primitive point is
again a convergent evaluation point. -/
theorem padicCompletedMultiplicativePrimitivePointUnitAction_hasEval
    (p : ℕ) [Fact p.Prime]
    (u : (padicLocalField p).valuationSubringˣ) (n : ℕ) :
    PowerSeries.HasEval
      (padicCompletedMultiplicativePrimitivePointUnitAction p u n) := by
  exact
    padicCompletedLevelPowerSeriesEval_hasEval p n
      (padicCompletedMultiplicativePrimitivePoint p n)
      (padicCompletedMultiplicativePrimitivePoint_hasEval p n)
      (padicCompletedMultiplicativeUnitEndomorphism p u)
      (padicCompletedMultiplicativeUnitEndomorphism_hasSubst p u)

end LubinTate

end
end

section
-- module Solutions.OAIQ244_DUKE.LubinTate_Padic_CompletedUnramifiedFrobeniusFixed
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 400000
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalClassFieldTheory.finiteGaloisLocalField_integerRing_moduleFinite _root_.LocalClassFieldTheory.localSelectedResidueIsAlgClosed _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.residueFieldZModAlgebra _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedIntegralAlgebraContextFieldAlgebra _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedIntegralAlgebraContextValuationSubringAlgebra _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.LubinTate.padicCompletedLevelCompleteDVF_hasExtensionInstance _root_.LubinTate.padicCompletedLevelField_algebra _root_.LubinTate.padicCompletedLevelField_finiteDimensional _root_.LubinTate.padicCompletedLevelField_isGalois _root_.LubinTate.padicCompletedLevelField_padicScalarTower _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.diagonalLogAction _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionResidueField.instField _root_.RamificationTheory.HilbertRamification.ValuationSubring.selectedResidueField.instAlgebra _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.RelativeIdeleGroup.relativeIdeleMulAction _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.LocalClassFieldTheory.comparisonIntegerRingIsIntegralClosure _root_.LocalClassFieldTheory.normalizationIntegerRingIsIntegralClosure _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.chosenFinitePlaceCompletionAlgebra _root_.finiteLocalUnitsOpen _root_.infiniteAdeleRingT2Space _root_.relativeAdeleRingIntermediateAlgebra _root_.relativeAdeleRingTopIntermediateAlgebra
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

/-!
# Fixed points of p-adic completed-unramified Frobenius

Witt Frobenius on `W(AlgebraicClosure (ZMod p))` has exactly the canonical
copy of `ℤ_[p]` as its fixed ring.  Passing to fraction fields shows that
the arithmetic Frobenius on the completed maximal-unramified coefficient
field has exactly the canonical copy of `ℚ_[p]` as its fixed field.

The fraction-field argument is integral: after writing a denominator as a
power of `p` times a unit, multiplication by that power of `p` puts a fixed
fraction back in the Witt ring.
-/

noncomputable section

namespace LubinTate

open LocalFieldTheory.DiscreteValuationField
open LocalFieldTheory.DiscreteValuationField.Examples.Qp

/-- The fixed ring of Witt Frobenius on the completed-unramified Witt
ring is the canonical image of the p-adic integers. -/
theorem padicCompletedUnramifiedWittRing_frobenius_fixed_iff
    (p : ℕ) [Fact p.Prime]
    (x : padicCompletedUnramifiedWittRing p) :
    WittVector.frobenius x = x ↔
      ∃ z : ℤ_[p],
        padicIntToCompletedUnramifiedWittRing p z = x := by
  constructor
  · intro hx
    have hcoeffPow (n : ℕ) :
        (x.coeff n) ^ p = x.coeff n := by
      rw [← WittVector.coeff_frobenius_charP]
      exact congrArg (fun y : padicCompletedUnramifiedWittRing p ↦ y.coeff n) hx
    have hcoeffInt (n : ℕ) :
        ∃ a : ℤ, (a : AlgebraicClosure (ZMod p)) = x.coeff n := by
      apply
        (mem_bot_iff_intCast p (AlgebraicClosure (ZMod p))).1
      exact
        (Subfield.mem_bot_iff_pow_eq_self
          (AlgebraicClosure (ZMod p)) p).2
          (hcoeffPow n)
    let c : ℕ → ℤ := fun n ↦ Classical.choose (hcoeffInt n)
    let y : WittVector p (ZMod p) :=
      WittVector.mk p (fun n ↦ (c n : ZMod p))
    refine ⟨WittVector.equiv p y, ?_⟩
    apply WittVector.ext
    intro n
    change
      (WittVector.map
          (algebraMap (ZMod p) (AlgebraicClosure (ZMod p)))
          ((WittVector.equiv p).symm (WittVector.equiv p y))).coeff n =
        x.coeff n
    rw [WittVector.map_coeff, RingEquiv.symm_apply_apply]
    change
      algebraMap (ZMod p) (AlgebraicClosure (ZMod p))
          (c n : ZMod p) = x.coeff n
    calc
      _ = (c n : AlgebraicClosure (ZMod p)) := by
        simp only [map_intCast]
      _ = x.coeff n := by
        simpa only [c] using
          (Classical.choose_spec (hcoeffInt n))
  · rintro ⟨z, rfl⟩
    exact padicIntToCompletedUnramifiedWittRing_frobenius p z

/-- The fixed field of completed-unramified arithmetic Frobenius is the
canonical image of `ℚ_[p]`. -/
theorem padicCompletedUnramifiedFrobenius_fixed_iff
    (p : ℕ) [Fact p.Prime]
    (x : padicCompletedUnramifiedField p) :
    padicCompletedUnramifiedFrobenius p x = x ↔
      ∃ q : ℚ_[p],
        algebraMap ℚ_[p] (padicCompletedUnramifiedField p) q = x := by
  let W := padicCompletedUnramifiedWittRing p
  let E := padicCompletedUnramifiedField p
  let φ := padicCompletedUnramifiedFrobenius p
  constructor
  · intro hx
    obtain ⟨a, b, hb, hab⟩ :=
      IsFractionRing.div_surjective (A := W) x
    have hb0 : b ≠ 0 := nonZeroDivisors.ne_zero hb
    obtain ⟨m, u, hbu⟩ :=
      WittVector.exists_eq_pow_p_mul' b hb0
    let c : W := a * (u⁻¹ : Wˣ)
    have hpW : (p : W) ≠ 0 := by
      exact
        WittVector.p_nonzero p
          (AlgebraicClosure (ZMod p))
    have hpE :
        algebraMap W E ((p : W) ^ m) ≠ 0 := by
      simpa only [map_zero] using
        (IsFractionRing.injective W E).ne
          (pow_ne_zero m hpW)
    have huE :
        algebraMap W E (u : W) ≠ 0 := by
      simpa only [map_zero] using
        (IsFractionRing.injective W E).ne u.ne_zero
    have hbE :
        algebraMap W E b ≠ 0 := by
      simpa only [map_zero] using
        (IsFractionRing.injective W E).ne hb0
    have hclear :
        algebraMap W E c =
          algebraMap W E ((p : W) ^ m) * x := by
      rw [show
        algebraMap W E c =
            algebraMap W E a *
              (algebraMap W E (u : W))⁻¹ by
          simp only [c, map_mul, map_units_inv]]
      rw [← div_eq_mul_inv]
      apply (div_eq_iff huE).2
      have habMul :
          algebraMap W E a =
            x * algebraMap W E b :=
        (div_eq_iff hbE).1 hab
      rw [hbu, map_mul] at habMul
      calc
        algebraMap W E a =
            x *
              (algebraMap W E ((p : W) ^ m) *
                algebraMap W E (u : W)) :=
          habMul
        _ =
            (algebraMap W E ((p : W) ^ m) * x) *
              algebraMap W E (u : W) := by
          ac_rfl
    have hpBase :
        algebraMap W E (p : W) =
          algebraMap ℚ_[p] E (p : ℚ_[p]) := by
      calc
        algebraMap W E (p : W) =
            algebraMap W E
              (padicIntToCompletedUnramifiedWittRing p
                (p : ℤ_[p])) := by
          exact congrArg (algebraMap W E)
            (map_natCast
              (padicIntToCompletedUnramifiedWittRing p) p).symm
        _ =
            algebraMap ℚ_[p] E
              (algebraMap ℤ_[p] ℚ_[p] (p : ℤ_[p])) :=
          (padicCompletedUnramifiedField_algebraMap_padicInt
            p (p : ℤ_[p])).symm
        _ = algebraMap ℚ_[p] E (p : ℚ_[p]) := by
          exact congrArg (algebraMap ℚ_[p] E)
            (map_natCast (algebraMap ℤ_[p] ℚ_[p]) p)
    have hpowBridge :
        algebraMap W E ((p : W) ^ m) =
          (p : E) ^ m := by
      calc
        algebraMap W E ((p : W) ^ m) =
            (algebraMap W E (p : W)) ^ m :=
          map_pow (algebraMap W E) (p : W) m
        _ = (algebraMap ℚ_[p] E (p : ℚ_[p])) ^ m := by
          rw [hpBase]
        _ = (p : E) ^ m := by
          rw [map_natCast]
    have hpowFixed :
        φ (algebraMap W E ((p : W) ^ m)) =
          algebraMap W E ((p : W) ^ m) := by
      have hbase :
          algebraMap W E ((p : W) ^ m) =
            algebraMap ℚ_[p] E ((p : ℚ_[p]) ^ m) := by
        calc
          algebraMap W E ((p : W) ^ m) =
              (p : E) ^ m :=
            hpowBridge
          _ =
              algebraMap ℚ_[p] E ((p : ℚ_[p]) ^ m) := by
            rw [map_pow, map_natCast]
      rw [hbase]
      exact φ.commutes ((p : ℚ_[p]) ^ m)
    have hcFieldFixed :
        φ (algebraMap W E c) = algebraMap W E c := by
      rw [hclear, map_mul, hpowFixed, hx]
    have hcFixed : WittVector.frobenius c = c := by
      apply IsFractionRing.injective W E
      rw [← padicCompletedUnramifiedFrobenius_algebraMap_witt]
      exact hcFieldFixed
    obtain ⟨z, hz⟩ :=
      (padicCompletedUnramifiedWittRing_frobenius_fixed_iff
        p c).1 hcFixed
    refine
      ⟨algebraMap ℤ_[p] ℚ_[p] z / (p : ℚ_[p]) ^ m, ?_⟩
    rw [map_div₀ (algebraMap ℚ_[p] E),
      padicCompletedUnramifiedField_algebraMap_padicInt]
    simp only [map_pow, map_natCast]
    have hpE' : (p : E) ^ m ≠ 0 := by
      rw [← hpowBridge]
      exact hpE
    have hclear' :
        algebraMap W E c =
          (p : E) ^ m * x := by
      rw [← hpowBridge]
      exact hclear
    rw [hz]
    exact (div_eq_iff hpE').2 (by
      simpa only [mul_comm] using hclear')
  · rintro ⟨q, rfl⟩
    exact (padicCompletedUnramifiedFrobenius p).commutes q

end LubinTate

end
end

section
-- module Solutions.OAIQ244_DUKE.GlobalClassFieldTheory_Reciprocity_RationalCyclotomicFinitePlaceArtin
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.infinitePlaceComplexificationOverfield_algebra _root_.GlobalClassFieldTheory.Reciprocity.infinitePlaceComplexificationOverfield_baseAlgebra _root_.GlobalClassFieldTheory.Reciprocity.infinitePlaceComplexificationOverfield_baseSmul _root_.GlobalClassFieldTheory.Reciprocity.infinitePlaceComplexificationOverfield_smul _root_.GlobalClassFieldTheory.Reciprocity.rationalIntermediateFieldAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.KummerTheory.rationalCyclotomicField_hasEnoughRootsOfUnity _root_.KummerTheory.rationalCyclotomicTorsionFixedField_isAbelianGalois _root_.KummerTheory.rationalCyclotomicTorsionFixedField_isGalois _root_.KummerTheory.rationalCyclotomicTorsionFixedField_isIntegral _root_.KummerTheory.rationalCyclotomicTorsionFixedField_normal _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.residueFieldZModAlgebra _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.labelPrime_fact _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable
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

attribute [local instance] GlobalClassFieldTheory.Reciprocity.instFactPrimeValNat_solutions_2
attribute [local instance] GlobalClassFieldTheory.Reciprocity.instNeZeroNatVal_solutions
attribute [local instance] GlobalClassFieldTheory.Reciprocity.rationalCyclotomicLevelFiniteDimensional
attribute [local instance] GlobalClassFieldTheory.Reciprocity.rationalCyclotomicLevelIsAbelianGalois
attribute [local instance] GlobalClassFieldTheory.Reciprocity.rationalFinitePlaceBaseLocallyCompactSpace
attribute [local instance] GlobalClassFieldTheory.Reciprocity.rationalFinitePlaceBaseIsUltrametricDist
attribute [local instance] GlobalClassFieldTheory.Reciprocity.rationalFinitePlaceBaseValuationIsNontrivial
attribute [local instance] GlobalClassFieldTheory.Reciprocity.rationalFinitePlaceBaseValuationCompatible
attribute [local instance] GlobalClassFieldTheory.Reciprocity.rationalFinitePlaceBaseValuativeRelIsNontrivial
attribute [local instance] GlobalClassFieldTheory.Reciprocity.rationalFinitePlaceCompletionRatAlgebra
attribute [local instance] GlobalClassFieldTheory.Reciprocity.rationalFinitePlaceBaseNontriviallyNormedField
attribute [local instance] GlobalClassFieldTheory.Reciprocity.rationalFinitePlaceBaseValued
attribute [local instance] GlobalClassFieldTheory.Reciprocity.rationalFinitePlaceBaseValuativeRel
noncomputable local instance rationalFinitePlaceBaseIsValuativeTopology_rb59fe0_1
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
noncomputable local instance
    rationalCyclotomicArtinLocalizedGlobalAlgebra
    (m : ℕ+) (q : Nat.Primes) :
    Algebra ℚ (rationalCyclotomicArtinLocalizedField m q) :=
  LocalClassFieldTheory.localizedCompletionGlobalAlgebra
    (rationalCyclotomicArtinBaseAbv q)
    (rationalCyclotomicArtinExtension m q)

noncomputable local instance
    rationalCyclotomicArtinLocalizedGlobalSMul
    (m : ℕ+) (q : Nat.Primes) :
    SMul ℚ (rationalCyclotomicArtinLocalizedField m q) :=
  (rationalCyclotomicArtinLocalizedGlobalAlgebra m q).toSMul

noncomputable local instance
    rationalCyclotomicArtinLocalizedScalarTower
    (m : ℕ+) (q : Nat.Primes) :
    IsScalarTower ℚ
      (rationalCyclotomicArtinBaseAbv q).Completion
      (rationalCyclotomicArtinLocalizedField m q) := by
  constructor
  intro r x y
  simp only [Algebra.smul_def, map_mul, eq_ratCast,
    map_ratCast, mul_assoc]
  try (first | exact (Rat.smul_def r _).symm | (rw [Algebra.smul_def, eq_ratCast]) | simp [Algebra.smul_def])

section RationalCyclotomicPrincipalPrime

/-! ## Ramified prime-power transport

This section reuses the canonical finite-place Artin tower above.  In
particular, it introduces no parallel completion/localization instance tower. -/

attribute [local instance] GlobalClassFieldTheory.Reciprocity.instFactPrimeValNat_solutions_2
attribute [local instance] GlobalClassFieldTheory.Reciprocity.instNeZeroNatVal_solutions
attribute [local instance] GlobalClassFieldTheory.Reciprocity.rationalCyclotomicLevelFiniteDimensional
attribute [local instance] GlobalClassFieldTheory.Reciprocity.rationalCyclotomicLevelIsAbelianGalois
attribute [local instance] GlobalClassFieldTheory.Reciprocity.rationalFinitePlaceBaseLocallyCompactSpace
attribute [local instance] GlobalClassFieldTheory.Reciprocity.rationalFinitePlaceBaseIsUltrametricDist
attribute [local instance] GlobalClassFieldTheory.Reciprocity.rationalFinitePlaceBaseValuationIsNontrivial
attribute [local instance] GlobalClassFieldTheory.Reciprocity.rationalFinitePlaceBaseValuationCompatible
attribute [local instance] GlobalClassFieldTheory.Reciprocity.rationalFinitePlaceBaseValuativeRelIsNontrivial
attribute [local instance] GlobalClassFieldTheory.Reciprocity.rationalFinitePlaceCompletionRatAlgebra
attribute [local instance] GlobalClassFieldTheory.Reciprocity.rationalFinitePlaceBaseNontriviallyNormedField
attribute [local instance] GlobalClassFieldTheory.Reciprocity.rationalFinitePlaceBaseValued
attribute [local instance] GlobalClassFieldTheory.Reciprocity.rationalFinitePlaceBaseValuativeRel
noncomputable local instance rationalFinitePlaceBaseIsValuativeTopology_rb59fe0_2
    (q : Nat.Primes) :
    IsValuativeTopology
      (HeightOneSpectrum.adicAbv ℚ
        (RayClass.rationalPrime q)).Completion :=
  isValuativeTopology_of_valued_ofValuation
    (HeightOneSpectrum.adicAbv ℚ
      (RayClass.rationalPrime q)).Completion ℝ≥0
attribute [local instance] GlobalClassFieldTheory.Reciprocity.rationalFinitePlaceBaseIsNonarchimedeanLocalField
attribute [local instance] GlobalClassFieldTheory.Reciprocity.rationalCyclotomicArtinCompletionAlgebra
noncomputable local instance
    rationalCyclotomicArtinLocalizedFiniteDimensional_rb59fe0_1
    (m : ℕ+) (q : Nat.Primes) :
    FiniteDimensional
      (rationalCyclotomicArtinBaseAbv q).Completion
      (rationalCyclotomicArtinLocalizedField m q) :=
  finitePlaceLocalArtinFiniteDimensional
    (K := ℚ) (L := rationalCyclotomicArtinLevel m)
    (rationalCyclotomicArtinPlace q)
    (rationalCyclotomicArtinExtension m q)
attribute [local instance] GlobalClassFieldTheory.Reciprocity.rationalCyclotomicArtinLocalizedAlgebra
noncomputable local instance
    rationalCyclotomicArtinLocalizedIsAbelianGalois_rb59fe0_1
    (m : ℕ+) (q : Nat.Primes) :
    IsAbelianGalois
      (rationalCyclotomicArtinBaseAbv q).Completion
      (rationalCyclotomicArtinLocalizedField m q) :=
  finitePlaceLocalArtinIsAbelianGalois
    (K := ℚ) (L := rationalCyclotomicArtinLevel m)
    (rationalCyclotomicArtinPlace q)
    (rationalCyclotomicArtinExtension m q)
    (inferInstance :
      FiniteDimensional ℚ (rationalCyclotomicArtinLevel m))
noncomputable local instance
    rationalCyclotomicArtinLocalizedIsCyclotomic_rb59fe0_1
    (m : ℕ+) (q : Nat.Primes) :
    IsCyclotomicExtension {(m : ℕ)}
      (rationalCyclotomicArtinBaseAbv q).Completion
      (rationalCyclotomicArtinLocalizedField m q) :=
  rationalCyclotomicLevel_localizedCompletion_isCyclotomicExtension
    m (rationalCyclotomicArtinPlace q)
noncomputable local instance
    rationalCyclotomicArtinExtensionFiniteDimensional_rb59fe0_1
    (m : ℕ+) (q : Nat.Primes) :
    FiniteDimensional
      (rationalCyclotomicArtinBaseAbv q).Completion
      (rationalCyclotomicArtinExtension m q).1.Completion :=
  completionModuleFinite
    (rationalCyclotomicArtinBaseAbv q)
    (RayClass.adicAbv_isNontrivial
      (rationalCyclotomicArtinPlace q))
    (rationalCyclotomicArtinExtension m q)
noncomputable local instance
    rationalCyclotomicArtinExtensionContinuousSMul_rb59fe0_1
    (m : ℕ+) (q : Nat.Primes) :
    ContinuousSMul
      (rationalCyclotomicArtinBaseAbv q).Completion
      (rationalCyclotomicArtinExtension m q).1.Completion :=
  continuousSMul_of_algebraMap _ _
    (AbsoluteValue.completionMap_isometry
      (rationalCyclotomicArtinBaseAbv q)
      (rationalCyclotomicArtinExtension m q).1
      (rationalCyclotomicArtinExtension m q).2).continuous
noncomputable local instance
    rationalCyclotomicArtinExtensionLocallyCompact_rb59fe0_1
    (m : ℕ+) (q : Nat.Primes) :
    LocallyCompactSpace
      (rationalCyclotomicArtinExtension m q).1.Completion :=
  LocallyCompactSpace.of_finiteDimensional_of_complete
    (rationalCyclotomicArtinBaseAbv q).Completion
    (rationalCyclotomicArtinExtension m q).1.Completion
noncomputable local instance
    rationalCyclotomicArtinLocalizedIsUltrametricDist_rb59fe0_1
    (m : ℕ+) (q : Nat.Primes) :
    IsUltrametricDist
      (rationalCyclotomicArtinLocalizedField m q) :=
  localizedCompletionIsUltrametricDist
    (rationalCyclotomicArtinBaseAbv q)
    (rationalCyclotomicArtinExtension m q)
    (HeightOneSpectrum.isNonarchimedean_adicAbv
      ℚ (rationalCyclotomicArtinPlace q))
noncomputable local instance rationalCyclotomicArtinLocalizedValued_rb59fe0_1
    (m : ℕ+) (q : Nat.Primes) :
    Valued (rationalCyclotomicArtinLocalizedField m q) ℝ≥0 :=
  localizedCompletionFinitePlaceValued
    (rationalCyclotomicArtinBaseAbv q)
    (rationalCyclotomicArtinExtension m q)
    (HeightOneSpectrum.isNonarchimedean_adicAbv
      ℚ (rationalCyclotomicArtinPlace q))
attribute [local instance] GlobalClassFieldTheory.Reciprocity.rationalCyclotomicArtinLocalizedValuativeRel
noncomputable local instance
    rationalCyclotomicArtinLocalizedValuationCompatible_rb59fe0_1
    (m : ℕ+) (q : Nat.Primes) :
    (Valued.v : Valuation
      (rationalCyclotomicArtinLocalizedField m q) ℝ≥0).Compatible :=
  Valuation.Compatible.ofValuation _
noncomputable local instance
    rationalCyclotomicArtinLocalizedValuationHasExtension_rb59fe0_1
    (m : ℕ+) (q : Nat.Primes) :
    Valuation.HasExtension
      (ValuativeRel.valuation
        (rationalCyclotomicArtinBaseAbv q).Completion)
      (ValuativeRel.valuation
        (rationalCyclotomicArtinLocalizedField m q)) :=
  localizedCompletionValuationHasExtension
    (rationalCyclotomicArtinBaseAbv q)
    (rationalCyclotomicArtinExtension m q)
    (HeightOneSpectrum.isNonarchimedean_adicAbv
      ℚ (rationalCyclotomicArtinPlace q))
noncomputable local instance
    rationalCyclotomicArtinLocalizedValuationIsNontrivial_rb59fe0_1
    (m : ℕ+) (q : Nat.Primes) :
    (ValuativeRel.valuation
      (rationalCyclotomicArtinLocalizedField m q)).IsNontrivial :=
  Valuation.IsNontrivial.of_hasExtension
    (ValuativeRel.valuation
      (rationalCyclotomicArtinBaseAbv q).Completion)
    (ValuativeRel.valuation
      (rationalCyclotomicArtinLocalizedField m q))
noncomputable local instance
    rationalCyclotomicArtinLocalizedValuativeRelIsNontrivial_rb59fe0_1
    (m : ℕ+) (q : Nat.Primes) :
    ValuativeRel.IsNontrivial
      (rationalCyclotomicArtinLocalizedField m q) :=
  (ValuativeRel.isNontrivial_iff_isNontrivial
    (ValuativeRel.valuation
      (rationalCyclotomicArtinLocalizedField m q))).2 inferInstance
noncomputable local instance
    rationalCyclotomicArtinLocalizedIsValuativeTopology_rb59fe0_1
    (m : ℕ+) (q : Nat.Primes) :
    IsValuativeTopology
      (rationalCyclotomicArtinLocalizedField m q) :=
  isValuativeTopology_of_valued_ofValuation
    (rationalCyclotomicArtinLocalizedField m q) ℝ≥0
noncomputable local instance
    rationalCyclotomicArtinLocalizedIsNonarchimedeanLocalField_rb59fe0_1
    (m : ℕ+) (q : Nat.Primes) :
    IsNonarchimedeanLocalField
      (rationalCyclotomicArtinLocalizedField m q) :=
  { toIsValuativeTopology := inferInstance
    toLocallyCompactSpace := inferInstance
    toIsNontrivial := inferInstance }
noncomputable local instance
    rationalCyclotomicArtinLocalizedIntegerAlgebra_rb59fe0_1
    (m : ℕ+) (q : Nat.Primes) :
    Algebra
      𝒪[(rationalCyclotomicArtinBaseAbv q).Completion]
      (rationalCyclotomicArtinLocalizedField m q) :=
  Algebra.ofSubsemiring
    𝒪[(rationalCyclotomicArtinBaseAbv q).Completion]
noncomputable local instance
    rationalCyclotomicArtinLocalizedIsIntegralClosure_rb59fe0_1
    (m : ℕ+) (q : Nat.Primes) :
    IsIntegralClosure
      𝒪[rationalCyclotomicArtinLocalizedField m q]
      𝒪[(rationalCyclotomicArtinBaseAbv q).Completion]
      (rationalCyclotomicArtinLocalizedField m q) :=
  localizedCompletionIsIntegralClosureWithExtension
    (rationalCyclotomicArtinBaseAbv q)
    (rationalCyclotomicArtinExtension m q)
    (RayClass.adicAbv_isNontrivial
      (rationalCyclotomicArtinPlace q))
    (HeightOneSpectrum.isNonarchimedean_adicAbv
      ℚ (rationalCyclotomicArtinPlace q))
noncomputable local instance
    rationalCyclotomicArtinLocalizedIntegerModuleFinite_rb59fe0_1
    (m : ℕ+) (q : Nat.Primes) :
    Module.Finite
      𝒪[(rationalCyclotomicArtinBaseAbv q).Completion]
      𝒪[rationalCyclotomicArtinLocalizedField m q] :=
  integerRing_moduleFinite_of_isIntegralClosure
    (rationalCyclotomicArtinBaseAbv q).Completion
    (rationalCyclotomicArtinLocalizedField m q)
noncomputable local instance
    rationalCyclotomicPrincipalPrimeLevelIsCyclotomicExtension_rb59fe0_1
    (p : Nat.Primes) (n : ℕ) :
    IsCyclotomicExtension {p.1 ^ (n + 1)} ℚ
      (KummerTheory.rationalCyclotomicLevel
        (rationalCyclotomicPrincipalPrimeModulus p n)) := by
  change
    IsCyclotomicExtension
      {(rationalCyclotomicPrincipalPrimeModulus p n : ℕ)} ℚ
      (KummerTheory.rationalCyclotomicLevel
        (rationalCyclotomicPrincipalPrimeModulus p n))
  exact
    KummerTheory.rationalCyclotomicLevel_isCyclotomicExtension
      (rationalCyclotomicPrincipalPrimeModulus p n)
abbrev rationalCyclotomicPrincipalPrimeLevel
    (m : ℕ+) :=
  rationalCyclotomicArtinLevel m

attribute [local instance] GlobalClassFieldTheory.Reciprocity.rationalCyclotomicArtinExtensionAlgebra
attribute [local instance] GlobalClassFieldTheory.Reciprocity.rationalCyclotomicArtinLocalizedPadicAlgebra
noncomputable def rationalFinitePlaceCompletionAlgEquivPadic
    (p : Nat.Primes) :
    (rationalCyclotomicArtinBaseAbv p).Completion ≃ₐ[ℚ] ℚ_[p.1] :=
  AlgEquiv.ofRingEquiv
    (f := rationalFinitePlaceCompletionRingEquivPadic p)
    (rationalFinitePlaceCompletionRingEquivPadic_algebraMap p)

noncomputable local instance
    rationalCyclotomicArtinLocalizedPadicScalarTower
    (m : ℕ+) (p : Nat.Primes) :
    IsScalarTower ℚ ℚ_[p.1]
      (rationalCyclotomicArtinLocalizedField m p) := by
  constructor
  intro r x y
  simp only [Algebra.smul_def, map_mul, eq_ratCast,
    map_ratCast, mul_assoc]
  try (first | exact (Rat.smul_def r _).symm | (rw [Algebra.smul_def, eq_ratCast]) | simp [Algebra.smul_def])

/-! ## The ramified principal finite-place factor -/

end RationalCyclotomicPrincipalPrime

end Reciprocity
end GlobalClassFieldTheory
end
end

section
-- module Solutions.OAIQ244_DUKE.Kummer_Concrete_Cyclotomic_ProfiniteUnitDecomposition_FiniteFree
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 400000
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_isCompleteDiscrete _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.DiscreteNthRootsSubgroup.instTopologicalSpaceSubtypeUnitsMemSubgroup _root_.LocalClassFieldTheory.finiteGaloisLocalField_integerRing_moduleFinite _root_.LocalFieldTheory.DiscreteValuationField.finite_principalUnits_nthPowerKernel _root_.LocalFieldTheory.DiscreteValuationField.finite_residueRootsOfUnityGroup _root_.LocalFieldTheory.DiscreteValuationField.finite_valuationSubringUnits_nthPowerKernel _root_.LocalFieldTheory.DiscreteValuationField.finite_valuationSubringUnits_nthPowerQuotient _root_.LocalFieldTheory.Padic.padicDVR_residueField_finite _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.LubinTate.padicCompletedLevelField_algebra _root_.LubinTate.padicCompletedUnramifiedFieldAlgebra _root_.LubinTate.standardLubinTateLevelCompleteDVF_hasExtensionInstance _root_.LubinTate.standardLubinTateLevelField_galFinite _root_.LubinTate.standardLubinTateLevelField_isAbelianGalois _root_.LubinTate.standardLubinTateLevelField_isMulCommutative _root_.LubinTate.standardLubinTateLevelValuationSubring_moduleFinite _root_.LubinTate.standardLubinTateUnitParameter_commGroup _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.instTopologicalSpaceLocalAlgebra _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.labelPrime_fact _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RamificationTheory.HilbertRamification.Higher.lowerRamificationGroup.instNormal _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionResidueField.instField _root_.RamificationTheory.HilbertRamification.ValuationSubring.selectedResidueField.instAlgebra _root_.RayClass.approximationCompletionTopologicalSpace _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.LocalClassFieldTheory.comparisonIntegerRingIsIntegralClosure _root_.LocalClassFieldTheory.normalizationIntegerRingIsIntegralClosure _root_.RamificationTheory.HilbertRamification.CompleteDVF.decompositionGroupMulSemiringAction _root_.RamificationTheory.HilbertRamification.CompleteDVF.decompositionGroupResidueFieldMulSemiringAction _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.chosenFinitePlaceCompletionAlgebra _root_.finiteLocalUnitsOpen _root_.infiniteAdeleRingT2Space _root_.relativeAdeleRingIntermediateAlgebra _root_.relativeAdeleRingTopIntermediateAlgebra
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

/-!
# Compiled finite/free collection stage of the profinite-unit decomposition
-/

open scoped Topology

noncomputable section

namespace KummerTheory.ProfiniteUnitDecomposition.Internal

open LocalFieldTheory.Padic

/-- Collect the finite and torsion-free coordinates of the local product. -/
noncomputable def finiteFreeSplit :
    ((p : Nat.Primes) →
      padicUnitFiniteFactor p.1 × Multiplicative ℤ_[p.1]) ≃ₜ*
    ((p : Nat.Primes) → Multiplicative ℤ_[p.1]) ×
      CyclotomicFinitePart where
  toFun x := (fun p => (x p).2, fun p => (x p).1)
  invFun x p := (x.2 p, x.1 p)
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl
  continuous_toFun :=
    (continuous_pi fun p =>
      continuous_snd.comp (continuous_apply p)).prodMk
        (continuous_pi fun p =>
          continuous_fst.comp (continuous_apply p))
  continuous_invFun :=
    continuous_pi fun p =>
      ((continuous_apply p).comp continuous_snd).prodMk
        ((continuous_apply p).comp continuous_fst)

end KummerTheory.ProfiniteUnitDecomposition.Internal
end
end

section
-- module Solutions.OAIQ244_DUKE.Kummer_Concrete_Cyclotomic_ProfiniteUnitDecomposition_Decomposition
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 400000
attribute [-instance] _root_.ClassFormation.DegreeData.FiniteAbstractExtension.ramificationQuotientFinite _root_.ClassFormation.DegreeData.FiniteAbstractExtension.residueQuotientFinite _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_isCompleteDiscrete _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.DiscreteNthRootsSubgroup.instTopologicalSpaceSubtypeUnitsMemSubgroup _root_.LocalClassFieldTheory.finiteGaloisLocalField_integerRing_moduleFinite _root_.LocalFieldTheory.DiscreteValuationField.finite_principalUnits_nthPowerKernel _root_.LocalFieldTheory.DiscreteValuationField.finite_residueRootsOfUnityGroup _root_.LocalFieldTheory.DiscreteValuationField.finite_valuationSubringUnits_nthPowerKernel _root_.LocalFieldTheory.DiscreteValuationField.finite_valuationSubringUnits_nthPowerQuotient _root_.LocalFieldTheory.Padic.padicDVR_residueField_finite _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.LubinTate.padicCompletedLevelField_algebra _root_.LubinTate.padicCompletedUnramifiedFieldAlgebra _root_.LubinTate.standardLubinTateLevelCompleteDVF_hasExtensionInstance _root_.LubinTate.standardLubinTateLevelField_galFinite _root_.LubinTate.standardLubinTateLevelField_isAbelianGalois _root_.LubinTate.standardLubinTateLevelField_isMulCommutative _root_.LubinTate.standardLubinTateLevelValuationSubring_moduleFinite _root_.LubinTate.standardLubinTateUnitParameter_commGroup _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.instTopologicalSpaceLocalAlgebra _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.labelPrime_fact _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RamificationTheory.HilbertRamification.Higher.lowerRamificationGroup.instNormal _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionResidueField.instField _root_.RamificationTheory.HilbertRamification.ValuationSubring.selectedResidueField.instAlgebra _root_.RayClass.approximationCompletionTopologicalSpace _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.LocalClassFieldTheory.comparisonIntegerRingIsIntegralClosure _root_.LocalClassFieldTheory.normalizationIntegerRingIsIntegralClosure _root_.RamificationTheory.HilbertRamification.CompleteDVF.decompositionGroupMulSemiringAction _root_.RamificationTheory.HilbertRamification.CompleteDVF.decompositionGroupResidueFieldMulSemiringAction _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.chosenFinitePlaceCompletionAlgebra _root_.finiteLocalUnitsOpen _root_.infiniteAdeleRingT2Space _root_.relativeAdeleRingIntermediateAlgebra _root_.relativeAdeleRingTopIntermediateAlgebra
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

/-!
# The profinite-unit product decomposition
-/

open scoped Topology

noncomputable section

namespace KummerTheory

open ClassFormation
open LocalFieldTheory.Padic

/-- Topological decomposition
`ℤ̂ˣ ≃ Multiplicative ℤ̂ × finite-product` used in the rational cyclotomic
calculation. -/
noncomputable def zHatUnitsDecomposition :
    ZHatˣ ≃ₜ* Multiplicative ZHat × CyclotomicFinitePart :=
  zHatUnitsContinuousMulEquivPrimeProduct.trans <|
    ProfiniteUnitDecomposition.Internal.localDecomposition.symm.trans <|
      ProfiniteUnitDecomposition.Internal.finiteFreeSplit.trans <|
        continuousMulEquivProdCongr
          ProfiniteUnitDecomposition.Internal.gatherFree
          (ContinuousMulEquiv.refl CyclotomicFinitePart)

end KummerTheory
end
end

section
-- module Solutions.OAIQ244_DUKE.Kummer_Concrete_Cyclotomic_ProfiniteUnitDecomposition_FreeCoordinate
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 400000
attribute [-instance] _root_.ClassFormation.DegreeData.FiniteAbstractExtension.ramificationQuotientFinite _root_.ClassFormation.DegreeData.FiniteAbstractExtension.residueQuotientFinite _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.DiscreteNthRootsSubgroup.instTopologicalSpaceSubtypeUnitsMemSubgroup _root_.LocalClassFieldTheory.finiteGaloisLocalField_integerRing_moduleFinite _root_.LocalFieldTheory.DiscreteValuationField.finite_principalUnits_nthPowerKernel _root_.LocalFieldTheory.DiscreteValuationField.finite_residueRootsOfUnityGroup _root_.LocalFieldTheory.DiscreteValuationField.finite_valuationSubringUnits_nthPowerKernel _root_.LocalFieldTheory.DiscreteValuationField.finite_valuationSubringUnits_nthPowerQuotient _root_.LocalFieldTheory.Padic.padicDVR_residueField_finite _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.LubinTate.padicCompletedLevelField_algebra _root_.LubinTate.padicCompletedUnramifiedFieldAlgebra _root_.LubinTate.standardLubinTateLevelCompleteDVF_hasExtensionInstance _root_.LubinTate.standardLubinTateLevelField_galFinite _root_.LubinTate.standardLubinTateLevelField_isAbelianGalois _root_.LubinTate.standardLubinTateLevelField_isMulCommutative _root_.LubinTate.standardLubinTateLevelValuationSubring_moduleFinite _root_.LubinTate.standardLubinTateUnitParameter_commGroup _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.instTopologicalSpaceLocalAlgebra _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.labelPrime_fact _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RamificationTheory.HilbertRamification.Higher.lowerRamificationGroup.instNormal _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionResidueField.instField _root_.RamificationTheory.HilbertRamification.ValuationSubring.selectedResidueField.instAlgebra _root_.RayClass.approximationCompletionTopologicalSpace _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.LocalClassFieldTheory.comparisonIntegerRingIsIntegralClosure _root_.LocalClassFieldTheory.normalizationIntegerRingIsIntegralClosure _root_.RamificationTheory.HilbertRamification.CompleteDVF.decompositionGroupMulSemiringAction _root_.RamificationTheory.HilbertRamification.CompleteDVF.decompositionGroupResidueFieldMulSemiringAction _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.chosenFinitePlaceCompletionAlgebra _root_.finiteLocalUnitsOpen _root_.infiniteAdeleRingT2Space _root_.relativeAdeleRingIntermediateAlgebra _root_.relativeAdeleRingTopIntermediateAlgebra
attribute [-simp] _root_.ClassFormation.DegreeData.FiniteAbstractExtension.inertia_relIndex_eq_ramificationIndex _root_.ClassFormation.DegreeData.FiniteAbstractExtension.mapped_relIndex_eq_residueDegree _root_.ClassFormation.DegreeData.FiniteAbstractExtension.ramificationIndex_coe _root_.ClassFormation.DegreeData.FiniteAbstractExtension.residueDegree_coe _root_.ClassFormation.DegreeData.extensionNormalizedDegreeContinuous_apply _root_.ClassFormation.DegreeData.extensionNormalizedDegreeContinuous_toMonoidHom _root_.ClassFormation.DegreeData.extensionNormalizedDegree_frobenius_mul _root_.ClassFormation.DegreeData.extensionNormalizedDegree_mk _root_.ClassFormation.DegreeData.fieldImageAdd_index _root_.ClassFormation.DegreeData.finiteReciprocityNaturalityFrobeniusConjugationLift_coe _root_.ClassFormation.DegreeData.finiteReciprocityNaturalityFrobeniusTowerLift_coe _root_.ClassFormation.DegreeData.finiteUnramifiedDegreeHom_mk _root_.ClassFormation.DegreeData.fixedFieldNormalizedDegree_generator _root_.ClassFormation.DegreeData.frobeniusActionConjugate_coe _root_.ClassFormation.DegreeData.frobeniusClosureDegreeInMulNatRange_coe _root_.ClassFormation.DegreeData.frobeniusClosureDegree_generator _root_.ClassFormation.DegreeData.frobeniusFixedFieldAction_coe _root_.ClassFormation.DegreeData.frobeniusFixedField_normalizedDegreeEquiv_apply _root_.ClassFormation.DegreeData.frobeniusLiftDifference_coe _root_.ClassFormation.DegreeData.frobeniusMul_coe _root_.ClassFormation.DegreeData.frobeniusPowerOfDegreeOne_coe _root_.ClassFormation.DegreeData.maximalUnramifiedDegreeEquiv_frobenius _root_.ClassFormation.DegreeData.maximalUnramifiedDegreeEquiv_mk _root_.ClassFormation.DegreeData.maximalUnramifiedFrobeniusPower_one _root_.ClassFormation.DegreeData.mem_fieldInertiaWithin_iff _root_.ClassFormation.DegreeData.mem_fieldInertia_iff _root_.ClassFormation.DegreeData.mem_inertia_iff _root_.ClassFormation.DegreeData.mem_maximalUnramifiedField_iff _root_.ClassFormation.DegreeData.normalizedDegree_apply_toAdd _root_.ClassFormation.DegreeData.restrictedDegreeInMulNatRange_coe _root_.ClassFormation.DegreeData.restrictedDegree_apply _root_.ClassFormation.DegreeData.transferNormNaturalityTransferFrobeniusLift_coe _root_.ClassFormation.DegreeData.transferNormNaturalityTransferNormOrbitEquiv_mk _root_.ClassFormation.ValuationData.canonicalValueQuotientHom_mk _root_.ClassFormation.ValuationData.canonicalValueReduction_one _root_.ClassFormation.ValuationData.maximalUnramifiedNormResidue_degree _root_.ClassFormation.ValuationData.mem_unitAddSubgroup_iff _root_.ClassFormation.ValuationData.oneValue_coe _root_.ClassFormation.ValuationData.valuationAt_chosenPrimeElement _root_.ClassFormation.ValuationData.valuationAt_coe _root_.ClassFormation.ValuationData.valueModulo_apply _root_.ClassFormation.canonicalValueQuotientMap_mk _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.ClassFormation.mem_nsmulImage_iff _root_.ClassFormation.nsmulImage_top _root_.ClassFormation.zHatPowNat_apply_toAdd _root_.ClassFormation.zHatPowNat_one _root_.ClassFormation.zHatReductionMul_apply_toAdd _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.GlobalClassFieldTheory.Reciprocity.rationalPrimeUnitValuationSubringUnit_coe _root_.IsDiscreteValuationRing.addVal_ringEquiv _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.KummerTheory.zHatUnitsContinuousMulEquivPrimeProduct_rationalCyclotomicCharacter _root_.LocalClassFieldTheory.finiteResidueFrobeniusFromZHat_apply _root_.LocalClassFieldTheory.finiteResidueFrobeniusFromZHat_one _root_.LocalClassFieldTheory.localBaseValuation_baseFieldUnitsEquiv _root_.LocalClassFieldTheory.residueAbsoluteDegreeIn_frobenius _root_.LocalClassFieldTheory.residueAbsoluteFrobenius_one _root_.LocalClassFieldTheory.residueFrobeniusToLimit_apply_component _root_.LocalFieldTheory.Padic.integerRingEquivPadicDVRValuationSubring_coe _root_.LocalFieldTheory.localIntegerValuationSubringEquiv_apply_coe _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.LocalFieldTheory.residueField_algebraMap_residue _root_.LubinTate.LubinTateSeries.padicMultiplicativeLubinTateSeries_toPowerSeries _root_.LubinTate.LubinTateSeries.standardLubinTateSeries_toPowerSeries _root_.LubinTate.SameUniformizer.coeff_recursiveIntertwiner _root_.LubinTate.SameUniformizer.constantCoeff_inVariable _root_.LubinTate.SameUniformizer.intertwinerApproximation_zero _root_.LubinTate.SameUniformizer.standardLubinTateEndomorphism_coeff_one _root_.LubinTate.padicChangedUniformizerIntertwiner_coeff _root_.LubinTate.padicChangedUniformizerIntertwiner_coeff_one _root_.LubinTate.padicCompletedChangedStandardScalarEndomorphism_coeff_one _root_.LubinTate.padicCompletedChangedStandardScalarEndomorphism_one _root_.LubinTate.padicCompletedLevelPadicIntegerCoefficientHom_coe _root_.LubinTate.padicCompletedLevelPowerSeriesEval_C _root_.LubinTate.padicCompletedLevelPowerSeriesEval_X _root_.LubinTate.padicCompletedLevelPowerSeriesEval_coe _root_.LubinTate.padicCompletedLevelWittCoefficientHom_apply _root_.LubinTate.padicCompletedMultiplicativeScalarEndomorphismValue_one _root_.LubinTate.padicCompletedMultiplicativeScalarEndomorphism_coeff_one _root_.LubinTate.padicCompletedPrimitiveRootInteger_coe _root_.LubinTate.padicCompletedStandardScalarEndomorphismValue_one _root_.LubinTate.padicCompletedStandardScalarEndomorphism_one _root_.LubinTate.padicCompletedUnramifiedIntegerMap_coe _root_.LubinTate.padicStandardToMultiplicativeIntertwiner_coeff_one _root_.LubinTate.padicValuationSubringToCompletedUnramifiedWittRing_uniformizer _root_.LubinTate.standardLubinTateBaseUniformizerUnit_coe _root_.LubinTate.standardLubinTateChangedUniformizerUnit_coe _root_.LubinTate.standardLubinTateEndomorphismEvalAt_one _root_.LubinTate.standardLubinTateEndomorphismEvalAt_zero _root_.LubinTate.standardLubinTateEndomorphismValue_one _root_.LubinTate.standardLubinTateEndomorphismValue_zero _root_.LubinTate.standardLubinTateLevelCoefficientHom_apply _root_.LubinTate.standardLubinTateLevelGenerator_coe _root_.LubinTate.standardLubinTateLevelPowerSeriesEval_C _root_.LubinTate.standardLubinTateLevelPowerSeriesEval_X _root_.LubinTate.standardLubinTateLevelPowerSeriesEval_coe _root_.LubinTate.standardLubinTatePolynomialIterateOverSeparableClosure_eval _root_.LubinTate.standardLubinTatePolynomialIterate_derivative_eval_zero _root_.LubinTate.standardLubinTatePolynomialIterate_eval_zero _root_.LubinTate.standardLubinTatePolynomialIterate_zero _root_.LubinTate.standardLubinTatePolynomial_derivative_eval_zero _root_.LubinTate.standardLubinTatePolynomial_eval _root_.LubinTate.standardLubinTatePolynomial_toPowerSeries _root_.LubinTate.standardLubinTatePolynomial_toPowerSeries_eq_series _root_.LubinTate.standardLubinTatePrimitiveLevelAction_coe _root_.LubinTate.standardLubinTatePrimitivePointIntegerAction_one _root_.LubinTate.standardLubinTatePrimitivePointInteger_coe _root_.LubinTate.standardLubinTatePrimitivePointIterateInteger_zero _root_.LubinTate.standardLubinTatePrimitivePolynomialOverField_coeff_zero _root_.LubinTate.standardLubinTatePrimitivePolynomial_coeff_zero _root_.LubinTate.standardLubinTatePrimitiveRootAction_one _root_.LubinTate.standardLubinTateUnitFactorFieldUnit_coe _root_.LubinTate.standardLubinTateUnitParameterAlgEquiv_apply_gen _root_.LubinTate.standardLubinTateUnitParameterAlgHom_apply_gen _root_.LubinTate.standardLubinTateUnitParameterChosenRepresentative_spec _root_.LubinTate.standardLubinTateUnitParameterEquivGal_apply _root_.LubinTate.standardLubinTateUnitParameterEquivGal_inv_class_apply_gen _root_.LubinTate.standardLubinTateUnitParameterLevelRoot_coe _root_.LubinTate.standardLubinTateUnitParameterLevelRoot_one _root_.LubinTate.standardLubinTateUnitParameterRoot_class _root_.LubinTate.standardLubinTateUnitParameterToGalHom_apply _root_.OAI.PrimeDegreePackets.ThetaConstruction.schwartzCM_apply _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteResidueActionOfHenselianDVF_apply _root_.RamificationTheory.HilbertRamification.CompleteDVF.decompositionResidueAction_algebraMap _root_.RamificationTheory.HilbertRamification.CompleteDVF.decompositionResidueAction_apply _root_.RamificationTheory.HilbertRamification.CompleteDVF.residueAction_apply _root_.RamificationTheory.HilbertRamification.Higher.dvfUniformizerQuotientUnit_mul_uniformizer _root_.RamificationTheory.HilbertRamification.Higher.dvfUniformizerRepresentativeHom_apply _root_.RamificationTheory.HilbertRamification.Higher.dvfValuationSubringUnitAut_apply _root_.RamificationTheory.HilbertRamification.Higher.intrinsicRamificationNumberOfUniqueExtension_one _root_.RamificationTheory.HilbertRamification.Higher.lowerRamificationGroup_neg_one _root_.RamificationTheory.HilbertRamification.Higher.mem_dvfHigherPrincipalUnitGroup_iff _root_.RamificationTheory.HilbertRamification.Higher.mem_lowerRamificationGroup_iff _root_.RamificationTheory.HilbertRamification.Higher.mem_valuationSubringDisplacementSubalgebraOfUniqueExtension_iff _root_.RamificationTheory.HilbertRamification.Higher.ramificationNumberDepthOfUniqueExtension_depth _root_.RamificationTheory.HilbertRamification.Higher.ramificationNumberOfUniqueExtension_one _root_.RamificationTheory.HilbertRamification.Higher.realRamificationIdeal_nat _root_.RamificationTheory.HilbertRamification.Higher.realRamificationIdeal_neg_one _root_.RamificationTheory.HilbertRamification.Higher.uniformizerGradedHom_mk _root_.RamificationTheory.HilbertRamification.Higher.valuationSubringAutOfUniqueExtension_apply_coe _root_.RamificationTheory.HilbertRamification.Higher.valuationSubringAutOfUniqueExtension_apply_inv_apply _root_.RamificationTheory.HilbertRamification.Higher.valuationSubringAutOfUniqueExtension_mul_apply _root_.RamificationTheory.HilbertRamification.Higher.valuationSubringAutOfUniqueExtension_one_apply _root_.RayClass.primesEquiv_val_eq_natGenerator _root_.LubinTate.standardLubinTateLevelAutomorphismIntegerRingEquiv_apply _root_.LubinTate.padicChangedUniformizerLinearCoefficient_coe _root_.LubinTate.padicMultiplicativeLevelAutomorphismIntegerRingEquiv_apply _root_.infinitePlace_mult_smul
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

/-!
# Local coordinates of the profinite-unit decomposition
-/

open scoped Topology

noncomputable section

namespace KummerTheory

open ClassFormation
open LocalFieldTheory.Padic

/-- The `p`-adic coordinate of the global free factor in
`zHatUnitsDecomposition` is exactly the free factor in the genuine
local decomposition of the `p`-adic unit coordinate. -/
@[simp]
theorem zHatUnitsDecomposition_freeCoordinate
    (u : ZHatˣ) (p : Nat.Primes) :
    zHatToPadicInt p
        (Multiplicative.toAdd
          (zHatUnitsDecomposition u).1) =
      Multiplicative.toAdd
        (((padicUnitDecomposition p.1).symm
          (zHatUnitsContinuousMulEquivPrimeProduct u p)).2) := by
  let y : ProfiniteIntegerPrimeProduct :=
    fun q =>
      Multiplicative.toAdd
        (((padicUnitDecomposition q.1).symm
          (zHatUnitsContinuousMulEquivPrimeProduct u q)).2)
  change
    zHatToPadicInt p
        (zHatContinuousAddEquivPrimeProduct.symm y) =
      y p
  exact
    congrFun
      (zHatContinuousAddEquivPrimeProduct.apply_symm_apply y) p

end KummerTheory
end
end


