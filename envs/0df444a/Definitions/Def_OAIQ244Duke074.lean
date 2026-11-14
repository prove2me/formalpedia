-- Prove2me | Definitions.Def_OAIQ244Duke074
-- name    : OAIQ244Duke074
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-13T23:07:38.069143+00:00
-- url     : https://prove2.me/theorems/731184bd-db9f-459a-a216-a48c0888e80b
-- title:
--   Definitions bundle OAIQ244Duke074 of the split of OpenAI, Equidistribution of Prime-Degree Torus Packets with Arbitrary Local Type
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.DukePrimeDegree.prime_degree_packet_measure_equidistribution_unconditional` and `OAI.DukePrimeDegree.prime_degree_packet_measures_tendsto_haar_unconditional`, carved from OpenAI's openai/math development (OpenAI, *Equidistribution of Prime-Degree Torus Packets with Arbitrary Local Type*, OpenAI Math Release, September 24, 2026, result family 15, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 61 declarations of OpenAI's Lean: 6 definitions and 55 theorems. The definitions and types are `GlobalClassFieldTheory.ClassFieldAxiom.sUnitKummerChosenBasePlaces`, `GlobalClassFieldTheory.ClassFieldAxiom.sUnitKummerCoordinatePlace`, `GlobalClassFieldTheory.ClassFieldAxiom.sUnitKummerPrimeSet`, `GlobalClassFieldTheory.Reciprocity.finitePlaceNormLowerRawArtin`, `GlobalClassFieldTheory.Reciprocity.finitePlaceNormUpperRawArtin`, `LocalClassFieldTheory.abelianLocalArtinMonoidHom`.
--
--   **Sources.** They come from these modules of lean/OAI/NumberTheory, in whole or in part: `AlgebraicNumberTheory_Idele_Cohomology_SPlaces_OutsideIntegralInduced_ChosenPlace`, `AlgebraicNumberTheory_Idele_Cohomology_SupportedBridge`, `AlgebraicNumberTheory_Idele_SufficientlyLarge`, `GlobalClassFieldTheory_ClassFieldAxiom_CyclicIdeleClassNormIndex`, `GlobalClassFieldTheory_ClassFieldAxiom_IdeleClassPowerLocalUnitQuotient_NormContainment`, `GlobalClassFieldTheory_ClassFieldAxiom_IdeleClassPowerLocalUnitQuotient_PrimePowerKummerIndex`, `GlobalClassFieldTheory_ClassFieldAxiom_IdelePowerLocalUnitNormContainment`, `GlobalClassFieldTheory_ClassFieldAxiom_KummerLocalNormContainment`, `GlobalClassFieldTheory_ClassFieldAxiom_SUnitKummerPrimeSelection_BasePlaceSelection`, `GlobalClassFieldTheory_ClassFieldAxiom_SUnitKummerPrimeSelection_Conclusion`, `GlobalClassFieldTheory_ClassFieldAxiom_SUnitKummerPrimeSelection_CoordinatePlaces`, `GlobalClassFieldTheory_ClassFieldAxiom_SUnitKummerPrimeSelection_DecompositionFields`, `GlobalClassFieldTheory_ClassFieldAxiom_SUnitKummerPrimeSelection_PrimeSet`, `GlobalClassFieldTheory_ClassFieldAxiom_SUnitLocalPowerMap`, `GlobalClassFieldTheory_Cohomology_CyclicPrimePowerFullDecomposition`, `GlobalClassFieldTheory_Cohomology_IdeleClassHerbrandSupportedFinal`, `GlobalClassFieldTheory_Reciprocity_FinitePlaceArtin_NormRestriction`, `LocalClassFieldTheory_Finite_LocalReciprocity_NormResidue`, `LubinTate_Padic_ChangedUniformizerIntertwiner_IntertwinerConstruction`.
--
--   **Imports.** It imports the bundles `OAIQ244Duke069`, `OAIQ244Duke070` and `OAIQ244Duke071` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ244Duke080`, `OAIQ244Duke082` and `OAIQ244Duke114`.
-- source:
--   OpenAI, Equidistribution of Prime-Degree Torus Packets with Arbitrary Local Type, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 15; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Equidistribution-of-Prime-Degree-Torus-Packets-with-Arbitrary-Local-Type-September-24-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/NumberTheory at commit 7ef5c0c

import Mathlib
import Mathlib.Algebra.Algebra.Basic
import Mathlib.Algebra.Algebra.Pi
import Mathlib.Algebra.Algebra.Tower
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.GroupWithZero.Finset
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Category.ModuleCat.Basic
import Mathlib.Algebra.CharP.Algebra
import Mathlib.Algebra.CharP.Lemmas
import Mathlib.Algebra.CharP.Subring
import Mathlib.Algebra.EuclideanDomain.Basic
import Mathlib.Algebra.Exact.Basic
import Mathlib.Algebra.Group.Action.Basic
import Mathlib.Algebra.Group.Equiv.Basic
import Mathlib.Algebra.Group.Equiv.TypeTags
import Mathlib.Algebra.Group.Hom.Basic
import Mathlib.Algebra.Group.Int.TypeTags
import Mathlib.Algebra.Group.Pi.Basic
import Mathlib.Algebra.Group.Pi.Units
import Mathlib.Algebra.Group.Subgroup.Basic
import Mathlib.Algebra.Group.Subgroup.Finite
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
import Mathlib.Algebra.Order.Field.Power
import Mathlib.Algebra.Order.Group.Cyclic
import Mathlib.Algebra.Order.Hom.Units
import Mathlib.Algebra.Order.Ring.IsNonarchimedean
import Mathlib.Algebra.Order.WithTop.Untop0
import Mathlib.Algebra.Polynomial.Div
import Mathlib.Algebra.Polynomial.FieldDivision
import Mathlib.Algebra.Polynomial.Lifts
import Mathlib.Algebra.Polynomial.Monic
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
import Mathlib.Combinatorics.Hall.Finite
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Finsupp
import Mathlib.Data.Finsupp.Fintype
import Mathlib.Data.Int.ModEq
import Mathlib.Data.Int.WithZero
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Rat.Cast.CharZero
import Mathlib.Data.Rat.Lemmas
import Mathlib.Data.Set.Finite.Range
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.ZMod.QuotientGroup
import Mathlib.Dynamics.BirkhoffSum.Basic
import Mathlib.FieldTheory.AbsoluteGaloisGroup
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.FieldTheory.Finite.Extension
import Mathlib.FieldTheory.Finite.GaloisField
import Mathlib.FieldTheory.Galois.Abelian
import Mathlib.FieldTheory.Galois.Basic
import Mathlib.FieldTheory.Galois.Infinite
import Mathlib.FieldTheory.Galois.IsGaloisGroup
import Mathlib.FieldTheory.Galois.NormalBasis
import Mathlib.FieldTheory.Galois.Notation
import Mathlib.FieldTheory.Galois.Profinite
import Mathlib.FieldTheory.IntermediateField.Adjoin.Algebra
import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
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
import Mathlib.GroupTheory.QuotientGroup.Finite
import Mathlib.GroupTheory.SpecificGroups.Cyclic
import Mathlib.GroupTheory.Sylow
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
import Mathlib.NumberTheory.NumberField.InfinitePlace.Ramification
import Mathlib.NumberTheory.NumberField.ProductFormula
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
import Mathlib.RingTheory.FractionalIdeal.Norm
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Ideal.GoingUp
import Mathlib.RingTheory.Ideal.IsPrincipalPowQuotient
import Mathlib.RingTheory.Ideal.Norm.AbsNorm
import Mathlib.RingTheory.Ideal.Norm.RelNorm
import Mathlib.RingTheory.Ideal.Quotient.Index
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.RingTheory.IntegralClosure.IsIntegralClosure.Basic
import Mathlib.RingTheory.Invariant.Profinite
import Mathlib.RingTheory.IsTensorProduct
import Mathlib.RingTheory.LaurentSeries
import Mathlib.RingTheory.LocalRing.Basic
import Mathlib.RingTheory.LocalRing.Module
import Mathlib.RingTheory.LocalRing.ResidueField.Basic
import Mathlib.RingTheory.Localization.Away.Basic
import Mathlib.RingTheory.Localization.Finiteness
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
import Mathlib.RingTheory.PowerSeries.Log
import Mathlib.RingTheory.PowerSeries.Order
import Mathlib.RingTheory.PowerSeries.Trunc
import Mathlib.RingTheory.PowerSeries.WellKnown
import Mathlib.RingTheory.QuasiFinite.Basic
import Mathlib.RingTheory.RamificationInertia.Basic
import Mathlib.RingTheory.RootsOfUnity.Basic
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
import Mathlib.Topology.Sets.Opens
import Mathlib.Topology.UniformSpace.AbsoluteValue
import Mathlib.Topology.WithTopology
import Definitions.Def_OAIQ244Duke069
import Definitions.Def_OAIQ244Duke070
import Definitions.Def_OAIQ244Duke071

section
-- module Solutions.OAIQ244_DUKE.AlgebraicNumberTheory_Idele_Cohomology_SPlaces_OutsideIntegralInduced_ChosenPlace
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalCyclotomicCompletionAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalCyclotomicLocalizedCompletionFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalCyclotomicLocalizedCompletionIsAlgebraic _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.DiscreteNthRootsSubgroup.instCommGroupSubtypeUnitsMemSubgroup _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalClassFieldTheory.finiteGaloisLocalField_integerRing_moduleFinite _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitQuotientCarrier_finite _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.residueFieldZModAlgebra _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedIntegralAlgebraContextValuationSubringAlgebra _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedIntegralLatticeContextModuleFinite _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedIntegralLatticeContextModuleFree _root_.LocalFieldTheory.DiscreteValuationField.finite_nsmulAddKernel_padicInt_pi _root_.LocalFieldTheory.DiscreteValuationField.finite_principalUnits_nthPowerKernel _root_.LocalFieldTheory.DiscreteValuationField.finite_residueRootsOfUnityGroup _root_.LocalFieldTheory.DiscreteValuationField.finite_valuationSubringUnits_nthPowerKernel _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.Padic.padicUnitFiniteFactor_finite _root_.LocalFieldTheory.finite_multiplicative_nthPowerKernel _root_.LocalFieldTheory.finite_nsmulAddKernel_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.LubinTate.compatibleGroupFamiliesCommGroup _root_.LubinTate.compatibleGroupFamiliesGroup _root_.LubinTate.padicCompletedLevelField_algebra _root_.LubinTate.padicCompletedUnramifiedFieldAlgebra _root_.LubinTate.standardLubinTateLevelField_galFinite _root_.LubinTate.standardLubinTateLevelValuationSubring_moduleFinite _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.boundedRealFields_finite _root_.OAI.PrimeDegreePackets.instIsTopologicalRingLocalAlgebra _root_.OAI.PrimeDegreePackets.instTopologicalSpaceLocalAlgebra _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.CyclicCohomology.binaryCoefficientFamilyCommGroup _root_.CyclicCohomology.instMulDistribMulActionBinaryCoefficientFamily _root_.LocalClassFieldTheory.comparisonIntegerRingIsIntegralClosure _root_.LocalClassFieldTheory.normalizationIntegerRingIsIntegralClosure _root_.relativeUnrestrictedSPlaceFactorCommGroup
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

/-!
# Integral induced blocks at the chosen finite place

This file specializes the integral induced-block construction to the actual
chosen localization above a finite place and proves its unramified Tate
cohomology consequences.
-/

open scoped NumberField TensorProduct ValuativeRel NNReal
open NumberField IsDedekindDomain

noncomputable section

open AlgebraicNumberTheory.Valuations
open HilbertRamification
open LocalClassFieldTheory
open LocalFieldTheory
open CyclicCohomology.ProfiniteCohomology.Herbrand
open CyclicCohomology

variable
    {K : Type} {L : Type}
    [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]

section ChosenFinitePlace

omit [NumberField L] in
/-- At an unramified chosen finite extension, the actual integral tensor
subgroup has trivial degree-zero Herbrand cohomology. -/
theorem
    relativeLocalTensorDecompositionIntegralUnitSubgroup_unramifiedHerbrandH0_subsingleton
    (w₀ : HeightOneSpectrum (𝓞 K))
    (σ : L ≃ₐ[K] L)
    (hσ : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ)
    (hunram : ChosenFinitePlaceIsUnramified
      (K := K) (L := L) w₀) :
    letI :=
      relativeLocalTensorDecompositionIntegralUnitSubgroupAction
        (K := K) (L := L) w₀
    Subsingleton
      (HerbrandH0 (L ≃ₐ[K] L)
        (relativeLocalTensorDecompositionIntegralUnitSubgroup
          (K := K) (L := L) w₀)) := by
  let :=
    relativeLocalTensorDecompositionIntegralUnitSubgroupAction
      (K := K) (L := L) w₀
  let E := ChosenFinitePlaceLocalizedCompletion
    (K := K) (L := L) w₀
  let H := absoluteValueDecompositionGroup K
    (chosenFinitePlaceExtension (L := L) w₀).1
  let : Fintype H :=
    chosenFinitePlaceDecompositionGroupFintypeProvider
      (K := K) (L := L) w₀
  let : MulDistribMulAction H 𝒪[E]ˣ :=
    chosenFinitePlaceDecompositionGroupIntegerUnitsAction
      (K := K) (L := L) w₀
  have hdecomp :=
    chosenFinitePlaceDecompositionGroupIntegerUnits_unramifiedHerbrand_subsingleton
      (K := K) (L := L) w₀ σ hσ hunram
  let eTensor := herbrandH0EquivariantMulEquiv
    (relativeLocalTensorDecompositionIntegralUnitSubgroupEquivInducedIntegerUnits
      (K := K) (L := L) w₀)
    (relativeLocalTensorDecompositionIntegralUnitSubgroupEquivInducedIntegerUnits_smul
      (K := K) (L := L) w₀)
  let eShapiro :=
    inducedHerbrandH0EquivOfFiniteCyclic (B := 𝒪[E]ˣ) H σ hσ
  refine ⟨fun x y ↦ eTensor.injective ?_⟩
  refine eShapiro.injective ?_
  exact @Subsingleton.elim _ hdecomp.1 _ _

omit [NumberField L] in
/-- At an unramified chosen finite extension, the actual integral tensor
subgroup has trivial degree-minus-one Herbrand cohomology. -/
theorem
    relativeLocalTensorDecompositionIntegralUnitSubgroup_unramifiedHerbrandHMinusOne_subsingleton
    (w₀ : HeightOneSpectrum (𝓞 K))
    (σ : L ≃ₐ[K] L)
    (hσ : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ)
    (hunram : ChosenFinitePlaceIsUnramified
      (K := K) (L := L) w₀) :
    letI :=
      relativeLocalTensorDecompositionIntegralUnitSubgroupAction
        (K := K) (L := L) w₀
    Subsingleton
      (HerbrandHMinusOne (L ≃ₐ[K] L)
        (relativeLocalTensorDecompositionIntegralUnitSubgroup
          (K := K) (L := L) w₀) σ) := by
  let :=
    relativeLocalTensorDecompositionIntegralUnitSubgroupAction
      (K := K) (L := L) w₀
  let E := ChosenFinitePlaceLocalizedCompletion
    (K := K) (L := L) w₀
  let H := absoluteValueDecompositionGroup K
    (chosenFinitePlaceExtension (L := L) w₀).1
  let : Fintype H :=
    chosenFinitePlaceDecompositionGroupFintypeProvider
      (K := K) (L := L) w₀
  let : MulDistribMulAction H 𝒪[E]ˣ :=
    chosenFinitePlaceDecompositionGroupIntegerUnitsAction
      (K := K) (L := L) w₀
  let δ := subgroupGeneratorOfGenerator H σ hσ
  have hdecomp :=
    chosenFinitePlaceDecompositionGroupIntegerUnits_unramifiedHerbrand_subsingleton
      (K := K) (L := L) w₀ σ hσ hunram
  let eTensor := herbrandHMinusOneEquivariantMulEquiv
    (relativeLocalTensorDecompositionIntegralUnitSubgroupEquivInducedIntegerUnits
      (K := K) (L := L) w₀)
    (relativeLocalTensorDecompositionIntegralUnitSubgroupEquivInducedIntegerUnits_smul
      (K := K) (L := L) w₀)
    σ
  let eShapiro :=
    inducedHerbrandHMinusOneEquivOfFiniteCyclic (B := 𝒪[E]ˣ) H σ hσ
  refine ⟨fun x y ↦ eTensor.injective ?_⟩
  refine eShapiro.injective ?_
  exact @Subsingleton.elim _ hdecomp.2 _ _

end ChosenFinitePlace
end
end

section
-- module Solutions.OAIQ244_DUKE.AlgebraicNumberTheory_Idele_SufficientlyLarge
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 400000
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.GlobalClassFields.ConductorialSubgroup.finiteIndex _root_.GlobalClassFieldTheory.GlobalClassFields.bigHilbertClassFieldNormSubgroup_normal _root_.GlobalClassFieldTheory.GlobalClassFields.smallHilbertClassFieldNormSubgroupFiniteIndex _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalClassFieldTheory.finiteGaloisLocalField_integerRing_moduleFinite _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.residueFieldZModAlgebra _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedIntegralAlgebraContextValuationSubringAlgebra _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.LubinTate.padicCompletedLevelField_algebra _root_.LubinTate.padicCompletedUnramifiedFieldAlgebra _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.CyclicCohomology.binaryCoefficientFamilyCommGroup _root_.LocalClassFieldTheory.comparisonIntegerRingIsIntegralClosure _root_.LocalClassFieldTheory.normalizationIntegerRingIsIntegralClosure _root_.chosenFinitePlaceCompletionAlgebra _root_.relativeUnrestrictedSPlaceFactorCommGroup
attribute [-simp] _root_.GlobalClassFieldTheory.ClassFieldAxiom.actualPushoutNormQuotientMap_mk _root_.GlobalClassFieldTheory.ClassFieldAxiom.hasseNormDiagonal_mk _root_.GlobalClassFieldTheory.ClassFieldAxiom.sUnitEquivSupportedPrincipalIdeleSubgroup_coe _root_.GlobalClassFieldTheory.GlobalClassFields.ConductorialSubgroup.ideleClassQuotientEquivOfNarrowFiniteConductorsEqOfRayClassGroupCardsEqQuotientCards_mk _root_.GlobalClassFieldTheory.GlobalClassFields.ConductorialSubgroup.mem_fullConductorInfinitePart_iff _root_.GlobalClassFieldTheory.GlobalClassFields.ConductorialSubgroup.narrowFiniteConductorRayClassGroupEquivQuotientOfCardEq_mk _root_.GlobalClassFieldTheory.GlobalClassFields.ConductorialSubgroup.narrowFiniteConductorRayClassGroupToQuotient_mk _root_.GlobalClassFieldTheory.GlobalClassFields.bigHilbertClassFieldQuotientEquivNarrowClassGroup_mk _root_.GlobalClassFieldTheory.GlobalClassFields.bigHilbertClassFieldQuotientToSmallHilbertClassFieldQuotient_mk _root_.GlobalClassFieldTheory.GlobalClassFields.realSignToBigHilbertClassFieldQuotient_apply _root_.GlobalClassFieldTheory.GlobalClassFields.realSignToNarrowClassKernel_apply _root_.GlobalClassFieldTheory.GlobalClassFields.smallHilbertClassFieldQuotientEquivClassGroup_mk _root_.GlobalClassFieldTheory.Reciprocity.globalNormClassFromIdele_principalIdele _root_.GlobalClassFieldTheory.Reciprocity.infinitePlaceGlobalArtinMonoidHom_finitePlaceIdele _root_.IdeleGroup.finitePlaceIdele_finiteComponent_of_ne _root_.IdeleGroup.finitePlaceIdele_finiteComponent_same _root_.IdeleGroup.finitePlaceIdele_infiniteComponent _root_.IdeleGroup.ideleNormContinuousMonoidHom_apply _root_.IdeleGroup.infinitePlaceIdeleContinuous_apply _root_.IdeleGroup.infinitePlaceIdele_finiteComponent _root_.IdeleGroup.infinitePlaceIdele_infiniteComponent_of_ne _root_.IdeleGroup.infinitePlaceIdele_infiniteComponent_same _root_.IsDiscreteValuationRing.addVal_ringEquiv _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.OAI.PrimeDegreePackets.ThetaConstruction.schwartzCM_apply _root_.RayClass.primesEquiv_val_eq_natGenerator _root_.RayClass.signToNarrow_mk _root_.finiteIdeleOfSPlaceFactors_apply_mem _root_.finiteIdeleOfSPlaceFactors_apply_notMem _root_.ideleSupportedAtEquivSPlaceFactors_infinite _root_.ideleSupportedAtEquivSPlaceFactors_inside _root_.ideleSupportedAtEquivSPlaceFactors_outside_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

/-!
# A sufficiently large finite set of places

Finiteness of the ordinary ideal
class group lets us choose one idele representing each ideal class.  The
union of the (finite) supports of those representatives is a finite set
`S` for which

`I_K = I_K^S Kˣ`.
-/

open scoped NumberField
open NumberField IsDedekindDomain

noncomputable section


variable {K : Type*} [Field K] [NumberField K]

namespace IdeleGroup

theorem classRepresentative_mem_support
    (c : ClassGroup (𝓞 K)) :
    classRepresentative (K := K) c ∈
      supportedAt (K := K)
        (classRepresentativeSupport (K := K) c : Set _) :=
  Classical.choose_spec
    (exists_finset_supportedAt
      (classRepresentative (K := K) c))

theorem classRepresentative_mem_sufficientlyLarge
    (c : ClassGroup (𝓞 K)) :
    classRepresentative (K := K) c ∈
      supportedAt (K := K)
        (sufficientlyLargeFiniteSet (K := K) : Set _) := by
  classical
  apply supportedAt_mono
    (S := (classRepresentativeSupport (K := K) c : Set _))
  · intro v hv
    exact Finset.mem_biUnion.mpr
      ⟨c, Finset.mem_univ c, hv⟩
  · exact classRepresentative_mem_support (K := K) c

/-- The ideles supported at `sufficientlyLargeFiniteSet` already map
surjectively to the ordinary ideal class group. -/
theorem idealClass_surjective_on_sufficientlyLarge :
    ∀ c : ClassGroup (𝓞 K),
      ∃ a ∈ supportedAt (K := K)
          (sufficientlyLargeFiniteSet (K := K) : Set _),
        idealClass a = c := by
  intro c
  exact ⟨classRepresentative (K := K) c,
    classRepresentative_mem_sufficientlyLarge (K := K) c,
    idealClass_classRepresentative (K := K) c⟩

/-- For a sufficiently large finite set `S` of
finite places, every idele is the product of an idele integral away from
`S` and a principal idele. -/
theorem supportedAt_sup_principalSubgroup_eq_top :
    supportedAt (K := K)
        (sufficientlyLargeFiniteSet (K := K) : Set _) ⊔
      principalSubgroup K = ⊤ := by
  let S : Set (HeightOneSpectrum (𝓞 K)) :=
    (sufficientlyLargeFiniteSet (K := K) : Set _)
  have hintegral :
      integralAtFinitePlaces (K := K) ≤ supportedAt (K := K) S := by
    rw [← supportedAt_empty (K := K)]
    exact supportedAt_mono (K := K) (Set.empty_subset S)
  have hkernel :
      (idealClass (K := K)).ker ≤
        supportedAt (K := K) S ⊔ principalSubgroup K := by
    rw [← ordinaryIdealClassSubgroup_eq_ker (K := K)]
    exact sup_le
      (hintegral.trans le_sup_left)
      le_sup_right
  apply top_unique
  intro a _
  obtain ⟨r, hrS, hr⟩ :=
    idealClass_surjective_on_sufficientlyLarge
      (K := K) (idealClass a)
  have hquot : a * r⁻¹ ∈ (idealClass (K := K)).ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, hr]
    simp
  have hquot' :
      a * r⁻¹ ∈ supportedAt (K := K) S ⊔ principalSubgroup K :=
    hkernel hquot
  have hr' :
      r ∈ supportedAt (K := K) S ⊔ principalSubgroup K :=
    Subgroup.mem_sup_left hrS
  convert Subgroup.mul_mem _ hquot' hr' using 1
  all_goals try with_reducible_and_instances rfl
  group

end IdeleGroup
end
end

section
-- module Solutions.OAIQ244_DUKE.AlgebraicNumberTheory_Idele_Cohomology_SupportedBridge
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.GlobalClassFields.ConductorialSubgroup.finiteIndex _root_.GlobalClassFieldTheory.GlobalClassFields.bigHilbertClassFieldNormSubgroup_normal _root_.GlobalClassFieldTheory.GlobalClassFields.smallHilbertClassFieldNormSubgroupFiniteIndex _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalClassFieldTheory.finiteGaloisLocalField_integerRing_moduleFinite _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.residueFieldZModAlgebra _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedIntegralAlgebraContextValuationSubringAlgebra _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.LubinTate.padicCompletedLevelField_algebra _root_.LubinTate.padicCompletedUnramifiedFieldAlgebra _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.LocalClassFieldTheory.comparisonIntegerRingIsIntegralClosure _root_.LocalClassFieldTheory.normalizationIntegerRingIsIntegralClosure _root_.chosenFinitePlaceCompletionAlgebra
attribute [-simp] _root_.GlobalClassFieldTheory.ClassFieldAxiom.actualPushoutNormQuotientMap_mk _root_.GlobalClassFieldTheory.ClassFieldAxiom.hasseNormDiagonal_mk _root_.GlobalClassFieldTheory.ClassFieldAxiom.sUnitEquivSupportedPrincipalIdeleSubgroup_coe _root_.GlobalClassFieldTheory.Cohomology.logPlaceOrbitBelowRelativeUnrestrictedIndex_mk _root_.GlobalClassFieldTheory.GlobalClassFields.ConductorialSubgroup.ideleClassQuotientEquivOfNarrowFiniteConductorsEqOfRayClassGroupCardsEqQuotientCards_mk _root_.GlobalClassFieldTheory.GlobalClassFields.ConductorialSubgroup.mem_fullConductorInfinitePart_iff _root_.GlobalClassFieldTheory.GlobalClassFields.ConductorialSubgroup.narrowFiniteConductorRayClassGroupEquivQuotientOfCardEq_mk _root_.GlobalClassFieldTheory.GlobalClassFields.ConductorialSubgroup.narrowFiniteConductorRayClassGroupToQuotient_mk _root_.GlobalClassFieldTheory.GlobalClassFields.bigHilbertClassFieldQuotientEquivNarrowClassGroup_mk _root_.GlobalClassFieldTheory.GlobalClassFields.bigHilbertClassFieldQuotientToSmallHilbertClassFieldQuotient_mk _root_.GlobalClassFieldTheory.GlobalClassFields.realSignToBigHilbertClassFieldQuotient_apply _root_.GlobalClassFieldTheory.GlobalClassFields.realSignToNarrowClassKernel_apply _root_.GlobalClassFieldTheory.GlobalClassFields.smallHilbertClassFieldQuotientEquivClassGroup_mk _root_.GlobalClassFieldTheory.Reciprocity.globalNormClassFromIdele_principalIdele _root_.GlobalClassFieldTheory.Reciprocity.infinitePlaceGlobalArtinMonoidHom_finitePlaceIdele _root_.IdeleGroup.finitePlaceIdele_finiteComponent_of_ne _root_.IdeleGroup.finitePlaceIdele_finiteComponent_same _root_.IdeleGroup.finitePlaceIdele_infiniteComponent _root_.IdeleGroup.ideleNormContinuousMonoidHom_apply _root_.IdeleGroup.infinitePlaceIdeleContinuous_apply _root_.IdeleGroup.infinitePlaceIdele_finiteComponent _root_.IdeleGroup.infinitePlaceIdele_infiniteComponent_of_ne _root_.IdeleGroup.infinitePlaceIdele_infiniteComponent_same _root_.IsDiscreteValuationRing.addVal_ringEquiv _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.OAI.PrimeDegreePackets.ThetaConstruction.schwartzCM_apply _root_.RayClass.primesEquiv_val_eq_natGenerator _root_.RayClass.signToNarrow_mk _root_.RelativeIdeleGroup.relativeFinitePlaceIdele_finiteComponent_of_ne _root_.RelativeIdeleGroup.relativeFinitePlaceIdele_finiteComponent_same _root_.RelativeIdeleGroup.relativeFinitePlaceIdele_infiniteComponent _root_.RelativeIdeleGroup.relativeInfinitePlaceIdele_finiteComponent _root_.RelativeIdeleGroup.relativeInfinitePlaceIdele_infiniteComponent_of_ne _root_.RelativeIdeleGroup.relativeInfinitePlaceIdele_infiniteComponent_same
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

/-!
# A sufficiently large unramified support for the idele-class calculation

This file constructs the finite set used in the idele-class Herbrand calculation.  It
contains the contractions of a sufficiently large set of places of `L`
and every finite place of `K` at which some place of `L` ramifies.

It also compares the concrete tensor-coordinate supported subgroup of
relative ideles with the ordinary supported idele subgroup of `L`.
-/

open scoped Classical NumberField TensorProduct
open NumberField IsDedekindDomain

noncomputable section


variable
    {K L : Type}
    [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]

omit [IsGalois K L] in
/-- Subgroup-level form of
`relativeIdeleBaseChange_mem_supportedAt_iff`. -/
theorem relativeIdeleLocalTensorDecompositionSupportedSubgroup_map_baseChange
    (S : Finset (HeightOneSpectrum (𝓞 K))) :
    (relativeIdeleLocalTensorDecompositionSupportedSubgroup
        (K := K) (L := L) S).map
      (relativeIdeleBaseChangeMulEquiv
        (K := K) (L := L)).toMonoidHom =
      IdeleGroup.supportedAt (K := L)
        (finitePlacesAbove (K := K) (L := L) S : Set _) := by
  ext y
  constructor
  · rintro ⟨z, hz, rfl⟩
    exact
      (relativeIdeleBaseChange_mem_supportedAt_iff
        (K := K) (L := L) S z).1 hz
  · intro hy
    refine ⟨(relativeIdeleBaseChangeMulEquiv
      (K := K) (L := L)).symm y, ?_, ?_⟩
    · apply
        (relativeIdeleBaseChange_mem_supportedAt_iff
          (K := K) (L := L) S _).2
      simpa using hy
    · exact
        (relativeIdeleBaseChangeMulEquiv
          (K := K) (L := L)).apply_symm_apply y

omit [IsGalois K L] in
/-- If the supported ordinary ideles and principal ideles generate
`I_L`, then their relative counterparts generate the full relative
idele group. -/
theorem relativeIdeleSupported_sup_principal_eq_top
    (S : Finset (HeightOneSpectrum (𝓞 K)))
    (hOrdinary :
      IdeleGroup.supportedAt (K := L)
          (finitePlacesAbove (K := K) (L := L) S : Set _) ⊔
        IdeleGroup.principalSubgroup L = ⊤) :
    relativeIdeleLocalTensorDecompositionSupportedSubgroup
          (K := K) (L := L) S ⊔
        RelativeIdeleGroup.principalSubgroup K L =
  ⊤ := by
  apply
    Subgroup.map_injective
      (f :=
        (relativeIdeleBaseChangeMulEquiv
          (K := K) (L := L)).toMonoidHom)
      (relativeIdeleBaseChangeMulEquiv
          (K := K) (L := L)).injective
  rw [Subgroup.map_sup,
    relativeIdeleLocalTensorDecompositionSupportedSubgroup_map_baseChange,
    relativeIdelePrincipalSubgroup_map_baseChange,
    hOrdinary,
    Subgroup.map_top_of_surjective
      (relativeIdeleBaseChangeMulEquiv
        (K := K) (L := L)).toMonoidHom
      (relativeIdeleBaseChangeMulEquiv
        (K := K) (L := L)).surjective]

omit [FiniteDimensional K L] [IsGalois K L] in
/-- Every place in the sufficiently large support of `L` lies above
the chosen base support. -/
theorem sufficientlyLargeFiniteSet_subset_finitePlacesAbove_support :
    (IdeleGroup.sufficientlyLargeFiniteSet (K := L) :
        Set (HeightOneSpectrum (𝓞 L))) ⊆
      ((finitePlacesAbove
          (K := K) (L := L)
          (ideleClassHerbrandSupport (K := K) (L := L)) :
            Finset (HeightOneSpectrum (𝓞 L))) :
        Set (HeightOneSpectrum (𝓞 L))) := by
  intro W hW
  change W ∈ finitePlacesAbove
    (K := K) (L := L)
    (ideleClassHerbrandSupport (K := K) (L := L))
  rw [mem_finitePlacesAbove_iff]
  apply Finset.mem_union_left
  exact Finset.mem_image.mpr ⟨W, hW, rfl⟩

omit [FiniteDimensional K L] [IsGalois K L] in
/-- The ordinary ideles supported above the chosen base support,
together with principal ideles, generate all of `I_L`. -/
theorem supportedAboveHerbrandSupport_sup_principal_eq_top :
    IdeleGroup.supportedAt (K := L)
        (finitePlacesAbove
          (K := K) (L := L)
          (ideleClassHerbrandSupport (K := K) (L := L)) : Set _) ⊔
      IdeleGroup.principalSubgroup L = ⊤ := by
  apply top_unique
  rw [← IdeleGroup.supportedAt_sup_principalSubgroup_eq_top
    (K := L)]
  exact sup_le_sup
    (IdeleGroup.supportedAt_mono
      (sufficientlyLargeFiniteSet_subset_finitePlacesAbove_support
      (K := K) (L := L)))
    le_rfl

omit [IsGalois K L] in
/-- The relative ideles supported at the Herbrand support, together
with the relative principal ideles, generate the full relative idele
group. -/
theorem relativeSupportedAboveHerbrandSupport_sup_principal_eq_top :
    relativeIdeleLocalTensorDecompositionSupportedSubgroup
          (K := K) (L := L)
          (ideleClassHerbrandSupport (K := K) (L := L)) ⊔
        RelativeIdeleGroup.principalSubgroup K L =
      ⊤ :=
  relativeIdeleSupported_sup_principal_eq_top
    (K := K) (L := L)
    (ideleClassHerbrandSupport (K := K) (L := L))
    (supportedAboveHerbrandSupport_sup_principal_eq_top
      (K := K) (L := L))

omit [FiniteDimensional K L] [IsGalois K L] in
/-- Outside the chosen base support, every finite place of `L` is
algebraically unramified over `K`. -/
theorem isUnramifiedAt_of_notMem_ideleClassHerbrandSupport
    (v : HeightOneSpectrum (𝓞 K))
    (hv :
      v ∉ ideleClassHerbrandSupport (K := K) (L := L))
    (W : HeightOneSpectrum (𝓞 L))
    (hW : finitePlaceBelow (K := K) W = v) :
    Algebra.IsUnramifiedAt (𝓞 K) W.asIdeal := by
  classical
  by_contra hram
  apply hv
  apply Finset.mem_union_right
  rw [mem_ramifiedBaseFinitePlaces_iff]
  refine ⟨W, ?_, hram⟩
  exact ⟨(congrArg HeightOneSpectrum.asIdeal hW).symm⟩
end
end

section
-- module Solutions.OAIQ244_DUKE.GlobalClassFieldTheory_ClassFieldAxiom_KummerLocalNormContainment
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalClassFieldTheory.finiteGaloisLocalField_integerRing_moduleFinite _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LubinTate.padicCompletedLevelField_algebra _root_.LubinTate.padicCompletedUnramifiedFieldAlgebra _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.CyclicCohomology.binaryCoefficientFamilyCommGroup _root_.LocalClassFieldTheory.comparisonIntegerRingIsIntegralClosure _root_.LocalClassFieldTheory.normalizationIntegerRingIsIntegralClosure _root_.relativeUnrestrictedSPlaceFactorCommGroup
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI
attribute [local instance] OAI.starSubalgebraCommCStarAlgebra

set_option autoImplicit false

/-!
# Local norm containment for Kummer extensions

This module proves that local powers, and then the concrete simple-Kummer
power subgroup, lie in the norm subgroup at a chosen finite place.
-/

open scoped NumberField Classical NNReal IsMulCommutative
open NumberField IsDedekindDomain
open AlgebraicNumberTheory.Valuations
open HilbertRamification
open KummerTheory
open LocalFieldTheory

noncomputable section

namespace GlobalClassFieldTheory.ClassFieldAxiom

variable {K : Type*} [Field K] [NumberField K]

/-- Local `n`-th powers are norms from the chosen finite-place
completion when the global Galois group has exponent dividing `n`. -/
theorem nthPowerSubgroup_le_chosenFinitePlaceLocalNormSubgroup
    {K L : Type}
    [Field K] [NumberField K]
    [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    (n : ℕ+) (r : ℕ)
    (eG :
      (L ≃ₐ[K] L) ≃*
        (Fin r → Multiplicative (ZMod (n : ℕ))))
    (v : HeightOneSpectrum (𝓞 K)) :
    (powMonoidHom (n : ℕ) :
        (v.adicCompletion K)ˣ →*
          (v.adicCompletion K)ˣ).range ≤
      _root_.chosenFinitePlaceLocalNormSubgroup
        (K := K) (L := L) v := by
  exact
    nthPowerSubgroup_le_chosenFinitePlaceLocalNormSubgroup_of_galois_pow_eq_one
      (K := K) (L := L) n
      (galois_pow_eq_one_of_field_equiv_pi_zmod n r eG) v


end GlobalClassFieldTheory.ClassFieldAxiom
end
end

section
-- module Solutions.OAIQ244_DUKE.GlobalClassFieldTheory_Cohomology_IdeleClassHerbrandSupportedFinal
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 400000
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.GlobalClassFields.ConductorialSubgroup.finiteIndex _root_.GlobalClassFieldTheory.GlobalClassFields.bigHilbertClassFieldNormSubgroup_normal _root_.GlobalClassFieldTheory.GlobalClassFields.smallHilbertClassFieldNormSubgroupFiniteIndex _root_.GlobalClassFieldTheory.Reciprocity.rationalCyclotomicCompletionAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalCyclotomicLocalizedCompletionFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalCyclotomicLocalizedCompletionIsAlgebraic _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.DiscreteNthRootsSubgroup.instCommGroupSubtypeUnitsMemSubgroup _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.KummerTheory.finite_sUnit_nthPowerQuotient _root_.KummerTheory.nthRootsSubgroupFintype _root_.KummerTheory.primeCyclotomicBaseFiniteDimensional _root_.LocalClassFieldTheory.finiteGaloisLocalField_integerRing_moduleFinite _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitQuotientCarrier_finite _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.residueFieldZModAlgebra _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedIntegralAlgebraContextValuationSubringAlgebra _root_.LocalFieldTheory.DiscreteValuationField.finite_nsmulAddKernel_padicInt_pi _root_.LocalFieldTheory.DiscreteValuationField.finite_principalUnits_nthPowerKernel _root_.LocalFieldTheory.DiscreteValuationField.finite_residueRootsOfUnityGroup _root_.LocalFieldTheory.DiscreteValuationField.finite_valuationSubringUnits_nthPowerKernel _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.Padic.padicUnitFiniteFactor_finite _root_.LocalFieldTheory.finite_multiplicative_nthPowerKernel _root_.LocalFieldTheory.finite_nsmulAddKernel_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.LubinTate.compatibleGroupFamiliesCommGroup _root_.LubinTate.compatibleGroupFamiliesGroup _root_.LubinTate.padicCompletedLevelField_algebra _root_.LubinTate.padicCompletedLevelField_finiteDimensional _root_.LubinTate.padicCompletedUnramifiedFieldAlgebra _root_.LubinTate.standardLubinTateLevelField_galFinite _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.boundedRealFields_finite _root_.OAI.PrimeDegreePackets.instNonemptyLeafTestSpace _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.LocalClassFieldTheory.comparisonIntegerRingIsIntegralClosure _root_.LocalClassFieldTheory.normalizationIntegerRingIsIntegralClosure
attribute [-simp] _root_.GlobalClassFieldTheory.ClassFieldAxiom.actualPushoutNormQuotientMap_mk _root_.GlobalClassFieldTheory.ClassFieldAxiom.hasseNormDiagonal_mk _root_.GlobalClassFieldTheory.ClassFieldAxiom.sUnitEquivSupportedPrincipalIdeleSubgroup_coe _root_.GlobalClassFieldTheory.GlobalClassFields.ConductorialSubgroup.ideleClassQuotientEquivOfNarrowFiniteConductorsEqOfRayClassGroupCardsEqQuotientCards_mk _root_.GlobalClassFieldTheory.GlobalClassFields.ConductorialSubgroup.mem_fullConductorInfinitePart_iff _root_.GlobalClassFieldTheory.GlobalClassFields.ConductorialSubgroup.narrowFiniteConductorRayClassGroupEquivQuotientOfCardEq_mk _root_.GlobalClassFieldTheory.GlobalClassFields.ConductorialSubgroup.narrowFiniteConductorRayClassGroupToQuotient_mk _root_.GlobalClassFieldTheory.GlobalClassFields.bigHilbertClassFieldQuotientEquivNarrowClassGroup_mk _root_.GlobalClassFieldTheory.GlobalClassFields.bigHilbertClassFieldQuotientToSmallHilbertClassFieldQuotient_mk _root_.GlobalClassFieldTheory.GlobalClassFields.realSignToBigHilbertClassFieldQuotient_apply _root_.GlobalClassFieldTheory.GlobalClassFields.realSignToNarrowClassKernel_apply _root_.GlobalClassFieldTheory.GlobalClassFields.smallHilbertClassFieldQuotientEquivClassGroup_mk _root_.GlobalClassFieldTheory.Reciprocity.globalNormClassFromIdele_principalIdele _root_.GlobalClassFieldTheory.Reciprocity.infinitePlaceGlobalArtinMonoidHom_finitePlaceIdele _root_.GlobalClassFieldTheory.Reciprocity.rationalCyclotomicGlobalToLocalizedAlgHom_apply _root_.GlobalClassFieldTheory.Reciprocity.rationalCyclotomicGlobalToLocalizedAlgHom_primitiveRoot _root_.IdeleGroup.finitePlaceIdele_finiteComponent_of_ne _root_.IdeleGroup.finitePlaceIdele_finiteComponent_same _root_.IdeleGroup.finitePlaceIdele_infiniteComponent _root_.IdeleGroup.ideleNormContinuousMonoidHom_apply _root_.IdeleGroup.infinitePlaceIdeleContinuous_apply _root_.IdeleGroup.infinitePlaceIdele_finiteComponent _root_.IdeleGroup.infinitePlaceIdele_infiniteComponent_of_ne _root_.IdeleGroup.infinitePlaceIdele_infiniteComponent_same _root_.IsDiscreteValuationRing.addVal_ringEquiv _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.KummerTheory.mem_sUnitFiniteKummerRadical_iff _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.OAI.PrimeDegreePackets.ThetaConstruction.schwartzCM_apply _root_.RayClass.primesEquiv_val_eq_natGenerator _root_.RayClass.signToNarrow_mk _root_.RelativeIdeleGroup.relativeFinitePlaceIdele_finiteComponent_of_ne _root_.RelativeIdeleGroup.relativeFinitePlaceIdele_finiteComponent_same _root_.RelativeIdeleGroup.relativeFinitePlaceIdele_infiniteComponent _root_.RelativeIdeleGroup.relativeInfinitePlaceIdele_finiteComponent _root_.RelativeIdeleGroup.relativeInfinitePlaceIdele_infiniteComponent_of_ne _root_.RelativeIdeleGroup.relativeInfinitePlaceIdele_infiniteComponent_same _root_.doubleCosetExtension_mk _root_.extendAbsoluteValueExtensionFromIntermediate_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

/-!
# Supported ideles and the idele-class norm index

This file joins the unrestricted local calculation, the vanishing of
the unramified integral factors outside the support, and the exact
sequence from `S`-units to supported ideles and idele classes.
-/

open scoped Classical NumberField TensorProduct
open NumberField IsDedekindDomain

noncomputable section

open RelativeIdeleGroup.Cohomology

namespace GlobalClassFieldTheory
namespace Cohomology

open CyclicCohomology.ProfiniteCohomology.Herbrand
open CyclicCohomology
open AlgebraicNumberTheory.Valuations
open HilbertRamification
open LocalClassFieldTheory

variable
    {K L : Type}
    [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]

/-- Outside the canonical Herbrand support, the chosen completed local
extension is unramified. -/
theorem
    chosenFinitePlaceIsUnramified_of_notMem_ideleClassHerbrandSupport
    (v : HeightOneSpectrum (𝓞 K))
    (hv :
      v ∉ ideleClassHerbrandSupport (K := K) (L := L)) :
    ChosenFinitePlaceIsUnramified
      (K := K) (L := L) v := by
  apply chosenFinitePlaceIsUnramified_of_isUnramifiedAt
    (K := K) (L := L) v
  apply isUnramifiedAt_of_notMem_ideleClassHerbrandSupport
    (K := K) (L := L) v hv
  exact
    finitePlaceBelow_finitePlaceExtensionCentre
      (K := K) (L := L) v
      (chosenFinitePlaceExtension (L := L) v)

omit [NumberField L] in
/-- If every chosen finite extension outside `S` is unramified, both
low-degree Tate cohomology groups of the product of its integral
factors are singletons. -/
theorem
    relativeOutsideSPlaceFactors_unramifiedHerbrand_subsingleton
    (S : Finset (HeightOneSpectrum (𝓞 K)))
    (σ : L ≃ₐ[K] L)
    (hgen : ∀ τ : L ≃ₐ[K] L,
      τ ∈ Subgroup.zpowers σ)
    (hUnram : ∀ w : HeightOneSpectrum (𝓞 K),
      w ∉ S →
        ChosenFinitePlaceIsUnramified
          (K := K) (L := L) w) :
    letI :=
      relativeOutsideSPlaceFactorsAction
        (K := K) (L := L) S
    Subsingleton
        (HerbrandH0 (L ≃ₐ[K] L)
          (RelativeOutsideSPlaceFactors
            (K := K) (L := L) S)) ∧
      Subsingleton
        (HerbrandHMinusOne (L ≃ₐ[K] L)
          (RelativeOutsideSPlaceFactors
            (K := K) (L := L) S) σ) := by
  let componentAction :
      ∀ w : {w : HeightOneSpectrum (𝓞 K) // w ∉ S},
        MulDistribMulAction (L ≃ₐ[K] L)
          (relativeLocalTensorDecompositionIntegralUnitSubgroup
            (K := K) (L := L) w.1) :=
    fun w =>
      relativeLocalTensorDecompositionIntegralUnitSubgroupAction
        (K := K) (L := L) w.1
  let outsideAction :=
    relativeOutsideSPlaceFactorsAction
      (K := K) (L := L) S
  let e0 :
      HerbrandH0 (L ≃ₐ[K] L)
          (RelativeOutsideSPlaceFactors
            (K := K) (L := L) S) ≃*
        ∀ w : {w : HeightOneSpectrum (𝓞 K) // w ∉ S},
          HerbrandH0 (L ≃ₐ[K] L)
            (relativeLocalTensorDecompositionIntegralUnitSubgroup
              (K := K) (L := L) w.1) :=
    herbrandH0PiEquiv
      (G := L ≃ₐ[K] L)
      (fun w : {w : HeightOneSpectrum (𝓞 K) // w ∉ S} =>
        relativeLocalTensorDecompositionIntegralUnitSubgroup
          (K := K) (L := L) w.1)
  let em :
      HerbrandHMinusOne (L ≃ₐ[K] L)
          (RelativeOutsideSPlaceFactors
            (K := K) (L := L) S) σ ≃*
        ∀ w : {w : HeightOneSpectrum (𝓞 K) // w ∉ S},
          HerbrandHMinusOne (L ≃ₐ[K] L)
            (relativeLocalTensorDecompositionIntegralUnitSubgroup
              (K := K) (L := L) w.1) σ :=
    herbrandHMinusOnePiEquiv
      (G := L ≃ₐ[K] L)
      (fun w : {w : HeightOneSpectrum (𝓞 K) // w ∉ S} =>
        relativeLocalTensorDecompositionIntegralUnitSubgroup
          (K := K) (L := L) w.1) σ
  constructor
  · constructor
    intro x y
    apply e0.injective
    funext w
    let :
        Subsingleton
          (HerbrandH0 (L ≃ₐ[K] L)
            (relativeLocalTensorDecompositionIntegralUnitSubgroup
              (K := K) (L := L) w.1)) :=
      relativeLocalTensorDecompositionIntegralUnitSubgroup_unramifiedHerbrandH0_subsingleton
        (K := K) (L := L) w.1 σ hgen (hUnram w.1 w.2)
    exact Subsingleton.elim _ _
  · constructor
    intro x y
    apply em.injective
    funext w
    let :
        Subsingleton
          (HerbrandHMinusOne (L ≃ₐ[K] L)
            (relativeLocalTensorDecompositionIntegralUnitSubgroup
              (K := K) (L := L) w.1) σ) :=
      relativeLocalTensorDecompositionIntegralUnitSubgroup_unramifiedHerbrandHMinusOne_subsingleton
        (K := K) (L := L) w.1 σ hgen (hUnram w.1 w.2)
    exact Subsingleton.elim _ _

omit [NumberField L] in
/-- The product of integral factors outside an unramified support has
Herbrand quotient one. -/
theorem
    relativeOutsideSPlaceFactors_unramifiedHerbrandQuotient_eq_one
    (S : Finset (HeightOneSpectrum (𝓞 K)))
    (σ : L ≃ₐ[K] L)
    (hgen : ∀ τ : L ≃ₐ[K] L,
      τ ∈ Subgroup.zpowers σ)
    (hUnram : ∀ w : HeightOneSpectrum (𝓞 K),
      w ∉ S →
        ChosenFinitePlaceIsUnramified
          (K := K) (L := L) w) :
    letI :=
      relativeOutsideSPlaceFactorsAction
        (K := K) (L := L) S
    ∃ h :
        HerbrandQuotientDefined
          (L ≃ₐ[K] L)
          (RelativeOutsideSPlaceFactors
            (K := K) (L := L) S) σ,
      @herbrandQuotient
          (L ≃ₐ[K] L)
          (RelativeOutsideSPlaceFactors
            (K := K) (L := L) S)
          _ _ _ _ σ h.1 h.2 = 1 := by
  let outsideAction :=
    relativeOutsideSPlaceFactorsAction
      (K := K) (L := L) S
  have hsub :=
    relativeOutsideSPlaceFactors_unramifiedHerbrand_subsingleton
      (K := K) (L := L) S σ hgen hUnram
  let h0Subsingleton := hsub.1
  let hmSubsingleton := hsub.2
  let h :
      HerbrandQuotientDefined
        (L ≃ₐ[K] L)
        (RelativeOutsideSPlaceFactors
          (K := K) (L := L) S) σ :=
    ⟨Finite.of_subsingleton, Finite.of_subsingleton⟩
  refine ⟨h, ?_⟩
  let h0Finite := h.1
  let hmFinite := h.2
  let : Inhabited
      (HerbrandH0 (L ≃ₐ[K] L)
        (RelativeOutsideSPlaceFactors
          (K := K) (L := L) S)) :=
    ⟨1⟩
  let : Inhabited
      (HerbrandHMinusOne (L ≃ₐ[K] L)
        (RelativeOutsideSPlaceFactors
          (K := K) (L := L) S) σ) :=
    ⟨1⟩
  let : Unique
      (HerbrandH0 (L ≃ₐ[K] L)
        (RelativeOutsideSPlaceFactors
          (K := K) (L := L) S)) :=
    Unique.mk' _
  let : Unique
      (HerbrandHMinusOne (L ≃ₐ[K] L)
        (RelativeOutsideSPlaceFactors
          (K := K) (L := L) S) σ) :=
    Unique.mk' _
  rw [herbrandQuotient_eq_card_ratio,
    Nat.card_unique,
    Nat.card_unique]
  norm_num

/-- After the unramified outside factors have been removed, the supported
relative ideles have Herbrand quotient equal to the product of the local
degrees at the unrestricted factors. -/
theorem
    relativeIdeleSupported_herbrandQuotient_eq_localDegreeProduct
    (S : Finset (HeightOneSpectrum (𝓞 K)))
    (σ : L ≃ₐ[K] L)
    (hgen : ∀ τ : L ≃ₐ[K] L,
      τ ∈ Subgroup.zpowers σ)
    (hUnram : ∀ w : HeightOneSpectrum (𝓞 K),
      w ∉ S →
        ChosenFinitePlaceIsUnramified
          (K := K) (L := L) w) :
    letI :=
      relativeIdeleLocalTensorDecompositionSupportedSubgroupAction
        (K := K) (L := L) S
    ∃ h :
        HerbrandQuotientDefined
          (L ≃ₐ[K] L)
          (relativeIdeleLocalTensorDecompositionSupportedSubgroup
            (K := K) (L := L) S) σ,
      @herbrandQuotient
          (L ≃ₐ[K] L)
          (relativeIdeleLocalTensorDecompositionSupportedSubgroup
            (K := K) (L := L) S)
          _ _ _ _ σ h.1 h.2 =
        ∏ i,
          (relativeUnrestrictedSPlaceLocalDegree
            (K := K) (L := L) S i : ℚ) := by
  let supportedAction :=
    relativeIdeleLocalTensorDecompositionSupportedSubgroupAction
      (K := K) (L := L) S
  let unrestrictedAction :=
    relativeUnrestrictedSPlaceFactorsAction
      (K := K) (L := L) S
  let outsideAction :=
    relativeOutsideSPlaceFactorsAction
      (K := K) (L := L) S
  let hU :
      HerbrandQuotientDefined
        (L ≃ₐ[K] L)
        (RelativeUnrestrictedSPlaceFactors
          (K := K) (L := L) S) σ :=
    ⟨relativeUnrestrictedSPlaceFactorsHerbrandH0Finite
        S σ hgen,
      relativeUnrestrictedSPlaceFactorsHerbrandHMinusOneFinite
        S σ hgen⟩
  obtain ⟨hO, hOq⟩ :=
    relativeOutsideSPlaceFactors_unramifiedHerbrandQuotient_eq_one
      (K := K) (L := L) S σ hgen hUnram
  let hU0 := hU.1
  let hUm := hU.2
  let hO0 := hO.1
  let hOm := hO.2
  let hProd0 :
      Finite
        (HerbrandH0 (L ≃ₐ[K] L)
          (RelativeUnrestrictedSPlaceFactors
              (K := K) (L := L) S ×
            RelativeOutsideSPlaceFactors
              (K := K) (L := L) S)) :=
    herbrandH0ProdFinite _ _
  let hProdm :
      Finite
        (HerbrandHMinusOne (L ≃ₐ[K] L)
          (RelativeUnrestrictedSPlaceFactors
              (K := K) (L := L) S ×
            RelativeOutsideSPlaceFactors
              (K := K) (L := L) S) σ) :=
    herbrandHMinusOneProdFinite _ _ σ
  let e0 :
      HerbrandH0 (L ≃ₐ[K] L)
          (relativeIdeleLocalTensorDecompositionSupportedSubgroup
            (K := K) (L := L) S) ≃*
        HerbrandH0 (L ≃ₐ[K] L)
          (RelativeUnrestrictedSPlaceFactors
              (K := K) (L := L) S ×
            RelativeOutsideSPlaceFactors
              (K := K) (L := L) S) :=
    relativeIdeleSupportedHerbrandH0EquivUnrestrictedProdOutside
      (K := K) (L := L) S
  let em :
      HerbrandHMinusOne (L ≃ₐ[K] L)
          (relativeIdeleLocalTensorDecompositionSupportedSubgroup
            (K := K) (L := L) S) σ ≃*
        HerbrandHMinusOne (L ≃ₐ[K] L)
          (RelativeUnrestrictedSPlaceFactors
              (K := K) (L := L) S ×
            RelativeOutsideSPlaceFactors
              (K := K) (L := L) S) σ :=
    relativeIdeleSupportedHerbrandHMinusOneEquivUnrestrictedProdOutside
      (K := K) (L := L) S σ
  let hSupported :
      HerbrandQuotientDefined
        (L ≃ₐ[K] L)
        (relativeIdeleLocalTensorDecompositionSupportedSubgroup
          (K := K) (L := L) S) σ :=
    ⟨Finite.of_equiv _ e0.symm.toEquiv,
      Finite.of_equiv _ em.symm.toEquiv⟩
  refine ⟨hSupported, ?_⟩
  let hS0 := hSupported.1
  let hSm := hSupported.2
  calc
    @herbrandQuotient
          (L ≃ₐ[K] L)
          (relativeIdeleLocalTensorDecompositionSupportedSubgroup
            (K := K) (L := L) S)
          _ _ _ _ σ hSupported.1 hSupported.2 =
        herbrandQuotient
          (G := L ≃ₐ[K] L)
          (A :=
            RelativeUnrestrictedSPlaceFactors
                (K := K) (L := L) S ×
              RelativeOutsideSPlaceFactors
                (K := K) (L := L) S) σ :=
      herbrandQuotient_eq_of_equivariantMulEquiv
        (relativeIdeleSupportedEquivUnrestrictedProdOutside
          (K := K) (L := L) S)
        (relativeIdeleSupportedEquivUnrestrictedProdOutside_smul
          (K := K) (L := L) S) σ
    _ =
        herbrandQuotient
            (G := L ≃ₐ[K] L)
            (A := RelativeUnrestrictedSPlaceFactors
              (K := K) (L := L) S) σ *
          herbrandQuotient
            (G := L ≃ₐ[K] L)
            (A := RelativeOutsideSPlaceFactors
              (K := K) (L := L) S) σ :=
      herbrandQuotient_prod _ _ σ
    _ =
        (∏ i,
          (relativeUnrestrictedSPlaceLocalDegree
            (K := K) (L := L) S i : ℚ)) * 1 := by
      rw [
        relativeUnrestrictedSPlaceFactors_herbrandQuotient
          (K := K) (L := L) S σ hgen,
        hOq]
    _ =
        ∏ i,
          (relativeUnrestrictedSPlaceLocalDegree
            (K := K) (L := L) S i : ℚ) := mul_one _

/-- The local-degree product occurring in the supported-idele
calculation is exactly the orbit-indexed local-degree product occurring
in the `S`-unit calculation. -/
theorem
    relativeUnrestrictedSPlaceLocalDegree_product_eq_logPlaceOrbitProduct
    (S : Finset (HeightOneSpectrum (𝓞 K))) :
    letI :=
      aboveSLogPlaceMulAction
        (K := K) (L := L) S
    letI :
        Fintype
          (MulAction.orbitRel.Quotient
            (L ≃ₐ[K] L)
            (SUnitGroup.LogPlace
              (K := L)
              (finitePlacesAbove
                (K := K) (L := L) S))) :=
      Fintype.ofFinite _
    (∏ i,
        (relativeUnrestrictedSPlaceLocalDegree
          (K := K) (L := L) S i : ℚ)) =
      ∏ ω :
          MulAction.orbitRel.Quotient
            (L ≃ₐ[K] L)
            (SUnitGroup.LogPlace
              (K := L)
              (finitePlacesAbove
                (K := K) (L := L) S)),
        (logPlaceLocalDegree K L
          (finitePlacesAbove (K := K) (L := L) S)
          ω.out : ℚ) := by
  let logAction :=
    aboveSLogPlaceMulAction
      (K := K) (L := L) S
  let orbitFintype :
      Fintype
        (MulAction.orbitRel.Quotient
          (L ≃ₐ[K] L)
          (SUnitGroup.LogPlace
            (K := L)
            (finitePlacesAbove
              (K := K) (L := L) S))) :=
    Fintype.ofFinite _
  let e :=
    logPlaceOrbitEquivRelativeUnrestrictedSPlaceIndex
      (K := K) (L := L) S
  calc
    (∏ i,
        (relativeUnrestrictedSPlaceLocalDegree
          (K := K) (L := L) S i : ℚ)) =
        ∏ ω,
          (relativeUnrestrictedSPlaceLocalDegree
            (K := K) (L := L) S (e ω) : ℚ) :=
      (e.prod_comp
        (fun i =>
          (relativeUnrestrictedSPlaceLocalDegree
            (K := K) (L := L) S i : ℚ))).symm
    _ =
        ∏ ω :
          MulAction.orbitRel.Quotient
            (L ≃ₐ[K] L)
            (SUnitGroup.LogPlace
              (K := L)
              (finitePlacesAbove
                (K := K) (L := L) S)),
          (logPlaceLocalDegree K L
            (finitePlacesAbove (K := K) (L := L) S)
            ω.out : ℚ) := by
      apply Finset.prod_congr rfl
      intro ω hω
      have he :
          e ω =
            logPlaceBelowRelativeUnrestrictedIndex
              (K := K) (L := L) S ω.out := by
        calc
          e ω = e (Quotient.mk'' ω.out) :=
            congrArg e (Quotient.out_eq' ω).symm
          _ =
              logPlaceBelowRelativeUnrestrictedIndex
                (K := K) (L := L) S ω.out := rfl
      rw [he]
      exact_mod_cast
        relativeUnrestrictedSPlaceLocalDegree_logPlaceBelow
          (K := K) (L := L) S ω.out

/-- With all local and `S`-unit calculations substituted, an unramified
sufficiently large support gives an idele-class Herbrand quotient equal
to the order of the Galois group. -/
theorem
    ideleClass_herbrandQuotient_eq_card_of_supported_local_calculation
    (S : Finset (HeightOneSpectrum (𝓞 K)))
    (σ : L ≃ₐ[K] L)
    (hgen : ∀ τ : L ≃ₐ[K] L,
      τ ∈ Subgroup.zpowers σ)
    (hSP :
      relativeIdeleLocalTensorDecompositionSupportedSubgroup
            (K := K) (L := L) S ⊔
          RelativeIdeleGroup.principalSubgroup K L =
        ⊤)
    (hUnram : ∀ w : HeightOneSpectrum (𝓞 K),
      w ∉ S →
        ChosenFinitePlaceIsUnramified
          (K := K) (L := L) w) :
    letI := ideleClassMulDistribMulAction K L
    ∃ hC :
        HerbrandQuotientDefined
          (L ≃ₐ[K] L)
          (RelativeIdeleGroup.ClassGroup K L) σ,
      @herbrandQuotient
          (L ≃ₐ[K] L)
          (RelativeIdeleGroup.ClassGroup K L)
          _ _ _ _ σ hC.1 hC.2 =
        (Fintype.card (L ≃ₐ[K] L) : ℚ) := by
  let T :=
    finitePlacesAbove (K := K) (L := L) S
  let hT :
      IsGaloisStableFinitePlaces K L T :=
    finitePlacesAbove_isGaloisStable
      (K := K) (L := L) S
  let ρ :=
    logPlacePermutationHom K L T hT
  let indexAction :
      MulAction (L ≃ₐ[K] L)
        (SUnitGroup.LogPlace (K := L) T) :=
    permutationMulAction ρ
  let sUnitAction :
      MulDistribMulAction (L ≃ₐ[K] L)
        (SUnitGroup (K := L) T) :=
    sUnitMulDistribMulAction K L T hT
  let orbitFintype :
      Fintype
        (MulAction.orbitRel.Quotient
          (L ≃ₐ[K] L)
          (SUnitGroup.LogPlace (K := L) T)) :=
    Fintype.ofFinite _
  let stabilizerFintype :
      ∀ ω :
          MulAction.orbitRel.Quotient
            (L ≃ₐ[K] L)
            (SUnitGroup.LogPlace (K := L) T),
        Fintype (permutationOrbitStabilizer ω) :=
    fun _ => Fintype.ofFinite _
  obtain ⟨hUnit, hUnitValue⟩ :=
    sUnit_herbrandQuotient_eq_localDegreeProduct_div_card
      (K := K) (L := L) hT σ hgen
  let supportedAction :=
    relativeIdeleLocalTensorDecompositionSupportedSubgroupAction
      (K := K) (L := L) S
  obtain ⟨hSupported, hSupportedValue⟩ :=
    relativeIdeleSupported_herbrandQuotient_eq_localDegreeProduct
      (K := K) (L := L) S σ hgen hUnram
  let q : ℚ :=
    ∏ i,
      (relativeUnrestrictedSPlaceLocalDegree
        (K := K) (L := L) S i : ℚ)
  have hq : q ≠ 0 := by
    apply Finset.prod_ne_zero_iff.mpr
    intro i hi
    exact
      Nat.cast_ne_zero.mpr
        (show
          relativeUnrestrictedSPlaceLocalDegree
              (K := K) (L := L) S i ≠ 0 by
          unfold relativeUnrestrictedSPlaceLocalDegree
          exact Nat.card_pos.ne')
  have hProducts :
      q =
        ∏ ω :
            MulAction.orbitRel.Quotient
              (L ≃ₐ[K] L)
              (SUnitGroup.LogPlace (K := L) T),
          (logPlaceLocalDegree K L T ω.out : ℚ) := by
    simpa [q, T, hT, ρ] using
      (relativeUnrestrictedSPlaceLocalDegree_product_eq_logPlaceOrbitProduct
        (K := K) (L := L) S)
  have hUnitValue' :
      @herbrandQuotient
          (L ≃ₐ[K] L)
          (SUnitGroup (K := L) T)
          _ _ _ _ σ hUnit.1 hUnit.2 =
        q / (Fintype.card (L ≃ₐ[K] L) : ℚ) := by
    rw [hProducts]
    simpa only [indexAction, ρ, T, hT] using hUnitValue
  have hSupportedValue' :
      @herbrandQuotient
          (L ≃ₐ[K] L)
          (relativeIdeleLocalTensorDecompositionSupportedSubgroup
            (K := K) (L := L) S)
          _ _ _ _ σ hSupported.1 hSupported.2 =
        q := by
    exact hSupportedValue
  exact
    ideleClass_herbrandQuotient_eq_card_of_sUnit_supported_values
      (K := K) (L := L) S σ hgen hSP
      hUnit hSupported q hq
      hSupportedValue' hUnitValue'

/-- The corresponding norm-index lower bound with all supported local
calculations substituted. -/
theorem
    card_le_ideleClassNorm_index_of_supported_local_calculation
    (S : Finset (HeightOneSpectrum (𝓞 K)))
    (σ : L ≃ₐ[K] L)
    (hgen : ∀ τ : L ≃ₐ[K] L,
      τ ∈ Subgroup.zpowers σ)
    (hSP :
      relativeIdeleLocalTensorDecompositionSupportedSubgroup
            (K := K) (L := L) S ⊔
          RelativeIdeleGroup.principalSubgroup K L =
        ⊤)
    (hUnram : ∀ w : HeightOneSpectrum (𝓞 K),
      w ∉ S →
        ChosenFinitePlaceIsUnramified
          (K := K) (L := L) w) :
    Fintype.card (L ≃ₐ[K] L) ≤
      (RelativeIdeleGroup.Cohomology.ideleClassNorm K L).range.index := by
  let classAction := ideleClassMulDistribMulAction K L
  obtain ⟨hC, hCvalue⟩ :=
    ideleClass_herbrandQuotient_eq_card_of_supported_local_calculation
      (K := K) (L := L) S σ hgen hSP hUnram
  let hC0 := hC.1
  let hCm := hC.2
  rw [ideleClassNorm_index_eq_herbrandH0_card K L]
  apply
    le_herbrandH0_card_of_herbrandQuotient_eq_nat
      (G := L ≃ₐ[K] L)
      (A := RelativeIdeleGroup.ClassGroup K L)
      σ (Fintype.card (L ≃ₐ[K] L))
  simpa using hCvalue

/-- Unconditional norm-index lower bound for a cyclic extension, in
Galois-group-order form. -/
theorem card_le_ideleClassNorm_index
    (σ : L ≃ₐ[K] L)
    (hgen : ∀ τ : L ≃ₐ[K] L,
      τ ∈ Subgroup.zpowers σ) :
    Fintype.card (L ≃ₐ[K] L) ≤
      (RelativeIdeleGroup.Cohomology.ideleClassNorm K L).range.index :=
  card_le_ideleClassNorm_index_of_supported_local_calculation
    (K := K) (L := L)
    (ideleClassHerbrandSupport (K := K) (L := L))
    σ hgen
    (relativeSupportedAboveHerbrandSupport_sup_principal_eq_top
      (K := K) (L := L))
    (chosenFinitePlaceIsUnramified_of_notMem_ideleClassHerbrandSupport
      (K := K) (L := L))

/-- Unconditional norm-index lower bound in extension-degree form. -/
theorem finrank_le_ideleClassNorm_index
    (σ : L ≃ₐ[K] L)
    (hgen : ∀ τ : L ≃ₐ[K] L,
      τ ∈ Subgroup.zpowers σ) :
    Module.finrank K L ≤
      (RelativeIdeleGroup.Cohomology.ideleClassNorm K L).range.index := by
  simpa only [Fintype.card_eq_nat_card,
    IsGalois.card_aut_eq_finrank K L] using
    card_le_ideleClassNorm_index
      (K := K) (L := L) σ hgen

end Cohomology
end GlobalClassFieldTheory
end
end

section
-- module Solutions.OAIQ244_DUKE.GlobalClassFieldTheory_Cohomology_CyclicPrimePowerFullDecomposition
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.GlobalClassFields.ConductorialSubgroup.finiteIndex _root_.GlobalClassFieldTheory.GlobalClassFields.bigHilbertClassFieldNormSubgroup_normal _root_.GlobalClassFieldTheory.GlobalClassFields.smallHilbertClassFieldNormSubgroupFiniteIndex _root_.GlobalClassFieldTheory.Reciprocity.complexFourthRootField_numberField _root_.GlobalClassFieldTheory.Reciprocity.infinitePlaceComplexificationOverfield_algebra _root_.GlobalClassFieldTheory.Reciprocity.infinitePlaceComplexificationOverfield_baseAlgebra _root_.GlobalClassFieldTheory.Reciprocity.infinitePlaceComplexificationOverfield_numberField _root_.GlobalClassFieldTheory.Reciprocity.rationalIntermediateFieldNumberField _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.KummerTheory.primeCyclotomicBaseFiniteDimensional _root_.KummerTheory.primeCyclotomicBaseIsGalois _root_.KummerTheory.primeCyclotomicBaseNumberField _root_.KummerTheory.rationalCyclotomicLevel_numberField _root_.LocalClassFieldTheory.finiteGaloisLocalField_integerRing_moduleFinite _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.residueFieldZModAlgebra _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedIntegralAlgebraContextValuationSubringAlgebra _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedIntegralAlgebraContextValuationSubringTower _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedQPadicContextValuationSubringTower _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.LubinTate.padicCompletedLevelField_algebra _root_.LubinTate.padicCompletedLevelField_finiteDimensional _root_.LubinTate.padicCompletedLevelField_isGalois _root_.LubinTate.padicCompletedUnramifiedFieldAlgebra _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.boundedRealFields_numberField _root_.OAI.PrimeDegreePackets.diagonalLogAction _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.LocalClassFieldTheory.comparisonIntegerRingIsIntegralClosure _root_.LocalClassFieldTheory.normalizationIntegerRingIsIntegralClosure _root_.cyclicPrimeDegreeIntermediate_isGalois
attribute [-simp] _root_.GlobalClassFieldTheory.ClassFieldAxiom.actualPushoutNormQuotientMap_mk _root_.GlobalClassFieldTheory.ClassFieldAxiom.hasseNormDiagonal_mk _root_.GlobalClassFieldTheory.ClassFieldAxiom.sUnitEquivSupportedPrincipalIdeleSubgroup_coe _root_.GlobalClassFieldTheory.GlobalClassFields.ConductorialSubgroup.ideleClassQuotientEquivOfNarrowFiniteConductorsEqOfRayClassGroupCardsEqQuotientCards_mk _root_.GlobalClassFieldTheory.GlobalClassFields.ConductorialSubgroup.mem_fullConductorInfinitePart_iff _root_.GlobalClassFieldTheory.GlobalClassFields.ConductorialSubgroup.narrowFiniteConductorRayClassGroupEquivQuotientOfCardEq_mk _root_.GlobalClassFieldTheory.GlobalClassFields.ConductorialSubgroup.narrowFiniteConductorRayClassGroupToQuotient_mk _root_.GlobalClassFieldTheory.GlobalClassFields.bigHilbertClassFieldQuotientEquivNarrowClassGroup_mk _root_.GlobalClassFieldTheory.GlobalClassFields.bigHilbertClassFieldQuotientToSmallHilbertClassFieldQuotient_mk _root_.GlobalClassFieldTheory.GlobalClassFields.realSignToBigHilbertClassFieldQuotient_apply _root_.GlobalClassFieldTheory.GlobalClassFields.realSignToNarrowClassKernel_apply _root_.GlobalClassFieldTheory.GlobalClassFields.smallHilbertClassFieldQuotientEquivClassGroup_mk _root_.GlobalClassFieldTheory.Reciprocity.globalNormClassFromIdele_principalIdele _root_.GlobalClassFieldTheory.Reciprocity.infinitePlaceGlobalArtinMonoidHom_finitePlaceIdele _root_.IdeleGroup.finitePlaceIdele_finiteComponent_of_ne _root_.IdeleGroup.finitePlaceIdele_finiteComponent_same _root_.IdeleGroup.finitePlaceIdele_infiniteComponent _root_.IdeleGroup.ideleNormContinuousMonoidHom_apply _root_.IdeleGroup.infinitePlaceIdeleContinuous_apply _root_.IdeleGroup.infinitePlaceIdele_finiteComponent _root_.IdeleGroup.infinitePlaceIdele_infiniteComponent_of_ne _root_.IdeleGroup.infinitePlaceIdele_infiniteComponent_same _root_.IsDiscreteValuationRing.addVal_ringEquiv _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.OAI.PrimeDegreePackets.ThetaConstruction.schwartzCM_apply _root_.RayClass.primesEquiv_val_eq_natGenerator _root_.RayClass.signToNarrow_mk _root_.RelativeIdeleGroup.relativeFinitePlaceIdele_finiteComponent_of_ne _root_.RelativeIdeleGroup.relativeFinitePlaceIdele_finiteComponent_same _root_.RelativeIdeleGroup.relativeFinitePlaceIdele_infiniteComponent _root_.RelativeIdeleGroup.relativeInfinitePlaceIdele_finiteComponent _root_.RelativeIdeleGroup.relativeInfinitePlaceIdele_infiniteComponent_of_ne _root_.RelativeIdeleGroup.relativeInfinitePlaceIdele_infiniteComponent_same
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

/-!
# Full decomposition places in cyclic prime-power extensions

This file proves the infinitude of full-decomposition places in cyclic
prime-power extensions.  For a cyclic group of prime-power order, every
proper subgroup is contained in the
chosen subgroup of index `p`.  Consequently every finite place whose
decomposition group is proper splits completely in the chosen
degree-`p` subextension.

The second part records the idelic approximation argument: if all
finite places outside a finite set split completely, then the idele
class norm is surjective.
-/

open scoped NumberField Classical
open NumberField IsDedekindDomain

noncomputable section

open RelativeIdeleGroup.Cohomology

namespace GlobalClassFieldTheory
namespace Cohomology

open AlgebraicNumberTheory.Valuations
open HilbertRamification

variable
    {K L : Type}
    [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    [IsCyclic (L ≃ₐ[K] L)]

/-- In a cyclic extension of prime-power degree, infinitely many finite
places have full decomposition group.  The norm-index input in the
preceding theorem is supplied by the unconditional lower bound for the
chosen degree-`p` subextension. -/
theorem cyclic_prime_power_infinite_fullDecompositionPlaces
    {p exponent : ℕ}
    (hp : p.Prime)
    (hexponent : 0 < exponent)
    (hcard : Nat.card (L ≃ₐ[K] L) = p ^ exponent) :
    Set.Infinite
      {v : HeightOneSpectrum (𝓞 K) |
        finitePlaceDecompositionGroup
            (K := K) (L := L) v = ⊤} := by
  let M :=
    cyclicPrimeSubextension
      (K := K) (L := L)
      hp hexponent hcard
  let : IsGalois K M :=
    cyclicPrimeSubextension_isGalois
      (K := K) (L := L)
      hp hexponent hcard
  let : IsCyclic (M ≃ₐ[K] M) := by
    simpa [M] using
      cyclicPrimeSubextension_isCyclic
        (K := K) (L := L)
        hp hexponent hcard
  obtain ⟨σ, hσ⟩ :=
    IsCyclic.exists_generator (α := M ≃ₐ[K] M)
  have hLowerM :
      Module.finrank K M ≤
        (RelativeIdeleGroup.Cohomology.ideleClassNorm K M).range.index :=
    finrank_le_ideleClassNorm_index
      (K := K) (L := M) σ hσ
  have hDegree : Module.finrank K M = p := by
    simpa [M] using
      cyclicPrimeSubextension_finrank
        (K := K) (L := L)
        hp hexponent hcard
  apply
    cyclic_prime_power_fullDecompositionPlaces_infinite_of_primeSubextension_normIndex
      (K := K) (L := L)
      hp hexponent hcard
  simpa [M, hDegree] using hLowerM

end Cohomology
end GlobalClassFieldTheory
end
end

section
-- module Solutions.OAIQ244_DUKE.GlobalClassFieldTheory_ClassFieldAxiom_SUnitKummerPrimeSelection_BasePlaceSelection
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.infinitePlaceComplexificationOverfield_algebra _root_.GlobalClassFieldTheory.Reciprocity.infinitePlaceComplexificationOverfield_baseAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.KummerTheory.primeCyclotomicBaseFiniteDimensional _root_.LocalClassFieldTheory.finiteGaloisLocalField_integerRing_moduleFinite _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitQuotientCarrier_finite _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.residueFieldZModAlgebra _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedIntegralAlgebraContextValuationSubringAlgebra _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedIntegralAlgebraContextValuationSubringTower _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedQPadicContextValuationSubringTower _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.Padic.padicUnitFiniteFactor_finite _root_.LubinTate.padicCompletedLevelField_algebra _root_.LubinTate.padicCompletedLevelField_finiteDimensional _root_.LubinTate.padicCompletedUnramifiedFieldAlgebra _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.boundedRealFields_finite _root_.OAI.PrimeDegreePackets.diagonalLogAction _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.LocalClassFieldTheory.comparisonIntegerRingIsIntegralClosure _root_.LocalClassFieldTheory.normalizationIntegerRingIsIntegralClosure
attribute [-simp] _root_.GlobalClassFieldTheory.ClassFieldAxiom.sUnitEquivSupportedPrincipalIdeleSubgroup_coe _root_.IsDiscreteValuationRing.addVal_ringEquiv _root_.OAI.PrimeDegreePackets.ThetaConstruction.schwartzCM_apply _root_.RayClass.primesEquiv_val_eq_natGenerator
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI
attribute [local instance] OAI.starSubalgebraCommCStarAlgebra

set_option autoImplicit false

/-!
# Base-place selection for S-unit Kummer extensions

This file constructs infinite full-decomposition candidate sets and chooses
pairwise distinct base places outside the finite avoidance set. Distinctness
is obtained from Mathlib's Hall marriage theorem.
-/

open scoped NumberField Classical IsMulCommutative
open NumberField IsDedekindDomain
open KummerTheory

noncomputable section

namespace GlobalClassFieldTheory.ClassFieldAxiom

section FinitePlaces

variable {K : Type} [Field K]
    [NumberField K]

/-- Each cyclic coordinate extension supplies infinitely many base
finite places below completely decomposed places. -/
theorem sUnitKummerCoordinateBasePlaceCandidates_infinite
    {Omega : Type} [Field Omega] [Algebra K Omega]
    [IsSepClosure K Omega]
    (E : IntermediateField K Omega)
    [FiniteDimensional K E] [IsGalois K E]
    [IsMulCommutative Gal(E/K)]
    (n : ℕ+)
    (hmu : (primitiveRoots (n : ℕ) K).Nonempty)
    (p v : ℕ) (hp : p.Prime) (hv : 0 < v)
    (hn : (n : ℕ) = p ^ v)
    (r : ℕ)
    (eG :
      Gal(E/K) ≃*
        (Fin r → Multiplicative (ZMod (n : ℕ))))
    (S : Finset (HeightOneSpectrum (𝓞 K)))
    (i : Fin
      (sUnitKummerPrimeCount
        (K := K) E n hmu r S)) :
    (sUnitKummerCoordinateBasePlaceCandidates
      (K := K) (Omega := Omega) E n hmu
      p v hp hv hn r eG S i).Infinite := by
  let S' :=
    enlargeByFiniteKummerRadicalSupport
      (K := K) (L := E) n hmu S
  let N :=
    fullSUnitKummerExtension
      (K := K) (Omega := Omega) n S'
  have hnK : ((n : ℕ) : K) ≠ 0 := by
    exact_mod_cast n.ne_zero
  let : FiniteDimensional K N :=
    fullSUnitKummerExtension_finiteDimensional
      (K := K) (Omega := Omega) n hnK hmu S'
  let : NumberField N :=
    NumberField.of_module_finite K N
  let Ni :=
    sUnitKummerCoordinateFixedField
      (K := K) (Omega := Omega) E n hmu
      p v hp hv hn r eG S i
  let : NumberField Ni :=
    NumberField.of_module_finite K Ni
  let : IsGalois Ni N :=
    enlargedSUnitKummerCyclicFixedField_isGalois
      (K := K) (Omega := Omega) E n hmu
      (galois_pow_eq_one_of_equiv_pi_zmod
        (K := K) E n r eG) S
      (sUnitKummerKernelGenerator
        (K := K) (Omega := Omega) E n hmu
        p v hp hv hn r eG S i)
  let : IsCyclic (N ≃ₐ[Ni] N) :=
    enlargedSUnitKummerCyclicFixedField_isCyclic
      (K := K) (Omega := Omega) E n hmu
      (galois_pow_eq_one_of_equiv_pi_zmod
        (K := K) E n r eG) S
      (sUnitKummerKernelGenerator
        (K := K) (Omega := Omega) E n hmu
        p v hp hv hn r eG S i)
  have hdegree : Module.finrank Ni N = (n : ℕ) := by
    simpa only [Ni, N, S'] using
      sUnitKummerCoordinateFixedField_finrank
        (K := K) (Omega := Omega) E n hmu
        p v hp hv hn r eG S i
  have hcard : Nat.card (N ≃ₐ[Ni] N) = p ^ v := by
    calc
      Nat.card (N ≃ₐ[Ni] N) = Module.finrank Ni N :=
        IsGalois.card_aut_eq_finrank Ni N
      _ = (n : ℕ) := hdegree
      _ = p ^ v := hn
  have hfull :=
    Cohomology.cyclic_prime_power_infinite_fullDecompositionPlaces
      (K := Ni) (L := N) hp hv hcard
  intro hfinite
  have hpre :=
    _root_.Set.Finite.preimage_finitePlaceBelow
      (K := K) (L := Ni) hfinite
  apply hfull
  apply hpre.subset
  intro q hq
  change _root_.finitePlaceBelow (K := K) q ∈
    sUnitKummerCoordinateBasePlaceCandidates
      (K := K) (Omega := Omega) E n hmu
      p v hp hv hn r eG S i
  change ∃ q' : HeightOneSpectrum (𝓞 Ni),
    _root_.finitePlaceBelow (K := K) q' =
      _root_.finitePlaceBelow (K := K) q ∧
    _root_.finitePlaceDecompositionGroup
      (K := Ni) (L := N) q' = ⊤
  exact ⟨q, rfl, hq⟩

/-- Simultaneously choose distinct full-decomposition candidates outside
the enlarged support, the ramified primes of `N/K`, and the support of `n`. -/
theorem exists_sUnitKummerChosenBasePlaces
    {Omega : Type} [Field Omega] [Algebra K Omega]
    [IsSepClosure K Omega]
    (E : IntermediateField K Omega)
    [FiniteDimensional K E] [IsGalois K E]
    [IsMulCommutative Gal(E/K)]
    (n : ℕ+)
    (hmu : (primitiveRoots (n : ℕ) K).Nonempty)
    (p v : ℕ) (hp : p.Prime) (hv : 0 < v)
    (hn : (n : ℕ) = p ^ v)
    (r : ℕ)
    (eG :
      Gal(E/K) ≃*
        (Fin r → Multiplicative (ZMod (n : ℕ))))
    (S : Finset (HeightOneSpectrum (𝓞 K))) :
    ∃ f :
        Fin
            (sUnitKummerPrimeCount
              (K := K) E n hmu r S) →
          HeightOneSpectrum (𝓞 K),
      Function.Injective f ∧
        ∀ i,
          f i ∈
              sUnitKummerCoordinateBasePlaceCandidates
                (K := K) (Omega := Omega) E n hmu
                p v hp hv hn r eG S i ∧
            f i ∉
              sUnitKummerAvoidedBasePlaces
                (K := K) (Omega := Omega) E n hmu S := by
  let q :=
    sUnitKummerPrimeCount
      (K := K) E n hmu r S
  let A :
      Fin q → Set (HeightOneSpectrum (𝓞 K)) :=
    fun i =>
      sUnitKummerCoordinateBasePlaceCandidates
          (K := K) (Omega := Omega) E n hmu
          p v hp hv hn r eG S i \
        (sUnitKummerAvoidedBasePlaces
          (K := K) (Omega := Omega) E n hmu S : Set _)
  have hA : ∀ i, (A i).Infinite := by
    intro i
    exact
      (sUnitKummerCoordinateBasePlaceCandidates_infinite
        (K := K) (Omega := Omega) E n hmu
        p v hp hv hn r eG S i).sdiff
        (sUnitKummerAvoidedBasePlaces
          (K := K) (Omega := Omega) E n hmu S).finite_toSet
  classical
  choose B hBsub hBcard using
    fun i => (hA i).exists_subset_card_eq q
  have hHall :
      ∀ t : Finset (Fin q),
        t.card ≤ (t.biUnion B).card := by
    intro t
    by_cases ht : t.Nonempty
    · obtain ⟨i, hi⟩ := ht
      calc
        t.card ≤ q := by
          simpa using t.card_le_univ
        _ = (B i).card := (hBcard i).symm
        _ ≤ (t.biUnion B).card :=
          Finset.card_le_card
            (Finset.subset_biUnion_of_mem B hi)
    · simp [Finset.not_nonempty_iff_eq_empty.mp ht]
  obtain ⟨f, hf, hfB⟩ :=
    (Finset.all_card_le_biUnion_card_iff_existsInjective' B).mp
      hHall
  refine ⟨f, hf, ?_⟩
  intro i
  exact hBsub i (hfB i)

/-- The chosen ordered family of base primes. -/
noncomputable def sUnitKummerChosenBasePlaces
    {Omega : Type} [Field Omega] [Algebra K Omega]
    [IsSepClosure K Omega]
    (E : IntermediateField K Omega)
    [FiniteDimensional K E] [IsGalois K E]
    [IsMulCommutative Gal(E/K)]
    (n : ℕ+)
    (hmu : (primitiveRoots (n : ℕ) K).Nonempty)
    (p v : ℕ) (hp : p.Prime) (hv : 0 < v)
    (hn : (n : ℕ) = p ^ v)
    (r : ℕ)
    (eG :
      Gal(E/K) ≃*
        (Fin r → Multiplicative (ZMod (n : ℕ))))
    (S : Finset (HeightOneSpectrum (𝓞 K))) :
    Fin
        (sUnitKummerPrimeCount
          (K := K) E n hmu r S) →
      HeightOneSpectrum (𝓞 K) :=
  Classical.choose
    (exists_sUnitKummerChosenBasePlaces
      (K := K) (Omega := Omega) E n hmu
      p v hp hv hn r eG S)

/-- The chosen base primes are pairwise distinct. -/
theorem sUnitKummerChosenBasePlaces_injective
    {Omega : Type} [Field Omega] [Algebra K Omega]
    [IsSepClosure K Omega]
    (E : IntermediateField K Omega)
    [FiniteDimensional K E] [IsGalois K E]
    [IsMulCommutative Gal(E/K)]
    (n : ℕ+)
    (hmu : (primitiveRoots (n : ℕ) K).Nonempty)
    (p v : ℕ) (hp : p.Prime) (hv : 0 < v)
    (hn : (n : ℕ) = p ^ v)
    (r : ℕ)
    (eG :
      Gal(E/K) ≃*
        (Fin r → Multiplicative (ZMod (n : ℕ))))
    (S : Finset (HeightOneSpectrum (𝓞 K))) :
    Function.Injective
      (sUnitKummerChosenBasePlaces
        (K := K) (Omega := Omega) E n hmu
        p v hp hv hn r eG S) :=
  (Classical.choose_spec
    (exists_sUnitKummerChosenBasePlaces
      (K := K) (Omega := Omega) E n hmu
      p v hp hv hn r eG S)).1

/-- Each chosen base prime lies below a completely decomposed place in
its coordinate fixed field. -/
theorem
    sUnitKummerChosenBasePlaces_mem_coordinateBasePlaceCandidates
    {Omega : Type} [Field Omega] [Algebra K Omega]
    [IsSepClosure K Omega]
    (E : IntermediateField K Omega)
    [FiniteDimensional K E] [IsGalois K E]
    [IsMulCommutative Gal(E/K)]
    (n : ℕ+)
    (hmu : (primitiveRoots (n : ℕ) K).Nonempty)
    (p v : ℕ) (hp : p.Prime) (hv : 0 < v)
    (hn : (n : ℕ) = p ^ v)
    (r : ℕ)
    (eG :
      Gal(E/K) ≃*
        (Fin r → Multiplicative (ZMod (n : ℕ))))
    (S : Finset (HeightOneSpectrum (𝓞 K)))
    (i : Fin
      (sUnitKummerPrimeCount
        (K := K) E n hmu r S)) :
    sUnitKummerChosenBasePlaces
        (K := K) (Omega := Omega) E n hmu
        p v hp hv hn r eG S i ∈
      sUnitKummerCoordinateBasePlaceCandidates
        (K := K) (Omega := Omega) E n hmu
        p v hp hv hn r eG S i :=
  ((Classical.choose_spec
    (exists_sUnitKummerChosenBasePlaces
      (K := K) (Omega := Omega) E n hmu
      p v hp hv hn r eG S)).2 i).1

/-- Every chosen base prime avoids the enlarged support, the ramified
primes of the full Kummer extension, and the support of `n`. -/
theorem sUnitKummerChosenBasePlaces_not_mem_avoided
    {Omega : Type} [Field Omega] [Algebra K Omega]
    [IsSepClosure K Omega]
    (E : IntermediateField K Omega)
    [FiniteDimensional K E] [IsGalois K E]
    [IsMulCommutative Gal(E/K)]
    (n : ℕ+)
    (hmu : (primitiveRoots (n : ℕ) K).Nonempty)
    (p v : ℕ) (hp : p.Prime) (hv : 0 < v)
    (hn : (n : ℕ) = p ^ v)
    (r : ℕ)
    (eG :
      Gal(E/K) ≃*
        (Fin r → Multiplicative (ZMod (n : ℕ))))
    (S : Finset (HeightOneSpectrum (𝓞 K)))
    (i : Fin
      (sUnitKummerPrimeCount
        (K := K) E n hmu r S)) :
    sUnitKummerChosenBasePlaces
        (K := K) (Omega := Omega) E n hmu
        p v hp hv hn r eG S i ∉
      sUnitKummerAvoidedBasePlaces
        (K := K) (Omega := Omega) E n hmu S :=
  ((Classical.choose_spec
    (exists_sUnitKummerChosenBasePlaces
      (K := K) (Omega := Omega) E n hmu
      p v hp hv hn r eG S)).2 i).2

/-- The exponent `n` is a unit at every chosen base prime. -/
theorem sUnitKummerChosenBasePlaces_valuation_natCast_eq_one
    {Omega : Type} [Field Omega] [Algebra K Omega]
    [IsSepClosure K Omega]
    (E : IntermediateField K Omega)
    [FiniteDimensional K E] [IsGalois K E]
    [IsMulCommutative Gal(E/K)]
    (n : ℕ+)
    (hmu : (primitiveRoots (n : ℕ) K).Nonempty)
    (p v : ℕ) (hp : p.Prime) (hv : 0 < v)
    (hn : (n : ℕ) = p ^ v)
    (r : ℕ)
    (eG :
      Gal(E/K) ≃*
        (Fin r → Multiplicative (ZMod (n : ℕ))))
    (S : Finset (HeightOneSpectrum (𝓞 K)))
    (i : Fin
      (sUnitKummerPrimeCount
        (K := K) E n hmu r S)) :
    (sUnitKummerChosenBasePlaces
        (K := K) (Omega := Omega) E n hmu
        p v hp hv hn r eG S i).valuation K
          ((n : ℕ) : K) =
      1 := by
  have hnK : ((n : ℕ) : K) ≠ 0 := by
    exact_mod_cast n.ne_zero
  let nUnit : Kˣ :=
    Units.mk0 ((n : ℕ) : K) hnK
  have hnotSupport :
      sUnitKummerChosenBasePlaces
          (K := K) (Omega := Omega) E n hmu
          p v hp hv hn r eG S i ∉
        chosenUnitFiniteSupport (K := K) nUnit := by
    intro hmem
    apply
      sUnitKummerChosenBasePlaces_not_mem_avoided
        (K := K) (Omega := Omega) E n hmu
        p v hp hv hn r eG S i
    unfold sUnitKummerAvoidedBasePlaces
    dsimp only
    exact Finset.mem_union_right _ hmem
  have hunit :=
    (mem_SUnitGroup_iff
      (K := K) (chosenUnitFiniteSupport (K := K) nUnit) nUnit).mp
      (mem_sUnitGroup_chosenUnitFiniteSupport (K := K) nUnit)
      (sUnitKummerChosenBasePlaces
        (K := K) (Omega := Omega) E n hmu
        p v hp hv hn r eG S i)
      hnotSupport
  simpa [nUnit] using hunit

end FinitePlaces

end GlobalClassFieldTheory.ClassFieldAxiom
end
end

section
-- module Solutions.OAIQ244_DUKE.GlobalClassFieldTheory_ClassFieldAxiom_SUnitKummerPrimeSelection_CoordinatePlaces
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 400000
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.infinitePlaceComplexificationOverfield_algebra _root_.GlobalClassFieldTheory.Reciprocity.infinitePlaceComplexificationOverfield_baseAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.KummerTheory.primeCyclotomicBaseFiniteDimensional _root_.LocalClassFieldTheory.finiteGaloisLocalField_integerRing_moduleFinite _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.residueFieldZModAlgebra _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedIntegralAlgebraContextValuationSubringAlgebra _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedIntegralAlgebraContextValuationSubringTower _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedQPadicContextValuationSubringTower _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LubinTate.padicCompletedLevelField_algebra _root_.LubinTate.padicCompletedLevelField_finiteDimensional _root_.LubinTate.padicCompletedUnramifiedFieldAlgebra _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.diagonalLogAction _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.LocalClassFieldTheory.comparisonIntegerRingIsIntegralClosure _root_.LocalClassFieldTheory.normalizationIntegerRingIsIntegralClosure
attribute [-simp] _root_.IsDiscreteValuationRing.addVal_ringEquiv _root_.OAI.PrimeDegreePackets.ThetaConstruction.schwartzCM_apply _root_.RayClass.primesEquiv_val_eq_natGenerator
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI
attribute [local instance] OAI.starSubalgebraCommCStarAlgebra

set_option autoImplicit false

/-!
# Coordinate places in an S-unit Kummer extension

This file lifts the chosen base places to coordinate places in the full
Kummer extension and proves the required decomposition and unramifiedness
properties.
-/

open scoped NumberField Classical IsMulCommutative
open NumberField IsDedekindDomain
open KummerTheory

noncomputable section

namespace GlobalClassFieldTheory.ClassFieldAxiom

section FinitePlaces

variable {K : Type} [Field K]
    [NumberField K]

/-- A completely decomposed coordinate place above the `i`-th chosen
base prime. -/
theorem exists_sUnitKummerCoordinatePlace
    {Omega : Type} [Field Omega] [Algebra K Omega]
    [IsSepClosure K Omega]
    (E : IntermediateField K Omega)
    [FiniteDimensional K E] [IsGalois K E]
    [IsMulCommutative Gal(E/K)]
    (n : ℕ+)
    (hmu : (primitiveRoots (n : ℕ) K).Nonempty)
    (p v : ℕ) (hp : p.Prime) (hv : 0 < v)
    (hn : (n : ℕ) = p ^ v)
    (r : ℕ)
    (eG :
      Gal(E/K) ≃*
        (Fin r → Multiplicative (ZMod (n : ℕ))))
    (S : Finset (HeightOneSpectrum (𝓞 K)))
    (i : Fin
      (sUnitKummerPrimeCount
        (K := K) E n hmu r S)) :
    let S' :=
      enlargeByFiniteKummerRadicalSupport
        (K := K) (L := E) n hmu S
    let N :=
      fullSUnitKummerExtension
        (K := K) (Omega := Omega) n S'
    let hnK : ((n : ℕ) : K) ≠ 0 := by
      exact_mod_cast n.ne_zero
    letI : FiniteDimensional K N :=
      fullSUnitKummerExtension_finiteDimensional
        (K := K) (Omega := Omega) n hnK hmu S'
    let Ni :=
      enlargedSUnitKummerCyclicFixedField
        (K := K) (Omega := Omega) E n hmu
        (galois_pow_eq_one_of_equiv_pi_zmod
          (K := K) E n r eG) S
        (sUnitKummerKernelGenerator
          (K := K) (Omega := Omega) E n hmu
          p v hp hv hn r eG S i)
    letI : NumberField Ni :=
      NumberField.of_module_finite K Ni
    letI : IsGalois Ni N :=
      enlargedSUnitKummerCyclicFixedField_isGalois
        (K := K) (Omega := Omega) E n hmu
        (galois_pow_eq_one_of_equiv_pi_zmod
          (K := K) E n r eG) S
        (sUnitKummerKernelGenerator
          (K := K) (Omega := Omega) E n hmu
          p v hp hv hn r eG S i)
    ∃ q : HeightOneSpectrum (𝓞 Ni),
      _root_.finitePlaceBelow (K := K) q =
          sUnitKummerChosenBasePlaces
            (K := K) (Omega := Omega) E n hmu
            p v hp hv hn r eG S i ∧
        _root_.finitePlaceDecompositionGroup
            (K := Ni) (L := N) q =
          ⊤ := by
  dsimp only
  let S' :=
    enlargeByFiniteKummerRadicalSupport
      (K := K) (L := E) n hmu S
  let N :=
    fullSUnitKummerExtension
      (K := K) (Omega := Omega) n S'
  have hnK : ((n : ℕ) : K) ≠ 0 := by
    exact_mod_cast n.ne_zero
  let : FiniteDimensional K N :=
    fullSUnitKummerExtension_finiteDimensional
      (K := K) (Omega := Omega) n hnK hmu S'
  let Ni :=
    enlargedSUnitKummerCyclicFixedField
      (K := K) (Omega := Omega) E n hmu
      (galois_pow_eq_one_of_equiv_pi_zmod
        (K := K) E n r eG) S
      (sUnitKummerKernelGenerator
        (K := K) (Omega := Omega) E n hmu
        p v hp hv hn r eG S i)
  let : NumberField Ni :=
    NumberField.of_module_finite K Ni
  let : IsGalois Ni N :=
    enlargedSUnitKummerCyclicFixedField_isGalois
      (K := K) (Omega := Omega) E n hmu
      (galois_pow_eq_one_of_equiv_pi_zmod
        (K := K) E n r eG) S
      (sUnitKummerKernelGenerator
        (K := K) (Omega := Omega) E n hmu
        p v hp hv hn r eG S i)
  have h :=
    sUnitKummerChosenBasePlaces_mem_coordinateBasePlaceCandidates
      (K := K) (Omega := Omega) E n hmu
      p v hp hv hn r eG S i
  change ∃ q : HeightOneSpectrum (𝓞 Ni),
    _root_.finitePlaceBelow (K := K) q =
        sUnitKummerChosenBasePlaces
          (K := K) (Omega := Omega) E n hmu
          p v hp hv hn r eG S i ∧
      _root_.finitePlaceDecompositionGroup
          (K := Ni) (L := N) q =
        ⊤ at h
  exact h

/-- The selected coordinate place above the `i`-th chosen base prime. -/
noncomputable def sUnitKummerCoordinatePlace
    {Omega : Type} [Field Omega] [Algebra K Omega]
    [IsSepClosure K Omega]
    (E : IntermediateField K Omega)
    [FiniteDimensional K E] [IsGalois K E]
    [IsMulCommutative Gal(E/K)]
    (n : ℕ+)
    (hmu : (primitiveRoots (n : ℕ) K).Nonempty)
    (p v : ℕ) (hp : p.Prime) (hv : 0 < v)
    (hn : (n : ℕ) = p ^ v)
    (r : ℕ)
    (eG :
      Gal(E/K) ≃*
        (Fin r → Multiplicative (ZMod (n : ℕ))))
    (S : Finset (HeightOneSpectrum (𝓞 K)))
    (i : Fin
      (sUnitKummerPrimeCount
        (K := K) E n hmu r S)) :=
  Classical.choose
    (exists_sUnitKummerCoordinatePlace
      (K := K) (Omega := Omega) E n hmu
      p v hp hv hn r eG S i)

/-- The selected coordinate place lies over the corresponding chosen
base prime. -/
@[simp]
theorem sUnitKummerCoordinatePlace_below
    {Omega : Type} [Field Omega] [Algebra K Omega]
    [IsSepClosure K Omega]
    (E : IntermediateField K Omega)
    [FiniteDimensional K E] [IsGalois K E]
    [IsMulCommutative Gal(E/K)]
    (n : ℕ+)
    (hmu : (primitiveRoots (n : ℕ) K).Nonempty)
    (p v : ℕ) (hp : p.Prime) (hv : 0 < v)
    (hn : (n : ℕ) = p ^ v)
    (r : ℕ)
    (eG :
      Gal(E/K) ≃*
        (Fin r → Multiplicative (ZMod (n : ℕ))))
    (S : Finset (HeightOneSpectrum (𝓞 K)))
    (i : Fin
      (sUnitKummerPrimeCount
        (K := K) E n hmu r S)) :
    let S' :=
      enlargeByFiniteKummerRadicalSupport
        (K := K) (L := E) n hmu S
    let N :=
      fullSUnitKummerExtension
        (K := K) (Omega := Omega) n S'
    let hnK : ((n : ℕ) : K) ≠ 0 := by
      exact_mod_cast n.ne_zero
    letI : FiniteDimensional K N :=
      fullSUnitKummerExtension_finiteDimensional
        (K := K) (Omega := Omega) n hnK hmu S'
    let Ni :=
      enlargedSUnitKummerCyclicFixedField
        (K := K) (Omega := Omega) E n hmu
        (galois_pow_eq_one_of_equiv_pi_zmod
          (K := K) E n r eG) S
        (sUnitKummerKernelGenerator
          (K := K) (Omega := Omega) E n hmu
          p v hp hv hn r eG S i)
    letI : NumberField Ni :=
      NumberField.of_module_finite K Ni
    _root_.finitePlaceBelow (K := K)
        (sUnitKummerCoordinatePlace
          (K := K) (Omega := Omega) E n hmu
          p v hp hv hn r eG S i) =
      sUnitKummerChosenBasePlaces
        (K := K) (Omega := Omega) E n hmu
        p v hp hv hn r eG S i :=
  (Classical.choose_spec
    (exists_sUnitKummerCoordinatePlace
      (K := K) (Omega := Omega) E n hmu
      p v hp hv hn r eG S i)).1

/-- The selected coordinate place is completely decomposed in the full
Kummer extension over its coordinate fixed field. -/
@[simp]
theorem sUnitKummerCoordinatePlace_decompositionGroup
    {Omega : Type} [Field Omega] [Algebra K Omega]
    [IsSepClosure K Omega]
    (E : IntermediateField K Omega)
    [FiniteDimensional K E] [IsGalois K E]
    [IsMulCommutative Gal(E/K)]
    (n : ℕ+)
    (hmu : (primitiveRoots (n : ℕ) K).Nonempty)
    (p v : ℕ) (hp : p.Prime) (hv : 0 < v)
    (hn : (n : ℕ) = p ^ v)
    (r : ℕ)
    (eG :
      Gal(E/K) ≃*
        (Fin r → Multiplicative (ZMod (n : ℕ))))
    (S : Finset (HeightOneSpectrum (𝓞 K)))
    (i : Fin
      (sUnitKummerPrimeCount
        (K := K) E n hmu r S)) :
    let S' :=
      enlargeByFiniteKummerRadicalSupport
        (K := K) (L := E) n hmu S
    let N :=
      fullSUnitKummerExtension
        (K := K) (Omega := Omega) n S'
    let hnK : ((n : ℕ) : K) ≠ 0 := by
      exact_mod_cast n.ne_zero
    letI : FiniteDimensional K N :=
      fullSUnitKummerExtension_finiteDimensional
        (K := K) (Omega := Omega) n hnK hmu S'
    let Ni :=
      enlargedSUnitKummerCyclicFixedField
        (K := K) (Omega := Omega) E n hmu
        (galois_pow_eq_one_of_equiv_pi_zmod
          (K := K) E n r eG) S
        (sUnitKummerKernelGenerator
          (K := K) (Omega := Omega) E n hmu
          p v hp hv hn r eG S i)
    letI : NumberField Ni :=
      NumberField.of_module_finite K Ni
    letI : IsGalois Ni N :=
      enlargedSUnitKummerCyclicFixedField_isGalois
        (K := K) (Omega := Omega) E n hmu
        (galois_pow_eq_one_of_equiv_pi_zmod
          (K := K) E n r eG) S
        (sUnitKummerKernelGenerator
          (K := K) (Omega := Omega) E n hmu
          p v hp hv hn r eG S i)
    _root_.finitePlaceDecompositionGroup
        (K := Ni) (L := N)
        (sUnitKummerCoordinatePlace
          (K := K) (Omega := Omega) E n hmu
          p v hp hv hn r eG S i) =
      ⊤ :=
  (Classical.choose_spec
    (exists_sUnitKummerCoordinatePlace
      (K := K) (Omega := Omega) E n hmu
      p v hp hv hn r eG S i)).2

/-- The `i`-th selected base prime is unramified in the full Kummer
extension. -/
theorem sUnitKummerChosenBasePlace_not_mem_ramified
    {Omega : Type} [Field Omega] [Algebra K Omega]
    [IsSepClosure K Omega]
    (E : IntermediateField K Omega)
    [FiniteDimensional K E] [IsGalois K E]
    [IsMulCommutative Gal(E/K)]
    (n : ℕ+)
    (hmu : (primitiveRoots (n : ℕ) K).Nonempty)
    (p v : ℕ) (hp : p.Prime) (hv : 0 < v)
    (hn : (n : ℕ) = p ^ v)
    (r : ℕ)
    (eG :
      Gal(E/K) ≃*
        (Fin r → Multiplicative (ZMod (n : ℕ))))
    (S : Finset (HeightOneSpectrum (𝓞 K)))
    (i : Fin
      (sUnitKummerPrimeCount
        (K := K) E n hmu r S)) :
    let S' :=
      enlargeByFiniteKummerRadicalSupport
        (K := K) (L := E) n hmu S
    let N :=
      fullSUnitKummerExtension
        (K := K) (Omega := Omega) n S'
    let hnK : ((n : ℕ) : K) ≠ 0 := by
      exact_mod_cast n.ne_zero
    letI : FiniteDimensional K N :=
      fullSUnitKummerExtension_finiteDimensional
        (K := K) (Omega := Omega) n hnK hmu S'
    letI : IsGalois K N :=
      fullSUnitKummerExtension_isGalois
        (K := K) (Omega := Omega) n S'
    letI : NumberField N :=
      NumberField.of_module_finite K N
    sUnitKummerChosenBasePlaces
        (K := K) (Omega := Omega) E n hmu
        p v hp hv hn r eG S i ∉
      _root_.ramifiedBaseFinitePlaces
        (K := K) (L := N) := by
  dsimp only
  intro hram
  apply
    sUnitKummerChosenBasePlaces_not_mem_avoided
      (K := K) (Omega := Omega) E n hmu
      p v hp hv hn r eG S i
  unfold sUnitKummerAvoidedBasePlaces
  dsimp only
  exact
    Finset.mem_union_left _
      (Finset.mem_union_right _ hram)

/-- The chosen completed place at `p_i` is unramified in `N/K`. -/
theorem sUnitKummerChosenBasePlace_isUnramified
    {Omega : Type} [Field Omega] [Algebra K Omega]
    [IsSepClosure K Omega]
    (E : IntermediateField K Omega)
    [FiniteDimensional K E] [IsGalois K E]
    [IsMulCommutative Gal(E/K)]
    (n : ℕ+)
    (hmu : (primitiveRoots (n : ℕ) K).Nonempty)
    (p v : ℕ) (hp : p.Prime) (hv : 0 < v)
    (hn : (n : ℕ) = p ^ v)
    (r : ℕ)
    (eG :
      Gal(E/K) ≃*
        (Fin r → Multiplicative (ZMod (n : ℕ))))
    (S : Finset (HeightOneSpectrum (𝓞 K)))
    (i : Fin
      (sUnitKummerPrimeCount
        (K := K) E n hmu r S)) :
    let S' :=
      enlargeByFiniteKummerRadicalSupport
        (K := K) (L := E) n hmu S
    let N :=
      fullSUnitKummerExtension
        (K := K) (Omega := Omega) n S'
    let hnK : ((n : ℕ) : K) ≠ 0 := by
      exact_mod_cast n.ne_zero
    letI : FiniteDimensional K N :=
      fullSUnitKummerExtension_finiteDimensional
        (K := K) (Omega := Omega) n hnK hmu S'
    letI : IsGalois K N :=
      fullSUnitKummerExtension_isGalois
        (K := K) (Omega := Omega) n S'
    letI : NumberField N :=
      NumberField.of_module_finite K N
    _root_.ChosenFinitePlaceIsUnramified
      (K := K) (L := N)
      (sUnitKummerChosenBasePlaces
        (K := K) (Omega := Omega) E n hmu
        p v hp hv hn r eG S i) := by
  dsimp only
  let S' :=
    enlargeByFiniteKummerRadicalSupport
      (K := K) (L := E) n hmu S
  let N :=
    fullSUnitKummerExtension
      (K := K) (Omega := Omega) n S'
  have hnK : ((n : ℕ) : K) ≠ 0 := by
    exact_mod_cast n.ne_zero
  let : FiniteDimensional K N :=
    fullSUnitKummerExtension_finiteDimensional
      (K := K) (Omega := Omega) n hnK hmu S'
  let : IsGalois K N :=
    fullSUnitKummerExtension_isGalois
      (K := K) (Omega := Omega) n S'
  let : NumberField N :=
    NumberField.of_module_finite K N
  apply
    _root_.chosenFinitePlaceIsUnramified_of_isUnramifiedAt
  by_contra hram
  apply
    sUnitKummerChosenBasePlace_not_mem_ramified
      (K := K) (Omega := Omega) E n hmu
      p v hp hv hn r eG S i
  rw [_root_.mem_ramifiedBaseFinitePlaces_iff]
  exact
    ⟨_,
      _root_.finitePlaceExtensionCentre_liesOver
        (K := K)
        (L := N)
        _
        (_root_.chosenFinitePlaceExtension
          (L := N) _),
      hram⟩

end FinitePlaces

end GlobalClassFieldTheory.ClassFieldAxiom
end
end

section
-- module Solutions.OAIQ244_DUKE.GlobalClassFieldTheory_ClassFieldAxiom_SUnitKummerPrimeSelection_PrimeSet
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 400000
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.infinitePlaceComplexificationOverfield_algebra _root_.GlobalClassFieldTheory.Reciprocity.infinitePlaceComplexificationOverfield_baseAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalClassFieldTheory.finiteGaloisLocalField_integerRing_moduleFinite _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.residueFieldZModAlgebra _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedIntegralAlgebraContextValuationSubringAlgebra _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedIntegralAlgebraContextValuationSubringTower _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedQPadicContextValuationSubringTower _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LubinTate.padicCompletedLevelField_algebra _root_.LubinTate.padicCompletedUnramifiedFieldAlgebra _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.diagonalLogAction _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.LocalClassFieldTheory.comparisonIntegerRingIsIntegralClosure _root_.LocalClassFieldTheory.normalizationIntegerRingIsIntegralClosure
attribute [-simp] _root_.GlobalClassFieldTheory.ClassFieldAxiom.sUnitKummerCoordinatePlace_below _root_.GlobalClassFieldTheory.ClassFieldAxiom.sUnitKummerCoordinatePlace_decompositionGroup _root_.IsDiscreteValuationRing.addVal_ringEquiv _root_.OAI.PrimeDegreePackets.ThetaConstruction.schwartzCM_apply _root_.RayClass.primesEquiv_val_eq_natGenerator
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI
attribute [local instance] OAI.starSubalgebraCommCStarAlgebra

set_option autoImplicit false

/-!
# The finite prime set for an S-unit Kummer extension

This file packages the chosen base places as a finite set and proves its
cardinality and disjointness properties.
-/

open scoped NumberField Classical IsMulCommutative
open NumberField IsDedekindDomain
open KummerTheory

noncomputable section

namespace GlobalClassFieldTheory.ClassFieldAxiom

section FinitePlaces

variable {K : Type} [Field K]
    [NumberField K]

/-- The finite set `T` of primes chosen for the coordinate cyclic extensions
that detect the enlarged `S`-unit Kummer radical. -/
noncomputable def sUnitKummerPrimeSet
    {Omega : Type} [Field Omega] [Algebra K Omega]
    [IsSepClosure K Omega]
    (E : IntermediateField K Omega)
    [FiniteDimensional K E] [IsGalois K E]
    [IsMulCommutative Gal(E/K)]
    (n : ℕ+)
    (hmu : (primitiveRoots (n : ℕ) K).Nonempty)
    (p v : ℕ) (hp : p.Prime) (hv : 0 < v)
    (hn : (n : ℕ) = p ^ v)
    (r : ℕ)
    (eG :
      Gal(E/K) ≃*
        (Fin r → Multiplicative (ZMod (n : ℕ))))
    (S : Finset (HeightOneSpectrum (𝓞 K))) :
    Finset (HeightOneSpectrum (𝓞 K)) :=
  Finset.univ.image
    (sUnitKummerChosenBasePlaces
      (K := K) (Omega := Omega) E n hmu
      p v hp hv hn r eG S)

/-- The chosen prime set has the required cardinality `s-r`. -/
@[simp]
theorem sUnitKummerPrimeSet_card
    {Omega : Type} [Field Omega] [Algebra K Omega]
    [IsSepClosure K Omega]
    (E : IntermediateField K Omega)
    [FiniteDimensional K E] [IsGalois K E]
    [IsMulCommutative Gal(E/K)]
    (n : ℕ+)
    (hmu : (primitiveRoots (n : ℕ) K).Nonempty)
    (p v : ℕ) (hp : p.Prime) (hv : 0 < v)
    (hn : (n : ℕ) = p ^ v)
    (r : ℕ)
    (eG :
      Gal(E/K) ≃*
        (Fin r → Multiplicative (ZMod (n : ℕ))))
    (S : Finset (HeightOneSpectrum (𝓞 K))) :
    (sUnitKummerPrimeSet
      (K := K) (Omega := Omega) E n hmu
      p v hp hv hn r eG S).card =
        sUnitKummerPrimeCount
          (K := K) E n hmu r S := by
  rw [sUnitKummerPrimeSet,
    Finset.card_image_of_injective Finset.univ
      (sUnitKummerChosenBasePlaces_injective
        (K := K) (Omega := Omega) E n hmu
        p v hp hv hn r eG S),
    Finset.card_univ, Fintype.card_fin]

/-- The chosen prime set is disjoint from the enlarged finite Kummer-radical support. -/
theorem sUnitKummerPrimeSet_disjoint_enlargeByFiniteKummerRadicalSupport
    {Omega : Type} [Field Omega] [Algebra K Omega]
    [IsSepClosure K Omega]
    (E : IntermediateField K Omega)
    [FiniteDimensional K E] [IsGalois K E]
    [IsMulCommutative Gal(E/K)]
    (n : ℕ+)
    (hmu : (primitiveRoots (n : ℕ) K).Nonempty)
    (p v : ℕ) (hp : p.Prime) (hv : 0 < v)
    (hn : (n : ℕ) = p ^ v)
    (r : ℕ)
    (eG :
      Gal(E/K) ≃*
        (Fin r → Multiplicative (ZMod (n : ℕ))))
    (S : Finset (HeightOneSpectrum (𝓞 K))) :
    Disjoint
      (sUnitKummerPrimeSet
        (K := K) (Omega := Omega) E n hmu
        p v hp hv hn r eG S)
      (enlargeByFiniteKummerRadicalSupport
        (K := K) (L := E) n hmu S) := by
  rw [Finset.disjoint_left]
  intro w hwT hwS
  rw [sUnitKummerPrimeSet, Finset.mem_image] at hwT
  obtain ⟨i, -, hi⟩ := hwT
  subst w
  exact
    sUnitKummerChosenBasePlaces_not_mem_avoided
      (K := K) (Omega := Omega) E n hmu
      p v hp hv hn r eG S i
      (enlargeByFiniteKummerRadicalSupport_subset_sUnitKummerAvoidedBasePlaces
        (K := K) (Omega := Omega) E n hmu S hwS)

end FinitePlaces

end GlobalClassFieldTheory.ClassFieldAxiom
end
end

section
-- module Solutions.OAIQ244_DUKE.GlobalClassFieldTheory_ClassFieldAxiom_SUnitKummerPrimeSelection_DecompositionFields
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 400000
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.infinitePlaceComplexificationOverfield_algebra _root_.GlobalClassFieldTheory.Reciprocity.infinitePlaceComplexificationOverfield_baseAlgebra _root_.GlobalClassFieldTheory.Reciprocity.infinitePlaceComplexificationOverfield_baseSmul _root_.GlobalClassFieldTheory.Reciprocity.infinitePlaceComplexificationOverfield_smul _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.KummerTheory.primeCyclotomicBaseFiniteDimensional _root_.LocalClassFieldTheory.finiteGaloisLocalField_integerRing_moduleFinite _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitQuotientCarrier_finite _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.residueFieldZModAlgebra _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedIntegralAlgebraContextValuationSubringAlgebra _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedIntegralAlgebraContextValuationSubringTower _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedQPadicContextValuationSubringTower _root_.LocalFieldTheory.DiscreteValuationField.finite_nsmulAddKernel_padicInt_pi _root_.LocalFieldTheory.DiscreteValuationField.finite_principalUnits_nthPowerKernel _root_.LocalFieldTheory.DiscreteValuationField.finite_residueRootsOfUnityGroup _root_.LocalFieldTheory.DiscreteValuationField.finite_valuationSubringUnits_nthPowerKernel _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.Padic.padicUnitFiniteFactor_finite _root_.LubinTate.compatibleGroupFamiliesGroup _root_.LubinTate.padicCompletedLevelField_algebra _root_.LubinTate.padicCompletedLevelField_finiteDimensional _root_.LubinTate.padicCompletedUnramifiedFieldAlgebra _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.boundedRealFields_finite _root_.OAI.PrimeDegreePackets.diagonalLogAction _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.LocalClassFieldTheory.comparisonIntegerRingIsIntegralClosure _root_.LocalClassFieldTheory.normalizationIntegerRingIsIntegralClosure
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI
attribute [local instance] OAI.starSubalgebraCommCStarAlgebra

set_option autoImplicit false

/-!
# Decomposition groups and fields for S-unit Kummer prime selection

This file identifies the chosen decomposition groups with the cyclic
coordinate subgroups, proves complete splitting in the prescribed extension,
and identifies the associated decomposition fields.
-/

open scoped NumberField Classical IsMulCommutative
open NumberField IsDedekindDomain
open KummerTheory

noncomputable section

namespace GlobalClassFieldTheory.ClassFieldAxiom

section FinitePlaces

variable {K : Type} [Field K]
    [NumberField K]

/-- The coordinate generator lies in the chosen global decomposition
group. -/
theorem sUnitKummerKernelGenerator_mem_decompositionGroup
    {Omega : Type} [Field Omega] [Algebra K Omega]
    [IsSepClosure K Omega]
    (E : IntermediateField K Omega)
    [FiniteDimensional K E] [IsGalois K E]
    [IsMulCommutative Gal(E/K)]
    (n : ℕ+)
    (hmu : (primitiveRoots (n : ℕ) K).Nonempty)
    (p v : ℕ) (hp : p.Prime) (hv : 0 < v)
    (hn : (n : ℕ) = p ^ v)
    (r : ℕ)
    (eG :
      Gal(E/K) ≃*
        (Fin r → Multiplicative (ZMod (n : ℕ))))
    (S : Finset (HeightOneSpectrum (𝓞 K)))
    (i : Fin
      (sUnitKummerPrimeCount
        (K := K) E n hmu r S)) :
    let S' :=
      enlargeByFiniteKummerRadicalSupport
        (K := K) (L := E) n hmu S
    let N :=
      fullSUnitKummerExtension
        (K := K) (Omega := Omega) n S'
    let hnK : ((n : ℕ) : K) ≠ 0 := by
      exact_mod_cast n.ne_zero
    letI : FiniteDimensional K N :=
      fullSUnitKummerExtension_finiteDimensional
        (K := K) (Omega := Omega) n hnK hmu S'
    letI : IsGalois K N :=
      fullSUnitKummerExtension_isGalois
        (K := K) (Omega := Omega) n S'
    letI : NumberField N :=
      NumberField.of_module_finite K N
    ((sUnitKummerKernelGenerator
        (K := K) (Omega := Omega) E n hmu
        p v hp hv hn r eG S i :
          (enlargedSUnitKummerRestrictionHom
            (K := K) (Omega := Omega) E n hmu
            (galois_pow_eq_one_of_equiv_pi_zmod
              (K := K) E n r eG) S).ker) :
        Gal(N/K)) ∈
      _root_.finitePlaceDecompositionGroup
        (K := K) (L := N)
        (sUnitKummerChosenBasePlaces
          (K := K) (Omega := Omega) E n hmu
          p v hp hv hn r eG S i) := by
  dsimp only
  let S' :=
    enlargeByFiniteKummerRadicalSupport
      (K := K) (L := E) n hmu S
  let N :=
    fullSUnitKummerExtension
      (K := K) (Omega := Omega) n S'
  have hnK : ((n : ℕ) : K) ≠ 0 := by
    exact_mod_cast n.ne_zero
  let : FiniteDimensional K N :=
    fullSUnitKummerExtension_finiteDimensional
      (K := K) (Omega := Omega) n hnK hmu S'
  let _ : IsGalois K N :=
    fullSUnitKummerExtension_isGalois
      (K := K) (Omega := Omega) n S'
  let : NumberField N :=
    NumberField.of_module_finite K N
  let sigmaKer :=
    sUnitKummerKernelGenerator
      (K := K) (Omega := Omega) E n hmu
      p v hp hv hn r eG S i
  let sigma : Gal(N/K) :=
    sigmaKer.1
  let P : Subgroup Gal(N/K) :=
    Subgroup.zpowers sigma
  let Ni := IntermediateField.fixedField P
  let : NumberField Ni :=
    NumberField.of_module_finite K Ni
  let : IsGalois Ni N :=
    enlargedSUnitKummerCyclicFixedField_isGalois
      (K := K) (Omega := Omega) E n hmu
      (galois_pow_eq_one_of_equiv_pi_zmod
        (K := K) E n r eG)
      S sigmaKer
  let : IsScalarTower K Ni N :=
    IntermediateField.isScalarTower_mid Ni
  let : IsMulCommutative Gal(N/K) :=
    KummerTheory.kummerRadicalExtension_isMulCommutative
      n hmu (fullSUnitKummerSubgroup (K := K) n S').1
  let q : HeightOneSpectrum (𝓞 Ni) :=
    sUnitKummerCoordinatePlace
      (K := K) (Omega := Omega) E n hmu
      p v hp hv hn r eG S i
  let tau : N ≃ₐ[Ni] N :=
    IntermediateField.subgroupEquivAlgEquiv P
      ⟨sigma, Subgroup.mem_zpowers sigma⟩
  have hq :
      _root_.finitePlaceBelow (K := K) q =
        sUnitKummerChosenBasePlaces
          (K := K) (Omega := Omega) E n hmu
          p v hp hv hn r eG S i :=
    sUnitKummerCoordinatePlace_below
      (K := K) (Omega := Omega) E n hmu
      p v hp hv hn r eG S i
  have hfull :
      _root_.finitePlaceDecompositionGroup
          (K := Ni) (L := N) q =
        ⊤ :=
    sUnitKummerCoordinatePlace_decompositionGroup
      (K := K) (Omega := Omega) E n hmu
      p v hp hv hn r eG S i
  have hmem :=
    restrictAutomorphismScalars_mem_finitePlaceDecompositionGroup_of_relative_eq_top
      (F := K) (M := Ni) (L := N)
      _ q hq hfull tau
  have htau :
      sigma =
        RamificationTheory.HilbertRamification.ValuationSubring.restrictAutomorphismScalars
          (K := K) (M := Ni) tau := by
    apply AlgEquiv.ext
    intro x
    rfl
  change
    sigma ∈ finitePlaceDecompositionGroup
      (sUnitKummerChosenBasePlaces E n hmu p v hp hv hn r eG S i)
  rw [htau]
  exact hmem

/-- The chosen global decomposition group is exactly the cyclic
coordinate subgroup generated by `σᵢ`. -/
theorem sUnitKummerChosenDecompositionGroup_eq_zpowers
    {Omega : Type} [Field Omega] [Algebra K Omega]
    [IsSepClosure K Omega]
    (E : IntermediateField K Omega)
    [FiniteDimensional K E] [IsGalois K E]
    [IsMulCommutative Gal(E/K)]
    (n : ℕ+)
    (hmu : (primitiveRoots (n : ℕ) K).Nonempty)
    (p v : ℕ) (hp : p.Prime) (hv : 0 < v)
    (hn : (n : ℕ) = p ^ v)
    (r : ℕ)
    (eG :
      Gal(E/K) ≃*
        (Fin r → Multiplicative (ZMod (n : ℕ))))
    (S : Finset (HeightOneSpectrum (𝓞 K)))
    (i : Fin
      (sUnitKummerPrimeCount
        (K := K) E n hmu r S)) :
    let S' :=
      enlargeByFiniteKummerRadicalSupport
        (K := K) (L := E) n hmu S
    let N :=
      fullSUnitKummerExtension
        (K := K) (Omega := Omega) n S'
    let hnK : ((n : ℕ) : K) ≠ 0 := by
      exact_mod_cast n.ne_zero
    letI : FiniteDimensional K N :=
      fullSUnitKummerExtension_finiteDimensional
        (K := K) (Omega := Omega) n hnK hmu S'
    letI : IsGalois K N :=
      fullSUnitKummerExtension_isGalois
        (K := K) (Omega := Omega) n S'
    letI : NumberField N :=
      NumberField.of_module_finite K N
    _root_.finitePlaceDecompositionGroup
        (K := K) (L := N)
        (sUnitKummerChosenBasePlaces
          (K := K) (Omega := Omega) E n hmu
          p v hp hv hn r eG S i) =
      Subgroup.zpowers
        ((sUnitKummerKernelGenerator
            (K := K) (Omega := Omega) E n hmu
            p v hp hv hn r eG S i :
              (enlargedSUnitKummerRestrictionHom
                (K := K) (Omega := Omega) E n hmu
                (galois_pow_eq_one_of_equiv_pi_zmod
                  (K := K) E n r eG) S).ker) :
          Gal(N/K)) := by
  dsimp only
  let S' :=
    enlargeByFiniteKummerRadicalSupport
      (K := K) (L := E) n hmu S
  let N :=
    fullSUnitKummerExtension
      (K := K) (Omega := Omega) n S'
  have hnK : ((n : ℕ) : K) ≠ 0 := by
    exact_mod_cast n.ne_zero
  let : FiniteDimensional K N :=
    fullSUnitKummerExtension_finiteDimensional
      (K := K) (Omega := Omega) n hnK hmu S'
  let _ : IsGalois K N :=
    fullSUnitKummerExtension_isGalois
      (K := K) (Omega := Omega) n S'
  let : NumberField N :=
    NumberField.of_module_finite K N
  let D :=
    _root_.finitePlaceDecompositionGroup
      (K := K) (L := N)
      (sUnitKummerChosenBasePlaces
        (K := K) (Omega := Omega) E n hmu
        p v hp hv hn r eG S i)
  let sigmaKer :=
    sUnitKummerKernelGenerator
      (K := K) (Omega := Omega) E n hmu
      p v hp hv hn r eG S i
  let sigma : Gal(N/K) :=
    sigmaKer.1
  let : Finite Gal(N/K) :=
    finite_fullSUnitKummerExtension_galois
      (K := K) (Omega := Omega) n
      (by
        exact_mod_cast n.ne_zero)
      hmu S'
  let : IsCyclic D :=
    finitePlaceDecompositionGroup_isCyclic_of_chosenUnramified
      (F := K) (L := N)
      _
      (sUnitKummerChosenBasePlace_isUnramified
        (K := K) (Omega := Omega) E n hmu
        p v hp hv hn r eG S i)
  have hsigma : sigma ∈ D :=
    sUnitKummerKernelGenerator_mem_decompositionGroup
      (K := K) (Omega := Omega) E n hmu
      p v hp hv hn r eG S i
  let sigmaD : D := ⟨sigma, hsigma⟩
  have horderD : orderOf sigmaD = (n : ℕ) := by
    calc
      orderOf sigmaD = orderOf sigma := by
        simpa only [sigmaD] using
          Subgroup.orderOf_mk sigma hsigma
      _ = orderOf sigmaKer := by
        simpa only [sigma] using
          Subgroup.orderOf_coe sigmaKer
      _ = (n : ℕ) :=
        orderOf_sUnitKummerKernelGenerator
          (K := K) (Omega := Omega) E n hmu
          p v hp hv hn r eG S i
  have hlower : (n : ℕ) ≤ Nat.card D := by
    rw [← horderD]
    exact orderOf_le_card
  let := Fintype.ofFinite D
  have hpow (g : D) : g ^ (n : ℕ) = 1 := by
    apply Subtype.ext
    exact
      fullSUnitKummerExtension_galois_pow_eq_one
        (K := K) (Omega := Omega) n hmu S' g.1
  have hupper : Nat.card D ≤ (n : ℕ) := by
    rw [Nat.card_eq_fintype_card]
    calc
      Fintype.card D =
          (Finset.univ.filter
            (fun g : D => g ^ (n : ℕ) = 1)).card := by
        simp only [hpow, Finset.filter_true, Finset.card_univ]
      _ ≤ (n : ℕ) :=
        IsCyclic.card_pow_eq_one_le n.pos
  have hcard : Nat.card D = (n : ℕ) :=
    le_antisymm hupper hlower
  have hgen :
      Subgroup.zpowers sigmaD = ⊤ := by
    apply Subgroup.eq_top_of_card_eq
    rw [Nat.card_zpowers, horderD, hcard]
  calc
    D = (⊤ : Subgroup D).map D.subtype := by
      rw [← MonoidHom.range_eq_map, Subgroup.range_subtype]
    _ = (Subgroup.zpowers sigmaD).map D.subtype := by
      rw [hgen]
    _ = Subgroup.zpowers sigma := by
      rw [MonoidHom.map_zpowers]
      congr 1

/-- Every prime selected by the Kummer construction splits completely in the
prescribed extension `E / K`.  The selected decomposition group
upstairs is generated by an element of the kernel of restriction to
`E`, so complete splitting follows from the actual tower restriction
formula. -/
theorem finitePlaceSplitsCompletely_of_mem_sUnitKummerPrimeSet
    {Omega : Type} [Field Omega] [Algebra K Omega]
    [IsSepClosure K Omega]
    (E : IntermediateField K Omega)
    [FiniteDimensional K E] [IsGalois K E]
    [IsMulCommutative Gal(E/K)]
    (n : ℕ+)
    (hmu : (primitiveRoots (n : ℕ) K).Nonempty)
    (p v : ℕ) (hp : p.Prime) (hv : 0 < v)
    (hn : (n : ℕ) = p ^ v)
    (r : ℕ)
    (eG :
      Gal(E/K) ≃*
        (Fin r → Multiplicative (ZMod (n : ℕ))))
    (S : Finset (HeightOneSpectrum (𝓞 K))) :
    ∀ w,
      w ∈ sUnitKummerPrimeSet
          (K := K) (Omega := Omega) E n hmu
          p v hp hv hn r eG S →
        _root_.FinitePlaceSplitsCompletely
          (K := K) (L := E) w := by
  intro w hw
  rw [sUnitKummerPrimeSet, Finset.mem_image] at hw
  obtain ⟨i, -, rfl⟩ := hw
  let S' :=
    enlargeByFiniteKummerRadicalSupport
      (K := K) (L := E) n hmu S
  let N :=
    fullSUnitKummerExtension
      (K := K) (Omega := Omega) n S'
  let hnK : ((n : ℕ) : K) ≠ 0 := by
    exact_mod_cast n.ne_zero
  let : FiniteDimensional K N :=
    fullSUnitKummerExtension_finiteDimensional
      (K := K) (Omega := Omega) n hnK hmu S'
  let _ : IsGalois K N :=
    fullSUnitKummerExtension_isGalois
      (K := K) (Omega := Omega) n S'
  let _ : NumberField N :=
    NumberField.of_module_finite K N
  let : Algebra E N :=
    enlargedSUnitKummerAlgebra
      (K := K) (Omega := Omega) E n hmu
      (galois_pow_eq_one_of_equiv_pi_zmod
        (K := K) E n r eG) S
  let : IsScalarTower K E N := by
    infer_instance
  apply
    finitePlaceSplitsCompletely_of_decompositionGroup_le_restrictNormalHom_ker
      (K := K) (E := E) (N := N)
  rw [
    sUnitKummerChosenDecompositionGroup_eq_zpowers
      (K := K) (Omega := Omega) E n hmu
      p v hp hv hn r eG S i]
  apply Subgroup.zpowers_le.mpr
  simpa only [enlargedSUnitKummerRestrictionHom, N, S'] using
    (sUnitKummerKernelGenerator
      (K := K) (Omega := Omega) E n hmu
      p v hp hv hn r eG S i).property

/-- The decomposition field of the chosen base place is the coordinate fixed
field used in the Kummer prime-selection construction. -/
theorem sUnitKummerChosenDecompositionField_eq_coordinateFixedField
    {Omega : Type} [Field Omega] [Algebra K Omega]
    [IsSepClosure K Omega]
    (E : IntermediateField K Omega)
    [FiniteDimensional K E] [IsGalois K E]
    [IsMulCommutative Gal(E/K)]
    (n : ℕ+)
    (hmu : (primitiveRoots (n : ℕ) K).Nonempty)
    (p v : ℕ) (hp : p.Prime) (hv : 0 < v)
    (hn : (n : ℕ) = p ^ v)
    (r : ℕ)
    (eG :
      Gal(E/K) ≃*
        (Fin r → Multiplicative (ZMod (n : ℕ))))
    (S : Finset (HeightOneSpectrum (𝓞 K)))
    (i : Fin
      (sUnitKummerPrimeCount
        (K := K) E n hmu r S)) :
    let S' :=
      enlargeByFiniteKummerRadicalSupport
        (K := K) (L := E) n hmu S
    let N :=
      fullSUnitKummerExtension
        (K := K) (Omega := Omega) n S'
    let hnK : ((n : ℕ) : K) ≠ 0 := by
      exact_mod_cast n.ne_zero
    letI : FiniteDimensional K N :=
      fullSUnitKummerExtension_finiteDimensional
        (K := K) (Omega := Omega) n hnK hmu S'
    letI : IsGalois K N :=
      fullSUnitKummerExtension_isGalois
        (K := K) (Omega := Omega) n S'
    letI : NumberField N :=
      NumberField.of_module_finite K N
    IntermediateField.fixedField
        (_root_.finitePlaceDecompositionGroup
          (K := K) (L := N)
          (sUnitKummerChosenBasePlaces
            (K := K) (Omega := Omega) E n hmu
            p v hp hv hn r eG S i)) =
      sUnitKummerCoordinateFixedField
        (K := K) (Omega := Omega) E n hmu
        p v hp hv hn r eG S i := by
  dsimp only
  let S' :=
    enlargeByFiniteKummerRadicalSupport
      (K := K) (L := E) n hmu S
  let N :=
    fullSUnitKummerExtension
      (K := K) (Omega := Omega) n S'
  have hnK : ((n : ℕ) : K) ≠ 0 := by
    exact_mod_cast n.ne_zero
  let : FiniteDimensional K N :=
    fullSUnitKummerExtension_finiteDimensional
      (K := K) (Omega := Omega) n hnK hmu S'
  let _ : IsGalois K N :=
    fullSUnitKummerExtension_isGalois
      (K := K) (Omega := Omega) n S'
  let : NumberField N :=
    NumberField.of_module_finite K N
  rw [
    sUnitKummerChosenDecompositionGroup_eq_zpowers
      (K := K) (Omega := Omega) E n hmu
      p v hp hv hn r eG S i]
  rfl

end FinitePlaces

end GlobalClassFieldTheory.ClassFieldAxiom
end
end

section
-- module Solutions.OAIQ244_DUKE.GlobalClassFieldTheory_ClassFieldAxiom_SUnitKummerPrimeSelection_Conclusion
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 400000
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.GlobalClassFields.ConductorialSubgroup.finiteIndex _root_.GlobalClassFieldTheory.GlobalClassFields.bigHilbertClassFieldNormSubgroup_normal _root_.GlobalClassFieldTheory.GlobalClassFields.smallHilbertClassFieldNormSubgroupFiniteIndex _root_.GlobalClassFieldTheory.Reciprocity.infinitePlaceComplexificationOverfield_algebra _root_.GlobalClassFieldTheory.Reciprocity.infinitePlaceComplexificationOverfield_baseAlgebra _root_.GlobalClassFieldTheory.Reciprocity.infinitePlaceComplexificationOverfield_baseSmul _root_.GlobalClassFieldTheory.Reciprocity.infinitePlaceComplexificationOverfield_smul _root_.GlobalClassFieldTheory.Reciprocity.rationalCyclotomicCompletionAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalCyclotomicLocalizedCompletionFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalCyclotomicLocalizedCompletionIsAlgebraic _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalClassFieldTheory.finiteGaloisLocalField_integerRing_moduleFinite _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.residueFieldZModAlgebra _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedIntegralAlgebraContextValuationSubringAlgebra _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedIntegralAlgebraContextValuationSubringTower _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedIntegralLatticeContextModuleFinite _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedIntegralLatticeContextModuleFree _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedQPadicContextValuationSubringTower _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LubinTate.compatibleGroupFamiliesGroup _root_.LubinTate.padicCompletedLevelField_algebra _root_.LubinTate.padicCompletedUnramifiedFieldAlgebra _root_.LubinTate.standardLubinTateLevelValuationSubring_moduleFinite _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.diagonalLogAction _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.LocalClassFieldTheory.comparisonIntegerRingIsIntegralClosure _root_.LocalClassFieldTheory.normalizationIntegerRingIsIntegralClosure _root_.RamificationTheory.HilbertRamification.CompleteDVF.decompositionGroupMulSemiringAction _root_.RamificationTheory.HilbertRamification.CompleteDVF.decompositionGroupResidueFieldMulSemiringAction
attribute [-simp] _root_.GlobalClassFieldTheory.ClassFieldAxiom.sUnitEquivSupportedPrincipalIdeleSubgroup_coe _root_.GlobalClassFieldTheory.Reciprocity.rationalCyclotomicGlobalToLocalizedAlgHom_apply _root_.GlobalClassFieldTheory.Reciprocity.rationalCyclotomicGlobalToLocalizedAlgHom_primitiveRoot _root_.IsDiscreteValuationRing.addVal_ringEquiv _root_.OAI.PrimeDegreePackets.ThetaConstruction.schwartzCM_apply _root_.RayClass.primesEquiv_val_eq_natGenerator
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI
attribute [local instance] OAI.starSubalgebraCommCStarAlgebra

set_option autoImplicit false

/-!
# The conclusion of S-unit Kummer prime selection

This file proves that the selected local power conditions cut out exactly
the finite Kummer radical and records the support-enlargement consequence
used by the global reciprocity argument.
-/

open scoped NumberField Classical IsMulCommutative
open NumberField IsDedekindDomain
open KummerTheory

noncomputable section

namespace GlobalClassFieldTheory.ClassFieldAxiom

section FinitePlaces

variable {K : Type} [Field K]
    [NumberField K]

/-- The chosen primes cut out exactly the Kummer radical of `E / K`: an
enlarged `S`-unit is a local `n`-th power at every chosen
prime if and only if it has an `n`-th root in `E`. -/
theorem
    sUnitLocalPowerKernel_sUnitKummerPrimeSet_eq_comap_sUnitFiniteKummerRadical
    {Omega : Type} [Field Omega] [Algebra K Omega]
    [IsSepClosure K Omega]
    (E : IntermediateField K Omega)
    [FiniteDimensional K E] [IsGalois K E]
    [IsMulCommutative Gal(E/K)]
    (n : ℕ+)
    (hmu : (primitiveRoots (n : ℕ) K).Nonempty)
    (p v : ℕ) (hp : p.Prime) (hv : 0 < v)
    (hn : (n : ℕ) = p ^ v)
    (r : ℕ)
    (eG :
      Gal(E/K) ≃*
        (Fin r → Multiplicative (ZMod (n : ℕ))))
    (S : Finset (HeightOneSpectrum (𝓞 K))) :
    let S' :=
      enlargeByFiniteKummerRadicalSupport
        (K := K) (L := E) n hmu S
    let T :=
      sUnitKummerPrimeSet
        (K := K) (Omega := Omega) E n hmu
        p v hp hv hn r eG S
    sUnitLocalPowerKernel (K := K) n S' T =
      (sUnitFiniteKummerRadical
        (K := K) (L := E) n S').comap
          (SUnitGroup (K := K) S').subtype := by
  dsimp only
  let S' :=
    enlargeByFiniteKummerRadicalSupport
      (K := K) (L := E) n hmu S
  let T :=
    sUnitKummerPrimeSet
      (K := K) (Omega := Omega) E n hmu
      p v hp hv hn r eG S
  let N :=
    fullSUnitKummerExtension
      (K := K) (Omega := Omega) n S'
  have hnK : ((n : ℕ) : K) ≠ 0 := by
    exact_mod_cast n.ne_zero
  let : FiniteDimensional K N :=
    fullSUnitKummerExtension_finiteDimensional
      (K := K) (Omega := Omega) n hnK hmu S'
  let : IsGalois K N :=
    fullSUnitKummerExtension_isGalois
      (K := K) (Omega := Omega) n S'
  let : Algebra E N :=
    enlargedSUnitKummerAlgebra
      (K := K) (Omega := Omega) E n hmu
      (galois_pow_eq_one_of_equiv_pi_zmod
        (K := K) E n r eG) S
  let : IsScalarTower K E N := by
    infer_instance
  change
    sUnitLocalPowerKernel (K := K) n S' T =
      (sUnitFiniteKummerRadical
        (K := K) (L := E) n S').comap
          (SUnitGroup (K := K) S').subtype
  ext x
  constructor
  · intro hx
    have hxLocal :
        ∀ w : T,
          Units.map
                (algebraMap K
                  ((w : HeightOneSpectrum (𝓞 K)).adicCompletion K)).toMonoidHom
                (x : Kˣ) ∈
            (powMonoidHom (n : ℕ) :
              ((w : HeightOneSpectrum (𝓞 K)).adicCompletion K)ˣ →*
                ((w : HeightOneSpectrum (𝓞 K)).adicCompletion K)ˣ).range :=
      (mem_sUnitLocalPowerKernel_iff
        (K := K) n S' T x).mp hx
    let aFull :
        (fullSUnitKummerSubgroup (K := K) n S').1 :=
      sUnitToFullSUnitKummerSubgroup
        (K := K) n S' x
    have haN :
        (x : Kˣ) ∈
          KummerTheory.finiteKummerRadicalSubgroup
            (K := K) (L := N) n :=
      KummerTheory.le_finiteKummerRadicalSubgroup_kummerRadicalExtension
        (K := K) (Omega := Omega) n hnK
        (fullSUnitKummerSubgroup (K := K) n S').1
        aFull.property
    obtain ⟨beta, hbeta⟩ :=
      (KummerTheory.mem_finiteKummerRadicalSubgroup_iff
        (K := K) (L := N) n).mp haN
    have hbetaCoordinate
        (i : Fin
          (sUnitKummerPrimeCount
            (K := K) E n hmu r S)) :
        (beta : N) ∈
          sUnitKummerCoordinateFixedField
            (K := K) (Omega := Omega) E n hmu
            p v hp hv hn r eG S i := by
      let wi :=
        sUnitKummerChosenBasePlaces
          (K := K) (Omega := Omega) E n hmu
          p v hp hv hn r eG S i
      have hwiT : wi ∈ T := by
        change
          wi ∈
            Finset.univ.image
              (sUnitKummerChosenBasePlaces
                (K := K) (Omega := Omega) E n hmu
                p v hp hv hn r eG S)
        exact
          Finset.mem_image.mpr
            ⟨i, Finset.mem_univ i, rfl⟩
      let wT : T := ⟨wi, hwiT⟩
      have hlocal :
              Units.map
                (algebraMap K (wi.adicCompletion K)).toMonoidHom
                (x : Kˣ) ∈
            (powMonoidHom (n : ℕ) :
              (wi.adicCompletion K)ˣ →*
                (wi.adicCompletion K)ˣ).range := by
        simpa [wT, wi] using hxLocal wT
      have hfixed :
          (beta : N) ∈
            IntermediateField.fixedField
              (HilbertRamification.absoluteValueDecompositionGroup K
                (_root_.chosenFinitePlaceExtension
                  (L := N) wi).1) :=
        (KummerTheory.finitePlaceKummerRadicand_mem_nthPowerSubgroup_iff_root_mem_decompositionFixedField
            (K := K) (L := N) wi n hmu (x : Kˣ) beta hbeta).mp
          hlocal
      rw [
        ← sUnitKummerChosenDecompositionField_eq_coordinateFixedField
          (K := K) (Omega := Omega) E n hmu
          p v hp hv hn r eG S i]
      simpa only [_root_.finitePlaceDecompositionGroup] using hfixed
    let R :=
      (enlargedSUnitKummerRestrictionHom
        (K := K) (Omega := Omega) E n hmu
        (galois_pow_eq_one_of_equiv_pi_zmod
          (K := K) E n r eG) S).ker
    let Fix : Subgroup R :=
      MulAction.stabilizer R (beta : N)
    have hgeneratorFix
        (i : Fin
          (sUnitKummerPrimeCount
            (K := K) E n hmu r S)) :
        sUnitKummerKernelGenerator
            (K := K) (Omega := Omega) E n hmu
            p v hp hv hn r eG S i ∈
          Fix := by
      have hbi := hbetaCoordinate i
      change
        (beta : N) ∈
          IntermediateField.fixedField
            (Subgroup.zpowers
              ((sUnitKummerKernelGenerator
                  (K := K) (Omega := Omega) E n hmu
                  p v hp hv hn r eG S i :
                    R).1)) at hbi
      rw [IntermediateField.mem_fixedField_iff] at hbi
      have hfix :=
        hbi
          ((sUnitKummerKernelGenerator
              (K := K) (Omega := Omega) E n hmu
              p v hp hv hn r eG S i :
                R).1)
          (Subgroup.mem_zpowers
            ((sUnitKummerKernelGenerator
                (K := K) (Omega := Omega) E n hmu
                p v hp hv hn r eG S i :
                  R).1))
      rw [show Fix = MulAction.stabilizer R (beta : N) from rfl,
        MulAction.mem_stabilizer_iff]
      simpa only [
        MulAction.subgroup_smul_def,
        AlgEquiv.smul_def] using hfix
    have hspan :
        (⨆ i :
            Fin
              (sUnitKummerPrimeCount
                (K := K) E n hmu r S),
          Subgroup.zpowers
            (sUnitKummerKernelGenerator
              (K := K) (Omega := Omega) E n hmu
              p v hp hv hn r eG S i)) ≤
          Fix := by
      refine iSup_le ?_
      intro i
      exact Subgroup.zpowers_le.mpr (hgeneratorFix i)
    have hFixTop : Fix = ⊤ := by
      apply top_unique
      rw [
        ← iSup_zpowers_sUnitKummerKernelGenerator_eq_top
          (K := K) (Omega := Omega) E n hmu
          p v hp hv hn r eG S]
      exact hspan
    have hbetaKernel :
        (beta : N) ∈
          IntermediateField.fixedField
            (enlargedSUnitKummerRestrictionHom
              (K := K) (Omega := Omega) E n hmu
              (galois_pow_eq_one_of_equiv_pi_zmod
                (K := K) E n r eG) S).ker := by
      rw [IntermediateField.mem_fixedField_iff]
      intro sigma hsigma
      let sigmaR : R := ⟨sigma, hsigma⟩
      have hsigmaFix : sigmaR ∈ Fix := by
        rw [hFixTop]
        exact Subgroup.mem_top sigmaR
      have hfix :
          sigmaR • (beta : N) = (beta : N) := by
        exact
          MulAction.mem_stabilizer_iff.mp
            (show
              sigmaR ∈ MulAction.stabilizer R (beta : N) by
              simpa only [Fix] using hsigmaFix)
      simpa only [
        MulAction.subgroup_smul_def,
        AlgEquiv.smul_def] using hfix
    have hbetaEmbedded :
        (beta : N) ∈
          enlargedSUnitKummerEmbeddedExtension
            (K := K) (Omega := Omega) E n hmu
            (galois_pow_eq_one_of_equiv_pi_zmod
              (K := K) E n r eG) S := by
      rw [
        ← fixedField_enlargedSUnitKummerRestrictionHom_ker
          (K := K) (Omega := Omega) E n hmu
          (galois_pow_eq_one_of_equiv_pi_zmod
            (K := K) E n r eG) S]
      exact hbetaKernel
    change
      (beta : N) ∈ Set.range (algebraMap E N)
        at hbetaEmbedded
    obtain ⟨gamma, hgamma⟩ := hbetaEmbedded
    have hgamma_ne : gamma ≠ 0 := by
      intro hgammaZero
      apply beta.ne_zero
      calc
        (beta : N) = algebraMap E N gamma := hgamma.symm
        _ = 0 := by rw [hgammaZero, map_zero]
    let gammaUnit : Eˣ :=
      Units.mk0 gamma hgamma_ne
    change
      (x : Kˣ) ∈
        sUnitFiniteKummerRadical
          (K := K) (L := E) n S'
    apply
      (mem_sUnitFiniteKummerRadical_iff
        (K := K) (L := E) n S' (x : Kˣ)).mpr
    refine ⟨x.property, gammaUnit, ?_⟩
    apply Units.ext
    apply (algebraMap E N).injective
    change
      algebraMap E N (gamma ^ (n : ℕ)) =
        algebraMap E N
          (algebraMap K E ((x : Kˣ) : K))
    calc
      algebraMap E N (gamma ^ (n : ℕ)) =
          (beta : N) ^ (n : ℕ) := by
        rw [map_pow, hgamma]
      _ = algebraMap K N ((x : Kˣ) : K) := by
        simpa using congrArg Units.val hbeta
      _ =
          algebraMap E N
            (algebraMap K E ((x : Kˣ) : K)) := by
        rw [IsScalarTower.algebraMap_apply K E N]
  · intro hx
    change
      (x : Kˣ) ∈
        sUnitFiniteKummerRadical
          (K := K) (L := E) n S' at hx
    obtain ⟨_hxS, betaE, hbetaE⟩ :=
      (mem_sUnitFiniteKummerRadical_iff
        (K := K) (L := E) n S' (x : Kˣ)).mp hx
    let betaN : Nˣ :=
      Units.map (algebraMap E N).toMonoidHom betaE
    have hbetaN :
        betaN ^ (n : ℕ) =
          Units.map (algebraMap K N).toMonoidHom
            (x : Kˣ) := by
      calc
        betaN ^ (n : ℕ) =
            Units.map (algebraMap E N).toMonoidHom
              (betaE ^ (n : ℕ)) := by
          rw [map_pow]
        _ =
            Units.map (algebraMap E N).toMonoidHom
              (Units.map (algebraMap K E).toMonoidHom
                (x : Kˣ)) := by
          rw [hbetaE]
        _ =
            Units.map (algebraMap K N).toMonoidHom
              (x : Kˣ) := by
          apply Units.ext
          exact
            (IsScalarTower.algebraMap_apply
              K E N ((x : Kˣ) : K)).symm
    apply
      (mem_sUnitLocalPowerKernel_iff
        (K := K) n S' T x).mpr
    intro w
    have hw :
        (w : HeightOneSpectrum (𝓞 K)) ∈
          sUnitKummerPrimeSet
            (K := K) (Omega := Omega) E n hmu
            p v hp hv hn r eG S :=
      w.property
    rw [sUnitKummerPrimeSet, Finset.mem_image] at hw
    obtain ⟨i, _hi, hwi⟩ := hw
    have hbetaEmbedded :
        (betaN : N) ∈
          enlargedSUnitKummerEmbeddedExtension
            (K := K) (Omega := Omega) E n hmu
            (galois_pow_eq_one_of_equiv_pi_zmod
              (K := K) E n r eG) S := by
      change
        (betaN : N) ∈ Set.range (algebraMap E N)
      exact ⟨(betaE : E), rfl⟩
    have hbetaCoordinate :
        (betaN : N) ∈
          sUnitKummerCoordinateFixedField
            (K := K) (Omega := Omega) E n hmu
            p v hp hv hn r eG S i := by
      exact
        enlargedSUnitKummerEmbeddedExtension_le_cyclicFixedField
          (K := K) (Omega := Omega) E n hmu
          (galois_pow_eq_one_of_equiv_pi_zmod
            (K := K) E n r eG) S
          (sUnitKummerKernelGenerator
            (K := K) (Omega := Omega) E n hmu
            p v hp hv hn r eG S i)
          hbetaEmbedded
    have hbetaFixed :
        (betaN : N) ∈
          IntermediateField.fixedField
            (HilbertRamification.absoluteValueDecompositionGroup K
              (_root_.chosenFinitePlaceExtension
                (L := N)
                (sUnitKummerChosenBasePlaces
                  (K := K) (Omega := Omega) E n hmu
                  p v hp hv hn r eG S i)).1) := by
      have hdecomp :
          (betaN : N) ∈
            IntermediateField.fixedField
              (_root_.finitePlaceDecompositionGroup
                (K := K) (L := N)
                (sUnitKummerChosenBasePlaces
                  (K := K) (Omega := Omega) E n hmu
                  p v hp hv hn r eG S i)) := by
        rw [
          sUnitKummerChosenDecompositionField_eq_coordinateFixedField
            (K := K) (Omega := Omega) E n hmu
            p v hp hv hn r eG S i]
        exact hbetaCoordinate
      simpa only [_root_.finitePlaceDecompositionGroup] using hdecomp
    have hlocal :=
      (KummerTheory.finitePlaceKummerRadicand_mem_nthPowerSubgroup_iff_root_mem_decompositionFixedField
          (K := K) (L := N)
          (sUnitKummerChosenBasePlaces
            (K := K) (Omega := Omega) E n hmu
            p v hp hv hn r eG S i)
          n hmu (x : Kˣ) betaN hbetaN).mpr
        hbetaFixed
    rw [← hwi]
    exact hlocal

/-- Enlarging `S` by the radical supports preserves the idelic
factorization `I_K = I_K^S Kˣ`. -/
theorem supportedAt_sup_principalSubgroup_eq_top_of_enlargeByRadicalSupport
    {L : Type*} [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    (n : ℕ+)
    (hmu : (primitiveRoots (n : ℕ) K).Nonempty)
    (S : Finset (HeightOneSpectrum (𝓞 K)))
    (hS :
      IdeleGroup.supportedAt (K := K) (S : Set _) ⊔
        IdeleGroup.principalSubgroup K = ⊤) :
    IdeleGroup.supportedAt
          (K := K)
          (enlargeByFiniteKummerRadicalSupport
            (K := K) (L := L) n hmu S : Set _) ⊔
        IdeleGroup.principalSubgroup K =
      ⊤ := by
  apply top_unique
  rw [← hS]
  apply sup_le
  · exact
      (IdeleGroup.supportedAt_mono
        (K := K)
        (show
          (S : Set (HeightOneSpectrum (𝓞 K))) ⊆
            (enlargeByFiniteKummerRadicalSupport
              (K := K) (L := L) n hmu S : Set _) by
          intro v hv
          exact subset_enlargeByFiniteKummerRadicalSupport
            (K := K) (L := L) n hmu S hv)).trans le_sup_left
  · exact le_sup_right

end FinitePlaces

end GlobalClassFieldTheory.ClassFieldAxiom
end
end

section
-- module Solutions.OAIQ244_DUKE.GlobalClassFieldTheory_ClassFieldAxiom_SUnitLocalPowerMap
attribute [-instance] _root_.GlobalClassFieldTheory.GlobalClassFields.bigHilbertClassFieldNormSubgroup_normal _root_.GlobalClassFieldTheory.Reciprocity.infinitePlaceComplexificationOverfield_algebra _root_.GlobalClassFieldTheory.Reciprocity.infinitePlaceComplexificationOverfield_baseAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalClassFieldTheory.finiteGaloisLocalField_integerRing_moduleFinite _root_.LocalFieldTheory.Padic.padicDVR_residueField_finite _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.Padic.padicUnitFiniteFactor_finite _root_.LocalFieldTheory.localIntegerValuation_residueFinite _root_.LubinTate.padicCompletedLevelCompleteDVF_hasExtensionInstance _root_.LubinTate.padicCompletedLevelField_algebra _root_.LubinTate.padicCompletedUnramifiedFieldAlgebra _root_.LubinTate.standardLubinTateLevelCompleteDVF_hasExtensionInstance _root_.LubinTate.standardLubinTateLevelField_galFinite _root_.LubinTate.standardLubinTateLevelField_isAbelianGalois _root_.LubinTate.standardLubinTateLevelField_isMulCommutative _root_.LubinTate.standardLubinTateLevelValuationSubring_moduleFinite _root_.LubinTate.standardLubinTateUnitParameter_commGroup _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.boundedRealFields_finite _root_.OAI.PrimeDegreePackets.diagonalLogAction _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_finite_residue _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.RamificationTheory.HilbertRamification.Higher.lowerRamificationGroup.instNormal _root_.LocalClassFieldTheory.comparisonIntegerRingIsIntegralClosure _root_.LocalClassFieldTheory.normalizationIntegerRingIsIntegralClosure _root_.RamificationTheory.HilbertRamification.CompleteDVF.decompositionGroupMulSemiringAction _root_.RamificationTheory.HilbertRamification.CompleteDVF.decompositionGroupResidueFieldMulSemiringAction
attribute [-simp] _root_.GlobalClassFieldTheory.ClassFieldAxiom.sUnitEquivSupportedPrincipalIdeleSubgroup_coe _root_.GlobalClassFieldTheory.Reciprocity.rationalPrimeUnitValuationSubringUnit_coe _root_.IsDiscreteValuationRing.addVal_ringEquiv _root_.KummerTheory.chosenSimpleKummerRootCharacter_apply _root_.LocalFieldTheory.Padic.integerRingEquivPadicDVRValuationSubring_coe _root_.LocalFieldTheory.localIntegerValuationSubringEquiv_apply_coe _root_.LubinTate.LubinTateSeries.padicMultiplicativeLubinTateSeries_toPowerSeries _root_.LubinTate.LubinTateSeries.standardLubinTateSeries_toPowerSeries _root_.LubinTate.SameUniformizer.coeff_recursiveIntertwiner _root_.LubinTate.SameUniformizer.constantCoeff_inVariable _root_.LubinTate.SameUniformizer.intertwinerApproximation_zero _root_.LubinTate.SameUniformizer.standardLubinTateEndomorphism_coeff_one _root_.LubinTate.padicChangedUniformizerIntertwiner_coeff _root_.LubinTate.padicChangedUniformizerIntertwiner_coeff_one _root_.LubinTate.padicCompletedChangedStandardScalarEndomorphism_coeff_one _root_.LubinTate.padicCompletedChangedStandardScalarEndomorphism_one _root_.LubinTate.padicCompletedLevelPadicIntegerCoefficientHom_coe _root_.LubinTate.padicCompletedLevelPowerSeriesEval_C _root_.LubinTate.padicCompletedLevelPowerSeriesEval_X _root_.LubinTate.padicCompletedLevelPowerSeriesEval_coe _root_.LubinTate.padicCompletedLevelWittCoefficientHom_apply _root_.LubinTate.padicCompletedMultiplicativeScalarEndomorphismValue_one _root_.LubinTate.padicCompletedMultiplicativeScalarEndomorphism_coeff_one _root_.LubinTate.padicCompletedPrimitiveRootInteger_coe _root_.LubinTate.padicCompletedStandardScalarEndomorphismValue_one _root_.LubinTate.padicCompletedStandardScalarEndomorphism_one _root_.LubinTate.padicCompletedUnramifiedIntegerMap_coe _root_.LubinTate.padicStandardToMultiplicativeIntertwiner_coeff_one _root_.LubinTate.padicValuationSubringToCompletedUnramifiedWittRing_uniformizer _root_.LubinTate.standardLubinTateBaseUniformizerUnit_coe _root_.LubinTate.standardLubinTateChangedUniformizerUnit_coe _root_.LubinTate.standardLubinTateEndomorphismEvalAt_one _root_.LubinTate.standardLubinTateEndomorphismEvalAt_zero _root_.LubinTate.standardLubinTateEndomorphismValue_one _root_.LubinTate.standardLubinTateEndomorphismValue_zero _root_.LubinTate.standardLubinTateLevelCoefficientHom_apply _root_.LubinTate.standardLubinTateLevelGenerator_coe _root_.LubinTate.standardLubinTateLevelPowerSeriesEval_C _root_.LubinTate.standardLubinTateLevelPowerSeriesEval_X _root_.LubinTate.standardLubinTateLevelPowerSeriesEval_coe _root_.LubinTate.standardLubinTatePolynomialIterateOverSeparableClosure_eval _root_.LubinTate.standardLubinTatePolynomialIterate_derivative_eval_zero _root_.LubinTate.standardLubinTatePolynomialIterate_eval_zero _root_.LubinTate.standardLubinTatePolynomialIterate_zero _root_.LubinTate.standardLubinTatePolynomial_derivative_eval_zero _root_.LubinTate.standardLubinTatePolynomial_eval _root_.LubinTate.standardLubinTatePolynomial_toPowerSeries _root_.LubinTate.standardLubinTatePolynomial_toPowerSeries_eq_series _root_.LubinTate.standardLubinTatePrimitiveLevelAction_coe _root_.LubinTate.standardLubinTatePrimitivePointIntegerAction_one _root_.LubinTate.standardLubinTatePrimitivePointInteger_coe _root_.LubinTate.standardLubinTatePrimitivePointIterateInteger_zero _root_.LubinTate.standardLubinTatePrimitivePolynomialOverField_coeff_zero _root_.LubinTate.standardLubinTatePrimitivePolynomial_coeff_zero _root_.LubinTate.standardLubinTatePrimitiveRootAction_one _root_.LubinTate.standardLubinTateUnitFactorFieldUnit_coe _root_.LubinTate.standardLubinTateUnitParameterAlgEquiv_apply_gen _root_.LubinTate.standardLubinTateUnitParameterAlgHom_apply_gen _root_.LubinTate.standardLubinTateUnitParameterChosenRepresentative_spec _root_.LubinTate.standardLubinTateUnitParameterEquivGal_apply _root_.LubinTate.standardLubinTateUnitParameterEquivGal_inv_class_apply_gen _root_.LubinTate.standardLubinTateUnitParameterLevelRoot_coe _root_.LubinTate.standardLubinTateUnitParameterLevelRoot_one _root_.LubinTate.standardLubinTateUnitParameterRoot_class _root_.LubinTate.standardLubinTateUnitParameterToGalHom_apply _root_.OAI.PrimeDegreePackets.ThetaConstruction.schwartzCM_apply _root_.RamificationTheory.HilbertRamification.CompleteDVF.decompositionResidueAction_algebraMap _root_.RamificationTheory.HilbertRamification.CompleteDVF.decompositionResidueAction_apply _root_.RamificationTheory.HilbertRamification.CompleteDVF.galEquivDecompositionGroup_coe _root_.RamificationTheory.HilbertRamification.CompleteDVF.residueAction_apply _root_.RamificationTheory.HilbertRamification.Higher.dvfUniformizerQuotientUnit_mul_uniformizer _root_.RamificationTheory.HilbertRamification.Higher.dvfUniformizerRepresentativeHom_apply _root_.RamificationTheory.HilbertRamification.Higher.dvfValuationSubringUnitAut_apply _root_.RamificationTheory.HilbertRamification.Higher.intrinsicRamificationNumberOfUniqueExtension_one _root_.RamificationTheory.HilbertRamification.Higher.lowerRamificationGroup_neg_one _root_.RamificationTheory.HilbertRamification.Higher.mem_dvfHigherPrincipalUnitGroup_iff _root_.RamificationTheory.HilbertRamification.Higher.mem_lowerRamificationGroup_iff _root_.RamificationTheory.HilbertRamification.Higher.mem_valuationSubringDisplacementSubalgebraOfUniqueExtension_iff _root_.RamificationTheory.HilbertRamification.Higher.ramificationNumberDepthOfUniqueExtension_depth _root_.RamificationTheory.HilbertRamification.Higher.ramificationNumberOfUniqueExtension_one _root_.RamificationTheory.HilbertRamification.Higher.realRamificationIdeal_nat _root_.RamificationTheory.HilbertRamification.Higher.realRamificationIdeal_neg_one _root_.RamificationTheory.HilbertRamification.Higher.uniformizerGradedHom_mk _root_.RamificationTheory.HilbertRamification.Higher.valuationSubringAutOfUniqueExtension_apply_coe _root_.RamificationTheory.HilbertRamification.Higher.valuationSubringAutOfUniqueExtension_apply_inv_apply _root_.RamificationTheory.HilbertRamification.Higher.valuationSubringAutOfUniqueExtension_mul_apply _root_.RamificationTheory.HilbertRamification.Higher.valuationSubringAutOfUniqueExtension_one_apply _root_.RayClass.primesEquiv_val_eq_natGenerator _root_.LubinTate.standardLubinTateLevelAutomorphismIntegerRingEquiv_apply _root_.LubinTate.padicChangedUniformizerLinearCoefficient_coe _root_.LubinTate.padicMultiplicativeLevelAutomorphismIntegerRingEquiv_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI
attribute [local instance] OAI.starSubalgebraCommCStarAlgebra

set_option autoImplicit false

/-!
# S-unit localization modulo local powers

This module constructs the localization map from an S-unit group to the
finite product of local unit power classes and proves its kernel and
surjectivity properties for the Kummer prime set.
-/

open scoped NumberField Classical NNReal IsMulCommutative
open NumberField IsDedekindDomain
open AlgebraicNumberTheory.Valuations
open HilbertRamification
open KummerTheory
open LocalFieldTheory

noncomputable section

namespace GlobalClassFieldTheory.ClassFieldAxiom

variable {K : Type} [Field K] [NumberField K]

/-- For the Kummer-selected primes, localization from the enlarged `S`-unit
group onto the product of integral-unit power quotients is
surjective.  The proof compares the actual Kummer radical quotient with
`Gal(E/K)` and uses the local unit-index formula only at the end. -/
theorem sUnitLocalUnitPowerMap_sUnitKummerPrimeSet_surjective
    {Omega : Type} [Field Omega] [Algebra K Omega]
    [IsSepClosure K Omega]
    (E : IntermediateField K Omega)
    [FiniteDimensional K E] [IsGalois K E]
    [IsMulCommutative Gal(E/K)]
    (n : ℕ+)
    (hmu : (primitiveRoots (n : ℕ) K).Nonempty)
    (p v : ℕ) (hp : p.Prime) (hv : 0 < v)
    (hn : (n : ℕ) = p ^ v)
    (r : ℕ)
    (eG :
      Gal(E/K) ≃*
        (Fin r → Multiplicative (ZMod (n : ℕ))))
    (S : Finset (HeightOneSpectrum (𝓞 K))) :
    let S' :=
      enlargeByFiniteKummerRadicalSupport
        (K := K) (L := E) n hmu S
    let T :=
      sUnitKummerPrimeSet
        (K := K) (Omega := Omega) E n hmu
        p v hp hv hn r eG S
    let hST : Disjoint S' T :=
      (sUnitKummerPrimeSet_disjoint_enlargeByFiniteKummerRadicalSupport
        (K := K) (Omega := Omega) E n hmu
        p v hp hv hn r eG S).symm
    Function.Surjective
      (sUnitLocalUnitPowerMap (K := K) n S' T hST) := by
  classical
  dsimp only
  let S' :=
    enlargeByFiniteKummerRadicalSupport
      (K := K) (L := E) n hmu S
  let T :=
    sUnitKummerPrimeSet
      (K := K) (Omega := Omega) E n hmu
      p v hp hv hn r eG S
  let hST : Disjoint S' T :=
    (sUnitKummerPrimeSet_disjoint_enlargeByFiniteKummerRadicalSupport
      (K := K) (Omega := Omega) E n hmu
      p v hp hv hn r eG S).symm
  let LocalPowerTarget : Type :=
    ∀ w : T,
      (w.1.adicCompletionIntegers K)ˣ ⧸
        (powMonoidHom (n : ℕ) :
          (w.1.adicCompletionIntegers K)ˣ →*
            (w.1.adicCompletionIntegers K)ˣ).range
  let f : SUnitGroup (K := K) S' →* LocalPowerTarget :=
    sUnitLocalUnitPowerMap (K := K) n S' T hST
  let rangeF : Subgroup LocalPowerTarget :=
    MonoidHom.range
      (G := SUnitGroup (K := K) S') (N := LocalPowerTarget) f
  let SU : Subgroup Kˣ :=
    SUnitGroup (K := K) S'
  let Delta : Subgroup SU :=
    sUnitLocalPowerKernel (K := K) n S' T
  let P : Subgroup SU :=
    (powMonoidHom (n : ℕ) : SU →* SU).range
  let H : Subgroup Kˣ :=
    sUnitFiniteKummerRadical
      (K := K) (L := E) n S'
  let Npow : Subgroup Kˣ :=
    KummerTheory.unitNthPowersSubgroup K n
  let D :=
    KummerTheory.chosenFiniteKummerRadicalDatum
      (K := K) (L := E) n
  change Function.Surjective f
  have hnOne : 1 < (n : ℕ) := by
    rw [hn]
    calc
      1 < p := hp.one_lt
      _ = p ^ 1 := (pow_one p).symm
      _ ≤ p ^ v :=
        Nat.pow_le_pow_right hp.pos
          (Nat.succ_le_iff.mpr hv)
  have hDeltaEq :
      Delta = H.subgroupOf SU := by
    change
      sUnitLocalPowerKernel (K := K) n S' T =
        (sUnitFiniteKummerRadical
          (K := K) (L := E) n S').comap
            (SUnitGroup (K := K) S').subtype
    exact
      sUnitLocalPowerKernel_sUnitKummerPrimeSet_eq_comap_sUnitFiniteKummerRadical
        (K := K) (Omega := Omega) E n hmu
        p v hp hv hn r eG S
  have hP :
      P = Npow.subgroupOf SU := by
    ext x
    constructor
    · intro hx
      obtain ⟨y, hy⟩ :=
        (MonoidHom.mem_range
          (G := SU)).mp hx
      rw [powMonoidHom_apply] at hy
      change (x : Kˣ) ∈ Npow
      apply
        (KummerTheory.mem_unitNthPowersSubgroup_iff n).mpr
      refine ⟨(y : Kˣ), ?_⟩
      exact congrArg (fun z : SU => (z : Kˣ)) hy
    · intro hx
      change (x : Kˣ) ∈ Npow at hx
      obtain ⟨y, hy⟩ :=
        (KummerTheory.mem_unitNthPowersSubgroup_iff n).mp hx
      have hySU : y ∈ SU :=
        mem_sUnitGroup_of_pow_mem
          (K := K) S' n y (by
            rw [hy]
            exact x.property)
      let ySU : SU := ⟨y, hySU⟩
      apply
        (MonoidHom.mem_range
          (G := SU)).mpr
      refine ⟨ySU, ?_⟩
      rw [powMonoidHom_apply]
      apply Subtype.ext
      exact hy
  have hHle : H ≤ SU := by
    exact inf_le_left
  have hsup :
      H ⊔ Npow = D.carrier := by
    change
      (sUnitKummerSubgroup
        (K := K) (L := E) n S').1 =
          KummerTheory.finiteKummerRadicalSubgroup
            (K := K) (L := E) n
    exact
      enlargedSUnitKummerSubgroup_eq_finiteKummerRadicalSubgroup
        (K := K) (L := E) n hmu S
  let eDelta :
      Delta ⧸ P.subgroupOf Delta ≃*
        H.subgroupOf SU ⧸
          P.subgroupOf (H.subgroupOf SU) :=
    QuotientGroup.equivQuotientSubgroupOfOfEq
      rfl hDeltaEq
  let ePower :
      H.subgroupOf SU ⧸
          P.subgroupOf (H.subgroupOf SU) ≃*
        H.subgroupOf SU ⧸
          (Npow.subgroupOf SU).subgroupOf
            (H.subgroupOf SU) :=
    QuotientGroup.equivQuotientSubgroupOfOfEq
      hP rfl
  let eH :
      H.subgroupOf SU ≃* H :=
    Subgroup.subgroupOfEquivOfLe hHle
  have hmap :
      ((Npow.subgroupOf SU).subgroupOf
          (H.subgroupOf SU)).map eH =
        Npow.subgroupOf H := by
    rw [Subgroup.map_equiv_eq_comap_symm]
    rfl
  let eInside :
      H.subgroupOf SU ⧸
          (Npow.subgroupOf SU).subgroupOf
            (H.subgroupOf SU) ≃*
        H ⧸ Npow.subgroupOf H :=
    QuotientGroup.congr _ _ eH hmap
  let eSecond :
      H ⧸ Npow.subgroupOf H ≃*
        (H ⊔ Npow : Subgroup Kˣ) ⧸
          Npow.subgroupOf (H ⊔ Npow) :=
    QuotientGroup.quotientInfEquivProdNormalQuotient
      H Npow
  let eRadicalCarrier :
      (H ⊔ Npow : Subgroup Kˣ) ⧸
          Npow.subgroupOf (H ⊔ Npow) ≃*
        D.carrier ⧸ Npow.subgroupOf D.carrier :=
    QuotientGroup.equivQuotientSubgroupOfOfEq
      rfl hsup
  have hden :
      Npow.subgroupOf D.carrier =
        D.ambientNthPowersSubgroup := by
    rfl
  let eNamedRadical :
      D.carrier ⧸ Npow.subgroupOf D.carrier ≃*
        D.RadicalQuotient :=
    (QuotientGroup.quotientMulEquivOfEq hden).trans
      D.radicalQuotientMulEquiv.symm
  let : CommGroup Gal(E/K) := by
    infer_instance
  have hexponentE :
      ∀ sigma : Gal(E/K), sigma ^ (n : ℕ) = 1 :=
    galois_pow_eq_one_of_equiv_pi_zmod
      (K := K) E n r eG
  let hbase :
      KummerTheory.NthRootsOfUnityInBase
        (K := K) (L := E) n :=
    KummerTheory.nthRootsOfUnityInBase_of_primitiveRoots
      (K := K) (L := E) n hmu
  let eKummer :
      D.RadicalQuotient ≃*
        (Gal(E/K) →*
          KummerTheory.nthRootsSubgroup E (n : ℕ)) :=
    KummerTheory.finiteKummerCharacterEquiv
      n hbase
  let eDual :
      (Gal(E/K) →*
          KummerTheory.nthRootsSubgroup E (n : ℕ)) ≃*
        Gal(E/K) :=
    Classical.choice <|
      KummerTheory.finiteNthRootsCharacterDuality
        (G := Gal(E/K)) (K := K) (L := E)
        n hmu hexponentE
  let eQuotient :
      Delta ⧸ P.subgroupOf Delta ≃*
        Gal(E/K) :=
    eDelta.trans
      (ePower.trans
        (eInside.trans
          (eSecond.trans
            (eRadicalCarrier.trans
              (eNamedRadical.trans
                (eKummer.trans eDual))))))
  have hDeltaCard :
      Nat.card
          (Delta ⧸
            sUnitLocalPowerKernelNthPowers
              (K := K) n S' T) =
        (n : ℕ) ^ r := by
    change
      Nat.card (Delta ⧸ P.subgroupOf Delta) =
        (n : ℕ) ^ r
    calc
      Nat.card (Delta ⧸ P.subgroupOf Delta) =
          Nat.card Gal(E/K) :=
        Nat.card_congr eQuotient.toEquiv
      _ = (n : ℕ) ^ r := by
        rw [Nat.card_congr eG.toEquiv, Nat.card_pi]
        simp
  have hPLe : P ≤ Delta :=
    nthPowerSubgroup_le_sUnitLocalPowerKernel
      (K := K) n S' T
  have hRel :
      P.relIndex Delta = (n : ℕ) ^ r := by
    change
      Nat.card
          (Delta ⧸
            sUnitLocalPowerKernelNthPowers
              (K := K) n S' T) =
        (n : ℕ) ^ r
    exact hDeltaCard
  have hPIndex :
      P.index =
        (n : ℕ) ^ totalPlaceCard (K := K) S' := by
    change
      Nat.card
          (SUnitGroup (K := K) S' ⧸
            (powMonoidHom (n : ℕ) :
              SUnitGroup (K := K) S' →*
                SUnitGroup (K := K) S').range) =
        (n : ℕ) ^ totalPlaceCard (K := K) S'
    exact
      card_sUnit_nthPowerQuotient
        (K := K) S' n hmu
  have hIndexFactor :
      (n : ℕ) ^ r * Delta.index =
        (n : ℕ) ^ totalPlaceCard (K := K) S' := by
    rw [← hRel, ← hPIndex]
    exact Subgroup.relIndex_mul_index hPLe
  have hr :
      r ≤ totalPlaceCard (K := K) S' :=
    galoisRank_le_totalPlaceCard_enlargedS
      (K := K) (Omega := Omega) E n hnOne hmu
      r eG S
  have hsplit :
      (n : ℕ) ^ totalPlaceCard (K := K) S' =
        (n : ℕ) ^ r *
          (n : ℕ) ^
            (totalPlaceCard (K := K) S' - r) := by
    rw [← pow_add, Nat.add_sub_of_le hr]
  have hDeltaIndex :
      Delta.index =
        (n : ℕ) ^
          (totalPlaceCard (K := K) S' - r) := by
    have hcancel :
        (n : ℕ) ^ r * Delta.index =
          (n : ℕ) ^ r *
            (n : ℕ) ^
              (totalPlaceCard (K := K) S' - r) :=
      hIndexFactor.trans hsplit
    exact
      Nat.eq_of_mul_eq_mul_left
        (pow_pos n.pos r) hcancel
  have hfker :
      f.ker = Delta := by
    change
      (sUnitLocalUnitPowerMap
        (K := K) n S' T hST).ker =
          sUnitLocalPowerKernel (K := K) n S' T
    exact
      sUnitLocalUnitPowerMap_ker
        (K := K) n S' T hST
  have hRangeCard :
      Nat.card rangeF =
        (n : ℕ) ^
          (totalPlaceCard (K := K) S' - r) := by
    rw [← Subgroup.index_ker
      (G := SUnitGroup (K := K) S') (G' := LocalPowerTarget) f, hfker]
    exact hDeltaIndex
  have hLocalCard
      (w : T) :
      Nat.card
          ((w.1.adicCompletionIntegers K)ˣ ⧸
            (powMonoidHom (n : ℕ) :
              (w.1.adicCompletionIntegers K)ˣ →*
                (w.1.adicCompletionIntegers K)ˣ).range) =
        (n : ℕ) := by
    let F :=
      LocalFieldTheory.DiscreteValuationField.LocalField.ofWithZeroValuation
        (Valued.v :
          Valuation (w.1.adicCompletion K)
            (WithZero (Multiplicative ℤ)))
    let : NeZero (n : ℕ) := ⟨n.ne_zero⟩
    have hnu : Function.Surjective
        (Valued.v :
          Valuation (w.1.adicCompletion K)
            (WithZero (Multiplicative ℤ))) :=
      w.1.valuedAdicCompletion_surjective K
    have hw :
        w.1 ∈
          sUnitKummerPrimeSet
            (K := K) (Omega := Omega) E n hmu
            p v hp hv hn r eG S :=
      w.2
    rw [sUnitKummerPrimeSet, Finset.mem_image] at hw
    obtain ⟨i, _hi, hi⟩ := hw
    have hnGlobal :
        w.1.valuation K ((n : ℕ) : K) = 1 := by
      rw [← hi]
      exact
        sUnitKummerChosenBasePlaces_valuation_natCast_eq_one
          (K := K) (Omega := Omega) E n hmu
          p v hp hv hn r eG S i
    have hnatCast :
        (((n : ℕ) : K) : w.1.adicCompletion K) =
          ((n : ℕ) : w.1.adicCompletion K) := by
      change
        algebraMap K (w.1.adicCompletion K) ((n : ℕ) : K) =
          ((n : ℕ) : w.1.adicCompletion K)
      rw [map_natCast]
    have hnuN :
        Valued.v ((n : ℕ) : w.1.adicCompletion K) = 1 := by
      rw [← hnatCast,
        HeightOneSpectrum.valuedAdicCompletion_eq_valuation']
      exact hnGlobal
    have hnuNF :
        F.valuation ((n : ℕ) : w.1.adicCompletion K) = 1 := by
      dsimp only [F]
      unfold
        LocalFieldTheory.DiscreteValuationField.LocalField.ofWithZeroValuation
      unfold
        LocalFieldTheory.DiscreteValuationField.LocalField.coherentWithZeroMultiplicativeIntGroup
      exact hnuN
    have hpnd :
        ¬ F.residueCharacteristic ∣ (n : ℕ) := by
      rw [←
        F.valuation_natCast_lt_one_iff_residueCharacteristic_dvd]
      rw [hnuNF]
      exact lt_irrefl 1
    let :
        Fact
          (Nat.Coprime (n : ℕ)
            F.residueCharacteristic) :=
      ⟨(F.residueCharacteristic_prime.coprime_iff_not_dvd.mpr
        hpnd).symm⟩
    let eValuationSubringUnits :
        F.valuationSubringˣ ≃*
          (w.1.adicCompletionIntegers K)ˣ := by
      exact MulEquiv.refl ((w.1.adicCompletionIntegers K)ˣ)
    have hindexPackaged :
        Nat.card
            (F.valuationSubringˣ ⧸
              (powMonoidHom (n : ℕ) :
                F.valuationSubringˣ →* F.valuationSubringˣ).range) =
          Nat.card
            ((powMonoidHom (n : ℕ) :
              (w.1.adicCompletion K)ˣ →*
                (w.1.adicCompletion K)ˣ).ker) := by
      simpa only [F] using
        LocalFieldTheory.DiscreteValuationField.LocalField.mixed_unitIndex_of_coprime
          (Valued.v :
            Valuation (w.1.adicCompletion K)
              (WithZero (Multiplicative ℤ)))
          hnu (n := (n : ℕ))
    have hindex :
        Nat.card
            ((w.1.adicCompletionIntegers K)ˣ ⧸
              (powMonoidHom (n : ℕ) :
                (w.1.adicCompletionIntegers K)ˣ →*
                  (w.1.adicCompletionIntegers K)ˣ).range) =
          Nat.card
            ((powMonoidHom (n : ℕ) :
              (w.1.adicCompletion K)ˣ →*
                (w.1.adicCompletion K)ˣ).ker) := by
      calc
        Nat.card
            ((w.1.adicCompletionIntegers K)ˣ ⧸
              (powMonoidHom (n : ℕ) :
                (w.1.adicCompletionIntegers K)ˣ →*
                  (w.1.adicCompletionIntegers K)ˣ).range) =
            Nat.card
              (F.valuationSubringˣ ⧸
                (powMonoidHom (n : ℕ) :
                  F.valuationSubringˣ →* F.valuationSubringˣ).range) := by
          exact Nat.card_congr
            (LocalFieldTheory.nthPowerQuotientEquivOfMulEquiv
              (w.1.adicCompletionIntegers K)ˣ
              F.valuationSubringˣ
              (n : ℕ)
              eValuationSubringUnits.symm).toEquiv
        _ = Nat.card
              ((powMonoidHom (n : ℕ) :
                (w.1.adicCompletion K)ˣ →*
                  (w.1.adicCompletion K)ˣ).ker) :=
          hindexPackaged
    have hroots :
        Nat.card
            ((powMonoidHom (n : ℕ) :
              (w.1.adicCompletion K)ˣ →*
                (w.1.adicCompletion K)ˣ).ker) =
          (n : ℕ) := by
      rw [
        LocalFieldTheory.powMonoidHom_ker_units_eq_rootsOfUnity]
      obtain ⟨zeta, hzeta⟩ := hmu
      have hzetaPrimitive :
          IsPrimitiveRoot zeta (n : ℕ) :=
        (mem_primitiveRoots n.pos).mp hzeta
      exact
        (hzetaPrimitive.map_of_injective
          (algebraMap K
            (w.1.adicCompletion K)).injective).card_rootsOfUnity
    simpa only [hroots] using hindex
  have hTcard :
      T.card =
        sUnitKummerPrimeCount
          (K := K) E n hmu r S :=
    sUnitKummerPrimeSet_card
      (K := K) (Omega := Omega) E n hmu
      p v hp hv hn r eG S
  have hTargetCard :
      Nat.card
          (∀ w : T,
            (w.1.adicCompletionIntegers K)ˣ ⧸
              (powMonoidHom (n : ℕ) :
                (w.1.adicCompletionIntegers K)ˣ →*
                  (w.1.adicCompletionIntegers K)ˣ).range) =
        (n : ℕ) ^
          (totalPlaceCard (K := K) S' - r) := by
    rw [Nat.card_pi]
    calc
      (∏ w : T,
          Nat.card
            ((w.1.adicCompletionIntegers K)ˣ ⧸
              (powMonoidHom (n : ℕ) :
                (w.1.adicCompletionIntegers K)ˣ →*
                  (w.1.adicCompletionIntegers K)ˣ).range)) =
          ∏ _w : T, (n : ℕ) := by
        apply Finset.prod_congr rfl
        intro w _
        exact hLocalCard w
      _ = (n : ℕ) ^ T.card := by
        simp
      _ =
          (n : ℕ) ^
            (totalPlaceCard (K := K) S' - r) := by
        rw [hTcard]
        rfl
  let : Finite rangeF :=
    Nat.finite_of_card_ne_zero (by
      rw [hRangeCard]
      exact pow_ne_zero _ n.ne_zero)
  have hRangeTop :
      rangeF = ⊤ :=
    Subgroup.eq_top_of_card_eq rangeF
      (hRangeCard.trans hTargetCard.symm)
  exact
    (MonoidHom.range_eq_top
      (G := SUnitGroup (K := K) S') (N := LocalPowerTarget) (f := f)).mp hRangeTop

end GlobalClassFieldTheory.ClassFieldAxiom
end
end

section
-- module Solutions.OAIQ244_DUKE.GlobalClassFieldTheory_ClassFieldAxiom_IdelePowerLocalUnitNormContainment
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 400000
attribute [-instance] _root_.GlobalClassFieldTheory.GlobalClassFields.ConductorialSubgroup.finiteIndex _root_.GlobalClassFieldTheory.GlobalClassFields.bigHilbertClassFieldNormSubgroup_normal _root_.GlobalClassFieldTheory.GlobalClassFields.smallHilbertClassFieldNormSubgroupFiniteIndex _root_.GlobalClassFieldTheory.Reciprocity.infinitePlaceComplexificationOverfield_algebra _root_.GlobalClassFieldTheory.Reciprocity.infinitePlaceComplexificationOverfield_baseAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.KummerTheory.primeCyclotomicBaseIsGalois _root_.LocalClassFieldTheory.finiteGaloisLocalField_integerRing_moduleFinite _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LubinTate.padicCompletedLevelField_algebra _root_.LubinTate.padicCompletedLevelField_isGalois _root_.LubinTate.padicCompletedUnramifiedFieldAlgebra _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.diagonalLogAction _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.LocalClassFieldTheory.comparisonIntegerRingIsIntegralClosure _root_.LocalClassFieldTheory.normalizationIntegerRingIsIntegralClosure _root_.cyclicPrimeDegreeIntermediate_isGalois
attribute [-simp] _root_.GlobalClassFieldTheory.ClassFieldAxiom.actualPushoutNormQuotientMap_mk _root_.GlobalClassFieldTheory.ClassFieldAxiom.hasseNormDiagonal_mk _root_.GlobalClassFieldTheory.ClassFieldAxiom.sUnitEquivSupportedPrincipalIdeleSubgroup_coe _root_.GlobalClassFieldTheory.GlobalClassFields.ConductorialSubgroup.ideleClassQuotientEquivOfNarrowFiniteConductorsEqOfRayClassGroupCardsEqQuotientCards_mk _root_.GlobalClassFieldTheory.GlobalClassFields.ConductorialSubgroup.mem_fullConductorInfinitePart_iff _root_.GlobalClassFieldTheory.GlobalClassFields.ConductorialSubgroup.narrowFiniteConductorRayClassGroupEquivQuotientOfCardEq_mk _root_.GlobalClassFieldTheory.GlobalClassFields.ConductorialSubgroup.narrowFiniteConductorRayClassGroupToQuotient_mk _root_.GlobalClassFieldTheory.GlobalClassFields.bigHilbertClassFieldQuotientEquivNarrowClassGroup_mk _root_.GlobalClassFieldTheory.GlobalClassFields.bigHilbertClassFieldQuotientToSmallHilbertClassFieldQuotient_mk _root_.GlobalClassFieldTheory.GlobalClassFields.realSignToBigHilbertClassFieldQuotient_apply _root_.GlobalClassFieldTheory.GlobalClassFields.realSignToNarrowClassKernel_apply _root_.GlobalClassFieldTheory.GlobalClassFields.smallHilbertClassFieldQuotientEquivClassGroup_mk _root_.GlobalClassFieldTheory.Reciprocity.globalNormClassFromIdele_principalIdele _root_.GlobalClassFieldTheory.Reciprocity.infinitePlaceGlobalArtinMonoidHom_finitePlaceIdele _root_.IdeleGroup.finitePlaceIdele_finiteComponent_of_ne _root_.IdeleGroup.finitePlaceIdele_finiteComponent_same _root_.IdeleGroup.finitePlaceIdele_infiniteComponent _root_.IdeleGroup.ideleNormContinuousMonoidHom_apply _root_.IdeleGroup.infinitePlaceIdeleContinuous_apply _root_.IdeleGroup.infinitePlaceIdele_finiteComponent _root_.IdeleGroup.infinitePlaceIdele_infiniteComponent_of_ne _root_.IdeleGroup.infinitePlaceIdele_infiniteComponent_same _root_.IsDiscreteValuationRing.addVal_ringEquiv _root_.OAI.PrimeDegreePackets.ThetaConstruction.schwartzCM_apply _root_.RayClass.primesEquiv_val_eq_natGenerator _root_.RayClass.signToNarrow_mk _root_.RelativeIdeleGroup.relativeFinitePlaceIdele_finiteComponent_of_ne _root_.RelativeIdeleGroup.relativeFinitePlaceIdele_finiteComponent_same _root_.RelativeIdeleGroup.relativeFinitePlaceIdele_infiniteComponent _root_.RelativeIdeleGroup.relativeInfinitePlaceIdele_finiteComponent _root_.RelativeIdeleGroup.relativeInfinitePlaceIdele_infiniteComponent_of_ne _root_.RelativeIdeleGroup.relativeInfinitePlaceIdele_infiniteComponent_same
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI
attribute [local instance] OAI.starSubalgebraCommCStarAlgebra

set_option autoImplicit false

/-!
# Norm containment for idele power-local-unit subgroups

This module packages the finite-place local norm conditions and proves the
global norm containment and principal-intersection identity used in the
idele-class norm-index argument.
-/

open scoped NumberField Classical NNReal IsMulCommutative
open NumberField IsDedekindDomain
open AlgebraicNumberTheory.Valuations
open HilbertRamification
open KummerTheory
open LocalFieldTheory

noncomputable section

namespace GlobalClassFieldTheory.ClassFieldAxiom

variable {K : Type*} [Field K] [NumberField K]

/-- Under the concrete splitting and unramifiedness conditions, every finite
component of `h(S,T)` is an actual local norm. -/
theorem idelePowerLocalUnitSubgroup_le_allFinitePlaceLocalNormCondition
    {K L : Type}
    [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    (n : ℕ+) (r : ℕ)
    (eG :
      (L ≃ₐ[K] L) ≃*
        (Fin r → Multiplicative (ZMod (n : ℕ))))
    (S T : Finset (HeightOneSpectrum (𝓞 K)))
    (hT :
      ∀ v, v ∈ T →
        _root_.FinitePlaceSplitsCompletely
          (K := K) (L := L) v)
    (hAway :
      ∀ v, v ∉ S ∪ T →
        _root_.ChosenFinitePlaceIsUnramified
          (K := K) (L := L) v) :
    idelePowerLocalUnitSubgroup (K := K) n S T ≤
      allFinitePlaceLocalNormCondition
        (K := K) (L := L) := by
  intro a ha
  rw [allFinitePlaceLocalNormCondition]
  apply Subgroup.mem_iInf.mpr
  intro v
  by_cases hv : v ∈ S ∪ T
  · rcases Finset.mem_union.mp hv with hvS | hvT
    · apply
        nthPowerSubgroup_le_chosenFinitePlaceLocalNormSubgroup
          (K := K) (L := L) n r eG v
      exact
        ((mem_idelePowerLocalUnitSubgroup_iff
          (K := K) n S T a).mp ha).2.1 v hvS
    · rw [
        _root_.chosenFinitePlaceLocalNormSubgroup_eq_top_of_splitsCompletely
          (K := K) (L := L) v (hT v hvT)]
      exact Subgroup.mem_top _
  · apply
      _root_.adicCompletionIntegerUnits_le_chosenFinitePlaceLocalNormSubgroup
        (K := K) (L := L) v (hAway v hv)
    exact
      ((mem_idelePowerLocalUnitSubgroup_iff
        (K := K) n S T a).mp ha).2.2 v hv

/-- Equality between the power/local-unit subgroup and the everywhere-local
norm condition for the Kummer-selected prime set.  Starting from an arbitrary
prescribed finite set `S`, the construction first adjoins a sufficiently large
idelic support and the support of the exponent, then performs the chosen
finite Kummer-radical enlargement before choosing `T`. -/
theorem
    principalIdelePowerLocalUnitSubgroup_eq_sUnitNthPowersInField_sUnitKummerPrimeSet
    {K : Type} [Field K] [NumberField K]
    {Omega : Type} [Field Omega] [Algebra K Omega]
    [IsSepClosure K Omega]
    (E : IntermediateField K Omega)
    [FiniteDimensional K E] [IsGalois K E]
    [IsMulCommutative Gal(E/K)]
    (n : ℕ+)
    (hmu : (primitiveRoots (n : ℕ) K).Nonempty)
    (p v : ℕ) (hp : p.Prime) (hv : 0 < v)
    (hn : (n : ℕ) = p ^ v)
    (r : ℕ)
    (eG :
      Gal(E/K) ≃*
        (Fin r → Multiplicative (ZMod (n : ℕ))))
    (S : Finset (HeightOneSpectrum (𝓞 K))) :
    let hnK : ((n : ℕ) : K) ≠ 0 := by
      exact_mod_cast n.ne_zero
    let nUnit : Kˣ :=
      Units.mk0 ((n : ℕ) : K) hnK
    let S₀ :=
      (S ∪ IdeleGroup.sufficientlyLargeFiniteSet (K := K)) ∪
        chosenUnitFiniteSupport (K := K) nUnit
    let S' :=
      enlargeByFiniteKummerRadicalSupport
        (K := K) (L := E) n hmu S₀
    let T :=
      sUnitKummerPrimeSet
        (K := K) (Omega := Omega) E n hmu
        p v hp hv hn r eG S₀
    principalIdelePowerLocalUnitSubgroup (K := K) n S' T =
      sUnitNthPowersInField (K := K) n (S' ∪ T) := by
  classical
  dsimp only
  let hnK : ((n : ℕ) : K) ≠ 0 := by
    exact_mod_cast n.ne_zero
  let nUnit : Kˣ :=
    Units.mk0 ((n : ℕ) : K) hnK
  let S₀ :=
    (S ∪ IdeleGroup.sufficientlyLargeFiniteSet (K := K)) ∪
      chosenUnitFiniteSupport (K := K) nUnit
  let S' :=
    enlargeByFiniteKummerRadicalSupport
      (K := K) (L := E) n hmu S₀
  let T :=
    sUnitKummerPrimeSet
      (K := K) (Omega := Omega) E n hmu
      p v hp hv hn r eG S₀
  let hST : Disjoint S' T :=
    (sUnitKummerPrimeSet_disjoint_enlargeByFiniteKummerRadicalSupport
      (K := K) (Omega := Omega) E n hmu
      p v hp hv hn r eG S₀).symm
  change
    principalIdelePowerLocalUnitSubgroup (K := K) n S' T =
      sUnitNthPowersInField (K := K) n (S' ∪ T)
  have hSurj :
      Function.Surjective
        (sUnitLocalUnitPowerMap (K := K) n S' T hST) := by
    simpa only [S', T, hST] using
      sUnitLocalUnitPowerMap_sUnitKummerPrimeSet_surjective
        (K := K) (Omega := Omega) E n hmu
        p v hp hv hn r eG S₀
  have hCanonical :
      (IdeleGroup.sufficientlyLargeFiniteSet (K := K) :
          Set (HeightOneSpectrum (𝓞 K))) ⊆
        (S₀ : Set (HeightOneSpectrum (𝓞 K))) := by
    intro w hw
    exact
      Finset.mem_union_left _
        (Finset.mem_union_right _ hw)
  have hS₀ :
      IdeleGroup.supportedAt
            (K := K) (S₀ : Set (HeightOneSpectrum (𝓞 K))) ⊔
          IdeleGroup.principalSubgroup K =
        ⊤ := by
    apply top_unique
    rw [
      ← IdeleGroup.supportedAt_sup_principalSubgroup_eq_top
        (K := K)]
    exact
      sup_le_sup
        (IdeleGroup.supportedAt_mono
          (K := K) hCanonical)
        le_rfl
  have hLarge :
      IdeleGroup.supportedAt
            (K := K) (S' : Set (HeightOneSpectrum (𝓞 K))) ⊔
          IdeleGroup.principalSubgroup K =
        ⊤ := by
    simpa only [S'] using
      supportedAt_sup_principalSubgroup_eq_top_of_enlargeByRadicalSupport
        (K := K) (L := E) n hmu S₀ hS₀
  apply le_antisymm
  · intro b hb
    have hbData :=
      (mem_idelePowerLocalUnitSubgroup_iff
        (K := K) n S' T
        (IdeleGroup.principalIdele K b)).mp hb
    have hbSUnit :
        b ∈ SUnitGroup (K := K) (S' ∪ T) :=
      principalIdelePowerLocalUnitSubgroup_le_sUnitGroup
        (K := K) n S' T hb
    let M :=
      KummerTheory.chosenSimpleKummerExtension K n hnK b
    let : FiniteDimensional K M :=
      KummerTheory.chosenSimpleKummerExtension_finiteDimensional
        K n hnK b
    let : IsAbelianGalois K M :=
      KummerTheory.chosenSimpleKummerExtension_isAbelianGalois
        K n hnK hmu b
    let : NumberField M :=
      NumberField.of_module_finite K M
    let : (RelativeIdeleGroup.principalSubgroup K M).Normal :=
      ⟨fun n hn g => by
        have hconj : g * n * g⁻¹ = n := by
          rw [mul_comm g n, mul_assoc, mul_inv_cancel, mul_one]
        rwa [hconj]⟩
    have hSplitS :
        ∀ w : HeightOneSpectrum (𝓞 K), w ∈ S' →
          _root_.FinitePlaceSplitsCompletely
            (K := K) (L := M) w := by
      intro w hw
      have hbLocal := hbData.2.1 w hw
      have hprincipal :
          IdeleGroup.finiteComponent w
              (IdeleGroup.principalIdele K b) =
            Units.map
              (algebraMap K (w.adicCompletion K)).toMonoidHom b := by
        apply Units.ext
        rfl
      rw [hprincipal] at hbLocal
      simpa only [M] using
        KummerTheory.chosenSimpleKummerExtension_finitePlaceSplitsCompletely_of_mem_nthPowerSubgroup
          (K := K) n hnK hmu b w hbLocal
    have hInfiniteTop :
        ∀ w : InfinitePlace K,
          _root_.infiniteTensorNormSubgroup
            (K := K) (L := M) w = ⊤ := by
      intro w
      have hbLocal := hbData.1 w
      have hprincipal :
          IdeleGroup.infiniteComponent w
              (IdeleGroup.principalIdele K b) =
            Units.map
              (algebraMap K w.Completion).toMonoidHom b := by
        apply Units.ext
        rfl
      rw [hprincipal] at hbLocal
      simpa only [M] using
        KummerTheory.chosenSimpleKummerExtension_infiniteTensorNormSubgroup_eq_top_of_mem_nthPowerSubgroup
          (K := K) n hnK hmu b w hbLocal
    have hAway :
        ∀ w : HeightOneSpectrum (𝓞 K), w ∉ S' ∪ T →
          _root_.ChosenFinitePlaceIsUnramified
            (K := K) (L := M) w := by
      intro w hw
      have hbVal :
          w.valuation K (b : K) = 1 :=
        (mem_SUnitGroup_iff
          (K := K) (S' ∪ T) b).mp hbSUnit w hw
      have hwS' : w ∉ S' := by
        intro hwS'
        exact hw (Finset.mem_union_left T hwS')
      have hwSupport :
          w ∉ chosenUnitFiniteSupport (K := K) nUnit := by
        intro hwSupport
        apply hwS'
        exact
          subset_enlargeByFiniteKummerRadicalSupport
            (K := K) (L := E) n hmu S₀
            (Finset.mem_union_right _ hwSupport)
      have hnUnitVal :
          w.valuation K (nUnit : K) = 1 :=
        (mem_SUnitGroup_iff
          (K := K)
          (chosenUnitFiniteSupport (K := K) nUnit) nUnit).mp
            (mem_sUnitGroup_chosenUnitFiniteSupport
              (K := K) nUnit)
            w hwSupport
      have hnVal :
          w.valuation K ((n : ℕ) : K) = 1 := by
        change w.valuation K ((n : ℕ) : K) = 1 at hnUnitVal
        exact hnUnitVal
      simpa only [M] using
        KummerTheory.chosenSimpleKummerExtension_chosenFinitePlaceIsUnramified_of_valuation_eq_one
          (K := K) n hnK hmu b w hbVal hnVal
    have hNormTop :
        (RelativeIdeleGroup.Cohomology.ideleClassNorm K M).range = ⊤ := by
      apply top_unique
      intro c _
      obtain ⟨a, rfl⟩ :=
        QuotientGroup.mk'_surjective
          (IdeleGroup.principalSubgroup K) c
      have ha :
          a ∈
            IdeleGroup.supportedAt
                (K := K)
                (S' : Set (HeightOneSpectrum (𝓞 K))) ⊔
              IdeleGroup.principalSubgroup K := by
        rw [hLarge]
        exact Subgroup.mem_top a
      rcases Subgroup.mem_sup.mp ha with
        ⟨u, hu, q, hq, huq⟩
      have hT_not_mem_S (w : T) : w.1 ∉ S' := by
        intro hwS
        exact (Finset.disjoint_left.mp hST) hwS w.2
      let uLocalUnit (w : T) :
          (w.1.adicCompletionIntegers K)ˣ :=
        (w.1.adicCompletionIntegers K).toSubmonoid.unitsEquivUnitsType
          ⟨IdeleGroup.finiteComponent w.1 u,
            (IdeleGroup.mem_supportedAt_iff
              (K := K)
              (S' : Set (HeightOneSpectrum (𝓞 K))) u).mp
                hu w.1 (by simpa using hT_not_mem_S w)⟩
      let target :
          ∀ w : T,
            (w.1.adicCompletionIntegers K)ˣ ⧸
              (powMonoidHom (n : ℕ) :
                (w.1.adicCompletionIntegers K)ˣ →*
                  (w.1.adicCompletionIntegers K)ˣ).range :=
        fun w =>
          QuotientGroup.mk'
            (powMonoidHom (n : ℕ) :
              (w.1.adicCompletionIntegers K)ˣ →*
                (w.1.adicCompletionIntegers K)ˣ).range
            (uLocalUnit w)
      obtain ⟨s, hs⟩ := hSurj target
      have hsSupported :
          IdeleGroup.principalIdele K (s : Kˣ) ∈
            IdeleGroup.supportedAt
              (K := K)
              (S' : Set (HeightOneSpectrum (𝓞 K))) :=
        (_root_.principalIdele_mem_supportedAt_iff_sUnit
          (L := K) S' (s : Kˣ)).2 s.2
      let sLocalUnit (w : T) :
          (w.1.adicCompletionIntegers K)ˣ :=
        (w.1.adicCompletionIntegers K).toSubmonoid.unitsEquivUnitsType
          ⟨IdeleGroup.finiteComponent w.1
              (IdeleGroup.principalIdele K (s : Kˣ)),
            (IdeleGroup.mem_supportedAt_iff
              (K := K)
              (S' : Set (HeightOneSpectrum (𝓞 K)))
              (IdeleGroup.principalIdele K (s : Kˣ))).mp
                hsSupported w.1 (by simpa using hT_not_mem_S w)⟩
      let d : IdeleGroup K :=
        u * (IdeleGroup.principalIdele K (s : Kˣ))⁻¹
      have hdSupported :
          d ∈
            IdeleGroup.supportedAt
              (K := K)
              (S' : Set (HeightOneSpectrum (𝓞 K))) := by
        dsimp only [d]
        exact
          (IdeleGroup.supportedAt
            (K := K)
            (S' : Set (HeightOneSpectrum (𝓞 K)))).mul_mem
              hu
              ((IdeleGroup.supportedAt
                (K := K)
                (S' : Set (HeightOneSpectrum (𝓞 K)))).inv_mem
                  hsSupported)
      have hTpower (w : T) :
          IdeleGroup.finiteComponent w.1 d ∈
            (powMonoidHom (n : ℕ) :
              (w.1.adicCompletion K)ˣ →*
                (w.1.adicCompletion K)ˣ).range := by
        have hw := congrFun hs w
        change
          QuotientGroup.mk'
              (powMonoidHom (n : ℕ) :
                (w.1.adicCompletionIntegers K)ˣ →*
                  (w.1.adicCompletionIntegers K)ˣ).range
              (sLocalUnit w) =
            QuotientGroup.mk'
              (powMonoidHom (n : ℕ) :
                (w.1.adicCompletionIntegers K)ˣ →*
                  (w.1.adicCompletionIntegers K)ˣ).range
              (uLocalUnit w) at hw
        have hIntegerPower :
            uLocalUnit w / sLocalUnit w ∈
              (powMonoidHom (n : ℕ) :
                (w.1.adicCompletionIntegers K)ˣ →*
                  (w.1.adicCompletionIntegers K)ˣ).range :=
          (QuotientGroup.eq_iff_div_mem).mp hw.symm
        let toField :
            (w.1.adicCompletionIntegers K)ˣ →*
              (w.1.adicCompletion K)ˣ :=
          Units.map
            (w.1.adicCompletionIntegers K).subtype.toMonoidHom
        obtain ⟨z, hz⟩ := hIntegerPower
        have hFieldPower :
            toField (uLocalUnit w / sLocalUnit w) ∈
              (powMonoidHom (n : ℕ) :
                (w.1.adicCompletion K)ˣ →*
                  (w.1.adicCompletion K)ˣ).range := by
          refine ⟨toField z, ?_⟩
          change
            (toField z) ^ (n : ℕ) =
              toField (uLocalUnit w / sLocalUnit w)
          simpa only [powMonoidHom_apply, map_pow] using
            congrArg toField hz
        have huToField :
            toField (uLocalUnit w) =
              IdeleGroup.finiteComponent w.1 u := by
          apply Units.ext
          rfl
        have hsToField :
            toField (sLocalUnit w) =
              IdeleGroup.finiteComponent w.1
                (IdeleGroup.principalIdele K (s : Kˣ)) := by
          apply Units.ext
          rfl
        simpa only [d, div_eq_mul_inv, map_mul, map_inv,
          huToField, hsToField] using hFieldPower
      have hInfinite :
          ∀ w : InfinitePlace K,
            IdeleGroup.infiniteComponent w d ∈
              _root_.infiniteTensorNormSubgroup
                (K := K) (L := M) w := by
        intro w
        rw [hInfiniteTop w]
        exact Subgroup.mem_top _
      have hFinite :
          ∀ w : HeightOneSpectrum (𝓞 K),
            IdeleGroup.finiteComponent w d ∈
              (localTensorNorm
                (K := K) (L := M) w).range := by
        intro w
        rw [
          _root_.finitePlaceLocalTensorNorm_range_eq_chosenLocalNormSubgroup
            (K := K) (L := M) w]
        by_cases hwS : w ∈ S'
        · rw [
            _root_.chosenFinitePlaceLocalNormSubgroup_eq_top_of_splitsCompletely
              (K := K) (L := M) w (hSplitS w hwS)]
          exact Subgroup.mem_top _
        · by_cases hwT : w ∈ T
          · have hle :
                (powMonoidHom (n : ℕ) :
                    (w.adicCompletion K)ˣ →*
                      (w.adicCompletion K)ˣ).range ≤
                  _root_.chosenFinitePlaceLocalNormSubgroup
                    (K := K) (L := M) w := by
              simpa only [M] using
                chosenSimpleKummerNthPowerSubgroup_le_chosenFinitePlaceLocalNormSubgroup
                  (K := K) n hnK hmu b w
            exact hle (hTpower ⟨w, hwT⟩)
          · have hwAway : w ∉ S' ∪ T := by
              intro hw
              rcases Finset.mem_union.mp hw with hw | hw
              · exact hwS hw
              · exact hwT hw
            apply
              _root_.adicCompletionIntegerUnits_le_chosenFinitePlaceLocalNormSubgroup
                (K := K) (L := M) w (hAway w hwAway)
            exact
              (IdeleGroup.mem_supportedAt_iff
                (K := K)
                (S' : Set (HeightOneSpectrum (𝓞 K))) d).mp
                  hdSupported w (by simpa using hwS)
      have hdNorm :
          d ∈ (RelativeIdeleGroup.norm K M).range :=
        (_root_.mem_relativeIdeleNorm_range_iff_localTensorNorms
          (K := K) (L := M) d).2
            ⟨hInfinite, hFinite⟩
      obtain ⟨z, hz⟩ := hdNorm
      refine
        ⟨QuotientGroup.mk'
            (RelativeIdeleGroup.principalSubgroup K M) z, ?_⟩
      rw [RelativeIdeleGroup.Cohomology.ideleClassNorm_mk, hz]
      change
        QuotientGroup.mk'
            (IdeleGroup.principalSubgroup K) d =
          QuotientGroup.mk'
            (IdeleGroup.principalSubgroup K) a
      have hqOne :
          QuotientGroup.mk'
              (IdeleGroup.principalSubgroup K) q = 1 :=
        (QuotientGroup.eq_one_iff q).mpr hq
      have hsOne :
          QuotientGroup.mk'
              (IdeleGroup.principalSubgroup K)
              (IdeleGroup.principalIdele K (s : Kˣ)) =
            1 :=
        (QuotientGroup.eq_one_iff
          (IdeleGroup.principalIdele K (s : Kˣ))).mpr
            ⟨(s : Kˣ), rfl⟩
      change
        QuotientGroup.mk'
            (IdeleGroup.principalSubgroup K)
            (u * (IdeleGroup.principalIdele K (s : Kˣ))⁻¹) =
          QuotientGroup.mk'
            (IdeleGroup.principalSubgroup K) a
      rw [← huq, map_mul, map_inv, hsOne, map_mul, hqOne]
      simp
    let : IsCyclic (M ≃ₐ[K] M) := by
      simpa only [M] using
        KummerTheory.chosenSimpleKummerExtension_isCyclic
          K n hnK hmu b
    obtain ⟨sigma, hsigma⟩ :=
      IsCyclic.exists_generator (α := M ≃ₐ[K] M)
    have hLower :
        Module.finrank K M ≤
          (RelativeIdeleGroup.Cohomology.ideleClassNorm K M).range.index :=
      Cohomology.finrank_le_ideleClassNorm_index
        (K := K) (L := M) sigma hsigma
    have hDegreeLe :
        Module.finrank K M ≤ 1 := by
      simpa only [hNormTop, Subgroup.index_top] using hLower
    have hDegree :
        Module.finrank K M = 1 :=
      le_antisymm hDegreeLe Module.finrank_pos
    have hAlgMap :
        Function.Bijective (algebraMap K M) :=
      (Algebra.finrank_eq_one_iff_bijective_algebraMap).mp
        hDegree
    let beta : Mˣ :=
      KummerTheory.chosenSimpleKummerRootUnit K n hnK b
    have hbeta :
        beta ^ (n : ℕ) =
          Units.map (algebraMap K M).toMonoidHom b := by
      simpa only [M, beta] using
        KummerTheory.chosenSimpleKummerRootUnit_pow K n hnK b
    obtain ⟨x, hx⟩ :=
      hAlgMap.2 (beta : M)
    have hx_ne : x ≠ 0 := by
      intro hx_zero
      apply beta.ne_zero
      calc
        (beta : M) = algebraMap K M x := hx.symm
        _ = 0 := by rw [hx_zero, map_zero]
    let xUnit : Kˣ :=
      Units.mk0 x hx_ne
    have hbPower :
        b ∈ (powMonoidHom (n : ℕ) : Kˣ →* Kˣ).range := by
      apply
        (MonoidHom.mem_range
          (G := Kˣ)).mpr
      refine ⟨xUnit, ?_⟩
      rw [powMonoidHom_apply]
      apply Units.ext
      apply (algebraMap K M).injective
      change
        algebraMap K M (x ^ (n : ℕ)) =
          algebraMap K M (b : K)
      calc
        algebraMap K M (x ^ (n : ℕ)) =
            (beta : M) ^ (n : ℕ) := by
          rw [map_pow, hx]
        _ = algebraMap K M (b : K) := by
          simpa using congrArg Units.val hbeta
    exact
      (mem_sUnitNthPowersInField_iff
        (K := K) n (S' ∪ T) b).2
          ⟨hbSUnit, hbPower⟩
  · exact
      sUnitNthPowersInField_le_principalIdelePowerLocalUnitSubgroup
        (K := K) n S' T


end GlobalClassFieldTheory.ClassFieldAxiom
end
end

section
-- module Solutions.OAIQ244_DUKE.GlobalClassFieldTheory_ClassFieldAxiom_IdeleClassPowerLocalUnitQuotient_NormContainment
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 400000
attribute [-instance] _root_.GlobalClassFieldTheory.GlobalClassFields.ConductorialSubgroup.finiteIndex _root_.GlobalClassFieldTheory.GlobalClassFields.bigHilbertClassFieldNormSubgroup_normal _root_.GlobalClassFieldTheory.GlobalClassFields.smallHilbertClassFieldNormSubgroupFiniteIndex _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalClassFieldTheory.finiteGaloisLocalField_integerRing_moduleFinite _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LubinTate.padicCompletedLevelField_algebra _root_.LubinTate.padicCompletedUnramifiedFieldAlgebra _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.LocalClassFieldTheory.comparisonIntegerRingIsIntegralClosure _root_.LocalClassFieldTheory.normalizationIntegerRingIsIntegralClosure
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

/-!
# Norm containment for idele power-local-unit subgroups

This file proves that the concrete local-condition subgroup lies in the global
idele norm range, and descends that inclusion to idele classes.
-/

open scoped NumberField Classical NNReal ValuativeRel TensorProduct
open NumberField IsDedekindDomain
open AlgebraicNumberTheory.Valuations
open KummerTheory
open LocalFieldTheory
open LocalFieldTheory.IsNonarchimedeanLocalField

noncomputable section

namespace GlobalClassFieldTheory.ClassFieldAxiom

variable {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] [FiniteDimensional K L] [IsGalois K L]

/-- The idele norm inclusion `h(S,T) ⊆ N_{L/K} I_L`. -/
theorem idelePowerLocalUnitSubgroup_le_relativeIdeleNorm_range
    (n : ℕ+) (r : ℕ)
    (eG :
      (L ≃ₐ[K] L) ≃*
        (Fin r → Multiplicative (ZMod (n : ℕ))))
    (S T : Finset (HeightOneSpectrum (𝓞 K)))
    (harch :
      Even (n : ℕ) ∨
        ∀ w : InfinitePlace K, ¬ w.IsReal)
    (hT :
      ∀ v, v ∈ T →
        _root_.FinitePlaceSplitsCompletely
          (K := K) (L := L) v)
    (hAway :
      ∀ v, v ∉ S ∪ T →
        _root_.ChosenFinitePlaceIsUnramified
          (K := K) (L := L) v) :
    idelePowerLocalUnitSubgroup (K := K) n S T ≤
      (RelativeIdeleGroup.norm K L).range := by
  intro a ha
  rw [_root_.mem_relativeIdeleNorm_range_iff_localTensorNorms]
  constructor
  · intro w
    apply
      _root_.infinitePositiveSubgroup_le_infiniteTensorNormSubgroup
        (K := K) (L := L) w
    apply
      nthPowerSubgroup_le_infinitePositiveSubgroup
        (K := K) n w
    · exact harch.imp_right (fun h => h w)
    · exact
        ((mem_idelePowerLocalUnitSubgroup_iff
          (K := K) n S T a).mp ha).1 w
  · intro v
    rw [
      _root_.finitePlaceLocalTensorNorm_range_eq_chosenLocalNormSubgroup]
    have hall :=
      idelePowerLocalUnitSubgroup_le_allFinitePlaceLocalNormCondition
        (K := K) (L := L) n r eG S T hT hAway ha
    exact Subgroup.mem_iInf.mp hall v

/-- The induced norm inclusion on idele class groups:
`N_{L/K} C_L ⊇ C_K(S,T)`. -/
theorem ideleClassPowerLocalUnitSubgroup_le_ideleClassNorm_range
    (n : ℕ+) (r : ℕ)
    (eG :
      (L ≃ₐ[K] L) ≃*
        (Fin r → Multiplicative (ZMod (n : ℕ))))
    (S T : Finset (HeightOneSpectrum (𝓞 K)))
    (harch :
      Even (n : ℕ) ∨
        ∀ w : InfinitePlace K, ¬ w.IsReal)
    (hT :
      ∀ v, v ∈ T →
        _root_.FinitePlaceSplitsCompletely
          (K := K) (L := L) v)
    (hAway :
      ∀ v, v ∉ S ∪ T →
        _root_.ChosenFinitePlaceIsUnramified
          (K := K) (L := L) v) :
    ideleClassPowerLocalUnitSubgroup (K := K) n S T ≤
      (RelativeIdeleGroup.Cohomology.ideleClassNorm K L).range := by
  rintro c ⟨a, ha, rfl⟩
  obtain ⟨b, hb⟩ :=
    idelePowerLocalUnitSubgroup_le_relativeIdeleNorm_range
      (K := K) (L := L) n r eG S T harch hT hAway ha
  refine
    ⟨QuotientGroup.mk'
        (RelativeIdeleGroup.principalSubgroup K L) b, ?_⟩
  rw [RelativeIdeleGroup.Cohomology.ideleClassNorm_mk, hb]


end GlobalClassFieldTheory.ClassFieldAxiom
end
end

section
-- module Solutions.OAIQ244_DUKE.GlobalClassFieldTheory_ClassFieldAxiom_IdeleClassPowerLocalUnitQuotient_PrimePowerKummerIndex
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 400000
attribute [-instance] _root_.GlobalClassFieldTheory.GlobalClassFields.ConductorialSubgroup.finiteIndex _root_.GlobalClassFieldTheory.GlobalClassFields.bigHilbertClassFieldNormSubgroup_normal _root_.GlobalClassFieldTheory.GlobalClassFields.smallHilbertClassFieldNormSubgroupFiniteIndex _root_.GlobalClassFieldTheory.Reciprocity.infinitePlaceComplexificationOverfield_algebra _root_.GlobalClassFieldTheory.Reciprocity.infinitePlaceComplexificationOverfield_baseAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalClassFieldTheory.finiteGaloisLocalField_integerRing_moduleFinite _root_.LubinTate.padicCompletedLevelField_algebra _root_.LubinTate.padicCompletedUnramifiedFieldAlgebra _root_.LubinTate.standardLubinTateLevelField_isMulCommutative _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.diagonalLogAction _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.LocalClassFieldTheory.comparisonIntegerRingIsIntegralClosure _root_.LocalClassFieldTheory.normalizationIntegerRingIsIntegralClosure
attribute [-simp] _root_.GlobalClassFieldTheory.ClassFieldAxiom.actualPushoutNormQuotientMap_mk _root_.GlobalClassFieldTheory.ClassFieldAxiom.hasseNormDiagonal_mk _root_.GlobalClassFieldTheory.GlobalClassFields.ConductorialSubgroup.ideleClassQuotientEquivOfNarrowFiniteConductorsEqOfRayClassGroupCardsEqQuotientCards_mk _root_.GlobalClassFieldTheory.GlobalClassFields.ConductorialSubgroup.mem_fullConductorInfinitePart_iff _root_.GlobalClassFieldTheory.GlobalClassFields.ConductorialSubgroup.narrowFiniteConductorRayClassGroupEquivQuotientOfCardEq_mk _root_.GlobalClassFieldTheory.GlobalClassFields.ConductorialSubgroup.narrowFiniteConductorRayClassGroupToQuotient_mk _root_.GlobalClassFieldTheory.GlobalClassFields.bigHilbertClassFieldQuotientEquivNarrowClassGroup_mk _root_.GlobalClassFieldTheory.GlobalClassFields.bigHilbertClassFieldQuotientToSmallHilbertClassFieldQuotient_mk _root_.GlobalClassFieldTheory.GlobalClassFields.realSignToBigHilbertClassFieldQuotient_apply _root_.GlobalClassFieldTheory.GlobalClassFields.realSignToNarrowClassKernel_apply _root_.GlobalClassFieldTheory.GlobalClassFields.smallHilbertClassFieldQuotientEquivClassGroup_mk _root_.GlobalClassFieldTheory.Reciprocity.globalNormClassFromIdele_principalIdele _root_.GlobalClassFieldTheory.Reciprocity.infinitePlaceGlobalArtinMonoidHom_finitePlaceIdele _root_.IdeleGroup.finitePlaceIdele_finiteComponent_of_ne _root_.IdeleGroup.finitePlaceIdele_finiteComponent_same _root_.IdeleGroup.finitePlaceIdele_infiniteComponent _root_.IdeleGroup.ideleNormContinuousMonoidHom_apply _root_.IdeleGroup.infinitePlaceIdeleContinuous_apply _root_.IdeleGroup.infinitePlaceIdele_finiteComponent _root_.IdeleGroup.infinitePlaceIdele_infiniteComponent_of_ne _root_.IdeleGroup.infinitePlaceIdele_infiniteComponent_same _root_.IsDiscreteValuationRing.addVal_ringEquiv _root_.OAI.PrimeDegreePackets.ThetaConstruction.schwartzCM_apply _root_.RayClass.primesEquiv_val_eq_natGenerator _root_.RayClass.signToNarrow_mk
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI
attribute [local instance] OAI.starSubalgebraCommCStarAlgebra

set_option autoImplicit false

/-!
# Prime-power Kummer norm index

This file combines the supported local index, principal-ideles exact sequence,
and norm containment to prove the prime-power Kummer norm-index theorem.
-/

open scoped NumberField Classical NNReal ValuativeRel TensorProduct
open NumberField IsDedekindDomain
open AlgebraicNumberTheory.Valuations
open KummerTheory
open LocalFieldTheory
open LocalFieldTheory.IsNonarchimedeanLocalField

noncomputable section

namespace GlobalClassFieldTheory.ClassFieldAxiom

variable {K : Type} [Field K] [NumberField K]

/-- The class-quotient calculation for the Kummer-selected prime set.
The localization equality identifies the left term of the exact sequence
with the canonical `n`-th-power quotient of the `(S' ∪ T)`-unit group;
all support and divisibility hypotheses are derived from the prescribed
seed `S`. -/
theorem
    card_ideleClassPowerLocalUnitQuotient_eq_finrank_sUnitKummerPrimeSet
    {Omega : Type} [Field Omega] [Algebra K Omega]
    [IsSepClosure K Omega]
    (E : IntermediateField K Omega)
    [FiniteDimensional K E] [IsGalois K E]
    [IsMulCommutative Gal(E/K)]
    (n : ℕ+)
    (hmu : (primitiveRoots (n : ℕ) K).Nonempty)
    (p v : ℕ) (hp : p.Prime) (hv : 0 < v)
    (hn : (n : ℕ) = p ^ v)
    (r : ℕ)
    (eG :
      Gal(E/K) ≃*
        (Fin r → Multiplicative (ZMod (n : ℕ))))
    (S : Finset (HeightOneSpectrum (𝓞 K))) :
    let hnK : ((n : ℕ) : K) ≠ 0 := by
      exact_mod_cast n.ne_zero
    let nUnit : Kˣ :=
      Units.mk0 ((n : ℕ) : K) hnK
    let S₀ :=
      (S ∪ IdeleGroup.sufficientlyLargeFiniteSet (K := K)) ∪
        chosenUnitFiniteSupport (K := K) nUnit
    let S' :=
      enlargeByFiniteKummerRadicalSupport
        (K := K) (L := E) n hmu S₀
    let T :=
      sUnitKummerPrimeSet
        (K := K) (Omega := Omega) E n hmu
        p v hp hv hn r eG S₀
    Nat.card
        (IdeleClassPowerLocalUnitQuotient
          (K := K) n S' T) =
      Module.finrank K E := by
  classical
  dsimp only
  let hnK : ((n : ℕ) : K) ≠ 0 := by
    exact_mod_cast n.ne_zero
  let nUnit : Kˣ :=
    Units.mk0 ((n : ℕ) : K) hnK
  let S₀ :=
    (S ∪ IdeleGroup.sufficientlyLargeFiniteSet (K := K)) ∪
      chosenUnitFiniteSupport (K := K) nUnit
  let S' :=
    enlargeByFiniteKummerRadicalSupport
      (K := K) (L := E) n hmu S₀
  let T :=
    sUnitKummerPrimeSet
      (K := K) (Omega := Omega) E n hmu
      p v hp hv hn r eG S₀
  let hST : Disjoint S' T :=
    (sUnitKummerPrimeSet_disjoint_enlargeByFiniteKummerRadicalSupport
      (K := K) (Omega := Omega) E n hmu
      p v hp hv hn r eG S₀).symm
  change
    Nat.card
        (IdeleClassPowerLocalUnitQuotient
          (K := K) n S' T) =
      Module.finrank K E
  have hnOne : 1 < (n : ℕ) := by
    rw [hn]
    calc
      1 < p := hp.one_lt
      _ = p ^ 1 := (pow_one p).symm
      _ ≤ p ^ v :=
        Nat.pow_le_pow_right hp.pos
          (Nat.succ_le_iff.mpr hv)
  have hr :
      r ≤ totalPlaceCard (K := K) S' := by
    simpa only [S'] using
      galoisRank_le_totalPlaceCard_enlargedS
        (K := K) (Omega := Omega) E n hnOne hmu
        r eG S₀
  have hTcard :
      T.card =
        totalPlaceCard (K := K) S' - r := by
    simpa only [T, S', sUnitKummerPrimeCount] using
      sUnitKummerPrimeSet_card
        (K := K) (Omega := Omega) E n hmu
        p v hp hv hn r eG S₀
  have hDoubleSub :
      2 * totalPlaceCard (K := K) S' - r =
        totalPlaceCard (K := K) S' +
          (totalPlaceCard (K := K) S' - r) := by
    rw [two_mul]
    exact Nat.add_sub_assoc hr _
  have hTotal :
      totalPlaceCard (K := K) (S' ∪ T) =
        2 * totalPlaceCard (K := K) S' - r := by
    change
      Fintype.card (InfinitePlace K) + (S' ∪ T).card =
        2 * totalPlaceCard (K := K) S' - r
    rw [Finset.card_union_of_disjoint hST, hTcard, hDoubleSub]
    unfold totalPlaceCard
    simp only [Nat.add_assoc]
  have hPrincipal :=
    principalIdelePowerLocalUnitSubgroup_eq_sUnitNthPowersInField_sUnitKummerPrimeSet
      (K := K) (Omega := Omega) E n hmu
      p v hp hv hn r eG S
  dsimp only at hPrincipal
  change
    principalIdelePowerLocalUnitSubgroup
        (K := K) n S' T =
      sUnitNthPowersInField
        (K := K) n (S' ∪ T) at hPrincipal
  have hDen :
      sUnitPrincipalIdelePowerSubgroup
          (K := K) n S' T =
        (powMonoidHom (n : ℕ) :
          SUnitGroup (K := K) (S' ∪ T) →*
            SUnitGroup (K := K) (S' ∪ T)).range := by
    rw [sUnitPrincipalIdelePowerSubgroup, hPrincipal,
      sUnitNthPowersInField]
    exact
      Subgroup.comap_map_eq_self_of_injective
        (SUnitGroup
          (K := K) (S' ∪ T)).subtype_injective _
  have hLeft :
      Nat.card
          (SUnitGroup (K := K) (S' ∪ T) ⧸
            sUnitPrincipalIdelePowerSubgroup
              (K := K) n S' T) =
        (n : ℕ) ^
          (2 * totalPlaceCard (K := K) S' - r) := by
    rw [hDen,
      card_sUnit_nthPowerQuotient
        (K := K) (S' ∪ T) n hmu,
      hTotal]
  have hDiv :
      ∀ w : HeightOneSpectrum (𝓞 K),
        w.asIdeal ∣
            Ideal.span {((n : ℕ) : 𝓞 K)} →
          w ∈ S' := by
    intro w hwDvd
    have hnValLt :
        w.valuation K ((n : ℕ) : K) < 1 := by
      simpa using
        (IsDedekindDomain.HeightOneSpectrum.valuation_lt_one_iff_dvd
          (K := K) w ((n : ℕ) : 𝓞 K)).2 hwDvd
    have hwSupport :
        w ∈ chosenUnitFiniteSupport (K := K) nUnit := by
      by_contra hwNotSupport
      have hnUnitVal :
          w.valuation K (nUnit : K) = 1 :=
        (mem_SUnitGroup_iff
          (K := K)
          (chosenUnitFiniteSupport (K := K) nUnit) nUnit).mp
            (mem_sUnitGroup_chosenUnitFiniteSupport
              (K := K) nUnit)
            w hwNotSupport
      have hnValEq :
          w.valuation K ((n : ℕ) : K) = 1 := by
        change w.valuation K ((n : ℕ) : K) = 1 at hnUnitVal
        exact hnUnitVal
      exact (ne_of_lt hnValLt) hnValEq
    exact
      subset_enlargeByFiniteKummerRadicalSupport
        (K := K) (L := E) n hmu S₀
        (Finset.mem_union_right _ hwSupport)
  have hCanonical :
      (IdeleGroup.sufficientlyLargeFiniteSet (K := K) :
          Set (HeightOneSpectrum (𝓞 K))) ⊆
        (S₀ : Set (HeightOneSpectrum (𝓞 K))) := by
    intro w hw
    exact
      Finset.mem_union_left _
        (Finset.mem_union_right _ hw)
  have hS₀ :
      IdeleGroup.supportedAt
            (K := K) (S₀ : Set (HeightOneSpectrum (𝓞 K))) ⊔
          IdeleGroup.principalSubgroup K =
        ⊤ := by
    apply top_unique
    rw [
      ← IdeleGroup.supportedAt_sup_principalSubgroup_eq_top
        (K := K)]
    exact
      sup_le_sup
        (IdeleGroup.supportedAt_mono
          (K := K) hCanonical)
        le_rfl
  have hLargeS' :
      IdeleGroup.supportedAt
            (K := K) (S' : Set (HeightOneSpectrum (𝓞 K))) ⊔
          IdeleGroup.principalSubgroup K =
        ⊤ := by
    simpa only [S'] using
      supportedAt_sup_principalSubgroup_eq_top_of_enlargeByRadicalSupport
        (K := K) (L := E) n hmu S₀ hS₀
  have hLarge :
      IdeleGroup.supportedAt
            (K := K)
            (S' ∪ T : Set (HeightOneSpectrum (𝓞 K))) ⊔
          IdeleGroup.principalSubgroup K =
        ⊤ := by
    apply top_unique
    rw [← hLargeS']
    exact
      sup_le_sup
          (IdeleGroup.supportedAt_mono
            (K := K) (by
              intro w hw
              exact Or.inl hw))
        le_rfl
  have hProduct :=
    card_sUnitPrincipalQuotient_mul_card_ideleClassQuotient_eq_power_two_totalPlaceCard
      (K := K) n hmu S' T hDiv hLarge
  rw [hLeft] at hProduct
  have hr2 :
      r ≤ 2 * totalPlaceCard (K := K) S' := by
    omega
  have hPow :
      (n : ℕ) ^
          (2 * totalPlaceCard (K := K) S') =
        (n : ℕ) ^
            (2 * totalPlaceCard (K := K) S' - r) *
          (n : ℕ) ^ r := by
    rw [← pow_add, Nat.sub_add_cancel hr2]
  have hClassCard :
      Nat.card
          (IdeleClassPowerLocalUnitQuotient
            (K := K) n S' T) =
        (n : ℕ) ^ r := by
    exact
      Nat.eq_of_mul_eq_mul_left
        (pow_pos n.pos
          (2 * totalPlaceCard (K := K) S' - r))
        (hProduct.trans hPow)
  calc
    Nat.card
          (IdeleClassPowerLocalUnitQuotient
            (K := K) n S' T) =
        (n : ℕ) ^ r :=
      hClassCard
    _ = Nat.card Gal(E/K) := by
      symm
      rw [Nat.card_congr eG.toEquiv, Nat.card_pi]
      simp
    _ = Module.finrank K E :=
      IsGalois.card_aut_eq_finrank K E

/-- Separable-closure realization of the norm-index calculation for a
prime-power Kummer extension presented as an intermediate field.  This
form is useful when the extension is already constructed inside a fixed
separable closure. -/
theorem
    ideleClassNorm_index_eq_finrank_primePowerKummer_intermediateField
    {Omega : Type} [Field Omega] [Algebra K Omega]
    [IsSepClosure K Omega]
    (E : IntermediateField K Omega)
    [FiniteDimensional K E] [IsGalois K E]
    (n : ℕ+)
    (hmu : (primitiveRoots (n : ℕ) K).Nonempty)
    (p v : ℕ) (hp : p.Prime) (hv : 0 < v)
    (hn : (n : ℕ) = p ^ v)
    (eG :
      Gal(E/K) ≃*
        (Fin 1 → Multiplicative (ZMod (n : ℕ)))) :
    letI : NumberField E :=
      NumberField.of_module_finite K E
    (RelativeIdeleGroup.Cohomology.ideleClassNorm K E).range.index =
      Module.finrank K E := by
  classical
  let _ : NumberField E :=
    NumberField.of_module_finite K E
  let eCyclic :
      Gal(E/K) ≃* Multiplicative (ZMod (n : ℕ)) :=
    eG.trans
      (MulEquiv.piUnique
        (fun _ : Fin 1 =>
          Multiplicative (ZMod (n : ℕ))))
  let : IsCyclic Gal(E/K) :=
    eCyclic.isCyclic.mpr inferInstance
  let S : Finset (HeightOneSpectrum (𝓞 K)) :=
    _root_.ideleClassHerbrandSupport
      (K := K) (L := E)
  let hnK : ((n : ℕ) : K) ≠ 0 := by
    exact_mod_cast n.ne_zero
  let nUnit : Kˣ :=
    Units.mk0 ((n : ℕ) : K) hnK
  let S₀ :=
    (S ∪ IdeleGroup.sufficientlyLargeFiniteSet (K := K)) ∪
      chosenUnitFiniteSupport (K := K) nUnit
  let S' :=
    enlargeByFiniteKummerRadicalSupport
      (K := K) (L := E) n hmu S₀
  let T :=
    sUnitKummerPrimeSet
      (K := K) (Omega := Omega) E n hmu
      p v hp hv hn 1 eG S₀
  have hClassCard :=
    card_ideleClassPowerLocalUnitQuotient_eq_finrank_sUnitKummerPrimeSet
      (K := K) (Omega := Omega) E n hmu
      p v hp hv hn 1 eG S
  dsimp only at hClassCard
  change
    Nat.card
        (IdeleClassPowerLocalUnitQuotient
          (K := K) n S' T) =
      Module.finrank K E at hClassCard
  have hT :
      ∀ w, w ∈ T →
        _root_.FinitePlaceSplitsCompletely
          (K := K) (L := E) w := by
    intro w hw
    apply
      finitePlaceSplitsCompletely_of_mem_sUnitKummerPrimeSet
        (K := K) (Omega := Omega) E n hmu
        p v hp hv hn 1 eG S₀ w
    simpa only [T] using hw
  have hAway :
      ∀ w, w ∉ S' ∪ T →
        _root_.ChosenFinitePlaceIsUnramified
          (K := K) (L := E) w := by
    intro w hwAway
    apply
      _root_.GlobalClassFieldTheory.Cohomology.chosenFinitePlaceIsUnramified_of_notMem_ideleClassHerbrandSupport
    intro hwSupport
    have hwS : w ∈ S := by
      simpa only [S] using hwSupport
    have hwS₀ : w ∈ S₀ :=
      Finset.mem_union_left _
        (Finset.mem_union_left _ hwS)
    have hwS' : w ∈ S' :=
      subset_enlargeByFiniteKummerRadicalSupport
        (K := K) (L := E) n hmu S₀ hwS₀
    exact hwAway (Finset.mem_union_left T hwS')
  have hnOne : 1 < (n : ℕ) := by
    rw [hn]
    calc
      1 < p := hp.one_lt
      _ = p ^ 1 := (pow_one p).symm
      _ ≤ p ^ v :=
        Nat.pow_le_pow_right hp.pos
          (Nat.succ_le_iff.mpr hv)
  have harch :
      Even (n : ℕ) ∨
        ∀ w : InfinitePlace K, ¬ w.IsReal := by
    by_cases hnEven : Even (n : ℕ)
    · exact Or.inl hnEven
    · refine Or.inr ?_
      have hnNeTwo : (n : ℕ) ≠ 2 := by
        intro hnTwo
        apply hnEven
        rw [hnTwo]
        decide
      have hnLarge : 2 < (n : ℕ) := by
        omega
      obtain ⟨ζ, hζ⟩ := hmu
      have hζPrim : IsPrimitiveRoot ζ (n : ℕ) :=
        (mem_primitiveRoots n.pos).mp hζ
      have hRealZero :
          InfinitePlace.nrRealPlaces K = 0 :=
        InfinitePlace.IsPrimitiveRoot.nrRealPlaces_eq_zero_of_two_lt
          hnLarge hζPrim
      intro w hwReal
      have hRealPos :
          0 < InfinitePlace.nrRealPlaces K :=
        Fintype.card_pos_iff.mpr ⟨⟨w, hwReal⟩⟩
      omega
  have hSub :
      ideleClassPowerLocalUnitSubgroup
          (K := K) n S' T ≤
        (RelativeIdeleGroup.Cohomology.ideleClassNorm K E).range :=
    ideleClassPowerLocalUnitSubgroup_le_ideleClassNorm_range
      (K := K) (L := E) n 1 eG S' T
      harch hT hAway
  have hPowerIndex :
      (ideleClassPowerLocalUnitSubgroup
          (K := K) n S' T).index =
        Module.finrank K E := by
    rw [Subgroup.index_eq_card]
    change
      Nat.card
          (IdeleClassPowerLocalUnitQuotient
            (K := K) n S' T) =
        Module.finrank K E
    exact hClassCard
  have hIndexDvd :
      (RelativeIdeleGroup.Cohomology.ideleClassNorm K E).range.index ∣
        (ideleClassPowerLocalUnitSubgroup
          (K := K) n S' T).index :=
    Subgroup.index_dvd_of_le hSub
  have hDvd :
      (RelativeIdeleGroup.Cohomology.ideleClassNorm K E).range.index ∣
        Module.finrank K E := by
    simpa only [hPowerIndex] using hIndexDvd
  have hUpper :
      (RelativeIdeleGroup.Cohomology.ideleClassNorm K E).range.index ≤
        Module.finrank K E :=
    Nat.le_of_dvd Module.finrank_pos hDvd
  obtain ⟨sigma, hsigma⟩ :=
    IsCyclic.exists_generator (α := Gal(E/K))
  have hLower :
      Module.finrank K E ≤
        (RelativeIdeleGroup.Cohomology.ideleClassNorm K E).range.index :=
    Cohomology.finrank_le_ideleClassNorm_index
      (K := K) (L := E) sigma hsigma
  exact le_antisymm hUpper hLower

/-- The norm subgroup has index `[E : K]` for an arbitrary prime-power
Kummer extension.  The proof realizes `E` as its field range in a fixed
separable closure, applies the intermediate-field calculation there,
and transports both the norm index and the degree back across the
resulting `K`-algebra equivalence. -/
theorem ideleClassNorm_index_eq_finrank_primePowerKummer
    {E : Type} [Field E] [Algebra K E]
    [FiniteDimensional K E] [IsGalois K E]
    (n : ℕ+)
    (hmu : (primitiveRoots (n : ℕ) K).Nonempty)
    (p v : ℕ) (hp : p.Prime) (hv : 0 < v)
    (hn : (n : ℕ) = p ^ v)
    (eG :
      Gal(E/K) ≃*
        (Fin 1 → Multiplicative (ZMod (n : ℕ)))) :
    letI : NumberField E :=
      NumberField.of_module_finite K E
    (RelativeIdeleGroup.Cohomology.ideleClassNorm K E).range.index =
      Module.finrank K E := by
  classical
  let : NumberField E :=
    NumberField.of_module_finite K E
  let i : E →ₐ[K] SeparableClosure K :=
    IsSepClosed.lift
  let R : IntermediateField K (SeparableClosure K) :=
    AlgHom.fieldRange i
  let e : E ≃ₐ[K] R :=
    AlgHom.equivFieldRange i
  let _ : FiniteDimensional K R :=
    e.toLinearEquiv.finiteDimensional
  let _ : IsGalois K R :=
    IsGalois.of_algEquiv e
  let _ : NumberField R :=
    NumberField.of_module_finite K R
  let _ : (RelativeIdeleGroup.principalSubgroup K R).Normal :=
    ⟨fun n hn g => by
      have hconj : g * n * g⁻¹ = n := by
        rw [mul_comm g n, mul_assoc, mul_inv_cancel, mul_one]
      rwa [hconj]⟩
  let _ : Group (RelativeIdeleGroup.ClassGroup K R) :=
    QuotientGroup.Quotient.group
      (RelativeIdeleGroup.principalSubgroup K R)
  let eG' :
      Gal(R/K) ≃*
        (Fin 1 → Multiplicative (ZMod (n : ℕ))) :=
    (AlgEquiv.autCongr e).symm.trans eG
  have hR :=
    ideleClassNorm_index_eq_finrank_primePowerKummer_intermediateField
      (K := K) (Omega := SeparableClosure K) R n hmu
      p v hp hv hn eG'
  calc
    (RelativeIdeleGroup.Cohomology.ideleClassNorm K E).range.index =
        (RelativeIdeleGroup.Cohomology.ideleClassNorm K R).range.index :=
      (ideleClassNorm_index_algEquiv
        (K := K) e).symm
    _ = Module.finrank K R := hR
    _ = Module.finrank K E :=
      e.toLinearEquiv.finrank_eq.symm


end GlobalClassFieldTheory.ClassFieldAxiom
end
end

section
-- module Solutions.OAIQ244_DUKE.GlobalClassFieldTheory_ClassFieldAxiom_CyclicIdeleClassNormIndex
attribute [-instance] _root_.GlobalClassFieldTheory.GlobalClassFields.ConductorialSubgroup.finiteIndex _root_.GlobalClassFieldTheory.GlobalClassFields.bigHilbertClassFieldNormSubgroup_normal _root_.GlobalClassFieldTheory.GlobalClassFields.smallHilbertClassFieldNormSubgroupFiniteIndex _root_.GlobalClassFieldTheory.Reciprocity.infinitePlaceComplexificationOverfield_algebra _root_.GlobalClassFieldTheory.Reciprocity.infinitePlaceComplexificationOverfield_baseAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalClassFieldTheory.finiteGaloisLocalField_integerRing_moduleFinite _root_.LubinTate.padicCompletedLevelField_algebra _root_.LubinTate.padicCompletedLevelField_finiteDimensional _root_.LubinTate.padicCompletedLevelField_isGalois _root_.LubinTate.padicCompletedUnramifiedFieldAlgebra _root_.LubinTate.standardLubinTateLevelValuationSubring_moduleFinite _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.diagonalLogAction _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.LocalClassFieldTheory.comparisonIntegerRingIsIntegralClosure _root_.LocalClassFieldTheory.normalizationIntegerRingIsIntegralClosure
attribute [-simp] _root_.GlobalClassFieldTheory.ClassFieldAxiom.hasseNormDiagonal_mk _root_.GlobalClassFieldTheory.GlobalClassFields.ConductorialSubgroup.ideleClassQuotientEquivOfNarrowFiniteConductorsEqOfRayClassGroupCardsEqQuotientCards_mk _root_.GlobalClassFieldTheory.GlobalClassFields.ConductorialSubgroup.mem_fullConductorInfinitePart_iff _root_.GlobalClassFieldTheory.GlobalClassFields.ConductorialSubgroup.narrowFiniteConductorRayClassGroupEquivQuotientOfCardEq_mk _root_.GlobalClassFieldTheory.GlobalClassFields.ConductorialSubgroup.narrowFiniteConductorRayClassGroupToQuotient_mk _root_.GlobalClassFieldTheory.GlobalClassFields.bigHilbertClassFieldQuotientEquivNarrowClassGroup_mk _root_.GlobalClassFieldTheory.GlobalClassFields.bigHilbertClassFieldQuotientToSmallHilbertClassFieldQuotient_mk _root_.GlobalClassFieldTheory.GlobalClassFields.realSignToBigHilbertClassFieldQuotient_apply _root_.GlobalClassFieldTheory.GlobalClassFields.realSignToNarrowClassKernel_apply _root_.GlobalClassFieldTheory.GlobalClassFields.smallHilbertClassFieldQuotientEquivClassGroup_mk _root_.GlobalClassFieldTheory.Reciprocity.globalNormClassFromIdele_principalIdele _root_.GlobalClassFieldTheory.Reciprocity.infinitePlaceGlobalArtinMonoidHom_finitePlaceIdele _root_.IdeleGroup.finitePlaceIdele_finiteComponent_of_ne _root_.IdeleGroup.finitePlaceIdele_finiteComponent_same _root_.IdeleGroup.finitePlaceIdele_infiniteComponent _root_.IdeleGroup.ideleNormContinuousMonoidHom_apply _root_.IdeleGroup.infinitePlaceIdeleContinuous_apply _root_.IdeleGroup.infinitePlaceIdele_finiteComponent _root_.IdeleGroup.infinitePlaceIdele_infiniteComponent_of_ne _root_.IdeleGroup.infinitePlaceIdele_infiniteComponent_same _root_.IsDiscreteValuationRing.addVal_ringEquiv _root_.OAI.PrimeDegreePackets.ThetaConstruction.schwartzCM_apply _root_.RayClass.primesEquiv_val_eq_natGenerator _root_.RayClass.signToNarrow_mk _root_.RelativeIdeleGroup.relativeFinitePlaceIdele_finiteComponent_of_ne _root_.RelativeIdeleGroup.relativeFinitePlaceIdele_finiteComponent_same _root_.RelativeIdeleGroup.relativeFinitePlaceIdele_infiniteComponent _root_.RelativeIdeleGroup.relativeInfinitePlaceIdele_finiteComponent _root_.RelativeIdeleGroup.relativeInfinitePlaceIdele_infiniteComponent_of_ne _root_.RelativeIdeleGroup.relativeInfinitePlaceIdele_infiniteComponent_same
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI
attribute [local instance] OAI.starSubalgebraCommCStarAlgebra

set_option autoImplicit false

/-!
# The global class-field axiom

This file proves the cyclic idele-class norm-index formula.  The first
input is the `H⁻¹` calculation for the principal-idele term in

`1 → Lˣ → I_L → C_L → 1`.

For a cyclic extension this term vanishes by Hilbert 90.  The result below
is transported through the actual low-degree Tate comparison and then
through the equivariant identification of `Lˣ` with the subgroup of
principal relative ideles.
-/

noncomputable section

namespace GlobalClassFieldTheory.ClassFieldAxiom

open CyclicCohomology
open CyclicCohomology.ProfiniteCohomology.Herbrand

section NormQuotientCommutativity

section IntermediateNormQuotientCommutativity

attribute [local instance] GlobalClassFieldTheory.ClassFieldAxiom.cyclicNormBase_isMulCommutative
local instance cyclicNormRelative_isMulCommutative_r87910d_1
    (A B : Type) [Field A] [NumberField A] [Field B] [Algebra A B] :
    IsMulCommutative (RelativeIdeleGroup.ClassGroup A B) :=
  ⟨⟨fun a b => mul_comm a b⟩⟩
/-- Prime-degree upper bound.  After adjoining the `p`-th roots of unity,
the prime-power Kummer calculation gives norm index `p` for the concrete
cyclotomic pushout.  Coprimality of the cyclotomic degree then makes the
actual pushout map on norm quotients injective. -/
theorem ideleClassNorm_index_le_prime_of_finrank_eq
    (K L : Type)
    [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    (p : ℕ) (hp : p.Prime)
    (hdegree : Module.finrank K L = p) :
    (RelativeIdeleGroup.Cohomology.ideleClassNorm K L).range.index ≤ p := by
  let : NeZero p := ⟨hp.ne_zero⟩
  let M := KummerTheory.PrimeCyclotomicBase K p
  let N := KummerTheory.PrimeCyclotomicPushout K L p
  let : Field N :=
    KummerTheory.primeCyclotomicPushoutField
      K L p hp hdegree
  let : Algebra L N :=
    Algebra.TensorProduct.rightAlgebra
  let : Algebra M N :=
    KummerTheory.primeCyclotomicPushoutAlgebra
      K L p hp hdegree
  let : FiniteDimensional M N :=
    Module.Finite.of_restrictScalars_finite K M N
  let : FiniteDimensional L N :=
    Module.Finite.of_restrictScalars_finite K L N
  let : NumberField N :=
    KummerTheory.primeCyclotomicPushout_numberField
      K L p hp hdegree
  let : IsGalois M N :=
    KummerTheory.primeCyclotomicPushout_isGalois
      K L p hp hdegree
  let n : ℕ+ := ⟨p, hp.pos⟩
  have hTargetIndex :
      (RelativeIdeleGroup.Cohomology.ideleClassNorm M N).range.index = p := by
    calc
      (RelativeIdeleGroup.Cohomology.ideleClassNorm M N).range.index =
          Module.finrank M N := by
        simpa only [M, N, n] using
          (ideleClassNorm_index_eq_finrank_primePowerKummer
            (K := M) (E := N) n
            (KummerTheory.primeCyclotomicBase_primitiveRoots_nonempty
              (K := K) p hp)
            p 1 hp (by omega) (by simp [n])
            (KummerTheory.primeCyclotomicPushoutGalEquivPiZMod
              K L p hp hdegree))
      _ = p :=
        KummerTheory.primeCyclotomicPushout_finrank
          K L p hp hdegree
  have hTargetCard :
      Nat.card
          (RelativeIdeleGroup.Cohomology.IdeleClassNormQuotient M N) =
        p := by
    rw [← Subgroup.index_eq_card]
    exact hTargetIndex
  let :
      Finite (RelativeIdeleGroup.Cohomology.IdeleClassNormQuotient M N) :=
    Nat.finite_of_card_ne_zero (by
      rw [hTargetCard]
      exact hp.ne_zero)
  rw [Subgroup.index_eq_card]
  calc
    Nat.card (RelativeIdeleGroup.Cohomology.IdeleClassNormQuotient K L) ≤
        Nat.card
          (RelativeIdeleGroup.Cohomology.IdeleClassNormQuotient M N) :=
      ideleClassNormQuotient_card_le_actualPushout
        K M L N
        (KummerTheory.primeCyclotomicBase_finrank_coprime
          (K := K) (L := L) p hp hdegree)
    _ = p := hTargetCard

end IntermediateNormQuotientCommutativity

attribute [local instance] GlobalClassFieldTheory.ClassFieldAxiom.cyclicNormBase_isMulCommutative
/-- Relative-coordinate source for the norm-index calculation. -/
theorem relativeIdeleClassNorm_index_eq_finrank_cyclic
    (K L : Type)
    [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    [IsCyclic (L ≃ₐ[K] L)] :
    (RelativeIdeleGroup.Cohomology.ideleClassNorm K L).range.index =
      Module.finrank K L := by
  classical
  induction hfinrank : Module.finrank K L using
      Nat.strong_induction_on generalizing K L with
  | h degree ih =>
    by_cases hdegreeOne : Module.finrank K L = 1
    · have hsurjective :
          Function.Surjective
            (RelativeIdeleGroup.Cohomology.ideleClassNorm K L) := by
        intro c
        refine
          ⟨RelativeIdeleGroup.classInclusion K L c, ?_⟩
        calc
          RelativeIdeleGroup.Cohomology.ideleClassNorm K L
                (RelativeIdeleGroup.classInclusion K L c) =
              c ^ Module.finrank K L :=
            ideleClassNorm_classInclusion K L c
          _ = c := by rw [hdegreeOne, pow_one]
      have hRange :
          (RelativeIdeleGroup.Cohomology.ideleClassNorm K L).range = ⊤ :=
        MonoidHom.range_eq_top.mpr hsurjective
      rw [hRange, Subgroup.index_top, ← hfinrank, hdegreeOne]
    · have hdegreeLarge :
          1 < Module.finrank K L := by
        have hpositive : 0 < Module.finrank K L :=
          Module.finrank_pos
        omega
      let p :=
        cyclicDegreePrime
          (K := K) (L := L) hdegreeLarge
      let M :=
        cyclicPrimeDegreeIntermediate
          (K := K) (L := L) hdegreeLarge
      let : IsGalois K M :=
        cyclicPrimeDegreeIntermediate_isGalois
          (K := K) (L := L) hdegreeLarge
      let : IsGalois M L :=
        cyclicPrimeDegreeIntermediate_top_isGalois
          (K := K) (L := L) hdegreeLarge
      let : IsCyclic (M ≃ₐ[K] M) :=
        cyclicPrimeDegreeIntermediate_base_isCyclic
          (K := K) (L := L) hdegreeLarge
      let : IsCyclic (L ≃ₐ[M] L) :=
        cyclicPrimeDegreeIntermediate_top_isCyclic
          (K := K) (L := L) hdegreeLarge
      let : NumberField M :=
        NumberField.of_module_finite K M
      have hp : p.Prime := by
        simpa only [p] using
          cyclicDegreePrime_prime
            (K := K) (L := L) hdegreeLarge
      have hBaseDegree :
          Module.finrank K M = p := by
        simpa only [M, p] using
          cyclicPrimeDegreeIntermediate_finrank
            (K := K) (L := L) hdegreeLarge
      have hTopDegree :
          Module.finrank M L =
            Module.finrank K L / p := by
        simpa only [M, p] using
          cyclicPrimeDegreeIntermediate_top_finrank
            (K := K) (L := L) hdegreeLarge
      have hTopLt :
          Module.finrank M L <
            Module.finrank K L := by
        rw [hTopDegree]
        exact
          Nat.div_lt_self Module.finrank_pos hp.one_lt
      have hTopLtDegree :
          Module.finrank M L < degree := by
        exact hTopLt.trans_eq hfinrank
      have hTopIndex :
          (RelativeIdeleGroup.Cohomology.ideleClassNorm M L).range.index =
            Module.finrank M L :=
        ih (Module.finrank M L) hTopLtDegree M L rfl
      have hBaseUpper :
          (RelativeIdeleGroup.Cohomology.ideleClassNorm K M).range.index ≤
            Module.finrank K M := by
        rw [hBaseDegree]
        exact
          ideleClassNorm_index_le_prime_of_finrank_eq
            K M p hp hBaseDegree
      obtain ⟨sigmaM, hsigmaM⟩ :=
        IsCyclic.exists_generator (α := M ≃ₐ[K] M)
      have hBaseLower :
          Module.finrank K M ≤
            (RelativeIdeleGroup.Cohomology.ideleClassNorm K M).range.index :=
        _root_.GlobalClassFieldTheory.Cohomology.finrank_le_ideleClassNorm_index
          (K := K) (L := M) sigmaM hsigmaM
      have hBaseIndex :
          (RelativeIdeleGroup.Cohomology.ideleClassNorm K M).range.index =
            Module.finrank K M :=
        le_antisymm hBaseUpper hBaseLower
      have hTopCard :
          Nat.card
              (RelativeIdeleGroup.Cohomology.IdeleClassNormQuotient M L) =
            Module.finrank M L := by
        rw [← Subgroup.index_eq_card]
        exact hTopIndex
      have hBaseCard :
          Nat.card
              (RelativeIdeleGroup.Cohomology.IdeleClassNormQuotient K M) =
            Module.finrank K M := by
        rw [← Subgroup.index_eq_card]
        exact hBaseIndex
      let :
          Finite (RelativeIdeleGroup.Cohomology.IdeleClassNormQuotient M L) :=
        Nat.finite_of_card_ne_zero (by
          rw [hTopCard]
          exact Nat.ne_of_gt Module.finrank_pos)
      let :
          Finite (RelativeIdeleGroup.Cohomology.IdeleClassNormQuotient K M) :=
        Nat.finite_of_card_ne_zero (by
          rw [hBaseCard]
          exact Nat.ne_of_gt Module.finrank_pos)
      have hUpperCard :
          Nat.card
              (RelativeIdeleGroup.Cohomology.IdeleClassNormQuotient K L) ≤
            Module.finrank K L := by
        calc
          Nat.card
                (RelativeIdeleGroup.Cohomology.IdeleClassNormQuotient K L) ≤
              Nat.card
                  (RelativeIdeleGroup.Cohomology.IdeleClassNormQuotient M L) *
                Nat.card
                  (RelativeIdeleGroup.Cohomology.IdeleClassNormQuotient K M) :=
            ideleClassNormQuotient_card_le_actual_tower_mul
              K M L
          _ =
              Module.finrank M L *
                Module.finrank K M := by
            rw [hTopCard, hBaseCard]
          _ = Module.finrank K L := by
            rw [Nat.mul_comm,
              Module.finrank_mul_finrank K M L]
      have hUpper :
          (RelativeIdeleGroup.Cohomology.ideleClassNorm K L).range.index ≤
            Module.finrank K L := by
        rw [Subgroup.index_eq_card]
        exact hUpperCard
      obtain ⟨sigma, hsigma⟩ :=
        IsCyclic.exists_generator (α := L ≃ₐ[K] L)
      have hLower :
          Module.finrank K L ≤
            (RelativeIdeleGroup.Cohomology.ideleClassNorm K L).range.index :=
        _root_.GlobalClassFieldTheory.Cohomology.finrank_le_ideleClassNorm_index
          (K := K) (L := L) sigma hsigma
      exact (le_antisymm hUpper hLower).trans hfinrank

/-- The cardinalities of the actual Herbrand models of the low Tate groups
for a finite cyclic extension.  The canonical Herbrand support
gives the Herbrand quotient `|G|`; the norm-index theorem supplies the
matching upper bound for `H⁰`, so the standard low-degree cardinal lemma
forces `H⁻¹` to have one element. -/
theorem ideleClass_lowDegree_card_eq_finrank_cyclic
    (K L : Type)
    [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    (sigma : L ≃ₐ[K] L)
    (hsigma :
      ∀ tau : L ≃ₐ[K] L,
        tau ∈ Subgroup.zpowers sigma) :
    letI :=
      RelativeIdeleGroup.Cohomology.ideleClassMulDistribMulAction K L
    Nat.card
          (HerbrandH0 (L ≃ₐ[K] L)
            (RelativeIdeleGroup.ClassGroup K L)) =
        Module.finrank K L ∧
      Nat.card
          (HerbrandHMinusOne (L ≃ₐ[K] L)
            (RelativeIdeleGroup.ClassGroup K L) sigma) =
        1 := by
  let :=
    RelativeIdeleGroup.Cohomology.ideleClassMulDistribMulAction K L
  let : IsCyclic (L ≃ₐ[K] L) :=
    ⟨⟨sigma, hsigma⟩⟩
  obtain ⟨hC, hCvalue⟩ :=
    _root_.GlobalClassFieldTheory.Cohomology.ideleClass_herbrandQuotient_eq_card_of_supported_local_calculation
      (K := K) (L := L)
      (_root_.ideleClassHerbrandSupport
        (K := K) (L := L))
      sigma hsigma
      (_root_.relativeSupportedAboveHerbrandSupport_sup_principal_eq_top
        (K := K) (L := L))
      (_root_.GlobalClassFieldTheory.Cohomology.chosenFinitePlaceIsUnramified_of_notMem_ideleClassHerbrandSupport
        (K := K) (L := L))
  let :
      Finite
        (HerbrandH0 (L ≃ₐ[K] L)
          (RelativeIdeleGroup.ClassGroup K L)) :=
    hC.1
  let :
      Finite
        (HerbrandHMinusOne (L ≃ₐ[K] L)
          (RelativeIdeleGroup.ClassGroup K L) sigma) :=
    hC.2
  have hQuotient :
      herbrandQuotient
          (G := L ≃ₐ[K] L)
          (A := RelativeIdeleGroup.ClassGroup K L)
          sigma =
        (Module.finrank K L : ℚ) := by
    simpa only [Fintype.card_eq_nat_card,
      IsGalois.card_aut_eq_finrank K L] using
      hCvalue
  have hH0 :
      Nat.card
          (HerbrandH0 (L ≃ₐ[K] L)
            (RelativeIdeleGroup.ClassGroup K L)) =
        Module.finrank K L := by
    calc
      Nat.card
            (HerbrandH0 (L ≃ₐ[K] L)
              (RelativeIdeleGroup.ClassGroup K L)) =
          (RelativeIdeleGroup.Cohomology.ideleClassNorm K L).range.index :=
        (RelativeIdeleGroup.Cohomology.ideleClassNorm_index_eq_herbrandH0_card
          K L).symm
      _ = Module.finrank K L :=
        relativeIdeleClassNorm_index_eq_finrank_cyclic K L
  exact
    CyclicCohomology.lowDegree_card_eq_of_herbrandQuotient_eq_nat_of_le
      sigma (Module.finrank K L) Module.finrank_pos
      hQuotient hH0.le

end NormQuotientCommutativity

end GlobalClassFieldTheory.ClassFieldAxiom
end
end

section
-- module Solutions.OAIQ244_DUKE.LocalClassFieldTheory_Finite_LocalReciprocity_NormResidue
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 400000
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.KummerTheory.primeCyclotomicBaseIsGalois _root_.LocalClassFieldTheory.finiteGaloisLocalField_integerRing_moduleFinite _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.LubinTate.padicCompletedLevelField_isGalois _root_.LubinTate.standardLubinTateLevelField_isMulCommutative _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.CyclicCohomology.binaryCoefficientFamilyCommGroup _root_.LocalClassFieldTheory.comparisonIntegerRingIsIntegralClosure _root_.LocalClassFieldTheory.normalizationIntegerRingIsIntegralClosure _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.adicCompletionProperSpace _root_.chosenFinitePlaceLocalizedIsGalois _root_.finiteLocalUnitsOpen _root_.infiniteAdeleRingT2Space _root_.relativeUnrestrictedSPlaceFactorCommGroup
attribute [-simp] _root_.IsDiscreteValuationRing.addVal_ringEquiv _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.OAI.PrimeDegreePackets.ThetaConstruction.schwartzCM_apply _root_.RayClass.primesEquiv_val_eq_natGenerator _root_.infinitePlace_mult_smul
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI
attribute [local instance] OAI.starSubalgebraCommCStarAlgebra

set_option autoImplicit false

/-!
# The actual abelian local Artin map

For a finite abelian Galois extension, finite local reciprocity takes values
in the actual Galois group, not merely its abelianization.  This module
provides both the algebraic homomorphism and its continuous refinement for
the native topologies.
-/

noncomputable section

namespace LocalClassFieldTheory

open LocalFieldTheory
open scoped IsMulCommutative

variable (K L : Type) [Field K] [Field L] [Algebra K L]
  [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [FiniteDimensional K L] [IsAbelianGalois K L]

/-- The finite local Artin homomorphism with values in the actual Galois
group of an abelian extension. -/
noncomputable def abelianLocalArtinMonoidHom :
    Kˣ →* Gal(L / K) :=
  ((Abelianization.equivOfComm (H := Gal(L / K))).symm).toMonoidHom.comp
    (localArtinMonoidHom K L)

/-- The kernel of the actual abelian local Artin homomorphism is the norm
subgroup. -/
theorem abelianLocalArtinMonoidHom_ker :
    MonoidHom.ker (abelianLocalArtinMonoidHom K L) =
      localNormSubgroup K L := by
  rw [← localArtinMonoidHom_ker K L]
  ext a
  simp only [MonoidHom.mem_ker, abelianLocalArtinMonoidHom,
    MonoidHom.coe_comp, Function.comp_apply]
  constructor
  · intro ha
    apply (Abelianization.equivOfComm (H := Gal(L / K))).symm.injective
    simpa using ha
  · intro ha
    rw [ha, map_one]

end LocalClassFieldTheory
end
end

section
-- module Solutions.OAIQ244_DUKE.GlobalClassFieldTheory_Reciprocity_FinitePlaceArtin_NormRestriction
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.infinitePlaceBaseFourthRootField_isAbelianGalois _root_.GlobalClassFieldTheory.Reciprocity.infinitePlaceComplexificationOverfield_algebra _root_.GlobalClassFieldTheory.Reciprocity.infinitePlaceComplexificationOverfield_baseAlgebra _root_.GlobalClassFieldTheory.Reciprocity.infinitePlaceEmbeddedExtensionField_isAbelianGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalCyclotomicCompletionAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalCyclotomicLocalizedCompletionFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalCyclotomicLocalizedCompletionIsAlgebraic _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.KummerTheory.primeCyclotomicBaseFiniteDimensional _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.residueFieldZModAlgebra _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedIntegralAlgebraContextValuationSubringAlgebra _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedIntegralAlgebraContextValuationSubringTower _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedIntegralLatticeContextModuleFinite _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedIntegralLatticeContextModuleFree _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedQPadicContextValuationSubringTower _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.LubinTate.padicCompletedLevelField_algebra _root_.LubinTate.padicCompletedLevelField_finiteDimensional _root_.LubinTate.padicCompletedUnramifiedFieldAlgebra _root_.LubinTate.standardLubinTateLevelField_isAbelianGalois _root_.LubinTate.standardLubinTateLevelValuationSubring_moduleFinite _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.diagonalLogAction _root_.OAI.PrimeDegreePackets.instTopologicalSpaceLocalAlgebra _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.LocalClassFieldTheory.normalizationIntegerRingIsIntegralClosure _root_.chosenFinitePlaceBaseIsNonarchimedeanLocalField _root_.chosenFinitePlaceBaseValuativeRel _root_.chosenFinitePlaceCompletionAlgebra _root_.chosenFinitePlaceCompletionContinuousSMul _root_.chosenFinitePlaceCompletionFiniteDimensional _root_.chosenFinitePlaceCompletionLocallyCompactSpace _root_.chosenFinitePlaceExtensionCompletionAlgebra _root_.chosenFinitePlaceExtensionCompletionSMul _root_.chosenFinitePlaceLocalizedFiniteDimensional _root_.chosenFinitePlaceLocalizedIntegerAlgebra _root_.chosenFinitePlaceLocalizedIntegerModuleFinite _root_.chosenFinitePlaceLocalizedIsGalois _root_.chosenFinitePlaceLocalizedIsIntegralClosure _root_.chosenFinitePlaceLocalizedIsNonarchimedeanLocalField _root_.chosenFinitePlaceLocalizedIsUltrametricDist _root_.chosenFinitePlaceLocalizedIsValuativeTopology _root_.chosenFinitePlaceLocalizedLocallyCompactSpace _root_.chosenFinitePlaceLocalizedValuationCompatible _root_.chosenFinitePlaceLocalizedValuationHasExtension _root_.chosenFinitePlaceLocalizedValuationIsNontrivial _root_.chosenFinitePlaceLocalizedValuativeRel _root_.chosenFinitePlaceLocalizedValuativeRelIsNontrivial _root_.chosenFinitePlaceLocalizedValued
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
# Norm--restriction for finite-place Artin homomorphisms

This module proves norm--restriction naturality for finite-place Artin maps in an actual square of number fields and their chosen completed local extensions.
-/

open scoped Classical IsMulCommutative NNReal NumberField
open NumberField IsDedekindDomain

noncomputable section

namespace GlobalClassFieldTheory
namespace Reciprocity

open AlgebraicNumberTheory.Valuations
open HilbertRamification
open LocalClassFieldTheory
open LocalFieldTheory

variable {K L : Type}
    [Field K] [NumberField K]
    [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsAbelianGalois K L]

section FinitePlaceNormRestrictionInstances

variable {K' L' : Type}
    [Field K'] [NumberField K']
    [Field L'] [NumberField L']
    [Algebra K K'] [Algebra K' L'] [Algebra K L']
    [IsScalarTower K K' L']
    [Algebra L L'] [IsScalarTower K L L']
    [IsAbelianGalois K' L']
    (v : HeightOneSpectrum (𝓞 K))
    (W : HeightOneSpectrum (𝓞 K'))
    (w : AbsoluteValueExtension
      (NumberField.HeightOneSpectrum.adicAbv K v) L)
    (w' : AbsoluteValueExtension
      (NumberField.HeightOneSpectrum.adicAbv K' W) L')

local notation "vKₙ" =>
  NumberField.HeightOneSpectrum.adicAbv K v
local notation "vKₙ'" =>
  NumberField.HeightOneSpectrum.adicAbv K' W
local notation "Cₙ" =>
  finitePlaceNormCompletion K v
local notation "Dₙ" =>
  finitePlaceNormCompletion K' W
local notation "Eₙ" =>
  finitePlaceNormLocalizedCompletion K L v w
local notation "Eₙ'" =>
  finitePlaceNormLocalizedCompletion K' L' W w'

local instance finitePlaceNormLowerExtensionAlgebra_r87910d_1 :
    Algebra K w.1.Completion :=
  AbsoluteValue.extensionCompletionAlgebra
    (K := K) w.1
local instance finitePlaceNormLowerCompletionAlgebra_r87910d_1 :
    Algebra Cₙ w.1.Completion :=
  AbsoluteValue.completionAlgebra vKₙ w.1 w.2
local instance finitePlaceNormLowerGlobalAlgebra_r87910d_1 :
    Algebra K Eₙ :=
  LocalClassFieldTheory.localizedCompletionGlobalAlgebra vKₙ w
local instance finitePlaceNormUpperExtensionAlgebra_r87910d_1 :
    Algebra K' w'.1.Completion :=
  AbsoluteValue.extensionCompletionAlgebra
    (K := K') w'.1
attribute [local instance] GlobalClassFieldTheory.Reciprocity.finitePlaceNormUpperCompletionAlgebra
local instance finitePlaceNormUpperGlobalAlgebra_r87910d_1 :
    Algebra K' Eₙ' :=
  LocalClassFieldTheory.localizedCompletionGlobalAlgebra vKₙ' w'
local instance finitePlaceNormLowerNontriviallyNormedField_r87910d_1 :
    NontriviallyNormedField Cₙ :=
  absoluteValueExtension_completionNontriviallyNormedField
    vKₙ (RayClass.adicAbv_isNontrivial v)
local instance finitePlaceNormLowerLocallyCompactSpace_r87910d_1 :
    LocallyCompactSpace Cₙ :=
  AbsoluteValue.Completion.locallyCompactSpace
    (finitePlaceCompletionBaseMap_isometry v)
attribute [local instance] GlobalClassFieldTheory.Reciprocity.finitePlaceNormUpperNontriviallyNormedField
attribute [local instance] GlobalClassFieldTheory.Reciprocity.finitePlaceNormUpperLocallyCompactSpace
attribute [local instance] GlobalClassFieldTheory.Reciprocity.finitePlaceNormLowerLocalizedFiniteDimensional
local instance finitePlaceNormLowerLocalizedAbelianGalois_r87910d_1 :
    IsAbelianGalois Cₙ Eₙ :=
  LocalClassFieldTheory.localizedCompletion_isAbelianGalois
    vKₙ (RayClass.adicAbv_isNontrivial v) w
attribute [local instance] GlobalClassFieldTheory.Reciprocity.finitePlaceNormUpperLocalizedFiniteDimensional
attribute [local instance] GlobalClassFieldTheory.Reciprocity.finitePlaceNormUpperLocalizedAbelianGalois
local instance finitePlaceNormLowerUltrametric_r87910d_1 :
    IsUltrametricDist Cₙ :=
  finitePlaceArtinCompletionIsUltrametricDist vKₙ
    (NumberField.HeightOneSpectrum.isNonarchimedean_adicAbv K v)
local instance finitePlaceNormLowerValued_r87910d_1 :
    Valued Cₙ ℝ≥0 :=
  finitePlaceArtinCompletionValued vKₙ
    (NumberField.HeightOneSpectrum.isNonarchimedean_adicAbv K v)
local instance finitePlaceNormLowerValuationNontrivial_r87910d_1 :
    (Valued.v : Valuation Cₙ ℝ≥0).IsNontrivial :=
  (inferInstance :
    (NormedField.valuation (K := Cₙ)).IsNontrivial)
local instance finitePlaceNormLowerValuativeRel_r87910d_1 :
    ValuativeRel Cₙ :=
  finitePlaceArtinCompletionValuativeRel vKₙ
    (NumberField.HeightOneSpectrum.isNonarchimedean_adicAbv K v)
local instance finitePlaceNormLowerValuationCompatible_r87910d_1 :
    (Valued.v : Valuation Cₙ ℝ≥0).Compatible :=
  Valuation.Compatible.ofValuation
    (Valued.v : Valuation Cₙ ℝ≥0)
local instance finitePlaceNormLowerValuativeRelNontrivial_r87910d_1 :
    ValuativeRel.IsNontrivial Cₙ :=
  (ValuativeRel.isNontrivial_iff_isNontrivial
    (Valued.v : Valuation Cₙ ℝ≥0)).2 inferInstance
local instance finitePlaceNormLowerLocalField_r87910d_1 :
    IsNonarchimedeanLocalField Cₙ :=
  finitePlaceArtinCompletionIsNonarchimedeanLocalField vKₙ
    (NumberField.HeightOneSpectrum.isNonarchimedean_adicAbv K v)
attribute [local instance] GlobalClassFieldTheory.Reciprocity.finitePlaceNormUpperUltrametric
local instance finitePlaceNormUpperValued_r87910d_1 :
    Valued Dₙ ℝ≥0 :=
  finitePlaceArtinCompletionValued vKₙ'
    (NumberField.HeightOneSpectrum.isNonarchimedean_adicAbv K' W)
local instance finitePlaceNormUpperValuationNontrivial_r87910d_1 :
    (Valued.v : Valuation Dₙ ℝ≥0).IsNontrivial :=
  (inferInstance :
    (NormedField.valuation (K := Dₙ)).IsNontrivial)
attribute [local instance] GlobalClassFieldTheory.Reciprocity.finitePlaceNormUpperValuativeRel
local instance finitePlaceNormUpperValuationCompatible_r87910d_1 :
    (Valued.v : Valuation Dₙ ℝ≥0).Compatible :=
  Valuation.Compatible.ofValuation
    (Valued.v : Valuation Dₙ ℝ≥0)
local instance finitePlaceNormUpperValuativeRelNontrivial_r87910d_1 :
    ValuativeRel.IsNontrivial Dₙ :=
  (ValuativeRel.isNontrivial_iff_isNontrivial
    (Valued.v : Valuation Dₙ ℝ≥0)).2 inferInstance
attribute [local instance] GlobalClassFieldTheory.Reciprocity.finitePlaceNormUpperLocalField
noncomputable def finitePlaceNormUpperRawArtin
    (y : Dₙˣ) :
    finitePlaceNormLocalizedAut K' L' W w' :=
  LocalClassFieldTheory.abelianLocalArtinMonoidHom
    Dₙ Eₙ' y

noncomputable def finitePlaceNormLowerRawArtin
    (hW : finitePlaceBelow (K := K) W = v)
    (y : Dₙˣ) :
    finitePlaceNormLocalizedAut K L v w :=
  LocalClassFieldTheory.abelianLocalArtinMonoidHom
    Cₙ Eₙ
    (finitePlaceRelativeNormUnits
      (K := K) (K' := K') v W hW y)

end FinitePlaceNormRestrictionInstances

end Reciprocity
end GlobalClassFieldTheory
end
end

section
-- module Solutions.OAIQ244_DUKE.LubinTate_Padic_ChangedUniformizerIntertwiner_IntertwinerConstruction
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 400000
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalClassFieldTheory.finiteGaloisLocalField_integerRing_moduleFinite _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitInverseLimitCarrierPadicModule _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitInverseLimitCarrierPadicSMul _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitQuotientCarrierPadicModule _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitQuotientCarrier_finite _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.adicPrincipalUnitsContinuousAdd _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.adicPrincipalUnitsContinuousSMul _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.adicPrincipalUnitsPadicModule _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.discretePrincipalUnitQuotientFinite _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.discretePrincipalUnitQuotientPadicModule _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitPadicModule _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitPadicSMul _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitProdiscreteLimitContinuousAdd _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitProdiscreteLimitContinuousSMul _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitProdiscreteLimitPadicModule _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.residueFieldZModAlgebra _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedIntegralAlgebraContextFieldAlgebra _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedIntegralAlgebraContextQPadic _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedIntegralAlgebraContextQPadicTower _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedIntegralAlgebraContextValuationSubringAlgebra _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedIntegralAlgebraContextValuationSubringTower _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedIntegralLatticeContextAlgebra _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedIntegralLatticeContextModuleFinite _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedIntegralLatticeContextModuleFree _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedMaximalIdealPowContextModuleFinite _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedMaximalIdealPowContextModuleFree _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedQPadicContextAlgebra _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedQPadicContextFact _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedQPadicContextFiniteDimensional _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedQPadicContextValuationExtension _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedQPadicContextValuationSubringTower _root_.LocalFieldTheory.DiscreteValuationField.finite_principalUnits_nthPowerKernel _root_.LocalFieldTheory.DiscreteValuationField.finite_residueRootsOfUnityGroup _root_.LocalFieldTheory.DiscreteValuationField.finite_valuationSubringUnits_nthPowerKernel _root_.LocalFieldTheory.DiscreteValuationField.finite_valuationSubringUnits_nthPowerQuotient _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.LubinTate.padicCompletedLevelCompleteDVF_hasExtensionInstance _root_.LubinTate.padicCompletedLevelField_algebra _root_.LubinTate.padicCompletedLevelField_finiteDimensional _root_.LubinTate.padicCompletedLevelField_isGalois _root_.LubinTate.standardLubinTateLevelField_galFinite _root_.LubinTate.standardLubinTateLevelField_isAbelianGalois _root_.LubinTate.standardLubinTateLevelField_isMulCommutative _root_.LubinTate.standardLubinTateUnitParameter_commGroup _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RamificationTheory.HilbertRamification.Higher.lowerRamificationGroup.instNormal _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionResidueField.instField _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.LocalClassFieldTheory.comparisonIntegerRingIsIntegralClosure _root_.LocalClassFieldTheory.normalizationIntegerRingIsIntegralClosure _root_.RamificationTheory.HilbertRamification.CompleteDVF.decompositionGroupMulSemiringAction _root_.RamificationTheory.HilbertRamification.CompleteDVF.decompositionGroupResidueFieldMulSemiringAction _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen _root_.infiniteAdeleRingT2Space
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

theorem padicChangedUniformizerIntertwiner_hasSubst
    (p : ℕ) [Fact p.Prime]
    (u : (padicLocalField p).valuationSubringˣ) :
    PowerSeries.HasSubst
      (padicChangedUniformizerIntertwiner p u) :=
  PowerSeries.HasSubst.of_constantCoeff_zero'
    (padicChangedUniformizerIntertwiner_constantCoeff p u)

end LubinTate

end
end


