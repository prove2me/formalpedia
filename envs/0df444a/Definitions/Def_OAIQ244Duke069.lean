-- Prove2me | Definitions.Def_OAIQ244Duke069
-- name    : OAIQ244Duke069
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-13T22:45:02.763777+00:00
-- url     : https://prove2.me/theorems/e3bdb292-507a-48f6-b149-68b6ede08574
-- title:
--   Definitions bundle OAIQ244Duke069 of the split of OpenAI, Equidistribution of Prime-Degree Torus Packets with Arbitrary Local Type
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.DukePrimeDegree.prime_degree_packet_measure_equidistribution_unconditional` and `OAI.DukePrimeDegree.prime_degree_packet_measures_tendsto_haar_unconditional`, carved from OpenAI's openai/math development (OpenAI, *Equidistribution of Prime-Degree Torus Packets with Arbitrary Local Type*, OpenAI Math Release, September 24, 2026, result family 15, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 43 declarations of OpenAI's Lean: 15 definitions and 28 theorems. The definitions and types are `GlobalClassFieldTheory.ClassFieldAxiom.sUnitKummerCoordinateBasePlaceCandidates`, `GlobalClassFieldTheory.Cohomology.AboveSUnitHerbrandQuotientDefined`, `GlobalClassFieldTheory.Cohomology.RelativeIdeleSupportedHerbrandQuotientDefined`, `GlobalClassFieldTheory.Cohomology.aboveSLogPlaceMulAction`, `GlobalClassFieldTheory.Cohomology.logPlaceBelowRelativeUnrestrictedIndex`, `GlobalClassFieldTheory.Cohomology.logPlaceOrbitBelowRelativeUnrestrictedIndex`, `GlobalClassFieldTheory.Cohomology.logPlaceOrbitEquivRelativeUnrestrictedSPlaceIndex`, `GlobalClassFieldTheory.Cohomology.relativeIdeleSupportedToClass`, `GlobalClassFieldTheory.Cohomology.sUnitToRelativeIdeleSupported`, `IdeleGroup.classRepresentativeSupport`, `IdeleGroup.sufficientlyLargeFiniteSet`, `LocalClassFieldTheory.localArtinMonoidHom`, `ideleClassHerbrandSupport`, `sUnitEquivRelativePrincipalSupportedIntersection`, `sUnitToRelativePrincipalSupportedIntersection`.
--
--   **Sources.** They come from these modules of lean/OAI/NumberTheory, in whole or in part: `AlgebraicNumberTheory_Idele_Cohomology_Decomposition`, `AlgebraicNumberTheory_Idele_Cohomology_SPlaces_OutsideIntegralInduced_ChosenPlace`, `AlgebraicNumberTheory_Idele_Cohomology_SPlaces_OutsideIntegralInduced_ChosenPlaceAction`, `AlgebraicNumberTheory_Idele_Cohomology_SupportedBridge`, `AlgebraicNumberTheory_Idele_NormApproximation_FinitePlaces`, `AlgebraicNumberTheory_Idele_NormApproximation_InfinitePlaces`, `AlgebraicNumberTheory_Idele_SufficientlyLarge`, `GlobalClassFieldTheory_ClassFieldAxiom_KummerLocalNormContainment`, `GlobalClassFieldTheory_ClassFieldAxiom_SUnitKummerPrimeSelection_BasePlaceSelection`, `GlobalClassFieldTheory_Cohomology_CyclicPrimePowerFullDecomposition`, `GlobalClassFieldTheory_Cohomology_IdeleClassHerbrandSupportedFinal`, `LocalClassFieldTheory_Finite_LocalReciprocity_Main`, `LocalClassFieldTheory_Finite_LocalReciprocity_TopologicalReciprocity`, `LocalClassFieldTheory_Finite_Unramified_Cohomology`.
--
--   **Imports.** It imports the bundles `OAIQ244Duke041`, `OAIQ244Duke062`, `OAIQ244Duke063` and `OAIQ244Duke064` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ244Duke074`, `OAIQ244Duke075`, `OAIQ244Duke076` and `OAIQ244Duke078`.
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
import Mathlib.Algebra.Group.Equiv.TypeTags
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
import Mathlib.FieldTheory.Galois.Profinite
import Mathlib.FieldTheory.IntermediateField.Adjoin.Algebra
import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
import Mathlib.FieldTheory.IntermediateField.Basic
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
import Mathlib.RingTheory.Polynomial.GaussLemma
import Mathlib.RingTheory.Polynomial.Vieta
import Mathlib.RingTheory.PowerSeries.Evaluation
import Mathlib.RingTheory.PowerSeries.Log
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
import Definitions.Def_OAIQ244Duke041
import Definitions.Def_OAIQ244Duke062
import Definitions.Def_OAIQ244Duke063
import Definitions.Def_OAIQ244Duke064

section
-- module Solutions.OAIQ244_DUKE.LocalClassFieldTheory_Finite_Unramified_Cohomology
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.DiscreteNthRootsSubgroup.instCommGroupSubtypeUnitsMemSubgroup _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalClassFieldTheory.finiteGaloisLocalField_integerRing_moduleFinite _root_.LocalClassFieldTheory.localDecompositionResidueFintype _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.residueFieldZModAlgebra _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedIntegralAlgebraContextValuationSubringAlgebra _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.LubinTate.compatibleGroupFamiliesCommGroup _root_.LubinTate.compatibleGroupFamiliesGroup _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.instTopologicalSpaceLocalAlgebra _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RamificationTheory.HilbertRamification.ValuationSubring.selectedResidueField.instAlgebra _root_.RayClass.approximationCompletionTopologicalSpace _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.CyclicCohomology.binaryCoefficientFamilyCommGroup _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.LocalClassFieldTheory.comparisonIntegerRingIsIntegralClosure _root_.LocalClassFieldTheory.normalizationIntegerRingIsIntegralClosure _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.chosenFinitePlaceCompletionAlgebra _root_.finiteLocalUnitsOpen _root_.infiniteAdeleRingT2Space _root_.relativeAdeleRingIntermediateAlgebra _root_.relativeAdeleRingTopIntermediateAlgebra _root_.relativeUnrestrictedSPlaceFactorCommGroup
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

/-!
# Tate cohomology of units in unramified extensions

For an unramified extension of local fields the actual low-degree Tate
cohomology of the integer units and of every principal-unit group is trivial.
The norm statements are the corresponding actual norm surjections.
-/

noncomputable section

universe u

namespace LocalClassFieldTheory

open scoped ValuativeRel
open LocalFieldTheory
open LocalFieldTheory.IsNonarchimedeanLocalField
open CyclicCohomology
open CyclicCohomology.ProfiniteCohomology.Herbrand

/-- Generator-explicit form of the unramified unit-cohomology theorem.  The canonical
endpoint below supplies the canonical unramified arithmetic Frobenius. -/
theorem unramified_units_tateCohomology_and_norm_surjective_for_generator
    (K L : Type) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    [ValuativeRel L] [UniformSpace L] [IsUniformAddGroup L]
    [IsNonarchimedeanLocalField L]
    [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]
    [IsIntegralClosure 𝒪[L] 𝒪[K] L] [Module.Finite 𝒪[K] 𝒪[L]]
    [IsUnramifiedValuedExtension K L]
    (g : Gal(L / K)) (hg : ∀ sigma : Gal(L / K), sigma ∈ Subgroup.zpowers g) :
    letI := galoisGroupIntegerUnitsMulDistribMulActionOfIsIntegralClosure K L
    (Subsingleton (HerbrandH0 Gal(L / K) 𝒪[L]ˣ) ∧
      Subsingleton (HerbrandHMinusOne Gal(L / K) 𝒪[L]ˣ g)) ∧
      (∀ n : Nat, 1 ≤ n →
        letI := galoisGroupPrincipalUnitsMulDistribMulActionOfIsIntegralClosure K L n
        Subsingleton (HerbrandH0 Gal(L / K) (principalUnits L n)) ∧
          Subsingleton
            (HerbrandHMinusOne Gal(L / K) (principalUnits L n) g)) ∧
      MonoidHom.range (normIntegerUnits K L) = ⊤ ∧
      ∀ n : Nat, 1 ≤ n → MonoidHom.range
        (principalUnitsNormOfUnramifiedValuationOfIsIntegralClosure K L n) = ⊤ := by
  refine ⟨unramified_integerUnits_herbrand_subsingleton K L g hg, ?_,
    MonoidHom.range_eq_top_of_surjective (normIntegerUnits K L)
      (normIntegerUnits_surjective_unramified_of_isIntegralClosure K L), ?_⟩
  · intro n hn
    exact unramified_principalUnits_herbrand_subsingleton K L n hn g hg
  · intro n hn
    exact MonoidHom.range_eq_top_of_surjective
      (principalUnitsNormOfUnramifiedValuationOfIsIntegralClosure K L n)
      (principalUnitsNormOfUnramifiedValuationOfIsIntegralClosure_surjective
        K L n hn)

end LocalClassFieldTheory
end
end

section
-- module Solutions.OAIQ244_DUKE.AlgebraicNumberTheory_Idele_Cohomology_Decomposition
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.DiscreteNthRootsSubgroup.instCommGroupSubtypeUnitsMemSubgroup _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalClassFieldTheory.finiteGaloisLocalField_integerRing_moduleFinite _root_.LocalClassFieldTheory.localDecompositionResidueFintype _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.residueFieldZModAlgebra _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedIntegralAlgebraContextValuationSubringAlgebra _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.LubinTate.compatibleGroupFamiliesCommGroup _root_.LubinTate.compatibleGroupFamiliesGroup _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.instTopologicalSpaceLocalAlgebra _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RamificationTheory.HilbertRamification.ValuationSubring.selectedResidueField.instAlgebra _root_.RayClass.approximationCompletionTopologicalSpace _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.CyclicCohomology.binaryCoefficientFamilyCommGroup _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.LocalClassFieldTheory.comparisonIntegerRingIsIntegralClosure _root_.LocalClassFieldTheory.normalizationIntegerRingIsIntegralClosure _root_.adicCompletionProperSpace _root_.chosenFinitePlaceCompletionAlgebra _root_.relativeAdeleRingIntermediateAlgebra _root_.relativeAdeleRingTopIntermediateAlgebra _root_.relativeUnrestrictedSPlaceFactorCommGroup
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

/-!
# Finite-support decompositions of actual ideles

For a finite set `S` of finite places, this file identifies the actual
subgroup `I_K^S` with the product of all archimedean local groups, the
full multiplicative groups at places in `S`, and the local unit groups
away from `S`.  The construction is componentwise and uses the genuine
restricted-product membership condition.

For a finite family of base places in a Galois extension, it also
assembles the local tensor-algebra decomposition and proves its
equivariance for the full Galois action.  Finally, the concrete
unramified local class-field theorem is transported through Shapiro to
show that every unramified induced integer-unit block has trivial
`H⁰` and `H⁻¹`.
-/

open scoped NumberField RestrictedProduct ValuativeRel
open NumberField IsDedekindDomain

noncomputable section

open LocalClassFieldTheory

open AlgebraicNumberTheory.Valuations
open HilbertRamification
open LocalClassFieldTheory
open LocalFieldTheory
open CyclicCohomology.ProfiniteCohomology.Herbrand
open CyclicCohomology

universe u

variable {F : Type u} [Field F] [NumberField F]

section UnramifiedLocalUnits

/-- Outside the ramified support, the local integer-unit factor has
trivial low-degree Tate cohomology.  This generator-explicit form is the
one needed after restricting a global cyclic generator to a decomposition
group. -/
theorem unramifiedLocalIntegerUnitsHerbrand_subsingleton
    (k ell : Type)
    [Field k] [Field ell] [Algebra k ell]
    [FiniteDimensional k ell] [IsGalois k ell]
    [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k]
    [ValuativeRel ell] [UniformSpace ell]
    [IsUniformAddGroup ell]
    [IsNonarchimedeanLocalField ell]
    [Valuation.HasExtension
      (ValuativeRel.valuation k) (ValuativeRel.valuation ell)]
    [IsIntegralClosure 𝒪[ell] 𝒪[k] ell]
    [Module.Finite 𝒪[k] 𝒪[ell]]
    [LocalFieldTheory.IsNonarchimedeanLocalField.IsUnramifiedValuedExtension
      k ell]
    (g : Gal(ell / k))
    (hg : ∀ σ : Gal(ell / k),
      σ ∈ Subgroup.zpowers g) :
    letI :=
      galoisGroupIntegerUnitsMulDistribMulActionOfIsIntegralClosure
        k ell
    Subsingleton
        (HerbrandH0 (Gal(ell / k)) 𝒪[ell]ˣ) ∧
      Subsingleton
        (HerbrandHMinusOne
          (Gal(ell / k)) 𝒪[ell]ˣ g) := by
  exact
    (unramified_units_tateCohomology_and_norm_surjective_for_generator
      k ell g hg).1

end UnramifiedLocalUnits
end
end

section
-- module Solutions.OAIQ244_DUKE.LocalClassFieldTheory_Finite_LocalReciprocity_Main
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 400000
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalClassFieldTheory.finiteGaloisLocalField_integerRing_moduleFinite _root_.LocalClassFieldTheory.realComplexNormQuotientFinite _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.CyclicCohomology.binaryCoefficientFamilyCommGroup _root_.LocalClassFieldTheory.comparisonIntegerRingIsIntegralClosure _root_.LocalClassFieldTheory.normalizationIntegerRingIsIntegralClosure _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen _root_.infiniteAdeleRingT2Space _root_.relativeUnrestrictedSPlaceFactorCommGroup
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

namespace LocalClassFieldTheory

open LocalFieldTheory

/-!
# Finite local reciprocity: the local reciprocity law

The residue Frobenius datum, the normalized henselian valuation, and the
class-field axiom constructed over the fixed separable closure are inserted
into the abstract reciprocity theorem.  The resulting isomorphism is independent of the
embedding used to realize the finite Galois extension in that closure.
-/

noncomputable section

variable (K L : Type) [Field K] [Field L] [Algebra K L]
  [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [FiniteDimensional K L] [IsGalois K L]

/-- The local norm-residue symbol is the inverse of reciprocity, preceded by
the quotient map from `Kˣ`. -/
noncomputable def localArtinMonoidHom :
    Kˣ →* Abelianization (Gal(L / K)) :=
  (abelianizationEquivNormQuotient K L).symm.toMonoidHom.comp
    (normClass K L)

/-- The kernel of the local norm-residue symbol is exactly the norm
subgroup `N_{L/K}(Lˣ)`. -/
theorem localArtinMonoidHom_ker :
    (localArtinMonoidHom K L).ker = localNormSubgroup K L := by
  ext x
  rw [MonoidHom.mem_ker]
  change
    (abelianizationEquivNormQuotient K L).symm
        (normClass K L x) = 1 ↔
      x ∈ localNormSubgroup K L
  constructor
  · intro hx
    have hx' := congrArg (abelianizationEquivNormQuotient K L) hx
    rw [(abelianizationEquivNormQuotient K L).apply_symm_apply, map_one] at hx'
    exact (normClass_eq_one_iff_mem K L x).mp hx'
  · intro hx
    have hq : normClass K L x = 1 :=
      (normClass_eq_one_iff_mem K L x).2 hx
    rw [hq, map_one]

end
end LocalClassFieldTheory
end

section
-- module Solutions.OAIQ244_DUKE.LocalClassFieldTheory_Finite_LocalReciprocity_TopologicalReciprocity
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.GlobalClassFields.ConductorialSubgroup.finiteIndex _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.IdeleClassGroup.normOneSubgroupCompactSpace _root_.KummerTheory.DiscreteNthRootsSubgroup.instTopologicalSpaceSubtypeUnitsMemSubgroup _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalClassFieldTheory.finiteGaloisLocalField_integerRing_moduleFinite _root_.LocalClassFieldTheory.realComplexNormQuotientFinite _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.residueFieldZModAlgebra _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedIntegralAlgebraContextValuationSubringAlgebra _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedIntegralAlgebraContextValuationSubringTower _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedQPadicContextValuationSubringTower _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.LubinTate.compatibleGroupFamiliesGroup _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction_continuous _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.completedMaximalOrderCompactSpace _root_.OAI.PrimeDegreePackets.diagonalLogAction _root_.OAI.PrimeDegreePackets.diagonalLogAction_continuous _root_.OAI.PrimeDegreePackets.gLocallyCompact _root_.OAI.PrimeDegreePackets.instContinuousSMulPadicLocalAlgebra _root_.OAI.PrimeDegreePackets.instIsTopologicalRingLocalAlgebra _root_.OAI.PrimeDegreePackets.instLocallyCompactSpaceLocalAlgebra _root_.OAI.PrimeDegreePackets.instT2SpaceLocalAlgebra _root_.OAI.PrimeDegreePackets.instTopologicalSpaceLocalAlgebra _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.OAI.PrimeDegreePackets.xLocallyCompact _root_.OAI.PrimeDegreePackets.xMetrizable _root_.OAI.PrimeDegreePackets.xT2Space _root_.RayClass.Modulus.infiniteCongruenceSubgroupFiniteIndex _root_.RayClass.approximationCompletionTopologicalSpace _root_.RayClass.congruenceSubgroupFiniteIndex _root_.RayClass.ideleCongruenceSupPrincipalFiniteIndex _root_.RayClass.narrowInfiniteCongruenceSubgroupFiniteIndex _root_.RayClass.ordinaryIdealClassSubgroupFiniteIndex _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.RelativeIdeleGroup.relativeIdeleMulAction _root_.CyclicCohomology.binaryCoefficientFamilyCommGroup _root_.LocalClassFieldTheory.comparisonIntegerRingIsIntegralClosure _root_.LocalClassFieldTheory.normalizationIntegerRingIsIntegralClosure _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.adicCompletionProperSpace _root_.chosenFinitePlaceBaseIsUltrametricDist _root_.chosenFinitePlaceBaseIsValuativeTopology _root_.chosenFinitePlaceBaseLocallyCompactSpace _root_.chosenFinitePlaceBaseValuationCompatible _root_.chosenFinitePlaceBaseValuationIsNontrivial _root_.chosenFinitePlaceBaseValuativeRelIsNontrivial _root_.chosenFinitePlaceBaseValued _root_.chosenFinitePlaceCompletionAlgebra _root_.chosenFinitePlaceCompletionContinuousSMul _root_.chosenFinitePlaceLocalizedIntegerAlgebra _root_.finiteIdeleGroupIsTopologicalGroup _root_.finiteIdeleGroupLocallyCompactSpace _root_.finiteIdeleGroupT2Space _root_.finiteLocalUnitsOpen _root_.ideleGroupIsTopologicalGroup _root_.ideleGroupLocallyCompactSpace _root_.ideleGroupT2Space _root_.infiniteAdeleRingT2Space _root_.infiniteIdeleGroupLocallyCompactSpace _root_.infiniteIdeleGroupT2Space _root_.relativeAdeleRingIntermediateAlgebra _root_.relativeAdeleRingTopIntermediateAlgebra _root_.relativeUnrestrictedSPlaceFactorCommGroup
attribute [-simp] _root_.IsDiscreteValuationRing.addVal_ringEquiv _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.OAI.PrimeDegreePackets.ThetaConstruction.schwartzCM_apply _root_.RayClass.primesEquiv_val_eq_natGenerator _root_.infinitePlace_mult_smul
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

/-!
# Topological finite local reciprocity

This module upgrades the algebraic finite local reciprocity isomorphism to a
homeomorphic group isomorphism.  The key input is that the norm subgroup of a
finite Galois extension is open.  Consequently its quotient is discrete, as
is the topological abelianization of the finite Krull Galois group.
-/

noncomputable section

namespace LocalClassFieldTheory

open scoped NNReal ValuativeRel
open LocalFieldTheory
open LocalFieldTheory.IsNonarchimedeanLocalField

section NormSubgroupTopology

universe u

noncomputable local instance normQuotientTopologicalSpace_r95b69b_1
    (K L : Type) [Field K] [Field L] [Algebra K L]
    [TopologicalSpace K] :
    TopologicalSpace (NormQuotient K L) := by
  change TopologicalSpace (Kˣ ⧸ localNormSubgroup K L)
  infer_instance
theorem localNormSubgroup_isOpen_of_compatibleLocalField
    (K L : Type)
    [NontriviallyNormedField K] [NormedField L] [NormedAlgebra K L]
    [CompleteSpace K]
    [ValuativeRel K] [IsNonarchimedeanLocalField K]
    [ValuativeRel L] [IsNonarchimedeanLocalField L]
    [FiniteDimensional K L] [IsGalois K L]
    [Valuation.HasExtension (ValuativeRel.valuation K)
      (ValuativeRel.valuation L)]
    [IsIntegralClosure 𝒪[L] 𝒪[K] L] :
    IsOpen (localNormSubgroup K L : Set Kˣ) := by
  have hintersection :
      integerUnitNormSubgroup K L =
        localNormSubgroup K L ⊓ localBaseUnitSubgroup K :=
    integerUnitNormSubgroup_eq_localNormSubgroup_inf_baseUnits K L
  have hcompact : IsCompact (integerUnitNormSubgroup K L : Set Kˣ) :=
    integerUnitNormSubgroup_isCompact K L
  have hclosed : IsClosed (integerUnitNormSubgroup K L : Set Kˣ) :=
    hcompact.isClosed

  let : Finite (Gal(L / K)) := by
    apply Nat.finite_of_card_ne_zero
    rw [IsGalois.card_aut_eq_finrank K L]
    exact Nat.ne_of_gt Module.finrank_pos
  let : Finite (Abelianization (Gal(L / K))) :=
    Finite.of_surjective Abelianization.of QuotientGroup.mk_surjective
  let : Finite (NormQuotient K L) :=
    Finite.of_equiv
      (Abelianization (Gal(L / K)))
      (abelianizationEquivNormQuotient K L).toEquiv
  let : Finite (Kˣ ⧸ localNormSubgroup K L) := by
    change Finite (NormQuotient K L)
    infer_instance
  let : (localNormSubgroup K L).FiniteIndex :=
    Subgroup.finiteIndex_of_finite_quotient
  let : ((localNormSubgroup K L).subgroupOf
      (localBaseUnitSubgroup K)).FiniteIndex := inferInstance

  have hrelativeClosed :
      IsClosed
        ((localNormSubgroup K L).subgroupOf (localBaseUnitSubgroup K) :
          Set (localBaseUnitSubgroup K)) := by
    have hpreimage :
        IsClosed ((fun z : localBaseUnitSubgroup K => (z : Kˣ)) ⁻¹'
          (integerUnitNormSubgroup K L : Set Kˣ)) :=
      hclosed.preimage continuous_subtype_val
    rw [show
        ((localNormSubgroup K L).subgroupOf (localBaseUnitSubgroup K) :
            Set (localBaseUnitSubgroup K)) =
          (fun z : localBaseUnitSubgroup K => (z : Kˣ)) ⁻¹'
            (integerUnitNormSubgroup K L : Set Kˣ) by
      ext z
      change (z : Kˣ) ∈ localNormSubgroup K L ↔
        (z : Kˣ) ∈ integerUnitNormSubgroup K L
      rw [hintersection]
      constructor
      · intro hz
        exact ⟨hz, z.property⟩
      · exact fun hz => hz.1]
    exact hpreimage

  have hrelativeOpen :
      IsOpen
        ((localNormSubgroup K L).subgroupOf (localBaseUnitSubgroup K) :
          Set (localBaseUnitSubgroup K)) :=
    Subgroup.isOpen_of_isClosed_of_finiteIndex _ hrelativeClosed
  have himageOpen :
      IsOpen (Subtype.val ''
        ((localNormSubgroup K L).subgroupOf (localBaseUnitSubgroup K) :
          Set (localBaseUnitSubgroup K))) :=
    (localBaseUnitSubgroup_isOpen K).isOpenMap_subtype_val _ hrelativeOpen
  have himage :
      Subtype.val ''
          ((localNormSubgroup K L).subgroupOf (localBaseUnitSubgroup K) :
            Set (localBaseUnitSubgroup K)) =
        (integerUnitNormSubgroup K L : Set Kˣ) := by
    ext x
    constructor
    · rintro ⟨z, hz, rfl⟩
      rw [hintersection]
      exact ⟨hz, z.property⟩
    · intro hx
      have hx' := hx
      rw [hintersection] at hx'
      exact ⟨⟨x, hx'.2⟩, hx'.1, rfl⟩
  rw [himage] at himageOpen

  apply Subgroup.isOpen_mono
    (H₁ := integerUnitNormSubgroup K L)
    (H₂ := localNormSubgroup K L) ?_ himageOpen
  intro x hx
  rw [hintersection] at hx
  exact hx.1

/-- The norm subgroup of a finite Galois extension of a nonarchimedean local
field is open in the native topology of the base-field unit group. -/
theorem localNormSubgroup_isOpen
    (K L : Type) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] :
    IsOpen (localNormSubgroup K L : Set Kˣ) := by
  let : UniformSpace K := IsTopologicalAddGroup.rightUniformSpace K
  let : IsUniformAddGroup K := isUniformAddGroup_of_addCommGroup
  let : (Valued.v : Valuation K
      (ValuativeRel.ValueGroupWithZero K)).RankOne :=
    { hom' := ValuativeRel.IsRankLeOne.nonempty.some.emb (R := K) |>.comp
        MonoidWithZeroHom.ValueGroup₀.embedding
      strictMono' := ValuativeRel.IsRankLeOne.nonempty.some.strictMono.comp
        MonoidWithZeroHom.ValueGroup₀.embedding_strictMono }
  let : NontriviallyNormedField K :=
    Valued.toNontriviallyNormedField
      (L := K) (Γ₀ := ValuativeRel.ValueGroupWithZero K)

  let : NontriviallyNormedField L :=
    spectralNorm.nontriviallyNormedField K L
  let : NormedAlgebra K L := spectralNorm.normedAlgebra K L
  let : CompleteSpace L := spectralNorm.completeSpace K L
  let : LocallyCompactSpace L :=
    LocallyCompactSpace.of_finiteDimensional_of_complete K L
  let : IsUltrametricDist L :=
    ⟨fun x y z => by
      change ‖x - z‖ ≤ max ‖x - y‖ ‖y - z‖
      rw [← sub_add_sub_cancel x y z]
      exact isNonarchimedean_spectralNorm
        (K := K) (L := L) (x - y) (y - z)⟩
  let : Valued L ℝ≥0 := NormedField.toValued
  let vL : Valuation L ℝ≥0 := Valued.v
  let : vL.IsNontrivial :=
    (inferInstance : (NormedField.valuation (K := L)).IsNontrivial)
  let : ValuativeRel L := ValuativeRel.ofValuation vL
  let : vL.Compatible := Valuation.Compatible.ofValuation vL
  let : ValuativeRel.IsNontrivial L :=
    (ValuativeRel.isNontrivial_iff_isNontrivial vL).2 inferInstance
  let : IsValuativeTopology L :=
    isValuativeTopology_of_valued_ofValuation L ℝ≥0
  let : IsNonarchimedeanLocalField L :=
    { toIsValuativeTopology := inferInstance
      toLocallyCompactSpace := inferInstance
      toIsNontrivial := inferInstance }

  let : (ValuativeRel.valuation K).HasExtension
      (ValuativeRel.valuation L) := by
    apply Valuation.HasExtension.ofComapInteger
    ext x
    change ValuativeRel.valuation L (algebraMap K L x) ≤ 1 ↔
      ValuativeRel.valuation K x ≤ 1
    rw [← (ValuativeRel.valuation L).vle_one_iff, vL.vle_one_iff]
    change spectralNorm K L (algebraMap K L x) ≤ 1 ↔
      ValuativeRel.valuation K x ≤ 1
    rw [spectralNorm_extends]
    exact Valued.toNormedField.norm_le_one_iff

  let : Algebra.IsIntegral 𝒪[K] 𝒪[L] := ⟨by
    intro y
    apply IsIntegral.tower_bot
      (R := 𝒪[K]) (A := 𝒪[L]) (B := L)
      (Subring.subtype_injective (ValuativeRel.valuation L).integer)
    have hyv : vL (y : L) ≤ 1 := by
      apply (vL.vle_one_iff).1
      apply ((ValuativeRel.valuation L).vle_one_iff).2
      exact y.property
    have hynorm : ‖(y : L)‖ ≤ 1 := by
      have hynormNN : ‖(y : L)‖₊ ≤ 1 := by
        simpa [vL, NormedField.valuation_apply] using hyv
      exact_mod_cast hynormNN
    change spectralNorm K L (y : L) ≤ 1 at hynorm
    have hcoeffNorm :
        ∀ n : ℕ, ‖(minpoly K (y : L)).coeff n‖ ≤ 1 :=
      (spectralValue_le_one_iff
        (minpoly.monic (Algebra.IsIntegral.isIntegral (y : L)))).1
        (by simpa [spectralNorm] using hynorm)
    have hcoeff :
        (↑(minpoly K (y : L)).coeffs : Set K) ⊆
          (ValuativeRel.valuation K).integer := by
      intro c hc
      obtain ⟨n, _hn, rfl⟩ := Polynomial.mem_coeffs_iff.mp hc
      exact ((ValuativeRel.valuation K).mem_integer_iff _).2
        (Valued.toNormedField.norm_le_one_iff.mp (hcoeffNorm n))
    let p : Polynomial 𝒪[K] :=
      (minpoly K (y : L)).toSubring
        (ValuativeRel.valuation K).integer hcoeff
    refine ⟨p, ?_, ?_⟩
    · exact (Polynomial.monic_toSubring
        (minpoly K (y : L)) (ValuativeRel.valuation K).integer hcoeff).2
          (minpoly.monic (Algebra.IsIntegral.isIntegral (y : L)))
    · have hmaproot :
          Polynomial.aeval (y : L)
            (p.map (algebraMap 𝒪[K] K)) = 0 := by
        dsimp only [p]
        rw [show algebraMap 𝒪[K] K =
          (ValuativeRel.valuation K).integer.subtype from rfl,
          Polynomial.map_toSubring]
        exact minpoly.aeval K (y : L)
      rwa [Polynomial.aeval_map_algebraMap K (y : L) p] at hmaproot⟩

  let : Algebra.IsIntegral
      (ValuativeRel.valuation K).valuationSubring
      (ValuativeRel.valuation L).valuationSubring := by
    change Algebra.IsIntegral 𝒪[K] 𝒪[L]
    infer_instance
  let hIntegralClosure : IsIntegralClosure
      (ValuativeRel.valuation L).valuationSubring
      (ValuativeRel.valuation K).valuationSubring L :=
    ValuationTheory.DiscreteValuationField.Valuation.valuationSubring_isIntegralClosure_of_isIntegral
      (ValuativeRel.valuation K) (ValuativeRel.valuation L)
  let : IsIntegralClosure 𝒪[L] 𝒪[K] L := by
    change IsIntegralClosure
      (ValuativeRel.valuation L).valuationSubring
      (ValuativeRel.valuation K).valuationSubring L
    exact hIntegralClosure

  exact localNormSubgroup_isOpen_of_compatibleLocalField K L

end NormSubgroupTopology

end LocalClassFieldTheory
end
end

section
-- module Solutions.OAIQ244_DUKE.AlgebraicNumberTheory_Idele_NormApproximation_FinitePlaces
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.infinitePlaceComplexificationOverfield_algebra _root_.GlobalClassFieldTheory.Reciprocity.infinitePlaceComplexificationOverfield_baseAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalCyclotomicCompletionAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalCyclotomicLocalizedCompletionFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalCyclotomicLocalizedCompletionIsAlgebraic _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalClassFieldTheory.finiteGaloisLocalField_integerRing_moduleFinite _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.residueFieldZModAlgebra _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedIntegralAlgebraContextValuationSubringAlgebra _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedIntegralAlgebraContextValuationSubringTower _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedIntegralLatticeContextModuleFinite _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedIntegralLatticeContextModuleFree _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedQPadicContextValuationSubringTower _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.diagonalLogAction _root_.OAI.PrimeDegreePackets.gLocallyCompact _root_.OAI.PrimeDegreePackets.instIsTopologicalRingLocalAlgebra _root_.OAI.PrimeDegreePackets.instLocallyCompactSpaceLocalAlgebra _root_.OAI.PrimeDegreePackets.instTopologicalSpaceLocalAlgebra _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.OAI.PrimeDegreePackets.xLocallyCompact _root_.LocalClassFieldTheory.comparisonIntegerRingIsIntegralClosure _root_.LocalClassFieldTheory.normalizationIntegerRingIsIntegralClosure _root_.chosenFinitePlaceBaseLocallyCompactSpace _root_.chosenFinitePlaceBaseValuationIsNontrivial _root_.chosenFinitePlaceCompletionAlgebra _root_.chosenFinitePlaceCompletionContinuousSMul _root_.chosenFinitePlaceCompletionFiniteDimensional _root_.chosenFinitePlaceCompletionLocallyCompactSpace _root_.chosenFinitePlaceExtensionCompletionAlgebra _root_.chosenFinitePlaceExtensionCompletionSMul _root_.chosenFinitePlaceLocalizedFiniteDimensional _root_.chosenFinitePlaceLocalizedIntegerAlgebra _root_.chosenFinitePlaceLocalizedIntegerModuleFinite _root_.chosenFinitePlaceLocalizedIsGalois _root_.chosenFinitePlaceLocalizedIsIntegralClosure _root_.chosenFinitePlaceLocalizedIsNonarchimedeanLocalField _root_.chosenFinitePlaceLocalizedIsUltrametricDist _root_.chosenFinitePlaceLocalizedIsValuativeTopology _root_.chosenFinitePlaceLocalizedLocallyCompactSpace _root_.chosenFinitePlaceLocalizedValuationCompatible _root_.chosenFinitePlaceLocalizedValuationHasExtension _root_.chosenFinitePlaceLocalizedValuationIsNontrivial _root_.chosenFinitePlaceLocalizedValuativeRel _root_.chosenFinitePlaceLocalizedValuativeRelIsNontrivial _root_.chosenFinitePlaceLocalizedValued _root_.scaledRelativeIntegerLatticeQuotientFinite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

/-!
# Weak approximation for actual local norm quotients

For a finite Galois extension `L / K` and a finite set `S` of finite
places of `K`, this file chooses an actual extension of every `v ∈ S`,
forms the corresponding algebraic localization `L_w / K_v`, and
transports its local norm subgroup to mathlib's concrete adic
completion.  These transported norm subgroups are open.  Multiplicative
weak approximation therefore gives a surjection

`Kˣ → ∏ v ∈ S, K_vˣ / N(L_wˣ)`.

All choices are made from the extension theorem for absolute values;
none of the local conclusions is included as input data.
-/

open scoped NumberField Classical NNReal
open NumberField IsDedekindDomain

noncomputable section

open LocalClassFieldTheory


open AlgebraicNumberTheory.Valuations
open LocalClassFieldTheory
open LocalFieldTheory

variable {K L : Type}
    [Field K] [NumberField K]
    [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]

/-- The local norm subgroup transported to the actual finite idele
coordinate is open. -/
theorem chosenFinitePlaceLocalNormSubgroup_isOpen
    (v : HeightOneSpectrum (𝓞 K)) :
    IsOpen
      (chosenFinitePlaceLocalNormSubgroup
        (K := K) (L := L) v :
        Set (v.adicCompletion K)ˣ) := by
  let vK :=
    NumberField.HeightOneSpectrum.adicAbv K v
  let w := chosenFinitePlaceExtension (L := L) v
  let hvK : vK.IsNontrivial :=
    RayClass.adicAbv_isNontrivial v
  let hK :=
    AbsoluteValue.extensionCompletionAlgebra
      (K := K) w.1
  let : SMul K w.1.Completion := hK.toSMul
  let : Algebra vK.Completion w.1.Completion :=
    AbsoluteValue.completionAlgebra vK w.1 w.2
  let := localizedCompletionGlobalAlgebra vK w
  let := localizedCompletionIsScalarTower vK w
  let E := LocalizedCompletion vK w
  let : FiniteDimensional vK.Completion E :=
    localizedCompletionModuleFinite vK hvK w
  let : IsGalois vK.Completion E :=
    HilbertRamification.algebraicLocalization_isGalois vK w
  let : NontriviallyNormedField vK.Completion :=
    absoluteValueExtension_completionNontriviallyNormedField
      vK hvK
  let : LocallyCompactSpace vK.Completion :=
    AbsoluteValue.Completion.locallyCompactSpace
      (finitePlaceCompletionBaseMap_isometry v)
  let : IsUltrametricDist vK.Completion :=
    IsUltrametricDist.isUltrametricDist_of_isNonarchimedean_norm
      (AbsoluteValue.completionAbsoluteValue_isNonarchimedean
        vK
        (NumberField.HeightOneSpectrum.isNonarchimedean_adicAbv
          K v))
  let : Valued vK.Completion ℝ≥0 :=
    NormedField.toValued
  let vC : Valuation vK.Completion ℝ≥0 := Valued.v
  let : vC.IsNontrivial :=
    (inferInstance :
      (NormedField.valuation
        (K := vK.Completion)).IsNontrivial)
  let : ValuativeRel vK.Completion :=
    ValuativeRel.ofValuation vC
  let : vC.Compatible :=
    Valuation.Compatible.ofValuation vC
  let : ValuativeRel.IsNontrivial vK.Completion :=
    (ValuativeRel.isNontrivial_iff_isNontrivial vC).2
      inferInstance
  let : IsValuativeTopology vK.Completion :=
    isValuativeTopology_of_valued_ofValuation
      vK.Completion ℝ≥0
  let : IsNonarchimedeanLocalField vK.Completion :=
    { toIsValuativeTopology := inferInstance
      toLocallyCompactSpace := inferInstance
      toIsNontrivial := inferInstance }
  let e :
      vK.Completionˣ ≃ₜ* (v.adicCompletion K)ˣ :=
    finitePlaceCompletionUnitsContinuousMulEquiv v
  have hN :
      IsOpen
        (localNormSubgroup vK.Completion E :
          Set vK.Completionˣ) :=
    LocalClassFieldTheory.localNormSubgroup_isOpen
      vK.Completion E
  change IsOpen
    (e '' (localNormSubgroup vK.Completion E :
      Set vK.Completionˣ))
  exact e.isOpenMap _ hN
end
end

section
-- module Solutions.OAIQ244_DUKE.AlgebraicNumberTheory_Idele_Cohomology_SPlaces_OutsideIntegralInduced_ChosenPlaceAction
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.infinitePlaceComplexificationOverfield_algebra _root_.GlobalClassFieldTheory.Reciprocity.infinitePlaceComplexificationOverfield_baseAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalCyclotomicCompletionAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalCyclotomicLocalizedCompletionFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalCyclotomicLocalizedCompletionIsAlgebraic _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.DiscreteNthRootsSubgroup.instTopologicalSpaceSubtypeUnitsMemSubgroup _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.KummerTheory.primeCyclotomicBaseFiniteDimensional _root_.KummerTheory.primeCyclotomicBaseIsGalois _root_.LocalClassFieldTheory.finiteGaloisLocalField_integerRing_moduleFinite _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.residueFieldZModAlgebra _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedIntegralAlgebraContextValuationSubringAlgebra _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedIntegralAlgebraContextValuationSubringTower _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedIntegralLatticeContextModuleFinite _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedIntegralLatticeContextModuleFree _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedQPadicContextValuationSubringTower _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.diagonalLogAction _root_.OAI.PrimeDegreePackets.instIsTopologicalRingLocalAlgebra _root_.OAI.PrimeDegreePackets.instTopologicalSpaceLocalAlgebra _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.CyclicCohomology.binaryCoefficientFamilyCommGroup _root_.LocalClassFieldTheory.comparisonIntegerRingIsIntegralClosure _root_.LocalClassFieldTheory.normalizationIntegerRingIsIntegralClosure _root_.cyclicPrimeDegreeIntermediate_isGalois _root_.cyclicPrimeSubextension_isGalois _root_.finiteNormalClosure_isGalois _root_.relativeUnrestrictedSPlaceFactorCommGroup
attribute [-simp] _root_.GlobalClassFieldTheory.Reciprocity.rationalCyclotomicGlobalToLocalizedAlgHom_apply _root_.GlobalClassFieldTheory.Reciprocity.rationalCyclotomicGlobalToLocalizedAlgHom_primitiveRoot _root_.IsDiscreteValuationRing.addVal_ringEquiv _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.OAI.PrimeDegreePackets.ThetaConstruction.schwartzCM_apply _root_.RayClass.primesEquiv_val_eq_natGenerator _root_.chosenFinitePlaceIntegerToLocalizedCompletion_coe _root_.chosenFinitePlaceLocalizedResidueEquiv_apply_mk _root_.doubleCosetExtension_mk _root_.extendAbsoluteValueExtensionFromIntermediate_apply _root_.finitePlaceCompletionRingEquiv_toCompletion _root_.finitePlaceExtensionAdicCompletionRingEquiv_toCompletion _root_.finitePlaceExtensionCompletionRingEquiv_toCompletion _root_.finitePlaceIdealResidueEquivCompletion_apply_mk _root_.finitePlaceIntegerToCompletion_coe _root_.finitePlaceTensorRingEquivAboveAdic_apply_extension _root_.finitePlaceTensorUnitsEquivAboveAdic_apply_extension _root_.infinitePlaceAboveEquivExtension_apply_val _root_.infinitePlaceTensorRingEquivAbove_apply _root_.infinitePlaceTensorUnitsEquivAbove_apply _root_.infinitePlace_mult_smul _root_.mem_finitePlaceDecompositionGroup_iff _root_.restrictAbsoluteValueExtensionToIntermediate_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

/-!
# The action at a chosen finite place

This file exposes the decomposition-group action and the direct local
cohomology endpoint used by the integral induced-block construction. Keeping
this localization boundary in a lower leaf prevents downstream transport
proofs from elaborating it together with the tensor-block API.
-/

open scoped NumberField ValuativeRel NNReal
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
/-- The actual completion selected over a finite place has trivial low-degree
Herbrand cohomology on its integer units whenever that local extension is
unramified. All valued-local-field and integer-ring structures here are the
canonical instances exported by `ChosenLocalization`. -/
theorem chosenFinitePlaceLocalizedIntegerUnits_unramifiedHerbrand_subsingleton
    (w₀ : HeightOneSpectrum (𝓞 K))
    (g : Gal(
      ChosenFinitePlaceLocalizedCompletion (K := K) (L := L) w₀ /
      ChosenFinitePlaceBaseCompletion (K := K) w₀))
    (hg : ∀ τ : Gal(
      ChosenFinitePlaceLocalizedCompletion (K := K) (L := L) w₀ /
      ChosenFinitePlaceBaseCompletion (K := K) w₀),
      τ ∈ Subgroup.zpowers g)
    (hunram : ChosenFinitePlaceIsUnramified
      (K := K) (L := L) w₀) :
    letI : MulDistribMulAction
        (Gal(
          ChosenFinitePlaceLocalizedCompletion (K := K) (L := L) w₀ /
          ChosenFinitePlaceBaseCompletion (K := K) w₀))
        𝒪[ChosenFinitePlaceLocalizedCompletion (K := K) (L := L) w₀]ˣ :=
      galoisGroupIntegerUnitsMulDistribMulActionOfIsIntegralClosure
        (ChosenFinitePlaceBaseCompletion (K := K) w₀)
        (ChosenFinitePlaceLocalizedCompletion (K := K) (L := L) w₀)
    Subsingleton
        (HerbrandH0
          (Gal(
            ChosenFinitePlaceLocalizedCompletion (K := K) (L := L) w₀ /
            ChosenFinitePlaceBaseCompletion (K := K) w₀))
          𝒪[ChosenFinitePlaceLocalizedCompletion (K := K) (L := L) w₀]ˣ) ∧
      Subsingleton
        (HerbrandHMinusOne
          (Gal(
            ChosenFinitePlaceLocalizedCompletion (K := K) (L := L) w₀ /
            ChosenFinitePlaceBaseCompletion (K := K) w₀))
          𝒪[ChosenFinitePlaceLocalizedCompletion (K := K) (L := L) w₀]ˣ g) := by
  let vK := HeightOneSpectrum.adicAbv K w₀
  let E := ChosenFinitePlaceLocalizedCompletion
    (K := K) (L := L) w₀
  let :
      IsNonarchimedeanLocalField.IsUnramifiedValuedExtension
        vK.Completion E := by
    simpa [ChosenFinitePlaceIsUnramified] using hunram
  exact
    unramifiedLocalIntegerUnitsHerbrand_subsingleton
      vK.Completion E g hg

end ChosenFinitePlace
end
end

section
-- module Solutions.OAIQ244_DUKE.AlgebraicNumberTheory_Idele_Cohomology_SPlaces_OutsideIntegralInduced_ChosenPlace
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.infinitePlaceComplexificationOverfield_algebra _root_.GlobalClassFieldTheory.Reciprocity.infinitePlaceComplexificationOverfield_baseAlgebra _root_.GlobalClassFieldTheory.Reciprocity.infinitePlaceComplexificationOverfield_baseSmul _root_.GlobalClassFieldTheory.Reciprocity.infinitePlaceComplexificationOverfield_smul _root_.GlobalClassFieldTheory.Reciprocity.rationalCyclotomicCompletionAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalCyclotomicLocalizedCompletionFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalCyclotomicLocalizedCompletionIsAlgebraic _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.KummerTheory.primeCyclotomicBaseFiniteDimensional _root_.LocalClassFieldTheory.finiteGaloisLocalField_integerRing_moduleFinite _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.residueFieldZModAlgebra _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedIntegralAlgebraContextValuationSubringAlgebra _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedIntegralAlgebraContextValuationSubringTower _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedIntegralLatticeContextModuleFinite _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedIntegralLatticeContextModuleFree _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedQPadicContextValuationSubringTower _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.LubinTate.compatibleGroupFamiliesGroup _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.diagonalLogAction _root_.OAI.PrimeDegreePackets.instIsTopologicalRingLocalAlgebra _root_.OAI.PrimeDegreePackets.instTopologicalSpaceLocalAlgebra _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.CyclicCohomology.binaryCoefficientFamilyCommGroup _root_.LocalClassFieldTheory.comparisonIntegerRingIsIntegralClosure _root_.LocalClassFieldTheory.normalizationIntegerRingIsIntegralClosure _root_.relativeUnrestrictedSPlaceFactorCommGroup
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
theorem
    chosenFinitePlaceDecompositionGroupIntegerUnits_unramifiedHerbrand_subsingleton
    (w₀ : HeightOneSpectrum (𝓞 K))
    (σ : L ≃ₐ[K] L)
    (hσ : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ)
    (hunram : ChosenFinitePlaceIsUnramified
      (K := K) (L := L) w₀) :
    let E := ChosenFinitePlaceLocalizedCompletion
      (K := K) (L := L) w₀
    let H := absoluteValueDecompositionGroup K
      (chosenFinitePlaceExtension (L := L) w₀).1
    letI : Fintype H :=
      chosenFinitePlaceDecompositionGroupFintypeProvider
        (K := K) (L := L) w₀
    letI : MulDistribMulAction H 𝒪[E]ˣ :=
      chosenFinitePlaceDecompositionGroupIntegerUnitsAction
        (K := K) (L := L) w₀
    Subsingleton (HerbrandH0 H 𝒪[E]ˣ) ∧
      Subsingleton
        (HerbrandHMinusOne H 𝒪[E]ˣ
          (subgroupGeneratorOfGenerator H σ hσ)) := by
  let vK := HeightOneSpectrum.adicAbv K w₀
  let w := chosenFinitePlaceExtension (L := L) w₀
  let E := ChosenFinitePlaceLocalizedCompletion
    (K := K) (L := L) w₀
  let H := absoluteValueDecompositionGroup K w.1
  let eLocal :=
    chosenFinitePlaceDecompositionGroupEquivProvider
      (K := K) (L := L) w₀
  let : MulDistribMulAction
      (Gal(E / vK.Completion)) 𝒪[E]ˣ :=
    chosenFinitePlaceLocalizedIntegerUnitsGaloisActionProvider
      (K := K) (L := L) w₀
  let : Fintype H :=
    chosenFinitePlaceDecompositionGroupFintypeProvider
      (K := K) (L := L) w₀
  let : MulDistribMulAction H 𝒪[E]ˣ :=
    chosenFinitePlaceDecompositionGroupIntegerUnitsAction
      (K := K) (L := L) w₀
  let δ := subgroupGeneratorOfGenerator H σ hσ
  have hlocal :=
    apply_of_zpowers_generator_map eLocal δ
      (subgroupGeneratorOfGenerator_generates H σ hσ)
      (fun g hg ↦
        chosenFinitePlaceLocalizedIntegerUnits_unramifiedHerbrand_subsingleton
          (K := K) (L := L) w₀ g hg hunram)
  have hsmul :
      ∀ (h : H) (x : 𝒪[E]ˣ),
        (MulEquiv.refl 𝒪[E]ˣ)
            ((chosenFinitePlaceDecompositionGroupIntegerUnitsAction
              (K := K) (L := L) w₀).smul h x) =
          (MulDistribMulAction.compHom
            𝒪[E]ˣ eLocal.toMonoidHom).smul h
              ((MulEquiv.refl 𝒪[E]ˣ) x) := by
    intro h x
    exact
      chosenFinitePlaceDecompositionGroupIntegerUnitsAction_smul_eq_pullback
        (K := K) (L := L) w₀ h x
  let eActionH0 :=
    @herbrandH0EquivariantMulEquiv
      H 𝒪[E]ˣ 𝒪[E]ˣ _ _ _ _
      (chosenFinitePlaceDecompositionGroupIntegerUnitsAction
        (K := K) (L := L) w₀)
      (MulDistribMulAction.compHom 𝒪[E]ˣ eLocal.toMonoidHom)
      (MulEquiv.refl 𝒪[E]ˣ) hsmul
  let eActionHMinusOne :=
    @herbrandHMinusOneEquivariantMulEquiv
      H 𝒪[E]ˣ 𝒪[E]ˣ _ _ _ _
      (chosenFinitePlaceDecompositionGroupIntegerUnitsAction
        (K := K) (L := L) w₀)
      (MulDistribMulAction.compHom 𝒪[E]ˣ eLocal.toMonoidHom)
      (MulEquiv.refl 𝒪[E]ˣ) hsmul δ
  let eGroupH0 := herbrandH0CompMulEquiv (A := 𝒪[E]ˣ) eLocal
  let eGroupHMinusOne :=
    herbrandHMinusOneCompMulEquiv (A := 𝒪[E]ˣ) eLocal δ
  exact
    ⟨subsingleton_of_equiv_of_equiv
        (underlyingEquivOfMulEquiv eActionH0)
        (underlyingEquivOfMulEquiv eGroupH0) hlocal.1,
      subsingleton_of_equiv_of_equiv
        (underlyingEquivOfMulEquiv eActionHMinusOne)
        (underlyingEquivOfMulEquiv eGroupHMinusOne) hlocal.2⟩

end ChosenFinitePlace
end
end

section
-- module Solutions.OAIQ244_DUKE.AlgebraicNumberTheory_Idele_SufficientlyLarge
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 400000
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.GlobalClassFields.ConductorialSubgroup.finiteIndex _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalClassFieldTheory.finiteGaloisLocalField_integerRing_moduleFinite _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.residueFieldZModAlgebra _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedIntegralAlgebraContextValuationSubringAlgebra _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.LocalClassFieldTheory.comparisonIntegerRingIsIntegralClosure _root_.LocalClassFieldTheory.normalizationIntegerRingIsIntegralClosure _root_.chosenFinitePlaceCompletionAlgebra
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

/-- A finite set outside which the chosen representative of `c` is
integral. -/
def classRepresentativeSupport (c : ClassGroup (𝓞 K)) :
    Finset (HeightOneSpectrum (𝓞 K)) :=
  Classical.choose
    (exists_finset_supportedAt
      (classRepresentative (K := K) c))

/-- The union of the supports of one representative of every ordinary
ideal class.  It is finite because the ideal class group is finite. -/
def sufficientlyLargeFiniteSet :
    Finset (HeightOneSpectrum (𝓞 K)) := by
  classical
  exact Finset.univ.biUnion (classRepresentativeSupport (K := K))

end IdeleGroup
end
end

section
-- module Solutions.OAIQ244_DUKE.AlgebraicNumberTheory_Idele_Cohomology_SupportedBridge
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.GlobalClassFields.ConductorialSubgroup.finiteIndex _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.KummerTheory.finite_sUnit_nthPowerQuotient _root_.LocalClassFieldTheory.finiteGaloisLocalField_integerRing_moduleFinite _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.residueFieldZModAlgebra _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedIntegralAlgebraContextValuationSubringAlgebra _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.LubinTate.compatibleGroupFamiliesGroup _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.LocalClassFieldTheory.comparisonIntegerRingIsIntegralClosure _root_.LocalClassFieldTheory.normalizationIntegerRingIsIntegralClosure _root_.chosenFinitePlaceCompletionAlgebra
attribute [-simp] _root_.GlobalClassFieldTheory.ClassFieldAxiom.actualPushoutNormQuotientMap_mk _root_.GlobalClassFieldTheory.ClassFieldAxiom.sUnitEquivSupportedPrincipalIdeleSubgroup_coe _root_.IdeleGroup.finitePlaceIdele_finiteComponent_of_ne _root_.IdeleGroup.finitePlaceIdele_finiteComponent_same _root_.IdeleGroup.finitePlaceIdele_infiniteComponent _root_.IdeleGroup.infinitePlaceIdeleContinuous_apply _root_.IdeleGroup.infinitePlaceIdele_finiteComponent _root_.IdeleGroup.infinitePlaceIdele_infiniteComponent_of_ne _root_.IdeleGroup.infinitePlaceIdele_infiniteComponent_same _root_.IsDiscreteValuationRing.addVal_ringEquiv _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.KummerTheory.mem_sUnitFiniteKummerRadical_iff _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.OAI.PrimeDegreePackets.ThetaConstruction.schwartzCM_apply _root_.RayClass.primesEquiv_val_eq_natGenerator _root_.RayClass.signToNarrow_mk _root_.RelativeIdeleGroup.relativeFinitePlaceIdele_finiteComponent_of_ne _root_.RelativeIdeleGroup.relativeFinitePlaceIdele_finiteComponent_same _root_.RelativeIdeleGroup.relativeFinitePlaceIdele_infiniteComponent _root_.RelativeIdeleGroup.relativeInfinitePlaceIdele_finiteComponent _root_.RelativeIdeleGroup.relativeInfinitePlaceIdele_infiniteComponent_of_ne _root_.RelativeIdeleGroup.relativeInfinitePlaceIdele_infiniteComponent_same
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

omit [FiniteDimensional K L] [IsGalois K L] in
@[simp]
theorem mem_finitePlacesAbove_iff
    (S : Finset (HeightOneSpectrum (𝓞 K)))
    (W : HeightOneSpectrum (𝓞 L)) :
    W ∈ finitePlacesAbove (K := K) (L := L) S ↔
      finitePlaceBelow (K := K) W ∈ S := by
  simp [finitePlacesAbove]

omit [FiniteDimensional K L] [IsGalois K L] in
/-- Galois conjugation does not change the place lying below a finite
place of the extension field. -/
@[simp]
theorem finitePlaceBelow_finitePlaceEquiv
    (σ : L ≃ₐ[K] L)
    (W : HeightOneSpectrum (𝓞 L)) :
    finitePlaceBelow (K := K) (finitePlaceEquiv K L σ W) =
      finitePlaceBelow (K := K) W := by
  apply HeightOneSpectrum.ext
  rw [finitePlaceBelow_asIdeal, finitePlaceBelow_asIdeal,
    finitePlaceEquiv_asIdeal]
  ext x
  rw [Ideal.mem_under, Ideal.mem_under]
  have hfix :
      NumberField.RingOfIntegers.mapAlgEquiv σ
          (algebraMap (𝓞 K) (𝓞 L) x) =
        algebraMap (𝓞 K) (𝓞 L) x := by
    apply NumberField.RingOfIntegers.ext
    exact σ.commutes (x : K)
  conv_lhs => rw [← hfix]
  exact
    (Ideal.apply_mem_of_equiv_iff
      (I := W.asIdeal)
      (f :=
        (NumberField.RingOfIntegers.mapAlgEquiv σ).toRingEquiv)
      (x := algebraMap (𝓞 K) (𝓞 L) x))

omit [FiniteDimensional K L] [IsGalois K L] in
/-- The full set of extension places above a base support is stable
under the concrete Galois action. -/
theorem finitePlacesAbove_isGaloisStable
    (S : Finset (HeightOneSpectrum (𝓞 K))) :
    IsGaloisStableFinitePlaces K L
      (finitePlacesAbove (K := K) (L := L) S) := by
  intro σ W
  simp only [mem_finitePlacesAbove_iff]
  change
    finitePlaceBelow (K := K) W ∈ S ↔
      finitePlaceBelow (K := K)
        (finitePlaceEquiv K L σ W) ∈ S
  rw [finitePlaceBelow_finitePlaceEquiv]

omit [IsGalois K L] in
/-- Scalar extension carries the concrete supported
relative ideles exactly to the ordinary ideles supported at all places
above the same base support. -/
theorem relativeIdeleBaseChange_mem_supportedAt_iff
    (S : Finset (HeightOneSpectrum (𝓞 K)))
    (z : RelativeIdeleGroup K L) :
    z ∈ relativeIdeleLocalTensorDecompositionSupportedSubgroup
          (K := K) (L := L) S ↔
      relativeIdeleBaseChangeMulEquiv
          (K := K) (L := L) z ∈
        IdeleGroup.supportedAt (K := L)
          (finitePlacesAbove (K := K) (L := L) S : Set _) := by
  rw [mem_relativeIdeleLocalTensorDecompositionSupportedSubgroup_iff,
    IdeleGroup.mem_supportedAt_iff]
  constructor
  · intro hz W hW
    have hbelow :
        finitePlaceBelow (K := K) W ∉ S := by
      intro hmem
      exact hW ((mem_finitePlacesAbove_iff
        (K := K) (L := L) S W).2 hmem)
    have hlocal :=
      (relativeLocalTensorDecompositionIntegralUnitAt_iff_aboveAdic
        (K := K) (L := L)
        (finitePlaceBelow (K := K) W)
        (RelativeIdeleGroup.finiteComponent
          (K := K) (L := L)
          (finitePlaceBelow (K := K) W) z)).1
        (hz (finitePlaceBelow (K := K) W) hbelow) ⟨W, rfl⟩
    rw [relativeIdeleBaseChangeMulEquiv_finite,
      relativeFiniteIdeleToFiniteIdele_apply,
      relativeFiniteTensorPiMulEquiv_apply]
    exact hlocal
  · intro hz w hw
    apply
      (relativeLocalTensorDecompositionIntegralUnitAt_iff_aboveAdic
        (K := K) (L := L) w
        (RelativeIdeleGroup.finiteComponent
          (K := K) (L := L) w z)).2
    intro W
    rcases W with ⟨W, hWbelow⟩
    subst w
    have hW :
        W ∉ (finitePlacesAbove (K := K) (L := L) S :
          Set (HeightOneSpectrum (𝓞 L))) := by
      intro hmem
      exact hw ((mem_finitePlacesAbove_iff
        (K := K) (L := L) S W).1 hmem)
    have hlocal := hz W hW
    rw [relativeIdeleBaseChangeMulEquiv_finite,
      relativeFiniteIdeleToFiniteIdele_apply,
      relativeFiniteTensorPiMulEquiv_apply] at hlocal
    exact hlocal

/-- The diagonal map from extension-field `S`-units into the
intersection of the relative principal and supported subgroups. -/
noncomputable def sUnitToRelativePrincipalSupportedIntersection
    (S : Finset (HeightOneSpectrum (𝓞 K))) :
    SUnitGroup (K := L)
        (finitePlacesAbove (K := K) (L := L) S) →*
      (RelativeIdeleGroup.principalSubgroup K L).subgroupOf
        (relativeIdeleLocalTensorDecompositionSupportedSubgroup
          (K := K) (L := L) S) where
  toFun x := by
    have hOrdinary :
        IdeleGroup.principalIdele L (x : Lˣ) ∈
          IdeleGroup.supportedAt (K := L)
            (finitePlacesAbove (K := K) (L := L) S : Set _) :=
      (principalIdele_mem_supportedAt_iff_sUnit
        (L := L)
        (finitePlacesAbove (K := K) (L := L) S)
        (x : Lˣ)).2 x.property
    have hRelative :
        RelativeIdeleGroup.principalIdele K L (x : Lˣ) ∈
          relativeIdeleLocalTensorDecompositionSupportedSubgroup
            (K := K) (L := L) S := by
      apply
        (relativeIdeleBaseChange_mem_supportedAt_iff
          (K := K) (L := L) S _).2
      simpa using hOrdinary
    exact
      ⟨⟨RelativeIdeleGroup.principalIdele K L (x : Lˣ),
          hRelative⟩,
        ⟨(x : Lˣ), rfl⟩⟩
  map_one' := by
    apply Subtype.ext
    apply Subtype.ext
    simp
  map_mul' x y := by
    apply Subtype.ext
    apply Subtype.ext
    simp

/-- The intersection of the relative principal ideles with the
relative `S`-idele subgroup is precisely the ordinary group of
`S`-units of `L`. -/
noncomputable def sUnitEquivRelativePrincipalSupportedIntersection
    (S : Finset (HeightOneSpectrum (𝓞 K))) :
    SUnitGroup (K := L)
        (finitePlacesAbove (K := K) (L := L) S) ≃*
      (RelativeIdeleGroup.principalSubgroup K L).subgroupOf
        (relativeIdeleLocalTensorDecompositionSupportedSubgroup
          (K := K) (L := L) S) :=
  MulEquiv.ofBijective
    (sUnitToRelativePrincipalSupportedIntersection
      (K := K) (L := L) S)
    ⟨by
      intro x y hxy
      apply Subtype.ext
      apply IdeleGroup.principalIdele_injective L
      have hRelative :=
        congrArg
          (fun z :
            (RelativeIdeleGroup.principalSubgroup K L).subgroupOf
              (relativeIdeleLocalTensorDecompositionSupportedSubgroup
                (K := K) (L := L) S) =>
            ((z :
                relativeIdeleLocalTensorDecompositionSupportedSubgroup
                  (K := K) (L := L) S) :
              RelativeIdeleGroup K L))
          hxy
      change
        RelativeIdeleGroup.principalIdele K L (x : Lˣ) =
          RelativeIdeleGroup.principalIdele K L (y : Lˣ)
        at hRelative
      have hOrdinary :=
        congrArg
          (relativeIdeleBaseChangeMulEquiv
            (K := K) (L := L))
          hRelative
      simpa using hOrdinary,
    by
      intro y
      obtain ⟨x, hx⟩ := y.property
      have hRelative :
          RelativeIdeleGroup.principalIdele K L x ∈
            relativeIdeleLocalTensorDecompositionSupportedSubgroup
              (K := K) (L := L) S := by
        rw [hx]
        exact y.1.property
      have hOrdinary :=
        (relativeIdeleBaseChange_mem_supportedAt_iff
          (K := K) (L := L) S
          (RelativeIdeleGroup.principalIdele K L x)).1 hRelative
      have hxS :
          x ∈ SUnitGroup (K := L)
            (finitePlacesAbove (K := K) (L := L) S) := by
        apply
          (principalIdele_mem_supportedAt_iff_sUnit
            (L := L)
            (finitePlacesAbove (K := K) (L := L) S) x).1
        simpa using hOrdinary
      refine ⟨⟨x, hxS⟩, ?_⟩
      apply Subtype.ext
      apply Subtype.ext
      exact hx⟩

/-- The idele-class Herbrand support: contractions of a sufficiently large support
for `I_L`, together with every ramified base finite place. -/
noncomputable def ideleClassHerbrandSupport :
    Finset (HeightOneSpectrum (𝓞 K)) := by
  classical
  exact
    (IdeleGroup.sufficientlyLargeFiniteSet (K := L)).image
        (finitePlaceBelow (K := K)) ∪
      ramifiedBaseFinitePlaces (K := K) (L := L)
end
end

section
-- module Solutions.OAIQ244_DUKE.AlgebraicNumberTheory_Idele_NormApproximation_InfinitePlaces
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.GlobalClassFields.ConductorialSubgroup.finiteIndex _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalClassFieldTheory.finiteGaloisLocalField_integerRing_moduleFinite _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.residueFieldZModAlgebra _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedIntegralAlgebraContextValuationSubringAlgebra _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.LocalClassFieldTheory.comparisonIntegerRingIsIntegralClosure _root_.LocalClassFieldTheory.normalizationIntegerRingIsIntegralClosure _root_.chosenFinitePlaceCompletionAlgebra
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

/-!
# Archimedean norm approximation

This file supplies the archimedean source used in the norm-approximation
argument. At a real place the positive units have
an `n`-th root, while at a complex place every unit has one.  Consequently
the standard positive subgroup is contained in the determinant-norm image
of every scalar extension of positive degree.
-/

open scoped NumberField TensorProduct
open NumberField IsDedekindDomain
open LocalFieldTheory

noncomputable section

open LocalClassFieldTheory

universe u v

variable {K : Type} [Field K] [NumberField K]
variable {L : Type} [Field L] [Algebra K L]
    [FiniteDimensional K L]

/-- Simultaneous weak approximation into the concrete finite local norm
subgroups and into the archimedean tensor-norm images. -/
theorem exists_principal_quotient_mem_localNormSubgroups
    [IsGalois K L]
    (S : Finset (HeightOneSpectrum (𝓞 K)))
    (a : IdeleGroup K) :
    ∃ x : Kˣ,
      (∀ v : ↥S,
        IdeleGroup.finiteComponent v.1 a *
            (IdeleGroup.finiteComponent v.1
              (IdeleGroup.principalIdele K x))⁻¹ ∈
          chosenFinitePlaceLocalNormSubgroup
            (K := K) (L := L) v.1) ∧
      (∀ w : InfinitePlace K,
        IdeleGroup.infiniteComponent w a *
            (IdeleGroup.infiniteComponent w
              (IdeleGroup.principalIdele K x))⁻¹ ∈
          infiniteTensorNormSubgroup
            (K := K) (L := L) w) := by
  obtain ⟨x, hfinite, hinfinite⟩ :=
    IdeleGroup.exists_principal_quotient_mem_openAllLocalSubgroups_finset
      S a
      (fun v =>
        chosenFinitePlaceLocalNormSubgroup
          (K := K) (L := L) v.1)
      (fun w => RayClass.infinitePositiveSubgroup w)
      (fun v =>
        chosenFinitePlaceLocalNormSubgroup_isOpen
          (K := K) (L := L) v.1)
      (fun w => RayClass.isOpen_infinitePositiveSubgroup w)
  refine ⟨x, hfinite, ?_⟩
  intro w
  exact
    infinitePositiveSubgroup_le_infiniteTensorNormSubgroup
      (K := K) (L := L) w (hinfinite w)

/-- If all finite places outside a finite set split completely, one
principal correction makes a given idele a determinant norm locally at
every finite and infinite place. -/
theorem exists_principal_quotient_locallyNormEverywhere_of_splitsOutside
    [IsGalois K L]
    (S : Finset (HeightOneSpectrum (𝓞 K)))
    (hsplit :
      ∀ v : HeightOneSpectrum (𝓞 K), v ∉ S →
        FinitePlaceSplitsCompletely
          (K := K) (L := L) v)
    (a : IdeleGroup K) :
    ∃ x : Kˣ,
      (∀ v : HeightOneSpectrum (𝓞 K),
        IdeleGroup.finiteComponent v a *
            (IdeleGroup.finiteComponent v
              (IdeleGroup.principalIdele K x))⁻¹ ∈
          chosenFinitePlaceLocalNormSubgroup
            (K := K) (L := L) v) ∧
      (∀ w : InfinitePlace K,
        IdeleGroup.infiniteComponent w a *
            (IdeleGroup.infiniteComponent w
              (IdeleGroup.principalIdele K x))⁻¹ ∈
          infiniteTensorNormSubgroup
            (K := K) (L := L) w) := by
  obtain ⟨x, hfinite, hinfinite⟩ :=
    exists_principal_quotient_mem_localNormSubgroups
      (K := K) (L := L) S a
  refine ⟨x, ?_, hinfinite⟩
  intro v
  by_cases hv : v ∈ S
  · exact hfinite ⟨v, hv⟩
  · rw [
      chosenFinitePlaceLocalNormSubgroup_eq_top_of_splitsCompletely
        (K := K) (L := L) v (hsplit v hv)]
    exact Subgroup.mem_top _
end
end

section
-- module Solutions.OAIQ244_DUKE.GlobalClassFieldTheory_ClassFieldAxiom_KummerLocalNormContainment
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.infinitePlaceComplexificationOverfield_algebra _root_.GlobalClassFieldTheory.Reciprocity.infinitePlaceComplexificationOverfield_baseAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalCyclotomicCompletionAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalCyclotomicLocalizedCompletionFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalCyclotomicLocalizedCompletionIsAlgebraic _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.KummerTheory.primeCyclotomicBaseIsGalois _root_.LocalClassFieldTheory.finiteGaloisLocalField_integerRing_moduleFinite _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.diagonalLogAction _root_.OAI.PrimeDegreePackets.gLocallyCompact _root_.OAI.PrimeDegreePackets.instIsTopologicalRingLocalAlgebra _root_.OAI.PrimeDegreePackets.instLocallyCompactSpaceLocalAlgebra _root_.OAI.PrimeDegreePackets.instTopologicalSpaceLocalAlgebra _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.OAI.PrimeDegreePackets.xLocallyCompact _root_.CyclicCohomology.binaryCoefficientFamilyCommGroup _root_.LocalClassFieldTheory.comparisonIntegerRingIsIntegralClosure _root_.LocalClassFieldTheory.normalizationIntegerRingIsIntegralClosure _root_.cyclicPrimeDegreeIntermediate_isGalois _root_.cyclicPrimeSubextension_isGalois _root_.relativeUnrestrictedSPlaceFactorCommGroup
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
completion when every global Galois automorphism has exponent dividing
`n`.  This is the shared local-field core used by the coordinate and
simple-Kummer wrappers below. -/
theorem
    nthPowerSubgroup_le_chosenFinitePlaceLocalNormSubgroup_of_galois_pow_eq_one
    {K L : Type}
    [Field K] [NumberField K]
    [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    (n : ℕ+)
    (hGlobal :
      ∀ sigma : L ≃ₐ[K] L,
        sigma ^ (n : ℕ) = 1)
    (v : HeightOneSpectrum (𝓞 K)) :
    (powMonoidHom (n : ℕ) :
        (v.adicCompletion K)ˣ →*
          (v.adicCompletion K)ˣ).range ≤
      _root_.chosenFinitePlaceLocalNormSubgroup
        (K := K) (L := L) v := by
  let vK :=
    NumberField.HeightOneSpectrum.adicAbv K v
  let w := _root_.chosenFinitePlaceExtension (L := L) v
  let hvK : vK.IsNontrivial :=
    RayClass.adicAbv_isNontrivial v
  let hK :=
    AbsoluteValue.extensionCompletionAlgebra
      (K := K) w.1
  let : SMul K w.1.Completion := hK.toSMul
  let : Algebra vK.Completion w.1.Completion :=
    AbsoluteValue.completionAlgebra vK w.1 w.2
  let :=
    LocalClassFieldTheory.localizedCompletionGlobalAlgebra vK w
  let :=
    LocalClassFieldTheory.localizedCompletionIsScalarTower vK w
  let E := AlgebraicNumberTheory.Valuations.LocalizedCompletion vK w
  let : FiniteDimensional vK.Completion E :=
    AlgebraicNumberTheory.Valuations.localizedCompletionModuleFinite vK hvK w
  let : IsGalois vK.Completion E :=
    HilbertRamification.algebraicLocalization_isGalois vK w
  let : NontriviallyNormedField vK.Completion :=
    absoluteValueExtension_completionNontriviallyNormedField
      vK hvK
  let : LocallyCompactSpace vK.Completion :=
    AbsoluteValue.Completion.locallyCompactSpace
      (_root_.finitePlaceCompletionBaseMap_isometry v)
  let : IsUltrametricDist vK.Completion :=
    IsUltrametricDist.isUltrametricDist_of_isNonarchimedean_norm
      (AbsoluteValue.completionAbsoluteValue_isNonarchimedean
        vK
        (NumberField.HeightOneSpectrum.isNonarchimedean_adicAbv
          K v))
  let : Valued vK.Completion ℝ≥0 :=
    NormedField.toValued
  let vC : Valuation vK.Completion ℝ≥0 := Valued.v
  let : vC.IsNontrivial :=
    (inferInstance :
      (NormedField.valuation
        (K := vK.Completion)).IsNontrivial)
  let : ValuativeRel vK.Completion :=
    ValuativeRel.ofValuation vC
  let : vC.Compatible :=
    Valuation.Compatible.ofValuation vC
  let : ValuativeRel.IsNontrivial vK.Completion :=
    (ValuativeRel.isNontrivial_iff_isNontrivial vC).2
      inferInstance
  let : IsValuativeTopology vK.Completion :=
    isValuativeTopology_of_valued_ofValuation
      vK.Completion ℝ≥0
  let : IsNonarchimedeanLocalField vK.Completion :=
    { toIsValuativeTopology := inferInstance
      toLocallyCompactSpace := inferInstance
      toIsNontrivial := inferInstance }
  let eLocal :
      absoluteValueDecompositionGroup K w.1 ≃*
        (E ≃ₐ[vK.Completion] E) :=
    decompositionGroupEquivAlgebraicLocalizationAut
      vK hvK w
  have hLocal :
      ∀ tau : E ≃ₐ[vK.Completion] E,
        tau ^ (n : ℕ) = 1 := by
    intro tau
    apply eLocal.symm.injective
    rw [map_pow, map_one]
    apply Subtype.ext
    exact hGlobal (eLocal.symm tau).1
  have hAbelianized :
      ∀ a : Abelianization (E ≃ₐ[vK.Completion] E),
        a ^ (n : ℕ) = 1 := by
    intro a
    refine QuotientGroup.induction_on a ?_
    intro tau
    change (Abelianization.of tau) ^ (n : ℕ) = 1
    rw [← map_pow, hLocal tau, map_one]
  intro x hx
  obtain ⟨y, hy⟩ :=
    (MonoidHom.mem_range
      (G := (v.adicCompletion K)ˣ)).mp hx
  rw [powMonoidHom_apply] at hy
  subst x
  let e :
      vK.Completionˣ ≃ₜ* (v.adicCompletion K)ˣ :=
    _root_.finitePlaceCompletionUnitsContinuousMulEquiv v
  change
    y ^ (n : ℕ) ∈
      (localNormSubgroup
        vK.Completion E).map e.toMonoidHom
  refine ⟨(e.symm y) ^ (n : ℕ), ?_, ?_⟩
  · rw [← LocalClassFieldTheory.localArtinMonoidHom_ker]
    change
      LocalClassFieldTheory.localArtinMonoidHom
          vK.Completion E ((e.symm y) ^ (n : ℕ)) = 1
    rw [map_pow]
    exact hAbelianized
      (LocalClassFieldTheory.localArtinMonoidHom
        vK.Completion E (e.symm y))
  · change e ((e.symm y) ^ (n : ℕ)) = y ^ (n : ℕ)
    rw [map_pow, e.apply_symm_apply]

/-- For the actual simple Kummer extension `K(ⁿ√b)/K`, every local
`n`-th power is a norm at every finite place.  The exponent input is
produced by the concrete Kummer character, rather than supplied as a
hypothesis. -/
theorem chosenSimpleKummerNthPowerSubgroup_le_chosenFinitePlaceLocalNormSubgroup
    {K : Type} [Field K] [NumberField K]
    (n : ℕ+)
    (hnK : ((n : ℕ) : K) ≠ 0)
    (hmu : (primitiveRoots (n : ℕ) K).Nonempty)
    (b : Kˣ)
    (v : HeightOneSpectrum (𝓞 K)) :
    let E :=
      KummerTheory.chosenSimpleKummerExtension K n hnK b
    letI : FiniteDimensional K E :=
      KummerTheory.chosenSimpleKummerExtension_finiteDimensional
        K n hnK b
    letI : IsAbelianGalois K E :=
      KummerTheory.chosenSimpleKummerExtension_isAbelianGalois
        K n hnK hmu b
    (powMonoidHom (n : ℕ) :
        (v.adicCompletion K)ˣ →*
          (v.adicCompletion K)ˣ).range ≤
      _root_.chosenFinitePlaceLocalNormSubgroup
        (K := K) (L := E) v := by
  let E :=
    KummerTheory.chosenSimpleKummerExtension K n hnK b
  let : FiniteDimensional K E :=
    KummerTheory.chosenSimpleKummerExtension_finiteDimensional
      K n hnK b
  let : IsAbelianGalois K E :=
    KummerTheory.chosenSimpleKummerExtension_isAbelianGalois
      K n hnK hmu b
  exact
    nthPowerSubgroup_le_chosenFinitePlaceLocalNormSubgroup_of_galois_pow_eq_one
      (K := K) (L := E) n
      (KummerTheory.chosenSimpleKummerExtension_galois_pow_eq_one
        K n hnK hmu b) v


end GlobalClassFieldTheory.ClassFieldAxiom
end
end

section
-- module Solutions.OAIQ244_DUKE.GlobalClassFieldTheory_Cohomology_IdeleClassHerbrandSupportedFinal
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 400000
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.infinitePlaceComplexificationOverfield_baseSmul _root_.GlobalClassFieldTheory.Reciprocity.infinitePlaceComplexificationOverfield_smul _root_.GlobalClassFieldTheory.Reciprocity.rationalCyclotomicCompletionAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalCyclotomicLocalizedCompletionFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalCyclotomicLocalizedCompletionIsAlgebraic _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.DiscreteNthRootsSubgroup.instCommGroupSubtypeUnitsMemSubgroup _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.KummerTheory.finite_sUnit_nthPowerQuotient _root_.LocalClassFieldTheory.finiteGaloisLocalField_integerRing_moduleFinite _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.residueFieldZModAlgebra _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedIntegralAlgebraContextValuationSubringAlgebra _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedIntegralAlgebraContextValuationSubringTower _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedIntegralLatticeContextModuleFinite _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedIntegralLatticeContextModuleFree _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedQPadicContextValuationSubringTower _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.LubinTate.compatibleGroupFamiliesCommGroup _root_.LubinTate.compatibleGroupFamiliesGroup _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.diagonalLogAction _root_.OAI.PrimeDegreePackets.instNonemptyLeafTestSpace _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.LocalClassFieldTheory.comparisonIntegerRingIsIntegralClosure _root_.LocalClassFieldTheory.normalizationIntegerRingIsIntegralClosure _root_.RamificationTheory.HilbertRamification.CompleteDVF.decompositionGroupMulSemiringAction _root_.RamificationTheory.HilbertRamification.CompleteDVF.decompositionGroupResidueFieldMulSemiringAction
attribute [-simp] _root_.GlobalClassFieldTheory.ClassFieldAxiom.actualPushoutNormQuotientMap_mk _root_.GlobalClassFieldTheory.ClassFieldAxiom.sUnitEquivSupportedPrincipalIdeleSubgroup_coe _root_.IsDiscreteValuationRing.addVal_ringEquiv _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.KummerTheory.mem_sUnitFiniteKummerRadical_iff _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.OAI.PrimeDegreePackets.ThetaConstruction.schwartzCM_apply _root_.RayClass.primesEquiv_val_eq_natGenerator _root_.RelativeIdeleGroup.relativeFinitePlaceIdele_finiteComponent_of_ne _root_.RelativeIdeleGroup.relativeFinitePlaceIdele_finiteComponent_same _root_.RelativeIdeleGroup.relativeFinitePlaceIdele_infiniteComponent _root_.RelativeIdeleGroup.relativeInfinitePlaceIdele_finiteComponent _root_.RelativeIdeleGroup.relativeInfinitePlaceIdele_infiniteComponent_of_ne _root_.RelativeIdeleGroup.relativeInfinitePlaceIdele_infiniteComponent_same
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

/-- The diagonal map from extension-field `S`-units directly into the
supported relative ideles. -/
noncomputable def sUnitToRelativeIdeleSupported
    (S : Finset (HeightOneSpectrum (𝓞 K))) :
    SUnitGroup (K := L)
        (finitePlacesAbove (K := K) (L := L) S) →*
      relativeIdeleLocalTensorDecompositionSupportedSubgroup
        (K := K) (L := L) S :=
  ((RelativeIdeleGroup.principalSubgroup K L).subgroupOf
      (relativeIdeleLocalTensorDecompositionSupportedSubgroup
        (K := K) (L := L) S)).subtype.comp
    (sUnitToRelativePrincipalSupportedIntersection
      (K := K) (L := L) S)

/-- The restriction of the idele-class quotient map to the supported
relative ideles. -/
noncomputable def relativeIdeleSupportedToClass
    (S : Finset (HeightOneSpectrum (𝓞 K))) :
    relativeIdeleLocalTensorDecompositionSupportedSubgroup
        (K := K) (L := L) S →*
      RelativeIdeleGroup.ClassGroup K L :=
  (QuotientGroup.mk'
      (RelativeIdeleGroup.principalSubgroup K L)).comp
    (relativeIdeleLocalTensorDecompositionSupportedSubgroup
      (K := K) (L := L) S).subtype

omit [IsGalois K L] in
/-- Equivariance of the diagonal `S`-unit map into supported relative
ideles. -/
theorem sUnitToRelativeIdeleSupported_equivariant
    (S : Finset (HeightOneSpectrum (𝓞 K))) :
    letI :=
      sUnitMulDistribMulAction K L
        (finitePlacesAbove (K := K) (L := L) S)
        (finitePlacesAbove_isGaloisStable
          (K := K) (L := L) S)
    letI :=
      relativeIdeleLocalTensorDecompositionSupportedSubgroupAction
        (K := K) (L := L) S
    ∀ (σ : L ≃ₐ[K] L)
      (x :
        SUnitGroup (K := L)
          (finitePlacesAbove (K := K) (L := L) S)),
      sUnitToRelativeIdeleSupported
          (K := K) (L := L) S (σ • x) =
        σ •
          sUnitToRelativeIdeleSupported
            (K := K) (L := L) S x := by
  let sUnitAction :=
    sUnitMulDistribMulAction K L
      (finitePlacesAbove (K := K) (L := L) S)
      (finitePlacesAbove_isGaloisStable
        (K := K) (L := L) S)
  let supportedAction :=
    relativeIdeleLocalTensorDecompositionSupportedSubgroupAction
      (K := K) (L := L) S
  intro σ x
  apply Subtype.ext
  change
    RelativeIdeleGroup.principalIdele K L
        (((σ • x :
          SUnitGroup (K := L)
            (finitePlacesAbove (K := K) (L := L) S)) :
          Lˣ)) =
      σ • RelativeIdeleGroup.principalIdele K L (x : Lˣ)
  rw [sUnit_smul_coe]
  exact
    (RelativeIdeleGroup.smul_principalIdele
      K L σ (x : Lˣ)).symm

omit [NumberField L] [IsGalois K L] in
/-- Equivariance of the supported-idele quotient map. -/
theorem relativeIdeleSupportedToClass_equivariant
    (S : Finset (HeightOneSpectrum (𝓞 K))) :
    letI :=
      relativeIdeleLocalTensorDecompositionSupportedSubgroupAction
        (K := K) (L := L) S
    letI := ideleClassMulDistribMulAction K L
    ∀ (σ : L ≃ₐ[K] L)
      (z :
        relativeIdeleLocalTensorDecompositionSupportedSubgroup
          (K := K) (L := L) S),
      relativeIdeleSupportedToClass
          (K := K) (L := L) S (σ • z) =
        σ •
          relativeIdeleSupportedToClass
            (K := K) (L := L) S z := by
  let supportedAction :=
    relativeIdeleLocalTensorDecompositionSupportedSubgroupAction
      (K := K) (L := L) S
  let classAction := ideleClassMulDistribMulAction K L
  intro σ z
  change
    QuotientGroup.mk'
        (RelativeIdeleGroup.principalSubgroup K L)
        ((σ • z :
          relativeIdeleLocalTensorDecompositionSupportedSubgroup
            (K := K) (L := L) S) :
          RelativeIdeleGroup K L) =
      σ •
        QuotientGroup.mk'
          (RelativeIdeleGroup.principalSubgroup K L)
          (z : RelativeIdeleGroup K L)
  rw [
    relativeIdeleLocalTensorDecompositionSupportedSubgroupAction_coe]
  exact ideleClassQuotientMap_equivariant K L σ z

omit [IsGalois K L] in
/-- The diagonal `S`-unit map into supported relative ideles is
injective. -/
theorem sUnitToRelativeIdeleSupported_injective
    (S : Finset (HeightOneSpectrum (𝓞 K))) :
    Function.Injective
      (sUnitToRelativeIdeleSupported
        (K := K) (L := L) S) := by
  intro x y hxy
  apply
    (sUnitEquivRelativePrincipalSupportedIntersection
      (K := K) (L := L) S).injective
  apply
    ((RelativeIdeleGroup.principalSubgroup K L).subgroupOf
      (relativeIdeleLocalTensorDecompositionSupportedSubgroup
        (K := K) (L := L) S)).subtype_injective
  exact hxy

omit [NumberField L] [IsGalois K L] in
/-- If the supported and principal relative ideles generate all
relative ideles, the restricted map to idele classes is surjective. -/
theorem relativeIdeleSupportedToClass_surjective
    (S : Finset (HeightOneSpectrum (𝓞 K)))
    (hSP :
      relativeIdeleLocalTensorDecompositionSupportedSubgroup
            (K := K) (L := L) S ⊔
          RelativeIdeleGroup.principalSubgroup K L =
        ⊤) :
    Function.Surjective
      (relativeIdeleSupportedToClass
        (K := K) (L := L) S) := by
  intro q
  refine q.inductionOn' ?_
  intro g
  have hg :
      g ∈
        relativeIdeleLocalTensorDecompositionSupportedSubgroup
              (K := K) (L := L) S ⊔
            RelativeIdeleGroup.principalSubgroup K L := by
    rw [hSP]
    exact Subgroup.mem_top g
  rw [Subgroup.mem_sup] at hg
  obtain ⟨s, hs, p, hp, hsp⟩ := hg
  refine ⟨⟨s, hs⟩, ?_⟩
  change
    QuotientGroup.mk'
        (RelativeIdeleGroup.principalSubgroup K L) s =
      QuotientGroup.mk'
        (RelativeIdeleGroup.principalSubgroup K L) g
  rw [← hsp, map_mul]
  have hpone :
      QuotientGroup.mk'
          (RelativeIdeleGroup.principalSubgroup K L) p =
        1 :=
    (QuotientGroup.eq_one_iff
      (N := RelativeIdeleGroup.principalSubgroup K L)
      (x := p)).2 hp
  rw [hpone]
  exact
    (mul_one
      (QuotientGroup.mk'
        (RelativeIdeleGroup.principalSubgroup K L) s)).symm

omit [IsGalois K L] in
/-- Exactness at the supported relative ideles of
`S`-units → supported ideles → idele classes. -/
theorem sUnit_supportedIdele_ideleClass_exact
    (S : Finset (HeightOneSpectrum (𝓞 K))) :
    ∀ z :
      relativeIdeleLocalTensorDecompositionSupportedSubgroup
        (K := K) (L := L) S,
      relativeIdeleSupportedToClass
          (K := K) (L := L) S z = 1 ↔
        ∃ x :
          SUnitGroup (K := L)
            (finitePlacesAbove (K := K) (L := L) S),
          sUnitToRelativeIdeleSupported
              (K := K) (L := L) S x =
            z := by
  intro z
  constructor
  · intro hz
    have hzPrincipal :
        (z : RelativeIdeleGroup K L) ∈
          RelativeIdeleGroup.principalSubgroup K L := by
      exact
        (QuotientGroup.eq_one_iff
          (N := RelativeIdeleGroup.principalSubgroup K L)
          (x := (z : RelativeIdeleGroup K L))).1 hz
    let y :
        (RelativeIdeleGroup.principalSubgroup K L).subgroupOf
          (relativeIdeleLocalTensorDecompositionSupportedSubgroup
            (K := K) (L := L) S) :=
      ⟨z, hzPrincipal⟩
    obtain ⟨x, hx⟩ :=
      (sUnitEquivRelativePrincipalSupportedIntersection
        (K := K) (L := L) S).surjective y
    refine ⟨x, ?_⟩
    apply Subtype.ext
    have hcoerce :=
      congrArg
        (fun a :
          (RelativeIdeleGroup.principalSubgroup K L).subgroupOf
            (relativeIdeleLocalTensorDecompositionSupportedSubgroup
              (K := K) (L := L) S) =>
          (a :
            relativeIdeleLocalTensorDecompositionSupportedSubgroup
              (K := K) (L := L) S))
        hx
    exact congrArg Subtype.val hcoerce
  · rintro ⟨x, rfl⟩
    change
      QuotientGroup.mk'
          (RelativeIdeleGroup.principalSubgroup K L)
          (RelativeIdeleGroup.principalIdele K L (x : Lˣ)) =
        1
    exact
      (QuotientGroup.eq_one_iff
        (N := RelativeIdeleGroup.principalSubgroup K L)
        (x :=
          RelativeIdeleGroup.principalIdele K L (x : Lˣ))).2
        ⟨(x : Lˣ), rfl⟩

/-- Finiteness of the low Tate groups of the `S`-unit module for the
support pulled back from `K`. -/
def AboveSUnitHerbrandQuotientDefined
    (S : Finset (HeightOneSpectrum (𝓞 K)))
    (σ : L ≃ₐ[K] L) : Prop :=
  letI :=
    sUnitMulDistribMulAction K L
      (finitePlacesAbove (K := K) (L := L) S)
      (finitePlacesAbove_isGaloisStable
        (K := K) (L := L) S)
  HerbrandQuotientDefined
    (L ≃ₐ[K] L)
    (SUnitGroup (K := L)
      (finitePlacesAbove (K := K) (L := L) S)) σ

/-- Finiteness of the low Tate groups of the supported relative-idele
module. -/
def RelativeIdeleSupportedHerbrandQuotientDefined
    (S : Finset (HeightOneSpectrum (𝓞 K)))
    (σ : L ≃ₐ[K] L) : Prop :=
  letI :=
    relativeIdeleLocalTensorDecompositionSupportedSubgroupAction
      (K := K) (L := L) S
  HerbrandQuotientDefined
    (L ≃ₐ[K] L)
    (relativeIdeleLocalTensorDecompositionSupportedSubgroup
      (K := K) (L := L) S) σ

/-- The permutation-representation presentation of the action on
logarithmic places above a base support.  This is the presentation used
by the `S`-unit Herbrand theorem. -/
@[reducible]
noncomputable def aboveSLogPlaceMulAction
    (S : Finset (HeightOneSpectrum (𝓞 K))) :
    MulAction (L ≃ₐ[K] L)
      (SUnitGroup.LogPlace
        (K := L)
        (finitePlacesAbove (K := K) (L := L) S)) :=
  permutationMulAction
    (logPlacePermutationHom K L
      (finitePlacesAbove (K := K) (L := L) S)
      (finitePlacesAbove_isGaloisStable
        (K := K) (L := L) S))

/-- Send a logarithmic place of `L` lying over the pulled-back support
to its underlying unrestricted place of `K`. -/
noncomputable def logPlaceBelowRelativeUnrestrictedIndex
    (S : Finset (HeightOneSpectrum (𝓞 K))) :
    SUnitGroup.LogPlace
        (K := L)
        (finitePlacesAbove (K := K) (L := L) S) →
      RelativeUnrestrictedSPlaceIndex (K := K) S
  | Sum.inl W =>
      Sum.inl (W.comap (algebraMap K L))
  | Sum.inr W =>
      Sum.inr
        ⟨finitePlaceBelow (K := K) W.1,
          (mem_finitePlacesAbove_iff
            (K := K) (L := L) S W.1).1 W.2⟩

omit [FiniteDimensional K L] [IsGalois K L] in
/-- The place-below map is constant on Galois orbits of logarithmic
places. -/
theorem logPlaceBelowRelativeUnrestrictedIndex_smul
    (S : Finset (HeightOneSpectrum (𝓞 K)))
    (σ : L ≃ₐ[K] L)
    (q :
      SUnitGroup.LogPlace
        (K := L)
        (finitePlacesAbove (K := K) (L := L) S)) :
    letI :=
      aboveSLogPlaceMulAction
        (K := K) (L := L) S
    logPlaceBelowRelativeUnrestrictedIndex
        (K := K) (L := L) S (σ • q) =
      logPlaceBelowRelativeUnrestrictedIndex
        (K := K) (L := L) S q := by
  let logAction :=
    aboveSLogPlaceMulAction
      (K := K) (L := L) S
  cases q with
  | inl W =>
      change
        logPlaceBelowRelativeUnrestrictedIndex
            (K := K) (L := L) S
            (logPlacePermutationHom K L
              (finitePlacesAbove (K := K) (L := L) S)
              (finitePlacesAbove_isGaloisStable
                (K := K) (L := L) S) σ (Sum.inl W)) =
          logPlaceBelowRelativeUnrestrictedIndex
            (K := K) (L := L) S (Sum.inl W)
      rw [logPlacePermutationHom_apply]
      change
        Sum.inl ((σ • W).comap (algebraMap K L)) =
          Sum.inl (W.comap (algebraMap K L))
      congr 1
      rw [NumberField.InfinitePlace.comap_smul]
      congr 1
      ext x
      exact σ.symm.commutes x
  | inr W =>
      change
        logPlaceBelowRelativeUnrestrictedIndex
            (K := K) (L := L) S
            (logPlacePermutationHom K L
              (finitePlacesAbove (K := K) (L := L) S)
              (finitePlacesAbove_isGaloisStable
                (K := K) (L := L) S) σ (Sum.inr W)) =
          logPlaceBelowRelativeUnrestrictedIndex
            (K := K) (L := L) S (Sum.inr W)
      rw [logPlacePermutationHom_apply]
      change
        Sum.inr
            (⟨finitePlaceBelow (K := K)
                (finitePlaceEquiv K L σ W.1), _⟩ :
              {v : HeightOneSpectrum (𝓞 K) // v ∈ S}) =
          Sum.inr
            (⟨finitePlaceBelow (K := K) W.1, _⟩ :
              {v : HeightOneSpectrum (𝓞 K) // v ∈ S})
      congr 1
      apply Subtype.ext
      exact
        finitePlaceBelow_finitePlaceEquiv
          (K := K) (L := L) σ W.1

/-- The map on Galois orbits induced by taking the place below. -/
noncomputable def logPlaceOrbitBelowRelativeUnrestrictedIndex
    (S : Finset (HeightOneSpectrum (𝓞 K))) :
    letI :=
      aboveSLogPlaceMulAction
        (K := K) (L := L) S
    MulAction.orbitRel.Quotient
        (L ≃ₐ[K] L)
        (SUnitGroup.LogPlace
          (K := L)
          (finitePlacesAbove (K := K) (L := L) S)) →
      RelativeUnrestrictedSPlaceIndex (K := K) S := by
  letI logAction :=
    aboveSLogPlaceMulAction
      (K := K) (L := L) S
  exact
    Quotient.lift
      (logPlaceBelowRelativeUnrestrictedIndex
        (K := K) (L := L) S)
      (by
        intro a b hab
        rcases hab with ⟨σ, hσ⟩
        rw [← hσ]
        exact
          logPlaceBelowRelativeUnrestrictedIndex_smul
            (K := K) (L := L) S σ b)

omit [FiniteDimensional K L] [IsGalois K L] in
/-- Evaluating the orbit-descended log-place map on a quotient class gives
the original map on any representative. -/
@[simp]
theorem logPlaceOrbitBelowRelativeUnrestrictedIndex_mk
    (S : Finset (HeightOneSpectrum (𝓞 K)))
    (q :
      SUnitGroup.LogPlace
        (K := L)
        (finitePlacesAbove (K := K) (L := L) S)) :
    letI :=
      aboveSLogPlaceMulAction
        (K := K) (L := L) S
    logPlaceOrbitBelowRelativeUnrestrictedIndex
        (K := K) (L := L) S (Quotient.mk'' q) =
      logPlaceBelowRelativeUnrestrictedIndex
        (K := K) (L := L) S q :=
  rfl

/-- Galois orbits of logarithmic places of `L` above `S` are
canonically indexed by all infinite places of `K` and the finite
places in `S`. -/
noncomputable def
    logPlaceOrbitEquivRelativeUnrestrictedSPlaceIndex
    (S : Finset (HeightOneSpectrum (𝓞 K))) :
    letI :=
      aboveSLogPlaceMulAction
        (K := K) (L := L) S
    MulAction.orbitRel.Quotient
        (L ≃ₐ[K] L)
        (SUnitGroup.LogPlace
          (K := L)
          (finitePlacesAbove (K := K) (L := L) S)) ≃
      RelativeUnrestrictedSPlaceIndex (K := K) S := by
  letI stableFiniteAction :=
    stableFinitePlaceMulAction K L
      (finitePlacesAbove (K := K) (L := L) S)
      (finitePlacesAbove_isGaloisStable
        (K := K) (L := L) S)
  letI logAction :=
    aboveSLogPlaceMulAction
      (K := K) (L := L) S
  let f :=
    logPlaceOrbitBelowRelativeUnrestrictedIndex
      (K := K) (L := L) S
  apply Equiv.ofBijective f
  constructor
  · intro x y hxy
    induction x using Quotient.inductionOn' with
    | _ a =>
      induction y using Quotient.inductionOn' with
      | _ b =>
        apply Quotient.sound
        apply MulAction.orbitRel_apply.mpr
        cases a with
        | inl W₁ =>
            cases b with
            | inl W₂ =>
                have hbelow :
                    W₁.comap (algebraMap K L) =
                      W₂.comap (algebraMap K L) := by
                  exact Sum.inl.inj hxy
                obtain ⟨σ, hσ⟩ :=
                  NumberField.InfinitePlace.exists_smul_eq_of_comap_eq
                    hbelow
                refine ⟨σ⁻¹, ?_⟩
                change
                  logPlacePermutationHom K L
                      (finitePlacesAbove (K := K) (L := L) S)
                      (finitePlacesAbove_isGaloisStable
                        (K := K) (L := L) S) σ⁻¹
                      (Sum.inl W₂) =
                    Sum.inl W₁
                rw [logPlacePermutationHom_apply]
                change Sum.inl (σ⁻¹ • W₂) = Sum.inl W₁
                rw [← hσ, inv_smul_smul]
            | inr W₂ =>
                change
                  Sum.inl (W₁.comap (algebraMap K L)) =
                    Sum.inr
                      (⟨finitePlaceBelow (K := K) W₂.1, _⟩ :
                        {v : HeightOneSpectrum (𝓞 K) // v ∈ S})
                  at hxy
                exact (Sum.inl_ne_inr hxy).elim
        | inr W₁ =>
            cases b with
            | inl W₂ =>
                change
                  Sum.inr
                      (⟨finitePlaceBelow (K := K) W₁.1, _⟩ :
                        {v : HeightOneSpectrum (𝓞 K) // v ∈ S}) =
                    Sum.inl (W₂.comap (algebraMap K L))
                  at hxy
                exact (Sum.inr_ne_inl hxy).elim
            | inr W₂ =>
                have hbelow :
                    finitePlaceBelow (K := K) W₁.1 =
                      finitePlaceBelow (K := K) W₂.1 := by
                  exact congrArg Subtype.val (Sum.inr.inj hxy)
                let v :=
                  finitePlaceBelow (K := K) W₁.1
                let : Finite (L ≃ₐ[K] L) :=
                  IsGaloisGroup.finite (L ≃ₐ[K] L) K L
                let :
                    IsGaloisGroup
                      (L ≃ₐ[K] L) (𝓞 K) (𝓞 L) :=
                  IsGaloisGroup.of_isFractionRing
                    (L ≃ₐ[K] L) (𝓞 K) (𝓞 L) K L
                let : W₁.1.asIdeal.LiesOver v.asIdeal :=
                  ⟨by
                    simp only [v, finitePlaceBelow_asIdeal]⟩
                let : W₂.1.asIdeal.LiesOver v.asIdeal :=
                  ⟨by
                    have h :=
                      congrArg HeightOneSpectrum.asIdeal hbelow
                    simpa only [v, finitePlaceBelow_asIdeal]
                      using h⟩
                obtain ⟨σ, hσ⟩ :=
                  HilbertRamification.Dedekind.exists_smul_eq_of_isGaloisGroup
                    v.asIdeal W₁.1.asIdeal W₂.1.asIdeal
                    (L ≃ₐ[K] L)
                have hplace :
                    finitePlaceEquiv K L σ W₁.1 = W₂.1 := by
                  apply HeightOneSpectrum.ext
                  rw [finitePlaceEquiv_asIdeal]
                  exact hσ
                have hsubtype : σ • W₁ = W₂ := by
                  apply Subtype.ext
                  exact hplace
                refine ⟨σ⁻¹, ?_⟩
                change
                  logPlacePermutationHom K L
                      (finitePlacesAbove (K := K) (L := L) S)
                      (finitePlacesAbove_isGaloisStable
                        (K := K) (L := L) S) σ⁻¹
                      (Sum.inr W₂) =
                    Sum.inr W₁
                rw [logPlacePermutationHom_apply]
                change Sum.inr (σ⁻¹ • W₂) = Sum.inr W₁
                rw [← hsubtype, inv_smul_smul]
  · intro i
    cases i with
    | inl v =>
        refine
          ⟨Quotient.mk''
              (Sum.inl
                (chosenInfinitePlaceAbove (L := L) v)), ?_⟩
        exact
          congrArg Sum.inl
            (chosenInfinitePlaceAbove_comap
              (L := L) v)
    | inr v =>
        let w :=
          chosenFinitePlaceExtension (L := L) v.1
        let W :=
          finitePlaceExtensionCentre
            (K := K) (L := L) v.1 w
        have hWbelow :
            finitePlaceBelow (K := K) W = v.1 :=
          finitePlaceBelow_finitePlaceExtensionCentre
            (K := K) (L := L) v.1 w
        have hWmem :
            W ∈ finitePlacesAbove
              (K := K) (L := L) S :=
          (mem_finitePlacesAbove_iff
            (K := K) (L := L) S W).2
            (hWbelow ▸ v.2)
        refine
          ⟨Quotient.mk''
              (Sum.inr
                (⟨W, hWmem⟩ :
                  finitePlacesAbove
                    (K := K) (L := L) S)), ?_⟩
        apply congrArg Sum.inr
        apply Subtype.ext
        exact hWbelow

/-- The local degree attached to a logarithmic place agrees with the
local degree attached to its place below. -/
theorem
    relativeUnrestrictedSPlaceLocalDegree_logPlaceBelow
    (S : Finset (HeightOneSpectrum (𝓞 K)))
    (q :
      SUnitGroup.LogPlace
        (K := L)
        (finitePlacesAbove (K := K) (L := L) S)) :
    relativeUnrestrictedSPlaceLocalDegree
        (K := K) (L := L) S
        (logPlaceBelowRelativeUnrestrictedIndex
          (K := K) (L := L) S q) =
      logPlaceLocalDegree K L
        (finitePlacesAbove (K := K) (L := L) S) q := by
  cases q with
  | inl W =>
      let W₀ :=
        chosenInfinitePlaceAbove
          (L := L) (W.comap (algebraMap K L))
      change
        Nat.card (absoluteValueDecompositionGroup K W₀.1) =
          if NumberField.InfinitePlace.IsUnramified K W
          then 1 else 2
      rw [
        absoluteValueDecompositionGroup_eq_infinitePlaceStabilizer W₀,
        NumberField.InfinitePlace.card_stabilizer]
      have hcomap :
          W₀.comap (algebraMap K L) =
            W.comap (algebraMap K L) :=
        chosenInfinitePlaceAbove_comap
          (L := L) (W.comap (algebraMap K L))
      obtain ⟨τ, hτ⟩ :=
        NumberField.InfinitePlace.exists_smul_eq_of_comap_eq
          hcomap
      rw [← hτ,
        NumberField.InfinitePlace.isUnramified_smul_iff]
  | inr W =>
      let v :=
        finitePlaceBelow (K := K) W.1
      let w :=
        chosenFinitePlaceExtension (L := L) v
      let W₀ :=
        finitePlaceExtensionCentre
          (K := K) (L := L) v w
      let finiteAction := finitePlaceMulAction K L
      let : Finite (L ≃ₐ[K] L) :=
        IsGaloisGroup.finite (L ≃ₐ[K] L) K L
      let :
          IsGaloisGroup
            (L ≃ₐ[K] L) (𝓞 K) (𝓞 L) :=
        IsGaloisGroup.of_isFractionRing
          (L ≃ₐ[K] L) (𝓞 K) (𝓞 L) K L
      let : W₀.asIdeal.LiesOver v.asIdeal :=
        ⟨(finitePlaceExtensionCentreIdeal_under
          (K := K) (L := L) v w).symm⟩
      let : W.1.asIdeal.LiesOver v.asIdeal :=
        ⟨by
          simp only [v, finitePlaceBelow_asIdeal]⟩
      obtain ⟨τ, hτ⟩ :=
        HilbertRamification.Dedekind.exists_smul_eq_of_isGaloisGroup
          v.asIdeal W₀.asIdeal W.1.asIdeal
          (L ≃ₐ[K] L)
      have hplace :
          finitePlaceEquiv K L τ W₀ = W.1 := by
        apply HeightOneSpectrum.ext
        rw [finitePlaceEquiv_asIdeal]
        exact hτ
      have hcard :
          Nat.card
              (MulAction.stabilizer (L ≃ₐ[K] L) W₀) =
            Nat.card
              (MulAction.stabilizer (L ≃ₐ[K] L) W.1) :=
        Nat.card_congr
          (MulAction.stabilizerEquivStabilizer
            hplace.symm).toEquiv
      change
        Nat.card (absoluteValueDecompositionGroup K w.1) =
          finiteLogPlaceLocalDegree K L W.1
      rw [
        absoluteValueDecompositionGroup_eq_finitePlaceStabilizer
          (K := K) (L := L) v w]
      exact
        hcard.trans
          (finitePlace_stabilizer_card_eq_localDegree
            K L W.1)

omit [IsGalois K L] in
/-- Cancellation on the supported short exact sequence: if supported
ideles and `S`-units have quotients `q` and `q / |G|`, respectively,
then the idele-class quotient is `|G|`. -/
theorem
    ideleClass_herbrandQuotient_eq_card_of_sUnit_supported_values
    (S : Finset (HeightOneSpectrum (𝓞 K)))
    (σ : L ≃ₐ[K] L)
    (hgen : ∀ τ : L ≃ₐ[K] L,
      τ ∈ Subgroup.zpowers σ)
    (hSP :
      relativeIdeleLocalTensorDecompositionSupportedSubgroup
            (K := K) (L := L) S ⊔
          RelativeIdeleGroup.principalSubgroup K L =
        ⊤)
    (hUnitDefined :
      AboveSUnitHerbrandQuotientDefined
        (K := K) (L := L) S σ)
    (hSupportedDefined :
      RelativeIdeleSupportedHerbrandQuotientDefined
        (K := K) (L := L) S σ)
    (q : ℚ) (hq : q ≠ 0)
    (hSupported :
      letI :=
        relativeIdeleLocalTensorDecompositionSupportedSubgroupAction
          (K := K) (L := L) S
      letI : Finite
          (HerbrandH0 (L ≃ₐ[K] L)
            (relativeIdeleLocalTensorDecompositionSupportedSubgroup
              (K := K) (L := L) S)) :=
        hSupportedDefined.1
      letI : Finite
          (HerbrandHMinusOne (L ≃ₐ[K] L)
            (relativeIdeleLocalTensorDecompositionSupportedSubgroup
              (K := K) (L := L) S) σ) :=
        hSupportedDefined.2
      herbrandQuotient
          (G := L ≃ₐ[K] L)
          (A := relativeIdeleLocalTensorDecompositionSupportedSubgroup
            (K := K) (L := L) S) σ = q)
    (hUnit :
      letI :=
        sUnitMulDistribMulAction K L
          (finitePlacesAbove (K := K) (L := L) S)
          (finitePlacesAbove_isGaloisStable
            (K := K) (L := L) S)
      letI : Finite
          (HerbrandH0 (L ≃ₐ[K] L)
            (SUnitGroup (K := L)
              (finitePlacesAbove
                (K := K) (L := L) S))) :=
        hUnitDefined.1
      letI : Finite
          (HerbrandHMinusOne (L ≃ₐ[K] L)
            (SUnitGroup (K := L)
              (finitePlacesAbove
                (K := K) (L := L) S)) σ) :=
        hUnitDefined.2
      herbrandQuotient
          (G := L ≃ₐ[K] L)
          (A := SUnitGroup (K := L)
            (finitePlacesAbove (K := K) (L := L) S)) σ =
        q / (Fintype.card (L ≃ₐ[K] L) : ℚ)) :
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
  let sUnitAction :=
    sUnitMulDistribMulAction K L
      (finitePlacesAbove (K := K) (L := L) S)
      (finitePlacesAbove_isGaloisStable
        (K := K) (L := L) S)
  let supportedAction :=
    relativeIdeleLocalTensorDecompositionSupportedSubgroupAction
      (K := K) (L := L) S
  let classAction := ideleClassMulDistribMulAction K L
  let hU0 :
      Finite
        (HerbrandH0 (L ≃ₐ[K] L)
          (SUnitGroup (K := L)
            (finitePlacesAbove (K := K) (L := L) S))) :=
    hUnitDefined.1
  let hUm :
      Finite
        (HerbrandHMinusOne (L ≃ₐ[K] L)
          (SUnitGroup (K := L)
            (finitePlacesAbove (K := K) (L := L) S)) σ) :=
    hUnitDefined.2
  let hS0 :
      Finite
        (HerbrandH0 (L ≃ₐ[K] L)
          (relativeIdeleLocalTensorDecompositionSupportedSubgroup
            (K := K) (L := L) S)) :=
    hSupportedDefined.1
  let hSm :
      Finite
        (HerbrandHMinusOne (L ≃ₐ[K] L)
          (relativeIdeleLocalTensorDecompositionSupportedSubgroup
            (K := K) (L := L) S) σ) :=
    hSupportedDefined.2
  let i :
      SUnitGroup (K := L)
          (finitePlacesAbove (K := K) (L := L) S) →*
        relativeIdeleLocalTensorDecompositionSupportedSubgroup
          (K := K) (L := L) S :=
    sUnitToRelativeIdeleSupported
      (K := K) (L := L) S
  let j :
      relativeIdeleLocalTensorDecompositionSupportedSubgroup
          (K := K) (L := L) S →*
        RelativeIdeleGroup.ClassGroup K L :=
    relativeIdeleSupportedToClass
      (K := K) (L := L) S
  have hi :
      ∀ (τ : L ≃ₐ[K] L)
        (x :
          SUnitGroup (K := L)
            (finitePlacesAbove (K := K) (L := L) S)),
        i (τ • x) = τ • i x := by
    simpa [i] using
      (sUnitToRelativeIdeleSupported_equivariant
        (K := K) (L := L) S)
  have hj :
      ∀ (τ : L ≃ₐ[K] L)
        (z :
          relativeIdeleLocalTensorDecompositionSupportedSubgroup
            (K := K) (L := L) S),
        j (τ • z) = τ • j z := by
    simpa [j] using
      (relativeIdeleSupportedToClass_equivariant
        (K := K) (L := L) S)
  have hker :
      ∀ z :
        relativeIdeleLocalTensorDecompositionSupportedSubgroup
          (K := K) (L := L) S,
        j z = 1 ↔
          ∃ x :
            SUnitGroup (K := L)
              (finitePlacesAbove (K := K) (L := L) S),
            i x = z := by
    simpa [i, j] using
      (sUnit_supportedIdele_ideleClass_exact
        (K := K) (L := L) S)
  have hinj : Function.Injective i := by
    simpa [i] using
      (sUnitToRelativeIdeleSupported_injective
        (K := K) (L := L) S)
  have hsurj : Function.Surjective j := by
    simpa [j] using
      (relativeIdeleSupportedToClass_surjective
        (K := K) (L := L) S hSP)
  let hC :
      HerbrandQuotientDefined
        (L ≃ₐ[K] L)
        (RelativeIdeleGroup.ClassGroup K L) σ :=
    @herbrandQuotientDefined_right_of_left_middle
      (L ≃ₐ[K] L)
      (SUnitGroup (K := L)
        (finitePlacesAbove (K := K) (L := L) S))
      (relativeIdeleLocalTensorDecompositionSupportedSubgroup
        (K := K) (L := L) S)
      (RelativeIdeleGroup.ClassGroup K L)
      inferInstance inferInstance inferInstance inferInstance
      inferInstance inferInstance inferInstance inferInstance
      i j hi hj hker hinj hsurj
      σ hgen hUnitDefined hSupportedDefined
  let hC0 := hC.1
  let hCm := hC.2
  have hmul :
      herbrandQuotient
          (G := L ≃ₐ[K] L)
          (A := relativeIdeleLocalTensorDecompositionSupportedSubgroup
            (K := K) (L := L) S) σ =
        herbrandQuotient
            (G := L ≃ₐ[K] L)
            (A := SUnitGroup (K := L)
              (finitePlacesAbove (K := K) (L := L) S)) σ *
          herbrandQuotient
            (G := L ≃ₐ[K] L)
            (A := RelativeIdeleGroup.ClassGroup K L) σ :=
    @herbrandQuotient_multiplicative_of_shortExact
      (L ≃ₐ[K] L)
      (SUnitGroup (K := L)
        (finitePlacesAbove (K := K) (L := L) S))
      (relativeIdeleLocalTensorDecompositionSupportedSubgroup
        (K := K) (L := L) S)
      (RelativeIdeleGroup.ClassGroup K L)
      inferInstance inferInstance inferInstance inferInstance
      inferInstance inferInstance inferInstance inferInstance
      i j hi hj hker hinj hsurj σ hgen
      inferInstance inferInstance inferInstance
      inferInstance inferInstance inferInstance
  have hcard :
      (Fintype.card (L ≃ₐ[K] L) : ℚ) ≠ 0 :=
    Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  have hfactor :
      q / (Fintype.card (L ≃ₐ[K] L) : ℚ) ≠ 0 :=
    div_ne_zero hq hcard
  refine ⟨hC, ?_⟩
  apply mul_left_cancel₀ hfactor
  calc
    (q / (Fintype.card (L ≃ₐ[K] L) : ℚ)) *
          @herbrandQuotient
            (L ≃ₐ[K] L)
            (RelativeIdeleGroup.ClassGroup K L)
            _ _ _ _ σ hC.1 hC.2 =
        q := by
      rw [← hUnit, ← hmul, hSupported]
    _ =
        (q / (Fintype.card (L ≃ₐ[K] L) : ℚ)) *
          (Fintype.card (L ≃ₐ[K] L) : ℚ) := by
      rw [div_mul_cancel₀ q hcard]

end Cohomology
end GlobalClassFieldTheory
end
end

section
-- module Solutions.OAIQ244_DUKE.GlobalClassFieldTheory_Cohomology_CyclicPrimePowerFullDecomposition
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.GlobalClassFields.ConductorialSubgroup.finiteIndex _root_.GlobalClassFieldTheory.Reciprocity.complexFourthRootField_numberField _root_.GlobalClassFieldTheory.Reciprocity.infinitePlaceComplexificationOverfield_algebra _root_.GlobalClassFieldTheory.Reciprocity.infinitePlaceComplexificationOverfield_baseAlgebra _root_.GlobalClassFieldTheory.Reciprocity.infinitePlaceComplexificationOverfield_numberField _root_.GlobalClassFieldTheory.Reciprocity.rationalIntermediateFieldNumberField _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.KummerTheory.primeCyclotomicBaseFiniteDimensional _root_.KummerTheory.primeCyclotomicBaseIsGalois _root_.KummerTheory.primeCyclotomicBaseNumberField _root_.KummerTheory.rationalCyclotomicLevel_numberField _root_.LocalClassFieldTheory.finiteGaloisLocalField_integerRing_moduleFinite _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.residueFieldZModAlgebra _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedIntegralAlgebraContextValuationSubringAlgebra _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedIntegralAlgebraContextValuationSubringTower _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedQPadicContextValuationSubringTower _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.boundedRealFields_numberField _root_.OAI.PrimeDegreePackets.diagonalLogAction _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.LocalClassFieldTheory.comparisonIntegerRingIsIntegralClosure _root_.LocalClassFieldTheory.normalizationIntegerRingIsIntegralClosure _root_.cyclicPrimeDegreeIntermediate_isGalois
attribute [-simp] _root_.GlobalClassFieldTheory.ClassFieldAxiom.actualPushoutNormQuotientMap_mk _root_.GlobalClassFieldTheory.ClassFieldAxiom.sUnitEquivSupportedPrincipalIdeleSubgroup_coe _root_.IdeleGroup.finitePlaceIdele_finiteComponent_of_ne _root_.IdeleGroup.finitePlaceIdele_finiteComponent_same _root_.IdeleGroup.finitePlaceIdele_infiniteComponent _root_.IdeleGroup.infinitePlaceIdeleContinuous_apply _root_.IdeleGroup.infinitePlaceIdele_finiteComponent _root_.IdeleGroup.infinitePlaceIdele_infiniteComponent_of_ne _root_.IdeleGroup.infinitePlaceIdele_infiniteComponent_same _root_.IsDiscreteValuationRing.addVal_ringEquiv _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.OAI.PrimeDegreePackets.ThetaConstruction.schwartzCM_apply _root_.RayClass.primesEquiv_val_eq_natGenerator _root_.RayClass.signToNarrow_mk _root_.RelativeIdeleGroup.relativeFinitePlaceIdele_finiteComponent_of_ne _root_.RelativeIdeleGroup.relativeFinitePlaceIdele_finiteComponent_same _root_.RelativeIdeleGroup.relativeFinitePlaceIdele_infiniteComponent _root_.RelativeIdeleGroup.relativeInfinitePlaceIdele_finiteComponent _root_.RelativeIdeleGroup.relativeInfinitePlaceIdele_infiniteComponent_of_ne _root_.RelativeIdeleGroup.relativeInfinitePlaceIdele_infiniteComponent_same
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

/-- If every finite place outside a finite set splits completely, then
idelic approximation shows that every idele class is a norm. -/
theorem ideleClassNorm_range_eq_top_of_splitsCompletely_outside
    {E : Type}
    [Field E] [NumberField E] [Algebra K E]
    [FiniteDimensional K E] [IsGalois K E]
    (S : Finset (HeightOneSpectrum (𝓞 K)))
    (hsplit :
      ∀ v : HeightOneSpectrum (𝓞 K), v ∉ S →
        FinitePlaceSplitsCompletely
          (K := K) (L := E) v) :
    (RelativeIdeleGroup.Cohomology.ideleClassNorm K E).range = ⊤ := by
  apply top_unique
  intro c _
  obtain ⟨a, rfl⟩ :=
    QuotientGroup.mk'_surjective
      (IdeleGroup.principalSubgroup K) c
  obtain ⟨x, hfinite, hinfinite⟩ :=
    exists_principal_quotient_locallyNormEverywhere_of_splitsOutside
      (K := K) (L := E) S hsplit a
  let b : IdeleGroup K :=
    a * (IdeleGroup.principalIdele K x)⁻¹
  have hInfinite :
      ∀ w : InfinitePlace K,
        IdeleGroup.infiniteComponent w b ∈
          infiniteTensorNormSubgroup
            (K := K) (L := E) w := by
    intro w
    change
      IdeleGroup.infiniteComponent w
          (a * (IdeleGroup.principalIdele K x)⁻¹) ∈
        infiniteTensorNormSubgroup
          (K := K) (L := E) w
    rw [map_mul, map_inv]
    exact hinfinite w
  have hFinite :
      ∀ v : HeightOneSpectrum (𝓞 K),
        IdeleGroup.finiteComponent v b ∈
          (_root_.localTensorNorm
            (K := K) (L := E) v).range := by
    intro v
    rw [
      finitePlaceLocalTensorNorm_range_eq_chosenLocalNormSubgroup
        (K := K) (L := E) v]
    simpa [b] using hfinite v
  have hb :
      b ∈ (RelativeIdeleGroup.norm K E).range :=
    (mem_relativeIdeleNorm_range_iff_localTensorNorms
      (K := K) (L := E) b).2 ⟨hInfinite, hFinite⟩
  obtain ⟨z, hz⟩ := hb
  refine
    ⟨QuotientGroup.mk'
        (RelativeIdeleGroup.principalSubgroup K E) z, ?_⟩
  rw [RelativeIdeleGroup.Cohomology.ideleClassNorm_mk, hz]
  change
    QuotientGroup.mk'
        (IdeleGroup.principalSubgroup K) b =
      QuotientGroup.mk'
        (IdeleGroup.principalSubgroup K) a
  have hp :
      QuotientGroup.mk'
          (IdeleGroup.principalSubgroup K)
          (IdeleGroup.principalIdele K x) = 1 :=
    (QuotientGroup.eq_one_iff
      (IdeleGroup.principalIdele K x)).2 ⟨x, rfl⟩
  change
    QuotientGroup.mk'
        (IdeleGroup.principalSubgroup K)
        (a * (IdeleGroup.principalIdele K x)⁻¹) =
      QuotientGroup.mk'
        (IdeleGroup.principalSubgroup K) a
  rw [map_mul, map_inv, hp]
  exact
    mul_one
      (QuotientGroup.mk'
        (IdeleGroup.principalSubgroup K) a)

/-- The preceding surjectivity says that the idele-class norm index is
one. -/
theorem ideleClassNorm_index_eq_one_of_splitsCompletely_outside
    {E : Type}
    [Field E] [NumberField E] [Algebra K E]
    [FiniteDimensional K E] [IsGalois K E]
    (S : Finset (HeightOneSpectrum (𝓞 K)))
    (hsplit :
      ∀ v : HeightOneSpectrum (𝓞 K), v ∉ S →
        FinitePlaceSplitsCompletely
          (K := K) (L := E) v) :
    (RelativeIdeleGroup.Cohomology.ideleClassNorm K E).range.index = 1 := by
  rw [
    ideleClassNorm_range_eq_top_of_splitsCompletely_outside
      (K := K) (E := E) S hsplit,
    Subgroup.index_top]

/-- Assuming the norm-index lower bound for the chosen prime-degree
subextension, the set of finite places whose decomposition group is the
whole Galois group is infinite. -/
theorem
    cyclic_prime_power_fullDecompositionPlaces_infinite_of_primeSubextension_normIndex
    {p exponent : ℕ}
    (hp : p.Prime)
    (hexponent : 0 < exponent)
    (hcard : Nat.card (L ≃ₐ[K] L) = p ^ exponent)
    (hLower :
      p ≤
        (RelativeIdeleGroup.Cohomology.ideleClassNorm K
          (cyclicPrimeSubextension
            (K := K) (L := L)
            hp hexponent hcard)).range.index) :
    Set.Infinite
      {v : HeightOneSpectrum (𝓞 K) |
        finitePlaceDecompositionGroup
            (K := K) (L := L) v = ⊤} := by
  intro hfinite
  let S : Finset (HeightOneSpectrum (𝓞 K)) :=
    hfinite.toFinset
  have hsplit :
      ∀ v : HeightOneSpectrum (𝓞 K), v ∉ S →
        FinitePlaceSplitsCompletely
          (K := K)
          (L := cyclicPrimeSubextension
            (K := K) (L := L)
            hp hexponent hcard) v := by
    intro v hv
    apply
      finitePlaceSplitsCompletely_in_cyclicPrimeSubextension_of_decompositionGroup_ne_top
        (K := K) (L := L)
        hp hexponent hcard v
    intro htop
    apply hv
    simp [S, htop]
  have hindex :
      (RelativeIdeleGroup.Cohomology.ideleClassNorm K
        (cyclicPrimeSubextension
          (K := K) (L := L)
          hp hexponent hcard)).range.index = 1 :=
    ideleClassNorm_index_eq_one_of_splitsCompletely_outside
      (K := K)
      (E := cyclicPrimeSubextension
        (K := K) (L := L)
        hp hexponent hcard)
      S hsplit
  have hp_le_one : p ≤ 1 := by
    simpa [hindex] using hLower
  exact (Nat.not_lt_of_ge hp_le_one) hp.one_lt

end Cohomology
end GlobalClassFieldTheory
end
end

section
-- module Solutions.OAIQ244_DUKE.GlobalClassFieldTheory_ClassFieldAxiom_SUnitKummerPrimeSelection_BasePlaceSelection
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.infinitePlaceComplexificationOverfield_algebra _root_.GlobalClassFieldTheory.Reciprocity.infinitePlaceComplexificationOverfield_baseAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.KummerTheory.primeCyclotomicBaseFiniteDimensional _root_.LocalClassFieldTheory.finiteGaloisLocalField_integerRing_moduleFinite _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.residueFieldZModAlgebra _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedIntegralAlgebraContextValuationSubringAlgebra _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedIntegralAlgebraContextValuationSubringTower _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedQPadicContextValuationSubringTower _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.diagonalLogAction _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.LocalClassFieldTheory.comparisonIntegerRingIsIntegralClosure _root_.LocalClassFieldTheory.normalizationIntegerRingIsIntegralClosure
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

/-- Base finite places lying below a full-decomposition place for the
cyclic coordinate extension `N/N_i`. -/
noncomputable def sUnitKummerCoordinateBasePlaceCandidates
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
    Set (HeightOneSpectrum (𝓞 K)) := by
  let S' :=
    enlargeByFiniteKummerRadicalSupport
      (K := K) (L := E) n hmu S
  let N :=
    fullSUnitKummerExtension
      (K := K) (Omega := Omega) n S'
  have hnK : ((n : ℕ) : K) ≠ 0 := by
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
  let _ : IsGalois Ni N :=
    enlargedSUnitKummerCyclicFixedField_isGalois
      (K := K) (Omega := Omega) E n hmu
      (galois_pow_eq_one_of_equiv_pi_zmod
        (K := K) E n r eG) S
      (sUnitKummerKernelGenerator
        (K := K) (Omega := Omega) E n hmu
        p v hp hv hn r eG S i)
  exact
    {w | ∃ q : HeightOneSpectrum (𝓞 Ni),
      _root_.finitePlaceBelow (K := K) q = w ∧
      _root_.finitePlaceDecompositionGroup
        (K := Ni) (L := N) q = ⊤}

end FinitePlaces

end GlobalClassFieldTheory.ClassFieldAxiom
end
end


