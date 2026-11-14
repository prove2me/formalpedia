-- Prove2me | Definitions.Def_OAIQ244Duke064
-- name    : OAIQ244Duke064
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-13T22:35:21.337797+00:00
-- url     : https://prove2.me/theorems/7f7030f0-0cbc-4aa1-8657-97e5f082db8e
-- title:
--   Definitions bundle OAIQ244Duke064 of the split of OpenAI, Equidistribution of Prime-Degree Torus Packets with Arbitrary Local Type
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.DukePrimeDegree.prime_degree_packet_measure_equidistribution_unconditional` and `OAI.DukePrimeDegree.prime_degree_packet_measures_tendsto_haar_unconditional`, carved from OpenAI's openai/math development (OpenAI, *Equidistribution of Prime-Degree Torus Packets with Arbitrary Local Type*, OpenAI Math Release, September 24, 2026, result family 15, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 40 declarations of OpenAI's Lean: 3 definitions and 37 theorems. The definitions and types are `GlobalClassFieldTheory.GlobalClassFields.ConductorialSubgroup.fullConductorInfinitePart`, `GlobalClassFieldTheory.GlobalClassFields.ConductorialSubgroup.narrowFiniteLocalConductorExponent`, `relativeLocalTensorDecompositionIntegralUnitSubgroupEquivInducedIntegerUnits`.
--
--   **Sources.** They come from these modules of lean/OAI/NumberTheory, in whole or in part: `AlgebraicNumberTheory_Completion_UnramifiedComparison_IdealToCompletion`, `AlgebraicNumberTheory_Idele_ClassGroup_AlgEquiv`, `AlgebraicNumberTheory_Idele_Cohomology_SPlaces_Herbrand_Factors`, `AlgebraicNumberTheory_Idele_Cohomology_SPlaces_Herbrand_FamilyCardinality`, `AlgebraicNumberTheory_Idele_Cohomology_SPlaces_Herbrand_Local`, `AlgebraicNumberTheory_Idele_Cohomology_SPlaces_OutsideIntegralInduced_ChosenPlaceIntegralBlock`, `AlgebraicNumberTheory_Idele_Cohomology_SPlaces_OutsideIntegralInduced_ChosenPlaceIntegralBlockEquiv`, `AlgebraicNumberTheory_Idele_Cohomology_SPlaces_OutsideIntegralInduced_ChosenPlaceIntegralBlockEquivApply`, `AlgebraicNumberTheory_Idele_Cohomology_SPlaces_OutsideIntegralInduced_ChosenPlaceIntegralBlockInducedSmul`, `AlgebraicNumberTheory_Idele_Relative_FinitePlaceTensorNorm`, `AlgebraicNumberTheory_Ramification_Splitting_FinitePlaceIdeal`, `AlgebraicNumberTheory_Ramification_Splitting_NormalClosure`, `AlgebraicNumberTheory_RayClass_LocalConductor`, `GlobalClassFieldTheory_ClassFieldAxiom_SUnitKummerPrimeSelection_BasePlaceSelection`, `GlobalClassFieldTheory_GlobalClassFields_ConductorInfinitePart`, `GlobalClassFieldTheory_GlobalClassFields_ConductorLattice`, `GlobalClassFieldTheory_GlobalClassFields_ConductorLocalComparison`, `KummerTheory_Concrete_SUnitPreparation_EnlargedSUnitRestriction`, `KummerTheory_Concrete_SimpleExtensionLocalBehavior`, `LocalClassFieldTheory_Finite_Unramified_Cohomology`, `LocalField_DiscreteValuationField_PadicPowerIndex`, `LocalField_DiscreteValuationField_PowerIndex`.
--
--   **Imports.** It imports the bundles `OAIQ244Duke054`, `OAIQ244Duke055`, `OAIQ244Duke056`, `OAIQ244Duke057`, `OAIQ244Duke058` and `OAIQ244Duke059` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ244Duke069`, `OAIQ244Duke070`, `OAIQ244Duke072` and `OAIQ244Duke073`.
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
import Definitions.Def_OAIQ244Duke054
import Definitions.Def_OAIQ244Duke055
import Definitions.Def_OAIQ244Duke056
import Definitions.Def_OAIQ244Duke057
import Definitions.Def_OAIQ244Duke058
import Definitions.Def_OAIQ244Duke059

section
-- module Solutions.OAIQ244_DUKE.AlgebraicNumberTheory_Idele_Relative_FinitePlaceTensorNorm
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.GlobalClassFields.ConductorialSubgroup.finiteIndex _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalClassFieldTheory.finiteGaloisLocalField_integerRing_moduleFinite _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.residueFieldZModAlgebra _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedIntegralAlgebraContextValuationSubringAlgebra _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.LocalClassFieldTheory.comparisonIntegerRingIsIntegralClosure _root_.LocalClassFieldTheory.normalizationIntegerRingIsIntegralClosure _root_.chosenFinitePlaceCompletionAlgebra
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

/-!
# Tensor norm images at actual finite places

This file specializes the local tensor norm calculation to a height-one
prime of a number field.  The canonical comparison

`(K, |·|_v)^∧ ≃ K_v`

identifies the determinant norm on
`(K, |·|_v)^∧ ⊗[K] L` with the determinant norm on the concrete tensor
factor `K_v ⊗[K] L` used by relative ideles.  Consequently its image is
the chosen open local norm subgroup from `LocalNormApproximation`.

The finite component of every global relative-idele norm therefore lies
in that subgroup, and its corresponding local quotient class is one.
-/

open scoped NumberField TensorProduct
open NumberField IsDedekindDomain

noncomputable section

open LocalClassFieldTheory


open AlgebraicNumberTheory.Valuations
open LocalFieldTheory

variable {K L : Type}
    [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]

omit [NumberField L] in
/-- Every finite component of a global relative-idele norm lies in the
chosen local norm subgroup. -/
theorem relativeIdeleNorm_finiteComponent_mem_chosenLocalNormSubgroup
    (v : HeightOneSpectrum (𝓞 K))
    (a : RelativeIdeleGroup K L) :
    IdeleGroup.finiteComponent v
        (RelativeIdeleGroup.norm K L a) ∈
      chosenFinitePlaceLocalNormSubgroup
        (K := K) (L := L) v := by
  rw [← finitePlaceLocalTensorNorm_range_eq_chosenLocalNormSubgroup
    (K := K) (L := L) v]
  exact
    ⟨RelativeIdeleGroup.finiteComponent
        (K := K) (L := L) v a,
      (RelativeIdeleGroup.finiteComponent_norm
        (K := K) (L := L) v a).symm⟩
end
end

section
-- module Solutions.OAIQ244_DUKE.AlgebraicNumberTheory_Completion_UnramifiedComparison_IdealToCompletion
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.infinitePlaceComplexificationOverfield_algebra _root_.GlobalClassFieldTheory.Reciprocity.infinitePlaceComplexificationOverfield_baseAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalCyclotomicCompletionAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.DiscreteNthRootsSubgroup.instTopologicalSpaceSubtypeUnitsMemSubgroup _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.KummerTheory.primeCyclotomicBaseFiniteDimensional _root_.LocalClassFieldTheory.finiteGaloisLocalField_integerRing_moduleFinite _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitInverseLimitCarrierPadicModule _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitQuotientCarrierPadicModule _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitPadicModule _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitPadicSMul _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.residueFieldZModAlgebra _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedIntegralAlgebraContextValuationSubringAlgebra _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedMaximalIdealPowContextModuleFinite _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedMaximalIdealPowContextModuleFree _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedQPadicContextValuationSubringTower _root_.LocalFieldTheory.DiscreteValuationField.finite_principalUnits_nthPowerKernel _root_.LocalFieldTheory.DiscreteValuationField.finite_residueRootsOfUnityGroup _root_.LocalFieldTheory.DiscreteValuationField.finite_valuationSubringUnits_nthPowerKernel _root_.LocalFieldTheory.DiscreteValuationField.finite_valuationSubringUnits_nthPowerQuotient _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.LubinTate.standardLubinTateLevelCompleteDVF_hasExtensionInstance _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.diagonalLogAction _root_.OAI.PrimeDegreePackets.instIsTopologicalRingLocalAlgebra _root_.OAI.PrimeDegreePackets.instTopologicalSpaceLocalAlgebra _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.RamificationTheory.HilbertRamification.Higher.lowerRamificationGroup.instNormal _root_.LocalClassFieldTheory.comparisonIntegerRingIsIntegralClosure _root_.LocalClassFieldTheory.normalizationIntegerRingIsIntegralClosure _root_.RamificationTheory.HilbertRamification.CompleteDVF.decompositionGroupMulSemiringAction
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

/-!
# From ideal-theoretic to completed unramifiedness

This file proves that ideal-theoretic unramifiedness at the centre of the
actual chosen finite-place extension implies unramifiedness of its localized
completion.
-/

open scoped NumberField Classical NNReal ValuativeRel
open NumberField IsDedekindDomain

noncomputable section

open AlgebraicNumberTheory.Valuations
open LocalClassFieldTheory
open LocalFieldTheory
open LocalFieldTheory.IsNonarchimedeanLocalField

variable
    {K L : Type}
    [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]

/-- If the centre of the chosen finite-place extension has ramification
index one, a global integral uniformizer remains a uniformizer after passing
to the chosen localized completion. In particular it is not in the square of
the target maximal ideal. -/
theorem chosenFinitePlace_integral_uniformizer_not_mem_maximalIdeal_sq
    (v : HeightOneSpectrum (𝓞 K))
    (π : 𝓞 K)
    (πBase :
      𝒪[ChosenFinitePlaceBaseCompletion (K := K) v])
    (hπ :
      v.intValuation π = WithZero.exp (-1 : ℤ))
    (hπBase :
      (πBase :
          ChosenFinitePlaceBaseCompletion (K := K) v) =
        algebraMap K
          (ChosenFinitePlaceBaseCompletion (K := K) v)
          (π : K))
    (hglobal :
      v.asIdeal.ramificationIdx'
          (finitePlaceExtensionCentre
            (K := K) (L := L) v
            (chosenFinitePlaceExtension (L := L) v)).asIdeal =
        1) :
    algebraMap
        𝒪[ChosenFinitePlaceBaseCompletion (K := K) v]
        𝒪[ChosenFinitePlaceLocalizedCompletion
          (K := K) (L := L) v] πBase ∉
      (𝓂[ChosenFinitePlaceLocalizedCompletion
        (K := K) (L := L) v] :
          Ideal
            𝒪[ChosenFinitePlaceLocalizedCompletion
              (K := K) (L := L) v]) ^ 2 := by
  let vK := HeightOneSpectrum.adicAbv K v
  let w := chosenFinitePlaceExtension (L := L) v
  let W :=
    finitePlaceExtensionCentre
      (K := K) (L := L) v w
  let : W.asIdeal.LiesOver v.asIdeal :=
    finitePlaceExtensionCentre_liesOver
      (K := K) (L := L) v w
  let E :=
    ChosenFinitePlaceLocalizedCompletion
      (K := K) (L := L) v
  let eTarget :
      𝒪[E] ≃+* W.adicCompletionIntegers L :=
    chosenFinitePlaceLocalizedIntegerRingEquiv
      (K := K) (L := L) v
  let πTarget : 𝒪[E] :=
    algebraMap 𝒪[vK.Completion] 𝒪[E] πBase
  change πTarget ∉
    (IsLocalRing.maximalIdeal 𝒪[E]) ^ 2
  intro hπTargetDeep
  have hπTargetConcrete :
      eTarget πTarget ∈
        (IsLocalRing.maximalIdeal
          (W.adicCompletionIntegers L)) ^ 2 :=
    (ValuationTheory.ringEquiv_mem_maximalIdeal_pow_iff
      eTarget 2 πTarget).2 hπTargetDeep
  have hπTargetField :
      (eTarget πTarget : W.adicCompletion L) =
        (algebraMap L (W.adicCompletion L)
          (algebraMap K L (π : K))) := by
    change
      finitePlaceExtensionAdicCompletionRingEquiv
            (K := K) (L := L) v w
            (localizedCompletionEquivCompletion
              vK (RayClass.adicAbv_isNontrivial v) w
              (algebraMap vK.Completion E
                (πBase : vK.Completion))) =
        _
    rw [(localizedCompletionEquivCompletion
      vK (RayClass.adicAbv_isNontrivial v) w).commutes, hπBase]
    change
      finitePlaceExtensionAdicCompletionRingEquiv
            (K := K) (L := L) v w
            (AbsoluteValue.completionMap
              vK w.1 w.2
              (algebraMap K vK.Completion
                (π : K))) =
        _
    rw [AbsoluteValue.completionMap_coe,
      finitePlaceExtensionAdicCompletionRingEquiv_toCompletion]
    rfl
  let targetDVF :
      ValuationTheory.DiscreteValuationField.DVF
        (W.adicCompletion L) :=
    { ValueGroup := WithZero (Multiplicative ℤ)
      valuation := Valued.v }
  have hπTargetValuation :
      targetDVF.valuation
          (eTarget πTarget : W.adicCompletion L) =
        WithZero.exp (-1 : ℤ) := by
    rw [hπTargetField]
    change
      Valued.v
          (algebraMap L (W.adicCompletion L)
            (algebraMap K L (π : K))) =
        WithZero.exp (-1 : ℤ)
    calc
      Valued.v
          (algebraMap L (W.adicCompletion L)
            (algebraMap K L (π : K))) =
          W.valuation L (algebraMap K L (π : K)) :=
        HeightOneSpectrum.valuedAdicCompletion_eq_valuation'
          W (algebraMap K L (π : K))
      _ =
          (v.valuation K (π : K)) ^
            v.asIdeal.ramificationIdx' W.asIdeal := by
        symm
        exact HeightOneSpectrum.valuation_liesOver
          L v W (π : K)
      _ = WithZero.exp (-1 : ℤ) := by
        rw [hglobal, pow_one,
          HeightOneSpectrum.valuation_of_algebraMap, hπ]
  have hπTargetUniformizer :
      targetDVF.valuation.IsUniformizer
        (eTarget πTarget : W.adicCompletion L) := by
    rw [Valuation.IsUniformizer.iff,
      Valuation.IsRankOneDiscrete.generator_eq_exp_neg_one_of_surjective
        (W.valuedAdicCompletion_surjective L)]
    exact hπTargetValuation
  exact
    (targetDVF.uniformizer_not_mem_maximalIdeal_sq
      hπTargetUniformizer) hπTargetConcrete

/-- Ramification index one at the global centre prevents the image of the
completed base maximal ideal from lying in the square of the target maximal
ideal. -/
theorem chosenFinitePlace_maximalIdeal_map_not_le_sq_of_centre_ramificationIdx_eq_one
    (v : HeightOneSpectrum (𝓞 K))
    (hglobal :
      v.asIdeal.ramificationIdx'
          (finitePlaceExtensionCentre
            (K := K) (L := L) v
            (chosenFinitePlaceExtension (L := L) v)).asIdeal =
        1) :
    ¬ (𝓂[ChosenFinitePlaceBaseCompletion (K := K) v] :
          Ideal
            𝒪[ChosenFinitePlaceBaseCompletion (K := K) v]).map
        (algebraMap
          𝒪[ChosenFinitePlaceBaseCompletion (K := K) v]
          𝒪[ChosenFinitePlaceLocalizedCompletion
            (K := K) (L := L) v]) ≤
      (𝓂[ChosenFinitePlaceLocalizedCompletion
        (K := K) (L := L) v] :
          Ideal
            𝒪[ChosenFinitePlaceLocalizedCompletion
              (K := K) (L := L) v]) ^ 2 := by
  let πData :=
    chosenFinitePlaceCompletionIntegralUniformizer v
  intro hdeep
  apply
    chosenFinitePlace_integral_uniformizer_not_mem_maximalIdeal_sq
      (K := K) (L := L) v
      πData.integer πData.completionInteger
      πData.intValuation_eq_exp_neg_one
      πData.coe_completionInteger hglobal
  exact
    hdeep
      (Ideal.mem_map_of_mem
        (algebraMap
          𝒪[ChosenFinitePlaceBaseCompletion (K := K) v]
          𝒪[ChosenFinitePlaceLocalizedCompletion
            (K := K) (L := L) v])
        πData.completionInteger_mem_maximalIdeal)

/-- Ramification index one at the global centre gives ramification index one
for the completed maximal ideals in the multiplicity formulation. -/
theorem chosenFinitePlace_maximalIdeal_ramificationIdx'_eq_one_of_centre_ramificationIdx_eq_one
    (v : HeightOneSpectrum (𝓞 K))
    (hglobal :
      v.asIdeal.ramificationIdx'
          (finitePlaceExtensionCentre
            (K := K) (L := L) v
            (chosenFinitePlaceExtension (L := L) v)).asIdeal =
        1) :
    (𝓂[ChosenFinitePlaceBaseCompletion (K := K) v] :
        Ideal
          𝒪[ChosenFinitePlaceBaseCompletion (K := K) v]).ramificationIdx'
      (𝓂[ChosenFinitePlaceLocalizedCompletion
        (K := K) (L := L) v] :
          Ideal
            𝒪[ChosenFinitePlaceLocalizedCompletion
              (K := K) (L := L) v]) =
      1 := by
  let vK := HeightOneSpectrum.adicAbv K v
  let E :=
    ChosenFinitePlaceLocalizedCompletion
      (K := K) (L := L) v
  change
    (𝓂[vK.Completion] :
        Ideal 𝒪[vK.Completion]).ramificationIdx'
      (𝓂[E] : Ideal 𝒪[E]) = 1
  let :
      IsLocalHom (algebraMap vK.Completion E) :=
    IsLocalRing.instIsLocalHomRingHomOfNontrivial
      (algebraMap vK.Completion E)
  let :
      IsLocalHom
        (algebraMap 𝒪[vK.Completion] 𝒪[E]) :=
    Valuation.HasExtension.instIsLocalHomValuationInteger
  rw [← not_ne_iff,
    Ideal.ramificationIdx'_ne_one_iff
      (IsLocalRing.map_maximalIdeal_le
        (algebraMap 𝒪[vK.Completion] 𝒪[E]))]
  exact
    chosenFinitePlace_maximalIdeal_map_not_le_sq_of_centre_ramificationIdx_eq_one
      (K := K) (L := L) v hglobal

/-- Ramification index one at the actual global centre gives ramification
index one for the maximal ideals of the corresponding completed valued-field
extension. -/
theorem chosenFinitePlace_maximalIdeal_ramificationIdx_eq_one_of_centre_ramificationIdx_eq_one
    (v : HeightOneSpectrum (𝓞 K))
    (hglobal :
      v.asIdeal.ramificationIdx'
          (finitePlaceExtensionCentre
            (K := K) (L := L) v
            (chosenFinitePlaceExtension (L := L) v)).asIdeal =
        1) :
    (𝓂[ChosenFinitePlaceLocalizedCompletion
        (K := K) (L := L) v] :
          Ideal
            𝒪[ChosenFinitePlaceLocalizedCompletion
              (K := K) (L := L) v]).ramificationIdx
        𝒪[ChosenFinitePlaceBaseCompletion (K := K) v] =
      1 := by
  let vK := HeightOneSpectrum.adicAbv K v
  let E :=
    ChosenFinitePlaceLocalizedCompletion
      (K := K) (L := L) v
  change
    (𝓂[E] : Ideal 𝒪[E]).ramificationIdx
      𝒪[vK.Completion] = 1
  have hbaseBot :
      (𝓂[vK.Completion] : Ideal 𝒪[vK.Completion]) ≠ ⊥ :=
    Ring.ne_bot_of_isMaximal_of_not_isField
      (IsLocalRing.maximalIdeal.isMaximal
        𝒪[vK.Completion])
      (IsDiscreteValuationRing.not_isField
        𝒪[vK.Completion])
  let :
      Module.IsTorsionFree vK.Completion E :=
    DivisionSemiring.to_moduleIsTorsionFree
  let :
      Module.IsTorsionFree
        𝒪[vK.Completion] 𝒪[E] :=
    Valuation.HasExtension.instIsTorsionFreeInteger
  let :
      (𝓂[E] : Ideal 𝒪[E]).LiesOver
        (𝓂[vK.Completion] : Ideal 𝒪[vK.Completion]) := by
    exact
      ⟨(Valuation.HasExtension.maximalIdeal_comap_algebraMap_eq_maximalIdeal
        (ValuativeRel.valuation vK.Completion)
        (ValuativeRel.valuation E)).symm⟩
  rw [← Ideal.ramificationIdx'_eq_ramificationIdx
    (𝓂[vK.Completion] : Ideal 𝒪[vK.Completion])
    (𝓂[E] : Ideal 𝒪[E]) hbaseBot]
  exact
    chosenFinitePlace_maximalIdeal_ramificationIdx'_eq_one_of_centre_ramificationIdx_eq_one
      (K := K) (L := L) v hglobal

/-- Ramification index one at the actual global centre implies
unramifiedness of the corresponding completed valued-field extension. -/
theorem chosenFinitePlaceIsUnramified_of_centre_ramificationIdx_eq_one
    (v : HeightOneSpectrum (𝓞 K))
    (hglobal :
      v.asIdeal.ramificationIdx'
          (finitePlaceExtensionCentre
            (K := K) (L := L) v
            (chosenFinitePlaceExtension (L := L) v)).asIdeal =
        1) :
    ChosenFinitePlaceIsUnramified
      (K := K) (L := L) v := by
  change
    IsNonarchimedeanLocalField.IsUnramifiedValuedExtension
      (ChosenFinitePlaceBaseCompletion (K := K) v)
      (ChosenFinitePlaceLocalizedCompletion
        (K := K) (L := L) v)
  refine
    { maximalIdeal_ramificationIdx_eq_one := ?_ }
  exact
    chosenFinitePlace_maximalIdeal_ramificationIdx_eq_one_of_centre_ramificationIdx_eq_one
      (K := K) (L := L) v hglobal

/-- Algebraic unramifiedness of the centre of the chosen extension
implies unramifiedness of the corresponding completed valued-field
extension. -/
theorem chosenFinitePlaceIsUnramified_of_isUnramifiedAt
    (v : HeightOneSpectrum (𝓞 K))
    (hunram :
      Algebra.IsUnramifiedAt (𝓞 K)
        (finitePlaceExtensionCentre
          (K := K) (L := L) v
          (chosenFinitePlaceExtension (L := L) v)).asIdeal) :
    ChosenFinitePlaceIsUnramified
      (K := K) (L := L) v := by
  apply
    chosenFinitePlaceIsUnramified_of_centre_ramificationIdx_eq_one
      (K := K) (L := L) v
  exact
    finitePlaceExtensionCentre_ramificationIdx_eq_one_of_isUnramifiedAt
      (K := K) (L := L) v hunram
end
end

section
-- module Solutions.OAIQ244_DUKE.AlgebraicNumberTheory_Idele_ClassGroup_AlgEquiv
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.GlobalClassFields.ConductorialSubgroup.finiteIndex _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalClassFieldTheory.finiteGaloisLocalField_integerRing_moduleFinite _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.residueFieldZModAlgebra _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedIntegralAlgebraContextValuationSubringAlgebra _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.CyclicCohomology.binaryCoefficientFamilyCommGroup _root_.LocalClassFieldTheory.comparisonIntegerRingIsIntegralClosure _root_.LocalClassFieldTheory.normalizationIntegerRingIsIntegralClosure _root_.chosenFinitePlaceCompletionAlgebra _root_.relativeUnrestrictedSPlaceFactorCommGroup
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI
attribute [local instance] OAI.starSubalgebraCommCStarAlgebra

set_option autoImplicit false

/-!
# Relative idele classes under an isomorphic realization

If two finite extensions of a number field are isomorphic over the base,
their tensor-product presentations of the relative adeles are canonically
isomorphic.  This file descends that canonical isomorphism to relative
ideles and idele classes and records compatibility with the determinant
norm.

The construction is the direct tensor-product congruence

`𝔸_K ⊗[K] L ≃ 𝔸_K ⊗[K] M`

induced by an algebra equivalence `L ≃ₐ[K] M`.  In particular, no second
model of relative adeles or of the idele-class norm is introduced.
-/

open scoped NumberField TensorProduct
open NumberField
open IsDedekindDomain

noncomputable section

open RelativeIdeleGroup.Cohomology


universe u v w

variable
    {K : Type u} {L : Type v} {M : Type w}
    [Field K] [NumberField K]
    [Field L] [Algebra K L]
    [Field M] [Algebra K M]

section Norm

variable [FiniteDimensional K L] [FiniteDimensional K M]

/-- Isomorphic realizations of a finite extension have the same actual
idele-class norm subgroup in the base idele class group. -/
theorem ideleClassNorm_range_algEquiv
    (e : L ≃ₐ[K] M) :
    (RelativeIdeleGroup.classNorm K M).range =
      (RelativeIdeleGroup.classNorm K L).range := by
  ext c
  constructor
  · rintro ⟨d, rfl⟩
    refine
      ⟨(relativeIdeleClassCongr
          (K := K) e).symm d, ?_⟩
    have h :=
      relativeIdeleClassCongr_ideleClassNorm
        (K := K) e
        ((relativeIdeleClassCongr
          (K := K) e).symm d)
    rw [MulEquiv.apply_symm_apply] at h
    exact h.symm
  · rintro ⟨d, rfl⟩
    exact
      ⟨relativeIdeleClassCongr (K := K) e d,
        relativeIdeleClassCongr_ideleClassNorm
          (K := K) e d⟩

/-- The idele-class norm index is invariant under an isomorphic realization
of the top field. -/
theorem ideleClassNorm_index_algEquiv
    (e : L ≃ₐ[K] M) :
    (RelativeIdeleGroup.classNorm K M).range.index =
      (RelativeIdeleGroup.classNorm K L).range.index := by
  rw [ideleClassNorm_range_algEquiv
    (K := K) e]

end Norm
end
end

section
-- module Solutions.OAIQ244_DUKE.LocalClassFieldTheory_Finite_Unramified_Cohomology
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.infinitePlaceComplexificationOverfield_baseSmul _root_.GlobalClassFieldTheory.Reciprocity.infinitePlaceComplexificationOverfield_smul _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.DiscreteNthRootsSubgroup.instCommGroupSubtypeUnitsMemSubgroup _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalClassFieldTheory.finiteGaloisLocalField_integerRing_moduleFinite _root_.LocalClassFieldTheory.localDecompositionResidueFinite _root_.LocalClassFieldTheory.localDecompositionResidueFintype _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitQuotientCarrier_finite _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.residueFieldZModAlgebra _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedIntegralAlgebraContextValuationSubringAlgebra _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.LubinTate.compatibleGroupFamiliesCommGroup _root_.LubinTate.compatibleGroupFamiliesGroup _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.boundedRealFields_finite _root_.OAI.PrimeDegreePackets.diagonalLogAction _root_.OAI.PrimeDegreePackets.instTopologicalSpaceLocalAlgebra _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RamificationTheory.HilbertRamification.ValuationSubring.selectedResidueField.instAlgebra _root_.RayClass.approximationCompletionTopologicalSpace _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.RelativeIdeleGroup.relativeIdeleMulAction _root_.CyclicCohomology.binaryCoefficientFamilyCommGroup _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.LocalClassFieldTheory.comparisonIntegerRingIsIntegralClosure _root_.LocalClassFieldTheory.normalizationIntegerRingIsIntegralClosure _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.chosenFinitePlaceCompletionAlgebra _root_.finiteLocalUnitsOpen _root_.infiniteAdeleRingT2Space _root_.relativeAdeleRingIntermediateAlgebra _root_.relativeAdeleRingTopIntermediateAlgebra _root_.relativeUnrestrictedSPlaceFactorCommGroup
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

/-- The unramified unit-cohomology theorem for the actual `n`-th principal-unit module.  The proof
uses the actual sequence `1 → U_L^n → 𝒪_Lˣ → 𝒪_Lˣ/U_L^n → 1`,
Herbrand-quotient multiplicativity, and the actual unramified norm lifting. -/
theorem unramified_principalUnits_herbrand_subsingleton
    (K L : Type) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    [ValuativeRel L] [UniformSpace L] [IsUniformAddGroup L]
    [IsNonarchimedeanLocalField L]
    [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]
    [IsIntegralClosure 𝒪[L] 𝒪[K] L] [Module.Finite 𝒪[K] 𝒪[L]]
    [IsUnramifiedValuedExtension K L]
    (n : Nat) (hn : 1 ≤ n) (g : Gal(L / K))
    (hg : ∀ sigma : Gal(L / K), sigma ∈ Subgroup.zpowers g) :
    letI := galoisGroupPrincipalUnitsMulDistribMulActionOfIsIntegralClosure K L n
    Subsingleton (HerbrandH0 Gal(L / K) (principalUnits L n)) ∧
      Subsingleton
        (HerbrandHMinusOne Gal(L / K) (principalUnits L n) g) := by
  let := galoisGroupPrincipalUnitsMulDistribMulActionOfIsIntegralClosure K L n
  let := galoisGroupIntegerUnitsMulDistribMulActionOfIsIntegralClosure K L
  let := galoisGroupIntegerUnitsModPrincipalUnitsMulDistribMulActionOfIsIntegralClosure
    K L n
  rcases integerUnits_herbrandQuotient_eq_one K L g hg with
    ⟨hU, hUone⟩
  let : Finite (IntegerUnitsModPrincipalUnitsAtLevel L n) :=
    integerUnitsModPrincipalUnitsAtLevel_finite_of_isNonarchimedeanLocalField L n
  let hQ : HerbrandQuotientDefined Gal(L / K)
      (IntegerUnitsModPrincipalUnitsAtLevel L n) g :=
    ⟨inferInstance, inferInstance⟩
  have hQone : herbrandQuotient (G := Gal(L / K))
      (A := IntegerUnitsModPrincipalUnitsAtLevel L n) g = 1 :=
    integerUnitsModPrincipalUnitsAtLevel_herbrandQuotient_eq_one_of_isNonarchimedeanLocalField
      K L n g hg
  let hseq := principalUnitsIntegerUnits_shortExact K L n
  let hP : HerbrandQuotientDefined Gal(L / K) (principalUnits L n) g :=
    herbrandQuotientDefined_left_of_middle_right
      (G := Gal(L / K)) (A := principalUnits L n) (B := 𝒪[L]ˣ)
      (C := IntegerUnitsModPrincipalUnitsAtLevel L n)
      (principalUnitsIntegerUnitsInclusion L n)
      (integerUnitsPrincipalUnitsQuotientMap L n)
      hseq.1 hseq.2.1 hseq.2.2.1 hseq.2.2.2.1 hseq.2.2.2.2
      g hg hU hQ
  let : Finite (HerbrandH0 Gal(L / K) 𝒪[L]ˣ) := hU.1
  let : Finite (HerbrandHMinusOne Gal(L / K) 𝒪[L]ˣ g) := hU.2
  let : Finite (HerbrandH0 Gal(L / K)
      (IntegerUnitsModPrincipalUnitsAtLevel L n)) := hQ.1
  let : Finite (HerbrandHMinusOne Gal(L / K)
      (IntegerUnitsModPrincipalUnitsAtLevel L n) g) := hQ.2
  let : Finite (HerbrandH0 Gal(L / K) (principalUnits L n)) := hP.1
  let : Finite (HerbrandHMinusOne Gal(L / K)
      (principalUnits L n) g) := hP.2
  have hPone : herbrandQuotient (G := Gal(L / K))
      (A := principalUnits L n) g = 1 := by
    have hmul := herbrandQuotient_multiplicative_of_shortExact
      (G := Gal(L / K)) (A := principalUnits L n) (B := 𝒪[L]ˣ)
      (C := IntegerUnitsModPrincipalUnitsAtLevel L n)
      (principalUnitsIntegerUnitsInclusion L n)
      (integerUnitsPrincipalUnitsQuotientMap L n)
      hseq.1 hseq.2.1 hseq.2.2.1 hseq.2.2.2.1 hseq.2.2.2.2 g hg
    rw [hUone, hQone, mul_one] at hmul
    exact hmul.symm
  have hfixed : fixedSubgroup Gal(L / K) (principalUnits L n) ≤
      tateNormSubgroup Gal(L / K) (principalUnits L n) := by
    intro a ha
    have haUnits : ∀ sigma : Gal(L / K),
        letI := galoisGroupIntegerUnitsMulDistribMulActionOfIsIntegralClosure K L
        sigma • ((a : principalUnits L n) : 𝒪[L]ˣ) =
          ((a : principalUnits L n) : 𝒪[L]ˣ) := by
      intro sigma
      exact congrArg (fun z : principalUnits L n => (z : 𝒪[L]ˣ)) (ha sigma)
    rcases exists_integerUnit_map_eq_of_galoisGroup_fixed K L (a : 𝒪[L]ˣ) haUnits with
      ⟨b, hb⟩
    have hbmem : b ∈ principalUnits K n :=
      principalUnits_of_integerUnitsMap_mem_principalUnits_of_unramifiedValuation
        K L n (by rw [hb]; exact a.2)
    let bP : principalUnits K n := ⟨b, hbmem⟩
    rcases principalUnitsNormOfUnramifiedValuationOfIsIntegralClosure_surjective
        K L n hn bP with ⟨z, hz⟩
    have hmap : principalUnitsMapOfUnramifiedValuation K L n bP = a := by
      apply Subtype.ext
      exact hb
    refine ⟨z, ?_⟩
    calc
      tateNorm Gal(L / K) (principalUnits L n) z =
          Finset.univ.prod (fun sigma : Gal(L / K) =>
            galoisGroupPrincipalUnitsMapEquivOfIsIntegralClosure K L n sigma z) := rfl
      _ = principalUnitsNormExtensionSideOfIsIntegralClosure K L n z :=
        (principalUnitsNormExtensionSideOfIsIntegralClosure_eq_galoisGroup_prod
          K L n z).symm
      _ = principalUnitsMapOfUnramifiedValuation K L n
          (principalUnitsNormOfUnramifiedValuationOfIsIntegralClosure K L n z) :=
        (principalUnitsMap_normOfUnramifiedValuationOfIsIntegralClosure_eq_normExtensionSide
          K L n z).symm
      _ = principalUnitsMapOfUnramifiedValuation K L n bP := by rw [hz]
      _ = a := hmap
  let : Subsingleton
      (HerbrandH0 Gal(L / K) (principalUnits L n)) :=
    herbrandH0_subsingleton_of_fixed_le_tateNormSubgroup hfixed
  exact ⟨inferInstance,
    herbrandHMinusOne_subsingleton_of_h0_subsingleton_of_quotient_eq_one
      Gal(L / K) (principalUnits L n) g hPone⟩

end LocalClassFieldTheory
end
end

section
-- module Solutions.OAIQ244_DUKE.AlgebraicNumberTheory_Idele_Cohomology_SPlaces_Herbrand_Local
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalCyclotomicCompletionAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalClassFieldTheory.finiteGaloisLocalField_integerRing_moduleFinite _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitQuotientCarrier_finite _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.residueFieldZModAlgebra _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedIntegralAlgebraContextValuationSubringAlgebra _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedQPadicContextValuationSubringTower _root_.LocalFieldTheory.DiscreteValuationField.finite_nsmulAddKernel_padicInt_pi _root_.LocalFieldTheory.DiscreteValuationField.finite_principalUnits_nthPowerKernel _root_.LocalFieldTheory.DiscreteValuationField.finite_residueRootsOfUnityGroup _root_.LocalFieldTheory.DiscreteValuationField.finite_valuationSubringUnits_nthPowerKernel _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_multiplicative_nthPowerKernel _root_.LocalFieldTheory.finite_nsmulAddKernel_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.LubinTate.compatibleGroupFamiliesGroup _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.boundedRealFields_finite _root_.OAI.PrimeDegreePackets.diagonalLogAction _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.CyclicCohomology.binaryCoefficientFamilyCommGroup _root_.LocalClassFieldTheory.comparisonIntegerRingIsIntegralClosure _root_.LocalClassFieldTheory.normalizationIntegerRingIsIntegralClosure
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

/-!
# Cohomology of the unrestricted factors of a relative `S`-idele

This file combines finite local class field theory with the explicit
real/complex norm calculation.  It treats the finite family consisting
of all infinite places and the finite places in `S`.
-/

open scoped NumberField BigOperators ValuativeRel Classical NNReal
open NumberField IsDedekindDomain

noncomputable section


open AlgebraicNumberTheory.Valuations
open CyclicCohomology.ProfiniteCohomology.Herbrand
open CyclicCohomology
open HilbertRamification
open LocalClassFieldTheory
open LocalFieldTheory

variable {K L : Type}
    [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]

omit [NumberField L] in
/-- The cardinality of one local degree-zero term is its local degree. -/
theorem relativeUnrestrictedLocalHerbrandH0_card_eq_localDegree
    (S : Finset (HeightOneSpectrum (𝓞 K)))
    (i : RelativeUnrestrictedSPlaceIndex (K := K) S)
    (σ : L ≃ₐ[K] L)
    (hgen : ∀ τ : L ≃ₐ[K] L,
      τ ∈ Subgroup.zpowers σ) :
    let d :=
      relativeUnrestrictedSPlaceDatum
        (K := K) (L := L) S
    letI : Fintype
        (absoluteValueDecompositionGroup K (d i).extension.1) :=
      Fintype.ofFinite _
    letI : MulDistribMulAction
        (absoluteValueDecompositionGroup K (d i).extension.1)
        (LocalizedCompletion
          (d i).base (d i).extension)ˣ :=
      decompositionGroupLocalUnitsAction
        (d i).base (d i).base_isNontrivial
        (d i).extension
    letI : Finite
        (HerbrandH0
          (absoluteValueDecompositionGroup K
            (d i).extension.1)
          (LocalizedCompletion
            (d i).base (d i).extension)ˣ) :=
      relativeUnrestrictedLocalHerbrandH0Finite
        S i σ hgen
    Nat.card
        (HerbrandH0
          (absoluteValueDecompositionGroup K
            (d i).extension.1)
          (LocalizedCompletion
            (d i).base (d i).extension)ˣ) =
      relativeUnrestrictedSPlaceLocalDegree
        (K := K) (L := L) S i := by
  cases i with
  | inl v =>
      dsimp only [relativeUnrestrictedSPlaceDatum,
        relativeUnrestrictedSPlaceLocalDegree]
      let w := chosenInfinitePlaceAbove (L := L) v
      let hw := chosenInfinitePlaceAbove_comap
        (L := L) v
      have hcard :=
        infinitePlaceLocalHerbrandH0_card_eq_localDegree
          v (chosenInfinitePlaceAbove (L := L) v)
          (chosenInfinitePlaceAbove_comap
            (L := L) v)
      have hgroup :
          Nat.card (absoluteValueDecompositionGroup K w.1) =
            if w.IsUnramified K then 1 else 2 := by
        rw [absoluteValueDecompositionGroup_eq_infinitePlaceStabilizer w,
          InfinitePlace.card_stabilizer]
      exact hcard.trans hgroup.symm
  | inr v =>
      let vK := HeightOneSpectrum.adicAbv K v.1
      let hvK := RayClass.adicAbv_isNontrivial v.1
      dsimp only [relativeUnrestrictedSPlaceDatum,
        relativeUnrestrictedSPlaceLocalDegree]
      exact
        (localHerbrandH0_card_eq_localDegree
          vK hvK
          (chosenFinitePlaceExtension
            (L := L) v.1)
          σ hgen).trans
        (absoluteValueDecompositionGroup_card_eq_localizedDegree
          (K := K) (L := L)
          vK hvK
          (chosenFinitePlaceExtension
            (L := L) v.1)).symm
end
end

section
-- module Solutions.OAIQ244_DUKE.AlgebraicNumberTheory_Idele_Cohomology_SPlaces_Herbrand_FamilyCardinality
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 400000
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalCyclotomicCompletionAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.DiscreteNthRootsSubgroup.instCommGroupSubtypeUnitsMemSubgroup _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.KummerTheory.nthRootsSubgroupFintype _root_.LocalClassFieldTheory.finiteGaloisLocalField_integerRing_moduleFinite _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitQuotientCarrier_finite _root_.LocalFieldTheory.DiscreteValuationField.finite_nsmulAddKernel_padicInt_pi _root_.LocalFieldTheory.DiscreteValuationField.finite_principalUnits_nthPowerKernel _root_.LocalFieldTheory.DiscreteValuationField.finite_residueRootsOfUnityGroup _root_.LocalFieldTheory.DiscreteValuationField.finite_valuationSubringUnits_nthPowerKernel _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_multiplicative_nthPowerKernel _root_.LocalFieldTheory.finite_nsmulAddKernel_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.LubinTate.compatibleGroupFamiliesCommGroup _root_.LubinTate.compatibleGroupFamiliesGroup _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.boundedRealFields_finite _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.CyclicCohomology.binaryCoefficientFamilyCommGroup _root_.LocalClassFieldTheory.comparisonIntegerRingIsIntegralClosure _root_.LocalClassFieldTheory.normalizationIntegerRingIsIntegralClosure
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

/-!
# Cardinalities of finite unrestricted local-block families

This leaf computes the two finite-family Herbrand cardinalities from the
finiteness results and the canonical family instance providers.
-/

open scoped NumberField BigOperators ValuativeRel Classical NNReal
open NumberField IsDedekindDomain

noncomputable section


open AlgebraicNumberTheory.Valuations
open CyclicCohomology.ProfiniteCohomology.Herbrand
open CyclicCohomology
open HilbertRamification
open LocalClassFieldTheory
open LocalFieldTheory

variable {K L : Type}
    [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]

omit [NumberField L] in
/-- The degree-zero cardinality of the unrestricted local-block family
is the product of its local degrees. -/
theorem
    relativeUnrestrictedLocalBlockFamilyHerbrandH0_card_eq_product
    (S : Finset (HeightOneSpectrum (𝓞 K)))
    (σ : L ≃ₐ[K] L)
    (hgen : ∀ τ : L ≃ₐ[K] L,
      τ ∈ Subgroup.zpowers σ) :
    let d :=
      relativeUnrestrictedSPlaceDatum
        (K := K) (L := L) S
    letI : ∀ i, MulDistribMulAction
        (absoluteValueDecompositionGroup K (d i).extension.1)
        (LocalizedCompletion
          (d i).base (d i).extension)ˣ :=
      fun i =>
        decompositionGroupLocalUnitsAction
          (d i).base (d i).base_isNontrivial
          (d i).extension
    letI : ∀ i, MulDistribMulAction
        (L ≃ₐ[K] L)
        (LocalPlaceBlock
          (d i).base (d i).base_isNontrivial
          (d i).extension) :=
      fun i =>
        inducedMulDistribMulAction
          (absoluteValueDecompositionGroup K
            (d i).extension.1)
    letI : MulDistribMulAction (L ≃ₐ[K] L)
        (LocalBlockFamily d) :=
      piMulDistribMulAction (L ≃ₐ[K] L)
        (fun i =>
          LocalPlaceBlock
            (d i).base (d i).base_isNontrivial
            (d i).extension)
    letI : Finite
        (HerbrandH0 (L ≃ₐ[K] L)
          (LocalBlockFamily d)) :=
      relativeUnrestrictedLocalBlockFamilyHerbrandH0Finite
        S σ hgen
    Nat.card
        (HerbrandH0 (L ≃ₐ[K] L)
          (LocalBlockFamily d)) =
      ∏ i,
        relativeUnrestrictedSPlaceLocalDegree
          (K := K) (L := L) S i := by
  let d :=
    relativeUnrestrictedSPlaceDatum
      (K := K) (L := L) S
  let localAction :=
    localBlockFamilyLocalAction d
  let blockAction :=
    localBlockFamilyBlockAction d
  let familyAction :=
    localBlockFamilyAction d
  let decompositionFintype :=
    localBlockFamilyDecompositionFintype d
  let localFinite : ∀ i, Finite
      (HerbrandH0
        (absoluteValueDecompositionGroup K (d i).extension.1)
        (LocalizedCompletion
          (d i).base (d i).extension)ˣ) :=
    fun i =>
      relativeUnrestrictedLocalHerbrandH0Finite
        S i σ hgen
  let familyFinite : Finite
      (HerbrandH0 (L ≃ₐ[K] L)
        (LocalBlockFamily d)) :=
    relativeUnrestrictedLocalBlockFamilyHerbrandH0Finite
      S σ hgen
  calc
    Nat.card
        (HerbrandH0 (L ≃ₐ[K] L)
          (LocalBlockFamily d)) =
      Nat.card
        (∀ i,
          HerbrandH0
            (absoluteValueDecompositionGroup K
              (d i).extension.1)
            (LocalizedCompletion
              (d i).base (d i).extension)ˣ) :=
      Nat.card_congr
        (localBlockFamilyHerbrandH0Equiv
          d σ hgen).toEquiv
    _ = ∏ i, Nat.card
        (HerbrandH0
          (absoluteValueDecompositionGroup K
            (d i).extension.1)
          (LocalizedCompletion
            (d i).base (d i).extension)ˣ) :=
      Nat.card_pi
    _ = ∏ i,
        relativeUnrestrictedSPlaceLocalDegree
          (K := K) (L := L) S i := by
      apply Finset.prod_congr rfl
      intro i _
      exact
        relativeUnrestrictedLocalHerbrandH0_card_eq_localDegree
          S i σ hgen
end
end

section
-- module Solutions.OAIQ244_DUKE.AlgebraicNumberTheory_Idele_Cohomology_SPlaces_Herbrand_Factors
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalCyclotomicCompletionAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.DiscreteNthRootsSubgroup.instCommGroupSubtypeUnitsMemSubgroup _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.KummerTheory.nthRootsSubgroupFintype _root_.LocalClassFieldTheory.finiteGaloisLocalField_integerRing_moduleFinite _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.LubinTate.compatibleGroupFamiliesCommGroup _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.CyclicCohomology.binaryCoefficientFamilyCommGroup _root_.LocalClassFieldTheory.comparisonIntegerRingIsIntegralClosure _root_.LocalClassFieldTheory.normalizationIntegerRingIsIntegralClosure
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

/-!
# Transport from local blocks to unrestricted factors

This leaf transports the finite-family Herbrand calculation to the actual
unrestricted relative S-idele factors.
-/

open scoped NumberField BigOperators ValuativeRel Classical NNReal
open NumberField IsDedekindDomain

noncomputable section


open AlgebraicNumberTheory.Valuations
open CyclicCohomology.ProfiniteCohomology.Herbrand
open CyclicCohomology
open HilbertRamification
open LocalClassFieldTheory
open LocalFieldTheory

variable {K L : Type}
    [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]

/-!
## Canonical factor-transport action providers
-/

omit [NumberField L] in
/-- Degree zero for the actual unrestricted factors: its
cardinality is the product of the local degrees. -/
theorem
    relativeUnrestrictedSPlaceFactorsHerbrandH0_card_eq_product
    (S : Finset (HeightOneSpectrum (𝓞 K)))
    (σ : L ≃ₐ[K] L)
    (hgen : ∀ τ : L ≃ₐ[K] L,
      τ ∈ Subgroup.zpowers σ) :
    letI :=
      relativeUnrestrictedSPlaceFactorsAction
        (K := K) (L := L) S
    letI : Finite
        (HerbrandH0 (L ≃ₐ[K] L)
          (RelativeUnrestrictedSPlaceFactors
            (K := K) (L := L) S)) :=
      relativeUnrestrictedSPlaceFactorsHerbrandH0Finite
        S σ hgen
    Nat.card
        (HerbrandH0 (L ≃ₐ[K] L)
          (RelativeUnrestrictedSPlaceFactors
            (K := K) (L := L) S)) =
      ∏ i,
        relativeUnrestrictedSPlaceLocalDegree
          (K := K) (L := L) S i := by
  let d :=
    relativeUnrestrictedSPlaceDatum
      (K := K) (L := L) S
  let sourceAction :=
    relativeUnrestrictedSPlaceFactorsActionProvider
      (K := K) (L := L) S
  let targetAction :=
    relativeUnrestrictedSPlaceLocalBlockFamilyActionProvider
      (K := K) (L := L) S
  let sourceFinite : Finite
      (HerbrandH0 (L ≃ₐ[K] L)
        (RelativeUnrestrictedSPlaceFactors
          (K := K) (L := L) S)) :=
    relativeUnrestrictedSPlaceFactorsHerbrandH0Finite
      S σ hgen
  let targetFinite : Finite
      (HerbrandH0 (L ≃ₐ[K] L)
        (LocalBlockFamily d)) :=
    relativeUnrestrictedLocalBlockFamilyHerbrandH0Finite
      S σ hgen
  calc
    Nat.card
        (HerbrandH0 (L ≃ₐ[K] L)
          (RelativeUnrestrictedSPlaceFactors
            (K := K) (L := L) S)) =
      Nat.card
        (HerbrandH0 (L ≃ₐ[K] L)
          (LocalBlockFamily d)) :=
      Nat.card_congr
        (relativeUnrestrictedSPlaceFactorsHerbrandH0EquivLocalBlockFamily
          (K := K) (L := L) S).toEquiv
    _ = ∏ i,
        relativeUnrestrictedSPlaceLocalDegree
          (K := K) (L := L) S i :=
      relativeUnrestrictedLocalBlockFamilyHerbrandH0_card_eq_product
        S σ hgen

omit [NumberField L] in
/-- Degree minus one for the actual unrestricted factors:
the group has one element. -/
theorem
    relativeUnrestrictedSPlaceFactorsHerbrandHMinusOne_card_eq_one
    (S : Finset (HeightOneSpectrum (𝓞 K)))
    (σ : L ≃ₐ[K] L)
    (hgen : ∀ τ : L ≃ₐ[K] L,
      τ ∈ Subgroup.zpowers σ) :
    letI :=
      relativeUnrestrictedSPlaceFactorsAction
        (K := K) (L := L) S
    letI : Finite
        (HerbrandHMinusOne (L ≃ₐ[K] L)
          (RelativeUnrestrictedSPlaceFactors
            (K := K) (L := L) S) σ) :=
      relativeUnrestrictedSPlaceFactorsHerbrandHMinusOneFinite
        S σ hgen
    Nat.card
        (HerbrandHMinusOne (L ≃ₐ[K] L)
          (RelativeUnrestrictedSPlaceFactors
            (K := K) (L := L) S) σ) = 1 := by
  let d :=
    relativeUnrestrictedSPlaceDatum
      (K := K) (L := L) S
  let sourceAction :=
    relativeUnrestrictedSPlaceFactorsActionProvider
      (K := K) (L := L) S
  let targetAction :=
    relativeUnrestrictedSPlaceLocalBlockFamilyActionProvider
      (K := K) (L := L) S
  let sourceFinite : Finite
      (HerbrandHMinusOne (L ≃ₐ[K] L)
        (RelativeUnrestrictedSPlaceFactors
          (K := K) (L := L) S) σ) :=
    relativeUnrestrictedSPlaceFactorsHerbrandHMinusOneFinite
      S σ hgen
  let targetFinite : Finite
      (HerbrandHMinusOne (L ≃ₐ[K] L)
        (LocalBlockFamily d) σ) :=
    relativeUnrestrictedLocalBlockFamilyHerbrandHMinusOneFinite
      S σ hgen
  calc
    Nat.card
        (HerbrandHMinusOne (L ≃ₐ[K] L)
          (RelativeUnrestrictedSPlaceFactors
            (K := K) (L := L) S) σ) =
      Nat.card
        (HerbrandHMinusOne (L ≃ₐ[K] L)
          (LocalBlockFamily d) σ) :=
      Nat.card_congr
        (relativeUnrestrictedSPlaceFactorsHerbrandHMinusOneEquivLocalBlockFamily
          (K := K) (L := L) S σ).toEquiv
    _ = 1 :=
      relativeUnrestrictedLocalBlockFamilyHerbrandHMinusOne_card_eq_one
        S σ hgen

omit [NumberField L] in
/-- The Herbrand quotient formula for the actual unrestricted tensor factors. -/
theorem relativeUnrestrictedSPlaceFactors_herbrandQuotient
    (S : Finset (HeightOneSpectrum (𝓞 K)))
    (σ : L ≃ₐ[K] L)
    (hgen : ∀ τ : L ≃ₐ[K] L,
      τ ∈ Subgroup.zpowers σ) :
    letI :=
      relativeUnrestrictedSPlaceFactorsAction
        (K := K) (L := L) S
    letI : Finite
        (HerbrandH0 (L ≃ₐ[K] L)
          (RelativeUnrestrictedSPlaceFactors
            (K := K) (L := L) S)) :=
      relativeUnrestrictedSPlaceFactorsHerbrandH0Finite
        S σ hgen
    letI : Finite
        (HerbrandHMinusOne (L ≃ₐ[K] L)
          (RelativeUnrestrictedSPlaceFactors
            (K := K) (L := L) S) σ) :=
      relativeUnrestrictedSPlaceFactorsHerbrandHMinusOneFinite
        S σ hgen
    herbrandQuotient
        (G := L ≃ₐ[K] L)
        (A := RelativeUnrestrictedSPlaceFactors
          (K := K) (L := L) S) σ =
      ∏ i,
        (relativeUnrestrictedSPlaceLocalDegree
          (K := K) (L := L) S i : ℚ) := by
  let :=
    relativeUnrestrictedSPlaceFactorsAction
      (K := K) (L := L) S
  let : Finite
      (HerbrandH0 (L ≃ₐ[K] L)
        (RelativeUnrestrictedSPlaceFactors
          (K := K) (L := L) S)) :=
    relativeUnrestrictedSPlaceFactorsHerbrandH0Finite
      S σ hgen
  let : Finite
      (HerbrandHMinusOne (L ≃ₐ[K] L)
        (RelativeUnrestrictedSPlaceFactors
          (K := K) (L := L) S) σ) :=
    relativeUnrestrictedSPlaceFactorsHerbrandHMinusOneFinite
      S σ hgen
  rw [herbrandQuotient_eq_card_ratio,
    relativeUnrestrictedSPlaceFactorsHerbrandH0_card_eq_product
      S σ hgen,
    relativeUnrestrictedSPlaceFactorsHerbrandHMinusOne_card_eq_one
      S σ hgen]
  simp only [Nat.cast_prod, Nat.cast_one, div_one]
end
end

section
-- module Solutions.OAIQ244_DUKE.AlgebraicNumberTheory_Idele_Cohomology_SPlaces_OutsideIntegralInduced_ChosenPlaceIntegralBlockEquiv
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 400000
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalCyclotomicCompletionAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalClassFieldTheory.finiteGaloisLocalField_integerRing_moduleFinite _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.residueFieldZModAlgebra _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedIntegralAlgebraContextValuationSubringAlgebra _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.LubinTate.compatibleGroupFamiliesGroup _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.instIsTopologicalRingLocalAlgebra _root_.OAI.PrimeDegreePackets.instTopologicalSpaceLocalAlgebra _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.CyclicCohomology.binaryCoefficientFamilyCommGroup _root_.LocalClassFieldTheory.comparisonIntegerRingIsIntegralClosure _root_.LocalClassFieldTheory.normalizationIntegerRingIsIntegralClosure _root_.relativeUnrestrictedSPlaceFactorCommGroup
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

/-!
# The chosen integral tensor equivalence

This file constructs the equivalence between the chosen integral tensor block
and the induced module of chosen local integer units.
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

/-- Outside a finite exceptional set, the actual integral tensor-unit
subgroup at a finite place is the induced module of the
integer units at the chosen extension. -/
noncomputable def
    relativeLocalTensorDecompositionIntegralUnitSubgroupEquivInducedIntegerUnits
    (w₀ : HeightOneSpectrum (𝓞 K)) :
    relativeLocalTensorDecompositionIntegralUnitSubgroup
        (K := K) (L := L) w₀ ≃*
      ChosenFinitePlaceInducedIntegerUnits
        (K := K) (L := L) w₀ :=
  by
    letI : MulDistribMulAction
        (absoluteValueDecompositionGroup K
          (chosenFinitePlaceExtension (L := L) w₀).1)
        𝒪[ChosenFinitePlaceLocalizedCompletion
          (K := K) (L := L) w₀]ˣ :=
      chosenFinitePlaceDecompositionGroupIntegerUnitsAction
        (K := K) (L := L) w₀
    exact
      (relativeLocalTensorDecompositionIntegralUnitSubgroupEquivPiUnits
        (K := K) (L := L) w₀).trans
        (completionProductIntegerUnitsEquivInducedModule
          (K := K) (L := L)
          (HeightOneSpectrum.adicAbv K w₀)
          (RayClass.adicAbv_isNontrivial w₀)
          (HeightOneSpectrum.isNonarchimedean_adicAbv K w₀)
          (chosenFinitePlaceExtension (L := L) w₀))
end ChosenFinitePlace
end
end

section
-- module Solutions.OAIQ244_DUKE.AlgebraicNumberTheory_Idele_Cohomology_SPlaces_OutsideIntegralInduced_ChosenPlaceIntegralBlockEquivApply
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 400000
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalCyclotomicCompletionAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalClassFieldTheory.finiteGaloisLocalField_integerRing_moduleFinite _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.residueFieldZModAlgebra _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedIntegralAlgebraContextValuationSubringAlgebra _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.CyclicCohomology.binaryCoefficientFamilyCommGroup _root_.LocalClassFieldTheory.comparisonIntegerRingIsIntegralClosure _root_.LocalClassFieldTheory.normalizationIntegerRingIsIntegralClosure _root_.relativeUnrestrictedSPlaceFactorCommGroup
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

/-!
# Compatibility of the chosen integral equivalence and inclusion

This file compares the integral-block inclusion with the finite-place tensor
equivalence on underlying field units.
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
/-- The integral-block inclusion is compatible with the pre-existing
local-block equivalence on underlying field units. -/
theorem
    chosenFinitePlaceIntegralInducedBlockToLocalPlaceBlock_equiv_apply
    (w₀ : HeightOneSpectrum (𝓞 K))
    (x : relativeLocalTensorDecompositionIntegralUnitSubgroup
      (K := K) (L := L) w₀) :
    chosenFinitePlaceIntegralInducedBlockToLocalPlaceBlock
        (K := K) (L := L) w₀
        (relativeLocalTensorDecompositionIntegralUnitSubgroupEquivInducedIntegerUnits
          (K := K) (L := L) w₀ x) =
      finitePlaceTensorUnitsEquivLocalPlaceBlock
        (K := K) (L := L) w₀
        (chosenFinitePlaceExtension (L := L) w₀)
        (x : (w₀.adicCompletion K ⊗[K] L)ˣ) := by
  let vK := HeightOneSpectrum.adicAbv K w₀
  let u := chosenFinitePlaceExtension (L := L) w₀
  let hvK : vK.IsNontrivial := RayClass.adicAbv_isNontrivial w₀
  let hvKna : IsNonarchimedean (vK : K → ℝ) :=
    HeightOneSpectrum.isNonarchimedean_adicAbv K w₀
  let := decompositionGroupLocalUnitsAction vK hvK u
  apply
    (inducedRightCosetCoordinates
      (absoluteValueDecompositionGroup K u.1)).injective
  funext q
  apply Units.ext
  rfl
end ChosenFinitePlace
end
end

section
-- module Solutions.OAIQ244_DUKE.AlgebraicNumberTheory_Idele_Cohomology_SPlaces_OutsideIntegralInduced_ChosenPlaceIntegralBlockInducedSmul
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 400000
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.infinitePlaceComplexificationOverfield_baseSmul _root_.GlobalClassFieldTheory.Reciprocity.infinitePlaceComplexificationOverfield_smul _root_.GlobalClassFieldTheory.Reciprocity.rationalCyclotomicCompletionAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalClassFieldTheory.finiteGaloisLocalField_integerRing_moduleFinite _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.residueFieldZModAlgebra _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedIntegralAlgebraContextValuationSubringAlgebra _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.LubinTate.compatibleGroupFamiliesGroup _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.diagonalLogAction _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.CyclicCohomology.binaryCoefficientFamilyCommGroup _root_.LocalClassFieldTheory.comparisonIntegerRingIsIntegralClosure _root_.LocalClassFieldTheory.normalizationIntegerRingIsIntegralClosure _root_.relativeUnrestrictedSPlaceFactorCommGroup
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

/-!
# Equivariance of the induced integral block

This file proves that the inclusion of the chosen integral induced block is
equivariant for the global Galois action.
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
/-- The embedding of the chosen integral induced block is equivariant for
the full global Galois action. -/
theorem chosenFinitePlaceIntegralInducedBlockToLocalPlaceBlock_smul
    (w₀ : HeightOneSpectrum (𝓞 K))
    (τ : L ≃ₐ[K] L) :
    ∀ f : ChosenFinitePlaceInducedIntegerUnits
        (K := K) (L := L) w₀,
    chosenFinitePlaceIntegralInducedBlockToLocalPlaceBlock
        (K := K) (L := L) w₀
        ((chosenFinitePlaceInducedIntegerUnitsAction
          (K := K) (L := L) w₀).smul τ f) =
      (chosenFinitePlaceLocalPlaceBlockAction
        (K := K) (L := L) w₀).smul τ
        (chosenFinitePlaceIntegralInducedBlockToLocalPlaceBlock
          (K := K) (L := L) w₀ f) := by
  intro f
  rfl

end ChosenFinitePlace
end
end

section
-- module Solutions.OAIQ244_DUKE.AlgebraicNumberTheory_Idele_Cohomology_SPlaces_OutsideIntegralInduced_ChosenPlaceIntegralBlock
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 400000
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.infinitePlaceComplexificationOverfield_baseSmul _root_.GlobalClassFieldTheory.Reciprocity.infinitePlaceComplexificationOverfield_smul _root_.GlobalClassFieldTheory.Reciprocity.rationalCyclotomicCompletionAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalClassFieldTheory.finiteGaloisLocalField_integerRing_moduleFinite _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.residueFieldZModAlgebra _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedIntegralAlgebraContextValuationSubringAlgebra _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.LubinTate.compatibleGroupFamiliesGroup _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.diagonalLogAction _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.CyclicCohomology.binaryCoefficientFamilyCommGroup _root_.LocalClassFieldTheory.comparisonIntegerRingIsIntegralClosure _root_.LocalClassFieldTheory.normalizationIntegerRingIsIntegralClosure _root_.relativeUnrestrictedSPlaceFactorCommGroup
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

/-!
# Equivariance facade for the integral induced block

This file combines the independent induced-block and tensor-block equivariance
lemmas into the transport used by the cohomology layer.
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
/-- The integral tensor-to-induced-module equivalence is equivariant for
the full global Galois action. -/
theorem
    relativeLocalTensorDecompositionIntegralUnitSubgroupEquivInducedIntegerUnits_smul
    (w₀ : HeightOneSpectrum (𝓞 K))
    (τ : L ≃ₐ[K] L)
    (x : relativeLocalTensorDecompositionIntegralUnitSubgroup
      (K := K) (L := L) w₀) :
    letI :=
      relativeLocalTensorDecompositionIntegralUnitSubgroupAction
        (K := K) (L := L) w₀
    letI :=
      chosenFinitePlaceInducedIntegerUnitsAction
        (K := K) (L := L) w₀
    relativeLocalTensorDecompositionIntegralUnitSubgroupEquivInducedIntegerUnits
        (K := K) (L := L) w₀ (τ • x) =
      τ •
        (relativeLocalTensorDecompositionIntegralUnitSubgroupEquivInducedIntegerUnits
          (K := K) (L := L) w₀ x) := by
  let :=
    relativeLocalTensorDecompositionIntegralUnitSubgroupAction
      (K := K) (L := L) w₀
  let :=
    chosenFinitePlaceInducedIntegerUnitsAction
      (K := K) (L := L) w₀
  let :=
    chosenFinitePlaceLocalPlaceBlockAction
      (K := K) (L := L) w₀
  apply
    chosenFinitePlaceIntegralInducedBlockToLocalPlaceBlock_injective
      (K := K) (L := L) w₀
  calc
    chosenFinitePlaceIntegralInducedBlockToLocalPlaceBlock
          (K := K) (L := L) w₀
          (relativeLocalTensorDecompositionIntegralUnitSubgroupEquivInducedIntegerUnits
            (K := K) (L := L) w₀
            ((relativeLocalTensorDecompositionIntegralUnitSubgroupAction
              (K := K) (L := L) w₀).smul τ x)) =
        finitePlaceTensorUnitsEquivLocalPlaceBlock
          (K := K) (L := L) w₀
          (chosenFinitePlaceExtension (L := L) w₀)
          (((relativeLocalTensorDecompositionIntegralUnitSubgroupAction
              (K := K) (L := L) w₀).smul τ x :
              relativeLocalTensorDecompositionIntegralUnitSubgroup
                (K := K) (L := L) w₀) :
            (w₀.adicCompletion K ⊗[K] L)ˣ) :=
      chosenFinitePlaceIntegralInducedBlockToLocalPlaceBlock_equiv_apply
        (K := K) (L := L) w₀
        ((relativeLocalTensorDecompositionIntegralUnitSubgroupAction
          (K := K) (L := L) w₀).smul τ x)
    _ =
        (chosenFinitePlaceLocalPlaceBlockAction
          (K := K) (L := L) w₀).smul τ
          (finitePlaceTensorUnitsEquivLocalPlaceBlock
            (K := K) (L := L) w₀
            (chosenFinitePlaceExtension (L := L) w₀)
            (x : (w₀.adicCompletion K ⊗[K] L)ˣ)) :=
      finitePlaceTensorUnitsEquivLocalPlaceBlock_restricted_smul
        (K := K) (L := L) w₀ τ x
    _ =
        (chosenFinitePlaceLocalPlaceBlockAction
          (K := K) (L := L) w₀).smul τ
          (chosenFinitePlaceIntegralInducedBlockToLocalPlaceBlock
            (K := K) (L := L) w₀
            (relativeLocalTensorDecompositionIntegralUnitSubgroupEquivInducedIntegerUnits
              (K := K) (L := L) w₀ x)) :=
      congrArg
        (fun z :
            ChosenFinitePlaceLocalPlaceBlock
              (K := K) (L := L) w₀ =>
          (chosenFinitePlaceLocalPlaceBlockAction
            (K := K) (L := L) w₀).smul τ z)
        (chosenFinitePlaceIntegralInducedBlockToLocalPlaceBlock_equiv_apply
          (K := K) (L := L) w₀ x).symm
    _ =
        chosenFinitePlaceIntegralInducedBlockToLocalPlaceBlock
          (K := K) (L := L) w₀
          ((chosenFinitePlaceInducedIntegerUnitsAction
            (K := K) (L := L) w₀).smul τ
            (relativeLocalTensorDecompositionIntegralUnitSubgroupEquivInducedIntegerUnits
              (K := K) (L := L) w₀ x)) :=
      (chosenFinitePlaceIntegralInducedBlockToLocalPlaceBlock_smul
        (K := K) (L := L) w₀ τ
        (relativeLocalTensorDecompositionIntegralUnitSubgroupEquivInducedIntegerUnits
          (K := K) (L := L) w₀ x)).symm

end ChosenFinitePlace
end
end

section
-- module Solutions.OAIQ244_DUKE.AlgebraicNumberTheory_Ramification_Splitting_FinitePlaceIdeal
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalCyclotomicCompletionAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.KummerTheory.primeCyclotomicBaseFiniteDimensional _root_.LocalClassFieldTheory.finiteGaloisLocalField_integerRing_moduleFinite _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.residueFieldZModAlgebra _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedIntegralAlgebraContextValuationSubringAlgebra _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.LocalClassFieldTheory.comparisonIntegerRingIsIntegralClosure _root_.LocalClassFieldTheory.normalizationIntegerRingIsIntegralClosure _root_.chosenFinitePlaceCompletionAlgebra _root_.chosenFinitePlaceCompletionContinuousSMul _root_.chosenFinitePlaceCompletionFiniteDimensional _root_.chosenFinitePlaceCompletionLocallyCompactSpace _root_.chosenFinitePlaceLocalizedFiniteDimensional _root_.chosenFinitePlaceLocalizedIntegerAlgebra _root_.chosenFinitePlaceLocalizedIntegerModuleFinite _root_.chosenFinitePlaceLocalizedIsGalois _root_.chosenFinitePlaceLocalizedIsIntegralClosure _root_.chosenFinitePlaceLocalizedIsNonarchimedeanLocalField _root_.chosenFinitePlaceLocalizedIsValuativeTopology _root_.chosenFinitePlaceLocalizedLocallyCompactSpace _root_.chosenFinitePlaceLocalizedValuationCompatible _root_.chosenFinitePlaceLocalizedValuationHasExtension _root_.chosenFinitePlaceLocalizedValuationIsNontrivial _root_.chosenFinitePlaceLocalizedValuativeRel _root_.chosenFinitePlaceLocalizedValuativeRelIsNontrivial _root_.chosenFinitePlaceLocalizedValued
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

/-!
# Finite-place splitting through prime ideals

For a finite Galois extension of number fields, an exact extension of a
normalized finite absolute value and its centre prime ideal have the same
decomposition group.  This file makes that comparison independent of the
chosen extension and records the finiteness of the fibres of contraction.
These are the place-theoretic ingredients used in the cyclic prime-power and
normal-closure splitting reductions.
-/

open scoped NumberField Classical
open NumberField IsDedekindDomain

noncomputable section

open AlgebraicNumberTheory.Valuations
open HilbertRamification

variable
    {K L : Type}
    [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]

omit [FiniteDimensional K L] in
/-- Complete splitting can be tested at the centre of any exact extension
of the normalized absolute value. -/
theorem finitePlaceSplitsCompletely_iff_centre_stabilizer_eq_bot
    (v : HeightOneSpectrum (𝓞 K))
    (w : AbsoluteValueExtension
      (HeightOneSpectrum.adicAbv K v) L) :
    FinitePlaceSplitsCompletely (K := K) (L := L) v ↔
      letI := finitePlaceMulAction K L
      MulAction.stabilizer (L ≃ₐ[K] L)
        (finitePlaceExtensionCentre (K := K) (L := L) v w) = ⊥ := by
  let := finitePlaceMulAction K L
  unfold FinitePlaceSplitsCompletely finitePlaceDecompositionGroup
  constructor
  · intro h
    have hw :
        absoluteValueDecompositionGroup K w.1 = ⊥ :=
      absoluteValueDecompositionGroup_eq_bot_independent_extension
        (HeightOneSpectrum.adicAbv K v)
        (RayClass.adicAbv_isNontrivial v)
        (chosenFinitePlaceExtension (L := L) v) w h
    rwa [absoluteValueDecompositionGroup_eq_finitePlaceStabilizer
      (K := K) (L := L) v w] at hw
  · intro h
    have hw :
        absoluteValueDecompositionGroup K w.1 = ⊥ := by
      rwa [absoluteValueDecompositionGroup_eq_finitePlaceStabilizer
        (K := K) (L := L) v w]
    exact
      absoluteValueDecompositionGroup_eq_bot_independent_extension
        (HeightOneSpectrum.adicAbv K v)
        (RayClass.adicAbv_isNontrivial v)
        w (chosenFinitePlaceExtension (L := L) v) hw

/-- Complete splitting can equivalently be tested at any finite place
above the base place. -/
theorem finitePlaceSplitsCompletely_iff_stabilizer_eq_bot
    (v : HeightOneSpectrum (𝓞 K))
    (W : HeightOneSpectrum (𝓞 L))
    (hW : finitePlaceBelow (K := K) W = v) :
    FinitePlaceSplitsCompletely (K := K) (L := L) v ↔
      letI := finitePlaceMulAction K L
      MulAction.stabilizer (L ≃ₐ[K] L) W = ⊥ := by
  let := finitePlaceMulAction K L
  let Wv :
      {W : HeightOneSpectrum (𝓞 L) //
        finitePlaceBelow (K := K) W = v} :=
    ⟨W, hW⟩
  let w :=
    (finitePlaceExtensionEquivAbove (K := K) (L := L) v).symm Wv
  have hw :
      finitePlaceExtensionCentre (K := K) (L := L) v w = W := by
    have happ :=
      (finitePlaceExtensionEquivAbove (K := K) (L := L) v).apply_symm_apply Wv
    exact congrArg Subtype.val happ
  rw [finitePlaceSplitsCompletely_iff_centre_stabilizer_eq_bot
    (K := K) (L := L) v w, hw]

section IntermediateField

variable {M : Type}
    [Field M] [NumberField M]
    [Algebra K M] [Algebra M L]
    [IsScalarTower K M L]
    [IsGalois M L]

/-- If a finite place splits completely in `L / K`, then every finite
place of an intermediate field above it splits completely in `L / M`.
The relation "above" is expressed canonically by ideal contraction,
so no comparison of differently normalized absolute values is needed. -/
theorem finitePlaceSplitsCompletely_over_intermediate_of_below
    (v' : HeightOneSpectrum (𝓞 M))
    (hsplit :
      FinitePlaceSplitsCompletely
        (K := K) (L := L)
        (finitePlaceBelow (K := K) v')) :
    FinitePlaceSplitsCompletely
      (K := M) (L := L) v' := by
  let w :=
    chosenFinitePlaceExtension (L := L) v'
  let W :=
    finitePlaceExtensionCentre
      (K := M) (L := L) v' w
  have hWM :
      finitePlaceBelow (K := M) W = v' :=
    finitePlaceBelow_finitePlaceExtensionCentre
      (K := M) (L := L) v' w
  have hWK :
      finitePlaceBelow (K := K) W =
        finitePlaceBelow (K := K) v' := by
    rw [← finitePlaceBelow_finitePlaceBelow
      (K := K) (M := M) (L := L) W, hWM]
  let := finitePlaceMulAction K L
  have hKbot :
      MulAction.stabilizer (L ≃ₐ[K] L) W = ⊥ :=
    (finitePlaceSplitsCompletely_iff_stabilizer_eq_bot
      (K := K) (L := L)
      (finitePlaceBelow (K := K) v') W hWK).mp hsplit
  let := finitePlaceMulAction M L
  apply
    (finitePlaceSplitsCompletely_iff_stabilizer_eq_bot
      (K := M) (L := L) v' W hWM).mpr
  apply le_bot_iff.mp
  intro σ hσ
  rw [Subgroup.mem_bot]
  let ρ : L ≃ₐ[K] L :=
    RamificationTheory.HilbertRamification.ValuationSubring.restrictAutomorphismScalars
      (K := K) (M := M) σ
  have hρ :
      ρ ∈ MulAction.stabilizer (L ≃ₐ[K] L) W := by
    simp only [MulAction.mem_stabilizer_iff] at hσ ⊢
    change finitePlaceEquiv M L σ W = W at hσ
    change finitePlaceEquiv K L ρ W = W
    unfold ρ
    rw [finitePlaceEquiv_restrictAutomorphismScalars
      (K := K) (M := M) (L := L)]
    exact hσ
  have hρOne : ρ = 1 :=
    Subgroup.mem_bot.mp (hKbot ▸ hρ)
  ext x
  have hx := DFunLike.congr_fun hρOne x
  change σ x = x
  change σ x = x at hx
  exact hx

/-- Finiteness of the nonsplitting finite places ascends from `K` to
an intermediate field `M`. -/
theorem finite_nonsplittingPlaces_over_intermediate
    (hfinite :
      {v : HeightOneSpectrum (𝓞 K) |
        ¬ FinitePlaceSplitsCompletely
          (K := K) (L := L) v}.Finite) :
    {v' : HeightOneSpectrum (𝓞 M) |
      ¬ FinitePlaceSplitsCompletely
        (K := M) (L := L) v'}.Finite := by
  apply
    (Set.Finite.preimage_finitePlaceBelow
      (K := K) (L := M) hfinite).subset
  intro v' hv'
  change
    ¬ FinitePlaceSplitsCompletely
      (K := K) (L := L)
      (finitePlaceBelow (K := K) v')
  intro hsplit
  exact hv'
    (finitePlaceSplitsCompletely_over_intermediate_of_below
      (K := K) (M := M) (L := L) v' hsplit)

end IntermediateField
end
end

section
-- module Solutions.OAIQ244_DUKE.AlgebraicNumberTheory_Ramification_Splitting_NormalClosure
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.infinitePlaceComplexificationOverfield_algebra _root_.GlobalClassFieldTheory.Reciprocity.infinitePlaceComplexificationOverfield_baseAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalCyclotomicCompletionAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalClassFieldTheory.finiteGaloisLocalField_integerRing_moduleFinite _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.residueFieldZModAlgebra _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedIntegralAlgebraContextValuationSubringAlgebra _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedQPadicContextValuationSubringTower _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.diagonalLogAction _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.LocalClassFieldTheory.comparisonIntegerRingIsIntegralClosure _root_.LocalClassFieldTheory.normalizationIntegerRingIsIntegralClosure _root_.chosenFinitePlaceCompletionAlgebra _root_.chosenFinitePlaceCompletionContinuousSMul _root_.chosenFinitePlaceCompletionFiniteDimensional _root_.chosenFinitePlaceCompletionLocallyCompactSpace _root_.chosenFinitePlaceLocalizedFiniteDimensional _root_.chosenFinitePlaceLocalizedIntegerAlgebra _root_.chosenFinitePlaceLocalizedIntegerModuleFinite _root_.chosenFinitePlaceLocalizedIsGalois _root_.chosenFinitePlaceLocalizedIsIntegralClosure _root_.chosenFinitePlaceLocalizedIsNonarchimedeanLocalField _root_.chosenFinitePlaceLocalizedIsValuativeTopology _root_.chosenFinitePlaceLocalizedLocallyCompactSpace _root_.chosenFinitePlaceLocalizedValuationCompatible _root_.chosenFinitePlaceLocalizedValuationHasExtension _root_.chosenFinitePlaceLocalizedValuationIsNontrivial _root_.chosenFinitePlaceLocalizedValuativeRel _root_.chosenFinitePlaceLocalizedValuativeRelIsNontrivial _root_.chosenFinitePlaceLocalizedValued _root_.scaledRelativeIntegerLatticeQuotientFinite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

/-!
# Complete splitting and normal closures

This file formalizes the normal-closure reduction for complete splitting.
For a finite Galois extension `M / K`, an intermediate field `L`, a
nontrivial absolute value `v` of `K`, and an extension `w` to `M`, put

* `G = Gal(M / K)`,
* `H = Gal(M / L)`, and
* `D = D(w / v)`.

Restriction of the conjugates of `w` gives an equivalence

`H \ G / D ≃ { extensions of v to L }`.

Thus the intrinsic complete-splitting condition for the possibly
non-Galois extension `L / K` is exactly the equality between the number
of double cosets and the number of left cosets.  If `M` is generated by
the `K`-conjugates of `L`, then `H` has trivial normal core.
`SplittingGroupTheory` consequently forces `D = 1`, so the place splits
completely already in `M`.
-/

open scoped NumberField Classical
open NumberField IsDedekindDomain

noncomputable section

open AlgebraicNumberTheory.Valuations
open HilbertRamification

section SplittingThroughRestriction

variable
    {K E N : Type}
    [Field K] [NumberField K]
    [Field E] [Algebra K E]
    [FiniteDimensional K E] [IsGalois K E]
    [Field N] [Algebra K N] [Algebra E N]
    [IsScalarTower K E N]
    [FiniteDimensional K N] [IsGalois K N]

omit [FiniteDimensional K N] in
/-- If the decomposition group upstairs acts trivially on a normal
subextension, then the finite place splits completely in that
subextension. -/
theorem
    finitePlaceSplitsCompletely_of_decompositionGroup_le_restrictNormalHom_ker
    (v : HeightOneSpectrum (𝓞 K))
    (h :
      finitePlaceDecompositionGroup (K := K) (L := N) v ≤
        (AlgEquiv.restrictNormalHom
          (F := K) (K₁ := N) (E := E)).ker) :
    FinitePlaceSplitsCompletely (K := K) (L := E) v := by
  let M : IntermediateField K N :=
    (IsScalarTower.toAlgHom K E N).fieldRange
  let e : E ≃ₐ[K] M :=
    (IsScalarTower.toAlgHom K E N).equivFieldRange
  let : FiniteDimensional K M :=
    e.toLinearEquiv.finiteDimensional
  let : IsGalois K M :=
    IsGalois.of_algEquiv e
  let vK :=
    NumberField.HeightOneSpectrum.adicAbv K v
  let hvK : vK.IsNontrivial :=
    RayClass.adicAbv_isNontrivial v
  let wN :=
    chosenFinitePlaceExtension (L := N) v
  let wM :=
    restrictAbsoluteValueExtensionToIntermediate
      vK wN M
  have hFix :
      finitePlaceDecompositionGroup (K := K) (L := N) v ≤
        M.fixingSubgroup := by
    intro sigma hsigma
    rw [IntermediateField.mem_fixingSubgroup_iff]
    intro y hy
    rcases hy with ⟨x, rfl⟩
    have hsigmaKer :
        AlgEquiv.restrictNormalHom
            (F := K) (K₁ := N) (E := E) sigma =
          1 :=
      MonoidHom.mem_ker.mp (h hsigma)
    have hx :
        sigma.restrictNormal E x = x := by
      change
        (AlgEquiv.restrictNormalHom
          (F := K) (K₁ := N) (E := E) sigma) x =
            (1 : Gal(E/K)) x
      rw [hsigmaKer]
    calc
      sigma (algebraMap E N x) =
          algebraMap E N (sigma.restrictNormal E x) :=
        (AlgEquiv.restrictNormal_commutes sigma E x).symm
      _ = algebraMap E N x :=
        congrArg (algebraMap E N) hx
  have hMap :
      (finitePlaceDecompositionGroup
          (K := K) (L := N) v).map
          (AlgEquiv.restrictNormalHom
            (F := K) (K₁ := N) M) =
        ⊥ := by
    rw [Subgroup.map_eq_bot_iff,
      IntermediateField.restrictNormalHom_ker]
    exact hFix
  have hwMbot :
      absoluteValueDecompositionGroup K wM.1 = ⊥ := by
    change
      absoluteValueDecompositionGroup K
        (wN.1.comp (f := algebraMap M N)
          (algebraMap M N).injective) = ⊥
    rw [← absoluteValueDecompositionGroup_map_restrictNormalHom
      (M := M) vK hvK wN]
    exact hMap
  have hM :
      FinitePlaceSplitsCompletely
        (K := K) (L := M) v := by
    change
      absoluteValueDecompositionGroup K
          (chosenFinitePlaceExtension (L := M) v).1 =
        ⊥
    exact
      absoluteValueDecompositionGroup_eq_bot_independent_extension
        vK hvK wM
        (chosenFinitePlaceExtension (L := M) v)
        hwMbot
  have hMIntrinsic :
      FinitePlaceSplitsCompletelyInExtension
        (K := K) (E := M) v :=
    (finitePlaceSplitsCompletely_iff_inExtension
      (K := K) (E := M) v).mp hM
  have hEIntrinsic :
      FinitePlaceSplitsCompletelyInExtension
        (K := K) (E := E) v :=
    (finitePlaceSplitsCompletelyInExtension_algEquiv e v).mpr
      hMIntrinsic
  exact
    (finitePlaceSplitsCompletely_iff_inExtension
      (K := K) (E := E) v).mpr hEIntrinsic

end SplittingThroughRestriction
end
end

section
-- module Solutions.OAIQ244_DUKE.AlgebraicNumberTheory_RayClass_LocalConductor
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 400000
attribute [-instance] _root_.ClassFormation.DegreeData.FrobeniusFixedFieldTower.extensionNormal _root_.ClassFormation.DegreeData.GaloisSubextension.extensionSubgroup_normalInstance _root_.ClassFormation.FiniteAbstractField.toFiniteResidueAbstractField_extensionNormal _root_.ClassFormation.FiniteCyclicSubextension.instNormalSubtypeMemSubgroupFieldExtensionSubgroupField _root_.ClassFormation.FiniteGaloisSubextension.extensionSubgroup_normalInstance _root_.ClassFormation.FiniteGaloisSubextension.extensionSubgroup_over_intermediate_normalInstance _root_.ClassFormation.FiniteGaloisSubextension.intermediateField_normalInstance _root_.ClassFormation.FiniteIntermediateField.galoisRefinement_normal _root_.ClassFormation.FiniteUnramifiedCyclicExtension.instNormalSubtypeMemSubgroupFieldExtensionSubgroupField _root_.ClassFormation.conjugateExtension_normal _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.GlobalClassFields.ConductorialSubgroup.finiteIndex _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalClassFieldTheory.extensionSubgroupBase_normal _root_.LocalClassFieldTheory.finiteGaloisExtensionSubgroupOfEmbedding_normal _root_.LocalClassFieldTheory.finiteGaloisLocalField_integerRing_moduleFinite _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.residueFieldZModAlgebra _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedIntegralAlgebraContextValuationSubringAlgebra _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionResidueField.instField _root_.RamificationTheory.HilbertRamification.ValuationSubring.inertiaGroup_normal _root_.RamificationTheory.HilbertRamification.ValuationSubring.ramificationGroupInInertiaAut_normal _root_.RamificationTheory.HilbertRamification.ValuationSubring.selectedResidueField.instAlgebra _root_.ValuationTheory.DiscreteValuationField.DVF.residueField.field _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.ValuationSubring.charP _root_.CyclicCohomology.binaryCoefficientFamilyCommGroup _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.LocalClassFieldTheory.comparisonIntegerRingIsIntegralClosure _root_.LocalClassFieldTheory.normalizationIntegerRingIsIntegralClosure _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.chosenFinitePlaceCompletionAlgebra _root_.relativeUnrestrictedSPlaceFactorCommGroup
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

/-!
# Local conductor subgroups in the idele class group

This file records the one-place higher-unit subgroups used to compare
ray-class moduli with local conductors.  The constructions are
idele- and ray-class data and do not depend on the existence of a
global class field.
-/

open scoped NumberField

noncomputable section

namespace RayClass

open NumberField IsDedekindDomain

variable {K : Type*} [Field K] [NumberField K]

/-- A one-place higher-unit condition is contained in the corresponding
global ray congruence subgroup. -/
theorem localHigherUnitClassSubgroup_le_congruenceSubgroup
    (m : Modulus K)
    (v : HeightOneSpectrum (𝓞 K)) :
    localHigherUnitClassSubgroup v (m.finitePart v) ≤
      m.congruenceSubgroup := by
  rintro _ ⟨x, hx, rfl⟩
  change
    IdeleGroup.finitePlaceIdeleClass v x ∈
      m.congruenceSubgroup
  rw [Modulus.congruenceSubgroup]
  refine ⟨IdeleGroup.finitePlaceIdele v x, ?_, rfl⟩
  apply Subgroup.mem_sup_left
  rw [Modulus.mem_ideleCongruenceSubgroup_iff]
  refine
    ⟨m.infiniteCongruenceSubgroup.one_mem, ?_⟩
  rw [mem_finiteCongruenceSubgroup_iff]
  intro w
  change
    IdeleGroup.finiteComponent w
        (IdeleGroup.finitePlaceIdele v x) ∈
      localHigherUnitGroup w (m.finitePart w)
  by_cases hw : w = v
  · subst w
    rw [IdeleGroup.finitePlaceIdele_finiteComponent_same]
    change
      x ∈
        (localHigherUnitGroup v (m.finitePart v) :
          Set (v.adicCompletion K)ˣ)
    exact hx
  · rw [
      IdeleGroup.finitePlaceIdele_finiteComponent_of_ne
        v w x hw]
    exact (localHigherUnitGroup w (m.finitePart w)).one_mem

end RayClass
end
end

section
-- module Solutions.OAIQ244_DUKE.KummerTheory_Concrete_SUnitPreparation_EnlargedSUnitRestriction
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.infinitePlaceComplexificationOverfield_algebra _root_.GlobalClassFieldTheory.Reciprocity.infinitePlaceComplexificationOverfield_baseAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalClassFieldTheory.finiteGaloisLocalField_integerRing_moduleFinite _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.residueFieldZModAlgebra _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedIntegralAlgebraContextValuationSubringAlgebra _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedQPadicContextValuationSubringTower _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LubinTate.compatibleGroupFamiliesGroup _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.diagonalLogAction _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionResidueField.instField _root_.RamificationTheory.HilbertRamification.ValuationSubring.selectedResidueField.instAlgebra _root_.ValuationTheory.DiscreteValuationField.DVF.maximalIdealPowSuccQuotModule _root_.ValuationTheory.DiscreteValuationField.DVF.residueField.field _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.isDomain _root_.ValuationTheory.ValuationSubring.charP _root_.CyclicCohomology.binaryCoefficientFamilyCommGroup _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.LocalClassFieldTheory.comparisonIntegerRingIsIntegralClosure _root_.LocalClassFieldTheory.normalizationIntegerRingIsIntegralClosure _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.chosenFinitePlaceCompletionAlgebra _root_.chosenFinitePlaceLocalizedIntegerAlgebra _root_.relativeUnrestrictedSPlaceFactorCommGroup
set_option synthInstance.maxHeartbeats 400000
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI
attribute [local instance] OAI.starSubalgebraCommCStarAlgebra

set_option autoImplicit false

/-!
# Restriction from an enlarged S-unit Kummer extension

The concrete embedding and Galois restriction map, its fixing subgroup, and the cyclic fixed fields attached to kernel elements.
-/

open scoped NumberField Classical IsMulCommutative NNReal ValuativeRel
open NumberField IsDedekindDomain
open LocalFieldTheory

noncomputable section

namespace KummerTheory

variable {K : Type*} [Field K]
    [numberFieldK : NumberField K]

/-- The relative Galois group `Gal(N/N_sigma)` is cyclic. -/
theorem enlargedSUnitKummerCyclicFixedField_isCyclic
    {Omega : Type*} [Field Omega] [Algebra K Omega]
    [IsSepClosure K Omega]
    (E : IntermediateField K Omega)
    [FiniteDimensional K E] [IsGalois K E]
    [IsMulCommutative Gal(E/K)]
    (n : ℕ+)
    (hmu : (primitiveRoots (n : ℕ) K).Nonempty)
    (hexponent : ∀ sigma : Gal(E/K), sigma ^ (n : ℕ) = 1)
    (S : Finset (HeightOneSpectrum (𝓞 K)))
    (sigma :
      (enlargedSUnitKummerRestrictionHom
        (K := K) (Omega := Omega) E n hmu
        hexponent S).ker) :
    IsCyclic
      ((fullSUnitKummerExtension
          (K := K) (Omega := Omega) n
          (enlargeByFiniteKummerRadicalSupport
            (K := K) (L := E) n hmu S)) ≃ₐ[
        enlargedSUnitKummerCyclicFixedField
          (K := K) (Omega := Omega) E n hmu
          hexponent S sigma]
        (fullSUnitKummerExtension
          (K := K) (Omega := Omega) n
          (enlargeByFiniteKummerRadicalSupport
            (K := K) (L := E) n hmu S))) := by
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
  let P : Subgroup Gal(N/K) :=
    Subgroup.zpowers (sigma : Gal(N/K))
  have hP : IsCyclic P :=
    Subgroup.isCyclic_zpowers (sigma : Gal(N/K))
  exact
    (IntermediateField.subgroupEquivAlgEquiv P).isCyclic.mp
      hP

end KummerTheory
end
end

section
-- module Solutions.OAIQ244_DUKE.GlobalClassFieldTheory_ClassFieldAxiom_SUnitKummerPrimeSelection_BasePlaceSelection
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.infinitePlaceComplexificationOverfield_algebra _root_.GlobalClassFieldTheory.Reciprocity.infinitePlaceComplexificationOverfield_baseAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalClassFieldTheory.finiteGaloisLocalField_integerRing_moduleFinite _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.residueFieldZModAlgebra _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedIntegralAlgebraContextValuationSubringAlgebra _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedQPadicContextValuationSubringTower _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.diagonalLogAction _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.LocalClassFieldTheory.comparisonIntegerRingIsIntegralClosure _root_.LocalClassFieldTheory.normalizationIntegerRingIsIntegralClosure
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

/-- The enlarged support is contained in the finite avoidance set. -/
theorem
    enlargeByFiniteKummerRadicalSupport_subset_sUnitKummerAvoidedBasePlaces
    {Omega : Type} [Field Omega] [Algebra K Omega]
    [IsSepClosure K Omega]
    (E : IntermediateField K Omega)
    [FiniteDimensional K E] [IsGalois K E]
    (n : ℕ+)
    (hmu : (primitiveRoots (n : ℕ) K).Nonempty)
    (S : Finset (HeightOneSpectrum (𝓞 K))) :
    enlargeByFiniteKummerRadicalSupport
        (K := K) (L := E) n hmu S ⊆
      sUnitKummerAvoidedBasePlaces
        (K := K) (Omega := Omega) E n hmu S := by
  unfold sUnitKummerAvoidedBasePlaces
  dsimp only
  intro w hw
  exact
    Finset.mem_union_left _
      (Finset.mem_union_left _ hw)

end FinitePlaces

end GlobalClassFieldTheory.ClassFieldAxiom
end
end

section
-- module Solutions.OAIQ244_DUKE.GlobalClassFieldTheory_GlobalClassFields_ConductorLocalComparison
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 400000
attribute [-instance] _root_.ClassFormation.DegreeData.FrobeniusFixedFieldTower.extensionNormal _root_.ClassFormation.DegreeData.GaloisSubextension.extensionSubgroup_normalInstance _root_.ClassFormation.FiniteAbstractField.toFiniteResidueAbstractField_extensionNormal _root_.ClassFormation.FiniteCyclicSubextension.instNormalSubtypeMemSubgroupFieldExtensionSubgroupField _root_.ClassFormation.FiniteGaloisSubextension.extensionSubgroup_normalInstance _root_.ClassFormation.FiniteGaloisSubextension.extensionSubgroup_over_intermediate_normalInstance _root_.ClassFormation.FiniteGaloisSubextension.intermediateField_normalInstance _root_.ClassFormation.FiniteIntermediateField.galoisRefinement_normal _root_.ClassFormation.FiniteUnramifiedCyclicExtension.instNormalSubtypeMemSubgroupFieldExtensionSubgroupField _root_.ClassFormation.conjugateExtension_normal _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalClassFieldTheory.extensionSubgroupBase_normal _root_.LocalClassFieldTheory.finiteGaloisExtensionSubgroupOfEmbedding_normal _root_.LocalClassFieldTheory.finiteGaloisLocalField_integerRing_moduleFinite _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.residueFieldZModAlgebra _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedIntegralAlgebraContextValuationSubringAlgebra _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.instTopologicalSpaceLocalAlgebra _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionResidueField.instField _root_.RamificationTheory.HilbertRamification.ValuationSubring.inertiaGroup_normal _root_.RamificationTheory.HilbertRamification.ValuationSubring.ramificationGroupInInertiaAut_normal _root_.RamificationTheory.HilbertRamification.ValuationSubring.selectedResidueField.instAlgebra _root_.ValuationTheory.DiscreteValuationField.DVF.residueField.field _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.ValuationSubring.charP _root_.CyclicCohomology.binaryCoefficientFamilyCommGroup _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.LocalClassFieldTheory.comparisonIntegerRingIsIntegralClosure _root_.LocalClassFieldTheory.normalizationIntegerRingIsIntegralClosure _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.chosenFinitePlaceCompletionAlgebra _root_.relativeUnrestrictedSPlaceFactorCommGroup
attribute [-simp] _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.IdeleGroup.extension_finiteComponent _root_.IdeleGroup.extension_principalIdele _root_.IdeleGroup.extension_self _root_.IdeleGroup.norm_principalIdele _root_.IdeleGroup.norm_relativeIdeleBaseChangeMulEquiv _root_.IsDiscreteValuationRing.addVal_ringEquiv _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.OAI.PrimeDegreePackets.ThetaConstruction.schwartzCM_apply _root_.RayClass.rationalFiniteModulus_apply _root_.finiteIdeleOfSPlaceFactors_apply_mem _root_.finiteIdeleOfSPlaceFactors_apply_notMem _root_.ideleClassCongr_mk _root_.ideleClassExtension_mk _root_.ideleClassExtension_self _root_.ideleClassNorm_mk _root_.ideleCongr_finiteComponent _root_.ideleCongr_principalIdele _root_.ideleSupportedAtEquivSPlaceFactors_infinite _root_.ideleSupportedAtEquivSPlaceFactors_inside _root_.ideleSupportedAtEquivSPlaceFactors_outside_coe _root_.infinitePlace_mult_smul _root_.ordinaryIdeleClassNorm_relativeIdeleClassBaseChange _root_.principalLocalNormQuotientMap_apply _root_.relativeFiniteIdeleMulEquiv_apply _root_.relativeFiniteIdeleToFiniteIdele_apply _root_.relativeIdeleBaseChangeMulEquiv_finite _root_.relativeIdeleBaseChangeMulEquiv_infinite _root_.relativeIdeleBaseChangeMulEquiv_principalIdele _root_.relativeIdeleClassBaseChangeMulEquiv_classInclusion _root_.relativeIdeleClassBaseChangeMulEquiv_mk _root_.relativeIdeleClassCongr_ideleClassNorm _root_.relativeIdeleCongr_norm _root_.towerRelativeIdeleViaOrdinaryMulEquiv_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

/-!
# Narrow finite and local conductor exponents

The narrow finite conductor is the finite component of the conductor in
the all-real-positive convention.  We formulate its local condition
directly inside the idele class group: insert a higher unit at one finite
place and `1` at every other place, then pass to the idele class group.

The proof is constructive.  One inequality follows by restricting any
global defining modulus to one place.  For the reverse inequality, replace
one exponent of a fixed defining modulus by the local minimum and split an
idele into its one-place component and the remaining defining-modulus
component.
-/

open scoped NumberField Classical

noncomputable section

namespace GlobalClassFieldTheory
namespace GlobalClassFields

open NumberField IsDedekindDomain

variable {K : Type*} [Field K] [NumberField K]

/-- If a global defining modulus exists, then at every finite place some
higher-unit class subgroup is already contained in the given subgroup. -/
theorem exists_localDefiningExponent
    (H : Subgroup (IdeleClassGroup K))
    (h : ∃ m, IsDefiningModulus H m)
    (v : HeightOneSpectrum (𝓞 K)) :
    ∃ n : ℕ,
      RayClass.localHigherUnitClassSubgroup v n ≤ H := by
  let m := Classical.choose h
  refine ⟨m.finitePart v, ?_⟩
  exact
    (RayClass.localHigherUnitClassSubgroup_le_congruenceSubgroup
      m v).trans (Classical.choose_spec h)

namespace ConductorialSubgroup

/-- The finite local conductor exponent seen by a conductorial subgroup. -/
noncomputable def narrowFiniteLocalConductorExponent
    (H : ConductorialSubgroup K)
    (v : HeightOneSpectrum (𝓞 K)) : ℕ :=
  Nat.find (exists_localDefiningExponent H.1 H.2 v)

/-- The finite local conductor exponent has its defining higher-unit
inclusion. -/
theorem narrowFiniteLocalConductorExponent_spec
    (H : ConductorialSubgroup K)
    (v : HeightOneSpectrum (𝓞 K)) :
    RayClass.localHigherUnitClassSubgroup v
        (H.narrowFiniteLocalConductorExponent v) ≤ H.1 :=
  Nat.find_spec (exists_localDefiningExponent H.1 H.2 v)

/-- Minimality of the finite local conductor exponent. -/
theorem narrowFiniteLocalConductorExponent_le
    (H : ConductorialSubgroup K)
    (v : HeightOneSpectrum (𝓞 K))
    {n : ℕ}
    (hn : RayClass.localHigherUnitClassSubgroup v n ≤ H.1) :
    H.narrowFiniteLocalConductorExponent v ≤ n := by
  exact Nat.find_min'
    (exists_localDefiningExponent H.1 H.2 v) hn

end ConductorialSubgroup

/-- Replacing one finite exponent of a defining modulus, while retaining its
selected real places, again gives a defining modulus. -/
theorem replaceFiniteExponent_definingModulus
    (H : Subgroup (IdeleClassGroup K))
    (m : RayClass.Modulus K)
    (hm : IsDefiningModulus H m)
    (v : HeightOneSpectrum (𝓞 K))
    (n : ℕ)
    (hn : RayClass.localHigherUnitClassSubgroup v n ≤ H) :
    IsDefiningModulus H
      (m.replaceFinitePart (m.finitePart.update v n)) := by
  let m' : RayClass.Modulus K :=
    m.replaceFinitePart (m.finitePart.update v n)
  change IsDefiningModulus H m'
  let q : IdeleGroup K →* IdeleClassGroup K :=
    QuotientGroup.mk' (IdeleGroup.principalSubgroup K)
  rw [IsDefiningModulus, RayClass.Modulus.congruenceSubgroup,
    Subgroup.map_le_iff_le_comap]
  apply sup_le
  · intro a ha
    have ha' := (RayClass.Modulus.mem_ideleCongruenceSubgroup_iff m' a).1 ha
    let s : IdeleGroup K :=
      IdeleGroup.finitePlaceIdele v (a.2 v)
    let b : IdeleGroup K := a * s⁻¹
    have hav :
        a.2 v ∈ RayClass.localHigherUnitGroup v n := by
      simpa [m', RayClass.Modulus.replaceFinitePart] using ha'.2 v
    have hsH : q s ∈ H := by
      apply hn
      exact ⟨a.2 v, hav, rfl⟩
    have hbCong : b ∈ m.ideleCongruenceSubgroup := by
      rw [RayClass.Modulus.mem_ideleCongruenceSubgroup_iff]
      refine ⟨?_, ?_⟩
      · rw [RayClass.Modulus.mem_infiniteCongruenceSubgroup_iff_local]
        intro w
        have haw :=
          (RayClass.Modulus.mem_infiniteCongruenceSubgroup_iff_local
            m' a.1).1 ha'.1 w
        have hlocal :
            m'.localInfiniteCongruenceSubgroup w =
              m.localInfiniteCongruenceSubgroup w := by
          simp [m']
        rw [hlocal] at haw
        change IdeleGroup.infiniteComponent w b ∈
          m.localInfiniteCongruenceSubgroup w
        dsimp only [b]
        rw [map_mul, map_inv]
        dsimp only [s]
        rw [IdeleGroup.finitePlaceIdele_infiniteComponent,
          inv_one, mul_one]
        exact haw
      · rw [RayClass.mem_finiteCongruenceSubgroup_iff]
        intro w
        by_cases hw : w = v
        · subst w
          change IdeleGroup.finiteComponent v b ∈
            RayClass.localHigherUnitGroup v (m.finitePart v)
          dsimp only [b]
          rw [map_mul, map_inv]
          dsimp only [s]
          rw [IdeleGroup.finitePlaceIdele_finiteComponent_same,
            IdeleGroup.finiteComponent_apply,
            mul_inv_cancel]
          exact Subgroup.one_mem _
        · have haw := ha'.2 w
          have hupdate : (m'.finitePart w) = m.finitePart w := by
            simp [m', RayClass.Modulus.replaceFinitePart, hw]
          rw [hupdate] at haw
          change IdeleGroup.finiteComponent w b ∈
            RayClass.localHigherUnitGroup w (m.finitePart w)
          dsimp only [b]
          rw [map_mul, map_inv]
          dsimp only [s]
          rw [IdeleGroup.finitePlaceIdele_finiteComponent_of_ne
              v w (a.2 v) hw,
            inv_one, mul_one,
            IdeleGroup.finiteComponent_apply]
          exact haw
    have hbH : q b ∈ H := by
      apply hm
      rw [RayClass.Modulus.congruenceSubgroup]
      exact ⟨b, Subgroup.mem_sup_left hbCong, rfl⟩
    have hab : a = b * s := by
      dsimp [b]
      group
    change q a ∈ H
    rw [hab, map_mul]
    exact H.mul_mem hbH hsH
  · intro a ha
    change q a ∈ H
    have hqa : q a = 1 :=
      (QuotientGroup.eq_one_iff a).2 ha
    rw [hqa]
    exact H.one_mem

namespace ConductorialSubgroup

/-- The narrow finite conductor exponent equals the independently defined
finite local conductor exponent at every finite place. -/
theorem narrowFiniteConductorExponent_eq_narrowFiniteLocalConductorExponent
    (H : ConductorialSubgroup K)
    (v : HeightOneSpectrum (𝓞 K)) :
    H.narrowFiniteConductorExponent v =
      H.narrowFiniteLocalConductorExponent v := by
  apply le_antisymm
  · let m := H.chosenDefiningModulus
    have hm : IsDefiningModulus H.1 m :=
      H.chosenDefiningModulus_spec
    have hlocal :
        RayClass.localHigherUnitClassSubgroup v
            (H.narrowFiniteLocalConductorExponent v) ≤ H.1 :=
      H.narrowFiniteLocalConductorExponent_spec v
    have hupdate :
        IsDefiningModulus H.1
          (m.replaceFinitePart
            (m.finitePart.update v
              (H.narrowFiniteLocalConductorExponent v))) :=
      replaceFiniteExponent_definingModulus H.1 m hm v
        (H.narrowFiniteLocalConductorExponent v) hlocal
    have hle :=
      H.narrowFiniteConductorExponent_le hupdate v
    simpa [m, RayClass.Modulus.replaceFinitePart] using hle
  · obtain ⟨m, hm, hmv⟩ :=
      H.narrowFiniteConductorExponent_spec v
    have hlocal :
        RayClass.localHigherUnitClassSubgroup v (m.finitePart v) ≤ H.1 :=
      (RayClass.localHigherUnitClassSubgroup_le_congruenceSubgroup
        m v).trans hm
    exact (H.narrowFiniteLocalConductorExponent_le v hlocal).trans_eq hmv

end ConductorialSubgroup

end GlobalClassFields
end GlobalClassFieldTheory
end
end

section
-- module Solutions.OAIQ244_DUKE.GlobalClassFieldTheory_GlobalClassFields_ConductorInfinitePart
attribute [-instance] _root_.ClassFormation.DegreeData.FrobeniusFixedFieldTower.extensionNormal _root_.ClassFormation.DegreeData.GaloisSubextension.extensionSubgroup_normalInstance _root_.ClassFormation.FiniteAbstractField.toFiniteResidueAbstractField_extensionNormal _root_.ClassFormation.FiniteCyclicSubextension.instNormalSubtypeMemSubgroupFieldExtensionSubgroupField _root_.ClassFormation.FiniteGaloisSubextension.extensionSubgroup_normalInstance _root_.ClassFormation.FiniteGaloisSubextension.extensionSubgroup_over_intermediate_normalInstance _root_.ClassFormation.FiniteGaloisSubextension.intermediateField_normalInstance _root_.ClassFormation.FiniteIntermediateField.galoisRefinement_normal _root_.ClassFormation.FiniteUnramifiedCyclicExtension.instNormalSubtypeMemSubgroupFieldExtensionSubgroupField _root_.ClassFormation.conjugateExtension_normal _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.KummerTheory.nthRootsSubgroupFintype _root_.LocalClassFieldTheory.extensionSubgroupBase_normal _root_.LocalClassFieldTheory.finiteGaloisExtensionSubgroupOfEmbedding_normal _root_.LocalClassFieldTheory.finiteGaloisLocalField_integerRing_moduleFinite _root_.LocalClassFieldTheory.localDecompositionResidueFintype _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.residueFieldZModAlgebra _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedIntegralAlgebraContextValuationSubringAlgebra _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionResidueField.instField _root_.RamificationTheory.HilbertRamification.ValuationSubring.inertiaGroup_normal _root_.RamificationTheory.HilbertRamification.ValuationSubring.ramificationGroupInInertiaAut_normal _root_.RamificationTheory.HilbertRamification.ValuationSubring.selectedResidueField.instAlgebra _root_.ValuationTheory.DiscreteValuationField.DVF.residueField.field _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.ValuationSubring.charP _root_.CyclicCohomology.binaryCoefficientFamilyCommGroup _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.LocalClassFieldTheory.comparisonIntegerRingIsIntegralClosure _root_.LocalClassFieldTheory.normalizationIntegerRingIsIntegralClosure _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.chosenFinitePlaceCompletionAlgebra _root_.relativeUnrestrictedSPlaceFactorCommGroup
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

/-!
# Removing one real place from a defining modulus

This file gives the one-place archimedean step toward the full conductor.
Removing the positivity condition at a real place preserves the defining
property exactly when the whole one-place idèle-class image is already
contained in the target subgroup.
-/

open scoped NumberField Classical

noncomputable section

namespace GlobalClassFieldTheory
namespace GlobalClassFields

open NumberField IsDedekindDomain

variable {K : Type*} [Field K] [NumberField K]

namespace ConductorialSubgroup

/-- The real places whose one-place idèle-class image is not contained in
the target subgroup. -/
noncomputable def fullConductorInfinitePart
    (H : ConductorialSubgroup K) : Finset (RayClass.RealPlace K) :=
  (Finset.univ : Finset (RayClass.RealPlace K)).filter fun v =>
    ¬ (IdeleGroup.infinitePlaceIdeleClass v.1).range ≤ H.1

end ConductorialSubgroup

end GlobalClassFields
end GlobalClassFieldTheory
end
end

section
-- module Solutions.OAIQ244_DUKE.GlobalClassFieldTheory_GlobalClassFields_ConductorLattice
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 400000
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalClassFieldTheory.finiteGaloisLocalField_integerRing_moduleFinite _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.LocalClassFieldTheory.comparisonIntegerRingIsIntegralClosure _root_.LocalClassFieldTheory.normalizationIntegerRingIsIntegralClosure _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

/-!
# Lattice operations on narrow finite conductors

Increasing a modulus decreases its ray congruence subgroup.  This
contravariance makes the narrow finite conductor of an intersection of
norm subgroups the pointwise maximum of their narrow finite conductors.
Under class-field correspondence, this is the finite-part lcm formula
for a compositum.  For a generated subgroup one obtains the
complementary divisibility by the pointwise minimum.
-/

open scoped NumberField Classical

noncomputable section

namespace GlobalClassFieldTheory
namespace GlobalClassFields

open NumberField IsDedekindDomain

variable {K : Type*} [Field K] [NumberField K]

/-- Infinite idèle congruence subgroups are contravariant in the full
modulus: selecting more real places imposes more positivity conditions. -/
theorem rayClassInfiniteCongruenceSubgroup_antitone
    {m n : RayClass.Modulus K} (hmn : m ≤ n) :
    n.infiniteCongruenceSubgroup ≤
      m.infiniteCongruenceSubgroup := by
  intro a ha
  rw [RayClass.Modulus.mem_infiniteCongruenceSubgroup_iff] at ha ⊢
  intro v hv
  exact ha v (hmn.2 hv)

end GlobalClassFields
end GlobalClassFieldTheory
end
end

section
-- module Solutions.OAIQ244_DUKE.LocalField_DiscreteValuationField_PowerIndex
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.DiscreteNthRootsSubgroup.instCommGroupSubtypeUnitsMemSubgroup _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.KummerTheory.finite_finsupp_nsmulQuotient _root_.LocalClassFieldTheory.finiteGaloisLocalField_integerRing_moduleFinite _root_.LocalClassFieldTheory.localSeparableValuationHasExtension _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.AdicPrincipalUnits.instAddCommGroup _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.AdicPrincipalUnits.instTopologicalSpace _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.DiscretePrincipalUnitQuotient.instAddCommGroup _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.DiscretePrincipalUnitQuotient.instDiscreteTopology _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.DiscretePrincipalUnitQuotient.instTopologicalSpace _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitInverseLimitCarrierPadicModule _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitQuotientCarrierPadicModule _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.PrincipalUnitProdiscreteLimit.instAddCommGroup _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.PrincipalUnitProdiscreteLimit.instTopologicalSpace _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.adicPrincipalUnitsT2Space _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitPadicModule _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitPadicSMul _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitProdiscreteLimitT2Space _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.residueFieldZModAlgebra _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedIntegralAlgebraContextValuationSubringAlgebra _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedMaximalIdealPowContextModuleFinite _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedMaximalIdealPowContextModuleFree _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedQPadicContextValuationExtension _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedQPadicContextValuationSubringTower _root_.LocalFieldTheory.DiscreteValuationField.finite_nsmulAddKernel_padicInt_pi _root_.LocalFieldTheory.DiscreteValuationField.finite_padicInt_finPi_nsmulQuotient _root_.LocalFieldTheory.DiscreteValuationField.finite_padicInt_pi_nsmulQuotient_of_coprime _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LubinTate.compatibleGroupFamiliesCommGroup _root_.LubinTate.compatibleGroupFamiliesGroup _root_.LubinTate.standardLubinTateLevelCompleteDVF_hasExtensionInstance _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RamificationTheory.HilbertRamification.Higher.lowerRamificationGroup.instNormal _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.CyclicCohomology.binaryCoefficientFamilyCommGroup _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.LocalClassFieldTheory.comparisonIntegerRingIsIntegralClosure _root_.LocalClassFieldTheory.normalizationIntegerRingIsIntegralClosure _root_.RamificationTheory.HilbertRamification.CompleteDVF.decompositionGroupMulSemiringAction _root_.RamificationTheory.HilbertRamification.CompleteDVF.decompositionGroupResidueFieldMulSemiringAction _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen _root_.infiniteAdeleRingT2Space _root_.relativeUnrestrictedSPlaceFactorCommGroup
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

/-!
# Power-index computations for complete discrete valuation fields

This LubinTate consumer specializes the public commutative-group power-index
API to the unit and principal-unit decompositions of a complete discrete
valuation field.
-/

noncomputable section

open ValuationTheory.DiscreteValuationField
open LocalFieldTheory.DiscreteValuationField
open LocalFieldTheory

namespace LocalFieldTheory.DiscreteValuationField

section CompleteDVF

universe u v

variable {K : Type u} [Field K]

/-- The local-field power-index formula, unit-index form reduced to the analytic principal-unit
input.  If the field-unit structure theorem supplies the principal-unit quotient as its
`n`-torsion kernel times a defect factor `c`, then the same defect multiplies
the full unit `n`-torsion kernel. -/
theorem card_unit_nthPowerQuotient_eq_mul_unitKernel_of_principalUnit_index
    (F : CompleteDVF.{u, v} K) [Finite F.residueField]
    {n c : ℕ} [NeZero n]
    [Finite
      ((LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup F) 1 ⧸
        (powMonoidHom n : ((LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup F) 1) →* ((LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup F) 1)).range)]
    (hprincipal :
      Nat.card
          ((LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup F) 1 ⧸
            (powMonoidHom n : ((LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup F) 1) →* ((LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup F) 1)).range) =
        Nat.card
          ((powMonoidHom n : ((LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup F) 1) →* ((LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup F) 1)).ker) * c) :
    Nat.card (F.valuationSubringˣ ⧸
        (powMonoidHom n : F.valuationSubringˣ →* F.valuationSubringˣ).range) =
      Nat.card ((powMonoidHom n : F.valuationSubringˣ →* F.valuationSubringˣ).ker) * c := by
  rw [card_unit_nthPowerQuotient_eq_mul_rootsKernel_principalUnit_nthPowerQuotient]
  rw [hprincipal]
  rw [card_unit_nthPowerKernel_eq_mul_roots_principalUnit_nthPowerKernel]
  ring

/-- The local-field power-index formula, unit-index form fed directly by a principal-unit logarithm
equivalence and an additive kernel/cokernel calculation. -/
theorem card_unit_nthPowerQuotient_eq_mul_unitKernel_of_logEquiv
    (F : CompleteDVF.{u, v} K) [Finite F.residueField]
    (A : Type*) [AddCommGroup A]
    {n c : ℕ} [NeZero n]
    [Finite
      ((LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup F) 1 ⧸
        (powMonoidHom n : ((LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup F) 1) →* ((LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup F) 1)).range)]
    [Finite (A ⧸ LocalFieldTheory.nsmulAddSubgroup A n)]
    [Finite (LocalFieldTheory.nsmulAddKernel A n)]
    (e : (LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup F) 1 ≃* Multiplicative A)
    (hadd :
      Nat.card (A ⧸ LocalFieldTheory.nsmulAddSubgroup A n) =
        Nat.card (LocalFieldTheory.nsmulAddKernel A n) * c) :
    Nat.card (F.valuationSubringˣ ⧸
        (powMonoidHom n : F.valuationSubringˣ →* F.valuationSubringˣ).range) =
      Nat.card ((powMonoidHom n : F.valuationSubringˣ →* F.valuationSubringˣ).ker) * c :=
  card_unit_nthPowerQuotient_eq_mul_unitKernel_of_principalUnit_index
    (F := F)
    (hprincipal :=
      card_principalUnit_nthPowerQuotient_eq_mul_kernel_of_logEquiv
        (F := F) (A := A) n c e hadd)

end CompleteDVF

end LocalFieldTheory.DiscreteValuationField

end
end

section
-- module Solutions.OAIQ244_DUKE.LocalField_DiscreteValuationField_PadicPowerIndex
attribute [-instance] _root_.ClassFormation.DegreeData.FiniteAbstractExtension.ramificationQuotientFinite _root_.ClassFormation.DegreeData.FiniteAbstractExtension.representedQuotientFinite _root_.ClassFormation.DegreeData.FiniteAbstractExtension.residueQuotientFinite _root_.ClassFormation.DegreeData.FiniteAmbientFrobeniusFixedFieldTower.ambientRepresentedQuotientFinite _root_.ClassFormation.DegreeData.FiniteResidueAbstractExtension.instFiniteQuotientSubtypeMemSubgroupFieldBaseExtensionSubgroupField _root_.ClassFormation.DegreeData.FiniteTower.baseQuotientFinite _root_.ClassFormation.DegreeData.FiniteTower.topQuotientFinite _root_.ClassFormation.DegreeData.FiniteTower.totalQuotientFinite _root_.ClassFormation.DegreeData.FrobeniusFixedFieldTower.baseAbsoluteFiniteInstance _root_.ClassFormation.DegreeData.FrobeniusFixedFieldTower.extensionFinite _root_.ClassFormation.DegreeData.FrobeniusFixedFieldTower.fieldAbsoluteFiniteInstance _root_.ClassFormation.DegreeData.FrobeniusPowerFixedFieldTower.baseRepresentedAbsoluteFinite _root_.ClassFormation.DegreeData.FrobeniusPowerFixedFieldTower.fieldRepresentedAbsoluteFinite _root_.ClassFormation.DegreeData.FrobeniusPowerFixedFieldTower.relativeRepresentedQuotientFinite _root_.ClassFormation.FiniteAbstractField.instFiniteQuotientSubtypeMemSubgroupBaseFieldExtensionSubgroupField _root_.ClassFormation.FiniteAbstractField.toFiniteResidueAbstractField_extensionFinite _root_.ClassFormation.FiniteAbstractFieldExtension.instFiniteQuotientSubtypeMemSubgroupFieldBaseExtensionSubgroupField _root_.ClassFormation.FiniteCyclicSubextension.instFiniteQuotientSubtypeMemSubgroupFieldExtensionSubgroupField _root_.ClassFormation.FiniteUnramifiedCyclicExtension.instFiniteQuotientSubtypeMemSubgroupBaseFieldExtensionSubgroupField _root_.ClassFormation.FiniteUnramifiedCyclicExtension.instFiniteQuotientSubtypeMemSubgroupFieldExtensionSubgroupField _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_isCompleteDiscrete _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.DiscreteNthRootsSubgroup.instCommGroupSubtypeUnitsMemSubgroup _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.KummerTheory.finite_finsupp_nsmulQuotient _root_.KummerTheory.finite_sUnit_nthPowerQuotient _root_.LocalClassFieldTheory.baseFixingExtensionQuotient_finite _root_.LocalClassFieldTheory.baseFixingExtensionQuotient_finite_of_isSeparable _root_.LocalClassFieldTheory.finiteGaloisLocalField_integerRing_moduleFinite _root_.LocalClassFieldTheory.localDecompositionResidueFinite _root_.LocalClassFieldTheory.localSeparableValuationHasExtension _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.AdicPrincipalUnits.instAddCommGroup _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.AdicPrincipalUnits.instTopologicalSpace _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.DiscretePrincipalUnitQuotient.instAddCommGroup _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.DiscretePrincipalUnitQuotient.instDiscreteTopology _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.DiscretePrincipalUnitQuotient.instTopologicalSpace _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitInverseLimitCarrierPadicModule _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitQuotientCarrierPadicModule _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitQuotientCarrier_finite _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.PrincipalUnitProdiscreteLimit.instAddCommGroup _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.PrincipalUnitProdiscreteLimit.instTopologicalSpace _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.adicPrincipalUnitsT2Space _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitPadicModule _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitPadicSMul _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitProdiscreteLimitT2Space _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.residueFieldZModAlgebra _root_.LocalFieldTheory.DiscreteValuationField.Examples.Qp.padicDVRValuation_isCompleteDiscrete _root_.LocalFieldTheory.DiscreteValuationField.Examples.Qp.padicDVRValuation_isRankOneDiscrete _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedIntegralAlgebraContextValuationSubringAlgebra _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedMaximalIdealPowContextModuleFinite _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedMaximalIdealPowContextModuleFree _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedQPadicContextValuationExtension _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedQPadicContextValuationSubringTower _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedWithZeroValuationContextIntegralAlgebra _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LubinTate.compatibleGroupFamiliesCommGroup _root_.LubinTate.compatibleGroupFamiliesGroup _root_.LubinTate.standardLubinTateLevelCompleteDVF_hasExtensionInstance _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.boundedRealFields_finite _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RamificationTheory.HilbertRamification.Higher.lowerRamificationGroup.instNormal _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.CyclicCohomology.binaryCoefficientFamilyCommGroup _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.LocalClassFieldTheory.comparisonIntegerRingIsIntegralClosure _root_.LocalClassFieldTheory.normalizationIntegerRingIsIntegralClosure _root_.RamificationTheory.HilbertRamification.CompleteDVF.decompositionGroupMulSemiringAction _root_.RamificationTheory.HilbertRamification.CompleteDVF.decompositionGroupResidueFieldMulSemiringAction _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen _root_.infiniteAdeleRingT2Space _root_.relativeUnrestrictedSPlaceFactorCommGroup
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

/-!
# The `n`-fold multiple quotient of `Z_p`

This is the free p-adic factor in the local-field structure theory, the local-field power-index formula.
-/

noncomputable section

universe u

open ValuationTheory.DiscreteValuationField
open LocalFieldTheory.DiscreteValuationField
open LocalFieldTheory

namespace LocalFieldTheory.DiscreteValuationField

variable {p : ℕ} [Fact p.Prime]

section LocalFieldIndex

variable {K : Type u} [Field K]

/-- The local-field power-index formula, mixed-characteristic unit-index formula from the same
principal-unit structure theorem. -/
theorem card_units_nthPowerQuotient_of_mixedPrincipalUnitStructure
    (F : CompleteDVF.{u, 0} K) [Finite F.residueField]
    (T : Type*) [AddCommGroup T] [Finite T]
    (d : ℕ) {n : ℕ} [NeZero n]
    [Finite
      ((LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup F) 1 ⧸
        (powMonoidHom n : ((LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup F) 1) →* ((LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup F) 1)).range)]
    (e : (LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup F) 1 ≃*
      Multiplicative (T × (Fin d → ℤ_[p]))) :
    Nat.card (F.valuationSubringˣ ⧸
        (powMonoidHom n : F.valuationSubringˣ →* F.valuationSubringˣ).range) =
      Nat.card ((powMonoidHom n : F.valuationSubringˣ →* F.valuationSubringˣ).ker) *
        p ^ (d * padicValNat p n) := by
  exact card_unit_nthPowerQuotient_eq_mul_unitKernel_of_logEquiv
    (F := F) (A := T × (Fin d → ℤ_[p])) e
      (card_finite_prod_padicInt_finPi_nsmulQuotient_eq_kernel_mul
        (p := p) T d n)

/-- The same mixed-characteristic unit formula with the finite kernel written
as the full field root group `μ_n(K)`. -/
theorem card_units_nthPowerQuotient_of_mixedPrincipalUnitStructure_fieldKernel
    (F : CompleteDVF.{u, 0} K) [Finite F.residueField]
    {π : F.valuationSubring} (hπ : F.valuation.IsUniformizer (π : K))
    (T : Type*) [AddCommGroup T] [Finite T]
    (d : ℕ) {n : ℕ} [NeZero n]
    [Finite
      ((LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup F) 1 ⧸
        (powMonoidHom n : ((LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup F) 1) →* ((LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup F) 1)).range)]
    (e : (LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup F) 1 ≃*
      Multiplicative (T × (Fin d → ℤ_[p]))) :
    Nat.card (F.valuationSubringˣ ⧸
        (powMonoidHom n : F.valuationSubringˣ →* F.valuationSubringˣ).range) =
      Nat.card ((powMonoidHom n : Kˣ →* Kˣ).ker) *
        p ^ (d * padicValNat p n) := by
  rw [card_units_nthPowerQuotient_of_mixedPrincipalUnitStructure
    (p := p) (F := F) T d e]
  rw [card_fieldUnits_nthPowerKernel_eq_unit_nthPowerKernel
    (F := F) hπ n]

/-! The exact equal-characteristic specialization, with no artificial finite
factor in the principal-unit product. -/

end LocalFieldIndex

end LocalFieldTheory.DiscreteValuationField
end
end

section
-- module Solutions.OAIQ244_DUKE.KummerTheory_Concrete_SimpleExtensionLocalBehavior
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.infinitePlaceComplexificationOverfield_algebra _root_.GlobalClassFieldTheory.Reciprocity.infinitePlaceComplexificationOverfield_baseAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalCyclotomicCompletionAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.KummerTheory.primeCyclotomicBaseIsGalois _root_.LocalClassFieldTheory.finiteGaloisLocalField_integerRing_moduleFinite _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.CyclicCohomology.binaryCoefficientFamilyCommGroup _root_.LocalClassFieldTheory.comparisonIntegerRingIsIntegralClosure _root_.LocalClassFieldTheory.normalizationIntegerRingIsIntegralClosure _root_.cyclicPrimeDegreeIntermediate_isGalois _root_.cyclicPrimeSubextension_isGalois _root_.relativeUnrestrictedSPlaceFactorCommGroup
attribute [-simp] _root_.GlobalClassFieldTheory.Reciprocity.rationalCyclotomicGlobalToLocalizedAlgHom_apply _root_.GlobalClassFieldTheory.Reciprocity.rationalCyclotomicGlobalToLocalizedAlgHom_primitiveRoot _root_.IsDiscreteValuationRing.addVal_ringEquiv _root_.OAI.PrimeDegreePackets.ThetaConstruction.schwartzCM_apply _root_.doubleCosetExtension_mk _root_.extendAbsoluteValueExtensionFromIntermediate_apply _root_.finitePlaceTensorRingEquivAboveAdic_apply_extension _root_.finitePlaceTensorUnitsEquivAboveAdic_apply_extension _root_.infinitePlaceAboveEquivExtension_apply_val _root_.infinitePlaceTensorRingEquivAbove_apply _root_.infinitePlaceTensorUnitsEquivAbove_apply _root_.restrictAbsoluteValueExtensionToIntermediate_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

/-!
# Unramified finite places in simple Kummer extensions

This file proves the local unit case of the Kummer ramification criterion.
If both `b` and the exponent `n` are units at a finite place, then the
chosen localization of `K(ⁿ√b) / K` at that place is unramified.

The proof uses the existing algebraic localization, mathlib's minimal
polynomial API, and the complete-DVF different criterion.  No auxiliary
Kummer extension or alternative notion of unramifiedness is introduced.
-/

open scoped NumberField Classical NNReal TensorProduct ValuativeRel
open NumberField IsDedekindDomain
open AlgebraicNumberTheory.Valuations
open HilbertRamification
open LocalFieldTheory
open LocalClassFieldTheory

noncomputable section

namespace KummerTheory

variable {K : Type} [Field K] [NumberField K]

/-- A finite place splits completely in the chosen simple Kummer extension when
the radicand is already an `n`-th power in the completion.  This is the
finite-place splitting source used in the local splitting analysis of simple radical extensions. -/
theorem
    chosenSimpleKummerExtension_finitePlaceSplitsCompletely_of_mem_nthPowerSubgroup
    (n : ℕ+)
    (hnK : ((n : ℕ) : K) ≠ 0)
    (hmu : (primitiveRoots (n : ℕ) K).Nonempty)
    (b : Kˣ)
    (v : HeightOneSpectrum (𝓞 K))
    (hb :
      Units.map
            (algebraMap K (v.adicCompletion K)).toMonoidHom b ∈
        (powMonoidHom (n : ℕ) :
          (v.adicCompletion K)ˣ →*
            (v.adicCompletion K)ˣ).range) :
    let E := chosenSimpleKummerExtension K n hnK b
    letI : FiniteDimensional K E :=
      chosenSimpleKummerExtension_finiteDimensional K n hnK b
    letI : IsAbelianGalois K E :=
      chosenSimpleKummerExtension_isAbelianGalois K n hnK hmu b
    FinitePlaceSplitsCompletely
      (K := K) (L := E) v := by
  let E := chosenSimpleKummerExtension K n hnK b
  let : FiniteDimensional K E :=
    chosenSimpleKummerExtension_finiteDimensional K n hnK b
  let : IsAbelianGalois K E :=
    chosenSimpleKummerExtension_isAbelianGalois K n hnK hmu b
  let beta : Eˣ :=
    chosenSimpleKummerRootUnit K n hnK b
  have hbeta :
      beta ^ (n : ℕ) =
        Units.map (algebraMap K E).toMonoidHom b := by
    dsimp only [E, beta]
    exact chosenSimpleKummerRootUnit_pow K n hnK b
  let D : Subgroup (E ≃ₐ[K] E) :=
    absoluteValueDecompositionGroup K
      (chosenFinitePlaceExtension (L := E) v).1
  have hfixed :
      (beta : E) ∈
        IntermediateField.fixedField D := by
    simpa only [D] using
      (finitePlaceKummerRadicand_mem_nthPowerSubgroup_iff_root_mem_decompositionFixedField
        (K := K) (L := E) v n hmu b beta hbeta).mp hb
  have hgen :
      IntermediateField.adjoin K ({(beta : E)} : Set E) = ⊤ := by
    simpa [E, beta] using
      chosenSimpleKummerExtension_adjoin_root_eq_top K n hnK b
  have hle :
      IntermediateField.adjoin K ({(beta : E)} : Set E) ≤
        IntermediateField.fixedField D := by
    apply IntermediateField.adjoin_le_iff.mpr
    intro x hx
    have hx' : x = (beta : E) :=
      Set.mem_singleton_iff.mp hx
    subst x
    exact hfixed
  have htop :
      IntermediateField.fixedField D = ⊤ := by
    apply top_unique
    rw [← hgen]
    exact hle
  change D = ⊥
  rw [← IntermediateField.fixingSubgroup_fixedField D,
    htop, IntermediateField.fixingSubgroup_top]

end KummerTheory
end
end


