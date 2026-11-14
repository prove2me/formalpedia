-- Prove2me | Definitions.Def_OAIQ244Duke054
-- name    : OAIQ244Duke054
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-13T07:02:49.609204+00:00
-- url     : https://prove2.me/theorems/4cc25526-0a1f-44b1-8c4e-e41aae895a70
-- title:
--   Definitions bundle OAIQ244Duke054 of the split of OpenAI, Equidistribution of Prime-Degree Torus Packets with Arbitrary Local Type
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.DukePrimeDegree.prime_degree_packet_measure_equidistribution_unconditional` and `OAI.DukePrimeDegree.prime_degree_packet_measures_tendsto_haar_unconditional`, carved from OpenAI's openai/math development (OpenAI, *Equidistribution of Prime-Degree Torus Packets with Arbitrary Local Type*, OpenAI Math Release, September 24, 2026, result family 15, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 122 declarations of OpenAI's Lean: 35 definitions, 2 instances and 85 theorems. The definitions and types are `IdeleGroup.extension`, `IdeleGroup.norm`, `RelativeIdeleGroup.classEmbedding`, `RelativeLocalIdeleData.toFiniteData`, `adeleCongr`, `adeleToRelativeAdele`, `adeleToRelativeLocalAdeleData`, `finiteIdeleRelativeTensorFamily`, `finiteIdeleToRelativeFiniteIdeleData`, `finitePlaceAdicCompletionCongrHom`, `ideleClassCongr`, `ideleClassExtension`, `ideleClassNorm`, `ideleCongr`, `infinitePlaceAbovePiRingEquiv`, `intermediateClassNormQuotientBaseChangeMulEquiv`, `intermediateRelativeAdeleBaseChangeAlgEquiv`, `relativeAdeleBaseChangeRingEquiv`, `relativeAdeleCongr`, `relativeAdeleMapOfCompatibleEquiv`, `relativeAdeleToAdele`, `relativeFiniteIdeleEquiv`, `relativeFiniteIdeleMulEquiv`, `relativeFiniteIdeleToFiniteIdele`, `relativeIdeleBaseChangeMulEquiv`, `relativeIdeleClassBaseChangeMulEquiv`, `relativeIdeleClassCongr`, `relativeIdeleCongr`, `relativeInfiniteIdeleMulEquiv`, `relativeInfiniteTensorPiRingEquiv`, `relativeLocalIdeleDataSplitMulEquiv`, `towerActualRelativeAdeleRingEquiv`, `towerRelativeIdeleBaseChangeMulEquiv`, `towerRelativeIdeleClassBaseChangeMulEquiv`, `towerRelativeIdeleViaOrdinaryMulEquiv`.
--
--   **Sources.** They come from these modules of lean/OAI/NumberTheory, in whole or in part: `AlgebraicNumberTheory_AdeleBaseChange`, `AlgebraicNumberTheory_Adele_FiniteRestrictedProductBaseChange`, `AlgebraicNumberTheory_Adele_IntegralTensorSupport_IdeleSupport`, `AlgebraicNumberTheory_Adele_IntegralTensorSupport_LocalTensorDecomposition`, `AlgebraicNumberTheory_Completion_AdicCompletionMap`, `AlgebraicNumberTheory_Idele_BaseChange`, `AlgebraicNumberTheory_Idele_ClassGroup_AlgEquiv`, `AlgebraicNumberTheory_Idele_ClassGroup_NormComparison`, `AlgebraicNumberTheory_Idele_ClassGroup_TowerBaseChange`, `AlgebraicNumberTheory_Idele_Extension_IdealClass`, `AlgebraicNumberTheory_Idele_Extension_IdeleClassBaseChange`, `AlgebraicNumberTheory_Idele_Extension_IdeleNorm`, `LocalField_DiscreteValuationField_MixedCharacteristicStructure_IntegralLattice`.
--
--   **Imports.** It imports the bundles `OAIQ244Duke046` and `OAIQ244Duke047` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ244Duke062`, `OAIQ244Duke063`, `OAIQ244Duke064`, `OAIQ244Duke065`, `OAIQ244Duke066`, `OAIQ244Duke067` and `OAIQ244Duke068`; the statement `OAI.DukePrimeDegree.idealCharacter_kernelLaw_of_even_modulus`.
-- source:
--   OpenAI, Equidistribution of Prime-Degree Torus Packets with Arbitrary Local Type, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 15; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Equidistribution-of-Prime-Degree-Torus-Packets-with-Arbitrary-Local-Type-September-24-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/NumberTheory at commit 7ef5c0c

import Mathlib
import Mathlib.Algebra.Algebra.Basic
import Mathlib.Algebra.Algebra.Pi
import Mathlib.Algebra.Algebra.Tower
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
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Finsupp
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
import Mathlib.FieldTheory.Galois.Basic
import Mathlib.FieldTheory.Galois.Infinite
import Mathlib.FieldTheory.Galois.IsGaloisGroup
import Mathlib.FieldTheory.Galois.NormalBasis
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
import Mathlib.NumberTheory.NumberField.InfinitePlace.Ramification
import Mathlib.NumberTheory.NumberField.ProductFormula
import Mathlib.NumberTheory.NumberField.Units.DirichletTheorem
import Mathlib.NumberTheory.NumberField.Units.Regulator
import Mathlib.NumberTheory.Ostrowski
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
import Mathlib.RingTheory.LocalRing.Basic
import Mathlib.RingTheory.LocalRing.ResidueField.Basic
import Mathlib.RingTheory.Localization.Finiteness
import Mathlib.RingTheory.Nakayama
import Mathlib.RingTheory.Norm.Basic
import Mathlib.RingTheory.Norm.Defs
import Mathlib.RingTheory.Norm.Transitivity
import Mathlib.RingTheory.Polynomial.ContentIdeal
import Mathlib.RingTheory.Polynomial.Cyclotomic.Roots
import Mathlib.RingTheory.Polynomial.GaussLemma
import Mathlib.RingTheory.Polynomial.Vieta
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
import Mathlib.Topology.Algebra.Module.Basic
import Mathlib.Topology.Algebra.Module.Compact
import Mathlib.Topology.Algebra.Module.FiniteDimension
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
import Definitions.Def_OAIQ244Duke046
import Definitions.Def_OAIQ244Duke047

section
-- module Solutions.OAIQ244_DUKE.AlgebraicNumberTheory_Adele_IntegralTensorSupport_LocalTensorDecomposition
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalCyclotomicCompletionAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.residueFieldZModAlgebra _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedIntegralAlgebraContextValuationSubringAlgebra _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.LocalClassFieldTheory.normalizationIntegerRingIsIntegralClosure _root_.chosenFinitePlaceCompletionAlgebra _root_.chosenFinitePlaceCompletionContinuousSMul _root_.chosenFinitePlaceCompletionFiniteDimensional _root_.chosenFinitePlaceCompletionLocallyCompactSpace _root_.chosenFinitePlaceLocalizedFiniteDimensional _root_.chosenFinitePlaceLocalizedIntegerAlgebra _root_.chosenFinitePlaceLocalizedIntegerModuleFinite _root_.chosenFinitePlaceLocalizedIsGalois _root_.chosenFinitePlaceLocalizedIsIntegralClosure _root_.chosenFinitePlaceLocalizedIsNonarchimedeanLocalField _root_.chosenFinitePlaceLocalizedIsValuativeTopology _root_.chosenFinitePlaceLocalizedLocallyCompactSpace _root_.chosenFinitePlaceLocalizedValuationCompatible _root_.chosenFinitePlaceLocalizedValuationHasExtension _root_.chosenFinitePlaceLocalizedValuationIsNontrivial _root_.chosenFinitePlaceLocalizedValuativeRel _root_.chosenFinitePlaceLocalizedValuativeRelIsNontrivial _root_.chosenFinitePlaceLocalizedValued
attribute [-simp] _root_.GlobalClassFieldTheory.Reciprocity.rationalCyclotomicGlobalToLocalizedAlgHom_apply _root_.GlobalClassFieldTheory.Reciprocity.rationalCyclotomicGlobalToLocalizedAlgHom_primitiveRoot _root_.IsDiscreteValuationRing.addVal_ringEquiv _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.OAI.PrimeDegreePackets.ThetaConstruction.schwartzCM_apply _root_.doubleCosetExtension_mk _root_.extendAbsoluteValueExtensionFromIntermediate_apply _root_.finitePlaceBelow_finitePlaceExtensionCentre _root_.finitePlaceExtensionAdicCompletionRingEquiv_toCompletion _root_.finitePlaceExtensionCentreInFibre_coe _root_.finitePlaceExtensionCentre_asIdeal _root_.finitePlaceExtensionCompletionRingEquiv_toCompletion _root_.finitePlaceExtensionEquivAbove_coe _root_.finitePlaceLocalTensorDecompositionComponentRingHom_apply _root_.finitePlaceLocalTensorDecompositionComponent_add _root_.finitePlaceLocalTensorDecompositionComponent_zero _root_.finitePlaceLocalTensorDecompositionUnitsComponent_coe _root_.finitePlaceLocalTensorDecompositionUnitsEquiv_apply _root_.finitePlaceTensorRingEquivAboveAdic_apply_extension _root_.finitePlaceTensorUnitsEquivAboveAdic_apply_extension _root_.infinitePlaceAboveEquivExtension_apply_val _root_.infinitePlaceTensorRingEquivAbove_apply _root_.infinitePlaceTensorUnitsEquivAbove_apply _root_.infinitePlace_mult_smul _root_.mem_finitePlaceDecompositionGroup_iff _root_.mem_relativeIdeleLocalTensorDecompositionSupport_iff _root_.mem_relativeIdeleLocalTensorDecompositionSupportedSubgroup_iff _root_.mem_relativeLocalTensorDecompositionIntegralUnitSubgroup_iff _root_.relativeAdeleCoefficientLinearEquiv_apply _root_.relativeAdeleCoefficient_ofCoefficients _root_.relativeAdeleFiniteComponent_basis_repr _root_.relativeAdeleInfiniteComponent_basis_repr _root_.relativeLocalAdeleCoefficient_finite _root_.relativeLocalAdeleCoefficient_infinite _root_.restrictAbsoluteValueExtensionToIntermediate_apply _root_.ringOfIntegersToFinitePlaceExtensionValuationSubring_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

/-!
# Integral comparison for local tensor decompositions

This module identifies integrality and units in a finite-place tensor factor
with the corresponding componentwise conditions in the completions above that
place.
-/

open scoped NumberField TensorProduct NNReal
open NumberField IsDedekindDomain

noncomputable section

open AlgebraicNumberTheory.Valuations

universe u v

variable
    {K : Type u} {L : Type v}
    [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L]

section LocalTensorDecompositionIntegralComparison

/-- The chosen-basis integral lattice maps into the actual product of
completion valuation rings under the local tensor decomposition, away from the finite
bad set. -/
theorem relativeBasisIntegralAt_imp_localTensorDecompositionIntegral_of_notMem
    (w : HeightOneSpectrum (𝓞 K))
    (hw : w ∉ integralTensorBadPlaces
      (K := K) (L := L))
    {x : w.adicCompletion K ⊗[K] L}
    (hx : RelativeBasisIntegralAt
      (K := K) (L := L) w x) :
    RelativeLocalTensorDecompositionIntegralAt
      (K := K) (L := L) w x := by
  obtain ⟨c, rfl⟩ := hx
  intro wL
  have hsum :
      finitePlaceLocalTensorDecompositionComponent
          (K := K) (L := L) w wL
          (∑ i : RelativeAdeleBasisIndex
              (K := K) (L := L),
            ((c i : w.adicCompletionIntegers K) :
                w.adicCompletion K) ⊗ₜ[K]
              relativeExtensionBasis
                (K := K) (L := L) i) =
        ∑ i : RelativeAdeleBasisIndex
            (K := K) (L := L),
          finitePlaceLocalTensorDecompositionComponent
            (K := K) (L := L) w wL
            (((c i : w.adicCompletionIntegers K) :
                w.adicCompletion K) ⊗ₜ[K]
              relativeExtensionBasis
                (K := K) (L := L) i) := by
    simp [finitePlaceLocalTensorDecompositionComponent]
  rw [hsum]
  apply Subring.sum_mem
  intro i hi
  rw [finitePlaceLocalTensorDecompositionComponent_tmul]
  apply
    (absoluteValueCompletionIntegers wL.1
      (absoluteValueExtension_isNonarchimedean
        (NumberField.HeightOneSpectrum.adicAbv K w)
        (NumberField.HeightOneSpectrum.isNonarchimedean_adicAbv
          K w) wL)).mul_mem
  · exact
      finitePlaceLocalTensorDecomposition_coefficient_mem_integers
        (K := K) (L := L) w wL (c i)
  · exact
      finitePlaceLocalTensorDecomposition_basis_mem_integers_of_notMem
        (K := K) (L := L) w hw wL i

/-- Consequently, basis integrality of a tensor unit and its inverse
is genuine integrality in every local tensor factor. -/
theorem relativeBasisIntegralUnitAt_imp_localTensorDecompositionIntegralUnit_of_notMem
    (w : HeightOneSpectrum (𝓞 K))
    (hw : w ∉ integralTensorBadPlaces
      (K := K) (L := L))
    {x : (w.adicCompletion K ⊗[K] L)ˣ}
    (hx : RelativeBasisIntegralUnitAt
      (K := K) (L := L) w x) :
    RelativeLocalTensorDecompositionIntegralUnitAt
      (K := K) (L := L) w x :=
  ⟨relativeBasisIntegralAt_imp_localTensorDecompositionIntegral_of_notMem
      (K := K) (L := L) w hw hx.1,
    relativeBasisIntegralAt_imp_localTensorDecompositionIntegral_of_notMem
      (K := K) (L := L) w hw hx.2⟩

/-- Away from one explicit finite bad set, basis integrality is
equivalent to integrality in every local tensor factor. -/
theorem relativeBasisIntegralAt_iff_localTensorDecompositionIntegral_of_notMem
    (w : HeightOneSpectrum (𝓞 K))
    (hw : w ∉ integralTensorComparisonBadPlaces
      (K := K) (L := L))
    {x : w.adicCompletion K ⊗[K] L} :
    RelativeBasisIntegralAt (K := K) (L := L) w x ↔
      RelativeLocalTensorDecompositionIntegralAt (K := K) (L := L) w x := by
  have hwold : w ∉ integralTensorBadPlaces (K := K) (L := L) := by
    intro hw'
    exact hw (by
      simp [integralTensorComparisonBadPlaces, hw'])
  exact
    ⟨relativeBasisIntegralAt_imp_localTensorDecompositionIntegral_of_notMem
        (K := K) (L := L) w hwold,
      localTensorDecompositionIntegral_imp_relativeBasisIntegralAt_of_notMem
        (K := K) (L := L) w hw⟩

/-- Unit version of the local tensor integral comparison. -/
theorem relativeBasisIntegralUnitAt_iff_localTensorDecompositionIntegralUnit_of_notMem
    (w : HeightOneSpectrum (𝓞 K))
    (hw : w ∉ integralTensorComparisonBadPlaces
      (K := K) (L := L))
    {x : (w.adicCompletion K ⊗[K] L)ˣ} :
    RelativeBasisIntegralUnitAt (K := K) (L := L) w x ↔
      RelativeLocalTensorDecompositionIntegralUnitAt (K := K) (L := L) w x := by
  have hwold : w ∉ integralTensorBadPlaces (K := K) (L := L) := by
    intro hw'
    exact hw (by
      simp [integralTensorComparisonBadPlaces, hw'])
  exact
    ⟨relativeBasisIntegralUnitAt_imp_localTensorDecompositionIntegralUnit_of_notMem
        (K := K) (L := L) w hwold,
      localTensorDecompositionIntegralUnit_imp_relativeBasisIntegralUnitAt_of_notMem
        (K := K) (L := L) w hw⟩

end LocalTensorDecompositionIntegralComparison
end
end

section
-- module Solutions.OAIQ244_DUKE.AlgebraicNumberTheory_Adele_IntegralTensorSupport_IdeleSupport
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.residueFieldZModAlgebra _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedIntegralAlgebraContextValuationSubringAlgebra _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.LocalClassFieldTheory.normalizationIntegerRingIsIntegralClosure _root_.chosenFinitePlaceCompletionAlgebra
attribute [-simp] _root_.IsDiscreteValuationRing.addVal_ringEquiv _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.OAI.PrimeDegreePackets.ThetaConstruction.schwartzCM_apply _root_.infinitePlace_mult_smul _root_.mem_relativeIdeleLocalTensorDecompositionSupportedSubgroup_iff _root_.mem_relativeLocalTensorDecompositionIntegralUnitSubgroup_iff _root_.relativeAdeleCoefficientLinearEquiv_apply _root_.relativeAdeleCoefficient_ofCoefficients _root_.relativeAdeleFiniteComponent_basis_repr _root_.relativeAdeleInfiniteComponent_basis_repr _root_.relativeAdeleOfCoefficients_coefficients _root_.relativeAdeleOfLocalData_finiteComponent _root_.relativeAdeleOfLocalData_infiniteComponent _root_.relativeIdeleLocalComponents_finite _root_.relativeIdeleLocalComponents_infinite _root_.relativeIdeleLocalTensorDecompositionSupportedSubgroupAction_coe _root_.relativeIdeleMulEquivLocalData_apply _root_.relativeIdeleOfLocalData_finiteComponent _root_.relativeIdeleOfLocalData_infiniteComponent _root_.relativeIdeleOfLocalData_toLocalData _root_.relativeIdeleOfSPlaceFactors_finiteComponent_inside _root_.relativeIdeleOfSPlaceFactors_finiteComponent_outside _root_.relativeIdeleOfSPlaceFactors_infiniteComponent _root_.relativeIdeleSupportedComponents_infinite _root_.relativeIdeleSupportedComponents_inside _root_.relativeIdeleSupportedComponents_outside_coe _root_.relativeLocalAdeleCoefficient_finite _root_.relativeLocalAdeleCoefficient_infinite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

/-!
# Finite support for integral relative ideles

This module combines coefficient support with the exceptional places of the
local tensor decomposition, producing one finite set that controls integrality
of a relative idele and its inverse.
-/

open scoped NumberField TensorProduct NNReal
open NumberField IsDedekindDomain

noncomputable section

open AlgebraicNumberTheory.Valuations

universe u v

variable
    {K : Type u} {L : Type v}
    [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L]

/-- Outside one explicit finite support, the actual finite component of
a relative idele and its inverse are units in every valuation-ring
factor of the local tensor decomposition. -/
theorem relativeIdele_finiteComponent_localTensorDecompositionIntegralUnit_of_notMem
    (z : RelativeIdeleGroup K L)
    (w : HeightOneSpectrum (𝓞 K))
    (hw : w ∉ relativeIdeleLocalTensorDecompositionSupport
      (K := K) (L := L) z) :
    RelativeLocalTensorDecompositionIntegralUnitAt
      (K := K) (L := L) w
      (RelativeIdeleGroup.finiteComponent
        (K := K) (L := L) w z) := by
  have hsep :
      w ∉ relativeIdeleCoefficientSupport
          (K := K) (L := L) z ∧
        w ∉ integralTensorBadPlaces
          (K := K) (L := L) := by
    simpa [relativeIdeleLocalTensorDecompositionSupport] using hw
  exact
    relativeBasisIntegralUnitAt_imp_localTensorDecompositionIntegralUnit_of_notMem
      (K := K) (L := L) w hsep.2
      (relativeIdele_finiteComponent_basisIntegralUnit_of_notMem
        (K := K) (L := L) z w hsep.1)
end
end

section
-- module Solutions.OAIQ244_DUKE.AlgebraicNumberTheory_Completion_AdicCompletionMap
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.residueFieldZModAlgebra _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedIntegralAlgebraContextValuationSubringAlgebra _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.OAI.PrimeDegreePackets.xT2Space _root_.LocalClassFieldTheory.normalizationIntegerRingIsIntegralClosure _root_.chosenFinitePlaceBaseIsUltrametricDist _root_.chosenFinitePlaceBaseValued _root_.chosenFinitePlaceCompletionAlgebra
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

/-!
# The canonical map between adic completions

A finite place above a base finite place determines the continuous
extension of the number-field algebra map to their concrete adic
completions.
-/

open scoped NumberField
open NumberField IsDedekindDomain

noncomputable section

universe u v w

variable
    (K : Type u) (L : Type v)
    [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]

/-- Canonical maps between concrete adic completions compose in a
number-field tower. -/
theorem finitePlaceAdicCompletionMap_comp
    {M : Type w}
    [Field M] [NumberField M]
    [Algebra K M] [Algebra M L]
    [IsScalarTower K M L]
    (vK : HeightOneSpectrum (𝓞 K))
    (vM : HeightOneSpectrum (𝓞 M))
    (vL : HeightOneSpectrum (𝓞 L))
    (hMK : finitePlaceBelow (K := K) vM = vK)
    (hLM : finitePlaceBelow (K := M) vL = vM)
    (hLK : finitePlaceBelow (K := K) vL = vK)
    (x : vK.adicCompletion K) :
    finitePlaceAdicCompletionMap M L vM ⟨vL, hLM⟩
        (finitePlaceAdicCompletionMap K M vK ⟨vM, hMK⟩ x) =
      finitePlaceAdicCompletionMap K L vK ⟨vL, hLK⟩ x := by
  let P : (vK.valuation K).Completion → Prop := fun y =>
    finitePlaceAdicCompletionMap M L vM ⟨vL, hLM⟩
        (finitePlaceAdicCompletionMap K M vK ⟨vM, hMK⟩
          (HeightOneSpectrum.adicCompletion.ofCompletion y)) =
      finitePlaceAdicCompletionMap K L vK ⟨vL, hLK⟩
        (HeightOneSpectrum.adicCompletion.ofCompletion y)
  change P x.toCompletion
  refine UniformSpace.Completion.induction_on
    (α := WithVal (vK.valuation K)) x.toCompletion ?_ ?_
  · exact isClosed_eq
      ((finitePlaceAdicCompletionMap_continuous
          M L vM ⟨vL, hLM⟩).comp
        ((finitePlaceAdicCompletionMap_continuous
            K M vK ⟨vM, hMK⟩).comp
          (HeightOneSpectrum.adicCompletion.continuous_ofCompletion K vK)))
      ((finitePlaceAdicCompletionMap_continuous
          K L vK ⟨vL, hLK⟩).comp
        (HeightOneSpectrum.adicCompletion.continuous_ofCompletion K vK))
  · intro r
    let k : K := WithVal.equiv (vK.valuation K) r
    change
      finitePlaceAdicCompletionMap M L vM ⟨vL, hLM⟩
          (finitePlaceAdicCompletionMap K M vK ⟨vM, hMK⟩
            (k : vK.adicCompletion K)) =
        finitePlaceAdicCompletionMap K L vK ⟨vL, hLK⟩
          (k : vK.adicCompletion K)
    rw [finitePlaceAdicCompletionMap_coe
        K M vK ⟨vM, hMK⟩ k,
      finitePlaceAdicCompletionMap_coe
        M L vM ⟨vL, hLM⟩ (algebraMap K M k),
      finitePlaceAdicCompletionMap_coe
        K L vK ⟨vL, hLK⟩ k,
      IsScalarTower.algebraMap_apply K M L]
end
end

section
-- module Solutions.OAIQ244_DUKE.AlgebraicNumberTheory_Adele_FiniteRestrictedProductBaseChange
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalCyclotomicCompletionAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.residueFieldZModAlgebra _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedIntegralAlgebraContextValuationSubringAlgebra _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.LocalClassFieldTheory.normalizationIntegerRingIsIntegralClosure _root_.chosenFinitePlaceCompletionAlgebra _root_.chosenFinitePlaceCompletionContinuousSMul _root_.chosenFinitePlaceCompletionFiniteDimensional _root_.chosenFinitePlaceCompletionLocallyCompactSpace _root_.chosenFinitePlaceLocalizedFiniteDimensional _root_.chosenFinitePlaceLocalizedIntegerAlgebra _root_.chosenFinitePlaceLocalizedIntegerModuleFinite _root_.chosenFinitePlaceLocalizedIsGalois _root_.chosenFinitePlaceLocalizedIsIntegralClosure _root_.chosenFinitePlaceLocalizedIsNonarchimedeanLocalField _root_.chosenFinitePlaceLocalizedIsValuativeTopology _root_.chosenFinitePlaceLocalizedLocallyCompactSpace _root_.chosenFinitePlaceLocalizedValuationCompatible _root_.chosenFinitePlaceLocalizedValuationHasExtension _root_.chosenFinitePlaceLocalizedValuationIsNontrivial _root_.chosenFinitePlaceLocalizedValuativeRel _root_.chosenFinitePlaceLocalizedValuativeRelIsNontrivial _root_.chosenFinitePlaceLocalizedValued
attribute [-simp] _root_.IsDiscreteValuationRing.addVal_ringEquiv _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.OAI.PrimeDegreePackets.ThetaConstruction.schwartzCM_apply _root_.finiteIdeleOfSPlaceFactors_apply_mem _root_.finiteIdeleOfSPlaceFactors_apply_notMem _root_.finitePlaceAdicCompletionMap_self_apply _root_.finitePlaceTensorRingEquivAboveAdic_apply_extension _root_.ideleSupportedAtEquivSPlaceFactors_infinite _root_.ideleSupportedAtEquivSPlaceFactors_inside _root_.ideleSupportedAtEquivSPlaceFactors_outside_coe _root_.relativeFiniteTensorPiRingEquiv_apply _root_.relativeFiniteTensorPiRingEquiv_symm_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

/-!
# Finite restricted products under scalar extension

This file flattens the finite local tensor factors of a relative idele over
`K` into the ordinary finite-place factors of `L`.  The local map is
The canonical local tensor decomposition followed by the comparison between an exact-extension
completion and the concrete adic completion at its centre.

The main point is restrictedness: coefficientwise restrictedness in a fixed
`K`-basis of `L` is equivalent, up to the already isolated finite comparison
set, to the usual valuation-ring-unit condition at almost every finite place
of `L`.
-/

open scoped NumberField TensorProduct RestrictedProduct
open NumberField IsDedekindDomain

noncomputable section


open AlgebraicNumberTheory.Valuations

universe u v

variable
    {K : Type u} {L : Type v}
    [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L]

/-- On a diagonal extension-field unit, the finite local
relative-to-ordinary comparison is the ordinary diagonal embedding. -/
theorem finitePlaceTensorUnitsEquivAboveAdic_localFieldIdeleInclusion
    (w : HeightOneSpectrum (𝓞 K))
    (W : {W : HeightOneSpectrum (𝓞 L) //
      finitePlaceBelow (K := K) W = w})
    (x : Lˣ) :
    finitePlaceTensorUnitsEquivAboveAdic
        (K := K) (L := L) w
        (localFieldIdeleInclusion
          (K := K) (L := L) w x) W =
      Units.map
        (FinitePlace.embedding (K := L) W.1)
        x := by
  obtain ⟨a, rfl⟩ :=
    (finitePlaceExtensionEquivAbove
      (K := K) (L := L) w).surjective W
  rw [finitePlaceTensorUnitsEquivAboveAdic_apply_extension]
  apply Units.ext
  simp only [Units.coe_map]
  change
    finitePlaceExtensionAdicCompletionRingEquiv
        (K := K) (L := L) w a
        (finitePlaceLocalTensorDecompositionComponent
          (K := K) (L := L) w a
          (1 ⊗ₜ[K] (x : L))) =
      FinitePlace.embedding
        (finitePlaceExtensionCentre
          (K := K) (L := L) w a)
        (x : L)
  rw [finitePlaceLocalTensorDecompositionComponent_tmul]
  simp only [map_one, one_mul,
    finitePlaceExtensionAdicCompletionRingEquiv_toCompletion]

/-- The local tensor unit is integral in every relative-tensor factor
exactly when its flattened concrete components are local integer units at
every finite place above the base place. -/
theorem relativeLocalTensorDecompositionIntegralUnitAt_iff_aboveAdic
    (w : HeightOneSpectrum (𝓞 K))
    (x : (w.adicCompletion K ⊗[K] L)ˣ) :
    RelativeLocalTensorDecompositionIntegralUnitAt
        (K := K) (L := L) w x ↔
      ∀ W : {W : HeightOneSpectrum (𝓞 L) //
          finitePlaceBelow (K := K) W = w},
        finitePlaceTensorUnitsEquivAboveAdic
            (K := K) (L := L) w x W ∈
          (W.1.adicCompletionIntegers L).units := by
  rw [relativeLocalTensorDecompositionIntegralUnitAt_iff]
  constructor
  · intro hx W
    let u :=
      (finitePlaceExtensionEquivAbove
        (K := K) (L := L) w).symm W
    have hW :
        finitePlaceExtensionEquivAbove
            (K := K) (L := L) w u = W :=
      (finitePlaceExtensionEquivAbove
        (K := K) (L := L) w).apply_symm_apply W
    rw [← hW]
    rw [finitePlaceTensorUnitsEquivAboveAdic_apply_extension]
    exact
      (unitsMapEquiv_mem_units_iff
        (finitePlaceExtensionAdicCompletionRingEquiv
          (K := K) (L := L) w u).toMulEquiv
        (absoluteValueCompletionIntegers u.1
          (absoluteValueExtension_isNonarchimedean
            (HeightOneSpectrum.adicAbv K w)
            (HeightOneSpectrum.isNonarchimedean_adicAbv K w) u)).toSubmonoid
        ((finitePlaceExtensionCentre
          (K := K) (L := L) w u).adicCompletionIntegers L).toSubmonoid
        (finitePlaceExtensionAdicCompletionRingEquiv_mem_integers_iff
          (K := K) (L := L) w u)
        (finitePlaceLocalTensorDecompositionUnitsComponent
          (K := K) (L := L) w u x)).2 (hx u)
  · intro hx u
    have h :=
      hx (finitePlaceExtensionEquivAbove
        (K := K) (L := L) w u)
    rw [finitePlaceTensorUnitsEquivAboveAdic_apply_extension] at h
    exact
      (unitsMapEquiv_mem_units_iff
        (finitePlaceExtensionAdicCompletionRingEquiv
          (K := K) (L := L) w u).toMulEquiv
        (absoluteValueCompletionIntegers u.1
          (absoluteValueExtension_isNonarchimedean
            (HeightOneSpectrum.adicAbv K w)
            (HeightOneSpectrum.isNonarchimedean_adicAbv K w) u)).toSubmonoid
        ((finitePlaceExtensionCentre
          (K := K) (L := L) w u).adicCompletionIntegers L).toSubmonoid
        (finitePlaceExtensionAdicCompletionRingEquiv_mem_integers_iff
          (K := K) (L := L) w u)
        (finitePlaceLocalTensorDecompositionUnitsComponent
          (K := K) (L := L) w u x)).1 h

/-- A finite relative restricted family is integral in every concrete
completion factor over almost every base finite place. -/
theorem RelativeFiniteIdeleData.eventually_aboveAdicUnit
    (a : RelativeFiniteIdeleData (K := K) (L := L)) :
    ∀ᶠ w : HeightOneSpectrum (𝓞 K) in Filter.cofinite,
      ∀ W : {W : HeightOneSpectrum (𝓞 L) //
          finitePlaceBelow (K := K) W = w},
        finitePlaceTensorUnitsEquivAboveAdic
            (K := K) (L := L) w (a.finite w) W ∈
          (W.1.adicCompletionIntegers L).units := by
  let z : RelativeIdeleGroup K L :=
    relativeIdeleOfLocalData
      (K := K) (L := L) a.toLocalData
  filter_upwards [
    (relativeIdeleLocalTensorDecompositionSupport
      (K := K) (L := L) z).eventually_cofinite_notMem] with w hw
  apply
    (relativeLocalTensorDecompositionIntegralUnitAt_iff_aboveAdic
      (K := K) (L := L) w (a.finite w)).mp
  have hz :=
    relativeIdele_finiteComponent_localTensorDecompositionIntegralUnit_of_notMem
      (K := K) (L := L) z w hw
  simpa [z, RelativeFiniteIdeleData.toLocalData] using hz

/-- Flatten a finite relative restricted family into an ordinary finite
idele of `L`. -/
noncomputable def relativeFiniteIdeleToFiniteIdele
    (a : RelativeFiniteIdeleData (K := K) (L := L)) :
    FiniteIdeleGroup L :=
  ⟨relativeFiniteTensorPiMulEquiv
      (K := K) (L := L) a.finite,
    (eventually_finitePlace_iff_eventually_all_above
      (K := K) (L := L)
      (fun W =>
        relativeFiniteTensorPiMulEquiv
            (K := K) (L := L) a.finite W ∈
          (W.adicCompletionIntegers L).units)).mpr <| by
      filter_upwards [a.eventually_aboveAdicUnit] with w hw
      intro W
      rcases W with ⟨W, hW⟩
      subst w
      exact hw ⟨W, rfl⟩⟩

/-- Evaluation of the map from relative finite idele data to finite
ideles. -/
@[simp]
theorem relativeFiniteIdeleToFiniteIdele_apply
    (a : RelativeFiniteIdeleData (K := K) (L := L))
    (W : HeightOneSpectrum (𝓞 L)) :
    relativeFiniteIdeleToFiniteIdele
        (K := K) (L := L) a W =
      relativeFiniteTensorPiMulEquiv
        (K := K) (L := L) a.finite W :=
  rfl

/-- Pull an ordinary finite idele back to the unrestricted family of
finite tensor-unit factors. -/
noncomputable def finiteIdeleRelativeTensorFamily
    (y : FiniteIdeleGroup L) :
    ∀ w : HeightOneSpectrum (𝓞 K),
      (w.adicCompletion K ⊗[K] L)ˣ :=
  (relativeFiniteTensorPiMulEquiv
    (K := K) (L := L)).symm (fun W => y W)

/-- The pulled-back tensor family is basis-integral, together with its
inverse, at almost every finite place of `K`. -/
theorem finiteIdeleRelativeTensorFamily_eventually_basisIntegralUnit
    (y : FiniteIdeleGroup L) :
    ∀ᶠ w : HeightOneSpectrum (𝓞 K) in Filter.cofinite,
      RelativeBasisIntegralUnitAt
        (K := K) (L := L) w
        (finiteIdeleRelativeTensorFamily
          (K := K) (L := L) y w) := by
  have habove :
      ∀ᶠ w : HeightOneSpectrum (𝓞 K) in Filter.cofinite,
        ∀ W : {W : HeightOneSpectrum (𝓞 L) //
            finitePlaceBelow (K := K) W = w},
          y W.1 ∈ (W.1.adicCompletionIntegers L).units :=
    (eventually_finitePlace_iff_eventually_all_above
      (K := K) (L := L)
      (fun W => y W ∈
        (W.adicCompletionIntegers L).units)).mp
      (FiniteIdeleGroup.eventually_mem_localUnits y)
  filter_upwards [
    habove,
    (integralTensorComparisonBadPlaces
      (K := K) (L := L)).eventually_cofinite_notMem] with w hw hbad
  apply
    (relativeBasisIntegralUnitAt_iff_localTensorDecompositionIntegralUnit_of_notMem
      (K := K) (L := L) w hbad).mpr
  apply
    (relativeLocalTensorDecompositionIntegralUnitAt_iff_aboveAdic
      (K := K) (L := L) w
      (finiteIdeleRelativeTensorFamily
        (K := K) (L := L) y w)).mpr
  intro W
  have hcomponent :=
    congrFun
      ((finitePlaceTensorUnitsEquivAboveAdic
        (K := K) (L := L) w).apply_symm_apply
          (fun W => y W.1)) W
  rw [finiteIdeleRelativeTensorFamily,
    relativeFiniteTensorPiMulEquiv_symm_apply,
    hcomponent]
  exact hw W

/-- Pull an ordinary finite idele back to finite relative restricted
data. -/
noncomputable def finiteIdeleToRelativeFiniteIdeleData
    (y : FiniteIdeleGroup L) :
    RelativeFiniteIdeleData (K := K) (L := L) where
  finite :=
    finiteIdeleRelativeTensorFamily
      (K := K) (L := L) y
  eventually_integral i :=
    (finiteIdeleRelativeTensorFamily_eventually_basisIntegralUnit
      (K := K) (L := L) y).mono fun w hw =>
        relativeBasisIntegralAt_repr_mem
          (K := K) (L := L) w _ hw.1 i
  eventually_inverse_integral i :=
    (finiteIdeleRelativeTensorFamily_eventually_basisIntegralUnit
      (K := K) (L := L) y).mono fun w hw =>
        relativeBasisIntegralAt_repr_mem
          (K := K) (L := L) w _ hw.2 i

/-- The finite relative restricted product is the ordinary finite idele
group of the extension field. -/
noncomputable def relativeFiniteIdeleEquiv :
    RelativeFiniteIdeleData (K := K) (L := L) ≃
      FiniteIdeleGroup L where
  toFun :=
    relativeFiniteIdeleToFiniteIdele
      (K := K) (L := L)
  invFun :=
    finiteIdeleToRelativeFiniteIdeleData
      (K := K) (L := L)
  left_inv a := by
    apply RelativeFiniteIdeleData.ext
    change
      (relativeFiniteTensorPiMulEquiv
        (K := K) (L := L)).symm
          (relativeFiniteTensorPiMulEquiv
            (K := K) (L := L) a.finite) =
        a.finite
    exact
      (relativeFiniteTensorPiMulEquiv
        (K := K) (L := L)).symm_apply_apply a.finite
  right_inv y := by
    apply Subtype.ext
    change
      relativeFiniteTensorPiMulEquiv
          (K := K) (L := L)
          ((relativeFiniteTensorPiMulEquiv
            (K := K) (L := L)).symm (fun W => y W)) =
        fun W => y W
    exact
      (relativeFiniteTensorPiMulEquiv
        (K := K) (L := L)).apply_symm_apply (fun W => y W)

/-- The transported group structure on the finite relative restricted
product. -/
noncomputable instance relativeFiniteIdeleDataGroup :
    Group (RelativeFiniteIdeleData (K := K) (L := L)) :=
  (relativeFiniteIdeleEquiv
    (K := K) (L := L)).group

/-- The finite restricted-product comparison as a multiplicative
equivalence. -/
noncomputable def relativeFiniteIdeleMulEquiv :
    RelativeFiniteIdeleData (K := K) (L := L) ≃*
      FiniteIdeleGroup L :=
  (relativeFiniteIdeleEquiv
    (K := K) (L := L)).mulEquiv

/-- The relative finite idele equivalence agrees with the underlying
finite-idele map. -/
@[simp]
theorem relativeFiniteIdeleMulEquiv_apply
    (a : RelativeFiniteIdeleData (K := K) (L := L)) :
    relativeFiniteIdeleMulEquiv
        (K := K) (L := L) a =
      relativeFiniteIdeleToFiniteIdele
        (K := K) (L := L) a :=
  rfl
end
end

section
-- module Solutions.OAIQ244_DUKE.AlgebraicNumberTheory_Idele_BaseChange
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalCyclotomicCompletionAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.residueFieldZModAlgebra _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedIntegralAlgebraContextValuationSubringAlgebra _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.LocalClassFieldTheory.normalizationIntegerRingIsIntegralClosure _root_.chosenFinitePlaceCompletionAlgebra _root_.chosenFinitePlaceCompletionContinuousSMul _root_.chosenFinitePlaceCompletionFiniteDimensional _root_.chosenFinitePlaceCompletionLocallyCompactSpace _root_.chosenFinitePlaceLocalizedFiniteDimensional _root_.chosenFinitePlaceLocalizedIntegerAlgebra _root_.chosenFinitePlaceLocalizedIntegerModuleFinite _root_.chosenFinitePlaceLocalizedIsGalois _root_.chosenFinitePlaceLocalizedIsIntegralClosure _root_.chosenFinitePlaceLocalizedIsNonarchimedeanLocalField _root_.chosenFinitePlaceLocalizedIsValuativeTopology _root_.chosenFinitePlaceLocalizedLocallyCompactSpace _root_.chosenFinitePlaceLocalizedValuationCompatible _root_.chosenFinitePlaceLocalizedValuationHasExtension _root_.chosenFinitePlaceLocalizedValuationIsNontrivial _root_.chosenFinitePlaceLocalizedValuativeRel _root_.chosenFinitePlaceLocalizedValuativeRelIsNontrivial _root_.chosenFinitePlaceLocalizedValued
attribute [-simp] _root_.IsDiscreteValuationRing.addVal_ringEquiv _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.OAI.PrimeDegreePackets.ThetaConstruction.schwartzCM_apply _root_.finiteIdeleOfSPlaceFactors_apply_mem _root_.finiteIdeleOfSPlaceFactors_apply_notMem _root_.ideleSupportedAtEquivSPlaceFactors_infinite _root_.ideleSupportedAtEquivSPlaceFactors_inside _root_.ideleSupportedAtEquivSPlaceFactors_outside_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

/-!
# Scalar extension from relative to ordinary ideles

The finite restricted-product comparison is combined here with the
archimedean form of the canonical local tensor decomposition. Infinite places above a fixed
infinite place of the base field are identified with exact extensions of
its absolute value.  Surjectivity is reduced through the finite normal
closure to the Galois valuation-extension comparison.
-/

open scoped NumberField TensorProduct RestrictedProduct
open NumberField IsDedekindDomain

noncomputable section


open AlgebraicNumberTheory.Valuations

universe u v

variable
    {K : Type u} {L : Type v}
    [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L]

/-- On a diagonal extension-field unit, the infinite local
relative-to-ordinary comparison is the ordinary diagonal embedding. -/
theorem infinitePlaceTensorUnitsEquivAbove_localFieldIdeleInclusion
    (w : InfinitePlace K)
    (W : {W : InfinitePlace L //
      infinitePlaceBelow (K := K) W = w})
    (x : Lˣ) :
    infinitePlaceTensorUnitsEquivAbove
        (K := K) (L := L) w
        (infiniteLocalFieldIdeleInclusion
          (K := K) (L := L) w x) W =
      Units.map
        (algebraMap L W.1.Completion)
        x := by
  rw [infinitePlaceTensorUnitsEquivAbove_apply]
  apply Units.ext
  simp only [Units.coe_map]
  change
    (InfinitePlace.Completion.equiv W.1).symm
        (completionTensorDecomposition_left
          w.1 w.isNontrivial
          (1 ⊗ₜ[K] (x : L))
          (infinitePlaceAboveEquivExtension
            (K := K) (L := L) w W)) =
      algebraMap L W.1.Completion (x : L)
  rw [completionTensorDecomposition_left_tmul_apply]
  simp only [map_one, one_mul]
  apply InfinitePlace.Completion.ext
  rfl

/-- The archimedean relative tensor factors form the ordinary infinite
idele group of `L`. -/
noncomputable def relativeInfiniteIdeleMulEquiv :
    (∀ w : InfinitePlace K,
      (w.Completion ⊗[K] L)ˣ) ≃*
      InfiniteIdeleGroup L :=
  (relativeInfiniteTensorPiMulEquiv
    (K := K) (L := L)).trans
    ContinuousMulEquiv.piUnits.symm.toMulEquiv

/-- Multiplication in the transported finite relative restricted product
is pointwise on its local tensor factors. -/
@[simp]
theorem RelativeFiniteIdeleData.finite_mul
    (a b : RelativeFiniteIdeleData (K := K) (L := L))
    (w : HeightOneSpectrum (𝓞 K)) :
    (a * b).finite w = a.finite w * b.finite w := by
  change
    (relativeFiniteTensorPiMulEquiv
      (K := K) (L := L)).symm
        (relativeFiniteTensorPiMulEquiv
            (K := K) (L := L) a.finite *
          relativeFiniteTensorPiMulEquiv
            (K := K) (L := L) b.finite) w =
      a.finite w * b.finite w
  rw [← map_mul,
    (relativeFiniteTensorPiMulEquiv
      (K := K) (L := L)).symm_apply_apply]
  rfl

/-- Forget the infinite component of restricted local idele data. -/
noncomputable def RelativeLocalIdeleData.toFiniteData
    (a : RelativeLocalIdeleData (K := K) (L := L)) :
    RelativeFiniteIdeleData (K := K) (L := L) where
  finite := a.finite
  eventually_integral := a.eventually_integral
  eventually_inverse_integral :=
    a.eventually_inverse_integral

/-- Passing relative local idele data to finite data preserves
multiplication. -/
@[simp]
theorem RelativeLocalIdeleData.toFiniteData_mul
    (a b : RelativeLocalIdeleData (K := K) (L := L)) :
    (a * b).toFiniteData =
      a.toFiniteData * b.toFiniteData := by
  apply RelativeFiniteIdeleData.ext
  funext w
  rw [RelativeFiniteIdeleData.finite_mul]
  change (a * b).finite w = a.finite w * b.finite w
  exact RelativeLocalIdeleData.finite_mul
    (K := K) (L := L) a b w

/-- Split restricted local idele data into its unrestricted infinite part
and finite restricted part. -/
noncomputable def relativeLocalIdeleDataSplitMulEquiv :
    RelativeLocalIdeleData (K := K) (L := L) ≃*
      ((∀ w : InfinitePlace K,
          (w.Completion ⊗[K] L)ˣ) ×
        RelativeFiniteIdeleData (K := K) (L := L)) where
  toFun a :=
    ⟨a.infinite, a.toFiniteData⟩
  invFun a :=
    { infinite := a.1
      finite := a.2.finite
      eventually_integral := a.2.eventually_integral
      eventually_inverse_integral :=
        a.2.eventually_inverse_integral }
  left_inv a := by
    apply RelativeLocalIdeleData.ext <;> rfl
  right_inv a := by
    rcases a with ⟨a, b⟩
    rfl
  map_mul' a b := by
    apply Prod.ext
    · funext w
      exact RelativeLocalIdeleData.infinite_mul
        (K := K) (L := L) a b w
    · exact RelativeLocalIdeleData.toFiniteData_mul
        (K := K) (L := L) a b

/-- Scalar extension identifies the actual relative
idele group `I_K ⊗_K L` with the ordinary idele group `I_L`. -/
noncomputable def relativeIdeleBaseChangeMulEquiv :
    RelativeIdeleGroup K L ≃* IdeleGroup L :=
  (relativeIdeleMulEquivLocalData
    (K := K) (L := L)).trans
    ((relativeLocalIdeleDataSplitMulEquiv
      (K := K) (L := L)).trans
      ((relativeInfiniteIdeleMulEquiv
        (K := K) (L := L)).prodCongr
        (relativeFiniteIdeleMulEquiv
          (K := K) (L := L))))

/-- The infinite component of the relative idele base-change
equivalence. -/
@[simp]
theorem relativeIdeleBaseChangeMulEquiv_infinite
    (z : RelativeIdeleGroup K L) :
    (relativeIdeleBaseChangeMulEquiv
      (K := K) (L := L) z).1 =
      relativeInfiniteIdeleMulEquiv
        (K := K) (L := L)
        (relativeIdeleToLocalData
          (K := K) (L := L) z).infinite :=
  rfl

/-- The finite component of the relative idele base-change
equivalence. -/
@[simp]
theorem relativeIdeleBaseChangeMulEquiv_finite
    (z : RelativeIdeleGroup K L) :
    (relativeIdeleBaseChangeMulEquiv
      (K := K) (L := L) z).2 =
      relativeFiniteIdeleToFiniteIdele
        (K := K) (L := L)
        (relativeIdeleToLocalData
          (K := K) (L := L) z).toFiniteData :=
  rfl
end
end

section
-- module Solutions.OAIQ244_DUKE.AlgebraicNumberTheory_AdeleBaseChange
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalCyclotomicCompletionAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.residueFieldZModAlgebra _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedIntegralAlgebraContextValuationSubringAlgebra _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.LocalClassFieldTheory.normalizationIntegerRingIsIntegralClosure _root_.chosenFinitePlaceCompletionAlgebra _root_.chosenFinitePlaceCompletionContinuousSMul _root_.chosenFinitePlaceCompletionFiniteDimensional _root_.chosenFinitePlaceCompletionLocallyCompactSpace _root_.chosenFinitePlaceLocalizedFiniteDimensional _root_.chosenFinitePlaceLocalizedIntegerAlgebra _root_.chosenFinitePlaceLocalizedIntegerModuleFinite _root_.chosenFinitePlaceLocalizedIsGalois _root_.chosenFinitePlaceLocalizedIsIntegralClosure _root_.chosenFinitePlaceLocalizedIsNonarchimedeanLocalField _root_.chosenFinitePlaceLocalizedIsValuativeTopology _root_.chosenFinitePlaceLocalizedLocallyCompactSpace _root_.chosenFinitePlaceLocalizedValuationCompatible _root_.chosenFinitePlaceLocalizedValuationHasExtension _root_.chosenFinitePlaceLocalizedValuationIsNontrivial _root_.chosenFinitePlaceLocalizedValuativeRel _root_.chosenFinitePlaceLocalizedValuativeRelIsNontrivial _root_.chosenFinitePlaceLocalizedValued
attribute [-simp] _root_.IsDiscreteValuationRing.addVal_ringEquiv _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.OAI.PrimeDegreePackets.ThetaConstruction.schwartzCM_apply _root_.finiteIdeleOfSPlaceFactors_apply_mem _root_.finiteIdeleOfSPlaceFactors_apply_notMem _root_.ideleSupportedAtEquivSPlaceFactors_infinite _root_.ideleSupportedAtEquivSPlaceFactors_inside _root_.ideleSupportedAtEquivSPlaceFactors_outside_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

/-!
# Scalar extension from relative to ordinary adeles

This file upgrades the relative-to-ordinary idele comparison to the
underlying adele rings.  The additive structure is needed to transport
determinant norms in a field tower.
-/

open scoped NumberField TensorProduct RestrictedProduct
open NumberField IsDedekindDomain

noncomputable section


open AlgebraicNumberTheory.Valuations

universe u v

variable
    {K : Type u} {L : Type v}
    [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L]

/-- On a pure tensor, the finite-place relative-to-ordinary comparison
is the canonical completion map on the local coefficient multiplied by
the diagonal image of the extension-field factor. -/
theorem finitePlaceTensorRingEquivAboveAdic_tmul
    (w : HeightOneSpectrum (𝓞 K))
    (W : {W : HeightOneSpectrum (𝓞 L) //
      finitePlaceBelow (K := K) W = w})
    (a : w.adicCompletion K)
    (x : L) :
    finitePlaceTensorRingEquivAboveAdic
        (K := K) (L := L) w
        (a ⊗ₜ[K] x) W =
      finitePlaceAdicCompletionMap K L w W a *
        algebraMap L (W.1.adicCompletion L) x := by
  obtain ⟨u, rfl⟩ :=
    (finitePlaceExtensionEquivAbove
      (K := K) (L := L) w).surjective W
  rw [finitePlaceTensorRingEquivAboveAdic_apply_extension,
    finitePlaceLocalTensorDecompositionComponent_tmul, map_mul]
  change
    finitePlaceExtensionAdicCompletionMap K L w u a *
        finitePlaceExtensionAdicCompletionRingEquiv
          (K := K) (L := L) w u
          (AbsoluteValue.toCompletion u.1 x) =
      _
  rw [
    finitePlaceExtensionAdicCompletionMap_eq_finitePlaceAdicCompletionMap,
    finitePlaceExtensionAdicCompletionRingEquiv_toCompletion]
  rfl

/-- On a pure tensor, the infinite-place relative-to-ordinary comparison
is the canonical completion map on the local coefficient multiplied by
the diagonal image of the extension-field factor. -/
theorem infinitePlaceTensorRingEquivAbove_tmul
    (w : InfinitePlace K)
    (W : {W : InfinitePlace L //
      infinitePlaceBelow (K := K) W = w})
    (a : w.Completion)
    (x : L) :
    letI : W.1.1.LiesOver w.1 :=
      ⟨congrArg (fun q : InfinitePlace K => q.1) W.2⟩
    infinitePlaceTensorRingEquivAbove
        (K := K) (L := L) w
        (a ⊗ₜ[K] x) W =
      NumberField.LiesOver.completionMap
          (v := w) (w := W.1) a *
        algebraMap L W.1.Completion x := by
  let : W.1.1.LiesOver w.1 :=
    ⟨congrArg (fun q : InfinitePlace K => q.1) W.2⟩
  rw [infinitePlaceTensorRingEquivAbove_apply]
  change
    (InfinitePlace.Completion.equiv W.1).symm
        (completionTensorDecomposition_left
          w.1 w.isNontrivial
          ((infinitePlaceCompletionAlgEquiv w a) ⊗ₜ[K] x)
          (infinitePlaceAboveToExtension
            (K := K) (L := L) w W)) =
      NumberField.LiesOver.completionMap
          (v := w) (w := W.1) a *
        algebraMap L W.1.Completion x
  dsimp only [infinitePlaceAboveToExtension]
  rw [completionTensorDecomposition_left_tmul_apply, map_mul]
  congr 1

/-- Flatten the products over infinite base places and places above
them to the product over all infinite places of the extension field. -/
noncomputable def infinitePlaceAbovePiRingEquiv :
    (∀ w : InfinitePlace K,
      ∀ W : {W : InfinitePlace L //
          infinitePlaceBelow (K := K) W = w},
        W.1.Completion) ≃+*
      ∀ W : InfinitePlace L, W.Completion where
  toFun f W :=
    f (infinitePlaceBelow (K := K) W) ⟨W, rfl⟩
  invFun f w W := f W.1
  left_inv f := by
    funext w W
    rcases W with ⟨W, hW⟩
    subst w
    rfl
  right_inv f := by
    funext W
    rfl
  map_add' f g := by
    funext W
    rfl
  map_mul' f g := by
    funext W
    rfl

/-- All infinite local tensor rings, flattened to the concrete infinite
completion family of the extension field. -/
noncomputable def relativeInfiniteTensorPiRingEquiv :
    (∀ w : InfinitePlace K,
      w.Completion ⊗[K] L) ≃+*
      ∀ W : InfinitePlace L, W.Completion :=
  (RingEquiv.piCongrRight fun w =>
      infinitePlaceTensorRingEquivAbove
        (K := K) (L := L) w).trans
    (infinitePlaceAbovePiRingEquiv (K := K) (L := L))

/-- Coordinate formula for the relative infinite tensor product
equivalence. -/
@[simp]
theorem relativeInfiniteTensorPiRingEquiv_apply
    (x : ∀ w : InfinitePlace K,
      w.Completion ⊗[K] L)
    (W : InfinitePlace L) :
    relativeInfiniteTensorPiRingEquiv
        (K := K) (L := L) x W =
      infinitePlaceTensorRingEquivAbove
        (K := K) (L := L)
        (infinitePlaceBelow (K := K) W)
        (x (infinitePlaceBelow (K := K) W)) ⟨W, rfl⟩ :=
  rfl

/-- Coordinate formula for the inverse relative infinite tensor product
equivalence. -/
@[simp]
theorem relativeInfiniteTensorPiRingEquiv_symm_apply
    (y : ∀ W : InfinitePlace L, W.Completion)
    (w : InfinitePlace K) :
    (relativeInfiniteTensorPiRingEquiv
        (K := K) (L := L)).symm y w =
      (infinitePlaceTensorRingEquivAbove
        (K := K) (L := L) w).symm
        (fun W => y W.1) :=
  rfl

/-- Integrality in the relative-tensor factors is exactly integrality
of every concrete finite completion coordinate. -/
theorem relativeLocalTensorDecompositionIntegralAt_iff_aboveAdicRing
    (w : HeightOneSpectrum (𝓞 K))
    (x : w.adicCompletion K ⊗[K] L) :
    RelativeLocalTensorDecompositionIntegralAt
        (K := K) (L := L) w x ↔
      ∀ W : {W : HeightOneSpectrum (𝓞 L) //
          finitePlaceBelow (K := K) W = w},
        finitePlaceTensorRingEquivAboveAdic
            (K := K) (L := L) w x W ∈
          W.1.adicCompletionIntegers L := by
  constructor
  · intro hx W
    let u :=
      (finitePlaceExtensionEquivAbove
        (K := K) (L := L) w).symm W
    have hW :
        finitePlaceExtensionEquivAbove
            (K := K) (L := L) w u = W :=
      (finitePlaceExtensionEquivAbove
        (K := K) (L := L) w).apply_symm_apply W
    rw [← hW,
      finitePlaceTensorRingEquivAboveAdic_apply_extension]
    exact
      (finitePlaceExtensionAdicCompletionRingEquiv_mem_integers_iff
        (K := K) (L := L) w u _).2 (hx u)
  · intro hx u
    have h :=
      hx (finitePlaceExtensionEquivAbove
        (K := K) (L := L) w u)
    rw [finitePlaceTensorRingEquivAboveAdic_apply_extension] at h
    exact
      (finitePlaceExtensionAdicCompletionRingEquiv_mem_integers_iff
        (K := K) (L := L) w u _).1 h

omit [NumberField L] in
/-- Outside its coefficient support, a relative adele finite component
belongs to the fixed local basis lattice. -/
theorem relativeAdele_finiteComponent_basisIntegral_of_notMem
    (z : RelativeAdeleRing K L)
    (w : HeightOneSpectrum (𝓞 K))
    (hw : w ∉ relativeAdeleCoefficientSupport
      (K := K) (L := L) z) :
    RelativeBasisIntegralAt
      (K := K) (L := L) w
      (relativeAdeleFiniteComponent
        (K := K) (L := L) w z) := by
  let c :
      ∀ i : RelativeAdeleBasisIndex (K := K) (L := L),
        w.adicCompletionIntegers K :=
    fun i =>
      ⟨(relativeAdeleCoefficient
          (K := K) (L := L) z i).2 w, by
        by_contra hi
        apply hw
        exact
          (mem_relativeAdeleCoefficientSupport_iff
            (K := K) (L := L) z w).2 ⟨i, hi⟩⟩
  refine ⟨c, ?_⟩
  simpa only [c, Subtype.coe_mk] using
    relativeAdeleFiniteComponent_eq_sum_tmul_coefficients
      (K := K) (L := L) z w

/-- A relative adele becomes integral in every concrete completion
above almost every finite base place. -/
theorem relativeAdele_eventually_aboveAdicIntegral
    (z : RelativeAdeleRing K L) :
    ∀ᶠ w : HeightOneSpectrum (𝓞 K) in Filter.cofinite,
      ∀ W : {W : HeightOneSpectrum (𝓞 L) //
          finitePlaceBelow (K := K) W = w},
        finitePlaceTensorRingEquivAboveAdic
            (K := K) (L := L) w
            (relativeAdeleFiniteComponent
              (K := K) (L := L) w z) W ∈
          W.1.adicCompletionIntegers L := by
  classical
  filter_upwards [
    (relativeAdeleCoefficientSupport
      (K := K) (L := L) z).eventually_cofinite_notMem,
    (integralTensorComparisonBadPlaces
      (K := K) (L := L)).eventually_cofinite_notMem] with w hs hbad
  apply
    (relativeLocalTensorDecompositionIntegralAt_iff_aboveAdicRing
      (K := K) (L := L) w _).1
  apply
    (relativeBasisIntegralAt_iff_localTensorDecompositionIntegral_of_notMem
      (K := K) (L := L) w hbad).1
  exact relativeAdele_finiteComponent_basisIntegral_of_notMem
    (K := K) (L := L) z w hs

/-- The forward ring-level scalar-extension map on adeles. -/
noncomputable def relativeAdeleToAdele
    (z : RelativeAdeleRing K L) :
    NumberField.AdeleRing (𝓞 L) L :=
  ⟨relativeInfiniteTensorPiRingEquiv
      (K := K) (L := L)
      (fun w =>
        relativeAdeleInfiniteComponent
          (K := K) (L := L) w z),
    ⟨relativeFiniteTensorPiRingEquiv
        (K := K) (L := L)
        (fun w =>
          relativeAdeleFiniteComponent
            (K := K) (L := L) w z),
      (eventually_finitePlace_iff_eventually_all_above
        (K := K) (L := L)
        (fun W =>
          relativeFiniteTensorPiRingEquiv
              (K := K) (L := L)
              (fun w =>
                relativeAdeleFiniteComponent
                  (K := K) (L := L) w z) W ∈
            W.adicCompletionIntegers L)).2 <| by
        filter_upwards [
          relativeAdele_eventually_aboveAdicIntegral
            (K := K) (L := L) z] with w hw
        intro W
        rcases W with ⟨W, hW⟩
        subst w
        exact hw ⟨W, rfl⟩⟩⟩

/-- The infinite component of the underlying adele of a relative adele. -/
@[simp]
theorem relativeAdeleToAdele_infinite
    (z : RelativeAdeleRing K L)
    (W : InfinitePlace L) :
    (relativeAdeleToAdele
      (K := K) (L := L) z).1 W =
      infinitePlaceTensorRingEquivAbove
        (K := K) (L := L)
        (infinitePlaceBelow (K := K) W)
        (relativeAdeleInfiniteComponent
          (K := K) (L := L)
          (infinitePlaceBelow (K := K) W) z) ⟨W, rfl⟩ :=
  rfl

/-- The finite component of the underlying adele of a relative adele. -/
@[simp]
theorem relativeAdeleToAdele_finite
    (z : RelativeAdeleRing K L)
    (W : HeightOneSpectrum (𝓞 L)) :
    (relativeAdeleToAdele
      (K := K) (L := L) z).2 W =
      finitePlaceTensorRingEquivAboveAdic
        (K := K) (L := L)
        (finitePlaceBelow (K := K) W)
        (relativeAdeleFiniteComponent
          (K := K) (L := L)
          (finitePlaceBelow (K := K) W) z) ⟨W, rfl⟩ :=
  rfl

/-- The pulled-back finite tensor family is basis-integral at almost
every finite place. -/
theorem finiteAdeleRelativeTensorFamily_eventually_basisIntegral
    (y : IsDedekindDomain.FiniteAdeleRing (𝓞 L) L) :
    ∀ᶠ w : HeightOneSpectrum (𝓞 K) in Filter.cofinite,
      RelativeBasisIntegralAt
        (K := K) (L := L) w
        (finiteAdeleRelativeTensorFamily
          (K := K) (L := L) y w) := by
  have habove :
      ∀ᶠ w : HeightOneSpectrum (𝓞 K) in Filter.cofinite,
        ∀ W : {W : HeightOneSpectrum (𝓞 L) //
            finitePlaceBelow (K := K) W = w},
          y W.1 ∈ W.1.adicCompletionIntegers L :=
    (eventually_finitePlace_iff_eventually_all_above
      (K := K) (L := L)
      (fun W => y W ∈ W.adicCompletionIntegers L)).1 y.2
  filter_upwards [
    habove,
    (integralTensorComparisonBadPlaces
      (K := K) (L := L)).eventually_cofinite_notMem] with w hw hbad
  apply
    (relativeBasisIntegralAt_iff_localTensorDecompositionIntegral_of_notMem
      (K := K) (L := L) w hbad).2
  apply
    (relativeLocalTensorDecompositionIntegralAt_iff_aboveAdicRing
      (K := K) (L := L) w _).2
  intro W
  have hcomponent :=
    congrFun
      ((finitePlaceTensorRingEquivAboveAdic
        (K := K) (L := L) w).apply_symm_apply
          (fun W => y W.1)) W
  rw [finiteAdeleRelativeTensorFamily,
    relativeFiniteTensorPiRingEquiv_symm_apply,
    hcomponent]
  exact hw W

/-- Pull an ordinary adele back to restricted relative local data. -/
noncomputable def adeleToRelativeLocalAdeleData
    (y : NumberField.AdeleRing (𝓞 L) L) :
    RelativeLocalAdeleData (K := K) (L := L) where
  infinite :=
    (relativeInfiniteTensorPiRingEquiv
      (K := K) (L := L)).symm (fun W => y.1 W)
  finite :=
    finiteAdeleRelativeTensorFamily
      (K := K) (L := L) y.2
  eventually_integral i :=
    (finiteAdeleRelativeTensorFamily_eventually_basisIntegral
      (K := K) (L := L) y.2).mono fun w hw =>
        relativeBasisIntegralAt_repr_mem
          (K := K) (L := L) w _ hw i

/-- The inverse ring-level scalar-extension map on adeles. -/
noncomputable def adeleToRelativeAdele
    (y : NumberField.AdeleRing (𝓞 L) L) :
    RelativeAdeleRing K L :=
  relativeAdeleOfLocalData
    (K := K) (L := L)
    (adeleToRelativeLocalAdeleData
      (K := K) (L := L) y)

/-- The infinite component of the relative adele reconstructed from an
ordinary adele. -/
@[simp]
theorem adeleToRelativeAdele_infiniteComponent
    (y : NumberField.AdeleRing (𝓞 L) L)
    (w : InfinitePlace K) :
    relativeAdeleInfiniteComponent
        (K := K) (L := L) w
        (adeleToRelativeAdele
          (K := K) (L := L) y) =
      (relativeInfiniteTensorPiRingEquiv
        (K := K) (L := L)).symm
        (fun W => y.1 W) w := by
  rw [adeleToRelativeAdele,
    relativeAdeleOfLocalData_infiniteComponent]
  rfl

/-- The finite component of the relative adele reconstructed from an
ordinary adele. -/
@[simp]
theorem adeleToRelativeAdele_finiteComponent
    (y : NumberField.AdeleRing (𝓞 L) L)
    (w : HeightOneSpectrum (𝓞 K)) :
    relativeAdeleFiniteComponent
        (K := K) (L := L) w
        (adeleToRelativeAdele
          (K := K) (L := L) y) =
      (relativeFiniteTensorPiRingEquiv
        (K := K) (L := L)).symm
        (fun W => y.2 W) w := by
  rw [adeleToRelativeAdele,
    relativeAdeleOfLocalData_finiteComponent]
  rfl

/-- Scalar extension identifies the relative adele ring over `K` with
the ordinary adele ring of `L`. -/
noncomputable def relativeAdeleBaseChangeRingEquiv :
    RelativeAdeleRing K L ≃+*
      NumberField.AdeleRing (𝓞 L) L where
  toFun :=
    relativeAdeleToAdele (K := K) (L := L)
  invFun :=
    adeleToRelativeAdele (K := K) (L := L)
  left_inv z := by
    apply relativeAdele_ext_of_components
    · intro w
      rw [adeleToRelativeAdele_infiniteComponent]
      change
        (relativeInfiniteTensorPiRingEquiv
          (K := K) (L := L)).symm
            (relativeInfiniteTensorPiRingEquiv
              (K := K) (L := L)
              (fun w =>
                relativeAdeleInfiniteComponent
                  (K := K) (L := L) w z)) w =
          relativeAdeleInfiniteComponent
            (K := K) (L := L) w z
      rw [(relativeInfiniteTensorPiRingEquiv
        (K := K) (L := L)).symm_apply_apply]
    · intro w
      rw [adeleToRelativeAdele_finiteComponent]
      change
        (relativeFiniteTensorPiRingEquiv
          (K := K) (L := L)).symm
            (relativeFiniteTensorPiRingEquiv
              (K := K) (L := L)
              (fun w =>
                relativeAdeleFiniteComponent
                  (K := K) (L := L) w z)) w =
          relativeAdeleFiniteComponent
            (K := K) (L := L) w z
      rw [(relativeFiniteTensorPiRingEquiv
        (K := K) (L := L)).symm_apply_apply]
  right_inv y := by
    apply Prod.ext
    · funext W
      rw [relativeAdeleToAdele_infinite,
        adeleToRelativeAdele_infiniteComponent]
      change
        relativeInfiniteTensorPiRingEquiv
            (K := K) (L := L)
            ((relativeInfiniteTensorPiRingEquiv
              (K := K) (L := L)).symm
              (fun W => y.1 W)) W =
          y.1 W
      rw [(relativeInfiniteTensorPiRingEquiv
        (K := K) (L := L)).apply_symm_apply]
    · apply DFunLike.coe_injective
      funext W
      change
        relativeFiniteTensorPiRingEquiv
            (K := K) (L := L)
            (fun w =>
              relativeAdeleFiniteComponent
                (K := K) (L := L) w
                (adeleToRelativeAdele
                  (K := K) (L := L) y)) W =
          y.2 W
      rw [show
        (fun w =>
          relativeAdeleFiniteComponent
            (K := K) (L := L) w
            (adeleToRelativeAdele
              (K := K) (L := L) y)) =
          (relativeFiniteTensorPiRingEquiv
            (K := K) (L := L)).symm
            (fun W => y.2 W) by
          funext w
          exact adeleToRelativeAdele_finiteComponent
            (K := K) (L := L) y w]
      rw [(relativeFiniteTensorPiRingEquiv
        (K := K) (L := L)).apply_symm_apply]
  map_add' x y := by
    apply Prod.ext
    · funext W
      change
        relativeInfiniteTensorPiRingEquiv
            (K := K) (L := L)
            (fun w =>
              relativeAdeleInfiniteComponent
                (K := K) (L := L) w (x + y)) W =
          relativeInfiniteTensorPiRingEquiv
              (K := K) (L := L)
              (fun w =>
                relativeAdeleInfiniteComponent
                  (K := K) (L := L) w x) W +
            relativeInfiniteTensorPiRingEquiv
              (K := K) (L := L)
              (fun w =>
                relativeAdeleInfiniteComponent
                  (K := K) (L := L) w y) W
      rw [show
        (fun w =>
          relativeAdeleInfiniteComponent
            (K := K) (L := L) w (x + y)) =
          (fun w =>
            relativeAdeleInfiniteComponent
              (K := K) (L := L) w x) +
          (fun w =>
            relativeAdeleInfiniteComponent
              (K := K) (L := L) w y) by
          funext w
          exact map_add _ _ _,
        map_add]
      rfl
    · apply Subtype.ext
      funext W
      change
        relativeFiniteTensorPiRingEquiv
            (K := K) (L := L)
            (fun w =>
              relativeAdeleFiniteComponent
                (K := K) (L := L) w (x + y)) W =
          relativeFiniteTensorPiRingEquiv
              (K := K) (L := L)
              (fun w =>
                relativeAdeleFiniteComponent
                  (K := K) (L := L) w x) W +
            relativeFiniteTensorPiRingEquiv
              (K := K) (L := L)
              (fun w =>
                relativeAdeleFiniteComponent
                  (K := K) (L := L) w y) W
      rw [show
        (fun w =>
          relativeAdeleFiniteComponent
            (K := K) (L := L) w (x + y)) =
          (fun w =>
            relativeAdeleFiniteComponent
              (K := K) (L := L) w x) +
          (fun w =>
            relativeAdeleFiniteComponent
              (K := K) (L := L) w y) by
          funext w
          exact map_add _ _ _,
        map_add]
      rfl
  map_mul' x y := by
    apply Prod.ext
    · funext W
      change
        relativeInfiniteTensorPiRingEquiv
            (K := K) (L := L)
            (fun w =>
              relativeAdeleInfiniteComponent
                (K := K) (L := L) w (x * y)) W =
          relativeInfiniteTensorPiRingEquiv
              (K := K) (L := L)
              (fun w =>
                relativeAdeleInfiniteComponent
                  (K := K) (L := L) w x) W *
            relativeInfiniteTensorPiRingEquiv
              (K := K) (L := L)
              (fun w =>
                relativeAdeleInfiniteComponent
                  (K := K) (L := L) w y) W
      rw [show
        (fun w =>
          relativeAdeleInfiniteComponent
            (K := K) (L := L) w (x * y)) =
          (fun w =>
            relativeAdeleInfiniteComponent
              (K := K) (L := L) w x) *
          (fun w =>
            relativeAdeleInfiniteComponent
              (K := K) (L := L) w y) by
          funext w
          exact map_mul _ _ _,
        map_mul]
      rfl
    · apply Subtype.ext
      funext W
      change
        relativeFiniteTensorPiRingEquiv
            (K := K) (L := L)
            (fun w =>
              relativeAdeleFiniteComponent
                (K := K) (L := L) w (x * y)) W =
          relativeFiniteTensorPiRingEquiv
              (K := K) (L := L)
              (fun w =>
                relativeAdeleFiniteComponent
                  (K := K) (L := L) w x) W *
            relativeFiniteTensorPiRingEquiv
              (K := K) (L := L)
              (fun w =>
                relativeAdeleFiniteComponent
                  (K := K) (L := L) w y) W
      rw [show
        (fun w =>
          relativeAdeleFiniteComponent
            (K := K) (L := L) w (x * y)) =
          (fun w =>
            relativeAdeleFiniteComponent
              (K := K) (L := L) w x) *
          (fun w =>
            relativeAdeleFiniteComponent
              (K := K) (L := L) w y) by
          funext w
          exact map_mul _ _ _,
        map_mul]
      rfl

/-- Finite-coordinate formula for scalar extension of a pure relative
adele tensor. -/
@[simp]
theorem relativeAdeleBaseChangeRingEquiv_finiteComponent_tmul
    (a : NumberField.AdeleRing (𝓞 K) K)
    (x : L)
    (W : HeightOneSpectrum (𝓞 L)) :
    (relativeAdeleBaseChangeRingEquiv
        (K := K) (L := L) (a ⊗ₜ[K] x)).2 W =
      finitePlaceAdicCompletionMap K L
          (finitePlaceBelow (K := K) W) ⟨W, rfl⟩
          (a.2 (finitePlaceBelow (K := K) W)) *
        algebraMap L (W.adicCompletion L) x := by
  change
    finitePlaceTensorRingEquivAboveAdic
        (K := K) (L := L)
        (finitePlaceBelow (K := K) W)
        (a.2 (finitePlaceBelow (K := K) W) ⊗ₜ[K] x)
        ⟨W, rfl⟩ =
      _
  exact
    finitePlaceTensorRingEquivAboveAdic_tmul
      (K := K) (L := L)
      (finitePlaceBelow (K := K) W) ⟨W, rfl⟩
      (a.2 (finitePlaceBelow (K := K) W)) x

/-- Infinite-coordinate formula for scalar extension of a pure relative
adele tensor. -/
@[simp]
theorem relativeAdeleBaseChangeRingEquiv_infiniteComponent_tmul
    (a : NumberField.AdeleRing (𝓞 K) K)
    (x : L)
    (W : InfinitePlace L) :
    let v := infinitePlaceBelow (K := K) W
    letI : W.1.LiesOver v.1 := ⟨rfl⟩
    (relativeAdeleBaseChangeRingEquiv
        (K := K) (L := L) (a ⊗ₜ[K] x)).1 W =
      NumberField.LiesOver.completionMap
          (v := v) (w := W) (a.1 v) *
        algebraMap L W.Completion x := by
  let v := infinitePlaceBelow (K := K) W
  let : W.1.LiesOver v.1 := ⟨rfl⟩
  change
    infinitePlaceTensorRingEquivAbove
        (K := K) (L := L) v
        (a.1 v ⊗ₜ[K] x) ⟨W, rfl⟩ =
      NumberField.LiesOver.completionMap
          (v := v) (w := W) (a.1 v) *
        algebraMap L W.Completion x
  exact
    infinitePlaceTensorRingEquivAbove_tmul
      (K := K) (L := L) v ⟨W, rfl⟩ (a.1 v) x

/-- A diagonal extension-field element has its expected concrete
finite component under the ring comparison. -/
theorem finitePlaceTensorRingEquivAboveAdic_tmul_one
    (w : HeightOneSpectrum (𝓞 K))
    (W : {W : HeightOneSpectrum (𝓞 L) //
      finitePlaceBelow (K := K) W = w})
    (x : L) :
    finitePlaceTensorRingEquivAboveAdic
        (K := K) (L := L) w
        ((1 : w.adicCompletion K) ⊗ₜ[K] x) W =
      algebraMap L (W.1.adicCompletion L) x := by
  obtain ⟨u, rfl⟩ :=
    (finitePlaceExtensionEquivAbove
      (K := K) (L := L) w).surjective W
  rw [finitePlaceTensorRingEquivAboveAdic_apply_extension,
    finitePlaceLocalTensorDecompositionComponent_tmul]
  simp only [map_one, one_mul,
    finitePlaceExtensionAdicCompletionRingEquiv_toCompletion]
  rfl

/-- A diagonal extension-field element has its expected concrete
archimedean component under the ring comparison. -/
theorem infinitePlaceTensorRingEquivAbove_tmul_one
    (w : InfinitePlace K)
    (W : {W : InfinitePlace L //
      infinitePlaceBelow (K := K) W = w})
    (x : L) :
    infinitePlaceTensorRingEquivAbove
        (K := K) (L := L) w
        ((1 : w.Completion) ⊗ₜ[K] x) W =
      algebraMap L W.1.Completion x := by
  rw [infinitePlaceTensorRingEquivAbove_apply]
  change
    (InfinitePlace.Completion.equiv W.1).symm
        (completionTensorDecomposition_left
          w.1 w.isNontrivial
          ((1 : w.1.Completion) ⊗ₜ[K] x)
          (infinitePlaceAboveEquivExtension
            (K := K) (L := L) w W)) =
      algebraMap L W.1.Completion x
  rw [completionTensorDecomposition_left_tmul_apply]
  simp only [map_one, one_mul]
  apply InfinitePlace.Completion.ext
  rfl

/-- The ring comparison carries the diagonal copy of `L` to the
ordinary diagonal adele. -/
theorem relativeAdeleBaseChangeRingEquiv_fieldInclusion
    (x : L) :
    relativeAdeleBaseChangeRingEquiv
        (K := K) (L := L)
        ((1 : NumberField.AdeleRing (𝓞 K) K) ⊗ₜ[K] x) =
      algebraMap L (NumberField.AdeleRing (𝓞 L) L) x := by
  change
    relativeAdeleToAdele
        (K := K) (L := L)
        ((1 : NumberField.AdeleRing (𝓞 K) K) ⊗ₜ[K] x) =
      algebraMap L (NumberField.AdeleRing (𝓞 L) L) x
  apply Prod.ext
  · funext W
    rw [relativeAdeleToAdele_infinite]
    change
      infinitePlaceTensorRingEquivAbove
          (K := K) (L := L)
          (infinitePlaceBelow (K := K) W)
          ((1 :
            (infinitePlaceBelow
              (K := K) W).Completion) ⊗ₜ[K] x)
          ⟨W, rfl⟩ =
        algebraMap L W.Completion x
    exact infinitePlaceTensorRingEquivAbove_tmul_one
      (K := K) (L := L)
      (infinitePlaceBelow (K := K) W) ⟨W, rfl⟩ x
  · apply DFunLike.coe_injective
    funext W
    rw [relativeAdeleToAdele_finite]
    change
      finitePlaceTensorRingEquivAboveAdic
          (K := K) (L := L)
          (finitePlaceBelow (K := K) W)
          ((1 :
            (finitePlaceBelow
              (K := K) W).adicCompletion K) ⊗ₜ[K] x)
          ⟨W, rfl⟩ =
        algebraMap L (W.adicCompletion L) x
    exact finitePlaceTensorRingEquivAboveAdic_tmul_one
      (K := K) (L := L)
      (finitePlaceBelow (K := K) W) ⟨W, rfl⟩ x

/-- The finite local unit comparison is induced by the corresponding
ring equivalence. -/
theorem finitePlaceTensorUnitsEquivAboveAdic_coe
    (w : HeightOneSpectrum (𝓞 K))
    (x : (w.adicCompletion K ⊗[K] L)ˣ)
    (W : {W : HeightOneSpectrum (𝓞 L) //
      finitePlaceBelow (K := K) W = w}) :
    ((finitePlaceTensorUnitsEquivAboveAdic
        (K := K) (L := L) w x W :
        (W.1.adicCompletion L)ˣ) :
        W.1.adicCompletion L) =
      finitePlaceTensorRingEquivAboveAdic
        (K := K) (L := L) w
        (x : w.adicCompletion K ⊗[K] L) W := by
  obtain ⟨u, rfl⟩ :=
    (finitePlaceExtensionEquivAbove
      (K := K) (L := L) w).surjective W
  rw [finitePlaceTensorUnitsEquivAboveAdic_apply_extension,
    finitePlaceTensorRingEquivAboveAdic_apply_extension]
  rfl

/-- The flattened finite unit comparison is induced by the flattened
finite ring comparison. -/
theorem relativeFiniteTensorPiMulEquiv_coe
    (x : ∀ w : HeightOneSpectrum (𝓞 K),
      (w.adicCompletion K ⊗[K] L)ˣ)
    (W : HeightOneSpectrum (𝓞 L)) :
    ((relativeFiniteTensorPiMulEquiv
        (K := K) (L := L) x W :
        (W.adicCompletion L)ˣ) :
        W.adicCompletion L) =
      relativeFiniteTensorPiRingEquiv
        (K := K) (L := L)
        (fun w =>
          (x w : w.adicCompletion K ⊗[K] L)) W := by
  rw [relativeFiniteTensorPiMulEquiv_apply,
    relativeFiniteTensorPiRingEquiv_apply]
  exact finitePlaceTensorUnitsEquivAboveAdic_coe
    (K := K) (L := L)
    (finitePlaceBelow (K := K) W)
    (x (finitePlaceBelow (K := K) W)) ⟨W, rfl⟩

/-- The previously constructed idele comparison is the unit-group map
induced by the ring comparison. -/
theorem relativeIdeleBaseChangeMulEquiv_eq_ringUnits
    (z : RelativeIdeleGroup K L) :
    IdeleGroup.equivAdeleRingUnits
        (relativeIdeleBaseChangeMulEquiv
          (K := K) (L := L) z) =
      Units.mapEquiv
        (relativeAdeleBaseChangeRingEquiv
          (K := K) (L := L)).toMulEquiv z := by
  apply Units.ext
  apply Prod.ext
  · funext W
    change
      ((IdeleGroup.infiniteComponent W
          (relativeIdeleBaseChangeMulEquiv
            (K := K) (L := L) z) :
          W.Completionˣ) : W.Completion) =
        (relativeAdeleToAdele
          (K := K) (L := L)
          (z : RelativeAdeleRing K L)).1 W
    rfl
  · apply DFunLike.coe_injective
    funext W
    change
      ((((relativeIdeleBaseChangeMulEquiv
          (K := K) (L := L) z).2 W :
          (W.adicCompletion L)ˣ)) :
          W.adicCompletion L) =
        relativeFiniteTensorPiRingEquiv
          (K := K) (L := L)
          (fun w =>
            relativeAdeleFiniteComponent
              (K := K) (L := L) w
              (z : RelativeAdeleRing K L)) W
    rw [relativeIdeleBaseChangeMulEquiv_finite,
      relativeFiniteIdeleToFiniteIdele_apply]
    exact relativeFiniteTensorPiMulEquiv_coe
      (K := K) (L := L)
      (fun w =>
        RelativeIdeleGroup.finiteComponent
          (K := K) (L := L) w z) W

/-- The relative-to-ordinary comparison sends the extension-field
diagonal to the ordinary diagonal idele. -/
@[simp]
theorem relativeIdeleBaseChangeMulEquiv_principalIdele
    (x : Lˣ) :
    relativeIdeleBaseChangeMulEquiv
        (K := K) (L := L)
        (RelativeIdeleGroup.principalIdele K L x) =
      IdeleGroup.principalIdele L x := by
  apply Prod.ext
  · apply Units.ext
    funext W
    change
      infinitePlaceTensorUnitsEquivAbove
          (K := K) (L := L)
          (infinitePlaceBelow (K := K) W)
          ((relativeIdeleToLocalData
            (K := K) (L := L)
            (RelativeIdeleGroup.principalIdele K L x)).infinite
              (infinitePlaceBelow (K := K) W))
          ⟨W, rfl⟩ =
        algebraMap L W.Completion (x : L)
    simp only [relativeIdeleToLocalData]
    rw [RelativeIdeleGroup.infiniteComponent_principalIdele,
      infinitePlaceTensorUnitsEquivAbove_localFieldIdeleInclusion]
    simp
  · rw [relativeIdeleBaseChangeMulEquiv_finite]
    apply RestrictedProduct.ext
    intro W
    rw [relativeFiniteIdeleToFiniteIdele_apply,
      relativeFiniteTensorPiMulEquiv_apply]
    change
      finitePlaceTensorUnitsEquivAboveAdic
          (K := K) (L := L)
          (finitePlaceBelow (K := K) W)
          ((relativeIdeleToLocalData
            (K := K) (L := L)
            (RelativeIdeleGroup.principalIdele K L x)).finite
              (finitePlaceBelow (K := K) W))
          ⟨W, rfl⟩ =
        Units.map (FinitePlace.embedding (K := L) W) x
    simp only [relativeIdeleToLocalData]
    rw [RelativeIdeleGroup.finiteComponent_principalIdele,
      finitePlaceTensorUnitsEquivAboveAdic_localFieldIdeleInclusion]
end
end

section
-- module Solutions.OAIQ244_DUKE.AlgebraicNumberTheory_Idele_Extension_IdealClass
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalCyclotomicCompletionAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.KummerTheory.primeCyclotomicBaseFiniteDimensional _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.residueFieldZModAlgebra _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedIntegralAlgebraContextValuationSubringAlgebra _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.CyclicCohomology.binaryCoefficientFamilyCommGroup _root_.LocalClassFieldTheory.normalizationIntegerRingIsIntegralClosure _root_.chosenFinitePlaceCompletionAlgebra _root_.chosenFinitePlaceCompletionContinuousSMul _root_.chosenFinitePlaceCompletionFiniteDimensional _root_.chosenFinitePlaceCompletionLocallyCompactSpace _root_.chosenFinitePlaceLocalizedFiniteDimensional _root_.chosenFinitePlaceLocalizedIntegerAlgebra _root_.chosenFinitePlaceLocalizedIntegerModuleFinite _root_.chosenFinitePlaceLocalizedIsGalois _root_.chosenFinitePlaceLocalizedIsIntegralClosure _root_.chosenFinitePlaceLocalizedIsNonarchimedeanLocalField _root_.chosenFinitePlaceLocalizedIsValuativeTopology _root_.chosenFinitePlaceLocalizedLocallyCompactSpace _root_.chosenFinitePlaceLocalizedValuationCompatible _root_.chosenFinitePlaceLocalizedValuationHasExtension _root_.chosenFinitePlaceLocalizedValuationIsNontrivial _root_.chosenFinitePlaceLocalizedValuativeRel _root_.chosenFinitePlaceLocalizedValuativeRelIsNontrivial _root_.chosenFinitePlaceLocalizedValued
attribute [-simp] _root_.IsDiscreteValuationRing.addVal_ringEquiv _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.OAI.PrimeDegreePackets.ThetaConstruction.schwartzCM_apply _root_.finiteIdeleOfSPlaceFactors_apply_mem _root_.finiteIdeleOfSPlaceFactors_apply_notMem _root_.ideleSupportedAtEquivSPlaceFactors_infinite _root_.ideleSupportedAtEquivSPlaceFactors_inside _root_.ideleSupportedAtEquivSPlaceFactors_outside_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

/-!
# Extension of ideles and ideal classes

For a finite Galois extension of number fields, scalar extension of the
relative adele algebra followed by the relative-to-ordinary comparison
gives the usual extension map on ideles.  This file descends that map to
idele classes and compares it with extension of fractional ideals and
ideal classes.
-/

open scoped NumberField TensorProduct nonZeroDivisors
open NumberField IsDedekindDomain

noncomputable section

open AlgebraicNumberTheory.Valuations

universe u v w

variable
    (K : Type u) (L : Type v)
    [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]

omit [IsGalois K L] in
/-- On a base-field local unit, the finite relative-to-ordinary
comparison is the canonical map to the chosen place above it. -/
theorem finitePlaceTensorUnitsEquivAboveAdic_localIdeleInclusion
    (w : HeightOneSpectrum (𝓞 K))
    (W : {W : HeightOneSpectrum (𝓞 L) //
      finitePlaceBelow (K := K) W = w})
    (x : (w.adicCompletion K)ˣ) :
    finitePlaceTensorUnitsEquivAboveAdic
        (K := K) (L := L) w
        (localIdeleInclusion
          (K := K) (L := L) w x) W =
      Units.map
        (finitePlaceAdicCompletionMap K L w W).toMonoidHom
        x := by
  obtain ⟨a, rfl⟩ :=
    (finitePlaceExtensionEquivAbove
      (K := K) (L := L) w).surjective W
  rw [finitePlaceTensorUnitsEquivAboveAdic_apply_extension]
  apply Units.ext
  simp only [Units.coe_map, Units.coe_mapEquiv,
    finitePlaceLocalTensorDecompositionUnitsComponent_coe,
    localIdeleInclusion]
  change
    finitePlaceExtensionAdicCompletionRingEquiv
        (K := K) (L := L) w a
        (finitePlaceLocalTensorDecompositionComponent
          (K := K) (L := L) w a
          ((x : w.adicCompletion K) ⊗ₜ[K] 1)) =
      finitePlaceAdicCompletionMap K L w
        (finitePlaceExtensionEquivAbove
          (K := K) (L := L) w a)
        (x : w.adicCompletion K)
  rw [finitePlaceLocalTensorDecompositionComponent_tmul]
  simp only [map_one, mul_one]
  exact
    finitePlaceExtensionAdicCompletionMap_eq_finitePlaceAdicCompletionMap
      K L w a (x : w.adicCompletion K)

namespace FractionalIdealGroup

omit [FiniteDimensional K L] [IsGalois K L] in
/-- At a place above `w`, the exponent of the extended prime is the
ramification index. -/
theorem count_extension_prime
    (w : HeightOneSpectrum (𝓞 K))
    (W : HeightOneSpectrum (𝓞 L))
    (hW : _root_.finitePlaceBelow (K := K) W = w) :
    FractionalIdeal.count L W
      ((extension K L (prime w) : FractionalIdealGroup L) :
        FractionalIdeal (nonZeroDivisors (𝓞 L)) L) =
      (w.asIdeal.ramificationIdx' W.asIdeal : ℤ) := by
  let : W.asIdeal.LiesOver w.asIdeal := by
    constructor
    exact congrArg HeightOneSpectrum.asIdeal hW.symm
  have hmap :
      w.asIdeal.map (algebraMap (𝓞 K) (𝓞 L)) ≠ ⊥ :=
    Ideal.map_ne_bot_of_ne_bot w.ne_bot
  rw [extension_prime_val,
    FractionalIdeal.count_coe L W hmap,
    Ideal.count_associates_factors_eq
      hmap W.isPrime W.ne_bot]
  norm_cast
  rw [←
    Ideal.IsDedekindDomain.ramificationIdx_eq_normalizedFactors_count
      w.asIdeal W.asIdeal hmap]
  exact
    (Ideal.ramificationIdx'_eq_ramificationIdx
      w.asIdeal W.asIdeal w.ne_bot).symm

omit [FiniteDimensional K L] [IsGalois K L] in
/-- A prime below a different place has zero exponent after extension. -/
theorem count_extension_prime_ne
    (w : HeightOneSpectrum (𝓞 K))
    (W : HeightOneSpectrum (𝓞 L))
    (hW : _root_.finitePlaceBelow (K := K) W ≠ w) :
    FractionalIdeal.count L W
      ((extension K L (prime w) : FractionalIdealGroup L) :
        FractionalIdeal (nonZeroDivisors (𝓞 L)) L) = 0 := by
  have hmap :
      w.asIdeal.map (algebraMap (𝓞 K) (𝓞 L)) ≠ ⊥ :=
    Ideal.map_ne_bot_of_ne_bot w.ne_bot
  rw [extension_prime_val,
    FractionalIdeal.count_coe L W hmap,
    Ideal.count_associates_factors_eq
      hmap W.isPrime W.ne_bot]
  norm_cast
  rw [Multiset.count_eq_zero]
  intro hmem
  have hprimes :
      W.asIdeal ∈ w.asIdeal.primesOver (𝓞 L) :=
    (Ideal.mem_primesOver_iff_mem_normalizedFactors
      (𝓞 L) w.ne_bot).2 hmem
  apply hW
  apply HeightOneSpectrum.ext
  rw [_root_.finitePlaceBelow_asIdeal]
  exact hprimes.2.over.symm

omit [FiniteDimensional K L] [IsGalois K L] in
/-- The exponent formula for extension of a fractional ideal presented
by its prime factorization. -/
theorem count_extension_factorization
    (exps : Multiplicative
      (HeightOneSpectrum (𝓞 K) →₀ ℤ))
    (W : HeightOneSpectrum (𝓞 L)) :
    FractionalIdeal.count L W
      ((extension K L
          (factorization exps) : FractionalIdealGroup L) :
        FractionalIdeal (nonZeroDivisors (𝓞 L)) L) =
      ((_root_.finitePlaceBelow
          (K := K) W).asIdeal.ramificationIdx' W.asIdeal : ℤ) *
        exps.toAdd
          (_root_.finitePlaceBelow (K := K) W) := by
  classical
  change FractionalIdeal.count L W
      (((extension K L)
        (exps.toAdd.prod fun v n =>
          primePowerHom v (Multiplicative.ofAdd n)) :
          FractionalIdealGroup L) :
        FractionalIdeal (nonZeroDivisors (𝓞 L)) L) = _
  rw [Finsupp.prod, map_prod]
  simp only [primePowerHom, MonoidHom.mk'_apply,
    toAdd_ofAdd, map_zpow]
  have hcoe :
      (((∏ v ∈ exps.toAdd.support,
          extension K L (prime v) ^ exps.toAdd v) :
            FractionalIdealGroup L) :
          FractionalIdeal (nonZeroDivisors (𝓞 L)) L) =
        ∏ v ∈ exps.toAdd.support,
          (((extension K L (prime v) :
            FractionalIdealGroup L) :
              FractionalIdeal (nonZeroDivisors (𝓞 L)) L) ^
            exps.toAdd v) := by
    simp
  rw [hcoe, FractionalIdeal.count_prod]
  · simp only [FractionalIdeal.count_zpow]
    by_cases hbelow :
        _root_.finitePlaceBelow
          (K := K) W ∈ exps.toAdd.support
    · rw [Finset.sum_eq_single
          (_root_.finitePlaceBelow (K := K) W)]
      · rw [count_extension_prime K L
          (_root_.finitePlaceBelow (K := K) W) W rfl]
        ring
      · intro v hv hne
        rw [count_extension_prime_ne K L v W]
        · simp
        · exact Ne.symm hne
      · exact fun h => (h hbelow).elim
    · have hzero :
          exps.toAdd
            (_root_.finitePlaceBelow (K := K) W) = 0 :=
        Finsupp.notMem_support_iff.mp hbelow
      rw [hzero, mul_zero]
      apply Finset.sum_eq_zero
      intro v hv
      rw [count_extension_prime_ne K L v W]
      · simp
      · intro h
        apply hbelow
        simpa [h] using hv
  · intro v hv
    exact zpow_ne_zero _ (Units.ne_zero
      (extension K L (prime v)))

omit [FiniteDimensional K L] [IsGalois K L] in
/-- Extension multiplies the exponent at `W` by the ramification index
over the place below `W`. -/
theorem count_extension
    (I : FractionalIdealGroup K)
    (W : HeightOneSpectrum (𝓞 L)) :
    FractionalIdeal.count L W
      ((extension K L I : FractionalIdealGroup L) :
        FractionalIdeal (nonZeroDivisors (𝓞 L)) L) =
      ((_root_.finitePlaceBelow
          (K := K) W).asIdeal.ramificationIdx' W.asIdeal : ℤ) *
        FractionalIdeal.count K
          (_root_.finitePlaceBelow (K := K) W)
          (I : FractionalIdeal
            (nonZeroDivisors (𝓞 K)) K) := by
  obtain ⟨exps, rfl⟩ :=
    factorization_surjective (K := K) I
  rw [count_extension_factorization,
    count_factorization]

end FractionalIdealGroup

namespace IdeleGroup

/-- The usual extension map on ideles, constructed through the relative
tensor-product presentation. -/
noncomputable def extension :
    IdeleGroup K →* IdeleGroup L :=
  relativeIdeleBaseChangeMulEquiv.toMonoidHom.comp
    (RelativeIdeleGroup.inclusion K L)

omit [IsGalois K L] in
theorem extension_infiniteComponent
    (a : IdeleGroup K)
    (W : InfinitePlace L) :
    infiniteComponent W (extension K L a) =
      letI : Algebra.IsIntegral K L :=
        Algebra.IsIntegral.of_finite K L
      let v :=
        _root_.infinitePlaceBelow (K := K) W
      letI : W.1.LiesOver v.1 := ⟨rfl⟩
      Units.map
        (NumberField.LiesOver.completionMap
          (v := v) (w := W))
        (infiniteComponent v a) := by
  let : Algebra.IsIntegral K L :=
    Algebra.IsIntegral.of_finite K L
  let : Algebra.IsSeparable K L :=
    Algebra.IsSeparable.of_integral K L
  let v :=
    _root_.infinitePlaceBelow (K := K) W
  let : W.1.LiesOver v.1 := ⟨rfl⟩
  apply Units.ext
  change
    (ContinuousMulEquiv.piUnits (extension K L a).1 W :
      W.Completion) = _
  change
    (ContinuousMulEquiv.piUnits
      (_root_.relativeIdeleBaseChangeMulEquiv
        (K := K) (L := L)
        (RelativeIdeleGroup.inclusion K L a)).1 W :
      W.Completion) = _
  rw [_root_.relativeIdeleBaseChangeMulEquiv_infinite]
  let f :=
    _root_.relativeInfiniteTensorPiMulEquiv
      (K := K) (L := L)
      ((_root_.relativeIdeleToLocalData
        (K := K) (L := L)
        (RelativeIdeleGroup.inclusion K L a)).infinite)
  change
    (ContinuousMulEquiv.piUnits
      (ContinuousMulEquiv.piUnits.symm f) W :
      W.Completion) = _
  rw [ContinuousMulEquiv.piUnits.apply_symm_apply]
  dsimp only [f]
  rw [_root_.relativeInfiniteTensorPiMulEquiv_apply]
  simp only [_root_.relativeIdeleToLocalData]
  rw [RelativeIdeleGroup.infiniteComponent_inclusion]
  rw [_root_.infinitePlaceTensorUnitsEquivAbove_apply]
  simp only [Units.coe_map]
  change
    _root_.infinitePlaceTensorRingEquivAbove
        (K := K) (L := L) v
        ((infiniteComponent v a : v.Completion) ⊗ₜ[K] (1 : L))
        ⟨W, rfl⟩ =
      NumberField.LiesOver.completionMap
        (v := v) (w := W)
        (infiniteComponent v a : v.Completion)
  simpa only [map_one, mul_one] using
    (_root_.infinitePlaceTensorRingEquivAbove_tmul
      (K := K) (L := L) v ⟨W, rfl⟩
      (infiniteComponent v a : v.Completion) (1 : L))

omit [IsGalois K L] in
/-- The finite component of an extended idele is the canonical local
completion map applied to the component below it. -/
@[simp]
theorem extension_finiteComponent
    (a : IdeleGroup K)
    (W : HeightOneSpectrum (𝓞 L)) :
    finiteComponent W (extension K L a) =
      Units.map
        (finitePlaceAdicCompletionMap K L
          (_root_.finitePlaceBelow (K := K) W)
          ⟨W, rfl⟩).toMonoidHom
        (finiteComponent
          (_root_.finitePlaceBelow (K := K) W) a) := by
  change (extension K L a).2 W = _
  rw [extension, MonoidHom.comp_apply]
  change
    (relativeIdeleBaseChangeMulEquiv
      (K := K) (L := L)
      (RelativeIdeleGroup.inclusion K L a)).2 W = _
  rw [
    relativeIdeleBaseChangeMulEquiv_finite,
    _root_.relativeFiniteIdeleToFiniteIdele_apply,
    _root_.relativeFiniteTensorPiMulEquiv_apply]
  change
    _root_.finitePlaceTensorUnitsEquivAboveAdic
        (K := K) (L := L)
        (_root_.finitePlaceBelow (K := K) W)
        ((_root_.relativeIdeleToLocalData
          (K := K) (L := L)
          (RelativeIdeleGroup.inclusion K L a)).finite
            (_root_.finitePlaceBelow (K := K) W))
        ⟨W, rfl⟩ =
      _
  simp only [_root_.relativeIdeleToLocalData]
  rw [RelativeIdeleGroup.finiteComponent_inclusion,
    _root_.finitePlaceTensorUnitsEquivAboveAdic_localIdeleInclusion]

omit [IsGalois K L] in
/-- Extension of a principal idele is the corresponding principal idele
of the extension field. -/
@[simp]
theorem extension_principalIdele (x : Kˣ) :
    extension K L (principalIdele K x) =
      principalIdele L
        (Units.map (algebraMap K L).toMonoidHom x) := by
  rw [extension, MonoidHom.comp_apply,
    RelativeIdeleGroup.inclusion_principalIdele]
  apply Prod.ext
  · apply Units.ext
    funext W
    change
      _root_.infinitePlaceTensorUnitsEquivAbove
          (K := K) (L := L)
          (_root_.infinitePlaceBelow (K := K) W)
          ((_root_.relativeIdeleToLocalData
            (K := K) (L := L)
            (RelativeIdeleGroup.principalIdele K L
              (Units.map (algebraMap K L).toMonoidHom x))).infinite
              (_root_.infinitePlaceBelow (K := K) W))
          ⟨W, rfl⟩ =
        algebraMap L W.Completion
          (algebraMap K L (x : K))
    simp only [_root_.relativeIdeleToLocalData]
    rw [RelativeIdeleGroup.infiniteComponent_principalIdele]
    rw [
      _root_.infinitePlaceTensorUnitsEquivAbove_localFieldIdeleInclusion]
    simp
  · change
      (relativeIdeleBaseChangeMulEquiv
        (K := K) (L := L)
        (RelativeIdeleGroup.principalIdele K L
          (Units.map (algebraMap K L).toMonoidHom x))).2 =
        (principalIdele L
          (Units.map (algebraMap K L).toMonoidHom x)).2
    rw [relativeIdeleBaseChangeMulEquiv_finite]
    apply RestrictedProduct.ext
    intro W
    rw [_root_.relativeFiniteIdeleToFiniteIdele_apply,
      _root_.relativeFiniteTensorPiMulEquiv_apply]
    change
      _root_.finitePlaceTensorUnitsEquivAboveAdic
          (K := K) (L := L)
          (_root_.finitePlaceBelow (K := K) W)
          ((_root_.relativeIdeleToLocalData
            (K := K) (L := L)
            (RelativeIdeleGroup.principalIdele K L
              (Units.map (algebraMap K L).toMonoidHom x))).finite
              (_root_.finitePlaceBelow (K := K) W))
          ⟨W, rfl⟩ =
        Units.map (FinitePlace.embedding (K := L) W)
          (Units.map (algebraMap K L).toMonoidHom x)
    simp only [_root_.relativeIdeleToLocalData]
    rw [RelativeIdeleGroup.finiteComponent_principalIdele]
    rw [
      _root_.finitePlaceTensorUnitsEquivAboveAdic_localFieldIdeleInclusion]

/-- Extension of ideles along the identity field extension is the
identity homomorphism. -/
@[simp]
theorem extension_self :
    extension K K = MonoidHom.id (IdeleGroup K) := by
  apply MonoidHom.ext
  intro a
  apply Prod.ext
  · apply ContinuousMulEquiv.piUnits.injective
    funext W
    change
      infiniteComponent W (extension K K a) =
        infiniteComponent W a
    rw [extension_infiniteComponent]
    dsimp only
    have hmap
        (v : InfinitePlace K)
        (hv : v = W)
        [hov : W.1.LiesOver v.1] :
        Units.map
            (NumberField.LiesOver.completionMap
              (v := v) (w := W)).toMonoidHom
            (infiniteComponent v a) =
          infiniteComponent W a := by
      subst v
      apply Units.ext
      change
        NumberField.LiesOver.completionMap
            (v := W) (w := W)
            (infiniteComponent W a : W.Completion) =
          (infiniteComponent W a : W.Completion)
      exact
        _root_.infinitePlaceCompletionMap_self_apply
          (K := K) W
          (infiniteComponent W a : W.Completion)
    exact
      hmap
        (_root_.infinitePlaceBelow (K := K) W)
        (_root_.infinitePlaceBelow_self (K := K) W)
        (hov := ⟨rfl⟩)
  · apply RestrictedProduct.ext
    intro W
    change
      finiteComponent W (extension K K a) =
        finiteComponent W a
    rw [extension_finiteComponent]
    dsimp only
    have hmap
        (v : HeightOneSpectrum (𝓞 K))
        (hbelow :
          _root_.finitePlaceBelow (K := K) W = v)
        (hv : v = W) :
        Units.map
            (finitePlaceAdicCompletionMap K K v
              ⟨W, hbelow⟩).toMonoidHom
            (finiteComponent v a) =
          finiteComponent W a := by
      subst v
      apply Units.ext
      change
        finitePlaceAdicCompletionMap K K W
            ⟨W,
              _root_.finitePlaceBelow_self
                (K := K) W⟩
            (finiteComponent W a : W.adicCompletion K) =
          (finiteComponent W a : W.adicCompletion K)
      exact
        _root_.finitePlaceAdicCompletionMap_self_apply K W
          (finiteComponent W a : W.adicCompletion K)
    exact
      hmap
        (_root_.finitePlaceBelow (K := K) W)
        rfl
        (_root_.finitePlaceBelow_self (K := K) W)

end IdeleGroup

/-- The usual extension map on idele classes. -/
noncomputable def ideleClassExtension :
    IdeleClassGroup K →* IdeleClassGroup L :=
  QuotientGroup.map
    (IdeleGroup.principalSubgroup K)
    (IdeleGroup.principalSubgroup L)
    (IdeleGroup.extension K L)
    (by
      rintro _ ⟨x, rfl⟩
      exact
        ⟨Units.map (algebraMap K L).toMonoidHom x,
          (IdeleGroup.extension_principalIdele K L x).symm⟩)

omit [IsGalois K L] in
@[simp]
theorem ideleClassExtension_mk (a : IdeleGroup K) :
    ideleClassExtension K L
        (QuotientGroup.mk'
          (IdeleGroup.principalSubgroup K) a) =
      QuotientGroup.mk'
        (IdeleGroup.principalSubgroup L)
        (IdeleGroup.extension K L a) :=
  rfl

/-- Extension of idele classes along the identity field extension is
the identity homomorphism. -/
@[simp]
theorem ideleClassExtension_self :
    ideleClassExtension K K =
      MonoidHom.id (IdeleClassGroup K) := by
  apply MonoidHom.ext
  intro c
  refine QuotientGroup.induction_on c ?_
  intro a
  change
    ideleClassExtension K K
        (QuotientGroup.mk'
          (IdeleGroup.principalSubgroup K) a) =
      QuotientGroup.mk'
        (IdeleGroup.principalSubgroup K) a
  rw [ideleClassExtension_mk,
    IdeleGroup.extension_self]
  rfl
end
end

section
-- module Solutions.OAIQ244_DUKE.AlgebraicNumberTheory_Idele_Extension_IdeleClassBaseChange
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.KummerTheory.primeCyclotomicBaseFiniteDimensional _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.residueFieldZModAlgebra _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedIntegralAlgebraContextValuationSubringAlgebra _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.CyclicCohomology.binaryCoefficientFamilyCommGroup _root_.LocalClassFieldTheory.normalizationIntegerRingIsIntegralClosure _root_.chosenFinitePlaceCompletionAlgebra _root_.chosenFinitePlaceCompletionFiniteDimensional _root_.chosenFinitePlaceLocalizedFiniteDimensional
attribute [-simp] _root_.IsDiscreteValuationRing.addVal_ringEquiv _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.OAI.PrimeDegreePackets.ThetaConstruction.schwartzCM_apply _root_.finiteIdeleOfSPlaceFactors_apply_mem _root_.finiteIdeleOfSPlaceFactors_apply_notMem _root_.ideleSupportedAtEquivSPlaceFactors_infinite _root_.ideleSupportedAtEquivSPlaceFactors_inside _root_.ideleSupportedAtEquivSPlaceFactors_outside_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

/-!
# Relative and ordinary idele classes

The tensor-product presentation of the ideles of a finite Galois
extension is canonically equivalent to the ordinary restricted-product
presentation.  This file descends that equivalence through principal
ideles and identifies relative class inclusion with the concrete
extension map on ordinary idele classes.
-/

open scoped NumberField TensorProduct
open NumberField

noncomputable section

universe u v

variable
    {K : Type u} {L : Type v}
    [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]

/-- Scalar extension identifies the relative and ordinary principal
idele subgroups. -/
theorem relativeIdelePrincipalSubgroup_map_baseChange :
    (RelativeIdeleGroup.principalSubgroup K L).map
        (relativeIdeleBaseChangeMulEquiv
          (K := K) (L := L)).toMonoidHom =
      IdeleGroup.principalSubgroup L := by
  ext y
  constructor
  · rintro ⟨z, ⟨x, hx⟩, rfl⟩
    rw [← hx]
    exact
      ⟨x,
        (relativeIdeleBaseChangeMulEquiv_principalIdele
          (K := K) (L := L) x).symm⟩
  · rintro ⟨x, rfl⟩
    refine
      ⟨RelativeIdeleGroup.principalIdele K L x,
        ⟨x, rfl⟩, ?_⟩
    exact
      relativeIdeleBaseChangeMulEquiv_principalIdele
        (K := K) (L := L) x

/-- Scalar extension identifies the relative presentation of the idele
class group with the ordinary idele class group of the extension field. -/
noncomputable def relativeIdeleClassBaseChangeMulEquiv :
    RelativeIdeleGroup.ClassGroup K L ≃*
      IdeleClassGroup L :=
  QuotientGroup.congr
    (RelativeIdeleGroup.principalSubgroup K L)
    (IdeleGroup.principalSubgroup L)
    (relativeIdeleBaseChangeMulEquiv
      (K := K) (L := L))
    (relativeIdelePrincipalSubgroup_map_baseChange
      (K := K) (L := L))

@[simp]
theorem relativeIdeleClassBaseChangeMulEquiv_mk
    (z : RelativeIdeleGroup K L) :
    relativeIdeleClassBaseChangeMulEquiv
        (K := K) (L := L)
        (QuotientGroup.mk'
          (RelativeIdeleGroup.principalSubgroup K L) z) =
      QuotientGroup.mk'
        (IdeleGroup.principalSubgroup L)
        (relativeIdeleBaseChangeMulEquiv
          (K := K) (L := L) z) :=
  rfl

/-- Under the relative-to-ordinary comparison, relative class inclusion
is the concrete extension map on ordinary idele classes. -/
@[simp]
theorem relativeIdeleClassBaseChangeMulEquiv_classInclusion
    (c : IdeleClassGroup K) :
    relativeIdeleClassBaseChangeMulEquiv
        (K := K) (L := L)
        (RelativeIdeleGroup.classInclusion K L c) =
      ideleClassExtension K L c := by
  refine QuotientGroup.induction_on c ?_
  intro a
  rfl
end
end

section
-- module Solutions.OAIQ244_DUKE.AlgebraicNumberTheory_Idele_Extension_IdeleNorm
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.KummerTheory.primeCyclotomicBaseFiniteDimensional _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.residueFieldZModAlgebra _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedIntegralAlgebraContextValuationSubringAlgebra _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.CyclicCohomology.binaryCoefficientFamilyCommGroup _root_.LocalClassFieldTheory.normalizationIntegerRingIsIntegralClosure _root_.chosenFinitePlaceCompletionAlgebra _root_.chosenFinitePlaceCompletionFiniteDimensional _root_.chosenFinitePlaceLocalizedFiniteDimensional
attribute [-simp] _root_.IdeleGroup.extension_finiteComponent _root_.IdeleGroup.extension_principalIdele _root_.IdeleGroup.extension_self _root_.IsDiscreteValuationRing.addVal_ringEquiv _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.OAI.PrimeDegreePackets.ThetaConstruction.schwartzCM_apply _root_.finiteIdeleOfSPlaceFactors_apply_mem _root_.finiteIdeleOfSPlaceFactors_apply_notMem _root_.ideleClassExtension_mk _root_.ideleClassExtension_self _root_.ideleSupportedAtEquivSPlaceFactors_infinite _root_.ideleSupportedAtEquivSPlaceFactors_inside _root_.ideleSupportedAtEquivSPlaceFactors_outside_coe _root_.relativeIdeleClassBaseChangeMulEquiv_classInclusion _root_.relativeIdeleClassBaseChangeMulEquiv_mk
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

/-!
# The norm on ordinary ideles

The relative idele group carries the determinant norm.  The
scalar-extension equivalence with the ordinary ideles of the extension
field transports that existing norm to the usual map
`N_{L/K} : I_L → I_K`.
-/

open scoped NumberField
open NumberField

noncomputable section

namespace IdeleGroup

universe u v

variable
    (K : Type u) (L : Type v)
    [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]

/-- The ordinary idele norm `N_{L/K} : I_L → I_K`, transported from
the determinant norm on the relative idele group. -/
noncomputable def norm :
    IdeleGroup L →* IdeleGroup K :=
  (RelativeIdeleGroup.norm K L).comp
    (relativeIdeleBaseChangeMulEquiv
      (K := K) (L := L)).symm.toMonoidHom

@[simp]
theorem norm_relativeIdeleBaseChangeMulEquiv
    (z : RelativeIdeleGroup K L) :
    norm K L
        (relativeIdeleBaseChangeMulEquiv
          (K := K) (L := L) z) =
      RelativeIdeleGroup.norm K L z := by
  simp [norm]

/-- On principal ideles, the ordinary idele norm is induced by the
field norm. -/
@[simp]
theorem norm_principalIdele
    (x : Lˣ) :
    norm K L (principalIdele L x) =
      principalIdele K (Units.map (Algebra.norm K) x) := by
  rw [← relativeIdeleBaseChangeMulEquiv_principalIdele
    (K := K) (L := L) x]
  rw [norm_relativeIdeleBaseChangeMulEquiv,
    RelativeIdeleGroup.norm_principalIdele]

end IdeleGroup

universe u v

variable
    (K : Type u) (L : Type v)
    [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]

/-- The ordinary idele-class norm `N_{L/K} : C_L → C_K`. -/
noncomputable def ideleClassNorm :
    IdeleClassGroup L →* IdeleClassGroup K :=
  QuotientGroup.map
    (IdeleGroup.principalSubgroup L)
    (IdeleGroup.principalSubgroup K)
    (IdeleGroup.norm K L)
    (by
      rintro _ ⟨x, rfl⟩
      exact
        ⟨Units.map (Algebra.norm K) x,
          (IdeleGroup.norm_principalIdele K L x).symm⟩)

@[simp]
theorem ideleClassNorm_mk
    (a : IdeleGroup L) :
    ideleClassNorm K L
        (QuotientGroup.mk'
          (IdeleGroup.principalSubgroup L) a) =
      QuotientGroup.mk'
        (IdeleGroup.principalSubgroup K)
        (IdeleGroup.norm K L a) :=
  rfl
end
end

section
-- module Solutions.OAIQ244_DUKE.AlgebraicNumberTheory_Idele_ClassGroup_NormComparison
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.KummerTheory.primeCyclotomicBaseFiniteDimensional _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.residueFieldZModAlgebra _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedIntegralAlgebraContextValuationSubringAlgebra _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.CyclicCohomology.binaryCoefficientFamilyCommGroup _root_.LocalClassFieldTheory.normalizationIntegerRingIsIntegralClosure _root_.chosenFinitePlaceCompletionAlgebra _root_.chosenFinitePlaceCompletionFiniteDimensional _root_.chosenFinitePlaceLocalizedFiniteDimensional
attribute [-simp] _root_.IsDiscreteValuationRing.addVal_ringEquiv _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.OAI.PrimeDegreePackets.ThetaConstruction.schwartzCM_apply _root_.finiteIdeleOfSPlaceFactors_apply_mem _root_.finiteIdeleOfSPlaceFactors_apply_notMem _root_.ideleSupportedAtEquivSPlaceFactors_infinite _root_.ideleSupportedAtEquivSPlaceFactors_inside _root_.ideleSupportedAtEquivSPlaceFactors_outside_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

/-!
# Relative and ordinary idele-class norms

The determinant norm on relative ideles and the ordinary idele norm give
the same map after the canonical scalar-extension equivalence
`C(𝔸_K ⊗_K L) ≃ C_L`.  This comparison lets the cohomological results
proved in relative coordinates be stated with the usual norm
`N_{L/K} : C_L → C_K`.
-/

open scoped NumberField
open NumberField

noncomputable section

namespace RelativeIdeleGroup

universe u v w

variable
    {K : Type u} {L : Type v} {M : Type w}
    [Field K] [NumberField K]
    [Field L] [Field M]
    [Algebra K L] [Algebra K M]
    [FiniteDimensional K L] [FiniteDimensional K M]

/-- A field embedding into an ambient finite extension, descended from
relative ideles to the existing relative idele class groups. -/
noncomputable def classEmbedding
    (f : L →ₐ[K] M) :
    RelativeIdeleGroup.ClassGroup K L →*
      RelativeIdeleGroup.ClassGroup K M :=
  QuotientGroup.map
    (RelativeIdeleGroup.principalSubgroup K L)
    (RelativeIdeleGroup.principalSubgroup K M)
    (RelativeIdeleGroup.ideleEmbedding f)
    (by
      rintro _ ⟨x, rfl⟩
      refine ⟨Units.map f x, ?_⟩
      apply Units.ext
      rfl)

omit [FiniteDimensional K L] [FiniteDimensional K M] in
@[simp]
theorem classEmbedding_mk
    (f : L →ₐ[K] M)
    (a : RelativeIdeleGroup K L) :
    classEmbedding f
        (QuotientGroup.mk'
          (RelativeIdeleGroup.principalSubgroup K L) a) =
      QuotientGroup.mk'
        (RelativeIdeleGroup.principalSubgroup K M)
        (RelativeIdeleGroup.ideleEmbedding f a) :=
  rfl

end RelativeIdeleGroup

variable
    {K L : Type*}
    [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    [IsGalois K L]

omit [IsGalois K L] in
/-- The relative determinant norm is the ordinary idele-class norm after
the canonical base-change equivalence. -/
@[simp]
theorem ordinaryIdeleClassNorm_relativeIdeleClassBaseChange
    (c : RelativeIdeleGroup.ClassGroup K L) :
    _root_.ideleClassNorm K L
        (relativeIdeleClassBaseChangeMulEquiv
          (K := K) (L := L) c) =
      RelativeIdeleGroup.classNorm K L c := by
  refine QuotientGroup.induction_on c ?_
  intro a
  change
    QuotientGroup.mk'
        (IdeleGroup.principalSubgroup K)
        (IdeleGroup.norm K L
          (relativeIdeleBaseChangeMulEquiv
            (K := K) (L := L) a)) =
      QuotientGroup.mk'
        (IdeleGroup.principalSubgroup K)
        (RelativeIdeleGroup.norm K L a)
  rw [IdeleGroup.norm_relativeIdeleBaseChangeMulEquiv]
end
end

section
-- module Solutions.OAIQ244_DUKE.AlgebraicNumberTheory_Idele_ClassGroup_AlgEquiv
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.KummerTheory.primeCyclotomicBaseFiniteDimensional _root_.KummerTheory.primeCyclotomicBaseNumberField _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.residueFieldZModAlgebra _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedIntegralAlgebraContextValuationSubringAlgebra _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.PrimeDegreePackets.diagonalLogAction _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.CyclicCohomology.binaryCoefficientFamilyCommGroup _root_.LocalClassFieldTheory.normalizationIntegerRingIsIntegralClosure _root_.chosenFinitePlaceBaseValued _root_.chosenFinitePlaceCompletionAlgebra _root_.chosenFinitePlaceCompletionFiniteDimensional _root_.chosenFinitePlaceLocalizedFiniteDimensional
attribute [-simp] _root_.IsDiscreteValuationRing.addVal_ringEquiv _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.OAI.PrimeDegreePackets.ThetaConstruction.schwartzCM_apply _root_.finiteIdeleOfSPlaceFactors_apply_mem _root_.finiteIdeleOfSPlaceFactors_apply_notMem _root_.ideleSupportedAtEquivSPlaceFactors_infinite _root_.ideleSupportedAtEquivSPlaceFactors_inside _root_.ideleSupportedAtEquivSPlaceFactors_outside_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

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

/-- A base-field algebra equivalence between two realizations of a finite
extension induces the canonical equivalence between their relative adele
algebras. -/
noncomputable def relativeAdeleCongr
    (e : L ≃ₐ[K] M) :
    RelativeAdeleRing K L ≃ₐ[
      NumberField.AdeleRing (𝓞 K) K]
      RelativeAdeleRing K M :=
  Algebra.TensorProduct.congr AlgEquiv.refl e

@[simp]
theorem relativeAdeleCongr_tmul
    (e : L ≃ₐ[K] M)
    (a : NumberField.AdeleRing (𝓞 K) K)
    (x : L) :
    relativeAdeleCongr (K := K) e (a ⊗ₜ[K] x) =
      a ⊗ₜ[K] e x :=
  rfl

/-- The canonical transport of relative ideles along an isomorphic
realization of the top field. -/
noncomputable def relativeIdeleCongr
    (e : L ≃ₐ[K] M) :
    RelativeIdeleGroup K L ≃*
      RelativeIdeleGroup K M :=
  Units.mapEquiv
    (relativeAdeleCongr (K := K) e).toMulEquiv

@[simp]
theorem relativeIdeleCongr_coe
    (e : L ≃ₐ[K] M)
    (a : RelativeIdeleGroup K L) :
    ((relativeIdeleCongr (K := K) e a :
        RelativeIdeleGroup K M) :
      RelativeAdeleRing K M) =
        relativeAdeleCongr (K := K) e
          (a : RelativeAdeleRing K L) :=
  rfl

/-- Transport of relative ideles sends a principal idele to the principal
idele of the transported field unit. -/
@[simp]
theorem relativeIdeleCongr_principalIdele
    (e : L ≃ₐ[K] M)
    (x : Lˣ) :
    relativeIdeleCongr (K := K) e
        (RelativeIdeleGroup.principalIdele K L x) =
      RelativeIdeleGroup.principalIdele K M
        (Units.mapEquiv e.toMulEquiv x) := by
  apply Units.ext
  change
    relativeAdeleCongr (K := K) e
        ((1 : NumberField.AdeleRing (𝓞 K) K) ⊗ₜ[K] (x : L)) =
      (1 : NumberField.AdeleRing (𝓞 K) K) ⊗ₜ[K] e (x : L)
  rfl

/-- The canonical transport identifies the two principal-relative-idele
subgroups. -/
theorem relativeIdelePrincipalSubgroup_map_congr
    (e : L ≃ₐ[K] M) :
    (RelativeIdeleGroup.principalSubgroup K L).map
        (relativeIdeleCongr (K := K) e) =
      RelativeIdeleGroup.principalSubgroup K M := by
  ext y
  constructor
  · rintro ⟨z, ⟨x, hx⟩, rfl⟩
    rw [← hx]
    exact
      ⟨Units.mapEquiv e.toMulEquiv x,
        (relativeIdeleCongr_principalIdele
          (K := K) e x).symm⟩
  · rintro ⟨y, rfl⟩
    obtain ⟨x, rfl⟩ :=
      (Units.mapEquiv e.toMulEquiv).surjective y
    exact
      ⟨RelativeIdeleGroup.principalIdele K L x,
        ⟨x, rfl⟩,
        relativeIdeleCongr_principalIdele
          (K := K) e x⟩

/-- The relative idele class group is unchanged when the top field is
replaced by an isomorphic realization. -/
noncomputable def relativeIdeleClassCongr
    (e : L ≃ₐ[K] M) :
    RelativeIdeleGroup.ClassGroup K L ≃*
      RelativeIdeleGroup.ClassGroup K M :=
  QuotientGroup.congr
    (RelativeIdeleGroup.principalSubgroup K L)
    (RelativeIdeleGroup.principalSubgroup K M)
    (relativeIdeleCongr (K := K) e)
    (relativeIdelePrincipalSubgroup_map_congr
      (K := K) e)

@[simp]
theorem relativeIdeleClassCongr_mk
    (e : L ≃ₐ[K] M)
    (a : RelativeIdeleGroup K L) :
    relativeIdeleClassCongr (K := K) e
        (QuotientGroup.mk'
          (RelativeIdeleGroup.principalSubgroup K L) a) =
      QuotientGroup.mk'
        (RelativeIdeleGroup.principalSubgroup K M)
        (relativeIdeleCongr (K := K) e a) :=
  rfl

/-- The determinant norm on relative ideles is invariant under replacement
of the top field by an isomorphic realization. -/
@[simp]
theorem relativeIdeleCongr_norm
    (e : L ≃ₐ[K] M)
    (a : RelativeIdeleGroup K L) :
    RelativeIdeleGroup.norm K M
        (relativeIdeleCongr (K := K) e a) =
      RelativeIdeleGroup.norm K L a := by
  apply
    (IdeleGroup.equivAdeleRingUnits
      (K := K)).injective
  simp only [RelativeIdeleGroup.norm,
    MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
    MulEquiv.apply_symm_apply]
  apply Units.ext
  change
    Algebra.norm
        (NumberField.AdeleRing (𝓞 K) K)
        (relativeAdeleCongr (K := K) e
          (a : RelativeAdeleRing K L)) =
      Algebra.norm
        (NumberField.AdeleRing (𝓞 K) K)
        (a : RelativeAdeleRing K L)
  exact
    Algebra.norm_eq_of_algEquiv
      (relativeAdeleCongr (K := K) e)
      (a : RelativeAdeleRing K L)

section Norm

variable [FiniteDimensional K L] [FiniteDimensional K M]

/-- The descended idele-class norm is invariant under the canonical
transport of the relative idele class group. -/
@[simp]
theorem relativeIdeleClassCongr_ideleClassNorm
    (e : L ≃ₐ[K] M)
    (c : RelativeIdeleGroup.ClassGroup K L) :
    RelativeIdeleGroup.classNorm K M
        (relativeIdeleClassCongr (K := K) e c) =
      RelativeIdeleGroup.classNorm K L c := by
  refine QuotientGroup.induction_on c ?_
  intro a
  change
    QuotientGroup.mk'
        (IdeleGroup.principalSubgroup K)
        (RelativeIdeleGroup.norm K M
          (relativeIdeleCongr (K := K) e a)) =
      QuotientGroup.mk'
        (IdeleGroup.principalSubgroup K)
        (RelativeIdeleGroup.norm K L a)
  rw [relativeIdeleCongr_norm (K := K) e a]

end Norm

section Absolute

variable
    {K : Type u} {M : Type w}
    [Field K] [NumberField K] [Algebra ℚ K]
    [Field M] [NumberField M] [Algebra ℚ M]

/-- The canonical transport of ordinary adele rings along an equivalence
of number fields.  It is the existing relative-adele transport over `ℚ`,
conjugated by the relative-to-ordinary scalar-extension equivalences. -/
noncomputable def adeleCongr
    (e : K ≃ₐ[ℚ] M) :
    NumberField.AdeleRing (𝓞 K) K ≃+*
      NumberField.AdeleRing (𝓞 M) M :=
  (relativeAdeleBaseChangeRingEquiv
      (K := ℚ) (L := K)).symm |>.trans
    ((relativeAdeleCongr (K := ℚ) e).toRingEquiv.trans
      (relativeAdeleBaseChangeRingEquiv
        (K := ℚ) (L := M)))

/-- The relative-to-ordinary scalar-extension comparison is natural for
transport of the top number field. -/
theorem relativeAdeleBaseChangeRingEquiv_relativeAdeleCongr
    (e : K ≃ₐ[ℚ] M)
    (z : RelativeAdeleRing ℚ K) :
    relativeAdeleBaseChangeRingEquiv
        (K := ℚ) (L := M)
        (relativeAdeleCongr (K := ℚ) e z) =
      adeleCongr e
        (relativeAdeleBaseChangeRingEquiv
          (K := ℚ) (L := K) z) := by
  change
    relativeAdeleBaseChangeRingEquiv
        (K := ℚ) (L := M)
        (relativeAdeleCongr (K := ℚ) e z) =
      relativeAdeleBaseChangeRingEquiv
        (K := ℚ) (L := M)
        (relativeAdeleCongr (K := ℚ) e
          ((relativeAdeleBaseChangeRingEquiv
            (K := ℚ) (L := K)).symm
            (relativeAdeleBaseChangeRingEquiv
              (K := ℚ) (L := K) z)))
  rw [RingEquiv.symm_apply_apply]

/-- Transport of ordinary adeles carries the diagonal field embedding to
the diagonal field embedding. -/
@[simp]
theorem adeleCongr_algebraMap
    (e : K ≃ₐ[ℚ] M)
    (x : K) :
    adeleCongr e
        (algebraMap K
          (NumberField.AdeleRing (𝓞 K) K) x) =
      algebraMap M
        (NumberField.AdeleRing (𝓞 M) M) (e x) := by
  have hx :
      (relativeAdeleBaseChangeRingEquiv
          (K := ℚ) (L := K)).symm
          (algebraMap K
            (NumberField.AdeleRing (𝓞 K) K) x) =
        (1 : NumberField.AdeleRing (𝓞 ℚ) ℚ) ⊗ₜ[ℚ] x := by
    apply
      (relativeAdeleBaseChangeRingEquiv
        (K := ℚ) (L := K)).injective
    rw [RingEquiv.apply_symm_apply,
      relativeAdeleBaseChangeRingEquiv_fieldInclusion]
  change
    relativeAdeleBaseChangeRingEquiv
        (K := ℚ) (L := M)
        (relativeAdeleCongr (K := ℚ) e
          ((relativeAdeleBaseChangeRingEquiv
            (K := ℚ) (L := K)).symm
              (algebraMap K
                (NumberField.AdeleRing (𝓞 K) K) x))) =
      algebraMap M
        (NumberField.AdeleRing (𝓞 M) M) (e x)
  rw [hx, relativeAdeleCongr_tmul,
    relativeAdeleBaseChangeRingEquiv_fieldInclusion]

omit [NumberField K] [NumberField M] in
@[simp]
theorem finitePlaceCongr_asIdeal
    (e : K ≃ₐ[ℚ] M)
    (v : HeightOneSpectrum (𝓞 K)) :
    (finitePlaceCongr e v).asIdeal =
      v.asIdeal.map
        (NumberField.RingOfIntegers.mapRingEquiv
          e.toRingEquiv) := by
  ext x
  exact Ideal.symm_apply_mem_of_equiv_iff

theorem finitePlaceBelow_eq_finitePlaceCongr_symm
    (e : K ≃ₐ[ℚ] M)
    (W : HeightOneSpectrum (𝓞 M)) :
    letI : Algebra K M := e.toRingHom.toAlgebra
    finitePlaceBelow (K := K) W =
      (finitePlaceCongr e).symm W := by
  apply HeightOneSpectrum.ext
  rfl

/-- The canonical map between corresponding finite completions induced by
an equivalence of number fields. -/
noncomputable def finitePlaceAdicCompletionCongrHom
    (e : K ≃ₐ[ℚ] M)
    (W : HeightOneSpectrum (𝓞 M)) :
    ((finitePlaceCongr e).symm W).adicCompletion K →+*
      W.adicCompletion M := by
  letI : Algebra K M := e.toRingHom.toAlgebra
  exact
    finitePlaceAdicCompletionMap K M
      ((finitePlaceCongr e).symm W)
      ⟨W, finitePlaceBelow_eq_finitePlaceCongr_symm e W⟩

/-- On finite coordinates, canonical adelic transport is the completion
map at the corresponding finite places. -/
theorem adeleCongr_finiteComponent
    (e : K ≃ₐ[ℚ] M)
    (a : NumberField.AdeleRing (𝓞 K) K)
    (W : HeightOneSpectrum (𝓞 M)) :
    (adeleCongr e a).2 W =
      finitePlaceAdicCompletionCongrHom e W
        (a.2 ((finitePlaceCongr e).symm W)) := by
  let : Algebra K M := e.toRingHom.toAlgebra
  let : IsScalarTower ℚ K M :=
    IsScalarTower.of_algHom e.toAlgHom
  let componentK :=
    (finiteAdeleComponentAlgHom
      ((finitePlaceCongr e).symm W)).toAddMonoidHom
  let componentM :=
    (finiteAdeleComponentAlgHom W).toAddMonoidHom
  change
    componentM (adeleCongr e a) =
      finitePlaceAdicCompletionCongrHom e W
        (componentK a)
  let z :=
    (relativeAdeleBaseChangeRingEquiv
      (K := ℚ) (L := K)).symm a
  have ha :
      relativeAdeleBaseChangeRingEquiv
          (K := ℚ) (L := K) z = a :=
    (relativeAdeleBaseChangeRingEquiv
      (K := ℚ) (L := K)).apply_symm_apply a
  rw [← ha]
  have htransport :
      componentM
        (relativeAdeleBaseChangeRingEquiv
        (K := ℚ) (L := M)
        (relativeAdeleCongr (K := ℚ) e z)) =
        componentM
          (adeleCongr e
          (relativeAdeleBaseChangeRingEquiv
            (K := ℚ) (L := K) z)) :=
    congrArg
      componentM
      (relativeAdeleBaseChangeRingEquiv_relativeAdeleCongr
        e z)
  rw [← htransport]
  induction z using OAI.tensorInductionOn with
  | add x y hx hy =>
      simpa only [map_add] using congrArg₂ (· + ·) hx hy
  | tmul b x =>
      let w : HeightOneSpectrum (𝓞 K) :=
        (finitePlaceCongr e).symm W
      have hW :
          finitePlaceBelow (K := K) W = w := by
        exact finitePlaceBelow_eq_finitePlaceCongr_symm e W
      have hq :
          finitePlaceBelow (K := ℚ) w =
            finitePlaceBelow (K := ℚ) W := by
        rw [← hW, finitePlaceBelow_finitePlaceBelow]
      have hcomponent
          (q' : HeightOneSpectrum (𝓞 ℚ))
          (hq' :
            q' = finitePlaceBelow (K := ℚ) W)
          (hwq :
            finitePlaceBelow (K := ℚ) w = q') :
          finitePlaceAdicCompletionMap ℚ M
                (finitePlaceBelow (K := ℚ) W) ⟨W, rfl⟩
                (b.2 (finitePlaceBelow (K := ℚ) W)) *
              algebraMap M (W.adicCompletion M) (e x) =
            finitePlaceAdicCompletionMap K M w ⟨W, hW⟩
              (finitePlaceAdicCompletionMap ℚ K q'
                    ⟨w, hwq⟩ (b.2 q') *
                algebraMap K (w.adicCompletion K) x) := by
        subst q'
        have hx :
            finitePlaceAdicCompletionMap K M w ⟨W, hW⟩
                (algebraMap K (w.adicCompletion K) x) =
              algebraMap M (W.adicCompletion M) (e x) := by
          change
            finitePlaceAdicCompletionMap K M w ⟨W, hW⟩
                (x : w.adicCompletion K) =
              (e x : W.adicCompletion M)
          exact
            finitePlaceAdicCompletionMap_coe K M w
              ⟨W, hW⟩ x
        rw [map_mul,
          finitePlaceAdicCompletionMap_comp ℚ M (M := K)
            (finitePlaceBelow (K := ℚ) W) w W
            hwq hW rfl,
          hx]
      rw [relativeAdeleCongr_tmul]
      change
        (relativeAdeleBaseChangeRingEquiv
          (K := ℚ) (L := M)
          (b ⊗ₜ[ℚ] e x)).2 W =
          finitePlaceAdicCompletionCongrHom e W
            ((relativeAdeleBaseChangeRingEquiv
              (K := ℚ) (L := K)
              (b ⊗ₜ[ℚ] x)).2 w)
      rw [
        relativeAdeleBaseChangeRingEquiv_finiteComponent_tmul,
        relativeAdeleBaseChangeRingEquiv_finiteComponent_tmul]
      change
        finitePlaceAdicCompletionMap ℚ M
              (finitePlaceBelow (K := ℚ) W) ⟨W, rfl⟩
              (b.2 (finitePlaceBelow (K := ℚ) W)) *
            algebraMap M (W.adicCompletion M) (e x) =
          finitePlaceAdicCompletionMap K M w ⟨W, hW⟩
            (finitePlaceAdicCompletionMap ℚ K
                  (finitePlaceBelow (K := ℚ) w) ⟨w, rfl⟩
                  (b.2 (finitePlaceBelow (K := ℚ) w)) *
              algebraMap K (w.adicCompletion K) x)
      exact hcomponent
        (finitePlaceBelow (K := ℚ) w) hq rfl

/-- The canonical transport of ordinary ideles along an equivalence of
number fields.  It is obtained from the existing relative-idele transport
over `ℚ` and the canonical relative-to-ordinary base-change equivalences. -/
noncomputable def ideleCongr
    (e : K ≃ₐ[ℚ] M) :
    IdeleGroup K ≃* IdeleGroup M :=
  (IdeleGroup.equivAdeleRingUnits (K := K)).trans
    ((Units.mapEquiv (adeleCongr e).toMulEquiv).trans
      (IdeleGroup.equivAdeleRingUnits (K := M)).symm)

/-- On finite coordinates, canonical idelic transport is the completion
map at the corresponding finite places. -/
@[simp]
theorem ideleCongr_finiteComponent
    (e : K ≃ₐ[ℚ] M)
    (a : IdeleGroup K)
    (W : HeightOneSpectrum (𝓞 M)) :
    IdeleGroup.finiteComponent W (ideleCongr e a) =
      Units.map
        (finitePlaceAdicCompletionCongrHom e W).toMonoidHom
        (IdeleGroup.finiteComponent
          ((finitePlaceCongr e).symm W) a) := by
  apply Units.ext
  exact
    adeleCongr_finiteComponent e
      (((IdeleGroup.equivAdeleRingUnits
        (K := K) a :
          (NumberField.AdeleRing (𝓞 K) K)ˣ) :
        NumberField.AdeleRing (𝓞 K) K))
      W

/-- Transport along a number-field equivalence carries the diagonal idele
to the diagonal idele of the transported field unit. -/
@[simp]
theorem ideleCongr_principalIdele
    (e : K ≃ₐ[ℚ] M)
    (x : Kˣ) :
    ideleCongr e (IdeleGroup.principalIdele K x) =
      IdeleGroup.principalIdele M
        (Units.mapEquiv e.toMulEquiv x) := by
  apply
    (IdeleGroup.equivAdeleRingUnits
      (K := M)).injective
  apply Units.ext
  exact adeleCongr_algebraMap e (x : K)

/-- The ordinary principal-idele subgroups are identified by transport
along a number-field equivalence. -/
theorem idelePrincipalSubgroup_map_congr
    (e : K ≃ₐ[ℚ] M) :
    (IdeleGroup.principalSubgroup K).map
        (ideleCongr e) =
      IdeleGroup.principalSubgroup M := by
  ext y
  constructor
  · rintro ⟨z, ⟨x, hx⟩, rfl⟩
    rw [← hx]
    exact
      ⟨Units.mapEquiv e.toMulEquiv x,
        (ideleCongr_principalIdele e x).symm⟩
  · rintro ⟨y, rfl⟩
    obtain ⟨x, rfl⟩ :=
      (Units.mapEquiv e.toMulEquiv).surjective y
    exact
      ⟨IdeleGroup.principalIdele K x,
        ⟨x, rfl⟩,
        ideleCongr_principalIdele e x⟩

/-- The canonical transport of ordinary idele classes along an equivalence
of number fields.  This descends `ideleCongr`; it does not introduce a
second idele-class quotient. -/
noncomputable def ideleClassCongr
    (e : K ≃ₐ[ℚ] M) :
    IdeleClassGroup K ≃* IdeleClassGroup M :=
  QuotientGroup.congr
    (IdeleGroup.principalSubgroup K)
    (IdeleGroup.principalSubgroup M)
    (ideleCongr e)
    (idelePrincipalSubgroup_map_congr e)

/-- The ordinary idele-class transport is induced by `ideleCongr` on
quotient representatives. -/
@[simp]
theorem ideleClassCongr_mk
    (e : K ≃ₐ[ℚ] M)
    (a : IdeleGroup K) :
    ideleClassCongr e
        (QuotientGroup.mk'
          (IdeleGroup.principalSubgroup K) a) =
      QuotientGroup.mk'
        (IdeleGroup.principalSubgroup M)
        (ideleCongr e a) :=
  rfl

section RelativeTowerCongr

variable
    {K L K' L' : Type}
    [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    [Field K'] [NumberField K']
    [Field L'] [NumberField L'] [Algebra K' L']

/-- The tensor-product map induced by compatible equivalences of both
fields in a finite extension.  The coefficient-ring equivalence is kept
explicit so the inverse uses that exact equivalence rather than a second
choice. -/
noncomputable def relativeAdeleMapOfCompatibleEquiv
    (eK : K ≃ₐ[ℚ] K')
    (eA :
      NumberField.AdeleRing (𝓞 K) K ≃+*
        NumberField.AdeleRing (𝓞 K') K')
    (hA : ∀ x : K,
      eA
          (algebraMap K
            (NumberField.AdeleRing (𝓞 K) K) x) =
        algebraMap K'
          (NumberField.AdeleRing (𝓞 K') K') (eK x))
    (eL : L ≃ₐ[ℚ] L')
    (hL : ∀ x : K,
      eL (algebraMap K L x) =
        algebraMap K' L' (eK x)) :
    RelativeAdeleRing K L →+*
      RelativeAdeleRing K' L' := by
  letI : Algebra K (RelativeAdeleRing K' L') :=
    ((algebraMap K' (RelativeAdeleRing K' L')).comp
      eK.toRingHom).toAlgebra
  let fA :
      NumberField.AdeleRing (𝓞 K) K →ₐ[K]
        RelativeAdeleRing K' L' :=
    { __ :=
        (RelativeIdeleGroup.adeleInclusion K' L').comp
          eA.toRingHom
      commutes' := by
        intro x
        change
          RelativeIdeleGroup.adeleInclusion K' L'
              (eA
                (algebraMap K
                  (NumberField.AdeleRing (𝓞 K) K) x)) =
            algebraMap K'
              (RelativeAdeleRing K' L') (eK x)
        rw [hA]
        simp [RelativeIdeleGroup.adeleInclusion] }
  let fL : L →ₐ[K] RelativeAdeleRing K' L' :=
    { __ :=
        (RelativeIdeleGroup.fieldInclusion K' L').comp
          eL.toRingHom
      commutes' := by
        intro x
        change
          RelativeIdeleGroup.fieldInclusion K' L'
              (eL (algebraMap K L x)) =
            algebraMap K'
              (RelativeAdeleRing K' L') (eK x)
        rw [hL]
        simp [RelativeIdeleGroup.fieldInclusion] }
  exact
    (Algebra.TensorProduct.lift
      fA fL (fun _ _ ↦ Commute.all _ _)).toRingHom

@[simp]
theorem relativeAdeleMapOfCompatibleEquiv_tmul
    (eK : K ≃ₐ[ℚ] K')
    (eA :
      NumberField.AdeleRing (𝓞 K) K ≃+*
        NumberField.AdeleRing (𝓞 K') K')
    (hA : ∀ x : K,
      eA
          (algebraMap K
            (NumberField.AdeleRing (𝓞 K) K) x) =
        algebraMap K'
          (NumberField.AdeleRing (𝓞 K') K') (eK x))
    (eL : L ≃ₐ[ℚ] L')
    (hL : ∀ x : K,
      eL (algebraMap K L x) =
        algebraMap K' L' (eK x))
    (a : NumberField.AdeleRing (𝓞 K) K)
    (x : L) :
    relativeAdeleMapOfCompatibleEquiv
        eK eA hA eL hL (a ⊗ₜ[K] x) =
      eA a ⊗ₜ[K'] eL x := by
  change
    Algebra.TensorProduct.includeLeft
          (R := K') (S := K')
          (A := NumberField.AdeleRing (𝓞 K') K') (B := L')
          (eA a) *
        Algebra.TensorProduct.includeRight
          (R := K')
          (A := NumberField.AdeleRing (𝓞 K') K') (B := L')
          (eL x) =
      eA a ⊗ₜ[K'] eL x
  rw [Algebra.TensorProduct.includeLeft_apply,
    Algebra.TensorProduct.includeRight_apply,
    Algebra.TensorProduct.tmul_mul_tmul,
    mul_one, one_mul]

end RelativeTowerCongr
end Absolute
end
end

section
-- module Solutions.OAIQ244_DUKE.AlgebraicNumberTheory_Idele_ClassGroup_TowerBaseChange
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.KummerTheory.primeCyclotomicBaseFiniteDimensional _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.residueFieldZModAlgebra _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedIntegralAlgebraContextValuationSubringAlgebra _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.PrimeDegreePackets.diagonalLogAction _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.CyclicCohomology.binaryCoefficientFamilyCommGroup _root_.LocalClassFieldTheory.normalizationIntegerRingIsIntegralClosure _root_.chosenFinitePlaceCompletionAlgebra _root_.chosenFinitePlaceCompletionFiniteDimensional _root_.chosenFinitePlaceLocalizedFiniteDimensional
attribute [-simp] _root_.IsDiscreteValuationRing.addVal_ringEquiv _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.OAI.PrimeDegreePackets.ThetaConstruction.schwartzCM_apply _root_.relativeAdeleMapOfCompatibleEquiv_tmul _root_.finiteIdeleOfSPlaceFactors_apply_mem _root_.finiteIdeleOfSPlaceFactors_apply_notMem _root_.ideleClassCongr_mk _root_.ideleCongr_finiteComponent _root_.ideleCongr_principalIdele _root_.ideleSupportedAtEquivSPlaceFactors_infinite _root_.ideleSupportedAtEquivSPlaceFactors_inside _root_.ideleSupportedAtEquivSPlaceFactors_outside_coe _root_.relativeAdeleCongr_tmul _root_.relativeIdeleClassCongr_ideleClassNorm _root_.relativeIdeleClassCongr_mk _root_.relativeIdeleCongr_coe _root_.relativeIdeleCongr_norm _root_.relativeIdeleCongr_principalIdele
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

/-!
# The fixed-bottom tower model and the actual intermediate-field model

For a tower `K ⊂ M ⊂ L`, `IdeleClassTower` presents the ideles of `L`
as units of `(𝔸_K ⊗[K] M) ⊗[M] L`.  Here we compare that presentation
with the actual relative idele group `𝔸_M ⊗[M] L`, by passing through
the ordinary ideles of `L`.
-/

open scoped NumberField TensorProduct
open NumberField IsDedekindDomain

noncomputable section

open AlgebraicNumberTheory.Valuations

universe u

variable
    (K M L : Type u)
    [Field K] [NumberField K]
    [Field M] [NumberField M]
    [Field L] [NumberField L]
    [Algebra K M] [Algebra M L] [Algebra K L]
    [IsScalarTower K M L]
    [FiniteDimensional K M] [FiniteDimensional M L]

-- These canonical commutativity proofs are local to the imported tower
-- module; retain them here for the quotient-group instances.
local instance
    towerBaseChange_towerRelativeIdeleGroupIsMulCommutative
    (A B C : Type u) [Field A] [NumberField A]
    [Field B] [Field C] [Algebra A B] [Algebra B C] :
    IsMulCommutative (TowerRelativeIdeleGroup A B C) :=
  ⟨⟨fun a b => mul_comm a b⟩⟩

local instance
    towerBaseChange_relativeIdeleClassGroupIsMulCommutative
    (A B : Type u) [Field A] [NumberField A]
    [Field B] [Algebra A B] :
    IsMulCommutative (RelativeIdeleGroup.ClassGroup A B) :=
  ⟨⟨fun a b => mul_comm a b⟩⟩

local instance towerBaseChange_ideleClassGroupIsMulCommutative
    (A : Type u) [Field A] [NumberField A] :
    IsMulCommutative (IdeleClassGroup A) :=
  ⟨⟨fun a b => mul_comm a b⟩⟩

section RingComparison

/-- The ring-level relative-to-ordinary comparison, regarded as an
equivalence of `M`-algebras. -/
noncomputable def intermediateRelativeAdeleBaseChangeAlgEquiv :
    RelativeAdeleRing K M ≃ₐ[M]
      NumberField.AdeleRing (𝓞 M) M :=
  AlgEquiv.ofRingEquiv
    (f := relativeAdeleBaseChangeRingEquiv
      (K := K) (L := M))
    (by
      intro m
      change
        relativeAdeleBaseChangeRingEquiv
            (K := K) (L := M)
            ((1 : NumberField.AdeleRing (𝓞 K) K) ⊗ₜ[K] m) =
          algebraMap M
            (NumberField.AdeleRing (𝓞 M) M) m
      exact relativeAdeleBaseChangeRingEquiv_fieldInclusion
        (K := K) (L := M) m)

/-- Extend the intermediate adele-ring comparison along `M → L`. -/
noncomputable def towerActualRelativeAdeleRingEquiv :
    TowerRelativeAdeleRing K M L ≃+*
      RelativeAdeleRing M L :=
  (Algebra.TensorProduct.congr
    (intermediateRelativeAdeleBaseChangeAlgEquiv K M)
    (AlgEquiv.refl : L ≃ₐ[M] L)).toRingEquiv

omit [NumberField L] [Algebra K L] [IsScalarTower K M L]
    [FiniteDimensional M L] in
@[simp]
theorem towerActualRelativeAdeleRingEquiv_tmul
    (b : RelativeAdeleRing K M)
    (x : L) :
    towerActualRelativeAdeleRingEquiv K M L (b ⊗ₜ[M] x) =
      intermediateRelativeAdeleBaseChangeAlgEquiv K M b ⊗ₜ[M] x :=
  rfl

end RingComparison

section IdeleComparison

section ViaOrdinary

/-- The comparison through ordinary ideles, recording the compatibility
with the original fixed-bottom flattening construction. -/
noncomputable def towerRelativeIdeleViaOrdinaryMulEquiv :
    TowerRelativeIdeleGroup K M L ≃*
      RelativeIdeleGroup M L :=
  (towerRelativeIdeleEquiv K M L).trans
    ((relativeIdeleBaseChangeMulEquiv
      (K := K) (L := L)).trans
      (relativeIdeleBaseChangeMulEquiv
        (K := M) (L := L)).symm)

omit [FiniteDimensional K M] in
@[simp]
theorem towerRelativeIdeleViaOrdinaryMulEquiv_apply
    (a : TowerRelativeIdeleGroup K M L) :
    towerRelativeIdeleViaOrdinaryMulEquiv K M L a =
      (relativeIdeleBaseChangeMulEquiv
        (K := M) (L := L)).symm
        (relativeIdeleBaseChangeMulEquiv
          (K := K) (L := L)
          (towerRelativeIdeleEquiv K M L a)) :=
  rfl

end ViaOrdinary

/-- The fixed-bottom tower presentation of the ideles of `L` is
canonically equivalent to the actual relative idele group over `M`,
using the underlying adele-ring scalar-extension equivalence. -/
noncomputable def towerRelativeIdeleBaseChangeMulEquiv :
    TowerRelativeIdeleGroup K M L ≃*
      RelativeIdeleGroup M L :=
  Units.mapEquiv
    (towerActualRelativeAdeleRingEquiv K M L).toMulEquiv

omit [NumberField L] [Algebra K L] [IsScalarTower K M L]
    [FiniteDimensional M L] in
/-- The comparison preserves the diagonal copy of `Lˣ`. -/
@[simp]
theorem towerRelativeIdeleBaseChangeMulEquiv_principalIdele
    (x : Lˣ) :
    towerRelativeIdeleBaseChangeMulEquiv K M L
        (TowerRelativeIdeleGroup.principalIdele K M L x) =
      RelativeIdeleGroup.principalIdele M L x := by
  apply Units.ext
  change
    towerActualRelativeAdeleRingEquiv K M L
        ((1 : RelativeAdeleRing K M) ⊗ₜ[M] (x : L)) =
      (1 : NumberField.AdeleRing (𝓞 M) M) ⊗ₜ[M] (x : L)
  rw [towerActualRelativeAdeleRingEquiv_tmul]
  simp

omit [NumberField L] [Algebra K L] [IsScalarTower K M L]
    [FiniteDimensional M L] in
/-- The comparison maps tower principal ideles exactly onto the actual
relative principal-ideles subgroup over `M`. -/
theorem towerPrincipalSubgroup_map_baseChange :
    (TowerRelativeIdeleGroup.principalSubgroup K M L).map
        (towerRelativeIdeleBaseChangeMulEquiv K M L) =
      RelativeIdeleGroup.principalSubgroup M L := by
  rw [TowerRelativeIdeleGroup.principalSubgroup,
    RelativeIdeleGroup.principalSubgroup,
    MonoidHom.map_range]
  congr 1
  ext x
  exact congrArg Units.val
    (towerRelativeIdeleBaseChangeMulEquiv_principalIdele
      K M L x)

/-- The fixed-bottom tower class group is canonically the actual
relative idele class group of `L/M`. -/
noncomputable def towerRelativeIdeleClassBaseChangeMulEquiv :
    TowerRelativeIdeleGroup.ClassGroup K M L ≃*
      RelativeIdeleGroup.ClassGroup M L :=
  QuotientGroup.congr
    (TowerRelativeIdeleGroup.principalSubgroup K M L)
    (RelativeIdeleGroup.principalSubgroup M L)
    (towerRelativeIdeleBaseChangeMulEquiv K M L)
    (towerPrincipalSubgroup_map_baseChange K M L)

omit [NumberField L] [Algebra K L] [IsScalarTower K M L]
    [FiniteDimensional M L] in
@[simp]
theorem towerRelativeIdeleClassBaseChangeMulEquiv_mk
    (a : TowerRelativeIdeleGroup K M L) :
    towerRelativeIdeleClassBaseChangeMulEquiv K M L
        (QuotientGroup.mk'
          (TowerRelativeIdeleGroup.principalSubgroup K M L) a) =
      QuotientGroup.mk'
        (RelativeIdeleGroup.principalSubgroup M L)
        (towerRelativeIdeleBaseChangeMulEquiv K M L a) :=
  rfl

end IdeleComparison

section NormComparison

omit [NumberField L] [Algebra K L] [IsScalarTower K M L]
    [FiniteDimensional M L] in
/-- The actual relative-idele norm is the tower determinant norm after
the intermediate relative-to-ordinary adele comparison. -/
theorem towerRelativeIdeleBaseChangeMulEquiv_norm
    (a : TowerRelativeIdeleGroup K M L) :
    relativeIdeleBaseChangeMulEquiv
        (K := K) (L := M)
        (TowerRelativeIdeleGroup.norm K M L a) =
      RelativeIdeleGroup.norm M L
        (towerRelativeIdeleBaseChangeMulEquiv K M L a) := by
  let e₁ :=
    relativeAdeleBaseChangeRingEquiv
      (K := K) (L := M)
  let e₂ :=
    towerActualRelativeAdeleRingEquiv K M L
  have he :
      (algebraMap
          (NumberField.AdeleRing (𝓞 M) M)
          (RelativeAdeleRing M L)).comp e₁.toRingHom =
        e₂.toRingHom.comp
          (algebraMap
            (RelativeAdeleRing K M)
            (TowerRelativeAdeleRing K M L)) := by
    apply DFunLike.ext _ _
    intro b
    change
      (e₁ b) ⊗ₜ[M] (1 : L) =
        e₂ (b ⊗ₜ[M] (1 : L))
    rw [towerActualRelativeAdeleRingEquiv_tmul]
    rfl
  have hnorm :=
    Algebra.norm_eq_of_equiv_equiv
      e₁ e₂ he (a : TowerRelativeAdeleRing K M L)
  have hnorm' :
      e₁
          (Algebra.norm
            (RelativeAdeleRing K M)
            (a : TowerRelativeAdeleRing K M L)) =
        Algebra.norm
          (NumberField.AdeleRing (𝓞 M) M)
          (e₂ (a : TowerRelativeAdeleRing K M L)) := by
    simpa using congrArg e₁ hnorm
  apply
    (IdeleGroup.equivAdeleRingUnits
      (K := M)).injective
  rw [relativeIdeleBaseChangeMulEquiv_eq_ringUnits
    (K := K) (L := M)]
  simp only [RelativeIdeleGroup.norm,
    MonoidHom.comp_apply]
  simp only [MulEquiv.coe_toMonoidHom,
    MulEquiv.apply_symm_apply]
  apply Units.ext
  change
    e₁
        (Algebra.norm
          (RelativeAdeleRing K M)
          (a : TowerRelativeAdeleRing K M L)) =
      Algebra.norm
        (NumberField.AdeleRing (𝓞 M) M)
        (e₂ (a : TowerRelativeAdeleRing K M L))
  exact hnorm'

end NormComparison

section ClassNormComparison

omit [NumberField L] [Algebra K L] [IsScalarTower K M L] in
/-- After both relative presentations are replaced by the ordinary
idele class groups, the fixed-bottom tower class norm is the actual
class norm for `L/M`. -/
theorem towerRelativeIdeleClassBaseChangeMulEquiv_classNorm
    (c : TowerRelativeIdeleGroup.ClassGroup K M L) :
    relativeIdeleClassBaseChangeMulEquiv
        (K := K) (L := M)
        (TowerRelativeIdeleGroup.classNorm K M L c) =
      RelativeIdeleGroup.classNorm M L
        (towerRelativeIdeleClassBaseChangeMulEquiv K M L c) := by
  refine QuotientGroup.induction_on c ?_
  intro a
  exact congrArg
    (QuotientGroup.mk'
      (IdeleGroup.principalSubgroup M))
    (towerRelativeIdeleBaseChangeMulEquiv_norm K M L a)

omit [NumberField L] [Algebra K L] [IsScalarTower K M L] in
/-- The fixed-bottom tower norm subgroup becomes exactly the actual
`L/M` class-norm subgroup after base change to the ordinary class group
of `M`. -/
theorem towerClassNorm_range_map_baseChange :
    (TowerRelativeIdeleGroup.classNorm K M L).range.map
        (relativeIdeleClassBaseChangeMulEquiv
          (K := K) (L := M)).toMonoidHom =
      (RelativeIdeleGroup.classNorm M L).range := by
  ext c
  constructor
  · rintro ⟨d, ⟨a, rfl⟩, rfl⟩
    exact
      ⟨towerRelativeIdeleClassBaseChangeMulEquiv K M L a,
        (towerRelativeIdeleClassBaseChangeMulEquiv_classNorm
          K M L a).symm⟩
  · rintro ⟨d, rfl⟩
    have h :
        relativeIdeleClassBaseChangeMulEquiv
            (K := K) (L := M)
            (TowerRelativeIdeleGroup.classNorm K M L
              ((towerRelativeIdeleClassBaseChangeMulEquiv
                K M L).symm d)) =
          RelativeIdeleGroup.classNorm M L d := by
      simpa using
        (towerRelativeIdeleClassBaseChangeMulEquiv_classNorm
          K M L
          ((towerRelativeIdeleClassBaseChangeMulEquiv
            K M L).symm d))
    exact
      ⟨TowerRelativeIdeleGroup.classNorm K M L
          ((towerRelativeIdeleClassBaseChangeMulEquiv
            K M L).symm d),
        ⟨(towerRelativeIdeleClassBaseChangeMulEquiv
            K M L).symm d, rfl⟩, h⟩

/-- The fixed-bottom quotient `C_M / N_{L/M} C_L` is canonically the
ordinary idele-class norm quotient for the actual extension `L/M`. -/
noncomputable def intermediateClassNormQuotientBaseChangeMulEquiv :
    IntermediateClassNormQuotient K M L ≃*
      RelativeIdeleGroup.ClassNormQuotient M L :=
  QuotientGroup.congr
    (TowerRelativeIdeleGroup.classNorm K M L).range
    (RelativeIdeleGroup.classNorm M L).range
    (relativeIdeleClassBaseChangeMulEquiv
      (K := K) (L := M))
    (towerClassNorm_range_map_baseChange K M L)

end ClassNormComparison
end
end

section
-- module Solutions.OAIQ244_DUKE.LocalField_DiscreteValuationField_MixedCharacteristicStructure_IntegralLattice
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.residueFieldZModAlgebra _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedWithZeroValuationContextIntegralAlgebra _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.LocalClassFieldTheory.normalizationIntegerRingIsIntegralClosure _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

/-!
# The integral lattice of a mixed-characteristic local field

This file identifies the integer ring of a mixed-characteristic local field
with the integral closure of the p-adic integers.  In particular it supplies
the finite free `Z_p` lattice of rank `[K : Q_p]` used in the proof of
the mixed-characteristic field-unit structure theorem.  The comparison is made for the canonical copy of `Q_p`
constructed in the local-field structure classification, not for a separately assumed scalar action.
-/

noncomputable section

universe u v

namespace LocalFieldTheory.DiscreteValuationField
namespace LocalField

open scoped WithZero nonZeroDivisors
open Module

variable {K : Type u} [Field K]

/-! ### Canonical mixed-characteristic scalar context -/

/-! ### the canonical `Z_p` integral basis -/

/--
Equips the target with its canonical `Algebra` structure, namely `Algebra
ℤ_[F.residueCharacteristic] K`.
-/
noncomputable instance mixedIntegralAlgebraContextFieldAlgebra
    (F : LocalField.{u, v} K) [CharZero K]
    [MixedIntegralAlgebraContext F] :
    Algebra ℤ_[F.residueCharacteristic] K :=
  F.padicIntFieldAlgebra

/-! ### The canonical `Z_p` action on `U^r` -/

end LocalField
end LocalFieldTheory.DiscreteValuationField
end
end


