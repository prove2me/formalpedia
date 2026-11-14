-- Prove2me | Definitions.Def_OAIQ244Duke056
-- name    : OAIQ244Duke056
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-13T22:15:32.389681+00:00
-- url     : https://prove2.me/theorems/089cc36d-eaed-49ab-a912-c7221d295715
-- title:
--   Definitions bundle OAIQ244Duke056 of the split of OpenAI, Equidistribution of Prime-Degree Torus Packets with Arbitrary Local Type
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.DukePrimeDegree.prime_degree_packet_measure_equidistribution_unconditional` and `OAI.DukePrimeDegree.prime_degree_packet_measures_tendsto_haar_unconditional`, carved from OpenAI's openai/math development (OpenAI, *Equidistribution of Prime-Degree Torus Packets with Arbitrary Local Type*, OpenAI Math Release, September 24, 2026, result family 15, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 17 declarations of OpenAI's Lean: 9 definitions and 8 theorems. The definitions and types are `chosenFinitePlaceIntegerToLocalizedCompletion`, `chosenFinitePlaceLocalizedIntegerRingEquiv`, `chosenFinitePlaceLocalizedResidueEquiv`, `relativeLocalTensorDecompositionIntegralUnitSubgroupEquivPiUnits`, `relativeLocalTensorDecompositionIntegralUnitSubgroupEquivProduct`, `relativeUnrestrictedSPlaceLocalDegree`, `singleFinitePlaceIntegralUnitFamily`, `singleRelativeLocalTensorDecompositionIntegralUnit`, `standardToChosenLocalizedIntegerRingEquiv`.
--
--   **Sources.** They come from these modules of lean/OAI/NumberTheory, in whole or in part: `AlgebraicNumberTheory_Adele_IntegralLocalFactor`, `AlgebraicNumberTheory_Completion_IntegerRingComparison`, `AlgebraicNumberTheory_Completion_UnramifiedComparison_IdealToCompletion`, `AlgebraicNumberTheory_Idele_Cohomology_SPlaces_Herbrand_Local`, `AlgebraicNumberTheory_Idele_NormApproximation_InfinitePlaces`, `AlgebraicNumberTheory_Idele_Relative_FiniteIntegralNormPreimage`, `AlgebraicNumberTheory_Idele_Relative_FinitePlaceTensorNorm`, `GlobalClassFieldTheory_Cohomology_CyclicPrimePowerFullDecomposition`, `LocalClassFieldTheory_Finite_Unramified_Cohomology`.
--
--   **Imports.** It imports the bundles `OAIQ244Duke046`, `OAIQ244Duke048` and `OAIQ244Duke049` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ244Duke063`, `OAIQ244Duke064`, `OAIQ244Duke065`, `OAIQ244Duke066`, `OAIQ244Duke067` and `OAIQ244Duke068`; the statement `chosenFinitePlaceLocalizedResidueEquiv_equivariant`; the proof of `chosenFinitePlaceLocalizedResidueEquiv_equivariant`.
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
import Mathlib.Algebra.Module.PID
import Mathlib.Algebra.Module.Shrink
import Mathlib.Algebra.Module.Torsion.Basic
import Mathlib.Algebra.Module.ZLattice.Basic
import Mathlib.Algebra.Order.Field.Power
import Mathlib.Algebra.Order.Group.Cyclic
import Mathlib.Algebra.Order.Hom.Units
import Mathlib.Algebra.Order.Ring.IsNonarchimedean
import Mathlib.Algebra.Order.WithTop.Untop0
import Mathlib.Algebra.Polynomial.Div
import Mathlib.Algebra.Polynomial.FieldDivision
import Mathlib.Algebra.Polynomial.Lifts
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
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.FieldTheory.IsSepClosed
import Mathlib.FieldTheory.KrullTopology
import Mathlib.FieldTheory.Minpoly.IsConjRoot
import Mathlib.FieldTheory.Minpoly.IsIntegrallyClosed
import Mathlib.FieldTheory.Normal.Basic
import Mathlib.FieldTheory.Normal.Closure
import Mathlib.FieldTheory.Perfect
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
import Mathlib.GroupTheory.Sylow
import Mathlib.GroupTheory.Transfer
import Mathlib.LinearAlgebra.Basis.SMul
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.LinearAlgebra.Charpoly.BaseChange
import Mathlib.LinearAlgebra.Determinant
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
import Mathlib.LinearAlgebra.Matrix.Gershgorin
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
import Mathlib.NumberTheory.NumberField.InfinitePlace.Ramification
import Mathlib.NumberTheory.NumberField.ProductFormula
import Mathlib.NumberTheory.NumberField.Units.DirichletTheorem
import Mathlib.NumberTheory.NumberField.Units.Regulator
import Mathlib.NumberTheory.Ostrowski
import Mathlib.NumberTheory.Padics.HeightOneSpectrum
import Mathlib.NumberTheory.Padics.PadicNumbers
import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Mathlib.NumberTheory.Padics.RingHoms
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
import Mathlib.Topology.Algebra.Group.Basic
import Mathlib.Topology.Algebra.Group.ClosedSubgroup
import Mathlib.Topology.Algebra.Group.Quotient
import Mathlib.Topology.Algebra.Group.SubmonoidClosure
import Mathlib.Topology.Algebra.Group.TopologicalAbelianization
import Mathlib.Topology.Algebra.Group.Units
import Mathlib.Topology.Algebra.InfiniteSum.Nonarchimedean
import Mathlib.Topology.Algebra.IsOpenUnits
import Mathlib.Topology.Algebra.IsUniformGroup.Basic
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.Topology.Algebra.OpenSubgroup
import Mathlib.Topology.Algebra.Order.Field
import Mathlib.Topology.Algebra.Ring.Basic
import Mathlib.Topology.Algebra.Ring.Compact
import Mathlib.Topology.Algebra.Valued.LocallyCompact
import Mathlib.Topology.Algebra.Valued.NormedValued
import Mathlib.Topology.Algebra.Valued.ValuativeRel
import Mathlib.Topology.Algebra.Valued.ValuedField
import Mathlib.Topology.Algebra.Valued.WithZeroMulInt
import Mathlib.Topology.Connected.Clopen
import Mathlib.Topology.Instances.Matrix
import Mathlib.Topology.Instances.Sign
import Mathlib.Topology.Instances.ZMod
import Mathlib.Topology.Maps.Basic
import Mathlib.Topology.Neighborhoods
import Mathlib.Topology.Sets.Opens
import Mathlib.Topology.UniformSpace.AbsoluteValue
import Definitions.Def_OAIQ244Duke046
import Definitions.Def_OAIQ244Duke048
import Definitions.Def_OAIQ244Duke049

section
-- module Solutions.OAIQ244_DUKE.AlgebraicNumberTheory_Idele_Relative_FinitePlaceTensorNorm
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalCyclotomicCompletionAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.residueFieldZModAlgebra _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.PrimeDegreePackets.diagonalLogAction _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.LocalClassFieldTheory.normalizationIntegerRingIsIntegralClosure _root_.chosenFinitePlaceCompletionAlgebra _root_.chosenFinitePlaceCompletionContinuousSMul _root_.chosenFinitePlaceCompletionFiniteDimensional _root_.chosenFinitePlaceCompletionLocallyCompactSpace _root_.chosenFinitePlaceLocalizedFiniteDimensional _root_.chosenFinitePlaceLocalizedIntegerAlgebra _root_.chosenFinitePlaceLocalizedIntegerModuleFinite _root_.chosenFinitePlaceLocalizedIsGalois _root_.chosenFinitePlaceLocalizedIsIntegralClosure _root_.chosenFinitePlaceLocalizedIsNonarchimedeanLocalField _root_.chosenFinitePlaceLocalizedIsValuativeTopology _root_.chosenFinitePlaceLocalizedLocallyCompactSpace _root_.chosenFinitePlaceLocalizedValuationCompatible _root_.chosenFinitePlaceLocalizedValuationHasExtension _root_.chosenFinitePlaceLocalizedValuationIsNontrivial _root_.chosenFinitePlaceLocalizedValuativeRel _root_.chosenFinitePlaceLocalizedValuativeRelIsNontrivial _root_.chosenFinitePlaceLocalizedValued _root_.scaledRelativeIntegerLatticeQuotientFinite
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
/-- **Actual finite-place tensor norm image.**  The image of the
determinant norm on `K_v ⊗[K] L` is exactly the chosen local field-norm
subgroup in the concrete finite idele coordinate. -/
theorem finitePlaceLocalTensorNorm_range_eq_chosenLocalNormSubgroup
    (v : HeightOneSpectrum (𝓞 K)) :
    (_root_.localTensorNorm
        (K := K) (L := L) v).range =
      chosenFinitePlaceLocalNormSubgroup
        (K := K) (L := L) v := by
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
  let E := LocalizedCompletion vK w
  let : Module.Finite vK.Completion E :=
    localizedCompletionModuleFinite vK hvK w
  rw [finitePlaceLocalTensorNorm_range_eq_transport
    (K := K) (L := L) v]
  change
    (localTensorNormSubgroup
      (K := K) (L := L) vK).map
        (finitePlaceCompletionUnitsContinuousMulEquiv
          v).toMonoidHom =
      (localNormSubgroup vK.Completion E).map
        (finitePlaceCompletionUnitsContinuousMulEquiv
          v).toMonoidHom
  rw [localTensorNormSubgroup_eq_localNormSubgroup
    (K := K) (L := L) vK w hvK]
end
end

section
-- module Solutions.OAIQ244_DUKE.AlgebraicNumberTheory_Adele_IntegralLocalFactor
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalCyclotomicCompletionAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.residueFieldZModAlgebra _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.LocalClassFieldTheory.normalizationIntegerRingIsIntegralClosure _root_.chosenFinitePlaceCompletionAlgebra _root_.chosenFinitePlaceCompletionContinuousSMul _root_.chosenFinitePlaceCompletionFiniteDimensional _root_.chosenFinitePlaceCompletionLocallyCompactSpace _root_.chosenFinitePlaceLocalizedFiniteDimensional _root_.chosenFinitePlaceLocalizedIntegerAlgebra _root_.chosenFinitePlaceLocalizedIntegerModuleFinite _root_.chosenFinitePlaceLocalizedIsGalois _root_.chosenFinitePlaceLocalizedIsIntegralClosure _root_.chosenFinitePlaceLocalizedIsNonarchimedeanLocalField _root_.chosenFinitePlaceLocalizedIsValuativeTopology _root_.chosenFinitePlaceLocalizedLocallyCompactSpace _root_.chosenFinitePlaceLocalizedValuationCompatible _root_.chosenFinitePlaceLocalizedValuationHasExtension _root_.chosenFinitePlaceLocalizedValuationIsNontrivial _root_.chosenFinitePlaceLocalizedValuativeRel _root_.chosenFinitePlaceLocalizedValuativeRelIsNontrivial _root_.chosenFinitePlaceLocalizedValued
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

/-!
# Integral finite local factors of the relative idele group

For a finite place `w` of the base field, the canonical local tensor decomposition identifies
`K_w ⊗_K L` with the product of the completions of `L` above `w`.
This file packages each projection as an actual ring homomorphism and
defines the subgroup of tensor units whose value and inverse are integral
in every completion factor.  Thus the integrality predicate used for the
restricted product is closed under all group operations for structural,
rather than coordinate-dependent, reasons.
-/

open scoped NumberField TensorProduct
open NumberField IsDedekindDomain

noncomputable section


open AlgebraicNumberTheory.Valuations
open LocalClassFieldTheory

universe u v

variable
    {K : Type u} {L : Type v}
    [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L]

/-- The integral local tensor-unit subgroup is exactly the product of
the valuation-ring unit groups occurring in the canonical local tensor decomposition. -/
noncomputable def
    relativeLocalTensorDecompositionIntegralUnitSubgroupEquivProduct
    (w : HeightOneSpectrum (𝓞 K)) :
    relativeLocalTensorDecompositionIntegralUnitSubgroup
        (K := K) (L := L) w ≃*
      FinitePlaceLocalTensorDecompositionIntegralUnitProduct
        (K := K) (L := L) w where
  toFun x := ⟨finitePlaceLocalTensorDecompositionUnitsEquiv
      (K := K) (L := L) w x, by
    have hx := x.property
    rw [mem_relativeLocalTensorDecompositionIntegralUnitSubgroup_iff,
      relativeLocalTensorDecompositionIntegralUnitAt_iff] at hx
    rw [Subgroup.mem_pi]
    intro wL hwL
    simpa only [finitePlaceLocalTensorDecompositionUnitsEquiv_apply] using
      (hx wL)⟩
  invFun y := ⟨(finitePlaceLocalTensorDecompositionUnitsEquiv
      (K := K) (L := L) w).symm y, by
    rw [mem_relativeLocalTensorDecompositionIntegralUnitSubgroup_iff,
      relativeLocalTensorDecompositionIntegralUnitAt_iff]
    intro wL
    have hy :
        finitePlaceLocalTensorDecompositionUnitsEquiv
            (K := K) (L := L) w
            ((finitePlaceLocalTensorDecompositionUnitsEquiv
              (K := K) (L := L) w).symm y) wL ∈
          (absoluteValueCompletionIntegers wL.1
            (absoluteValueExtension_isNonarchimedean
              (HeightOneSpectrum.adicAbv K w)
              (HeightOneSpectrum.isNonarchimedean_adicAbv K w)
              wL)).units := by
      rw [(finitePlaceLocalTensorDecompositionUnitsEquiv
        (K := K) (L := L) w).apply_symm_apply]
      exact y.property wL (Set.mem_univ wL)
    simpa only [finitePlaceLocalTensorDecompositionUnitsEquiv_apply] using hy⟩
  left_inv x := by
    apply Subtype.ext
    exact
      (finitePlaceLocalTensorDecompositionUnitsEquiv
        (K := K) (L := L) w).symm_apply_apply x
  right_inv y := by
    apply Subtype.ext
    exact
      (finitePlaceLocalTensorDecompositionUnitsEquiv
        (K := K) (L := L) w).apply_symm_apply y
  map_mul' x y := by
    apply Subtype.ext
    exact
      (finitePlaceLocalTensorDecompositionUnitsEquiv
        (K := K) (L := L) w).map_mul x y

/-- Final local form: the integral tensor units are the product of the
intrinsic unit groups of all completion valuation rings above `w`. -/
noncomputable def
    relativeLocalTensorDecompositionIntegralUnitSubgroupEquivPiUnits
    (w : HeightOneSpectrum (𝓞 K)) :
    relativeLocalTensorDecompositionIntegralUnitSubgroup
        (K := K) (L := L) w ≃*
      ∀ wL : AbsoluteValueExtension
          (HeightOneSpectrum.adicAbv K w) L,
        (absoluteValueCompletionIntegers wL.1
          (absoluteValueExtension_isNonarchimedean
            (HeightOneSpectrum.adicAbv K w)
            (HeightOneSpectrum.isNonarchimedean_adicAbv K w)
            wL))ˣ :=
  (relativeLocalTensorDecompositionIntegralUnitSubgroupEquivProduct
    (K := K) (L := L) w).trans
      (finitePlaceLocalTensorDecompositionIntegralUnitProductEquivPiUnits
        (K := K) (L := L) w)
end
end

section
-- module Solutions.OAIQ244_DUKE.AlgebraicNumberTheory_Completion_IntegerRingComparison
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalCyclotomicCompletionAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.DiscreteNthRootsSubgroup.instTopologicalSpaceSubtypeUnitsMemSubgroup _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.residueFieldZModAlgebra _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.PrimeDegreePackets.diagonalLogAction _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.LocalClassFieldTheory.normalizationIntegerRingIsIntegralClosure
attribute [-simp] _root_.GlobalClassFieldTheory.Reciprocity.rationalCyclotomicGlobalToLocalizedAlgHom_apply _root_.GlobalClassFieldTheory.Reciprocity.rationalCyclotomicGlobalToLocalizedAlgHom_primitiveRoot _root_.IsDiscreteValuationRing.addVal_ringEquiv _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.OAI.PrimeDegreePackets.ThetaConstruction.schwartzCM_apply _root_.doubleCosetExtension_mk _root_.extendAbsoluteValueExtensionFromIntermediate_apply _root_.finitePlaceTensorRingEquivAboveAdic_apply_extension _root_.finitePlaceTensorUnitsEquivAboveAdic_apply_extension _root_.infinitePlaceAboveEquivExtension_apply_val _root_.infinitePlaceTensorRingEquivAbove_apply _root_.infinitePlaceTensorUnitsEquivAbove_apply _root_.mem_finitePlaceDecompositionGroup_iff _root_.restrictAbsoluteValueExtensionToIntermediate_apply
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

/-!
# Integer rings in the two finite-place completion models

This file restricts the canonical equivalences between the absolute-value and
adic completion models to their valuation rings.  It also identifies the
residue field of a rational finite-place completion.
-/

open scoped NumberField Classical NNReal ValuativeRel
open NumberField IsDedekindDomain

noncomputable section

open AlgebraicNumberTheory.Valuations
open LocalFieldTheory
open LocalFieldTheory.IsNonarchimedeanLocalField

/-- The canonical equivalence between the valuation ring of the chosen
localized completion and the concrete adic completion integers at its
centre. -/
noncomputable def chosenFinitePlaceLocalizedIntegerRingEquiv
    {K L : Type}
    [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    (v : HeightOneSpectrum (𝓞 K)) :
    let W :=
      finitePlaceExtensionCentre
        (K := K) (L := L) v
        (chosenFinitePlaceExtension (L := L) v)
    𝒪[ChosenFinitePlaceLocalizedCompletion
        (K := K) (L := L) v] ≃+*
      W.adicCompletionIntegers L := by
  let vK := HeightOneSpectrum.adicAbv K v
  let w := chosenFinitePlaceExtension (L := L) v
  let W :=
    finitePlaceExtensionCentre
      (K := K) (L := L) v w
  let E :=
    ChosenFinitePlaceLocalizedCompletion
      (K := K) (L := L) v
  let eField : E ≃+* W.adicCompletion L :=
    (AlgebraicNumberTheory.Valuations.localizedCompletionEquivCompletion
        vK (RayClass.adicAbv_isNontrivial v) w).toRingEquiv.trans
      (finitePlaceExtensionAdicCompletionRingEquiv
        (K := K) (L := L) v w)
  exact
    RingEquiv.restrict eField 𝒪[E]
      (W.adicCompletionIntegers L).toSubring (by
        intro x
        symm
        change
          eField x ∈ W.adicCompletionIntegers L ↔
            x ∈ 𝒪[E]
        change
          finitePlaceExtensionAdicCompletionRingEquiv
                (K := K) (L := L) v w
                (AlgebraicNumberTheory.Valuations.localizedCompletionEquivCompletion
                  vK (RayClass.adicAbv_isNontrivial v) w x) ∈
              W.adicCompletionIntegers L ↔
            x ∈ 𝒪[E]
        rw [
          finitePlaceExtensionAdicCompletionRingEquiv_mem_integers_iff,
          mem_absoluteValueCompletionIntegers_iff,
          localizedCompletion_mem_integers_iff_norm_le_one
            vK w
            (HeightOneSpectrum.isNonarchimedean_adicAbv K v) x]
        rfl)

/-- The integer rings of the standard completion at the centre and of the
chosen localized completion are canonically equivalent. -/
noncomputable def standardToChosenLocalizedIntegerRingEquiv
    {K L : Type}
    [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    (v : HeightOneSpectrum (𝓞 K)) :
    let W := finitePlaceExtensionCentre
      (K := K) (L := L) v (chosenFinitePlaceExtension (L := L) v)
    𝒪[ChosenFinitePlaceBaseCompletion (K := L) W] ≃+*
      𝒪[ChosenFinitePlaceLocalizedCompletion (K := K) (L := L) v] := by
  let W := finitePlaceExtensionCentre
    (K := K) (L := L) v (chosenFinitePlaceExtension (L := L) v)
  exact (finitePlaceCompletionIntegerRingEquiv W).trans
    (chosenFinitePlaceLocalizedIntegerRingEquiv (K := K) (L := L) v).symm

/-- Embed global integers into the integer ring of the chosen localized
completion, through the canonical comparison of completion models. -/
noncomputable def chosenFinitePlaceIntegerToLocalizedCompletion
    {K L : Type}
    [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    (v : HeightOneSpectrum (𝓞 K)) :
    (𝓞 L) →+*
      𝒪[ChosenFinitePlaceLocalizedCompletion (K := K) (L := L) v] := by
  let W := finitePlaceExtensionCentre
    (K := K) (L := L) v (chosenFinitePlaceExtension (L := L) v)
  exact (standardToChosenLocalizedIntegerRingEquiv
    (K := K) (L := L) v).toRingHom.comp
      (finitePlaceIntegerToCompletion W)

/-- On global integers the chosen localized integer-ring map is the
standard field embedding into the algebraic localization. -/
@[simp]
theorem chosenFinitePlaceIntegerToLocalizedCompletion_coe
    {K L : Type}
    [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    (v : HeightOneSpectrum (𝓞 K)) (x : 𝓞 L) :
    ((chosenFinitePlaceIntegerToLocalizedCompletion
        (K := K) (L := L) v x :
        𝒪[ChosenFinitePlaceLocalizedCompletion (K := K) (L := L) v]) :
        ChosenFinitePlaceLocalizedCompletion (K := K) (L := L) v) =
      AbsoluteValue.toAlgebraicLocalization
        (HeightOneSpectrum.adicAbv K v)
        (chosenFinitePlaceExtension (L := L) v).1
        (chosenFinitePlaceExtension (L := L) v).2
        (x : L) := by
  let vK := HeightOneSpectrum.adicAbv K v
  let w := chosenFinitePlaceExtension (L := L) v
  let W := finitePlaceExtensionCentre (K := K) (L := L) v w
  let E := ChosenFinitePlaceLocalizedCompletion (K := K) (L := L) v
  let eField : E ≃+* W.adicCompletion L :=
    (AlgebraicNumberTheory.Valuations.localizedCompletionEquivCompletion
        vK (RayClass.adicAbv_isNontrivial v) w).toRingEquiv.trans
      (finitePlaceExtensionAdicCompletionRingEquiv
        (K := K) (L := L) v w)
  have hRight :
      eField (AbsoluteValue.toAlgebraicLocalization
          vK w.1 w.2 (x : L)) =
        FinitePlace.embedding W (x : L) := by
    change
      finitePlaceExtensionAdicCompletionRingEquiv
          (K := K) (L := L) v w
          (AlgebraicNumberTheory.Valuations.localizedCompletionEquivCompletion
            vK (RayClass.adicAbv_isNontrivial v) w
            (AbsoluteValue.toAlgebraicLocalization vK w.1 w.2 (x : L))) =
        FinitePlace.embedding W (x : L)
    rw [AlgebraicNumberTheory.Valuations.localizedCompletionEquivCompletion_coe,
      AbsoluteValue.toAlgebraicLocalization_apply]
    exact finitePlaceExtensionAdicCompletionRingEquiv_toCompletion v w (x : L)
  apply eField.injective
  calc
    eField
        ((chosenFinitePlaceIntegerToLocalizedCompletion
          (K := K) (L := L) v x : 𝒪[E]) : E) =
      finitePlaceCompletionRingEquiv W
        ((finitePlaceIntegerToCompletion W x :
          𝒪[ChosenFinitePlaceBaseCompletion (K := L) W]) :
            ChosenFinitePlaceBaseCompletion (K := L) W) := by
        have hInteger :
            chosenFinitePlaceLocalizedIntegerRingEquiv (K := K) (L := L) v
                (chosenFinitePlaceIntegerToLocalizedCompletion
                  (K := K) (L := L) v x) =
              finitePlaceCompletionIntegerRingEquiv W
                (finitePlaceIntegerToCompletion W x) := by
          change
            (chosenFinitePlaceLocalizedIntegerRingEquiv (K := K) (L := L) v)
                ((chosenFinitePlaceLocalizedIntegerRingEquiv
                  (K := K) (L := L) v).symm
                  ((finitePlaceCompletionIntegerRingEquiv W)
                    (finitePlaceIntegerToCompletion W x))) = _
          exact RingEquiv.apply_symm_apply _ _
        exact congrArg
          (fun y : W.adicCompletionIntegers L =>
            (y : W.adicCompletion L)) hInteger
    _ = FinitePlace.embedding W (x : L) := by
      rw [finitePlaceIntegerToCompletion_coe]
      exact finitePlaceCompletionRingEquiv_toCompletion W (x : L)
    _ = eField (AbsoluteValue.toAlgebraicLocalization vK w.1 w.2 (x : L)) :=
      hRight.symm

/-- The centre ideal and the chosen localized completion have canonically
equivalent residue fields.  This transfers ideal-theoretic Frobenius
conditions to the local field on which the chosen Artin map acts. -/
noncomputable def chosenFinitePlaceLocalizedResidueEquiv
    {K L : Type}
    [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    (v : HeightOneSpectrum (𝓞 K)) :
    let W := finitePlaceExtensionCentre
      (K := K) (L := L) v (chosenFinitePlaceExtension (L := L) v)
    (𝓞 L ⧸ W.asIdeal) ≃+*
      𝓀[ChosenFinitePlaceLocalizedCompletion (K := K) (L := L) v] := by
  let W := finitePlaceExtensionCentre
    (K := K) (L := L) v (chosenFinitePlaceExtension (L := L) v)
  exact (finitePlaceIdealResidueEquivCompletion W).trans
    (IsLocalRing.ResidueField.mapEquiv
      (standardToChosenLocalizedIntegerRingEquiv (K := K) (L := L) v))

@[simp]
theorem chosenFinitePlaceLocalizedResidueEquiv_apply_mk
    {K L : Type}
    [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    (v : HeightOneSpectrum (𝓞 K)) (x : 𝓞 L) :
    let W := finitePlaceExtensionCentre
      (K := K) (L := L) v (chosenFinitePlaceExtension (L := L) v)
    chosenFinitePlaceLocalizedResidueEquiv (K := K) (L := L) v
        (Ideal.Quotient.mk W.asIdeal x) =
      IsLocalRing.residue
        𝒪[ChosenFinitePlaceLocalizedCompletion (K := K) (L := L) v]
        (chosenFinitePlaceIntegerToLocalizedCompletion
          (K := K) (L := L) v x) := by
  let W := finitePlaceExtensionCentre
    (K := K) (L := L) v (chosenFinitePlaceExtension (L := L) v)
  let eInteger :
      𝒪[ChosenFinitePlaceBaseCompletion (K := L) W] ≃+*
        𝒪[ChosenFinitePlaceLocalizedCompletion (K := K) (L := L) v] :=
    standardToChosenLocalizedIntegerRingEquiv (K := K) (L := L) v
  have hMap :
      eInteger (finitePlaceIntegerToCompletion W x) =
        chosenFinitePlaceIntegerToLocalizedCompletion
          (K := K) (L := L) v x := by
    rfl
  calc
    chosenFinitePlaceLocalizedResidueEquiv (K := K) (L := L) v
        (Ideal.Quotient.mk W.asIdeal x) =
      (IsLocalRing.ResidueField.mapEquiv eInteger)
        (finitePlaceIdealResidueEquivCompletion W
          (Ideal.Quotient.mk W.asIdeal x)) := by
        rfl
    _ = (IsLocalRing.ResidueField.mapEquiv eInteger)
          (IsLocalRing.residue
            𝒪[ChosenFinitePlaceBaseCompletion (K := L) W]
            (finitePlaceIntegerToCompletion W x)) := by
      exact congrArg (IsLocalRing.ResidueField.mapEquiv eInteger)
        (finitePlaceIdealResidueEquivCompletion_apply_mk W x)
    _ = IsLocalRing.residue
          𝒪[ChosenFinitePlaceLocalizedCompletion (K := K) (L := L) v]
          (eInteger (finitePlaceIntegerToCompletion W x)) := by
      rfl
    _ = IsLocalRing.residue
          𝒪[ChosenFinitePlaceLocalizedCompletion (K := K) (L := L) v]
          (chosenFinitePlaceIntegerToLocalizedCompletion
            (K := K) (L := L) v x) := by
      exact congrArg
        (IsLocalRing.residue
          𝒪[ChosenFinitePlaceLocalizedCompletion (K := K) (L := L) v]) hMap
end
end

section
-- module Solutions.OAIQ244_DUKE.AlgebraicNumberTheory_Completion_UnramifiedComparison_IdealToCompletion
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.residueFieldZModAlgebra _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.LocalClassFieldTheory.normalizationIntegerRingIsIntegralClosure
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

omit [FiniteDimensional K L] in
/-- Ideal-theoretic unramifiedness gives ramification index one at the actual
centre of the chosen finite-place extension. -/
theorem finitePlaceExtensionCentre_ramificationIdx_eq_one_of_isUnramifiedAt
    (v : HeightOneSpectrum (𝓞 K))
    (hunram :
      Algebra.IsUnramifiedAt (𝓞 K)
        (finitePlaceExtensionCentre
          (K := K) (L := L) v
          (chosenFinitePlaceExtension (L := L) v)).asIdeal) :
    v.asIdeal.ramificationIdx'
        (finitePlaceExtensionCentre
          (K := K) (L := L) v
          (chosenFinitePlaceExtension (L := L) v)).asIdeal =
      1 := by
  let w := chosenFinitePlaceExtension (L := L) v
  let W :=
    finitePlaceExtensionCentre
      (K := K) (L := L) v w
  let : W.asIdeal.LiesOver v.asIdeal :=
    finitePlaceExtensionCentre_liesOver
      (K := K) (L := L) v w
  rw [Ideal.ramificationIdx'_eq_ramificationIdx
    v.asIdeal W.asIdeal v.ne_bot]
  let : Algebra.IsUnramifiedAt (𝓞 K) W.asIdeal := hunram
  exact Ideal.ramificationIdx_eq_one W.asIdeal (𝓞 K)
end
end

section
-- module Solutions.OAIQ244_DUKE.LocalClassFieldTheory_Finite_Unramified_Cohomology
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.DiscreteNthRootsSubgroup.instCommGroupSubtypeUnitsMemSubgroup _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalClassFieldTheory.localDecompositionResidueFintype _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.residueFieldZModAlgebra _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.LubinTate.compatibleGroupFamiliesCommGroup _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.RamificationTheory.HilbertRamification.ValuationSubring.selectedResidueField.instAlgebra _root_.RayClass.approximationCompletionTopologicalSpace _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.CyclicCohomology.binaryCoefficientFamilyCommGroup _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.LocalClassFieldTheory.normalizationIntegerRingIsIntegralClosure _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.chosenFinitePlaceCompletionAlgebra _root_.finiteLocalUnitsOpen _root_.relativeAdeleRingIntermediateAlgebra _root_.relativeAdeleRingTopIntermediateAlgebra _root_.relativeUnrestrictedSPlaceFactorCommGroup
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

/-- The normal-basis construction, restricted to its actual
integer-unit conclusion `h(G,𝒪_Lˣ)=1`. -/
theorem integerUnits_herbrandQuotient_eq_one
    (K L : Type) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    [ValuativeRel L] [UniformSpace L] [IsUniformAddGroup L]
    [IsNonarchimedeanLocalField L]
    [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]
    [IsIntegralClosure 𝒪[L] 𝒪[K] L] [Module.Finite 𝒪[K] 𝒪[L]]
    (g : Gal(L / K)) (hg : ∀ sigma : Gal(L / K), sigma ∈ Subgroup.zpowers g) :
    letI := galoisGroupIntegerUnitsMulDistribMulActionOfIsIntegralClosure K L
    ∃ hU : HerbrandQuotientDefined Gal(L / K) 𝒪[L]ˣ g,
      @herbrandQuotient Gal(L / K) 𝒪[L]ˣ _ _ _
        (galoisGroupIntegerUnitsMulDistribMulActionOfIsIntegralClosure K L)
        g hU.1 hU.2 = 1 := by
  rcases exists_chosenNormalBasisPrincipalUnitSubgroup (K := K) (L := L) with
    ⟨cV, hcV⟩
  rcases exists_chosenNormalBasisPrincipalUnit_herbrand_subsingleton
      (K := K) (L := L) g hg with ⟨cH, hcH⟩
  rcases exists_integerUnits_herbrandQuotient_eq_one_of_large_chosenNormalBasisLevel
      (K := K) (L := L) with ⟨cU, hcU⟩
  let n : Nat := max cV (max cH cU)
  have hcVn : cV ≤ n := le_max_left cV (max cH cU)
  have hrest : max cH cU ≤ n := le_max_right cV (max cH cU)
  have hcHn : cH ≤ n := le_trans (le_max_left cH cU) hrest
  have hcUn : cU ≤ n := le_trans (le_max_right cH cU) hrest
  rcases hcV n hcVn with ⟨V, hV, _⟩
  let := chosenNormalBasisPrincipalUnitSubgroupMulDistribMulAction K L n V hV
  let := galoisGroupIntegerUnitsMulDistribMulActionOfIsIntegralClosure K L
  let := chosenNormalBasisIntegerUnitsQuotMulDistribMulAction K L n V hV
  have hcoh := hcH n hcHn V hV
  exact hcU n hcUn V hV g hg hcoh.1 hcoh.2

end LocalClassFieldTheory
end
end

section
-- module Solutions.OAIQ244_DUKE.AlgebraicNumberTheory_Idele_Cohomology_SPlaces_Herbrand_Local
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalCyclotomicCompletionAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.LocalClassFieldTheory.normalizationIntegerRingIsIntegralClosure
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

/-- The local degree attached to one unrestricted place.  At a finite
place it is the degree of the chosen localization; at an infinite place
it is one or two according as the place is unramified or ramified. -/
noncomputable def relativeUnrestrictedSPlaceLocalDegree
    (S : Finset (HeightOneSpectrum (𝓞 K))) :
    RelativeUnrestrictedSPlaceIndex (K := K) S → ℕ :=
  fun i =>
    Nat.card
      (absoluteValueDecompositionGroup K
        ((relativeUnrestrictedSPlaceDatum
          (K := K) (L := L) S i).extension.1))
end
end

section
-- module Solutions.OAIQ244_DUKE.AlgebraicNumberTheory_Idele_NormApproximation_InfinitePlaces
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalCyclotomicCompletionAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.residueFieldZModAlgebra _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.PrimeDegreePackets.diagonalLogAction _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.LocalClassFieldTheory.normalizationIntegerRingIsIntegralClosure _root_.chosenFinitePlaceCompletionAlgebra _root_.chosenFinitePlaceCompletionContinuousSMul _root_.chosenFinitePlaceCompletionFiniteDimensional _root_.chosenFinitePlaceCompletionLocallyCompactSpace _root_.chosenFinitePlaceLocalizedFiniteDimensional _root_.chosenFinitePlaceLocalizedIntegerAlgebra _root_.chosenFinitePlaceLocalizedIntegerModuleFinite _root_.chosenFinitePlaceLocalizedIsGalois _root_.chosenFinitePlaceLocalizedIsIntegralClosure _root_.chosenFinitePlaceLocalizedIsNonarchimedeanLocalField _root_.chosenFinitePlaceLocalizedIsValuativeTopology _root_.chosenFinitePlaceLocalizedLocallyCompactSpace _root_.chosenFinitePlaceLocalizedValuationCompatible _root_.chosenFinitePlaceLocalizedValuationHasExtension _root_.chosenFinitePlaceLocalizedValuationIsNontrivial _root_.chosenFinitePlaceLocalizedValuativeRel _root_.chosenFinitePlaceLocalizedValuativeRelIsNontrivial _root_.chosenFinitePlaceLocalizedValued _root_.scaledRelativeIntegerLatticeQuotientFinite
attribute [-simp] _root_.GlobalClassFieldTheory.Reciprocity.rationalCyclotomicGlobalToLocalizedAlgHom_apply _root_.GlobalClassFieldTheory.Reciprocity.rationalCyclotomicGlobalToLocalizedAlgHom_primitiveRoot _root_.IsDiscreteValuationRing.addVal_ringEquiv _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.OAI.PrimeDegreePackets.ThetaConstruction.schwartzCM_apply _root_.chosenFinitePlaceIntegerToLocalizedCompletion_coe _root_.chosenFinitePlaceLocalizedResidueEquiv_apply_mk _root_.doubleCosetExtension_mk _root_.extendAbsoluteValueExtensionFromIntermediate_apply _root_.finitePlaceBelow_finitePlaceExtensionCentre _root_.finitePlaceExtensionAdicCompletionRingEquiv_toCompletion _root_.finitePlaceExtensionCentreInFibre_coe _root_.finitePlaceExtensionCentre_asIdeal _root_.finitePlaceExtensionCompletionRingEquiv_toCompletion _root_.finitePlaceExtensionEquivAbove_coe _root_.finitePlaceLocalTensorDecompositionComponentRingHom_apply _root_.finitePlaceLocalTensorDecompositionComponent_add _root_.finitePlaceLocalTensorDecompositionComponent_tmul _root_.finitePlaceLocalTensorDecompositionComponent_zero _root_.finitePlaceLocalTensorDecompositionUnitsComponent_coe _root_.finitePlaceLocalTensorDecompositionUnitsEquiv_apply _root_.finitePlaceTensorRingEquivAboveAdic_apply_extension _root_.finitePlaceTensorUnitsEquivAboveAdic_apply_extension _root_.infinitePlaceAboveEquivExtension_apply_val _root_.infinitePlaceTensorRingEquivAbove_apply _root_.infinitePlaceTensorUnitsEquivAbove_apply _root_.infinitePlace_mult_smul _root_.restrictAbsoluteValueExtensionToIntermediate_apply _root_.ringOfIntegersToFinitePlaceExtensionValuationSubring_coe
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

/-- Complete splitting at a finite place makes the chosen local norm
subgroup the whole multiplicative group. -/
theorem chosenFinitePlaceLocalNormSubgroup_eq_top_of_splitsCompletely
    [IsGalois K L]
    (v : HeightOneSpectrum (𝓞 K))
    (hsplit :
      FinitePlaceSplitsCompletely
        (K := K) (L := L) v) :
    chosenFinitePlaceLocalNormSubgroup
        (K := K) (L := L) v = ⊤ := by
  apply top_unique
  intro x _
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
  let E :=
    AlgebraicNumberTheory.Valuations.LocalizedCompletion vK w
  let : FiniteDimensional vK.Completion E :=
    AlgebraicNumberTheory.Valuations.localizedCompletionModuleFinite
      vK hvK w
  have hdegree :
      Module.finrank vK.Completion E = 1 := by
    simpa [finitePlaceLocalDegree, vK, w, E] using
      (finitePlaceSplitsCompletely_iff_localDegree_eq_one
        (K := K) (L := L) v).mp hsplit
  let e :
      vK.Completionˣ ≃ₜ* (v.adicCompletion K)ˣ :=
    finitePlaceCompletionUnitsContinuousMulEquiv v
  change x ∈
    (localNormSubgroup vK.Completion E).map e.toMonoidHom
  refine ⟨e.symm x, ?_, e.apply_symm_apply x⟩
  refine
    ⟨LocalFieldTheory.IsNonarchimedeanLocalField.mapBaseUnitsToExtensionUnits
        vK.Completion E (e.symm x), ?_⟩
  change
    LocalFieldTheory.normUnits
        vK.Completion E
        (LocalFieldTheory.IsNonarchimedeanLocalField.mapBaseUnitsToExtensionUnits
          vK.Completion E (e.symm x)) =
      e.symm x
  simpa [hdegree] using
    (LocalFieldTheory.IsNonarchimedeanLocalField.normUnits_algebraMap_base
      (K := vK.Completion) (L := E) (e.symm x))
end
end

section
-- module Solutions.OAIQ244_DUKE.AlgebraicNumberTheory_Idele_Relative_FiniteIntegralNormPreimage
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalCyclotomicCompletionAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.residueFieldZModAlgebra _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.PrimeDegreePackets.diagonalLogAction _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.LocalClassFieldTheory.normalizationIntegerRingIsIntegralClosure
attribute [-simp] _root_.GlobalClassFieldTheory.Reciprocity.rationalCyclotomicGlobalToLocalizedAlgHom_apply _root_.GlobalClassFieldTheory.Reciprocity.rationalCyclotomicGlobalToLocalizedAlgHom_primitiveRoot _root_.IsDiscreteValuationRing.addVal_ringEquiv _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.OAI.PrimeDegreePackets.ThetaConstruction.schwartzCM_apply _root_.chosenFinitePlaceIntegerToLocalizedCompletion_coe _root_.chosenFinitePlaceLocalizedResidueEquiv_apply_mk _root_.doubleCosetExtension_mk _root_.extendAbsoluteValueExtensionFromIntermediate_apply _root_.finitePlaceBelow_finitePlaceExtensionCentre _root_.finitePlaceExtensionAdicCompletionRingEquiv_toCompletion _root_.finitePlaceExtensionCentreInFibre_coe _root_.finitePlaceExtensionCentre_asIdeal _root_.finitePlaceExtensionCompletionRingEquiv_toCompletion _root_.finitePlaceExtensionEquivAbove_coe _root_.finitePlaceTensorRingEquivAboveAdic_apply_extension _root_.finitePlaceTensorUnitsEquivAboveAdic_apply_extension _root_.infinitePlaceAboveEquivExtension_apply_val _root_.infinitePlaceTensorRingEquivAbove_apply _root_.infinitePlaceTensorUnitsEquivAbove_apply _root_.infinitePlace_mult_smul _root_.mem_finitePlaceDecompositionGroup_iff _root_.restrictAbsoluteValueExtensionToIntermediate_apply _root_.ringOfIntegersToFinitePlaceExtensionValuationSubring_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

/-!
# Integral finite-place preimages of local tensor norms

If a finite local component is both a determinant norm and a local
integer unit, its determinant-norm preimage can be chosen integral in
every factor of the canonical local tensor decomposition.  This is the local restricted-product
input needed to assemble pointwise local norm preimages globally.
-/

open scoped NumberField TensorProduct ValuativeRel NNReal
open NumberField IsDedekindDomain

noncomputable section


open AlgebraicNumberTheory.Valuations
open LocalClassFieldTheory
open LocalFieldTheory
open LocalFieldTheory.IsNonarchimedeanLocalField
open ValuationTheory.Completion

variable
    {K L : Type}
    [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]

universe u

omit [NumberField K] [NumberField L] [IsGalois K L] in
/-- A unit of a localized completion whose underlying element and inverse
have norm at most one determines an integer unit in the full completion. -/
theorem exists_absoluteValueCompletionIntegerUnit_of_localizedCompletion_norm_bounds
    (vK : AbsoluteValue K ℝ)
    (hvK : vK.IsNontrivial)
    (hvKna : IsNonarchimedean (vK : K → ℝ))
    (w : AbsoluteValueExtension vK L)
    (y : (LocalizedCompletion vK w)ˣ)
    (hy : ‖(y : LocalizedCompletion vK w)‖ ≤ 1)
    (hyInv :
      ‖((y⁻¹ : (LocalizedCompletion vK w)ˣ) :
        LocalizedCompletion vK w)‖ ≤ 1) :
    ∃ yO :
        (absoluteValueCompletionIntegers w.1
          (absoluteValueExtension_isNonarchimedean
            vK hvKna w))ˣ,
      ((Units.map
        (absoluteValueCompletionIntegers w.1
          (absoluteValueExtension_isNonarchimedean
            vK hvKna w)).subtype yO :
          w.1.Completionˣ) :
        w.1.Completion) =
      ((y : LocalizedCompletion vK w) :
        w.1.Completion) := by
  let hK :=
    AbsoluteValue.extensionCompletionAlgebra (K := K) w.1
  let : SMul K w.1.Completion := hK.toSMul
  let : Algebra vK.Completion w.1.Completion :=
    AbsoluteValue.completionAlgebra vK w.1 w.2
  let eW :=
    localizedCompletionEquivCompletion vK hvK w
  let yW : w.1.Completionˣ :=
    Units.mapEquiv eW.toMulEquiv y
  have hyWMem :
      (yW : w.1.Completion) ∈
        absoluteValueCompletionIntegers w.1
          (absoluteValueExtension_isNonarchimedean
            vK hvKna w) := by
    rw [mem_absoluteValueCompletionIntegers_iff]
    change ‖eW (y : LocalizedCompletion vK w)‖ ≤ 1
    change ‖(y : LocalizedCompletion vK w)‖ ≤ 1
    exact hy
  have hyWInvMem :
      ((yW⁻¹ : w.1.Completionˣ) : w.1.Completion) ∈
        absoluteValueCompletionIntegers w.1
          (absoluteValueExtension_isNonarchimedean
            vK hvKna w) := by
    rw [mem_absoluteValueCompletionIntegers_iff]
    change
      ‖eW
        (((y⁻¹ : (LocalizedCompletion vK w)ˣ) :
          LocalizedCompletion vK w))‖ ≤ 1
    change
      ‖((y⁻¹ : (LocalizedCompletion vK w)ˣ) :
        LocalizedCompletion vK w)‖ ≤ 1
    exact hyInv
  let yO :
      (absoluteValueCompletionIntegers w.1
        (absoluteValueExtension_isNonarchimedean
          vK hvKna w))ˣ :=
    { val := ⟨yW, hyWMem⟩
      inv := ⟨yW⁻¹, by simpa using hyWInvMem⟩
      val_inv := by
        apply Subtype.ext
        simp
      inv_val := by
        apply Subtype.ext
        simp }
  refine ⟨yO, ?_⟩
  rfl

/-- A family of completion-integer units supported at one extension of a
finite place. -/
noncomputable def singleFinitePlaceIntegralUnitFamily
    (v₀ : HeightOneSpectrum (𝓞 K))
    (w :
      AbsoluteValueExtension
        (HeightOneSpectrum.adicAbv K v₀) L)
    (y :
      (absoluteValueCompletionIntegers w.1
        (absoluteValueExtension_isNonarchimedean
          (HeightOneSpectrum.adicAbv K v₀)
          (HeightOneSpectrum.isNonarchimedean_adicAbv K v₀)
          w))ˣ) :
    ∀ u :
        AbsoluteValueExtension
          (HeightOneSpectrum.adicAbv K v₀) L,
      (absoluteValueCompletionIntegers u.1
        (absoluteValueExtension_isNonarchimedean
          (HeightOneSpectrum.adicAbv K v₀)
          (HeightOneSpectrum.isNonarchimedean_adicAbv K v₀)
          u))ˣ := by
  classical
  exact fun u =>
    dite (w = u)
      (fun h => h ▸ y)
      (fun _ => 1)

/-- The integral local tensor unit represented by a unit in one completion
factor and by one in every other factor. -/
noncomputable def singleRelativeLocalTensorDecompositionIntegralUnit
    (v₀ : HeightOneSpectrum (𝓞 K))
    (w :
      AbsoluteValueExtension
        (HeightOneSpectrum.adicAbv K v₀) L)
    (y :
      (absoluteValueCompletionIntegers w.1
        (absoluteValueExtension_isNonarchimedean
          (HeightOneSpectrum.adicAbv K v₀)
          (HeightOneSpectrum.isNonarchimedean_adicAbv K v₀)
          w))ˣ) :
    relativeLocalTensorDecompositionIntegralUnitSubgroup
      (K := K) (L := L) v₀ :=
  (relativeLocalTensorDecompositionIntegralUnitSubgroupEquivPiUnits
    (K := K) (L := L) v₀).symm
      (singleFinitePlaceIntegralUnitFamily
        (K := K) (L := L) v₀ w y)
end
end

section
-- module Solutions.OAIQ244_DUKE.GlobalClassFieldTheory_Cohomology_CyclicPrimePowerFullDecomposition
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalCyclotomicCompletionAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.KummerTheory.primeCyclotomicBaseIsGalois _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.residueFieldZModAlgebra _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.PrimeDegreePackets.diagonalLogAction _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.LocalClassFieldTheory.normalizationIntegerRingIsIntegralClosure _root_.cyclicPrimeDegreeIntermediate_isGalois
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

omit [NumberField L] in
/-- Every place with proper decomposition group in `L / K` splits
completely, in the standard chosen-extension sense, in the actual
degree-`p` fixed subextension. -/
theorem
    finitePlaceSplitsCompletely_in_cyclicPrimeSubextension_of_decompositionGroup_ne_top
    {p exponent : ℕ}
    (hp : p.Prime)
    (hexponent : 0 < exponent)
    (hcard : Nat.card (L ≃ₐ[K] L) = p ^ exponent)
    (v : HeightOneSpectrum (𝓞 K))
    (hproper :
      finitePlaceDecompositionGroup
          (K := K) (L := L) v ≠ ⊤) :
    FinitePlaceSplitsCompletely
      (K := K)
      (L := cyclicPrimeSubextension
        (K := K) (L := L)
        hp hexponent hcard) v := by
  let M :=
    cyclicPrimeSubextension
      (K := K) (L := L)
      hp hexponent hcard
  let : IsGalois K M :=
    cyclicPrimeSubextension_isGalois
      (K := K) (L := L)
      hp hexponent hcard
  let vK :=
    NumberField.HeightOneSpectrum.adicAbv K v
  let hvK : vK.IsNontrivial :=
    RayClass.adicAbv_isNontrivial v
  let w :=
    chosenFinitePlaceExtension (L := L) v
  let wM :=
    restrictAbsoluteValueExtensionToIntermediate
      vK w M
  have hcustom :
      cyclicPrimeSubextensionDecompositionGroup
          (K := K) (L := L)
          hp hexponent hcard v = ⊥ :=
    cyclicPrimeSubextensionDecompositionGroup_eq_bot_of_ne_top
      (K := K) (L := L)
      hp hexponent hcard v hproper
  have hwMbot :
      absoluteValueDecompositionGroup K wM.1 = ⊥ := by
    change
      absoluteValueDecompositionGroup K
        (w.1.comp (f := algebraMap M L)
          (algebraMap M L).injective) = ⊥
    rw [← absoluteValueDecompositionGroup_map_restrictNormalHom
      (M := M) vK hvK w]
    exact hcustom
  change
    absoluteValueDecompositionGroup K
      (chosenFinitePlaceExtension
        (L := M) v).1 = ⊥
  exact
    absoluteValueDecompositionGroup_eq_bot_independent_extension
      vK hvK wM
      (chosenFinitePlaceExtension (L := M) v)
      hwMbot

end Cohomology
end GlobalClassFieldTheory
end
end


