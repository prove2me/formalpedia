-- Prove2me | Definitions.Def_OAIQ244Duke057
-- name    : OAIQ244Duke057
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-13T22:15:42.171261+00:00
-- url     : https://prove2.me/theorems/36c095c4-38c6-40c5-9d1a-9f4f607cf1ea
-- title:
--   Definitions bundle OAIQ244Duke057 of the split of OpenAI, Equidistribution of Prime-Degree Torus Packets with Arbitrary Local Type
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.DukePrimeDegree.prime_degree_packet_measure_equidistribution_unconditional` and `OAI.DukePrimeDegree.prime_degree_packet_measures_tendsto_haar_unconditional`, carved from OpenAI's openai/math development (OpenAI, *Equidistribution of Prime-Degree Torus Packets with Arbitrary Local Type*, OpenAI Math Release, September 24, 2026, result family 15, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 14 declarations of OpenAI's Lean: 9 definitions and 5 theorems. The definitions and types are `RelativeOutsideSPlaceFactors`, `chosenFinitePlaceIntegralInducedBlockToLocalPlaceBlock`, `completionProductIntegerUnitsEquivInducedModule`, `inducedIntegerUnitsToLocalPlaceBlock`, `relativeIdeleSPlaceFactorsAction`, `relativeIdeleSPlaceFactorsEquivUnrestrictedProdOutside`, `relativeOutsideSPlaceFactorsAction`, `relativeUnrestrictedProdOutsideAction`, `rightCosetCompletionIntegersRingEquivLocalized`.
--
--   **Sources.** They come from these modules of lean/OAI/NumberTheory, in whole or in part: `AlgebraicNumberTheory_Idele_Cohomology_SPlaces_OutsideIntegralInduced_ChosenPlaceAction`, `AlgebraicNumberTheory_Idele_Cohomology_SPlaces_OutsideIntegralInduced_ChosenPlaceIntegralBlockInclusion`, `AlgebraicNumberTheory_Idele_Cohomology_SPlaces_OutsideIntegralInduced_CompletionTransport`, `AlgebraicNumberTheory_Idele_Cohomology_SPlaces_OutsideIntegralInduced_LocalInduction_Equiv`, `AlgebraicNumberTheory_Idele_Cohomology_SPlaces_OutsideIntegralInduced_LocalInduction_Inclusion`, `AlgebraicNumberTheory_Idele_Cohomology_SPlaces_Reassociation`, `AlgebraicNumberTheory_Idele_Relative_SPlaces`, `KummerTheory_Concrete_SUnitPreparation_FiniteRadicalSupport`.
--
--   **Imports.** It imports the bundles `OAIQ244Duke046`, `OAIQ244Duke048` and `OAIQ244Duke049` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ244Duke063` and `OAIQ244Duke064`.
-- source:
--   OpenAI, Equidistribution of Prime-Degree Torus Packets with Arbitrary Local Type, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 15; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Equidistribution-of-Prime-Degree-Torus-Packets-with-Arbitrary-Local-Type-September-24-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/NumberTheory at commit 7ef5c0c

import Mathlib
import Mathlib.Algebra.Algebra.Basic
import Mathlib.Algebra.Algebra.Pi
import Mathlib.Algebra.Algebra.Tower
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Category.ModuleCat.Basic
import Mathlib.Algebra.CharP.Lemmas
import Mathlib.Algebra.CharP.Subring
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
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Int.ModEq
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
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.FieldTheory.IsSepClosed
import Mathlib.FieldTheory.KrullTopology
import Mathlib.FieldTheory.Minpoly.IsConjRoot
import Mathlib.FieldTheory.Minpoly.IsIntegrallyClosed
import Mathlib.FieldTheory.Normal.Basic
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
import Mathlib.LinearAlgebra.FreeModule.IdealQuotient
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
import Mathlib.NumberTheory.NumberField.ProductFormula
import Mathlib.NumberTheory.NumberField.Units.DirichletTheorem
import Mathlib.NumberTheory.NumberField.Units.Regulator
import Mathlib.NumberTheory.Ostrowski
import Mathlib.NumberTheory.RamificationInertia.Galois
import Mathlib.NumberTheory.RamificationInertia.Inertia
import Mathlib.NumberTheory.RamificationInertia.Ramification
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
import Mathlib.RingTheory.Complex
import Mathlib.RingTheory.DedekindDomain.Factorization
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
import Mathlib.RingTheory.Polynomial.GaussLemma
import Mathlib.RingTheory.Polynomial.Vieta
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
import Mathlib.RingTheory.Valuation.Discrete.Basic
import Mathlib.RingTheory.Valuation.Discrete.IsDiscreteValuationRing
import Mathlib.RingTheory.Valuation.Extension
import Mathlib.RingTheory.Valuation.Integral
import Mathlib.RingTheory.Valuation.LocalSubring
import Mathlib.RingTheory.Valuation.RamificationGroup
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
import Mathlib.Topology.Algebra.IsOpenUnits
import Mathlib.Topology.Algebra.IsUniformGroup.Basic
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.Topology.Algebra.OpenSubgroup
import Mathlib.Topology.Algebra.Ring.Basic
import Mathlib.Topology.Algebra.Ring.Compact
import Mathlib.Topology.Algebra.Valued.LocallyCompact
import Mathlib.Topology.Algebra.Valued.ValuativeRel
import Mathlib.Topology.Algebra.Valued.ValuedField
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
-- module Solutions.OAIQ244_DUKE.AlgebraicNumberTheory_Idele_Cohomology_SPlaces_OutsideIntegralInduced_CompletionTransport
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalCyclotomicCompletionAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.residueFieldZModAlgebra _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.PrimeDegreePackets.diagonalLogAction _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.LocalClassFieldTheory.normalizationIntegerRingIsIntegralClosure _root_.chosenFinitePlaceCompletionAlgebra _root_.chosenFinitePlaceCompletionContinuousSMul _root_.chosenFinitePlaceCompletionFiniteDimensional _root_.chosenFinitePlaceCompletionLocallyCompactSpace _root_.chosenFinitePlaceLocalizedFiniteDimensional _root_.chosenFinitePlaceLocalizedIntegerAlgebra _root_.chosenFinitePlaceLocalizedIntegerModuleFinite _root_.chosenFinitePlaceLocalizedIsGalois _root_.chosenFinitePlaceLocalizedIsIntegralClosure _root_.chosenFinitePlaceLocalizedIsNonarchimedeanLocalField _root_.chosenFinitePlaceLocalizedIsValuativeTopology _root_.chosenFinitePlaceLocalizedLocallyCompactSpace _root_.chosenFinitePlaceLocalizedValuationCompatible _root_.chosenFinitePlaceLocalizedValuationHasExtension _root_.chosenFinitePlaceLocalizedValuationIsNontrivial _root_.chosenFinitePlaceLocalizedValuativeRel _root_.chosenFinitePlaceLocalizedValuativeRelIsNontrivial _root_.chosenFinitePlaceLocalizedValued
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

/-!
# Transporting integer rings across finite-place cosets

This file transports completion fields and their valuation rings from every
right coset of a decomposition group to the chosen algebraic localization.
-/

open scoped NumberField TensorProduct ValuativeRel NNReal
open NumberField IsDedekindDomain

noncomputable section

open AlgebraicNumberTheory.Valuations
open HilbertRamification
open LocalClassFieldTheory
open LocalFieldTheory

variable
    {K : Type} {L : Type}
    [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]

section CompletionTransport

variable (vK : AbsoluteValue K ℝ) (hvK : vK.IsNontrivial)
    (w : AbsoluteValueExtension vK L)

omit [NumberField K] [NumberField L] in
/-- The right-coset transport is an isometry for the inherited norms. -/
theorem rightCosetCompletionRingEquivLocalized_norm_eq
    (q : InducedRightCosets (absoluteValueDecompositionGroup K w.1))
    (x : (absoluteValueExtensionConjugate
      vK w (Quotient.out q)).1.Completion) :
    letI hK := AbsoluteValue.extensionCompletionAlgebra (K := K) w.1
    letI : SMul K w.1.Completion := hK.toSMul
    letI := AbsoluteValue.completionAlgebra vK w.1 w.2
    ‖rightCosetCompletionRingEquivLocalized vK hvK w q x‖ =
      ‖x‖ := by
  let hK := AbsoluteValue.extensionCompletionAlgebra (K := K) w.1
  let : SMul K w.1.Completion := hK.toSMul
  let := AbsoluteValue.completionAlgebra vK w.1 w.2
  let z :=
    conjugateExtensionCompletionRingEquiv
      vK w (Quotient.out q) x
  have hcoe :
      (((localizedCompletionEquivCompletion vK hvK w).symm z :
          LocalizedCompletion vK w) : w.1.Completion) = z := by
    have h :=
      localizedCompletionEquivCompletion_coe
        vK hvK w
          ((localizedCompletionEquivCompletion vK hvK w).symm z)
    rw [AlgEquiv.apply_symm_apply] at h
    exact h.symm
  change
    ‖(((localizedCompletionEquivCompletion vK hvK w).symm z :
        LocalizedCompletion vK w) : w.1.Completion)‖ = ‖x‖
  rw [hcoe]
  exact
    conjugateExtensionCompletionRingEquiv_norm_eq
      vK w (Quotient.out q) x

/-- The same transport restricted to the two valuation integer rings. -/
noncomputable def rightCosetCompletionIntegersRingEquivLocalized
    (hvKna : IsNonarchimedean (vK : K → ℝ))
    (q : InducedRightCosets (absoluteValueDecompositionGroup K w.1)) :
    letI hK := AbsoluteValue.extensionCompletionAlgebra (K := K) w.1
    letI : SMul K w.1.Completion := hK.toSMul
    letI := AbsoluteValue.completionAlgebra vK w.1 w.2
    letI : Valued (LocalizedCompletion vK w) ℝ≥0 :=
      localizedCompletionFinitePlaceValued vK w hvKna
    letI : ValuativeRel (LocalizedCompletion vK w) :=
      localizedCompletionFinitePlaceValuativeRel vK w hvKna
    (absoluteValueCompletionIntegers
      (absoluteValueExtensionConjugate
        vK w (Quotient.out q)).1
      (absoluteValueExtension_isNonarchimedean
        vK hvKna
        (absoluteValueExtensionConjugate
          vK w (Quotient.out q)))) ≃+*
      𝒪[LocalizedCompletion vK w] := by
  letI hK := AbsoluteValue.extensionCompletionAlgebra (K := K) w.1
  letI : SMul K w.1.Completion := hK.toSMul
  letI := AbsoluteValue.completionAlgebra vK w.1 w.2
  letI : Valued (LocalizedCompletion vK w) ℝ≥0 :=
    localizedCompletionFinitePlaceValued vK w hvKna
  letI : ValuativeRel (LocalizedCompletion vK w) :=
    localizedCompletionFinitePlaceValuativeRel vK w hvKna
  let e :
      (absoluteValueExtensionConjugate
        vK w (Quotient.out q)).1.Completion ≃+*
        LocalizedCompletion vK w :=
    rightCosetCompletionRingEquivLocalized vK hvK w q
  refine e.restrict _ _ ?_
  intro x
  rw [mem_absoluteValueCompletionIntegers_iff,
    localizedCompletion_mem_integers_iff_norm_le_one]
  have hnorm :=
    rightCosetCompletionRingEquivLocalized_norm_eq
      vK hvK w q x
  change ‖e x‖ = ‖x‖ at hnorm
  rw [hnorm]

end CompletionTransport
end
end

section
-- module Solutions.OAIQ244_DUKE.AlgebraicNumberTheory_Idele_Cohomology_SPlaces_OutsideIntegralInduced_LocalInduction_Equiv
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 400000
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalCyclotomicCompletionAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.CyclicCohomology.binaryCoefficientFamilyCommGroup _root_.LocalClassFieldTheory.normalizationIntegerRingIsIntegralClosure _root_.chosenFinitePlaceCompletionAlgebra _root_.chosenFinitePlaceCompletionContinuousSMul _root_.chosenFinitePlaceCompletionFiniteDimensional _root_.chosenFinitePlaceCompletionLocallyCompactSpace _root_.chosenFinitePlaceLocalizedFiniteDimensional _root_.chosenFinitePlaceLocalizedIntegerAlgebra _root_.chosenFinitePlaceLocalizedIntegerModuleFinite _root_.chosenFinitePlaceLocalizedIsGalois _root_.chosenFinitePlaceLocalizedIsIntegralClosure _root_.chosenFinitePlaceLocalizedIsNonarchimedeanLocalField _root_.chosenFinitePlaceLocalizedIsValuativeTopology _root_.chosenFinitePlaceLocalizedLocallyCompactSpace _root_.chosenFinitePlaceLocalizedValuationCompatible _root_.chosenFinitePlaceLocalizedValuationHasExtension _root_.chosenFinitePlaceLocalizedValuationIsNontrivial _root_.chosenFinitePlaceLocalizedValuativeRel _root_.chosenFinitePlaceLocalizedValuativeRelIsNontrivial _root_.chosenFinitePlaceLocalizedValued _root_.relativeUnrestrictedSPlaceFactorCommGroup
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

/-!
# Integral local induction equivalence

This leaf identifies the product of completed integer-unit groups with the
induced integer-unit module.
-/

open scoped NumberField TensorProduct ValuativeRel NNReal
open NumberField IsDedekindDomain

noncomputable section

open AlgebraicNumberTheory.Valuations
open HilbertRamification
open LocalClassFieldTheory
open LocalFieldTheory

variable
    {K : Type} {L : Type}
    [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]

section IntegralInduction

variable (vK : AbsoluteValue K ℝ) (hvK : vK.IsNontrivial)
    (hvKna : IsNonarchimedean (vK : K → ℝ))
    (w : AbsoluteValueExtension vK L)

/-- The product of all local integer-unit groups from the canonical local tensor decomposition, rewritten
as the induced integer-unit module at a chosen extension. -/
noncomputable def completionProductIntegerUnitsEquivInducedModule :
    letI := LocalInductionInternal.extensionCompletionAlgebra vK w
    letI : SMul K w.1.Completion :=
      LocalInductionInternal.extensionCompletionSMul vK w
    letI := LocalInductionInternal.completionAlgebra vK w
    letI : Valued vK.Completion ℝ≥0 :=
      LocalInductionInternal.baseValued vK hvKna
    letI : ValuativeRel vK.Completion :=
      LocalInductionInternal.baseValuativeRel vK hvKna
    letI : Valued (LocalizedCompletion vK w) ℝ≥0 :=
      LocalInductionInternal.localizedValued vK w hvKna
    letI : ValuativeRel (LocalizedCompletion vK w) :=
      LocalInductionInternal.localizedValuativeRel vK w hvKna
    letI := LocalInductionInternal.valuationHasExtension vK w hvKna
    letI := LocalInductionInternal.isIntegralClosure
      vK w hvK hvKna
    letI := decompositionGroupLocalizedIntegerUnitsAction
      (vK := vK) (hvK := hvK) (hvKna := hvKna) (w := w)
    (∀ w' : AbsoluteValueExtension vK L,
      (absoluteValueCompletionIntegers w'.1
        (absoluteValueExtension_isNonarchimedean
          vK hvKna w'))ˣ) ≃*
      CyclicCohomology.InducedModule
        (B := 𝒪[LocalizedCompletion vK w]ˣ)
        (absoluteValueDecompositionGroup K w.1) := by
  letI := LocalInductionInternal.extensionCompletionAlgebra vK w
  letI : SMul K w.1.Completion :=
    LocalInductionInternal.extensionCompletionSMul vK w
  letI := LocalInductionInternal.completionAlgebra vK w
  letI : Valued vK.Completion ℝ≥0 :=
    LocalInductionInternal.baseValued vK hvKna
  letI : ValuativeRel vK.Completion :=
    LocalInductionInternal.baseValuativeRel vK hvKna
  letI : Valued (LocalizedCompletion vK w) ℝ≥0 :=
    LocalInductionInternal.localizedValued vK w hvKna
  letI : ValuativeRel (LocalizedCompletion vK w) :=
    LocalInductionInternal.localizedValuativeRel vK w hvKna
  letI := LocalInductionInternal.valuationHasExtension vK w hvKna
  letI := LocalInductionInternal.isIntegralClosure
    vK w hvK hvKna
  letI := decompositionGroupLocalizedIntegerUnitsAction
    (vK := vK) (hvK := hvK) (hvKna := hvKna) (w := w)
  let reindex :=
    Equiv.piCongrLeft'
      (fun w' : AbsoluteValueExtension vK L =>
        (absoluteValueCompletionIntegers w'.1
          (absoluteValueExtension_isNonarchimedean
            vK hvKna w'))ˣ)
      (rightCosetExtensionEquiv vK hvK w).symm
  let reindexMul :
      (∀ w' : AbsoluteValueExtension vK L,
        (absoluteValueCompletionIntegers w'.1
          (absoluteValueExtension_isNonarchimedean
            vK hvKna w'))ˣ) ≃*
        (∀ q : InducedRightCosets
            (absoluteValueDecompositionGroup K w.1),
          (absoluteValueCompletionIntegers
            (rightCosetExtensionEquiv vK hvK w q).1
            (absoluteValueExtension_isNonarchimedean
              vK hvKna
              (rightCosetExtensionEquiv vK hvK w q)))ˣ) :=
    { reindex with
      map_mul' := by
        intro x y
        funext q
        rfl }
  exact
    reindexMul.trans
      ((MulEquiv.piCongrRight fun q :
          InducedRightCosets (absoluteValueDecompositionGroup K w.1) =>
        Units.mapEquiv
          (rightCosetCompletionIntegersRingEquivLocalized
            vK hvK w hvKna q).toMulEquiv).trans
        (inducedRightCosetCoordinates
          (absoluteValueDecompositionGroup K w.1)).symm)

end IntegralInduction
end
end

section
-- module Solutions.OAIQ244_DUKE.AlgebraicNumberTheory_Idele_Cohomology_SPlaces_OutsideIntegralInduced_LocalInduction_Inclusion
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 400000
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalCyclotomicCompletionAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.residueFieldZModAlgebra _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.LubinTate.compatibleGroupFamiliesGroup _root_.OAI.PrimeDegreePackets.diagonalLogAction _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.CyclicCohomology.binaryCoefficientFamilyCommGroup _root_.LocalClassFieldTheory.normalizationIntegerRingIsIntegralClosure _root_.chosenFinitePlaceCompletionAlgebra _root_.chosenFinitePlaceCompletionContinuousSMul _root_.chosenFinitePlaceCompletionFiniteDimensional _root_.chosenFinitePlaceCompletionLocallyCompactSpace _root_.chosenFinitePlaceLocalizedFiniteDimensional _root_.chosenFinitePlaceLocalizedIntegerAlgebra _root_.chosenFinitePlaceLocalizedIntegerModuleFinite _root_.chosenFinitePlaceLocalizedIsGalois _root_.chosenFinitePlaceLocalizedIsIntegralClosure _root_.chosenFinitePlaceLocalizedIsNonarchimedeanLocalField _root_.chosenFinitePlaceLocalizedIsValuativeTopology _root_.chosenFinitePlaceLocalizedLocallyCompactSpace _root_.chosenFinitePlaceLocalizedValuationCompatible _root_.chosenFinitePlaceLocalizedValuationHasExtension _root_.chosenFinitePlaceLocalizedValuationIsNontrivial _root_.chosenFinitePlaceLocalizedValuativeRel _root_.chosenFinitePlaceLocalizedValuativeRelIsNontrivial _root_.chosenFinitePlaceLocalizedValued _root_.relativeUnrestrictedSPlaceFactorCommGroup
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

/-!
# Inclusion of integral local induced modules

This leaf embeds the induced integer-unit module into the ordinary local
multiplicative induced block and proves injectivity.
-/

open scoped NumberField TensorProduct ValuativeRel NNReal
open NumberField IsDedekindDomain

noncomputable section

open AlgebraicNumberTheory.Valuations
open HilbertRamification
open LocalClassFieldTheory
open LocalFieldTheory

variable
    {K : Type} {L : Type}
    [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]

section IntegralInduction

variable (vK : AbsoluteValue K ℝ) (hvK : vK.IsNontrivial)
    (hvKna : IsNonarchimedean (vK : K → ℝ))
    (w : AbsoluteValueExtension vK L)

/-- Pointwise inclusion of integer units embeds the integral induced
block into the ordinary local multiplicative induced block. -/
noncomputable def inducedIntegerUnitsToLocalPlaceBlock :
    letI := LocalInductionInternal.extensionCompletionAlgebra vK w
    letI : SMul K w.1.Completion :=
      LocalInductionInternal.extensionCompletionSMul vK w
    letI := LocalInductionInternal.completionAlgebra vK w
    letI : Valued vK.Completion ℝ≥0 :=
      LocalInductionInternal.baseValued vK hvKna
    letI : ValuativeRel vK.Completion :=
      LocalInductionInternal.baseValuativeRel vK hvKna
    letI : Valued (LocalizedCompletion vK w) ℝ≥0 :=
      LocalInductionInternal.localizedValued vK w hvKna
    letI : ValuativeRel (LocalizedCompletion vK w) :=
      LocalInductionInternal.localizedValuativeRel vK w hvKna
    letI : Algebra 𝒪[vK.Completion] (LocalizedCompletion vK w) :=
      LocalInductionInternal.integerAlgebra vK w hvKna
    letI := LocalInductionInternal.valuationHasExtension vK w hvKna
    letI := LocalInductionInternal.isIntegralClosure
      vK w hvK hvKna
    letI := decompositionGroupLocalizedIntegerUnitsAction
      (vK := vK) (hvK := hvK) (hvKna := hvKna) (w := w)
    CyclicCohomology.InducedModule
          (B := 𝒪[LocalizedCompletion vK w]ˣ)
          (absoluteValueDecompositionGroup K w.1) →*
      LocalPlaceBlock vK hvK w := by
  letI := LocalInductionInternal.extensionCompletionAlgebra vK w
  letI : SMul K w.1.Completion :=
    LocalInductionInternal.extensionCompletionSMul vK w
  letI := LocalInductionInternal.completionAlgebra vK w
  letI : Valued vK.Completion ℝ≥0 :=
    LocalInductionInternal.baseValued vK hvKna
  letI : ValuativeRel vK.Completion :=
    LocalInductionInternal.baseValuativeRel vK hvKna
  letI : Valued (LocalizedCompletion vK w) ℝ≥0 :=
    LocalInductionInternal.localizedValued vK w hvKna
  letI : ValuativeRel (LocalizedCompletion vK w) :=
    LocalInductionInternal.localizedValuativeRel vK w hvKna
  letI : Algebra 𝒪[vK.Completion] (LocalizedCompletion vK w) :=
    LocalInductionInternal.integerAlgebra vK w hvKna
  letI := LocalInductionInternal.valuationHasExtension vK w hvKna
  letI := LocalInductionInternal.isIntegralClosure
    vK w hvK hvKna
  letI := decompositionGroupLocalizedIntegerUnitsAction
    (vK := vK) (hvK := hvK) (hvKna := hvKna) (w := w)
  letI := decompositionGroupLocalUnitsAction vK hvK w
  refine
    { toFun := fun f =>
        ⟨fun g =>
            LocalFieldTheory.IsNonarchimedeanLocalField.integerUnitsToFieldUnits
              (LocalizedCompletion vK w) (f.1 g),
          by
            intro h g
            change
              LocalFieldTheory.IsNonarchimedeanLocalField.integerUnitsToFieldUnits
                    (LocalizedCompletion vK w) (f.1 (h.1 * g)) =
                h •
                  LocalFieldTheory.IsNonarchimedeanLocalField.integerUnitsToFieldUnits
                    (LocalizedCompletion vK w) (f.1 g)
            rw [f.2 h g]
            let : MulDistribMulAction
                (Gal(LocalizedCompletion vK w / vK.Completion))
                𝒪[LocalizedCompletion vK w]ˣ :=
              galoisGroupIntegerUnitsMulDistribMulActionOfIsIntegralClosure
                vK.Completion (LocalizedCompletion vK w)
            let : MulDistribMulAction
                (Gal(LocalizedCompletion vK w / vK.Completion))
                (LocalizedCompletion vK w)ˣ :=
              galoisGroupFieldUnitsMulDistribMulAction
                vK.Completion (LocalizedCompletion vK w)
            exact
              integerUnitsToFieldUnits_galoisGroup_equivariant
                vK.Completion (LocalizedCompletion vK w)
                (decompositionGroupEquivAlgebraicLocalizationAut
                  vK hvK w h)
                (f.1 g)⟩
      map_one' := by
        apply Subtype.ext
        funext g
        rfl
      map_mul' := fun f₁ f₂ ↦ by
        apply Subtype.ext
        funext g
        rfl }

omit [NumberField K] [NumberField L] in
/-- The map from induced localized integer units to the corresponding
local-place block is injective. -/
theorem inducedIntegerUnitsToLocalPlaceBlock_injective :
    letI := LocalInductionInternal.extensionCompletionAlgebra vK w
    letI : SMul K w.1.Completion :=
      LocalInductionInternal.extensionCompletionSMul vK w
    letI := LocalInductionInternal.completionAlgebra vK w
    letI : Valued vK.Completion ℝ≥0 :=
      LocalInductionInternal.baseValued vK hvKna
    letI : ValuativeRel vK.Completion :=
      LocalInductionInternal.baseValuativeRel vK hvKna
    letI : Valued (LocalizedCompletion vK w) ℝ≥0 :=
      LocalInductionInternal.localizedValued vK w hvKna
    letI : ValuativeRel (LocalizedCompletion vK w) :=
      LocalInductionInternal.localizedValuativeRel vK w hvKna
    letI : Algebra 𝒪[vK.Completion] (LocalizedCompletion vK w) :=
      LocalInductionInternal.integerAlgebra vK w hvKna
    letI := LocalInductionInternal.valuationHasExtension vK w hvKna
    letI := LocalInductionInternal.isIntegralClosure
      vK w hvK hvKna
    letI := decompositionGroupLocalizedIntegerUnitsAction
      (vK := vK) (hvK := hvK) (hvKna := hvKna) (w := w)
    Function.Injective
      (inducedIntegerUnitsToLocalPlaceBlock
        (K := K) (L := L) vK hvK hvKna w) := by
  let := LocalInductionInternal.extensionCompletionAlgebra vK w
  let : SMul K w.1.Completion :=
    LocalInductionInternal.extensionCompletionSMul vK w
  let := LocalInductionInternal.completionAlgebra vK w
  let : Valued vK.Completion ℝ≥0 :=
    LocalInductionInternal.baseValued vK hvKna
  let : ValuativeRel vK.Completion :=
    LocalInductionInternal.baseValuativeRel vK hvKna
  let : Valued (LocalizedCompletion vK w) ℝ≥0 :=
    LocalInductionInternal.localizedValued vK w hvKna
  let : ValuativeRel (LocalizedCompletion vK w) :=
    LocalInductionInternal.localizedValuativeRel vK w hvKna
  let : Algebra 𝒪[vK.Completion] (LocalizedCompletion vK w) :=
    LocalInductionInternal.integerAlgebra vK w hvKna
  let := LocalInductionInternal.valuationHasExtension vK w hvKna
  let := LocalInductionInternal.isIntegralClosure
    vK w hvK hvKna
  let := decompositionGroupLocalizedIntegerUnitsAction
    (vK := vK) (hvK := hvK) (hvKna := hvKna) (w := w)
  intro f₁ f₂ h
  apply Subtype.ext
  funext g
  apply
    LocalFieldTheory.IsNonarchimedeanLocalField.integerUnitsToFieldUnits_injective
      (LocalizedCompletion vK w)
  exact congrArg
    (fun z : LocalPlaceBlock vK hvK w => z.1 g) h


end IntegralInduction
end
end

section
-- module Solutions.OAIQ244_DUKE.AlgebraicNumberTheory_Idele_Cohomology_SPlaces_OutsideIntegralInduced_ChosenPlaceAction
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalCyclotomicCompletionAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.residueFieldZModAlgebra _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.LubinTate.compatibleGroupFamiliesGroup _root_.OAI.PrimeDegreePackets.diagonalLogAction _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.LocalClassFieldTheory.normalizationIntegerRingIsIntegralClosure
attribute [-simp] _root_.GlobalClassFieldTheory.Reciprocity.rationalCyclotomicGlobalToLocalizedAlgHom_apply _root_.GlobalClassFieldTheory.Reciprocity.rationalCyclotomicGlobalToLocalizedAlgHom_primitiveRoot _root_.IsDiscreteValuationRing.addVal_ringEquiv _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.OAI.PrimeDegreePackets.ThetaConstruction.schwartzCM_apply _root_.doubleCosetExtension_mk _root_.extendAbsoluteValueExtensionFromIntermediate_apply _root_.finitePlaceBelow_finitePlaceExtensionCentre _root_.finitePlaceExtensionAdicCompletionRingEquiv_toCompletion _root_.finitePlaceExtensionCentreInFibre_coe _root_.finitePlaceExtensionCentre_asIdeal _root_.finitePlaceExtensionCompletionRingEquiv_toCompletion _root_.finitePlaceExtensionEquivAbove_coe _root_.finitePlaceIdealResidueEquivCompletion_apply_mk _root_.finitePlaceIntegerToCompletion_coe _root_.finitePlaceTensorRingEquivAboveAdic_apply_extension _root_.finitePlaceTensorUnitsEquivAboveAdic_apply_extension _root_.infinitePlaceAboveEquivExtension_apply_val _root_.infinitePlaceTensorRingEquivAbove_apply _root_.infinitePlaceTensorUnitsEquivAbove_apply _root_.infinitePlace_mult_smul _root_.mem_finitePlaceDecompositionGroup_iff _root_.restrictAbsoluteValueExtensionToIntermediate_apply _root_.ringOfIntegersToFinitePlaceExtensionValuationSubring_coe
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
/-- On the actual chosen localization, the decomposition-group action on
integer units is the pullback of the local Galois action along the canonical
decomposition equivalence. Both sides are evaluated with the valued-field
and integral-closure data used by `LocalInduction`. -/
theorem
    chosenFinitePlaceDecompositionGroupIntegerUnitsAction_smul_eq_pullback
    (w₀ : HeightOneSpectrum (𝓞 K)) :
    let vK := HeightOneSpectrum.adicAbv K w₀
    let w := chosenFinitePlaceExtension (L := L) w₀
    let E := ChosenFinitePlaceLocalizedCompletion
      (K := K) (L := L) w₀
    let eLocal :=
      decompositionGroupEquivAlgebraicLocalizationAut
        vK
        (RayClass.adicAbv_isNontrivial w₀)
        w
    letI : MulDistribMulAction
        (Gal(E / vK.Completion)) 𝒪[E]ˣ :=
      galoisGroupIntegerUnitsMulDistribMulActionOfIsIntegralClosure
        vK.Completion E
    ∀ (σ : absoluteValueDecompositionGroup K w.1)
      (x : 𝒪[E]ˣ),
      (chosenFinitePlaceDecompositionGroupIntegerUnitsAction
        (K := K) (L := L) w₀).smul σ x =
        (MulDistribMulAction.compHom
          𝒪[E]ˣ eLocal.toMonoidHom).smul σ x := by
  unfold chosenFinitePlaceDecompositionGroupIntegerUnitsAction
  dsimp
  intro σ x
  rfl

end ChosenFinitePlace
end
end

section
-- module Solutions.OAIQ244_DUKE.AlgebraicNumberTheory_Idele_Cohomology_SPlaces_OutsideIntegralInduced_ChosenPlaceIntegralBlockInclusion
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 400000
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalCyclotomicCompletionAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.residueFieldZModAlgebra _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.LubinTate.compatibleGroupFamiliesGroup _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.CyclicCohomology.binaryCoefficientFamilyCommGroup _root_.LocalClassFieldTheory.normalizationIntegerRingIsIntegralClosure _root_.relativeUnrestrictedSPlaceFactorCommGroup
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

/-!
# Inclusion of the chosen integral induced block

This file embeds the chosen induced module of local integer units into the
ordinary local multiplicative block and proves injectivity.
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

/-- Inclusion of the chosen integral block into the ordinary chosen
local multiplicative block. -/
noncomputable def chosenFinitePlaceIntegralInducedBlockToLocalPlaceBlock
    (w₀ : HeightOneSpectrum (𝓞 K)) :
    ChosenFinitePlaceInducedIntegerUnits
        (K := K) (L := L) w₀ →
      ChosenFinitePlaceLocalPlaceBlock
        (K := K) (L := L) w₀ :=
  by
    letI : MulDistribMulAction
        (absoluteValueDecompositionGroup K
          (chosenFinitePlaceExtension (L := L) w₀).1)
        𝒪[ChosenFinitePlaceLocalizedCompletion
          (K := K) (L := L) w₀]ˣ :=
      chosenFinitePlaceDecompositionGroupIntegerUnitsAction
        (K := K) (L := L) w₀
    change
      InducedModule
          (B := ChosenFinitePlaceLocalizedIntegerUnits
            (K := K) (L := L) w₀)
          (ChosenFinitePlaceDecompositionGroup
            (K := K) (L := L) w₀) →
        ChosenFinitePlaceLocalPlaceBlock
          (K := K) (L := L) w₀
    exact
      (inducedIntegerUnitsToLocalPlaceBlock
          (HeightOneSpectrum.adicAbv K w₀)
          (RayClass.adicAbv_isNontrivial w₀)
          (HeightOneSpectrum.isNonarchimedean_adicAbv K w₀)
          (chosenFinitePlaceExtension (L := L) w₀)).toFun

omit [NumberField L] in
/-- The chosen finite-place integral induced block embeds into its
unrestricted local-place block. -/
theorem chosenFinitePlaceIntegralInducedBlockToLocalPlaceBlock_injective
    (w₀ : HeightOneSpectrum (𝓞 K)) :
    Function.Injective
      (chosenFinitePlaceIntegralInducedBlockToLocalPlaceBlock
        (K := K) (L := L) w₀) := by
  let vK := HeightOneSpectrum.adicAbv K w₀
  let u := chosenFinitePlaceExtension (L := L) w₀
  let hvK : vK.IsNontrivial := RayClass.adicAbv_isNontrivial w₀
  let hvKna : IsNonarchimedean (vK : K → ℝ) :=
    HeightOneSpectrum.isNonarchimedean_adicAbv K w₀
  unfold chosenFinitePlaceIntegralInducedBlockToLocalPlaceBlock
  exact inducedIntegerUnitsToLocalPlaceBlock_injective
    vK hvK hvKna u
end ChosenFinitePlace
end
end

section
-- module Solutions.OAIQ244_DUKE.AlgebraicNumberTheory_Idele_Relative_SPlaces
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.DiscreteNthRootsSubgroup.instCommGroupSubtypeUnitsMemSubgroup _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.residueFieldZModAlgebra _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.LubinTate.compatibleGroupFamiliesCommGroup _root_.LubinTate.compatibleGroupFamiliesGroup _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.CyclicCohomology.binaryCoefficientFamilyCommGroup _root_.CyclicCohomology.instMulDistribMulActionBinaryCoefficientFamily _root_.LocalClassFieldTheory.normalizationIntegerRingIsIntegralClosure _root_.chosenFinitePlaceCompletionAlgebra _root_.relativeUnrestrictedSPlaceFactorCommGroup
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

/-!
# Finite-place support for relative ideles

This file packages a restricted-product assertion for relative ideles. At
every finite place outside a finite
set, a relative idele belongs to the actual product of valuation-ring
unit groups supplied by the completion decomposition. The resulting supported
subgroups are stable under the Galois action and exhaust the full
relative idele group.
-/

open scoped NumberField TensorProduct
open NumberField IsDedekindDomain

noncomputable section

open CyclicCohomology


open AlgebraicNumberTheory.Valuations

universe u v

variable
    {K : Type u} {L : Type v}
    [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]

/-- Coordinatewise Galois action on the complete local-factor model. -/
@[reducible]
noncomputable def relativeIdeleSPlaceFactorsAction
    (S : Finset (HeightOneSpectrum (𝓞 K))) :
    MulDistribMulAction
      (L ≃ₐ[K] L)
      (RelativeIdeleSPlaceFactors
        (K := K) (L := L) S) := by
  letI : ∀ w : InfinitePlace K,
      MulDistribMulAction
        (L ≃ₐ[K] L) (w.Completion ⊗[K] L)ˣ :=
    fun w =>
      scalarTensorUnitsAction
        (K := K) (L := L) (A := w.Completion)
  letI : MulDistribMulAction
      (L ≃ₐ[K] L)
      (∀ w : InfinitePlace K,
        (w.Completion ⊗[K] L)ˣ) :=
    piMulDistribMulAction
      (L ≃ₐ[K] L)
      (fun w : InfinitePlace K =>
        (w.Completion ⊗[K] L)ˣ)
  letI : ∀ w :
      {w : HeightOneSpectrum (𝓞 K) // w ∈ S},
      MulDistribMulAction
        (L ≃ₐ[K] L)
        (w.1.adicCompletion K ⊗[K] L)ˣ :=
    fun w =>
      scalarTensorUnitsAction
        (K := K) (L := L)
        (A := w.1.adicCompletion K)
  letI : MulDistribMulAction
      (L ≃ₐ[K] L)
      (∀ w : {w : HeightOneSpectrum (𝓞 K) // w ∈ S},
        (w.1.adicCompletion K ⊗[K] L)ˣ) :=
    piMulDistribMulAction
      (L ≃ₐ[K] L)
      (fun w :
        {w : HeightOneSpectrum (𝓞 K) // w ∈ S} =>
          (w.1.adicCompletion K ⊗[K] L)ˣ)
  letI : ∀ w :
      {w : HeightOneSpectrum (𝓞 K) // w ∉ S},
      MulDistribMulAction
        (L ≃ₐ[K] L)
        (relativeLocalTensorDecompositionIntegralUnitSubgroup
          (K := K) (L := L) w.1) :=
    fun w =>
      relativeLocalTensorDecompositionIntegralUnitSubgroupAction
        (K := K) (L := L) w.1
  letI : MulDistribMulAction
      (L ≃ₐ[K] L)
      (∀ w : {w : HeightOneSpectrum (𝓞 K) // w ∉ S},
        relativeLocalTensorDecompositionIntegralUnitSubgroup
          (K := K) (L := L) w.1) :=
    piMulDistribMulAction
      (L ≃ₐ[K] L)
      (fun w :
        {w : HeightOneSpectrum (𝓞 K) // w ∉ S} =>
          relativeLocalTensorDecompositionIntegralUnitSubgroup
            (K := K) (L := L) w.1)
  exact inferInstance
end
end

section
-- module Solutions.OAIQ244_DUKE.AlgebraicNumberTheory_Idele_Cohomology_SPlaces_Reassociation
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 400000
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.DiscreteNthRootsSubgroup.instCommGroupSubtypeUnitsMemSubgroup _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.residueFieldZModAlgebra _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.LubinTate.compatibleGroupFamiliesCommGroup _root_.LubinTate.compatibleGroupFamiliesGroup _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.LocalClassFieldTheory.normalizationIntegerRingIsIntegralClosure _root_.chosenFinitePlaceCompletionAlgebra
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

/-!
# Reassociation of supported relative-idele factors

The factor model of a supported relative idele is reassociated into the
finite family of unrestricted places and the product of integral factors
outside the support.  The comparison respects the concrete Galois
actions.
-/

open scoped NumberField
open NumberField IsDedekindDomain

noncomputable section


open CyclicCohomology.ProfiniteCohomology.Herbrand
open CyclicCohomology

variable
    {K L : Type}
    [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]

/-- The product of the actual integral tensor-unit factors outside
`S`. -/
abbrev RelativeOutsideSPlaceFactors
    (S : Finset (HeightOneSpectrum (𝓞 K))) :=
  ∀ w : {w : HeightOneSpectrum (𝓞 K) // w ∉ S},
    relativeLocalTensorDecompositionIntegralUnitSubgroup
      (K := K) (L := L) w.1

/-- The componentwise Galois action on the integral factors outside
`S`. -/
@[reducible]
noncomputable def relativeOutsideSPlaceFactorsAction
    (S : Finset (HeightOneSpectrum (𝓞 K))) :
    MulDistribMulAction (L ≃ₐ[K] L)
      (RelativeOutsideSPlaceFactors
        (K := K) (L := L) S) := by
  letI : ∀ w :
      {w : HeightOneSpectrum (𝓞 K) // w ∉ S},
      MulDistribMulAction (L ≃ₐ[K] L)
        (relativeLocalTensorDecompositionIntegralUnitSubgroup
          (K := K) (L := L) w.1) :=
    fun w =>
      relativeLocalTensorDecompositionIntegralUnitSubgroupAction
        (K := K) (L := L) w.1
  exact
    piMulDistribMulAction
      (L ≃ₐ[K] L)
      (fun w :
        {w : HeightOneSpectrum (𝓞 K) // w ∉ S} =>
          relativeLocalTensorDecompositionIntegralUnitSubgroup
            (K := K) (L := L) w.1)

/-- The componentwise Galois action on the product of unrestricted and
outside-integral local factors. -/
@[reducible]
noncomputable def relativeUnrestrictedProdOutsideAction
    (S : Finset (HeightOneSpectrum (𝓞 K))) :
    MulDistribMulAction (L ≃ₐ[K] L)
      (RelativeUnrestrictedSPlaceFactors
          (K := K) (L := L) S ×
        RelativeOutsideSPlaceFactors
          (K := K) (L := L) S) := by
  letI :=
    relativeUnrestrictedSPlaceFactorsAction
      (K := K) (L := L) S
  letI :=
    relativeOutsideSPlaceFactorsAction
      (K := K) (L := L) S
  infer_instance

/-- Reassociate all supported local factors as
`(unrestricted factors) × (outside integral factors)`. -/
noncomputable def
    relativeIdeleSPlaceFactorsEquivUnrestrictedProdOutside
    (S : Finset (HeightOneSpectrum (𝓞 K))) :
    RelativeIdeleSPlaceFactors (K := K) (L := L) S ≃*
      RelativeUnrestrictedSPlaceFactors
          (K := K) (L := L) S ×
        RelativeOutsideSPlaceFactors
          (K := K) (L := L) S where
  toFun z :=
    ⟨fun i =>
      match i with
      | Sum.inl w => z.1 w
      | Sum.inr w => z.2.1 w,
      z.2.2⟩
  invFun z :=
    ⟨fun w => z.1 (Sum.inl w),
      ⟨fun w => z.1 (Sum.inr w), z.2⟩⟩
  left_inv _ := rfl
  right_inv z := by
    apply Prod.ext
    · funext i
      cases i <;> rfl
    · rfl
  map_mul' x y := by
    apply Prod.ext
    · funext i
      cases i <;> rfl
    · rfl
end
end

section
-- module Solutions.OAIQ244_DUKE.KummerTheory_Concrete_SUnitPreparation_FiniteRadicalSupport
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.ValuationTheory.DiscreteValuationField.DVF.maximalIdealPowSuccQuotModule _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.isDomain _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.LocalClassFieldTheory.normalizationIntegerRingIsIntegralClosure _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

/-!
# Finite support for Kummer radicals

A chosen finite enlargement of places containing representatives of every class in a finite Kummer radical.
-/

open scoped NumberField Classical IsMulCommutative NNReal ValuativeRel
open NumberField IsDedekindDomain
open LocalFieldTheory

noncomputable section

namespace KummerTheory

variable {K : Type*} [Field K]
    [numberFieldK : NumberField K]

/-- The radical-support enlargement contains its starting set. -/
theorem subset_enlargeByFiniteKummerRadicalSupport
    {L : Type*} [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    (n : ℕ+)
    (hmu : (primitiveRoots (n : ℕ) K).Nonempty)
    (S : Finset (HeightOneSpectrum (𝓞 K))) :
    S ⊆ enlargeByFiniteKummerRadicalSupport
      (K := K) (L := L) n hmu S :=
  Finset.subset_union_left

end KummerTheory
end
end


