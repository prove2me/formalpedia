-- Prove2me | Definitions.Def_OAIQ244Duke058
-- name    : OAIQ244Duke058
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-13T22:15:00.600917+00:00
-- url     : https://prove2.me/theorems/93262abc-fe85-4781-94fa-a99008963c81
-- title:
--   Definitions bundle OAIQ244Duke058 of the split of OpenAI, Equidistribution of Prime-Degree Torus Packets with Arbitrary Local Type
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.DukePrimeDegree.prime_degree_packet_measure_equidistribution_unconditional` and `OAI.DukePrimeDegree.prime_degree_packet_measures_tendsto_haar_unconditional`, carved from OpenAI's openai/math development (OpenAI, *Equidistribution of Prime-Degree Torus Packets with Arbitrary Local Type*, OpenAI Math Release, September 24, 2026, result family 15, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 29 declarations of OpenAI's Lean: 7 definitions and 22 theorems. The definitions and types are `KummerTheory.sUnitLocalPowerKernelNthPowers`, `LocalClassFieldTheory.localHerbrandH0EquivNormQuotient`, `chosenFinitePlaceCompletionIntegralUniformizer`, `relativeIdeleSupportedEquivSPlaceFactors`, `relativeUnrestrictedSPlaceFactorsEquivLocalBlockFamily`, `relativeUnrestrictedSPlaceFactorsHerbrandH0EquivLocalBlockFamily`, `relativeUnrestrictedSPlaceFactorsHerbrandHMinusOneEquivLocalBlockFamily`.
--
--   **Sources.** They come from these modules of lean/OAI/NumberTheory, in whole or in part: `AlgebraicNumberTheory_Completion_UnramifiedComparison_IdealToCompletion`, `AlgebraicNumberTheory_Idele_Cohomology_SPlaces_Herbrand_Factors`, `AlgebraicNumberTheory_Idele_Cohomology_SPlaces_Herbrand_FamilyCardinality`, `AlgebraicNumberTheory_Idele_Cohomology_SPlaces_Herbrand_FamilyFinite`, `AlgebraicNumberTheory_Idele_Cohomology_SPlaces_Herbrand_Local`, `AlgebraicNumberTheory_Idele_Cohomology_SPlaces_LocalBlocks`, `AlgebraicNumberTheory_Idele_Cohomology_SPlaces_OutsideIntegralInduced_ChosenPlaceIntegralBlockTensorSmul`, `AlgebraicNumberTheory_Idele_Relative_SPlaces`, `AlgebraicNumberTheory_Ramification_Splitting_FinitePlaceIdeal`, `AlgebraicNumberTheory_Ramification_Splitting_NormalClosure`, `GlobalClassFieldTheory_ClassFieldAxiom_SUnitKummerPrimeSelection_FinitePlaceDecomposition`, `KummerTheory_Concrete_SUnitPreparation_SUnitLocalPowerKernel`, `LocalClassFieldTheory_ClassFormation_ArchimedeanNormQuotient`, `LocalClassFieldTheory_ClassFormation_LocalizedCompletionCohomology_Cardinality_H0`, `LocalClassFieldTheory_ClassFormation_LocalizedCompletionCohomology_Cardinality_HMinusOne`, `LocalClassFieldTheory_ClassFormation_LocalizedCompletionCohomology_Finite`, `LocalClassFieldTheory_ClassFormation_LocalizedCompletionCohomology_HerbrandEquiv`.
--
--   **Imports.** It imports the bundles `OAIQ244Duke046`, `OAIQ244Duke047`, `OAIQ244Duke048`, `OAIQ244Duke049` and `OAIQ244Duke050` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ244Duke063`, `OAIQ244Duke064` and `OAIQ244Duke068`.
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
import Mathlib.NumberTheory.NumberField.Cyclotomic.Basic
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
import Definitions.Def_OAIQ244Duke047
import Definitions.Def_OAIQ244Duke048
import Definitions.Def_OAIQ244Duke049
import Definitions.Def_OAIQ244Duke050

section
-- module Solutions.OAIQ244_DUKE.LocalClassFieldTheory_ClassFormation_LocalizedCompletionCohomology_HerbrandEquiv
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalCyclotomicCompletionAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalClassFieldTheory.localDecompositionResidueFinite _root_.LocalClassFieldTheory.localDecompositionResidueFintype _root_.LocalClassFieldTheory.realComplexNormQuotientFinite _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitQuotientCarrier_finite _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.residueFieldZModAlgebra _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedIntegralAlgebraContextValuationSubringAlgebra _root_.LocalFieldTheory.DiscreteValuationField.finite_nsmulAddKernel_padicInt_pi _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_multiplicative_nthPowerKernel _root_.LocalFieldTheory.finite_nsmulAddKernel_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.LubinTate.compatibleGroupFamiliesGroup _root_.OAI.PrimeDegreePackets.boundedRealFields_finite _root_.OAI.PrimeDegreePackets.diagonalLogAction _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionResidueField.instField _root_.RamificationTheory.HilbertRamification.ValuationSubring.selectedResidueField.instAlgebra _root_.RayClass.approximationCompletionTopologicalSpace _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.RelativeIdeleGroup.relativeIdeleMulAction _root_.CyclicCohomology.binaryCoefficientFamilyCommGroup _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.LocalClassFieldTheory.normalizationIntegerRingIsIntegralClosure _root_.adicCompletionProperSpace _root_.chosenFinitePlaceCompletionAlgebra _root_.chosenFinitePlaceCompletionContinuousSMul _root_.chosenFinitePlaceCompletionFiniteDimensional _root_.chosenFinitePlaceCompletionLocallyCompactSpace _root_.chosenFinitePlaceLocalizedFiniteDimensional _root_.chosenFinitePlaceLocalizedIntegerAlgebra _root_.chosenFinitePlaceLocalizedIntegerModuleFinite _root_.chosenFinitePlaceLocalizedIsGalois _root_.chosenFinitePlaceLocalizedIsIntegralClosure _root_.chosenFinitePlaceLocalizedIsNonarchimedeanLocalField _root_.chosenFinitePlaceLocalizedIsValuativeTopology _root_.chosenFinitePlaceLocalizedLocallyCompactSpace _root_.chosenFinitePlaceLocalizedValuationCompatible _root_.chosenFinitePlaceLocalizedValuationHasExtension _root_.chosenFinitePlaceLocalizedValuationIsNontrivial _root_.chosenFinitePlaceLocalizedValuativeRel _root_.chosenFinitePlaceLocalizedValuativeRelIsNontrivial _root_.chosenFinitePlaceLocalizedValued _root_.finiteLocalUnitsOpen _root_.relativeAdeleRingIntermediateAlgebra _root_.relativeAdeleRingTopIntermediateAlgebra _root_.relativeUnrestrictedSPlaceFactorCommGroup
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

/-!
# Low-degree Herbrand equivalences for a localized completion
-/

open AlgebraicNumberTheory.Valuations
open HilbertRamification
open LocalClassFieldTheory
open LocalFieldTheory
open CyclicCohomology
open CyclicCohomology.ProfiniteCohomology.Herbrand
open scoped TensorProduct

noncomputable section

namespace LocalClassFieldTheory

section LocalTateComparison

variable {k ell : Type}
    [Field k] [Field ell] [Algebra k ell]
    [FiniteDimensional k ell] [IsGalois k ell]

/-- Degree-zero Herbrand cohomology for a decomposition group identified with
the norm quotient of the localized field extension. -/
noncomputable def localHerbrandH0EquivNormQuotient
    (vK : AbsoluteValue k ℝ) (hvK : vK.IsNontrivial)
    (w : AbsoluteValueExtension vK ell) :
    letI hK :=
      AbsoluteValue.extensionCompletionAlgebra
        (K := k) w.1
    letI : SMul k w.1.Completion := hK.toSMul
    letI : Algebra vK.Completion w.1.Completion :=
      AbsoluteValue.completionAlgebra vK w.1 w.2
    letI := localizedCompletionGlobalAlgebra vK w
    letI := localizedCompletionIsScalarTower vK w
    letI : FiniteDimensional vK.Completion
        (LocalizedCompletion vK w) :=
      localizedCompletionModuleFinite vK hvK w
    letI : IsGalois vK.Completion
        (LocalizedCompletion vK w) :=
      HilbertRamification.algebraicLocalization_isGalois vK w
    letI : Fintype (absoluteValueDecompositionGroup k w.1) :=
      Fintype.ofFinite _
    letI :=
      decompositionGroupLocalUnitsAction vK hvK w
    HerbrandH0 (absoluteValueDecompositionGroup k w.1)
        (LocalizedCompletion vK w)ˣ ≃*
      NormQuotient vK.Completion
        (LocalizedCompletion vK w) := by
  letI := localizedCompletionBaseAlgebra vK w
  letI := localizedCompletionGlobalAlgebra vK w
  letI := localizedCompletionIsScalarTower vK w
  letI : FiniteDimensional vK.Completion
      (LocalizedCompletion vK w) :=
    localizedCompletionFiniteDimensional vK hvK w
  letI : IsGalois vK.Completion
      (LocalizedCompletion vK w) :=
    localizedCompletionIsGalois vK w
  letI := localizedCompletionDecompositionGroupFintype vK w
  let e0 :=
    localHerbrandH0EquivUnitsTateH0 vK hvK w
  let eAdd :
      tateCohomology
          (Rep.ofAlgebraAutOnUnits vK.Completion
            (LocalizedCompletion vK w)) 0 ≃+
        Additive
          (NormQuotient vK.Completion
            (LocalizedCompletion vK w)) :=
    (H0TateUnitsIsoNormQuotient
      vK.Completion
      (LocalizedCompletion vK w)).toLinearEquiv.toAddEquiv
  exact e0.trans <|
    eAdd.toMultiplicative.trans <|
      MulEquiv.multiplicativeAdditive
        (NormQuotient vK.Completion
          (LocalizedCompletion vK w))


end LocalTateComparison

end LocalClassFieldTheory
end
end

section
-- module Solutions.OAIQ244_DUKE.LocalClassFieldTheory_ClassFormation_LocalizedCompletionCohomology_Finite
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 400000
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalCyclotomicCompletionAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalClassFieldTheory.localDecompositionResidueFinite _root_.LocalClassFieldTheory.localDecompositionResidueFintype _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitQuotientCarrier_finite _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.residueFieldZModAlgebra _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedIntegralAlgebraContextValuationSubringAlgebra _root_.LocalFieldTheory.DiscreteValuationField.finite_nsmulAddKernel_padicInt_pi _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_multiplicative_nthPowerKernel _root_.LocalFieldTheory.finite_nsmulAddKernel_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.LubinTate.compatibleGroupFamiliesGroup _root_.OAI.PrimeDegreePackets.boundedRealFields_finite _root_.OAI.PrimeDegreePackets.diagonalLogAction _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionResidueField.instField _root_.RamificationTheory.HilbertRamification.ValuationSubring.selectedResidueField.instAlgebra _root_.RayClass.approximationCompletionTopologicalSpace _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.RelativeIdeleGroup.relativeIdeleMulAction _root_.CyclicCohomology.binaryCoefficientFamilyCommGroup _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.LocalClassFieldTheory.normalizationIntegerRingIsIntegralClosure _root_.adicCompletionProperSpace _root_.chosenFinitePlaceCompletionAlgebra _root_.chosenFinitePlaceCompletionContinuousSMul _root_.chosenFinitePlaceCompletionFiniteDimensional _root_.chosenFinitePlaceCompletionLocallyCompactSpace _root_.chosenFinitePlaceLocalizedFiniteDimensional _root_.chosenFinitePlaceLocalizedIntegerAlgebra _root_.chosenFinitePlaceLocalizedIntegerModuleFinite _root_.chosenFinitePlaceLocalizedIsGalois _root_.chosenFinitePlaceLocalizedIsIntegralClosure _root_.chosenFinitePlaceLocalizedIsNonarchimedeanLocalField _root_.chosenFinitePlaceLocalizedIsValuativeTopology _root_.chosenFinitePlaceLocalizedLocallyCompactSpace _root_.chosenFinitePlaceLocalizedValuationCompatible _root_.chosenFinitePlaceLocalizedValuationHasExtension _root_.chosenFinitePlaceLocalizedValuationIsNontrivial _root_.chosenFinitePlaceLocalizedValuativeRel _root_.chosenFinitePlaceLocalizedValuativeRelIsNontrivial _root_.chosenFinitePlaceLocalizedValued _root_.finiteLocalUnitsOpen _root_.relativeAdeleRingIntermediateAlgebra _root_.relativeAdeleRingTopIntermediateAlgebra _root_.relativeUnrestrictedSPlaceFactorCommGroup
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

/-!
# Finiteness of localized-completion Herbrand groups
-/

open AlgebraicNumberTheory.Valuations
open HilbertRamification
open LocalClassFieldTheory
open LocalFieldTheory
open CyclicCohomology
open CyclicCohomology.ProfiniteCohomology.Herbrand
open scoped TensorProduct

noncomputable section

namespace LocalClassFieldTheory

section LocalTateComparison

variable {k ell : Type}
    [Field k] [Field ell] [Algebra k ell]
    [FiniteDimensional k ell] [IsGalois k ell]

theorem localHerbrandH0Finite
    (vK : AbsoluteValue k ℝ) (hvK : vK.IsNontrivial)
    (w : AbsoluteValueExtension vK ell)
    (σ : ell ≃ₐ[k] ell)
    (hgen : ∀ τ : ell ≃ₐ[k] ell,
      τ ∈ Subgroup.zpowers σ)
    [ValuativeRel vK.Completion]
    [IsNonarchimedeanLocalField vK.Completion] :
    letI hK :=
      AbsoluteValue.extensionCompletionAlgebra
        (K := k) w.1
    letI : SMul k w.1.Completion := hK.toSMul
    letI : Algebra vK.Completion w.1.Completion :=
      AbsoluteValue.completionAlgebra vK w.1 w.2
    letI := localizedCompletionGlobalAlgebra vK w
    letI := localizedCompletionIsScalarTower vK w
    letI : FiniteDimensional vK.Completion
        (LocalizedCompletion vK w) :=
      localizedCompletionModuleFinite vK hvK w
    letI : IsGalois vK.Completion
        (LocalizedCompletion vK w) :=
      HilbertRamification.algebraicLocalization_isGalois vK w
    letI : Fintype (absoluteValueDecompositionGroup k w.1) :=
      Fintype.ofFinite _
    letI :=
      decompositionGroupLocalUnitsAction vK hvK w
    Finite
      (HerbrandH0 (absoluteValueDecompositionGroup k w.1)
        (LocalizedCompletion vK w)ˣ) := by
  let := localizedCompletionBaseAlgebra vK w
  let := localizedCompletionGlobalAlgebra vK w
  let := localizedCompletionIsScalarTower vK w
  let : FiniteDimensional vK.Completion
      (LocalizedCompletion vK w) :=
    localizedCompletionFiniteDimensional vK hvK w
  let : IsGalois vK.Completion
      (LocalizedCompletion vK w) :=
    localizedCompletionIsGalois vK w
  let := localizedCompletionDecompositionGroupFintype vK w
  let g :=
    localizedCompletionGaloisGenerator
      vK hvK w σ hgen
  let hg :=
    localizedCompletionGaloisGenerator_generates
      vK hvK w σ hgen
  let hcard :=
    finiteExtensionUnits_tate_card_of_generator
      vK.Completion (LocalizedCompletion vK w)
      g hg
  let : Finite
      (tateCohomology
        (Rep.ofAlgebraAutOnUnits vK.Completion
          (LocalizedCompletion vK w)) 0) :=
    hcard.finiteH0
  exact Finite.of_equiv
    (Multiplicative
      (tateCohomology
        (Rep.ofAlgebraAutOnUnits vK.Completion
          (LocalizedCompletion vK w)) 0))
    (localHerbrandH0EquivUnitsTateH0
      vK hvK w).symm.toEquiv

theorem localHerbrandHMinusOneFinite
    (vK : AbsoluteValue k ℝ) (hvK : vK.IsNontrivial)
    (w : AbsoluteValueExtension vK ell)
    (σ : ell ≃ₐ[k] ell)
    (hgen : ∀ τ : ell ≃ₐ[k] ell,
      τ ∈ Subgroup.zpowers σ)
    [ValuativeRel vK.Completion]
    [IsNonarchimedeanLocalField vK.Completion] :
    letI hK :=
      AbsoluteValue.extensionCompletionAlgebra
        (K := k) w.1
    letI : SMul k w.1.Completion := hK.toSMul
    letI : Algebra vK.Completion w.1.Completion :=
      AbsoluteValue.completionAlgebra vK w.1 w.2
    letI := localizedCompletionGlobalAlgebra vK w
    letI := localizedCompletionIsScalarTower vK w
    letI : FiniteDimensional vK.Completion
        (LocalizedCompletion vK w) :=
      localizedCompletionModuleFinite vK hvK w
    letI : IsGalois vK.Completion
        (LocalizedCompletion vK w) :=
      HilbertRamification.algebraicLocalization_isGalois vK w
    letI : Fintype (absoluteValueDecompositionGroup k w.1) :=
      Fintype.ofFinite _
    letI :=
      decompositionGroupLocalUnitsAction vK hvK w
    Finite
      (HerbrandHMinusOne
        (absoluteValueDecompositionGroup k w.1)
        (LocalizedCompletion vK w)ˣ
        (subgroupGeneratorOfGenerator
          (absoluteValueDecompositionGroup k w.1)
          σ hgen)) := by
  let := localizedCompletionBaseAlgebra vK w
  let := localizedCompletionGlobalAlgebra vK w
  let := localizedCompletionIsScalarTower vK w
  let : FiniteDimensional vK.Completion
      (LocalizedCompletion vK w) :=
    localizedCompletionFiniteDimensional vK hvK w
  let : IsGalois vK.Completion
      (LocalizedCompletion vK w) :=
    localizedCompletionIsGalois vK w
  let := localizedCompletionDecompositionGroupFintype vK w
  let g :=
    localizedCompletionGaloisGenerator
      vK hvK w σ hgen
  let hg :=
    localizedCompletionGaloisGenerator_generates
      vK hvK w σ hgen
  let hcard :=
    finiteExtensionUnits_tate_card_of_generator
      vK.Completion (LocalizedCompletion vK w)
      g hg
  let : Finite
      (tateCohomology
        (Rep.ofAlgebraAutOnUnits vK.Completion
          (LocalizedCompletion vK w)) (-1)) := by
    apply Nat.finite_of_card_ne_zero
    rw [hcard.cardHminusOne]
    exact one_ne_zero
  exact Finite.of_equiv
    (tateCohomology
      (Rep.ofAlgebraAutOnUnits vK.Completion
        (LocalizedCompletion vK w)) (-1))
    (localHerbrandHMinusOneEquivUnitsTateHminusOne
      vK hvK w σ hgen).symm


end LocalTateComparison

end LocalClassFieldTheory
end
end

section
-- module Solutions.OAIQ244_DUKE.LocalClassFieldTheory_ClassFormation_LocalizedCompletionCohomology_Cardinality_H0
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 400000
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalCyclotomicCompletionAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalClassFieldTheory.localDecompositionResidueFinite _root_.LocalClassFieldTheory.localDecompositionResidueFintype _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitQuotientCarrier_finite _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.residueFieldZModAlgebra _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedIntegralAlgebraContextValuationSubringAlgebra _root_.LocalFieldTheory.DiscreteValuationField.finite_nsmulAddKernel_padicInt_pi _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_multiplicative_nthPowerKernel _root_.LocalFieldTheory.finite_nsmulAddKernel_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.LubinTate.compatibleGroupFamiliesGroup _root_.OAI.PrimeDegreePackets.boundedRealFields_finite _root_.OAI.PrimeDegreePackets.diagonalLogAction _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionResidueField.instField _root_.RamificationTheory.HilbertRamification.ValuationSubring.selectedResidueField.instAlgebra _root_.RayClass.approximationCompletionTopologicalSpace _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.RelativeIdeleGroup.relativeIdeleMulAction _root_.CyclicCohomology.binaryCoefficientFamilyCommGroup _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.LocalClassFieldTheory.normalizationIntegerRingIsIntegralClosure _root_.adicCompletionProperSpace _root_.chosenFinitePlaceCompletionAlgebra _root_.chosenFinitePlaceCompletionContinuousSMul _root_.chosenFinitePlaceCompletionFiniteDimensional _root_.chosenFinitePlaceCompletionLocallyCompactSpace _root_.chosenFinitePlaceLocalizedFiniteDimensional _root_.chosenFinitePlaceLocalizedIntegerAlgebra _root_.chosenFinitePlaceLocalizedIntegerModuleFinite _root_.chosenFinitePlaceLocalizedIsGalois _root_.chosenFinitePlaceLocalizedIsIntegralClosure _root_.chosenFinitePlaceLocalizedIsNonarchimedeanLocalField _root_.chosenFinitePlaceLocalizedIsValuativeTopology _root_.chosenFinitePlaceLocalizedLocallyCompactSpace _root_.chosenFinitePlaceLocalizedValuationCompatible _root_.chosenFinitePlaceLocalizedValuationHasExtension _root_.chosenFinitePlaceLocalizedValuationIsNontrivial _root_.chosenFinitePlaceLocalizedValuativeRel _root_.chosenFinitePlaceLocalizedValuativeRelIsNontrivial _root_.chosenFinitePlaceLocalizedValued _root_.finiteLocalUnitsOpen _root_.relativeAdeleRingIntermediateAlgebra _root_.relativeAdeleRingTopIntermediateAlgebra _root_.relativeUnrestrictedSPlaceFactorCommGroup
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

/-!
# Degree-zero localized Herbrand cardinality
-/

open AlgebraicNumberTheory.Valuations
open HilbertRamification
open LocalClassFieldTheory
open LocalFieldTheory
open CyclicCohomology
open CyclicCohomology.ProfiniteCohomology.Herbrand
open scoped TensorProduct

noncomputable section

namespace LocalClassFieldTheory

section LocalTateComparison

variable {k ell : Type}
    [Field k] [Field ell] [Algebra k ell]
    [FiniteDimensional k ell] [IsGalois k ell]

theorem localHerbrandH0_card_eq_localDegree
    (vK : AbsoluteValue k ℝ) (hvK : vK.IsNontrivial)
    (w : AbsoluteValueExtension vK ell)
    (σ : ell ≃ₐ[k] ell)
    (hgen : ∀ τ : ell ≃ₐ[k] ell,
      τ ∈ Subgroup.zpowers σ)
    [ValuativeRel vK.Completion]
    [IsNonarchimedeanLocalField vK.Completion] :
    letI hK :=
      AbsoluteValue.extensionCompletionAlgebra
        (K := k) w.1
    letI : SMul k w.1.Completion := hK.toSMul
    letI : Algebra vK.Completion w.1.Completion :=
      AbsoluteValue.completionAlgebra vK w.1 w.2
    letI := localizedCompletionGlobalAlgebra vK w
    letI := localizedCompletionIsScalarTower vK w
    letI : FiniteDimensional vK.Completion
        (LocalizedCompletion vK w) :=
      localizedCompletionModuleFinite vK hvK w
    letI : IsGalois vK.Completion
        (LocalizedCompletion vK w) :=
      HilbertRamification.algebraicLocalization_isGalois vK w
    letI : Fintype (absoluteValueDecompositionGroup k w.1) :=
      Fintype.ofFinite _
    letI :=
      decompositionGroupLocalUnitsAction vK hvK w
    letI : Finite
        (HerbrandH0
          (absoluteValueDecompositionGroup k w.1)
          (LocalizedCompletion vK w)ˣ) :=
      localHerbrandH0Finite vK hvK w σ hgen
    Nat.card
        (HerbrandH0
          (absoluteValueDecompositionGroup k w.1)
          (LocalizedCompletion vK w)ˣ) =
      Module.finrank vK.Completion
        (LocalizedCompletion vK w) := by
  let := localizedCompletionBaseAlgebra vK w
  let := localizedCompletionGlobalAlgebra vK w
  let := localizedCompletionIsScalarTower vK w
  let : FiniteDimensional vK.Completion
      (LocalizedCompletion vK w) :=
    localizedCompletionFiniteDimensional vK hvK w
  let : IsGalois vK.Completion
      (LocalizedCompletion vK w) :=
    localizedCompletionIsGalois vK w
  let := localizedCompletionDecompositionGroupFintype vK w
  let :=
    decompositionGroupLocalUnitsAction vK hvK w
  let : Finite
      (HerbrandH0
        (absoluteValueDecompositionGroup k w.1)
        (LocalizedCompletion vK w)ˣ) :=
    localHerbrandH0Finite vK hvK w σ hgen
  let g :=
    localizedCompletionGaloisGenerator
      vK hvK w σ hgen
  let hg :=
    localizedCompletionGaloisGenerator_generates
      vK hvK w σ hgen
  let hcard :=
    finiteExtensionUnits_tate_card_of_generator
      vK.Completion (LocalizedCompletion vK w)
      g hg
  let : Finite
      (tateCohomology
        (Rep.ofAlgebraAutOnUnits vK.Completion
          (LocalizedCompletion vK w)) 0) :=
    hcard.finiteH0
  calc
    Nat.card
        (HerbrandH0
          (absoluteValueDecompositionGroup k w.1)
          (LocalizedCompletion vK w)ˣ) =
      Nat.card
        (Multiplicative
          (tateCohomology
            (Rep.ofAlgebraAutOnUnits vK.Completion
              (LocalizedCompletion vK w)) 0)) :=
      Nat.card_congr
        (localHerbrandH0EquivUnitsTateH0
          vK hvK w).toEquiv
    _ = Nat.card
        (tateCohomology
          (Rep.ofAlgebraAutOnUnits vK.Completion
            (LocalizedCompletion vK w)) 0) := rfl
    _ = Module.finrank vK.Completion
        (LocalizedCompletion vK w) :=
      hcard.cardH0


end LocalTateComparison

end LocalClassFieldTheory
end
end

section
-- module Solutions.OAIQ244_DUKE.LocalClassFieldTheory_ClassFormation_LocalizedCompletionCohomology_Cardinality_HMinusOne
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 400000
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalCyclotomicCompletionAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalClassFieldTheory.localDecompositionResidueFinite _root_.LocalClassFieldTheory.localDecompositionResidueFintype _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitQuotientCarrier_finite _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.residueFieldZModAlgebra _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedIntegralAlgebraContextValuationSubringAlgebra _root_.LocalFieldTheory.DiscreteValuationField.finite_nsmulAddKernel_padicInt_pi _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_multiplicative_nthPowerKernel _root_.LocalFieldTheory.finite_nsmulAddKernel_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.LubinTate.compatibleGroupFamiliesGroup _root_.OAI.PrimeDegreePackets.boundedRealFields_finite _root_.OAI.PrimeDegreePackets.diagonalLogAction _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionResidueField.instField _root_.RamificationTheory.HilbertRamification.ValuationSubring.selectedResidueField.instAlgebra _root_.RayClass.approximationCompletionTopologicalSpace _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.RelativeIdeleGroup.relativeIdeleMulAction _root_.CyclicCohomology.binaryCoefficientFamilyCommGroup _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.LocalClassFieldTheory.normalizationIntegerRingIsIntegralClosure _root_.adicCompletionProperSpace _root_.chosenFinitePlaceCompletionAlgebra _root_.chosenFinitePlaceCompletionContinuousSMul _root_.chosenFinitePlaceCompletionFiniteDimensional _root_.chosenFinitePlaceCompletionLocallyCompactSpace _root_.chosenFinitePlaceLocalizedFiniteDimensional _root_.chosenFinitePlaceLocalizedIntegerAlgebra _root_.chosenFinitePlaceLocalizedIntegerModuleFinite _root_.chosenFinitePlaceLocalizedIsGalois _root_.chosenFinitePlaceLocalizedIsIntegralClosure _root_.chosenFinitePlaceLocalizedIsNonarchimedeanLocalField _root_.chosenFinitePlaceLocalizedIsValuativeTopology _root_.chosenFinitePlaceLocalizedLocallyCompactSpace _root_.chosenFinitePlaceLocalizedValuationCompatible _root_.chosenFinitePlaceLocalizedValuationHasExtension _root_.chosenFinitePlaceLocalizedValuationIsNontrivial _root_.chosenFinitePlaceLocalizedValuativeRel _root_.chosenFinitePlaceLocalizedValuativeRelIsNontrivial _root_.chosenFinitePlaceLocalizedValued _root_.finiteLocalUnitsOpen _root_.relativeAdeleRingIntermediateAlgebra _root_.relativeAdeleRingTopIntermediateAlgebra _root_.relativeUnrestrictedSPlaceFactorCommGroup
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

/-!
# Degree-minus-one localized Herbrand cardinality
-/

open AlgebraicNumberTheory.Valuations
open HilbertRamification
open LocalClassFieldTheory
open LocalFieldTheory
open CyclicCohomology
open CyclicCohomology.ProfiniteCohomology.Herbrand
open scoped TensorProduct

noncomputable section

namespace LocalClassFieldTheory

section LocalTateComparison

variable {k ell : Type}
    [Field k] [Field ell] [Algebra k ell]
    [FiniteDimensional k ell] [IsGalois k ell]

theorem localHerbrandHMinusOne_card_eq_one
    (vK : AbsoluteValue k ℝ) (hvK : vK.IsNontrivial)
    (w : AbsoluteValueExtension vK ell)
    (σ : ell ≃ₐ[k] ell)
    (hgen : ∀ τ : ell ≃ₐ[k] ell,
      τ ∈ Subgroup.zpowers σ)
    [ValuativeRel vK.Completion]
    [IsNonarchimedeanLocalField vK.Completion] :
    letI hK :=
      AbsoluteValue.extensionCompletionAlgebra
        (K := k) w.1
    letI : SMul k w.1.Completion := hK.toSMul
    letI : Algebra vK.Completion w.1.Completion :=
      AbsoluteValue.completionAlgebra vK w.1 w.2
    letI := localizedCompletionGlobalAlgebra vK w
    letI := localizedCompletionIsScalarTower vK w
    letI : FiniteDimensional vK.Completion
        (LocalizedCompletion vK w) :=
      localizedCompletionModuleFinite vK hvK w
    letI : IsGalois vK.Completion
        (LocalizedCompletion vK w) :=
      HilbertRamification.algebraicLocalization_isGalois vK w
    letI : Fintype (absoluteValueDecompositionGroup k w.1) :=
      Fintype.ofFinite _
    letI :=
      decompositionGroupLocalUnitsAction vK hvK w
    letI : Finite
        (HerbrandHMinusOne
          (absoluteValueDecompositionGroup k w.1)
          (LocalizedCompletion vK w)ˣ
          (subgroupGeneratorOfGenerator
            (absoluteValueDecompositionGroup k w.1)
            σ hgen)) :=
      localHerbrandHMinusOneFinite
        vK hvK w σ hgen
    Nat.card
        (HerbrandHMinusOne
          (absoluteValueDecompositionGroup k w.1)
          (LocalizedCompletion vK w)ˣ
          (subgroupGeneratorOfGenerator
            (absoluteValueDecompositionGroup k w.1)
            σ hgen)) = 1 := by
  let := localizedCompletionBaseAlgebra vK w
  let := localizedCompletionGlobalAlgebra vK w
  let := localizedCompletionIsScalarTower vK w
  let : FiniteDimensional vK.Completion
      (LocalizedCompletion vK w) :=
    localizedCompletionFiniteDimensional vK hvK w
  let : IsGalois vK.Completion
      (LocalizedCompletion vK w) :=
    localizedCompletionIsGalois vK w
  let := localizedCompletionDecompositionGroupFintype vK w
  let :=
    decompositionGroupLocalUnitsAction vK hvK w
  let : Finite
      (HerbrandHMinusOne
        (absoluteValueDecompositionGroup k w.1)
        (LocalizedCompletion vK w)ˣ
        (subgroupGeneratorOfGenerator
          (absoluteValueDecompositionGroup k w.1)
          σ hgen)) :=
    localHerbrandHMinusOneFinite
      vK hvK w σ hgen
  let g :=
    localizedCompletionGaloisGenerator
      vK hvK w σ hgen
  let hg :=
    localizedCompletionGaloisGenerator_generates
      vK hvK w σ hgen
  let hcard :=
    finiteExtensionUnits_tate_card_of_generator
      vK.Completion (LocalizedCompletion vK w)
      g hg
  calc
    Nat.card
        (HerbrandHMinusOne
          (absoluteValueDecompositionGroup k w.1)
          (LocalizedCompletion vK w)ˣ
          (subgroupGeneratorOfGenerator
            (absoluteValueDecompositionGroup k w.1)
            σ hgen)) =
      Nat.card
        (tateCohomology
          (Rep.ofAlgebraAutOnUnits vK.Completion
            (LocalizedCompletion vK w)) (-1)) :=
      Nat.card_congr
        (localHerbrandHMinusOneEquivUnitsTateHminusOne
          vK hvK w σ hgen)
    _ = 1 := hcard.cardHminusOne


end LocalTateComparison

end LocalClassFieldTheory
end
end

section
-- module Solutions.OAIQ244_DUKE.AlgebraicNumberTheory_Completion_UnramifiedComparison_IdealToCompletion
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitInverseLimitCarrierPadicModule _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitQuotientCarrierPadicModule _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitPadicModule _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitPadicSMul _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.residueFieldZModAlgebra _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedIntegralAlgebraContextValuationSubringAlgebra _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.RamificationTheory.HilbertRamification.Higher.lowerRamificationGroup.instNormal _root_.LocalClassFieldTheory.normalizationIntegerRingIsIntegralClosure _root_.RamificationTheory.HilbertRamification.CompleteDVF.decompositionGroupMulSemiringAction
attribute [-simp] _root_.IsDiscreteValuationRing.addVal_ringEquiv _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.EqualCharacteristicLaurent.coeffHom_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.EqualCharacteristicLaurent.powerSeriesEvalHom_C _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.EqualCharacteristicLaurent.powerSeriesEvalHom_X _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.EqualCharacteristicLaurent.powerSeriesEvalSubringHom_C _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.EqualCharacteristicLaurent.powerSeriesEvalSubringHom_X _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.AdicPrincipalUnits.addEquiv_map_smul _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.AdicPrincipalUnits.val_of _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.DiscretePrincipalUnitQuotient.addEquiv_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.DiscretePrincipalUnitQuotient.addEquiv_map_smul _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.DiscretePrincipalUnitQuotient.addEquiv_of _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.DiscretePrincipalUnitQuotient.addEquiv_symm_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.DiscretePrincipalUnitQuotient.val_transition _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.adicPrincipalUnitsHomeomorphUnderlying_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.iwasawaGlobalInverseLimitCarrier_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitAddEquivInverseLimitCarrier_map_smul _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitAddHomeomorphInverseLimitCarrier_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitInverseLimitCarrierEval_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitInverseLimitCarrierPadic_smul_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitMulEquivInverseLimitCarrier_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitPadic_smul_carrier_coordinate _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitProdiscreteLimitHomeomorphUnderlying_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitQuotientCarrierPadicScalar_eq_smul _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitQuotientCarrierToFull_mk _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitQuotientCarrierTransition_mk _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.uniformizerHigherUnitQuotientEquiv_mk _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.PrincipalUnitProdiscreteLimit.addEquiv_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.PrincipalUnitProdiscreteLimit.addEquiv_map_smul _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.PrincipalUnitProdiscreteLimit.addEquiv_symm_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.PrincipalUnitProdiscreteLimit.coordinate_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.adicPrincipalUnitsContinuousAddEquivUnderlyingOfWithZeroValuation_map_smul _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.adicPrincipalUnitsHomeomorphProdiscreteLimit_to_addEquiv _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.iwasawaDegreeTerm_zero _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.iwasawaGn_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.iwasawaPartialProduct_zero_input _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.iwasawaSeedAtLevel_val _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.iwasawaSeedIdeal_val _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.iwasawaSeed_val _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitPadic_natCast_smul _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitPadic_nsmul_eq_pow _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitPadic_smul_def _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitSuccQuotAddEquivResidue_iwasawaSeed _root_.LocalFieldTheory.DiscreteValuationField.LocalField.higherPrincipalUnitAddToFirst_smul _root_.LocalFieldTheory.DiscreteValuationField.LocalField.laurentSeriesEquivLaurentImageSubfield_apply_coe _root_.LocalFieldTheory.DiscreteValuationField.LocalField.padicIntToValuationSubring_coe _root_.LocalFieldTheory.DiscreteValuationField.MultiplicativeIntegerValuation.fieldUnitDecompositionLogHomWithUniformizerValue_apply _root_.LocalFieldTheory.DiscreteValuationField.MultiplicativeIntegerValuation.fieldUnitDecompositionLogHomWithUniformizerValue_principal _root_.LocalFieldTheory.DiscreteValuationField.MultiplicativeIntegerValuation.fieldUnitDecompositionLogHomWithUniformizerValue_root _root_.LocalFieldTheory.DiscreteValuationField.MultiplicativeIntegerValuation.fieldUnitDecompositionLogHomWithUniformizerValue_uniformizer _root_.LocalFieldTheory.DiscreteValuationField.MultiplicativeIntegerValuation.fieldUnitLogHomWithUniformizerValue_apply _root_.LocalFieldTheory.DiscreteValuationField.MultiplicativeIntegerValuation.principalUnitExpSeriesHomOfMaximalIdealPow_apply _root_.LocalFieldTheory.DiscreteValuationField.MultiplicativeIntegerValuation.principalUnitLogSeriesHomOfWithZeroValuationScaled_apply_toAdd _root_.LocalFieldTheory.Padic.integerRingEquivPadicDVRValuationSubring_coe _root_.LocalFieldTheory.localIntegerValuationSubringEquiv_apply_coe _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.LubinTate.LubinTateSeries.standardLubinTateSeries_toPowerSeries _root_.LubinTate.SameUniformizer.coeff_recursiveIntertwiner _root_.LubinTate.SameUniformizer.constantCoeff_inVariable _root_.LubinTate.SameUniformizer.intertwinerApproximation_zero _root_.LubinTate.SameUniformizer.standardLubinTateEndomorphism_coeff_one _root_.LubinTate.standardLubinTateBaseUniformizerUnit_coe _root_.LubinTate.standardLubinTateChangedUniformizerUnit_coe _root_.LubinTate.standardLubinTateLevelGenerator_coe _root_.LubinTate.standardLubinTatePolynomialIterateOverSeparableClosure_eval _root_.LubinTate.standardLubinTatePolynomialIterate_derivative_eval_zero _root_.LubinTate.standardLubinTatePolynomialIterate_eval_zero _root_.LubinTate.standardLubinTatePolynomialIterate_zero _root_.LubinTate.standardLubinTatePolynomial_derivative_eval_zero _root_.LubinTate.standardLubinTatePolynomial_eval _root_.LubinTate.standardLubinTatePolynomial_toPowerSeries _root_.LubinTate.standardLubinTatePolynomial_toPowerSeries_eq_series _root_.LubinTate.standardLubinTatePrimitivePointInteger_coe _root_.LubinTate.standardLubinTatePrimitivePolynomialOverField_coeff_zero _root_.LubinTate.standardLubinTatePrimitivePolynomial_coeff_zero _root_.LubinTate.standardLubinTateUnitFactorFieldUnit_coe _root_.OAI.PrimeDegreePackets.ThetaConstruction.schwartzCM_apply _root_.RamificationTheory.HilbertRamification.Higher.dvfValuationSubringUnitAut_apply _root_.RamificationTheory.HilbertRamification.Higher.lowerRamificationGroup_neg_one _root_.RamificationTheory.HilbertRamification.Higher.mem_dvfHigherPrincipalUnitGroup_iff _root_.RamificationTheory.HilbertRamification.Higher.mem_lowerRamificationGroup_iff _root_.RamificationTheory.HilbertRamification.Higher.mem_valuationSubringDisplacementSubalgebraOfUniqueExtension_iff _root_.RamificationTheory.HilbertRamification.Higher.realRamificationIdeal_nat _root_.RamificationTheory.HilbertRamification.Higher.realRamificationIdeal_neg_one _root_.RamificationTheory.HilbertRamification.Higher.valuationSubringAutOfUniqueExtension_apply_coe _root_.RamificationTheory.HilbertRamification.Higher.valuationSubringAutOfUniqueExtension_apply_inv_apply _root_.RamificationTheory.HilbertRamification.Higher.valuationSubringAutOfUniqueExtension_mul_apply _root_.RamificationTheory.HilbertRamification.Higher.valuationSubringAutOfUniqueExtension_one_apply
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

/-- A chosen global integral uniformizer and its image in a finite-place
completion. -/
noncomputable def chosenFinitePlaceCompletionIntegralUniformizer
    {F : Type} [Field F] [NumberField F]
    (v : HeightOneSpectrum (𝓞 F)) :
    FinitePlaceCompletionIntegralUniformizer v := by
  let vF := HeightOneSpectrum.adicAbv F v
  let eBaseField :
      vF.Completion ≃+* v.adicCompletion F :=
    finitePlaceCompletionRingEquiv v
  let eBase :
      𝒪[vF.Completion] ≃+*
        v.adicCompletionIntegers F :=
    finitePlaceCompletionIntegerRingEquiv v
  let π : 𝓞 F :=
    Classical.choose v.intValuation_exists_uniformizer
  have hπ :
      v.intValuation π = WithZero.exp (-1 : ℤ) :=
    Classical.choose_spec v.intValuation_exists_uniformizer
  let πConcrete :
      v.adicCompletionIntegers F :=
    ⟨algebraMap (𝓞 F) (v.adicCompletion F) π, by
      rw [HeightOneSpectrum.mem_adicCompletionIntegers]
      change Valued.v (π : v.adicCompletion F) ≤ 1
      rw [HeightOneSpectrum.valuedAdicCompletion_eq_valuation',
        HeightOneSpectrum.valuation_of_algebraMap, hπ]
      change WithZero.exp (-1 : ℤ) ≤ WithZero.exp 0
      rw [WithZero.exp_le_exp]
      omega⟩
  let baseDVF :
      ValuationTheory.DiscreteValuationField.DVF
        (v.adicCompletion F) :=
    { ValueGroup := WithZero (Multiplicative ℤ)
      valuation := Valued.v }
  have hπConcreteUniformizer :
      baseDVF.valuation.IsUniformizer
        (πConcrete : v.adicCompletion F) := by
    rw [Valuation.IsUniformizer.iff,
      Valuation.IsRankOneDiscrete.generator_eq_exp_neg_one_of_surjective
        (v.valuedAdicCompletion_surjective F)]
    change Valued.v (π : v.adicCompletion F) =
      WithZero.exp (-1 : ℤ)
    rw [HeightOneSpectrum.valuedAdicCompletion_eq_valuation',
      HeightOneSpectrum.valuation_of_algebraMap, hπ]
  let πCompletion : 𝒪[vF.Completion] :=
    eBase.symm πConcrete
  have hπCompletionField :
      (πCompletion : vF.Completion) =
        algebraMap F vF.Completion (π : F) := by
    apply eBaseField.injective
    have happ :=
      congrArg Subtype.val
        (eBase.apply_symm_apply πConcrete)
    change
      eBaseField (πCompletion : vF.Completion) =
        (πConcrete : v.adicCompletion F) at happ
    rw [happ]
    let x : WithAbs vF :=
      (WithAbs.equiv vF).symm (π : F)
    change
      (π : v.adicCompletion F) =
        finitePlaceCompletionRingHom v
          (x : vF.Completion)
    rw [finitePlaceCompletionRingHom_coe]
    rfl
  have hπCompletionMaximal :
      πCompletion ∈
        (IsLocalRing.maximalIdeal
          𝒪[vF.Completion]) := by
    have hπConcreteMaximal :
        πConcrete ∈
          (IsLocalRing.maximalIdeal
            (v.adicCompletionIntegers F)) :=
      baseDVF.uniformizer_mem_maximalIdeal
        hπConcreteUniformizer
    have hpow :
        eBase πCompletion ∈
          (IsLocalRing.maximalIdeal
              (v.adicCompletionIntegers F)) ^ 1 := by
      simpa [πCompletion] using hπConcreteMaximal
    have hmem :=
      (ValuationTheory.ringEquiv_mem_maximalIdeal_pow_iff
        eBase 1 πCompletion).1 hpow
    simpa using hmem
  have hπConcreteNotDeep :
      πConcrete ∉
        (IsLocalRing.maximalIdeal
          (v.adicCompletionIntegers F)) ^ 2 :=
    baseDVF.uniformizer_not_mem_maximalIdeal_sq
      hπConcreteUniformizer
  have hπCompletionNotDeep :
      πCompletion ∉
        (IsLocalRing.maximalIdeal
          𝒪[vF.Completion]) ^ 2 := by
    intro hdeep
    apply hπConcreteNotDeep
    simpa [πCompletion] using
      ((ValuationTheory.ringEquiv_mem_maximalIdeal_pow_iff
        eBase 2 πCompletion).2 hdeep)
  let completionDVF :
      ValuationTheory.DiscreteValuationField.DVF
        vF.Completion :=
    { ValueGroup := ValuativeRel.ValueGroupWithZero vF.Completion
      valuation := ValuativeRel.valuation vF.Completion }
  have hπCompletionUniformizer :
      completionDVF.valuation.IsUniformizer
        (πCompletion : vF.Completion) :=
    completionDVF.isUniformizer_of_mem_maximalIdeal_of_not_mem_maximalIdeal_sq
      hπCompletionMaximal hπCompletionNotDeep
  exact
    { integer := π
      completionInteger := πCompletion
      intValuation_eq_exp_neg_one := hπ
      coe_completionInteger := hπCompletionField
      completionInteger_isUniformizer :=
        hπCompletionUniformizer
      completionInteger_mem_maximalIdeal :=
        hπCompletionMaximal }
end
end

section
-- module Solutions.OAIQ244_DUKE.LocalClassFieldTheory_ClassFormation_ArchimedeanNormQuotient
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalCyclotomicCompletionAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalClassFieldTheory.localDecompositionResidueFinite _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitQuotientCarrier_finite _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.residueFieldZModAlgebra _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedIntegralAlgebraContextValuationSubringAlgebra _root_.LocalFieldTheory.DiscreteValuationField.finite_nsmulAddKernel_padicInt_pi _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_multiplicative_nthPowerKernel _root_.LocalFieldTheory.finite_nsmulAddKernel_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.LubinTate.compatibleGroupFamiliesGroup _root_.OAI.PrimeDegreePackets.boundedRealFields_finite _root_.OAI.PrimeDegreePackets.diagonalLogAction _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionResidueField.instField _root_.RamificationTheory.HilbertRamification.ValuationSubring.selectedResidueField.instAlgebra _root_.CyclicCohomology.binaryCoefficientFamilyCommGroup _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.LocalClassFieldTheory.normalizationIntegerRingIsIntegralClosure _root_.adicCompletionProperSpace _root_.chosenFinitePlaceCompletionAlgebra _root_.chosenFinitePlaceCompletionContinuousSMul _root_.chosenFinitePlaceCompletionFiniteDimensional _root_.chosenFinitePlaceCompletionLocallyCompactSpace _root_.chosenFinitePlaceLocalizedFiniteDimensional _root_.chosenFinitePlaceLocalizedIntegerAlgebra _root_.chosenFinitePlaceLocalizedIntegerModuleFinite _root_.chosenFinitePlaceLocalizedIsGalois _root_.chosenFinitePlaceLocalizedIsIntegralClosure _root_.chosenFinitePlaceLocalizedIsNonarchimedeanLocalField _root_.chosenFinitePlaceLocalizedIsValuativeTopology _root_.chosenFinitePlaceLocalizedLocallyCompactSpace _root_.chosenFinitePlaceLocalizedValuationCompatible _root_.chosenFinitePlaceLocalizedValuationHasExtension _root_.chosenFinitePlaceLocalizedValuationIsNontrivial _root_.chosenFinitePlaceLocalizedValuativeRel _root_.chosenFinitePlaceLocalizedValuativeRelIsNontrivial _root_.chosenFinitePlaceLocalizedValued _root_.finiteLocalUnitsOpen _root_.relativeAdeleRingIntermediateAlgebra _root_.relativeAdeleRingTopIntermediateAlgebra _root_.relativeUnrestrictedSPlaceFactorCommGroup
attribute [-simp] _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.CyclicCohomology.fixedPiEquiv_apply_coe _root_.CyclicCohomology.herbrandH0EquivariantMulEquiv_mk _root_.GlobalClassFieldTheory.Reciprocity.rationalCyclotomicGlobalToLocalizedAlgHom_apply _root_.GlobalClassFieldTheory.Reciprocity.rationalCyclotomicGlobalToLocalizedAlgHom_primitiveRoot _root_.IsDiscreteValuationRing.addVal_ringEquiv _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.LocalClassFieldTheory.mem_decompositionRightCosetsFinset _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.OAI.PrimeDegreePackets.ThetaConstruction.schwartzCM_apply _root_.RelativeIdeleGroup.Cohomology.baseIdeleClassEquivFixed_coe _root_.RelativeIdeleGroup.Cohomology.baseIdeleClassToFixed_coe _root_.doubleCosetExtension_mk _root_.extendAbsoluteValueExtensionFromIntermediate_apply _root_.finitePlaceBelow_finitePlaceExtensionCentre _root_.finitePlaceExtensionAdicCompletionRingEquiv_toCompletion _root_.finitePlaceExtensionCentreInFibre_coe _root_.finitePlaceExtensionCentre_asIdeal _root_.finitePlaceExtensionCompletionRingEquiv_toCompletion _root_.finitePlaceExtensionEquivAbove_coe _root_.finitePlaceLocalTensorDecompositionComponentRingHom_apply _root_.finitePlaceLocalTensorDecompositionComponent_add _root_.finitePlaceLocalTensorDecompositionComponent_tmul _root_.finitePlaceLocalTensorDecompositionComponent_zero _root_.finitePlaceLocalTensorDecompositionUnitsComponent_coe _root_.finitePlaceLocalTensorDecompositionUnitsEquiv_apply _root_.finitePlaceTensorRingEquivAboveAdic_apply_extension _root_.finitePlaceTensorUnitsEquivAboveAdic_apply_extension _root_.infinitePlaceAboveEquivExtension_apply_val _root_.infinitePlaceTensorRingEquivAbove_apply _root_.infinitePlaceTensorUnitsEquivAbove_apply _root_.infinitePlace_mult_smul _root_.mem_finitePlaceDecompositionGroup_iff _root_.restrictAbsoluteValueExtensionToIntermediate_apply _root_.ringOfIntegersToFinitePlaceExtensionValuationSubring_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

/-!
# The real/complex norm quotient

At a ramified infinite place the local extension is `ℂ/ℝ`.  Its norm
subgroup consists exactly of the positive real units, so the sign map
identifies the norm quotient with `ℤˣ`, a group of order two.
-/

open LocalFieldTheory
open CyclicCohomology.ProfiniteCohomology.Herbrand
open CyclicCohomology

noncomputable section

namespace LocalClassFieldTheory

universe u v w z

open AlgebraicNumberTheory.Valuations
open HilbertRamification
open NumberField
open scoped Classical NumberField.LiesOver

variable
    {K L : Type}
    [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]

omit [NumberField L] in
omit [NumberField L] in
/-- The degree-zero local Herbrand group at an infinite place has
cardinality equal to the archimedean local degree: one at an
unramified place and two at a ramified real-to-complex place. -/
theorem infinitePlaceLocalHerbrandH0_card_eq_localDegree
    (v : InfinitePlace K) (w : InfinitePlace L)
    (hw : w.comap (algebraMap K L) = v) :
    let u :=
      infinitePlaceAbsoluteValueExtension v w hw
    letI hL :=
      AbsoluteValue.extensionCompletionAlgebra
        (K := K) u.1
    letI : SMul K u.1.Completion := hL.toSMul
    letI : Algebra v.1.Completion u.1.Completion :=
      AbsoluteValue.completionAlgebra v.1 u.1 u.2
    letI := localizedCompletionGlobalAlgebra v.1 u
    letI := localizedCompletionIsScalarTower v.1 u
    letI : FiniteDimensional v.1.Completion
        (LocalizedCompletion v.1 u) :=
      localizedCompletionModuleFinite v.1 v.isNontrivial u
    letI : IsGalois v.1.Completion
        (LocalizedCompletion v.1 u) :=
      HilbertRamification.algebraicLocalization_isGalois v.1 u
    letI : Fintype (absoluteValueDecompositionGroup K w.1) :=
      Fintype.ofFinite _
    letI : MulDistribMulAction
        (absoluteValueDecompositionGroup K w.1)
        (LocalizedCompletion v.1 u)ˣ :=
      decompositionGroupLocalUnitsAction
        v.1 v.isNontrivial u
    Nat.card
        (HerbrandH0
          (absoluteValueDecompositionGroup K w.1)
          (LocalizedCompletion v.1 u)ˣ) =
      if w.IsUnramified K then 1 else 2 := by
  let u :=
    infinitePlaceAbsoluteValueExtension v w hw
  let hL :=
    AbsoluteValue.extensionCompletionAlgebra
      (K := K) u.1
  let : SMul K u.1.Completion := hL.toSMul
  let : Algebra v.1.Completion u.1.Completion :=
    AbsoluteValue.completionAlgebra v.1 u.1 u.2
  let := localizedCompletionGlobalAlgebra v.1 u
  let := localizedCompletionIsScalarTower v.1 u
  let : FiniteDimensional v.1.Completion
      (LocalizedCompletion v.1 u) :=
    localizedCompletionModuleFinite v.1 v.isNontrivial u
  let : IsGalois v.1.Completion
      (LocalizedCompletion v.1 u) :=
    HilbertRamification.algebraicLocalization_isGalois v.1 u
  let : Fintype (absoluteValueDecompositionGroup K w.1) :=
    Fintype.ofFinite _
  let : MulDistribMulAction
      (absoluteValueDecompositionGroup K w.1)
      (LocalizedCompletion v.1 u)ˣ :=
    decompositionGroupLocalUnitsAction
      v.1 v.isNontrivial u
  by_cases hUnramified : w.IsUnramified K
  · rw [ite_eq_left hUnramified]
    apply herbrandH0_card_eq_one_of_group_card_eq_one
    rw [absoluteValueDecompositionGroup_eq_infinitePlaceStabilizer w,
      InfinitePlace.card_stabilizer, ite_eq_left hUnramified]
  · rw [ite_eq_right hUnramified]
    have hRamified : w.IsRamified K := hUnramified
    have hvReal : v.IsReal := by
      rw [← hw]
      exact hRamified.isReal
    have hwComplex : w.IsComplex :=
      hRamified.isComplex
    let eH0 :=
      localHerbrandH0EquivNormQuotient
        v.1 v.isNontrivial u
    let eCompletion :=
      localizedCompletionNormQuotientEquivAbsoluteCompletions
        v w hw
    let eRealComplex :=
      absoluteCompletionNormQuotientEquivRealComplex
        v w hw hvReal hwComplex
    calc
      Nat.card
          (HerbrandH0
            (absoluteValueDecompositionGroup K w.1)
            (LocalizedCompletion v.1 u)ˣ) =
          Nat.card (NormQuotient ℝ ℂ) :=
        Nat.card_congr
          (eH0.trans
            (eCompletion.trans eRealComplex)).toEquiv
      _ = 2 := realComplexNormQuotient_card_eq_two

omit [NumberField L] in
/-- Complete archimedean local class-field axiom, in the exact form
used in the relative-idele Herbrand quotient: Hilbert 90 gives
`#H⁻¹ = 1`, while the norm quotient gives the local degree in `H⁰`. -/
theorem infinitePlaceLocalClassAxiom_cards
    (v : InfinitePlace K) (w : InfinitePlace L)
    (hw : w.comap (algebraMap K L) = v)
    (σ : L ≃ₐ[K] L)
    (hgen : ∀ τ : L ≃ₐ[K] L,
      τ ∈ Subgroup.zpowers σ) :
    let u :=
      infinitePlaceAbsoluteValueExtension v w hw
    letI hL :=
      AbsoluteValue.extensionCompletionAlgebra
        (K := K) u.1
    letI : SMul K u.1.Completion := hL.toSMul
    letI : Algebra v.1.Completion u.1.Completion :=
      AbsoluteValue.completionAlgebra v.1 u.1 u.2
    letI := localizedCompletionGlobalAlgebra v.1 u
    letI := localizedCompletionIsScalarTower v.1 u
    letI : FiniteDimensional v.1.Completion
        (LocalizedCompletion v.1 u) :=
      localizedCompletionModuleFinite v.1 v.isNontrivial u
    letI : IsGalois v.1.Completion
        (LocalizedCompletion v.1 u) :=
      HilbertRamification.algebraicLocalization_isGalois v.1 u
    letI : Fintype (absoluteValueDecompositionGroup K w.1) :=
      Fintype.ofFinite _
    letI : MulDistribMulAction
        (absoluteValueDecompositionGroup K w.1)
        (LocalizedCompletion v.1 u)ˣ :=
      decompositionGroupLocalUnitsAction
        v.1 v.isNontrivial u
    Nat.card
        (HerbrandHMinusOne
          (absoluteValueDecompositionGroup K w.1)
          (LocalizedCompletion v.1 u)ˣ
          (subgroupGeneratorOfGenerator
            (absoluteValueDecompositionGroup K w.1)
            σ hgen)) = 1 ∧
      Nat.card
          (HerbrandH0
            (absoluteValueDecompositionGroup K w.1)
            (LocalizedCompletion v.1 u)ˣ) =
        if w.IsUnramified K then 1 else 2 := by
  let u :=
    infinitePlaceAbsoluteValueExtension v w hw
  let hL :=
    AbsoluteValue.extensionCompletionAlgebra
      (K := K) u.1
  let : SMul K u.1.Completion := hL.toSMul
  let : Algebra v.1.Completion u.1.Completion :=
    AbsoluteValue.completionAlgebra v.1 u.1 u.2
  let := localizedCompletionGlobalAlgebra v.1 u
  let := localizedCompletionIsScalarTower v.1 u
  let : FiniteDimensional v.1.Completion
      (LocalizedCompletion v.1 u) :=
    localizedCompletionModuleFinite v.1 v.isNontrivial u
  let : IsGalois v.1.Completion
      (LocalizedCompletion v.1 u) :=
    HilbertRamification.algebraicLocalization_isGalois v.1 u
  let : Fintype (absoluteValueDecompositionGroup K w.1) :=
    Fintype.ofFinite _
  let : MulDistribMulAction
      (absoluteValueDecompositionGroup K w.1)
      (LocalizedCompletion v.1 u)ˣ :=
    decompositionGroupLocalUnitsAction
      v.1 v.isNontrivial u
  exact
    ⟨localHerbrandHMinusOne_card_eq_one_of_absoluteValue
        v.1 v.isNontrivial u σ hgen,
      infinitePlaceLocalHerbrandH0_card_eq_localDegree
        v w hw⟩

omit [NumberField L] in
/-- Finiteness of the archimedean degree-zero local Herbrand group,
deduced from its explicit nonzero cardinality. -/
theorem infinitePlaceLocalHerbrandH0Finite
    (v : InfinitePlace K) (w : InfinitePlace L)
    (hw : w.comap (algebraMap K L) = v) :
    let u :=
      infinitePlaceAbsoluteValueExtension v w hw
    letI : Fintype (absoluteValueDecompositionGroup K w.1) :=
      Fintype.ofFinite _
    letI : MulDistribMulAction
        (absoluteValueDecompositionGroup K w.1)
        (LocalizedCompletion v.1 u)ˣ :=
      decompositionGroupLocalUnitsAction
        v.1 v.isNontrivial u
    Finite
      (HerbrandH0
        (absoluteValueDecompositionGroup K w.1)
        (LocalizedCompletion v.1 u)ˣ) := by
  let u :=
    infinitePlaceAbsoluteValueExtension v w hw
  let hL :=
    AbsoluteValue.extensionCompletionAlgebra
      (K := K) u.1
  let : SMul K u.1.Completion := hL.toSMul
  let : Algebra v.1.Completion u.1.Completion :=
    AbsoluteValue.completionAlgebra v.1 u.1 u.2
  let := localizedCompletionGlobalAlgebra v.1 u
  let := localizedCompletionIsScalarTower v.1 u
  let : FiniteDimensional v.1.Completion
      (LocalizedCompletion v.1 u) :=
    localizedCompletionModuleFinite v.1 v.isNontrivial u
  let : IsGalois v.1.Completion
      (LocalizedCompletion v.1 u) :=
    HilbertRamification.algebraicLocalization_isGalois v.1 u
  let : Fintype (absoluteValueDecompositionGroup K w.1) :=
    Fintype.ofFinite _
  let : MulDistribMulAction
      (absoluteValueDecompositionGroup K w.1)
      (LocalizedCompletion v.1 u)ˣ :=
    decompositionGroupLocalUnitsAction
      v.1 v.isNontrivial u
  change
    Finite
      (HerbrandH0
        (absoluteValueDecompositionGroup K w.1)
        (LocalizedCompletion v.1 u)ˣ)
  by_cases hUnramified : w.IsUnramified K
  · have hGroup :
        Nat.card (absoluteValueDecompositionGroup K w.1) = 1 := by
      rw [absoluteValueDecompositionGroup_eq_infinitePlaceStabilizer w,
        InfinitePlace.card_stabilizer, ite_eq_left hUnramified]
    let : Subsingleton (absoluteValueDecompositionGroup K w.1) :=
      (Nat.card_eq_one_iff_unique.mp hGroup).1
    let :
        Subsingleton
          (HerbrandH0
            (absoluteValueDecompositionGroup K w.1)
            (LocalizedCompletion v.1 u)ˣ) :=
      herbrandH0_subsingleton_of_fixed_le_tateNormSubgroup
        (G := absoluteValueDecompositionGroup K w.1)
        (A := (LocalizedCompletion v.1 u)ˣ) (by
          intro a ha
          refine ⟨a, ?_⟩
          rw [tateNormHom_apply]
          unfold tateNorm
          classical
          have huniv :
              (Finset.univ :
                Finset (absoluteValueDecompositionGroup K w.1)) =
                {1} := by
            ext g
            simp [Subsingleton.elim g 1]
          rw [huniv]
          simp)
    exact
      Finite.of_injective
        (fun _ :
          HerbrandH0
            (absoluteValueDecompositionGroup K w.1)
            (LocalizedCompletion v.1 u)ˣ => false)
        (fun x y _ => Subsingleton.elim x y)
  · have hRamified : w.IsRamified K := hUnramified
    have hvReal : v.IsReal := by
      rw [← hw]
      exact hRamified.isReal
    have hwComplex : w.IsComplex :=
      hRamified.isComplex
    let eH0 :=
      localHerbrandH0EquivNormQuotient
        v.1 v.isNontrivial u
    let eCompletion :=
      localizedCompletionNormQuotientEquivAbsoluteCompletions
        v w hw
    let eRealComplex :=
      absoluteCompletionNormQuotientEquivRealComplex
        v w hw hvReal hwComplex
    exact
      Finite.of_equiv
        (NormQuotient ℝ ℂ)
        (eH0.trans
          (eCompletion.trans eRealComplex)).symm.toEquiv

end LocalClassFieldTheory
end
end

section
-- module Solutions.OAIQ244_DUKE.AlgebraicNumberTheory_Idele_Cohomology_SPlaces_LocalBlocks
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalCyclotomicCompletionAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.residueFieldZModAlgebra _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedIntegralAlgebraContextValuationSubringAlgebra _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.LubinTate.compatibleGroupFamiliesGroup _root_.OAI.PrimeDegreePackets.diagonalLogAction _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.CyclicCohomology.binaryCoefficientFamilyCommGroup _root_.LocalClassFieldTheory.normalizationIntegerRingIsIntegralClosure _root_.chosenFinitePlaceCompletionAlgebra _root_.chosenFinitePlaceCompletionContinuousSMul _root_.chosenFinitePlaceCompletionFiniteDimensional _root_.chosenFinitePlaceCompletionLocallyCompactSpace _root_.chosenFinitePlaceLocalizedFiniteDimensional _root_.chosenFinitePlaceLocalizedIntegerAlgebra _root_.chosenFinitePlaceLocalizedIntegerModuleFinite _root_.chosenFinitePlaceLocalizedIsGalois _root_.chosenFinitePlaceLocalizedIsIntegralClosure _root_.chosenFinitePlaceLocalizedIsNonarchimedeanLocalField _root_.chosenFinitePlaceLocalizedIsValuativeTopology _root_.chosenFinitePlaceLocalizedLocallyCompactSpace _root_.chosenFinitePlaceLocalizedValuationCompatible _root_.chosenFinitePlaceLocalizedValuationHasExtension _root_.chosenFinitePlaceLocalizedValuationIsNontrivial _root_.chosenFinitePlaceLocalizedValuativeRel _root_.chosenFinitePlaceLocalizedValuativeRelIsNontrivial _root_.chosenFinitePlaceLocalizedValued _root_.scaledRelativeIntegerLatticeQuotientFinite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

/-!
# The local blocks occurring in a relative `S`-idele

For a finite set `S` of finite places, the unrestricted factors consist
of every infinite place and the finite places in `S`.  This file packages
those two kinds of concrete tensor factors into one finite dependent
family and identifies it equivariantly with the induced local blocks of
the local tensor decomposition.
-/

open scoped NumberField TensorProduct
open NumberField IsDedekindDomain

noncomputable section

open LocalClassFieldTheory
open AlgebraicNumberTheory.Valuations
open CyclicCohomology
open HilbertRamification

variable {K L : Type}
    [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]

/-- The componentwise local tensor equivalence for every unrestricted place in `S`. -/
noncomputable def
    relativeUnrestrictedSPlaceFactorsEquivLocalBlockFamily
    (S : Finset (HeightOneSpectrum (𝓞 K))) :
    RelativeUnrestrictedSPlaceFactors
        (K := K) (L := L) S ≃*
      LocalBlockFamily
        (relativeUnrestrictedSPlaceDatum
          (K := K) (L := L) S) :=
  MulEquiv.piCongrRight fun i => by
    cases i with
    | inl v =>
        exact
          infinitePlaceTensorUnitsEquivLocalPlaceBlock
            (K := K) (L := L) v v.isNontrivial
            (infinitePlaceAbsoluteValueExtension
              v (chosenInfinitePlaceAbove (L := L) v)
              (chosenInfinitePlaceAbove_comap
                (L := L) v))
    | inr v =>
        exact
          finitePlaceTensorUnitsEquivLocalPlaceBlock
            (K := K) (L := L) v.1
            (chosenFinitePlaceExtension
              (L := L) v.1)

omit [NumberField L] in
/-- The unrestricted-factor realization is equivariant for the full
global Galois action. -/
theorem
    relativeUnrestrictedSPlaceFactorsEquivLocalBlockFamily_smul
    (S : Finset (HeightOneSpectrum (𝓞 K)))
    (σ : L ≃ₐ[K] L)
    (z : RelativeUnrestrictedSPlaceFactors
      (K := K) (L := L) S) :
    relativeUnrestrictedSPlaceFactorsEquivLocalBlockFamily
        (K := K) (L := L) S
        ((relativeUnrestrictedSPlaceFactorsAction
          (K := K) (L := L) S).smul σ z) =
      (localBlockFamilyAction
          (relativeUnrestrictedSPlaceDatum
            (K := K) (L := L) S)).smul σ
        (relativeUnrestrictedSPlaceFactorsEquivLocalBlockFamily
          (K := K) (L := L) S z) := by
  funext i
  cases i with
  | inl v =>
      let u :=
        infinitePlaceAbsoluteValueExtension
          v (chosenInfinitePlaceAbove (L := L) v)
          (chosenInfinitePlaceAbove_comap (L := L) v)
      let :=
        scalarTensorUnitsAction
          (K := K) (L := L) (A := v.Completion)
      let :=
        decompositionGroupLocalUnitsAction
          v.1 v.isNontrivial u
      let : MulDistribMulAction (L ≃ₐ[K] L)
          (LocalPlaceBlock v.1 v.isNontrivial u) :=
        inducedMulDistribMulAction
          (absoluteValueDecompositionGroup K u.1)
      change
        infinitePlaceTensorUnitsEquivLocalPlaceBlock
            (K := K) (L := L) v v.isNontrivial u
            (σ • z (Sum.inl v)) =
          σ •
            infinitePlaceTensorUnitsEquivLocalPlaceBlock
              (K := K) (L := L) v v.isNontrivial u
              (z (Sum.inl v))
      exact
        infinitePlaceTensorUnitsEquivLocalPlaceBlock_smul
          (K := K) (L := L) v v.isNontrivial u
          σ (z (Sum.inl v))
  | inr v =>
      let u := chosenFinitePlaceExtension (L := L) v.1
      let :=
        scalarTensorUnitsAction
          (K := K) (L := L) (A := v.1.adicCompletion K)
      let :=
        decompositionGroupLocalUnitsAction
          (HeightOneSpectrum.adicAbv K v.1)
          (RayClass.adicAbv_isNontrivial v.1) u
      let : MulDistribMulAction (L ≃ₐ[K] L)
          (LocalPlaceBlock
            (HeightOneSpectrum.adicAbv K v.1)
            (RayClass.adicAbv_isNontrivial v.1) u) :=
        inducedMulDistribMulAction
          (absoluteValueDecompositionGroup K u.1)
      change
        finitePlaceTensorUnitsEquivLocalPlaceBlock
            (K := K) (L := L) v.1 u
            (σ • z (Sum.inr v)) =
          σ •
            finitePlaceTensorUnitsEquivLocalPlaceBlock
              (K := K) (L := L) v.1 u
              (z (Sum.inr v))
      exact
        finitePlaceTensorUnitsEquivLocalPlaceBlock_smul
          (K := K) (L := L) v.1 u
          σ (z (Sum.inr v))
end
end

section
-- module Solutions.OAIQ244_DUKE.AlgebraicNumberTheory_Idele_Cohomology_SPlaces_Herbrand_Local
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalCyclotomicCompletionAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitQuotientCarrier_finite _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.residueFieldZModAlgebra _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedIntegralAlgebraContextValuationSubringAlgebra _root_.LocalFieldTheory.DiscreteValuationField.finite_nsmulAddKernel_padicInt_pi _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_multiplicative_nthPowerKernel _root_.LocalFieldTheory.finite_nsmulAddKernel_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.LubinTate.compatibleGroupFamiliesGroup _root_.OAI.PrimeDegreePackets.boundedRealFields_finite _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.CyclicCohomology.binaryCoefficientFamilyCommGroup _root_.LocalClassFieldTheory.normalizationIntegerRingIsIntegralClosure
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
/-- Every local degree-zero Herbrand group in the unrestricted family is
finite. -/
theorem relativeUnrestrictedLocalHerbrandH0Finite
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
    Finite
      (HerbrandH0
        (absoluteValueDecompositionGroup K (d i).extension.1)
        (LocalizedCompletion
          (d i).base (d i).extension)ˣ) := by
  cases i with
  | inl v =>
      exact
        infinitePlaceLocalHerbrandH0Finite
          v (chosenInfinitePlaceAbove (L := L) v)
          (chosenInfinitePlaceAbove_comap
            (L := L) v)
  | inr v =>
      let vK := HeightOneSpectrum.adicAbv K v.1
      let hvK := RayClass.adicAbv_isNontrivial v.1
      exact
        localHerbrandH0Finite
          vK hvK
          (chosenFinitePlaceExtension
            (L := L) v.1)
          σ hgen

omit [NumberField L] in
/-- Every local degree-minus-one Herbrand group in the unrestricted
family is finite. -/
theorem relativeUnrestrictedLocalHerbrandHMinusOneFinite
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
    Finite
      (HerbrandHMinusOne
        (absoluteValueDecompositionGroup K (d i).extension.1)
        (LocalizedCompletion
          (d i).base (d i).extension)ˣ
        (subgroupGeneratorOfGenerator
          (absoluteValueDecompositionGroup K
            (d i).extension.1)
          σ hgen)) := by
  cases i with
  | inl v =>
      exact
        infinitePlaceLocalHerbrandHMinusOneFinite
          v (chosenInfinitePlaceAbove (L := L) v)
          (chosenInfinitePlaceAbove_comap
            (L := L) v)
          σ hgen
  | inr v =>
      let vK := HeightOneSpectrum.adicAbv K v.1
      let hvK := RayClass.adicAbv_isNontrivial v.1
      exact
        localHerbrandHMinusOneFinite
          vK hvK
          (chosenFinitePlaceExtension
            (L := L) v.1)
          σ hgen

omit [NumberField L] in
/-- Every local degree-minus-one term has cardinality one. -/
theorem relativeUnrestrictedLocalHerbrandHMinusOne_card_eq_one
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
        (HerbrandHMinusOne
          (absoluteValueDecompositionGroup K
            (d i).extension.1)
          (LocalizedCompletion
            (d i).base (d i).extension)ˣ
          (subgroupGeneratorOfGenerator
            (absoluteValueDecompositionGroup K
              (d i).extension.1)
            σ hgen)) :=
      relativeUnrestrictedLocalHerbrandHMinusOneFinite
        S i σ hgen
    Nat.card
        (HerbrandHMinusOne
          (absoluteValueDecompositionGroup K
            (d i).extension.1)
          (LocalizedCompletion
            (d i).base (d i).extension)ˣ
          (subgroupGeneratorOfGenerator
            (absoluteValueDecompositionGroup K
              (d i).extension.1)
            σ hgen)) = 1 := by
  cases i with
  | inl v =>
      dsimp only [relativeUnrestrictedSPlaceDatum]
      exact
        (infinitePlaceLocalClassAxiom_cards
          v (chosenInfinitePlaceAbove (L := L) v)
          (chosenInfinitePlaceAbove_comap
            (L := L) v)
          σ hgen).1
  | inr v =>
      let vK := HeightOneSpectrum.adicAbv K v.1
      let hvK := RayClass.adicAbv_isNontrivial v.1
      dsimp only [relativeUnrestrictedSPlaceDatum]
      exact
        localHerbrandHMinusOne_card_eq_one
          vK hvK
          (chosenFinitePlaceExtension
            (L := L) v.1)
          σ hgen
end
end

section
-- module Solutions.OAIQ244_DUKE.AlgebraicNumberTheory_Idele_Cohomology_SPlaces_Herbrand_FamilyFinite
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 400000
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalCyclotomicCompletionAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.DiscreteNthRootsSubgroup.instCommGroupSubtypeUnitsMemSubgroup _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.KummerTheory.nthRootsSubgroupFintype _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitQuotientCarrier_finite _root_.LocalFieldTheory.DiscreteValuationField.finite_nsmulAddKernel_padicInt_pi _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_multiplicative_nthPowerKernel _root_.LocalFieldTheory.finite_nsmulAddKernel_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.LubinTate.compatibleGroupFamiliesCommGroup _root_.LubinTate.compatibleGroupFamiliesGroup _root_.OAI.PrimeDegreePackets.boundedRealFields_finite _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.CyclicCohomology.binaryCoefficientFamilyCommGroup _root_.LocalClassFieldTheory.normalizationIntegerRingIsIntegralClosure
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

/-!
# Finite unrestricted local-block families

This leaf assembles the local Herbrand calculations over the finite family of
unrestricted places.
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
/-- Degree-zero cohomology of the finite family of unrestricted local
blocks is finite. -/
theorem relativeUnrestrictedLocalBlockFamilyHerbrandH0Finite
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
    Finite
      (HerbrandH0 (L ≃ₐ[K] L)
        (LocalBlockFamily d)) := by
  let d :=
    relativeUnrestrictedSPlaceDatum
      (K := K) (L := L) S
  let localAction :=
    localBlockFamilyLocalAction d
  let blockAction :=
    localBlockFamilyBlockAction d
  let familyAction :=
    localBlockFamilyCohomologyAction d
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
  exact
    Finite.of_equiv
      (∀ i,
        HerbrandH0
          (absoluteValueDecompositionGroup K
            (d i).extension.1)
          (LocalizedCompletion
            (d i).base (d i).extension)ˣ)
      (localBlockFamilyHerbrandH0Equiv
        d σ hgen).symm.toEquiv

omit [NumberField L] in
/-- Degree-minus-one cohomology of the finite family of unrestricted
local blocks is finite. -/
theorem relativeUnrestrictedLocalBlockFamilyHerbrandHMinusOneFinite
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
    Finite
      (HerbrandHMinusOne (L ≃ₐ[K] L)
        (LocalBlockFamily d) σ) := by
  let d :=
    relativeUnrestrictedSPlaceDatum
      (K := K) (L := L) S
  let localAction :=
    localBlockFamilyLocalAction d
  let blockAction :=
    localBlockFamilyBlockAction d
  let familyAction :=
    localBlockFamilyCohomologyAction d
  let decompositionFintype :=
    localBlockFamilyDecompositionFintype d
  let localFinite : ∀ i, Finite
      (HerbrandHMinusOne
        (absoluteValueDecompositionGroup K (d i).extension.1)
        (LocalizedCompletion
          (d i).base (d i).extension)ˣ
        (subgroupGeneratorOfGenerator
          (absoluteValueDecompositionGroup K
            (d i).extension.1)
          σ hgen)) :=
    fun i =>
      relativeUnrestrictedLocalHerbrandHMinusOneFinite
        S i σ hgen
  exact
    Finite.of_equiv
      (∀ i,
        HerbrandHMinusOne
          (absoluteValueDecompositionGroup K
            (d i).extension.1)
          (LocalizedCompletion
            (d i).base (d i).extension)ˣ
          (subgroupGeneratorOfGenerator
            (absoluteValueDecompositionGroup K
              (d i).extension.1)
            σ hgen))
      (localBlockFamilyHerbrandHMinusOneEquiv
        d σ hgen).symm.toEquiv
end
end

section
-- module Solutions.OAIQ244_DUKE.AlgebraicNumberTheory_Idele_Cohomology_SPlaces_Herbrand_FamilyCardinality
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 400000
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalCyclotomicCompletionAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.DiscreteNthRootsSubgroup.instCommGroupSubtypeUnitsMemSubgroup _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.KummerTheory.nthRootsSubgroupFintype _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitQuotientCarrier_finite _root_.LocalFieldTheory.DiscreteValuationField.finite_nsmulAddKernel_padicInt_pi _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_multiplicative_nthPowerKernel _root_.LocalFieldTheory.finite_nsmulAddKernel_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.LubinTate.compatibleGroupFamiliesCommGroup _root_.LubinTate.compatibleGroupFamiliesGroup _root_.OAI.PrimeDegreePackets.boundedRealFields_finite _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.CyclicCohomology.binaryCoefficientFamilyCommGroup _root_.LocalClassFieldTheory.normalizationIntegerRingIsIntegralClosure
attribute [-simp] _root_.GlobalClassFieldTheory.Reciprocity.rationalCyclotomicGlobalToLocalizedAlgHom_apply _root_.GlobalClassFieldTheory.Reciprocity.rationalCyclotomicGlobalToLocalizedAlgHom_primitiveRoot _root_.IsDiscreteValuationRing.addVal_ringEquiv _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.OAI.PrimeDegreePackets.ThetaConstruction.schwartzCM_apply _root_.doubleCosetExtension_mk _root_.extendAbsoluteValueExtensionFromIntermediate_apply _root_.finitePlaceBelow_finitePlaceExtensionCentre _root_.finitePlaceExtensionAdicCompletionRingEquiv_toCompletion _root_.finitePlaceExtensionCentreInFibre_coe _root_.finitePlaceExtensionCentre_asIdeal _root_.finitePlaceExtensionCompletionRingEquiv_toCompletion _root_.finitePlaceExtensionEquivAbove_coe _root_.finitePlaceTensorRingEquivAboveAdic_apply_extension _root_.finitePlaceTensorUnitsEquivAboveAdic_apply_extension _root_.infinitePlaceAboveEquivExtension_apply_val _root_.infinitePlaceTensorRingEquivAbove_apply _root_.infinitePlaceTensorUnitsEquivAbove_apply _root_.infinitePlace_mult_smul _root_.mem_finitePlaceDecompositionGroup_iff _root_.restrictAbsoluteValueExtensionToIntermediate_apply _root_.ringOfIntegersToFinitePlaceExtensionValuationSubring_coe
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
/-- The degree-minus-one cardinality of the unrestricted local-block
family is one. -/
theorem
    relativeUnrestrictedLocalBlockFamilyHerbrandHMinusOne_card_eq_one
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
        (HerbrandHMinusOne (L ≃ₐ[K] L)
          (LocalBlockFamily d) σ) :=
      relativeUnrestrictedLocalBlockFamilyHerbrandHMinusOneFinite
        S σ hgen
    Nat.card
        (HerbrandHMinusOne (L ≃ₐ[K] L)
          (LocalBlockFamily d) σ) = 1 := by
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
      (HerbrandHMinusOne
        (absoluteValueDecompositionGroup K (d i).extension.1)
        (LocalizedCompletion
          (d i).base (d i).extension)ˣ
        (subgroupGeneratorOfGenerator
          (absoluteValueDecompositionGroup K
            (d i).extension.1)
          σ hgen)) :=
    fun i =>
      relativeUnrestrictedLocalHerbrandHMinusOneFinite
        S i σ hgen
  let familyFinite : Finite
      (HerbrandHMinusOne (L ≃ₐ[K] L)
        (LocalBlockFamily d) σ) :=
    relativeUnrestrictedLocalBlockFamilyHerbrandHMinusOneFinite
      S σ hgen
  calc
    Nat.card
        (HerbrandHMinusOne (L ≃ₐ[K] L)
          (LocalBlockFamily d) σ) =
      Nat.card
        (∀ i,
          HerbrandHMinusOne
            (absoluteValueDecompositionGroup K
              (d i).extension.1)
            (LocalizedCompletion
              (d i).base (d i).extension)ˣ
            (subgroupGeneratorOfGenerator
              (absoluteValueDecompositionGroup K
                (d i).extension.1)
              σ hgen)) :=
      Nat.card_congr
        (localBlockFamilyHerbrandHMinusOneEquiv
          d σ hgen).toEquiv
    _ = ∏ i, Nat.card
        (HerbrandHMinusOne
          (absoluteValueDecompositionGroup K
            (d i).extension.1)
          (LocalizedCompletion
            (d i).base (d i).extension)ˣ
          (subgroupGeneratorOfGenerator
            (absoluteValueDecompositionGroup K
              (d i).extension.1)
            σ hgen)) :=
      Nat.card_pi
    _ = ∏ _i :
        RelativeUnrestrictedSPlaceIndex (K := K) S, 1 := by
      apply Finset.prod_congr rfl
      intro i _
      exact
        relativeUnrestrictedLocalHerbrandHMinusOne_card_eq_one
          S i σ hgen
    _ = 1 := by simp
end
end

section
-- module Solutions.OAIQ244_DUKE.AlgebraicNumberTheory_Idele_Cohomology_SPlaces_Herbrand_Factors
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalCyclotomicCompletionAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.DiscreteNthRootsSubgroup.instCommGroupSubtypeUnitsMemSubgroup _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.LubinTate.compatibleGroupFamiliesCommGroup _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.CyclicCohomology.binaryCoefficientFamilyCommGroup _root_.LocalClassFieldTheory.normalizationIntegerRingIsIntegralClosure
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
/-- The equivariant realization by local blocks identifies degree-zero
Herbrand cohomology of the actual unrestricted factors with that of the
local-block family. -/
noncomputable def
    relativeUnrestrictedSPlaceFactorsHerbrandH0EquivLocalBlockFamily
    (S : Finset (HeightOneSpectrum (𝓞 K))) :
    @HerbrandH0 (L ≃ₐ[K] L)
        (RelativeUnrestrictedSPlaceFactors
          (K := K) (L := L) S)
        _ _ _
        (relativeUnrestrictedSPlaceFactorsAction
          (K := K) (L := L) S) ≃*
      @HerbrandH0 (L ≃ₐ[K] L)
        (LocalBlockFamily
          (relativeUnrestrictedSPlaceDatum
            (K := K) (L := L) S))
        _ _ _
        (localBlockFamilyAction
          (relativeUnrestrictedSPlaceDatum
            (K := K) (L := L) S)) := by
  let d :=
    relativeUnrestrictedSPlaceDatum
      (K := K) (L := L) S
  letI sourceAction :=
    relativeUnrestrictedSPlaceFactorsActionProvider
      (K := K) (L := L) S
  letI targetAction :=
    relativeUnrestrictedSPlaceLocalBlockFamilyActionProvider
      (K := K) (L := L) S
  exact
    herbrandH0EquivariantMulEquiv
      (relativeUnrestrictedSPlaceFactorsEquivLocalBlockFamily
        (K := K) (L := L) S)
      (relativeUnrestrictedSPlaceFactorsEquivLocalBlockFamily_smul
        (K := K) (L := L) S)

omit [NumberField L] in
/-- The equivariant realization by local blocks identifies degree-minus-one
Herbrand cohomology of the actual unrestricted factors with that of the
local-block family. -/
noncomputable def
    relativeUnrestrictedSPlaceFactorsHerbrandHMinusOneEquivLocalBlockFamily
    (S : Finset (HeightOneSpectrum (𝓞 K)))
    (σ : L ≃ₐ[K] L) :
    @HerbrandHMinusOne (L ≃ₐ[K] L)
        (RelativeUnrestrictedSPlaceFactors
          (K := K) (L := L) S)
        _ _ _
        (relativeUnrestrictedSPlaceFactorsAction
          (K := K) (L := L) S) σ ≃*
      @HerbrandHMinusOne (L ≃ₐ[K] L)
        (LocalBlockFamily
          (relativeUnrestrictedSPlaceDatum
            (K := K) (L := L) S))
        _ _ _
        (localBlockFamilyAction
          (relativeUnrestrictedSPlaceDatum
            (K := K) (L := L) S)) σ := by
  let d :=
    relativeUnrestrictedSPlaceDatum
      (K := K) (L := L) S
  letI sourceAction :=
    relativeUnrestrictedSPlaceFactorsActionProvider
      (K := K) (L := L) S
  letI targetAction :=
    relativeUnrestrictedSPlaceLocalBlockFamilyActionProvider
      (K := K) (L := L) S
  exact
    herbrandHMinusOneEquivariantMulEquiv
      (relativeUnrestrictedSPlaceFactorsEquivLocalBlockFamily
        (K := K) (L := L) S)
      (relativeUnrestrictedSPlaceFactorsEquivLocalBlockFamily_smul
        (K := K) (L := L) S) σ

omit [NumberField L] in
/-- Degree-zero cohomology of the actual unrestricted tensor factors is
finite. -/
theorem relativeUnrestrictedSPlaceFactorsHerbrandH0Finite
    (S : Finset (HeightOneSpectrum (𝓞 K)))
    (σ : L ≃ₐ[K] L)
    (hgen : ∀ τ : L ≃ₐ[K] L,
      τ ∈ Subgroup.zpowers σ) :
    letI :=
      relativeUnrestrictedSPlaceFactorsAction
        (K := K) (L := L) S
    Finite
      (HerbrandH0 (L ≃ₐ[K] L)
        (RelativeUnrestrictedSPlaceFactors
          (K := K) (L := L) S)) := by
  let d :=
    relativeUnrestrictedSPlaceDatum
      (K := K) (L := L) S
  let sourceAction :=
    relativeUnrestrictedSPlaceFactorsActionProvider
      (K := K) (L := L) S
  let targetAction :=
    relativeUnrestrictedSPlaceLocalBlockFamilyActionProvider
      (K := K) (L := L) S
  let targetFinite : Finite
      (HerbrandH0 (L ≃ₐ[K] L)
        (LocalBlockFamily d)) :=
    relativeUnrestrictedLocalBlockFamilyHerbrandH0Finite
      S σ hgen
  exact
    Finite.of_equiv
      (HerbrandH0 (L ≃ₐ[K] L)
        (LocalBlockFamily d))
      (relativeUnrestrictedSPlaceFactorsHerbrandH0EquivLocalBlockFamily
        (K := K) (L := L) S).symm.toEquiv

omit [NumberField L] in
/-- Degree-minus-one cohomology of the actual unrestricted tensor
factors is finite. -/
theorem relativeUnrestrictedSPlaceFactorsHerbrandHMinusOneFinite
    (S : Finset (HeightOneSpectrum (𝓞 K)))
    (σ : L ≃ₐ[K] L)
    (hgen : ∀ τ : L ≃ₐ[K] L,
      τ ∈ Subgroup.zpowers σ) :
    letI :=
      relativeUnrestrictedSPlaceFactorsAction
        (K := K) (L := L) S
    Finite
      (HerbrandHMinusOne (L ≃ₐ[K] L)
        (RelativeUnrestrictedSPlaceFactors
          (K := K) (L := L) S) σ) := by
  let d :=
    relativeUnrestrictedSPlaceDatum
      (K := K) (L := L) S
  let sourceAction :=
    relativeUnrestrictedSPlaceFactorsActionProvider
      (K := K) (L := L) S
  let targetAction :=
    relativeUnrestrictedSPlaceLocalBlockFamilyActionProvider
      (K := K) (L := L) S
  let targetFinite : Finite
      (HerbrandHMinusOne (L ≃ₐ[K] L)
        (LocalBlockFamily d) σ) :=
    relativeUnrestrictedLocalBlockFamilyHerbrandHMinusOneFinite
      S σ hgen
  exact
    Finite.of_equiv
      (HerbrandHMinusOne (L ≃ₐ[K] L)
        (LocalBlockFamily d) σ)
      (relativeUnrestrictedSPlaceFactorsHerbrandHMinusOneEquivLocalBlockFamily
        (K := K) (L := L) S σ).symm.toEquiv
end
end

section
-- module Solutions.OAIQ244_DUKE.AlgebraicNumberTheory_Idele_Cohomology_SPlaces_OutsideIntegralInduced_ChosenPlaceIntegralBlockTensorSmul
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 400000
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalCyclotomicCompletionAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.residueFieldZModAlgebra _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedIntegralAlgebraContextValuationSubringAlgebra _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.LubinTate.compatibleGroupFamiliesGroup _root_.OAI.PrimeDegreePackets.diagonalLogAction _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.CyclicCohomology.binaryCoefficientFamilyCommGroup _root_.CyclicCohomology.instMulDistribMulActionBinaryCoefficientFamily _root_.LocalClassFieldTheory.normalizationIntegerRingIsIntegralClosure _root_.relativeUnrestrictedSPlaceFactorCommGroup
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

/-!
# Equivariance of the integral tensor block

This file proves equivariance of the finite-place tensor-unit block under the
restricted global Galois action.
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
/-- The local-place block equivalence intertwines the restricted integral
tensor action with the global Galois action. -/
theorem
    finitePlaceTensorUnitsEquivLocalPlaceBlock_restricted_smul
    (w₀ : HeightOneSpectrum (𝓞 K))
    (τ : L ≃ₐ[K] L)
    (x : relativeLocalTensorDecompositionIntegralUnitSubgroup
      (K := K) (L := L) w₀) :
    letI :=
      relativeLocalTensorDecompositionIntegralUnitSubgroupAction
        (K := K) (L := L) w₀
    finitePlaceTensorUnitsEquivLocalPlaceBlock
        (K := K) (L := L) w₀
        (chosenFinitePlaceExtension (L := L) w₀)
        (((τ • x :
            relativeLocalTensorDecompositionIntegralUnitSubgroup
              (K := K) (L := L) w₀)) :
          (w₀.adicCompletion K ⊗[K] L)ˣ) =
      τ •
        finitePlaceTensorUnitsEquivLocalPlaceBlock
          (K := K) (L := L) w₀
          (chosenFinitePlaceExtension (L := L) w₀)
          (x : (w₀.adicCompletion K ⊗[K] L)ˣ) := by
  let :=
    relativeLocalTensorDecompositionIntegralUnitSubgroupAction
      (K := K) (L := L) w₀
  let tensorUnitsAction :=
    scalarTensorUnitsAction
      (K := K) (L := L) (A := w₀.adicCompletion K)
  calc
    finitePlaceTensorUnitsEquivLocalPlaceBlock
        (K := K) (L := L) w₀
        (chosenFinitePlaceExtension (L := L) w₀)
        (((τ • x :
            relativeLocalTensorDecompositionIntegralUnitSubgroup
              (K := K) (L := L) w₀)) :
          (w₀.adicCompletion K ⊗[K] L)ˣ) =
      finitePlaceTensorUnitsEquivLocalPlaceBlock
        (K := K) (L := L) w₀
        (chosenFinitePlaceExtension (L := L) w₀)
        (τ • (x : (w₀.adicCompletion K ⊗[K] L)ˣ)) :=
      congrArg
        (finitePlaceTensorUnitsEquivLocalPlaceBlock
          (K := K) (L := L) w₀
          (chosenFinitePlaceExtension (L := L) w₀))
        (relativeLocalTensorDecompositionIntegralUnitSubgroupAction_coe
          (K := K) (L := L) w₀ τ x)
    _ = τ •
        finitePlaceTensorUnitsEquivLocalPlaceBlock
          (K := K) (L := L) w₀
          (chosenFinitePlaceExtension (L := L) w₀)
          (x : (w₀.adicCompletion K ⊗[K] L)ˣ) :=
      finitePlaceTensorUnitsEquivLocalPlaceBlock_smul
        (K := K) (L := L) w₀
        (chosenFinitePlaceExtension (L := L) w₀) τ
        (x : (w₀.adicCompletion K ⊗[K] L)ˣ)

end ChosenFinitePlace
end
end

section
-- module Solutions.OAIQ244_DUKE.AlgebraicNumberTheory_Idele_Relative_SPlaces
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.residueFieldZModAlgebra _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedIntegralAlgebraContextValuationSubringAlgebra _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.LubinTate.compatibleGroupFamiliesGroup _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.LocalClassFieldTheory.normalizationIntegerRingIsIntegralClosure _root_.chosenFinitePlaceCompletionAlgebra
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

omit [NumberField L] [IsGalois K L] in
/-- All local components determine a supported relative idele. -/
theorem relativeIdeleSupportedComponents_injective
    (S : Finset (HeightOneSpectrum (𝓞 K))) :
    Function.Injective
      (relativeIdeleSupportedComponents
        (K := K) (L := L) S) := by
  intro x y hxy
  apply Subtype.ext
  apply relativeIdeleLocalComponents_injective
  apply Prod.ext
  · funext w
    exact congrArg (fun q => q.1 w) hxy
  · funext w
    by_cases hw : w ∈ S
    · exact
        congrArg
          (fun q => q.2.1
            (⟨w, hw⟩ :
              {w : HeightOneSpectrum (𝓞 K) // w ∈ S}))
          hxy
    · exact
        congrArg Subtype.val
          (congrArg
            (fun q => q.2.2
              (⟨w, hw⟩ :
                {w : HeightOneSpectrum (𝓞 K) // w ∉ S}))
            hxy)

omit [IsGalois K L] in
/-- Every complete family of local factors is realized by a supported
relative idele. -/
theorem relativeIdeleSupportedComponents_surjective
    (S : Finset (HeightOneSpectrum (𝓞 K))) :
    Function.Surjective
      (relativeIdeleSupportedComponents
        (K := K) (L := L) S) := by
  intro x
  refine
    ⟨relativeIdeleOfSPlaceFactors
        (K := K) (L := L) S x, ?_⟩
  apply Prod.ext
  · funext w
    exact
      relativeIdeleOfSPlaceFactors_infiniteComponent
        (K := K) (L := L) S x w
  · apply Prod.ext
    · funext w
      exact
        relativeIdeleOfSPlaceFactors_finiteComponent_inside
          (K := K) (L := L) S x w.1 w.2
    · funext w
      apply Subtype.ext
      exact
        relativeIdeleOfSPlaceFactors_finiteComponent_outside
          (K := K) (L := L) S x w.1 w.2

/-- The exact relative finite-support decomposition:

`I_{L/K}^S` is the product of all archimedean tensor-unit factors,
the unrestricted finite tensor-unit factors over `S`, and the genuine
valuation-ring unit factors away from `S`. -/
noncomputable def relativeIdeleSupportedEquivSPlaceFactors
    (S : Finset (HeightOneSpectrum (𝓞 K))) :
    relativeIdeleLocalTensorDecompositionSupportedSubgroup
        (K := K) (L := L) S ≃*
      RelativeIdeleSPlaceFactors (K := K) (L := L) S :=
  MulEquiv.ofBijective
    (relativeIdeleSupportedComponents
      (K := K) (L := L) S)
    ⟨relativeIdeleSupportedComponents_injective
        (K := K) (L := L) S,
      relativeIdeleSupportedComponents_surjective
        (K := K) (L := L) S⟩
end
end

section
-- module Solutions.OAIQ244_DUKE.AlgebraicNumberTheory_Ramification_Splitting_FinitePlaceIdeal
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalCyclotomicCompletionAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.residueFieldZModAlgebra _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedIntegralAlgebraContextValuationSubringAlgebra _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.LocalClassFieldTheory.normalizationIntegerRingIsIntegralClosure _root_.chosenFinitePlaceCompletionAlgebra _root_.chosenFinitePlaceCompletionContinuousSMul _root_.chosenFinitePlaceCompletionFiniteDimensional _root_.chosenFinitePlaceCompletionLocallyCompactSpace _root_.chosenFinitePlaceLocalizedFiniteDimensional _root_.chosenFinitePlaceLocalizedIntegerAlgebra _root_.chosenFinitePlaceLocalizedIntegerModuleFinite _root_.chosenFinitePlaceLocalizedIsGalois _root_.chosenFinitePlaceLocalizedIsIntegralClosure _root_.chosenFinitePlaceLocalizedIsNonarchimedeanLocalField _root_.chosenFinitePlaceLocalizedIsValuativeTopology _root_.chosenFinitePlaceLocalizedLocallyCompactSpace _root_.chosenFinitePlaceLocalizedValuationCompatible _root_.chosenFinitePlaceLocalizedValuationHasExtension _root_.chosenFinitePlaceLocalizedValuationIsNontrivial _root_.chosenFinitePlaceLocalizedValuativeRel _root_.chosenFinitePlaceLocalizedValuativeRelIsNontrivial _root_.chosenFinitePlaceLocalizedValued
attribute [-simp] _root_.GlobalClassFieldTheory.Reciprocity.rationalCyclotomicGlobalToLocalizedAlgHom_apply _root_.GlobalClassFieldTheory.Reciprocity.rationalCyclotomicGlobalToLocalizedAlgHom_primitiveRoot _root_.IsDiscreteValuationRing.addVal_ringEquiv _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.OAI.PrimeDegreePackets.ThetaConstruction.schwartzCM_apply _root_.doubleCosetExtension_mk _root_.extendAbsoluteValueExtensionFromIntermediate_apply _root_.finitePlaceExtensionAdicCompletionRingEquiv_toCompletion _root_.finitePlaceExtensionCompletionRingEquiv_toCompletion _root_.finitePlaceTensorRingEquivAboveAdic_apply_extension _root_.finitePlaceTensorUnitsEquivAboveAdic_apply_extension _root_.infinitePlaceAboveEquivExtension_apply_val _root_.infinitePlaceTensorRingEquivAbove_apply _root_.infinitePlaceTensorUnitsEquivAbove_apply
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

omit [FiniteDimensional K L] [IsGalois K L] in
/-- The decomposition group of an exact finite-place extension is the
stabilizer of its centre prime. -/
theorem absoluteValueDecompositionGroup_eq_finitePlaceStabilizer
    (v : HeightOneSpectrum (𝓞 K))
    (w : AbsoluteValueExtension
      (HeightOneSpectrum.adicAbv K v) L) :
    letI := finitePlaceMulAction K L
    absoluteValueDecompositionGroup K w.1 =
      MulAction.stabilizer (L ≃ₐ[K] L)
        (finitePlaceExtensionCentre (K := K) (L := L) v w) := by
  let := finitePlaceMulAction K L
  ext σ
  rw [mem_absoluteValueDecompositionGroup_iff_extensionConjugate_eq
      (HeightOneSpectrum.adicAbv K v)
      (RayClass.adicAbv_isNontrivial v) w σ]
  simp only [MulAction.mem_stabilizer_iff]
  change
    absoluteValueExtensionConjugate
        (HeightOneSpectrum.adicAbv K v) w σ = w ↔
      finitePlaceEquiv K L σ
          (finitePlaceExtensionCentre (K := K) (L := L) v w) =
        finitePlaceExtensionCentre (K := K) (L := L) v w
  constructor
  · intro h
    have hc := congrArg
      (finitePlaceExtensionCentre (K := K) (L := L) v) h
    rw [finitePlaceExtensionCentre_conjugate] at hc
    calc
      finitePlaceEquiv K L σ
          (finitePlaceExtensionCentre (K := K) (L := L) v w) =
          finitePlaceEquiv K L σ
            (finitePlaceEquiv K L σ⁻¹
              (finitePlaceExtensionCentre (K := K) (L := L) v w)) :=
        congrArg (finitePlaceEquiv K L σ) hc.symm
      _ = finitePlaceExtensionCentre (K := K) (L := L) v w := by
        rw [← finitePlaceEquiv_mul]
        simp
  · intro h
    apply finitePlaceExtensionCentre_injective
      (K := K) (L := L) v
    rw [finitePlaceExtensionCentre_conjugate]
    calc
      finitePlaceEquiv K L σ⁻¹
          (finitePlaceExtensionCentre (K := K) (L := L) v w) =
          finitePlaceEquiv K L σ⁻¹
            (finitePlaceEquiv K L σ
              (finitePlaceExtensionCentre (K := K) (L := L) v w)) :=
        congrArg (finitePlaceEquiv K L σ⁻¹) h.symm
      _ = finitePlaceExtensionCentre (K := K) (L := L) v w := by
        rw [← finitePlaceEquiv_mul]
        simp
end
end

section
-- module Solutions.OAIQ244_DUKE.AlgebraicNumberTheory_Ramification_Splitting_NormalClosure
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitQuotientCarrier_finite _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.residueFieldZModAlgebra _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedIntegralAlgebraContextValuationSubringAlgebra _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.PrimeDegreePackets.boundedRealFields_finite _root_.OAI.PrimeDegreePackets.diagonalLogAction _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.LocalClassFieldTheory.normalizationIntegerRingIsIntegralClosure _root_.chosenFinitePlaceCompletionAlgebra
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

section GaloisSplittingBridge

variable
    {K E : Type}
    [Field K] [NumberField K]
    [Field E] [Algebra K E]
    [FiniteDimensional K E]
    [IsGalois K E]

/-- For a finite Galois extension, complete splitting defined by the
chosen decomposition group is equivalent to intrinsic complete
splitting by the number of extensions of the place. -/
theorem finitePlaceSplitsCompletely_iff_inExtension
    (v : HeightOneSpectrum (𝓞 K)) :
    FinitePlaceSplitsCompletely
        (K := K) (L := E) v ↔
      FinitePlaceSplitsCompletelyInExtension
        (K := K) (E := E) v := by
  let T : IntermediateField K E := ⊤
  let e : T ≃ₐ[K] E := by
    simpa only [T] using
      (IntermediateField.topEquiv :
        (⊤ : IntermediateField K E) ≃ₐ[K] E)
  have htransport :
      FinitePlaceSplitsCompletelyInExtension
          (K := K) (E := T) v ↔
        FinitePlaceSplitsCompletelyInExtension
          (K := K) (E := E) v :=
    finitePlaceSplitsCompletelyInExtension_algEquiv e v
  constructor
  · intro hsplit
    apply htransport.mp
    apply
      (finitePlaceSplitsCompletelyInExtension_iff_doubleCoset_card_eq
        (K := K) (M := E) T v).2
    rw [hsplit]
  · intro hsplit
    have hcard :=
      (finitePlaceSplitsCompletelyInExtension_iff_doubleCoset_card_eq
        (K := K) (M := E) T v).mp
        (htransport.mpr hsplit)
    change
      finitePlaceDecompositionGroup
          (K := K) (L := E) v =
        ⊥
    exact
      (doubleCoset_card_eq_leftCoset_iff_of_normalCore_eq_bot
        T.fixingSubgroup
        (finitePlaceDecompositionGroup
          (K := K) (L := E) v)
        (by
          simpa only
            [T, IntermediateField.fixingSubgroup_top]
            using
              (Subgroup.normalCore_eq_self
                (⊥ : Subgroup (E ≃ₐ[K] E))))).mp hcard

end GaloisSplittingBridge
end
end

section
-- module Solutions.OAIQ244_DUKE.GlobalClassFieldTheory_ClassFieldAxiom_SUnitKummerPrimeSelection_FinitePlaceDecomposition
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalCyclotomicCompletionAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.residueFieldZModAlgebra _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedIntegralAlgebraContextValuationSubringAlgebra _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.LocalClassFieldTheory.normalizationIntegerRingIsIntegralClosure
attribute [-simp] _root_.GlobalClassFieldTheory.Reciprocity.rationalCyclotomicGlobalToLocalizedAlgHom_apply _root_.GlobalClassFieldTheory.Reciprocity.rationalCyclotomicGlobalToLocalizedAlgHom_primitiveRoot _root_.IsDiscreteValuationRing.addVal_ringEquiv _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.OAI.PrimeDegreePackets.ThetaConstruction.schwartzCM_apply _root_.doubleCosetExtension_mk _root_.extendAbsoluteValueExtensionFromIntermediate_apply _root_.finitePlaceAdicCompletionMap_self_apply _root_.finitePlaceExtensionAdicCompletionRingEquiv_toCompletion _root_.finitePlaceExtensionCompletionRingEquiv_toCompletion _root_.finitePlaceTensorRingEquivAboveAdic_apply_extension _root_.finitePlaceTensorUnitsEquivAboveAdic_apply_extension _root_.infinitePlaceAboveEquivExtension_apply_val _root_.infinitePlaceTensorRingEquivAbove_apply _root_.infinitePlaceTensorUnitsEquivAbove_apply _root_.relativeFiniteTensorPiMulEquiv_apply _root_.relativeFiniteTensorPiMulEquiv_symm_apply _root_.relativeFiniteTensorPiRingEquiv_apply _root_.relativeFiniteTensorPiRingEquiv_symm_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

/-!
# Finite-place decomposition groups in Galois towers

This file relates relative and absolute finite-place decomposition groups and
proves cyclicity for the decomposition group at a chosen unramified place.
The results are independent of the S-unit Kummer construction.
-/

open scoped NumberField Classical IsMulCommutative
open NumberField IsDedekindDomain

noncomputable section

namespace GlobalClassFieldTheory.ClassFieldAxiom

/-- Full relative decomposition above `q` puts every
`M`-automorphism inside the global chosen decomposition group below
`q`. -/
theorem
    restrictAutomorphismScalars_mem_finitePlaceDecompositionGroup_of_relative_eq_top
    {F M L : Type}
    [Field F] [NumberField F]
    [Field M] [NumberField M]
    [Field L] [NumberField L]
    [Algebra F M] [Algebra M L] [Algebra F L]
    [IsScalarTower F M L]
    [FiniteDimensional F L]
    [FiniteDimensional M L]
    [IsGalois F L] [IsGalois M L]
    [IsMulCommutative (L ≃ₐ[F] L)]
    (p : HeightOneSpectrum (𝓞 F))
    (q : HeightOneSpectrum (𝓞 M))
    (hq :
      _root_.finitePlaceBelow (K := F) q = p)
    (hfull :
      _root_.finitePlaceDecompositionGroup
          (K := M) (L := L) q =
        ⊤)
    (tau : L ≃ₐ[M] L) :
    RamificationTheory.HilbertRamification.ValuationSubring.restrictAutomorphismScalars
          (K := F) (M := M) tau ∈
      _root_.finitePlaceDecompositionGroup
        (K := F) (L := L) p := by
  let wM :=
    _root_.chosenFinitePlaceExtension
      (L := L) q
  let W :=
    _root_.finitePlaceExtensionCentre
      (K := M) (L := L) q wM
  have hWM :
      _root_.finitePlaceBelow (K := M) W =
        q :=
    _root_.finitePlaceBelow_finitePlaceExtensionCentre
      (K := M) (L := L) q wM
  have hWF :
      _root_.finitePlaceBelow (K := F) W =
        p := by
    rw [
      ← _root_.finitePlaceBelow_finitePlaceBelow
        (K := F) (M := M) (L := L) W,
      hWM, hq]
  let Wp :
      {W : HeightOneSpectrum (𝓞 L) //
        _root_.finitePlaceBelow (K := F) W = p} :=
    ⟨W, hWF⟩
  let wF :=
    (_root_.finitePlaceExtensionEquivAbove
      (K := F) (L := L) p).symm Wp
  have hwFcentre :
      _root_.finitePlaceExtensionCentre
          (K := F) (L := L) p wF =
        W := by
    have hh :=
      (_root_.finitePlaceExtensionEquivAbove
        (K := F) (L := L) p).apply_symm_apply Wp
    simpa only [wF, Wp, finitePlaceExtensionEquivAbove_coe] using
      congrArg
        (fun T :
          {W : HeightOneSpectrum (𝓞 L) //
            _root_.finitePlaceBelow (K := F) W = p} =>
          (T : HeightOneSpectrum (𝓞 L))) hh
  have hequiv : wM.1.IsEquiv wF.1 := by
    apply
      _root_.finitePlaceExtensions_isEquiv_of_centres_eq
        (F := M) (M := F) q p wM wF
    simpa [W] using hwFcentre.symm
  have hDvalue :
      HilbertRamification.absoluteValueDecompositionGroup
          F wM.1 =
        HilbertRamification.absoluteValueDecompositionGroup
          F wF.1 :=
    absoluteValueDecompositionGroup_eq_of_absoluteValue_isEquiv
      wM.1 wF.1 hequiv
  have hDchosen :
      HilbertRamification.absoluteValueDecompositionGroup
          F wF.1 =
        HilbertRamification.absoluteValueDecompositionGroup
          F
          (_root_.chosenFinitePlaceExtension
            (L := L) p).1 :=
    absoluteValueDecompositionGroup_eq_of_exactExtensions_of_isMulCommutative
      (HeightOneSpectrum.adicAbv F p)
      (RayClass.adicAbv_isNontrivial p)
      wF
      (_root_.chosenFinitePlaceExtension
        (L := L) p)
  have htauM :
      tau ∈
        HilbertRamification.absoluteValueDecompositionGroup
          M wM.1 := by
    change
      tau ∈
        _root_.finitePlaceDecompositionGroup
          (K := M) (L := L) q
    rw [hfull]
    exact Subgroup.mem_top tau
  let rho :=
    RamificationTheory.HilbertRamification.ValuationSubring.restrictAutomorphismScalars
      (K := F) (M := M) tau
  have hrho :
      rho ∈
        HilbertRamification.absoluteValueDecompositionGroup
          F wM.1 := by
    exact
      (HilbertRamification.decompositionGroupRestriction_mem_absoluteValueDecompositionGroup_restrictScalars_iff
          (K := F) (M := M) wM.1 tau).mpr htauM
  change
    rho ∈
      HilbertRamification.absoluteValueDecompositionGroup
        F
        (_root_.chosenFinitePlaceExtension
          (L := L) p).1
  rw [← hDchosen, ← hDvalue]
  exact hrho

end GlobalClassFieldTheory.ClassFieldAxiom
end
end

section
-- module Solutions.OAIQ244_DUKE.KummerTheory_Concrete_SUnitPreparation_SUnitLocalPowerKernel
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LubinTate.compatibleGroupFamiliesCommGroup _root_.LubinTate.compatibleGroupFamiliesGroup _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.CyclicCohomology.binaryCoefficientFamilyCommGroup _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.LocalClassFieldTheory.normalizationIntegerRingIsIntegralClosure _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.relativeUnrestrictedSPlaceFactorCommGroup
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

/-!
# The local-power kernel of S-units

The localization map on `S`-units, its kernel, its quotient by global powers, and the associated Kummer radical.
-/

open scoped NumberField Classical IsMulCommutative NNReal ValuativeRel
open NumberField IsDedekindDomain
open LocalFieldTheory

noncomputable section

namespace KummerTheory

variable {K : Type*} [Field K]
    [numberFieldK : NumberField K]

/-- The copy of `Kˢⁿ` inside the local-power kernel `Δ`. -/
def sUnitLocalPowerKernelNthPowers
    (n : ℕ+)
    (S T : Finset (HeightOneSpectrum (𝓞 K))) :
    Subgroup (sUnitLocalPowerKernel (K := K) n S T) :=
  ((powMonoidHom (n : ℕ) :
      SUnitGroup (K := K) S →*
        SUnitGroup (K := K) S).range).comap
    (sUnitLocalPowerKernel (K := K) n S T).subtype

end KummerTheory
end
end


