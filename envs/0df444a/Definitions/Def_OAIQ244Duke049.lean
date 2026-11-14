-- Prove2me | Definitions.Def_OAIQ244Duke049
-- name    : OAIQ244Duke049
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-13T06:53:42.399196+00:00
-- url     : https://prove2.me/theorems/64bcb99f-4cf7-486f-b111-446dc2299daf
-- title:
--   Definitions bundle OAIQ244Duke049 of the split of OpenAI, Equidistribution of Prime-Degree Torus Packets with Arbitrary Local Type
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.DukePrimeDegree.prime_degree_packet_measure_equidistribution_unconditional` and `OAI.DukePrimeDegree.prime_degree_packet_measures_tendsto_haar_unconditional`, carved from OpenAI's openai/math development (OpenAI, *Equidistribution of Prime-Degree Torus Packets with Arbitrary Local Type*, OpenAI Math Release, September 24, 2026, result family 15, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 84 declarations of OpenAI's Lean: 26 definitions, 1 instance and 57 theorems. The definitions and types are `LocalClassFieldTheory.chosenPrincipalUnitsNormOfUnramifiedValuationOfIsIntegralClosureApproxCorrection`, `LocalClassFieldTheory.chosenPrincipalUnitsNormOfUnramifiedValuationOfIsIntegralClosureApproxCorrectionSeq`, `LocalClassFieldTheory.galoisGroupPrincipalUnitsMulDistribMulActionOfIsIntegralClosure`, `LocalClassFieldTheory.integerUnitNormMap`, `LocalClassFieldTheory.integerUnitNormSubgroup`, `LocalClassFieldTheory.integerUnitsModPrincipalUnitsNormOfGaloisOfIsIntegralClosure`, `LocalClassFieldTheory.principalUnitsIntegerUnitsInclusion`, `LocalClassFieldTheory.principalUnitsNormExtensionSideOfIsIntegralClosure`, `LocalClassFieldTheory.principalUnitsNormOfUnramifiedValuationOfIsIntegralClosure`, `LocalClassFieldTheory.principalUnitsNormOfUnramifiedValuationOfIsIntegralClosureApproxState`, `LocalClassFieldTheory.principalUnitsNormOfUnramifiedValuationOfIsIntegralClosureApproxStep`, `LocalClassFieldTheory.principalUnitsSuccQuotNormExtensionSideOfIsIntegralClosure`, `LocalClassFieldTheory.principalUnitsSuccQuotNormOfUnramifiedValuationOfIsIntegralClosure`, `LocalClassFieldTheory.principalUnitsSuccQuotTraceOfUnramifiedValuation`, `LocalClassFieldTheory.rightCosetCompletionAlgEquiv`, `LocalClassFieldTheory.valuationModDegree`, `LocalClassFieldTheory.valuationModDegreeMulHom`, `LubinTate.SameUniformizer.standardFormalGroupPowerSeries`, `RelativeUnrestrictedSPlaceFactor`, `RelativeUnrestrictedSPlaceFactors`, `finitePlaceLocalTensorDecompositionIntegralUnitProductEquivPiUnits`, `relativeUnrestrictedSPlaceDatum`, `relativeUnrestrictedSPlaceFactorsAction`, `relativeUnrestrictedSPlaceFactorsActionProvider`, `relativeUnrestrictedSPlaceLocalBlockFamilyActionProvider`, `rightCosetCompletionRingEquivLocalized`.
--
--   **Sources.** They come from these modules of lean/OAI/NumberTheory, in whole or in part: `AlgebraicNumberTheory_Adele_IntegralLocalFactor`, `AlgebraicNumberTheory_Adele_RestrictedAction`, `AlgebraicNumberTheory_Idele_Cohomology_SPlaces_Herbrand_Factors`, `AlgebraicNumberTheory_Idele_Cohomology_SPlaces_LocalBlocks`, `AlgebraicNumberTheory_Idele_Cohomology_SPlaces_OutsideIntegralInduced_CompletionTransport`, `AlgebraicNumberTheory_Idele_Relative_FiniteIntegralNormPreimage`, `AlgebraicNumberTheory_Ramification_Splitting_FinitePlace`, `AlgebraicNumberTheory_Ramification_Splitting_NormalClosure`, `LocalClassFieldTheory_ClassFormation_LocalBlocks_TensorNorm`, `LocalClassFieldTheory_Finite_Existence_UnramifiedNormSubgroup`, `LocalClassFieldTheory_Finite_LocalReciprocity_TopologicalReciprocity`, `LocalClassFieldTheory_Finite_Unramified_Cohomology`, `LocalClassFieldTheory_Finite_Unramified_Norm`, `LocalClassFieldTheory_Finite_Unramified_PrincipalUnits_Basic`, `LocalClassFieldTheory_Finite_Unramified_PrincipalUnits_Lift`, `LocalClassFieldTheory_Finite_Unramified_PrincipalUnits_NormSide`, `LocalClassFieldTheory_Finite_Unramified_PrincipalUnits_Trace`, `LocalClassFieldTheory_Finite_Unramified_ResidueNorm`, `LocalField_NonarchimedeanLocalField_SeparableNormValuation`, `LubinTate_FormalModule_StandardFormalGroup`.
--
--   **Imports.** It imports the bundles `OAIQ244Duke037`, `OAIQ244Duke038`, `OAIQ244Duke039`, `OAIQ244Duke040`, `OAIQ244Duke042` and `OAIQ244Duke043` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ244Duke056`, `OAIQ244Duke057`, `OAIQ244Duke058`, `OAIQ244Duke059`, `OAIQ244Duke060` and `OAIQ244Duke061`.
-- source:
--   OpenAI, Equidistribution of Prime-Degree Torus Packets with Arbitrary Local Type, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 15; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Equidistribution-of-Prime-Degree-Torus-Packets-with-Arbitrary-Local-Type-September-24-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/NumberTheory at commit 7ef5c0c

import Mathlib
import Mathlib.Algebra.Algebra.Basic
import Mathlib.Algebra.Algebra.Pi
import Mathlib.Algebra.Algebra.Tower
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Category.ModuleCat.Basic
import Mathlib.Algebra.CharP.Algebra
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
import Mathlib.Algebra.Module.Equiv.Basic
import Mathlib.Algebra.Module.LinearMap.Polynomial
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
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.FreeModule.IdealQuotient
import Mathlib.LinearAlgebra.Quotient.Pi
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
import Mathlib.NumberTheory.NumberField.ProductFormula
import Mathlib.NumberTheory.NumberField.Units.DirichletTheorem
import Mathlib.NumberTheory.Ostrowski
import Mathlib.NumberTheory.Padics.PadicNumbers
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
import Mathlib.RingTheory.FormalGroup.Basic
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
import Mathlib.RingTheory.MvPowerSeries.Expand
import Mathlib.RingTheory.MvPowerSeries.Order
import Mathlib.RingTheory.MvPowerSeries.Substitution
import Mathlib.RingTheory.MvPowerSeries.Trunc
import Mathlib.RingTheory.Nakayama
import Mathlib.RingTheory.Norm.Basic
import Mathlib.RingTheory.Norm.Defs
import Mathlib.RingTheory.Norm.Transitivity
import Mathlib.RingTheory.Polynomial.ContentIdeal
import Mathlib.RingTheory.Polynomial.GaussLemma
import Mathlib.RingTheory.Polynomial.Vieta
import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.RingTheory.PowerSeries.Substitution
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
import Definitions.Def_OAIQ244Duke037
import Definitions.Def_OAIQ244Duke038
import Definitions.Def_OAIQ244Duke039
import Definitions.Def_OAIQ244Duke040
import Definitions.Def_OAIQ244Duke042
import Definitions.Def_OAIQ244Duke043

section
-- module Solutions.OAIQ244_DUKE.LocalField_NonarchimedeanLocalField_SeparableNormValuation
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.residueFieldZModAlgebra _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.LubinTate.Valuations.exponentialValuationSubringIsLocalRing _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionFixedSubring.instIsLocalRing _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionResidueField.instField _root_.RamificationTheory.HilbertRamification.ValuationSubring.selectedResidueField.instAlgebra _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.maximalIdealPowSuccQuotModule _root_.ValuationTheory.DiscreteValuationField.DVF.residueField.field _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.isDomain _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.isLocalRing _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.LocalClassFieldTheory.normalizationIntegerRingIsIntegralClosure _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.chosenFinitePlaceCompletionAlgebra _root_.finiteLocalUnitsOpen _root_.relativeAdeleRingIntermediateAlgebra _root_.relativeAdeleRingTopIntermediateAlgebra
set_option synthInstance.maxHeartbeats 400000
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

namespace LocalClassFieldTheory

open LocalFieldTheory

/-!
# Finite local reciprocity: normalized valuation of field norms

This file supplies the local-field calculation used when the abstract
class-formation framework is specialized to separable-closure units.  All
ramification and residue degrees below are the actual invariants of the
valuation-ring extension; no packaged norm-valuation hypothesis is assumed.
-/

noncomputable section

universe u v w

open scoped BigOperators ValuativeRel
open IsNonarchimedeanLocalField

attribute [local instance] FractionRing.liftAlgebra

/-- The Galois specialization of the finite-separable normalized norm
calculation in the finite local reciprocity construction. -/
theorem v_normUnits_eq_residue_finrank_mul_of_isGalois
    (K L : Type u)
    [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    [Field L] [ValuativeRel L] [TopologicalSpace L]
    [IsNonarchimedeanLocalField L]
    [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    [Valuation.HasExtension (ValuativeRel.valuation K)
      (ValuativeRel.valuation L)]
    [IsIntegralClosure 𝒪[L] 𝒪[K] L]
    (x : Lˣ) :
    v K (Additive.ofMul (normUnits K L x)) =
      (Module.finrank 𝓀[K] 𝓀[L] : Int) *
        v L (Additive.ofMul x) :=
  v_normUnits_eq_residue_finrank_mul_of_isSeparable K L x

end
end LocalClassFieldTheory
end

section
-- module Solutions.OAIQ244_DUKE.LocalClassFieldTheory_Finite_LocalReciprocity_TopologicalReciprocity
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.DiscreteNthRootsSubgroup.instTopologicalSpaceSubtypeUnitsMemSubgroup _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.residueFieldZModAlgebra _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.RayClass.approximationCompletionTopologicalSpace _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.LocalClassFieldTheory.normalizationIntegerRingIsIntegralClosure _root_.adicCompletionProperSpace _root_.chosenFinitePlaceCompletionAlgebra _root_.chosenFinitePlaceCompletionContinuousSMul _root_.finiteLocalUnitsOpen _root_.relativeAdeleRingIntermediateAlgebra _root_.relativeAdeleRingTopIntermediateAlgebra
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

/-- The norm map restricted to valuation-ring units upstairs. -/
def integerUnitNormMap
    (K L : Type u) [Field K] [Field L] [Algebra K L]
    [ValuativeRel L] : 𝒪[L]ˣ →* Kˣ :=
  (LocalFieldTheory.normUnits K L).comp (integerUnitsToFieldUnits L)

/-- The image of valuation-ring units under the field norm. -/
def integerUnitNormSubgroup
    (K L : Type u) [Field K] [Field L] [Algebra K L]
    [ValuativeRel L] : Subgroup Kˣ :=
  MonoidHom.range (integerUnitNormMap K L)

theorem integerUnitNormSubgroup_isCompact
    (K L : Type u) [NontriviallyNormedField K] [NormedField L]
    [NormedAlgebra K L] [FiniteDimensional K L] [CompleteSpace K]
    [ValuativeRel L] [CompactSpace 𝒪[L]] :
    IsCompact (integerUnitNormSubgroup K L : Set Kˣ) := by
  have hcontinuous : Continuous (integerUnitNormMap K L) :=
    (normUnits_continuous_of_finiteDimensional K L).comp
      (integerUnitsToFieldUnits_continuous L)
  have hcompact : IsCompact (Set.univ : Set 𝒪[L]ˣ) := isCompact_univ
  have himage := hcompact.image hcontinuous
  change IsCompact (Set.range (integerUnitNormMap K L))
  simpa only [Set.image_univ] using himage

end NormSubgroupTopology

end LocalClassFieldTheory
end
end

section
-- module Solutions.OAIQ244_DUKE.LocalClassFieldTheory_ClassFormation_LocalBlocks_TensorNorm
attribute [-instance] _root_.ClassFormation.FiniteCyclicSubextension.instFintypeQuotientSubtypeMemSubgroupFieldExtensionSubgroupField _root_.ClassFormation.FiniteUnramifiedCyclicExtension.instFintypeQuotientSubtypeMemSubgroupFieldExtensionSubgroupField _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalCyclotomicCompletionAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.residueFieldZModAlgebra _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.PrimeDegreePackets.diagonalLogAction _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionResidueField.instField _root_.RamificationTheory.HilbertRamification.ValuationSubring.selectedResidueField.instAlgebra _root_.RayClass.approximationCompletionTopologicalSpace _root_.CyclicCohomology.binaryCoefficientFamilyCommGroup _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.LocalClassFieldTheory.normalizationIntegerRingIsIntegralClosure _root_.adicCompletionProperSpace _root_.chosenFinitePlaceCompletionAlgebra _root_.chosenFinitePlaceCompletionContinuousSMul _root_.chosenFinitePlaceCompletionFiniteDimensional _root_.chosenFinitePlaceCompletionLocallyCompactSpace _root_.chosenFinitePlaceLocalizedFiniteDimensional _root_.chosenFinitePlaceLocalizedIntegerAlgebra _root_.chosenFinitePlaceLocalizedIntegerModuleFinite _root_.chosenFinitePlaceLocalizedIsGalois _root_.chosenFinitePlaceLocalizedIsIntegralClosure _root_.chosenFinitePlaceLocalizedIsNonarchimedeanLocalField _root_.chosenFinitePlaceLocalizedIsValuativeTopology _root_.chosenFinitePlaceLocalizedLocallyCompactSpace _root_.chosenFinitePlaceLocalizedValuationCompatible _root_.chosenFinitePlaceLocalizedValuationHasExtension _root_.chosenFinitePlaceLocalizedValuationIsNontrivial _root_.chosenFinitePlaceLocalizedValuativeRel _root_.chosenFinitePlaceLocalizedValuativeRelIsNontrivial _root_.chosenFinitePlaceLocalizedValued _root_.finiteLocalUnitsOpen _root_.relativeAdeleRingIntermediateAlgebra _root_.relativeAdeleRingTopIntermediateAlgebra
attribute [-simp] _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.GlobalClassFieldTheory.Reciprocity.rationalCyclotomicGlobalToLocalizedAlgHom_apply _root_.GlobalClassFieldTheory.Reciprocity.rationalCyclotomicGlobalToLocalizedAlgHom_primitiveRoot _root_.IsDiscreteValuationRing.addVal_ringEquiv _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.OAI.PrimeDegreePackets.ThetaConstruction.schwartzCM_apply _root_.doubleCosetExtension_mk _root_.extendAbsoluteValueExtensionFromIntermediate_apply _root_.finitePlaceLocalTensorDecompositionComponentRingHom_apply _root_.finitePlaceLocalTensorDecompositionComponent_add _root_.finitePlaceLocalTensorDecompositionComponent_tmul _root_.finitePlaceLocalTensorDecompositionComponent_zero _root_.finitePlaceLocalTensorDecompositionUnitsComponent_coe _root_.finitePlaceLocalTensorDecompositionUnitsEquiv_apply _root_.infinitePlaceLocalTensorAlgEquiv_tmul _root_.infinitePlace_mult_smul _root_.mem_finitePlaceDecompositionGroup_iff _root_.restrictAbsoluteValueExtensionToIntermediate_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

/-!
# The norm image of a local tensor factor

For a finite Galois extension `L / K`, the completion tensor-product theorem decomposes

`K_v ⊗[K] L`

as the product of the completions above `v`.  After choosing one extension
`w`, Galois conjugation identifies every factor with `L_w`.  Consequently
the image of the determinant norm on the tensor algebra is exactly the field
norm subgroup of `L_w / K_v`.

This is the concrete norm-subgroup form of the local calculation used in
the local-block norm calculation, and it is also the bridge between the local cohomology
calculation and multiplicative weak approximation.
-/

open scoped BigOperators TensorProduct

noncomputable section

namespace LocalClassFieldTheory

open AlgebraicNumberTheory.Valuations
open HilbertRamification
open LocalFieldTheory
open ValuationTheory.Completion

universe u

variable {K L : Type u}
    [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]

section ChosenCompletion

variable (vK : AbsoluteValue K ℝ) (hvK : vK.IsNontrivial)
    (w : AbsoluteValueExtension vK L)

/-- For a right coset of the decomposition group, conjugation followed by
the localization/completion equivalence identifies the corresponding
completion with the chosen algebraic localization. -/
noncomputable def rightCosetCompletionAlgEquiv
    (q : InducedRightCosets
      (absoluteValueDecompositionGroup K w.1)) :
    letI hK :=
      AbsoluteValue.extensionCompletionAlgebra (K := K) w.1
    letI : SMul K w.1.Completion := hK.toSMul
    letI := AbsoluteValue.completionAlgebra vK w.1 w.2
    letI :
        Algebra vK.Completion
          (rightCosetExtensionEquiv vK hvK w q).1.Completion :=
      AbsoluteValue.completionAlgebra vK
        (rightCosetExtensionEquiv vK hvK w q).1
        (rightCosetExtensionEquiv vK hvK w q).2
    (rightCosetExtensionEquiv vK hvK w q).1.Completion ≃ₐ[
      vK.Completion] LocalizedCompletion vK w := by
  letI hK :=
    AbsoluteValue.extensionCompletionAlgebra (K := K) w.1
  letI : SMul K w.1.Completion := hK.toSMul
  letI := AbsoluteValue.completionAlgebra vK w.1 w.2
  letI :
      Algebra vK.Completion
        (rightCosetExtensionEquiv vK hvK w q).1.Completion :=
    AbsoluteValue.completionAlgebra vK
      (rightCosetExtensionEquiv vK hvK w q).1
      (rightCosetExtensionEquiv vK hvK w q).2
  let eConj :
      (rightCosetExtensionEquiv vK hvK w q).1.Completion ≃ₐ[
        vK.Completion] w.1.Completion :=
    { conjugateExtensionCompletionRingEquiv
        vK w (Quotient.out q) with
      commutes' :=
        conjugateExtensionCompletionRingEquiv_algebraMap
          vK w (Quotient.out q) }
  exact eConj.trans
    (localizedCompletionEquivCompletion vK hvK w).symm

/-- Transporting a completion unit to the chosen localization preserves
its determinant norm over the completed base field. -/
theorem normUnits_rightCosetCompletionAlgEquiv
    (q : InducedRightCosets
      (absoluteValueDecompositionGroup K w.1))
    (z :
      ((rightCosetExtensionEquiv vK hvK w q).1.Completion)ˣ) :
    letI hK :=
      AbsoluteValue.extensionCompletionAlgebra (K := K) w.1
    letI : SMul K w.1.Completion := hK.toSMul
    letI := AbsoluteValue.completionAlgebra vK w.1 w.2
    letI :
        Algebra vK.Completion
          (rightCosetExtensionEquiv vK hvK w q).1.Completion :=
      AbsoluteValue.completionAlgebra vK
        (rightCosetExtensionEquiv vK hvK w q).1
        (rightCosetExtensionEquiv vK hvK w q).2
    letI : Module.Finite vK.Completion
        (rightCosetExtensionEquiv vK hvK w q).1.Completion :=
      completionModuleFinite vK hvK
        (rightCosetExtensionEquiv vK hvK w q)
    letI : Module.Finite vK.Completion
        (LocalizedCompletion vK w) :=
      localizedCompletionModuleFinite vK hvK w
    normUnits vK.Completion (LocalizedCompletion vK w)
        (Units.mapEquiv
          (rightCosetCompletionAlgEquiv
            vK hvK w q).toMulEquiv z) =
      Units.map (Algebra.norm vK.Completion) z := by
  let hK :=
    AbsoluteValue.extensionCompletionAlgebra (K := K) w.1
  let _ : SMul K w.1.Completion := hK.toSMul
  let _ := AbsoluteValue.completionAlgebra vK w.1 w.2
  let _ :
      Algebra vK.Completion
        (rightCosetExtensionEquiv vK hvK w q).1.Completion :=
    AbsoluteValue.completionAlgebra vK
      (rightCosetExtensionEquiv vK hvK w q).1
      (rightCosetExtensionEquiv vK hvK w q).2
  let _ : Module.Finite vK.Completion
      (rightCosetExtensionEquiv vK hvK w q).1.Completion :=
    completionModuleFinite vK hvK
      (rightCosetExtensionEquiv vK hvK w q)
  let _ : Module.Finite vK.Completion
      (LocalizedCompletion vK w) :=
    localizedCompletionModuleFinite vK hvK w
  apply Units.ext
  change
    Algebra.norm vK.Completion
        (rightCosetCompletionAlgEquiv vK hvK w q
          (z :
            (rightCosetExtensionEquiv
              vK hvK w q).1.Completion)) =
      Algebra.norm vK.Completion
        (z :
          (rightCosetExtensionEquiv
            vK hvK w q).1.Completion)
  exact Algebra.norm_eq_of_algEquiv
    (rightCosetCompletionAlgEquiv vK hvK w q) _

/-- The field norm of a transported coordinate is the determinant norm
of the original completion coordinate. -/
theorem normUnits_completionProductUnitsEquivRightCosets
    (p : ∀ w' : AbsoluteValueExtension vK L,
      w'.1.Completionˣ)
    (q : InducedRightCosets
      (absoluteValueDecompositionGroup K w.1)) :
    letI hK :=
      AbsoluteValue.extensionCompletionAlgebra (K := K) w.1
    letI : SMul K w.1.Completion := hK.toSMul
    letI := AbsoluteValue.completionAlgebra vK w.1 w.2
    letI : ∀ w' : AbsoluteValueExtension vK L,
        Algebra vK.Completion w'.1.Completion :=
      fun w' ↦ AbsoluteValue.completionAlgebra vK w'.1 w'.2
    letI : ∀ w' : AbsoluteValueExtension vK L,
        Module.Finite vK.Completion w'.1.Completion :=
      fun w' ↦ completionModuleFinite vK hvK w'
    letI : Module.Finite vK.Completion
        (LocalizedCompletion vK w) :=
      localizedCompletionModuleFinite vK hvK w
    normUnits vK.Completion (LocalizedCompletion vK w)
        (completionProductUnitsEquivRightCosets
          vK hvK w p q) =
      Units.map (Algebra.norm vK.Completion)
        (p (rightCosetExtensionEquiv vK hvK w q)) := by
  let hK :=
    AbsoluteValue.extensionCompletionAlgebra (K := K) w.1
  let _ : SMul K w.1.Completion := hK.toSMul
  let _ := AbsoluteValue.completionAlgebra vK w.1 w.2
  let _ : ∀ w' : AbsoluteValueExtension vK L,
      Algebra vK.Completion w'.1.Completion :=
    fun w' ↦ AbsoluteValue.completionAlgebra vK w'.1 w'.2
  let _ : ∀ w' : AbsoluteValueExtension vK L,
      Module.Finite vK.Completion w'.1.Completion :=
    fun w' ↦ completionModuleFinite vK hvK w'
  let _ : Module.Finite vK.Completion
      (LocalizedCompletion vK w) :=
    localizedCompletionModuleFinite vK hvK w
  rw [← normUnits_rightCosetCompletionAlgEquiv
    vK hvK w q
      (p (rightCosetExtensionEquiv vK hvK w q))]
  congr 1

/-- The determinant norm on `K_v ⊗[K] L` is the product of the field
norms of its coordinates after all factors have been transported to the
chosen localization. -/
theorem localTensorDetNorm_eq_prod_chosenCoordinates
    (z : (LocalTensorAlgebra (L := L) vK)ˣ) :
    letI hK :=
      AbsoluteValue.extensionCompletionAlgebra (K := K) w.1
    letI : SMul K w.1.Completion := hK.toSMul
    letI := AbsoluteValue.completionAlgebra vK w.1 w.2
    letI : ∀ w' : AbsoluteValueExtension vK L,
        Algebra vK.Completion w'.1.Completion :=
      fun w' ↦ AbsoluteValue.completionAlgebra vK w'.1 w'.2
    letI : ∀ w' : AbsoluteValueExtension vK L,
        Module.Finite vK.Completion w'.1.Completion :=
      fun w' ↦ completionModuleFinite vK hvK w'
    letI : Module.Finite vK.Completion
        (LocalizedCompletion vK w) :=
      localizedCompletionModuleFinite vK hvK w
    localTensorDetNorm (K := K) (L := L) vK z =
      ∏ q ∈ decompositionRightCosetsFinset
          (K := K) (vK := vK) (w := w),
        normUnits vK.Completion
          (LocalizedCompletion vK w)
          (localTensorUnitsEquivChosenCoordinates
            vK hvK w z q) := by
  classical
  let _ :=
    completionTensorDecomposition_extensionFintype
      (K := K) (L := L) vK hvK
  let hK :=
    AbsoluteValue.extensionCompletionAlgebra (K := K) w.1
  let _ : SMul K w.1.Completion := hK.toSMul
  let _ := AbsoluteValue.completionAlgebra vK w.1 w.2
  let _ : ∀ w' : AbsoluteValueExtension vK L,
      Algebra vK.Completion w'.1.Completion :=
    fun w' ↦ AbsoluteValue.completionAlgebra vK w'.1 w'.2
  let _ : ∀ w' : AbsoluteValueExtension vK L,
      Module.Finite vK.Completion w'.1.Completion :=
    fun w' ↦ completionModuleFinite vK hvK w'
  let _ : Module.Finite vK.Completion
      (LocalizedCompletion vK w) :=
    localizedCompletionModuleFinite vK hvK w
  apply Units.ext
  change
    Algebra.norm vK.Completion
        (z : LocalTensorAlgebra (L := L) vK) =
      ((∏ q ∈ decompositionRightCosetsFinset
          (K := K) (vK := vK) (w := w),
        normUnits vK.Completion
          (LocalizedCompletion vK w)
          (localTensorUnitsEquivChosenCoordinates
            vK hvK w z q) : vK.Completionˣ) :
        vK.Completion)
  have hnorm :=
    RelativeIdeleGroup.localNorm_units_eq_prod
      vK hvK z
  change
    Algebra.norm vK.Completion
        (z : LocalTensorAlgebra (L := L) vK) =
      ∏ w' : AbsoluteValueExtension vK L,
        Algebra.norm vK.Completion
          (completionTensorDecomposition_left
            (K := K) (L := L) vK hvK
            (z : LocalTensorAlgebra (L := L) vK) w')
    at hnorm
  rw [hnorm]
  change
    (∏ w' : AbsoluteValueExtension vK L,
      Algebra.norm vK.Completion
        (completionTensorDecomposition_left
          (K := K) (L := L) vK hvK
          (z : LocalTensorAlgebra (L := L) vK) w')) =
      Units.coeHom vK.Completion
        (∏ q ∈ decompositionRightCosetsFinset
            (K := K) (vK := vK) (w := w),
          normUnits vK.Completion
            (LocalizedCompletion vK w)
            (localTensorUnitsEquivChosenCoordinates
              vK hvK w z q))
  rw [map_prod]
  rw [show decompositionRightCosetsFinset
      (K := K) (vK := vK) (w := w) =
      Finset.univ by
    ext q
    simp]
  rw [← (rightCosetExtensionEquiv
    vK hvK w).prod_comp]
  apply Finset.prod_congr rfl
  intro q _
  have h :=
    normUnits_completionProductUnitsEquivRightCosets
      vK hvK w
      (localTensorUnitsEquivCompletionProduct vK hvK z) q
  exact (congrArg (fun x : vK.Completionˣ ↦
    (x : vK.Completion)) h).symm

/-- **Local tensor norm image.**  The determinant norm image of the local
tensor algebra is exactly the field-norm subgroup of any chosen completion
above `v`. -/
theorem localTensorNormSubgroup_eq_localNormSubgroup
    (hvK : vK.IsNontrivial) :
    letI hK :=
      AbsoluteValue.extensionCompletionAlgebra (K := K) w.1
    letI : SMul K w.1.Completion := hK.toSMul
    letI := AbsoluteValue.completionAlgebra vK w.1 w.2
    letI : Module.Finite vK.Completion
        (LocalizedCompletion vK w) :=
      localizedCompletionModuleFinite vK hvK w
    localTensorNormSubgroup (K := K) (L := L) vK =
      localNormSubgroup vK.Completion
        (LocalizedCompletion vK w) := by
  classical
  let _ :=
    completionTensorDecomposition_extensionFintype
      (K := K) (L := L) vK hvK
  let hK :=
    AbsoluteValue.extensionCompletionAlgebra (K := K) w.1
  let _ : SMul K w.1.Completion := hK.toSMul
  let _ := AbsoluteValue.completionAlgebra vK w.1 w.2
  let _ : ∀ w' : AbsoluteValueExtension vK L,
      Algebra vK.Completion w'.1.Completion :=
    fun w' ↦ AbsoluteValue.completionAlgebra vK w'.1 w'.2
  let _ : ∀ w' : AbsoluteValueExtension vK L,
      Module.Finite vK.Completion w'.1.Completion :=
    fun w' ↦ completionModuleFinite vK hvK w'
  let _ : Module.Finite vK.Completion
      (LocalizedCompletion vK w) :=
      localizedCompletionModuleFinite vK hvK w
  ext x
  change
    (∃ z : (LocalTensorAlgebra (L := L) vK)ˣ,
      localTensorDetNorm (K := K) (L := L) vK z = x) ↔
      ∃ y : (LocalizedCompletion vK w)ˣ,
        normUnits vK.Completion
          (LocalizedCompletion vK w) y = x
  constructor
  · rintro ⟨z, rfl⟩
    refine
      ⟨∏ q ∈ decompositionRightCosetsFinset
          (K := K) (vK := vK) (w := w),
        localTensorUnitsEquivChosenCoordinates
          vK hvK w z q, ?_⟩
    rw [map_prod,
      localTensorDetNorm_eq_prod_chosenCoordinates
        vK hvK w z]
  · rintro ⟨y, rfl⟩
    let q₀ : InducedRightCosets
        (absoluteValueDecompositionGroup K w.1) :=
      Quotient.mk'' (1 : L ≃ₐ[K] L)
    let f :
        InducedRightCosets
            (absoluteValueDecompositionGroup K w.1) →
          (LocalizedCompletion vK w)ˣ :=
      fun q ↦ if q₀ = q then y else 1
    let z : (LocalTensorAlgebra (L := L) vK)ˣ :=
      (localTensorUnitsEquivChosenCoordinates
        vK hvK w).symm f
    refine ⟨z, ?_⟩
    rw [localTensorDetNorm_eq_prod_chosenCoordinates
      vK hvK w z]
    change
      (∏ q ∈ decompositionRightCosetsFinset
          (K := K) (vK := vK) (w := w),
        normUnits vK.Completion
          (LocalizedCompletion vK w)
          (localTensorUnitsEquivChosenCoordinates
            vK hvK w z q)) =
        normUnits vK.Completion
          (LocalizedCompletion vK w) y
    rw [(localTensorUnitsEquivChosenCoordinates
      vK hvK w).apply_symm_apply f]
    have hq₀ :
        q₀ ∈ decompositionRightCosetsFinset
          (K := K) (vK := vK) (w := w) :=
      mem_decompositionRightCosetsFinset
        (K := K) (vK := vK) (w := w) q₀
    simpa only [f, apply_ite, map_one] using
      Finset.prod_ite_eq_of_mem
        (decompositionRightCosetsFinset
          (K := K) (vK := vK) (w := w))
        q₀
        (fun _ ↦
          normUnits vK.Completion
            (LocalizedCompletion vK w) y)
        hq₀

end ChosenCompletion

end LocalClassFieldTheory
end
end

section
-- module Solutions.OAIQ244_DUKE.AlgebraicNumberTheory_Adele_RestrictedAction
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.residueFieldZModAlgebra _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.PrimeDegreePackets.diagonalLogAction _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionResidueField.instField _root_.RamificationTheory.HilbertRamification.ValuationSubring.selectedResidueField.instAlgebra _root_.RelativeIdeleGroup.principalQuotientAction _root_.ValuationTheory.DiscreteValuationField.DVF.maximalIdealPowSuccQuotModule _root_.ValuationTheory.DiscreteValuationField.DVF.residueField.field _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.LocalClassFieldTheory.normalizationIntegerRingIsIntegralClosure _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.chosenFinitePlaceCompletionAlgebra _root_.finiteLocalUnitsOpen _root_.relativeAdeleRingIntermediateAlgebra _root_.relativeAdeleRingTopIntermediateAlgebra
attribute [-simp] _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.IsDiscreteValuationRing.addVal_ringEquiv _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.LocalFieldTheory.residueField_algebraMap_residue _root_.OAI.PrimeDegreePackets.ThetaConstruction.schwartzCM_apply _root_.RelativeIdeleGroup.Cohomology.baseIdeleClassEquivFixed_coe _root_.RelativeIdeleGroup.Cohomology.baseIdeleClassToFixed_coe _root_.RelativeIdeleGroup.Cohomology.ideleClassNorm_mk _root_.RelativeIdeleGroup.Cohomology.ideleClass_smul_mk _root_.RelativeIdeleGroup.Cohomology.relativeIdele_smul_def _root_.RelativeIdeleGroup.classInclusion_mk _root_.RelativeIdeleGroup.classNorm_mk _root_.RelativeIdeleGroup.smul_class_mk _root_.TowerRelativeIdeleGroup.classGroupEquiv_mk _root_.TowerRelativeIdeleGroup.classNorm_mk _root_.TowerRelativeIdeleGroup.norm_principalIdele _root_.TowerRelativeIdeleGroup.towerRelativeIdeleEquiv_principalIdele _root_.bottomAdeleToTower_apply _root_.compositeToBaseNormQuotient_mk _root_.fieldUnitsEquivPrincipalIdeles_coe _root_.infinitePlace_mult_smul _root_.intermediateAdeleInclusion_tmul _root_.intermediateToCompositeNormQuotient_mk _root_.pushoutNormQuotientMap_mk _root_.pushoutNormQuotientNormBack_mk _root_.pushoutTowerAdeleInclusion_tmul _root_.pushoutTowerClassInclusion_mk _root_.pushoutTowerIdeleInclusion_principalIdele _root_.topFieldToOneStep_apply _root_.topFieldToTower_apply _root_.towerRelativeAdeleFlatten_tmul _root_.towerRelativeAdeleUnflatten_tmul
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

/-!
# Galois action on the restricted local product

The Galois action on `𝔸_K ⊗[K] L` commutes with evaluation at every
place.  Consequently the exact restricted-product equivalence for
relative ideles is equivariant, and the transported action is the
coordinatewise tensor-conjugation action.
-/

open scoped NumberField TensorProduct
open NumberField IsDedekindDomain

noncomputable section


universe u v w

variable
    {K : Type u} {L : Type v}
    [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L]

omit [NumberField L] [FiniteDimensional K L] in
/-- Infinite-place evaluation commutes with Galois conjugation. -/
theorem relativeAdeleInfiniteComponent_conjugation
    (w : InfinitePlace K)
    (σ : L ≃ₐ[K] L)
    (z : RelativeAdeleRing K L) :
    relativeAdeleInfiniteComponent
        (K := K) (L := L) w
        (RelativeIdeleGroup.conjugation K L σ z) =
      scalarTensorConjugation
        (K := K) (L := L)
        (A := w.Completion) σ
        (relativeAdeleInfiniteComponent
          (K := K) (L := L) w z) := by
  induction z using OAI.tensorInductionOn with
  | tmul a x => rfl
  | add x y hx hy => simp [hx, hy]

omit [NumberField L] [FiniteDimensional K L] in
/-- The infinite local unit component map is equivariant. -/
theorem RelativeIdeleGroup.infiniteComponent_smul
    (w : InfinitePlace K)
    (σ : L ≃ₐ[K] L)
    (z : RelativeIdeleGroup K L) :
    letI := scalarTensorUnitsAction
      (K := K) (L := L) (A := w.Completion)
    RelativeIdeleGroup.infiniteComponent
        (K := K) (L := L) w (σ • z) =
      σ • RelativeIdeleGroup.infiniteComponent
        (K := K) (L := L) w z := by
  let _ := scalarTensorUnitsAction
    (K := K) (L := L) (A := w.Completion)
  apply Units.ext
  exact relativeAdeleInfiniteComponent_conjugation
    (K := K) (L := L) w σ
      (z : RelativeAdeleRing K L)
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

/-- Replace each valuation-ring unit subgroup by the intrinsic unit
group of the valuation ring. -/
noncomputable def
    finitePlaceLocalTensorDecompositionIntegralUnitProductEquivPiUnits
    (w : HeightOneSpectrum (𝓞 K)) :
    FinitePlaceLocalTensorDecompositionIntegralUnitProduct
        (K := K) (L := L) w ≃*
      ∀ wL : AbsoluteValueExtension
          (HeightOneSpectrum.adicAbv K w) L,
        (absoluteValueCompletionIntegers wL.1
          (absoluteValueExtension_isNonarchimedean
            (HeightOneSpectrum.adicAbv K w)
            (HeightOneSpectrum.isNonarchimedean_adicAbv K w)
            wL))ˣ :=
  (finitePlaceLocalTensorDecompositionIntegralUnitProductEquivPi
    (K := K) (L := L) w).trans
      (MulEquiv.piCongrRight fun wL =>
        (absoluteValueCompletionIntegers wL.1
          (absoluteValueExtension_isNonarchimedean
            (HeightOneSpectrum.adicAbv K w)
            (HeightOneSpectrum.isNonarchimedean_adicAbv K w)
            wL)).unitsEquivUnitsType)
end
end

section
-- module Solutions.OAIQ244_DUKE.LocalClassFieldTheory_Finite_Existence_UnramifiedNormSubgroup
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.LocalClassFieldTheory.normalizationIntegerRingIsIntegralClosure _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen
attribute [-simp] _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.IsDiscreteValuationRing.addVal_ringEquiv _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.LocalFieldTheory.residueField_algebraMap_residue _root_.OAI.PrimeDegreePackets.ThetaConstruction.schwartzCM_apply _root_.infinitePlace_mult_smul
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

/-!
# Unramified norm subgroups

For a nonarchimedean local field, the norm subgroup of an unramified
extension of degree n is characterized by divisibility of the normalized
valuation by n. This file packages that subgroup, its quotient map, and
the canonical identification of the quotient with ZMod n.
-/

noncomputable section

universe u

namespace LocalClassFieldTheory

/-- The normalized valuation map reduced modulo a positive or zero degree n. -/
noncomputable def valuationModDegree (K : Type u) [Field K] [ValuativeRel K]
    [TopologicalSpace K] [IsNonarchimedeanLocalField K] (n : Nat) :
    Additive Kˣ →+ ZMod n :=
  (Int.castAddHom (ZMod n)).comp (LocalFieldTheory.IsNonarchimedeanLocalField.valuationMap K)

/-- Evaluates the normalized valuation map after reduction modulo `n`. -/
@[simp]
theorem valuationModDegree_apply (K : Type u) [Field K] [ValuativeRel K]
    [TopologicalSpace K] [IsNonarchimedeanLocalField K] (n : Nat) (x : Additive Kˣ) :
    valuationModDegree K n x =
      (LocalFieldTheory.IsNonarchimedeanLocalField.valuationMap K x : ZMod n) :=
  rfl

/-- Multiplicative form of the normalized valuation map modulo a degree. -/
noncomputable def valuationModDegreeMulHom (K : Type u) [Field K] [ValuativeRel K]
    [TopologicalSpace K] [IsNonarchimedeanLocalField K] (n : Nat) :
    Kˣ →* Multiplicative (ZMod n) :=
  AddMonoidHom.toMultiplicativeRight (valuationModDegree K n)

/-- Evaluates the multiplicative form of the valuation-modulo-degree map. -/
@[simp]
theorem valuationModDegreeMulHom_apply (K : Type u) [Field K] [ValuativeRel K]
    [TopologicalSpace K] [IsNonarchimedeanLocalField K] (n : Nat) (x : Kˣ) :
    valuationModDegreeMulHom K n x =
      Multiplicative.ofAdd
        (LocalFieldTheory.IsNonarchimedeanLocalField.valuationMap K (Additive.ofMul x) : ZMod n) :=
  rfl


end LocalClassFieldTheory
end
end

section
-- module Solutions.OAIQ244_DUKE.LocalClassFieldTheory_Finite_Unramified_PrincipalUnits_NormSide
attribute [-instance] _root_.ClassFormation.DegreeData.FrobeniusFixedFieldTower.extensionNormal _root_.ClassFormation.DegreeData.GaloisSubextension.extensionSubgroup_normalInstance _root_.ClassFormation.FiniteAbstractField.toFiniteResidueAbstractField_extensionNormal _root_.ClassFormation.FiniteCyclicSubextension.instNormalSubtypeMemSubgroupFieldExtensionSubgroupField _root_.ClassFormation.FiniteGaloisSubextension.extensionSubgroup_normalInstance _root_.ClassFormation.FiniteGaloisSubextension.extensionSubgroup_over_intermediate_normalInstance _root_.ClassFormation.FiniteGaloisSubextension.intermediateField_normalInstance _root_.ClassFormation.FiniteIntermediateField.galoisRefinement_normal _root_.ClassFormation.FiniteUnramifiedCyclicExtension.instNormalSubtypeMemSubgroupFieldExtensionSubgroupField _root_.ClassFormation.conjugateExtension_normal _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.HilbertRamification.Dedekind.inertiaSubgroupOfDecomposition_normal _root_.KummerTheory.DiscreteNthRootsSubgroup.instCommGroupSubtypeUnitsMemSubgroup _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalClassFieldTheory.extensionSubgroupBase_normal _root_.LocalClassFieldTheory.finiteGaloisExtensionSubgroupOfEmbedding_normal _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.residueFieldZModAlgebra _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.LubinTate.Valuations.exponentialValuationSubringIsLocalRing _root_.LubinTate.compatibleGroupFamiliesCommGroup _root_.LubinTate.compatibleGroupFamiliesGroup _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionFixedSubring.instIsLocalRing _root_.RamificationTheory.HilbertRamification.ValuationSubring.inertiaGroup_normal _root_.RamificationTheory.HilbertRamification.ValuationSubring.ramificationGroupInInertiaAut_normal _root_.RamificationTheory.HilbertRamification.ValuationSubring.selectedResidueField.instAlgebra _root_.RayClass.Modulus.congruenceSubgroup_normal _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.maximalIdealPowSuccQuotModule _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.isDomain _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.isLocalRing _root_.CyclicCohomology.binaryCoefficientFamilyCommGroup _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.LocalClassFieldTheory.normalizationIntegerRingIsIntegralClosure _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.chosenFinitePlaceCompletionAlgebra _root_.finiteLocalUnitsOpen _root_.relativeAdeleRingIntermediateAlgebra _root_.relativeAdeleRingTopIntermediateAlgebra
attribute [-simp] _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.CyclicCohomology.galoisGroupIntegerUnitsModPrincipalUnitsMapEquivOfIsIntegralClosure_mk _root_.CyclicCohomology.integerUnitsModPrincipalUnitsAtLevelConcreteEquiv_mk _root_.CyclicCohomology.integerUnitsModPrincipalUnitsAtLevelLift_mk _root_.CyclicCohomology.integerUnitsModPrincipalUnitsAtLevelMk_eq_iff_div_mem _root_.CyclicCohomology.principalUnitsSuccQuotToIntegerUnitsModPrincipalUnitsSucc_mk _root_.IsDiscreteValuationRing.addVal_ringEquiv _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.LocalClassFieldTheory.chosenNormalBasisPrincipalUnitSequenceAsPrincipalUnits_val _root_.LocalClassFieldTheory.galoisGroupIntegerUnitsMulDistribMulActionOfIsIntegralClosure_smul _root_.LocalFieldTheory.IsNonarchimedeanLocalField.additiveIntegerUnitsToFieldUnits_apply _root_.LocalFieldTheory.IsNonarchimedeanLocalField.integerUnitOfValuationMapZero_spec _root_.LocalFieldTheory.IsNonarchimedeanLocalField.integerUnitsToFieldUnits_uniformizerUnitFactor _root_.LocalFieldTheory.maximalIdealPowMapOfUnramifiedValuation_apply _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.LocalFieldTheory.principalUnitsMapOfUnramifiedValuation_apply _root_.LocalFieldTheory.principalUnitsSuccQuotAddEquivResidueOfIrreducible_symm_apply _root_.LocalFieldTheory.principalUnitsSuccQuotAddEquivResidueOfIrreducible_symm_residue _root_.LocalFieldTheory.principalUnitsSuccQuotMapOfUnramifiedValuation_mk _root_.LocalFieldTheory.principalUnitsSuccQuotUniformizerCoordAddHom_apply _root_.LocalFieldTheory.principalUnitsSuccQuotUniformizerCoord_zero _root_.OAI.PrimeDegreePackets.ThetaConstruction.schwartzCM_apply _root_.infinitePlace_mult_smul
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false
/-! Provides the public declarations in the `LocalClassFieldTheory.Finite.Unramified.PrincipalUnits.NormSide` Lean module. -/

noncomputable section

universe u

namespace LocalClassFieldTheory

open scoped ValuativeRel
open LocalFieldTheory
open LocalFieldTheory.IsNonarchimedeanLocalField

/-- Actual integral-closure version of the integer-unit norm product formula.

This is the unramified norm calculation input that embeds `N(u)` back into `𝒪[L]` and
identifies it with the product of Galois conjugates of `u`; the Galois action
on `𝒪[L]` is produced from integral closure, not from a valuation-invariance
certificate. -/
theorem integerUnitsMap_normIntegerUnits_eq_galoisGroup_prod_of_isIntegralClosure
    (K L : Type u)
    [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
    [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]
    [IsIntegralClosure 𝒪[L] 𝒪[K] L] [LocalFieldTheory.ValuativeExtension K L]
    (u : 𝒪[L]ˣ) :
    integerUnitsMapOfValuationExtension K L (normIntegerUnits K L u) =
      Finset.univ.prod (fun σ : Gal(L / K) =>
        Units.mapEquiv
          (galoisGroupIntegerRingEquivOfIsIntegralClosure K L σ).toMulEquiv u) := by
  ext
  have hfield := mapBaseUnits_normUnits_eq_prod_gal (K := K) (L := L)
    (integerUnitsToFieldUnits L u)
  have hfield' := congrArg (fun z : Lˣ => (z : L)) hfield
  simp only [mapBaseUnitsToExtensionUnits_apply_coe, normUnits_apply_coe,
    integerUnitsToFieldUnits_apply] at hfield'
  change (algebraMap K L (((normIntegerUnits K L u : 𝒪[K]ˣ) : 𝒪[K]) : K)) =
      (((Finset.univ.prod (fun σ : Gal(L / K) =>
        Units.mapEquiv
          (galoisGroupIntegerRingEquivOfIsIntegralClosure K L σ).toMulEquiv u) : 𝒪[L]ˣ) :
          𝒪[L]) : L)
  rw [normIntegerUnits_apply_coe]
  simpa [galoisGroupIntegerRingEquivOfIsIntegralClosure_apply] using hfield'

/-- Actual integral-closure version: after embedding `N(u)` back into `𝒪[L]`,
the result remains in the same principal-unit level. -/
theorem integerUnitsMap_normIntegerUnits_mem_principalUnits_of_isIntegralClosure
    (K L : Type u)
    [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
    [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]
    [IsIntegralClosure 𝒪[L] 𝒪[K] L] [LocalFieldTheory.ValuativeExtension K L]
    (n : Nat) (u : 𝒪[L]ˣ) (hu : u ∈ principalUnits L n) :
    integerUnitsMapOfValuationExtension K L (normIntegerUnits K L u) ∈
      principalUnits L n := by
  rw [integerUnitsMap_normIntegerUnits_eq_galoisGroup_prod_of_isIntegralClosure K L u]
  exact galoisGroup_prod_mem_principalUnits_of_isIntegralClosure K L n u hu

/-- Actual integral-closure version of the base-extended norm on `U_L^n`.

This is the source map for the unramified norm product calculation; it
asserts only that the embedded norm remains in `U_L^n`. -/
noncomputable def principalUnitsNormExtensionSideOfIsIntegralClosure (K L : Type u)
    [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
    [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]
    [IsIntegralClosure 𝒪[L] 𝒪[K] L] [LocalFieldTheory.ValuativeExtension K L] (n : Nat) :
    principalUnits L n →* principalUnits L n where
  toFun u :=
    ⟨integerUnitsMapOfValuationExtension K L (normIntegerUnits K L u.1),
      integerUnitsMap_normIntegerUnits_mem_principalUnits_of_isIntegralClosure
        K L n u.1 u.2⟩
  map_one' := by
    ext
    simp [integerUnitsMapOfValuationExtension]
  map_mul' := by
    intro u v
    ext
    simp [integerUnitsMapOfValuationExtension]

/-- States the theorem `principalUnitsNormExtensionSideOfIsIntegralClosure_apply`. -/
@[simp]
theorem principalUnitsNormExtensionSideOfIsIntegralClosure_apply (K L : Type u)
    [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
    [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]
    [IsIntegralClosure 𝒪[L] 𝒪[K] L] [LocalFieldTheory.ValuativeExtension K L]
    (n : Nat) (u : principalUnits L n) :
    ((principalUnitsNormExtensionSideOfIsIntegralClosure K L n u :
        principalUnits L n) : 𝒪[L]ˣ) =
      integerUnitsMapOfValuationExtension K L (normIntegerUnits K L u.1) :=
  rfl

/-- Actual integral-closure version: the base-extended norm on `U_L^n` is the
product of the actual integral-closure real Galois actions. -/
theorem principalUnitsNormExtensionSideOfIsIntegralClosure_eq_galoisGroup_prod
    (K L : Type u)
    [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
    [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]
    [IsIntegralClosure 𝒪[L] 𝒪[K] L] [LocalFieldTheory.ValuativeExtension K L]
    (n : Nat) (u : principalUnits L n) :
    principalUnitsNormExtensionSideOfIsIntegralClosure K L n u =
      Finset.univ.prod (fun σ : Gal(L / K) =>
        galoisGroupPrincipalUnitsMapEquivOfIsIntegralClosure K L n σ u) := by
  apply Subtype.ext
  simpa [principalUnitsNormExtensionSideOfIsIntegralClosure_apply,
    galoisGroupPrincipalUnitsMapEquivOfIsIntegralClosure_apply] using
    integerUnitsMap_normIntegerUnits_eq_galoisGroup_prod_of_isIntegralClosure K L u.1

/-- Actual integral-closure version of the first-order norm-product
calculation before residue trace identification. -/
theorem principalUnitsNormExtensionSideOfIsIntegralClosure_oneAdd_sub_one_sub_sum_mem_maximalIdeal_pow_succ
    (K L : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] [Field L] [ValuativeRel L] [TopologicalSpace L]
    [IsNonarchimedeanLocalField L] [Algebra K L] [FiniteDimensional K L]
    [IsGalois K L]
    [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]
    [IsIntegralClosure 𝒪[L] 𝒪[K] L] [LocalFieldTheory.ValuativeExtension K L]
    (n : Nat) (hn : 1 ≤ n) (a : (𝓂[L] ^ n : Ideal 𝒪[L])) :
    (((principalUnitsNormExtensionSideOfIsIntegralClosure K L n
          (principalUnitOneAddOfMemPowSubgroup L hn (a : 𝒪[L]) a.2) :
        principalUnits L n) : 𝒪[L]ˣ) : 𝒪[L]) - 1 -
      (Finset.univ.sum fun σ : Gal(L / K) =>
        galoisGroupIntegerRingEquivOfIsIntegralClosure K L σ (a : 𝒪[L])) ∈
        (𝓂[L] ^ (n + 1) : Ideal 𝒪[L]) := by
  classical
  rw [principalUnitsNormExtensionSideOfIsIntegralClosure_eq_galoisGroup_prod K L n
    (principalUnitOneAddOfMemPowSubgroup L hn (a : 𝒪[L]) a.2)]
  simpa [galoisGroupPrincipalUnitsMapEquivOfIsIntegralClosure,
    principalUnitsMapEquivOfIntegerRingEquiv,
    principalUnitOneAddOfMemPowSubgroup, principalUnitOneAddOfMemPow_val]
    using
      galoisGroup_prod_one_add_sub_one_sub_sum_mem_maximalIdeal_pow_succ_of_isIntegralClosure
        K L n hn a

/-- Actual integral-closure version of the base-extended norm on successive
principal-unit quotients. -/
def principalUnitsSuccQuotNormExtensionSideOfIsIntegralClosure (K L : Type u)
    [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
    [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]
    [IsIntegralClosure 𝒪[L] 𝒪[K] L] [LocalFieldTheory.ValuativeExtension K L] (n : Nat) :
    PrincipalUnitsSuccQuot L n →* PrincipalUnitsSuccQuot L n :=
  QuotientGroup.map
    ((principalUnits L (n + 1)).subgroupOf (principalUnits L n))
    ((principalUnits L (n + 1)).subgroupOf (principalUnits L n))
    (principalUnitsNormExtensionSideOfIsIntegralClosure K L n)
    (by
      intro u hu
      change ((principalUnitsNormExtensionSideOfIsIntegralClosure K L n u :
          principalUnits L n) : 𝒪[L]ˣ) ∈ principalUnits L (n + 1)
      simpa [principalUnitsNormExtensionSideOfIsIntegralClosure_apply] using
        integerUnitsMap_normIntegerUnits_mem_principalUnits_of_isIntegralClosure
          K L (n + 1) u.1 hu)

/-- States the theorem `principalUnitsSuccQuotNormExtensionSideOfIsIntegralClosure_mk`. -/
@[simp]
theorem principalUnitsSuccQuotNormExtensionSideOfIsIntegralClosure_mk
    (K L : Type u)
    [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
    [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]
    [IsIntegralClosure 𝒪[L] 𝒪[K] L] [LocalFieldTheory.ValuativeExtension K L]
    (n : Nat) (u : principalUnits L n) :
    principalUnitsSuccQuotNormExtensionSideOfIsIntegralClosure K L n
        (QuotientGroup.mk u) =
      QuotientGroup.mk
        (principalUnitsNormExtensionSideOfIsIntegralClosure K L n u) :=
  rfl

end LocalClassFieldTheory
end
end

section
-- module Solutions.OAIQ244_DUKE.LocalClassFieldTheory_Finite_Unramified_PrincipalUnits_Basic
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.residueFieldZModAlgebra _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.LubinTate.Valuations.exponentialValuationSubringIsLocalRing _root_.LubinTate.compatibleGroupFamiliesGroup _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionFixedSubring.instIsLocalRing _root_.RamificationTheory.HilbertRamification.ValuationSubring.selectedResidueField.instAlgebra _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.maximalIdealPowSuccQuotModule _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.isDomain _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.isLocalRing _root_.CyclicCohomology.binaryCoefficientFamilyCommGroup _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.LocalClassFieldTheory.normalizationIntegerRingIsIntegralClosure _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.chosenFinitePlaceCompletionAlgebra _root_.finiteLocalUnitsOpen _root_.relativeAdeleRingIntermediateAlgebra _root_.relativeAdeleRingTopIntermediateAlgebra
attribute [-simp] _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.CyclicCohomology.galoisGroupIntegerUnitsModPrincipalUnitsMapEquivOfIsIntegralClosure_mk _root_.CyclicCohomology.integerUnitsModPrincipalUnitsAtLevelConcreteEquiv_mk _root_.CyclicCohomology.integerUnitsModPrincipalUnitsAtLevelLift_mk _root_.CyclicCohomology.integerUnitsModPrincipalUnitsAtLevelMk_eq_iff_div_mem _root_.CyclicCohomology.principalUnitsSuccQuotToIntegerUnitsModPrincipalUnitsSucc_mk _root_.IsDiscreteValuationRing.addVal_ringEquiv _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.LocalClassFieldTheory.chosenNormalBasisPrincipalUnitSequenceAsPrincipalUnits_val _root_.LocalClassFieldTheory.galoisGroupIntegerUnitsMulDistribMulActionOfIsIntegralClosure_smul _root_.LocalFieldTheory.galoisGroupEquivResidueAlgEquivOfUnramifiedValuationOfIsIntegralClosure_arithmeticFrobenius _root_.LocalFieldTheory.galoisGroupEquivZModOfUnramifiedValuationNormalized_arithmeticFrobenius _root_.LocalFieldTheory.galoisGroupEquivZModOfUnramifiedValuationNormalized_arithmeticFrobenius_zpow _root_.LocalFieldTheory.galoisGroupResidueAlgEquivOfIsIntegralClosure_arithmeticFrobenius _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.OAI.PrimeDegreePackets.ThetaConstruction.schwartzCM_apply _root_.infinitePlace_mult_smul
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false
/-! Provides the public declarations in the `LocalClassFieldTheory.Finite.Unramified.PrincipalUnits.Basic` Lean module. -/

noncomputable section

universe u

namespace LocalClassFieldTheory

open scoped ValuativeRel
open LocalFieldTheory
open LocalFieldTheory.IsNonarchimedeanLocalField
open Filter

/-- In an actual unramified valuation extension, the actual integer-unit norm
sends `U_L^n` into `U_K^n`. -/
theorem normIntegerUnits_mem_principalUnits_of_unramifiedValuation_of_isIntegralClosure
    (K L : Type u)
    [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
    [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]
    [LocalFieldTheory.ValuativeExtension K L] [IsIntegralClosure 𝒪[L] 𝒪[K] L]
    [Module.Finite 𝒪[K] 𝒪[L]]
    [LocalFieldTheory.IsNonarchimedeanLocalField.IsUnramifiedValuedExtension K L]
    (n : Nat) (u : 𝒪[L]ˣ) (hu : u ∈ principalUnits L n) :
    normIntegerUnits K L u ∈ principalUnits K n := by
  apply principalUnits_of_integerUnitsMap_mem_principalUnits_of_unramifiedValuation K L n
  exact integerUnitsMap_normIntegerUnits_mem_principalUnits_of_isIntegralClosure K L n u hu

/-- Actual integral-closure version of the integer-unit norm restricted to
principal units in an actual unramified valuation extension. -/
noncomputable def principalUnitsNormOfUnramifiedValuationOfIsIntegralClosure
    (K L : Type u)
    [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
    [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]
    [LocalFieldTheory.ValuativeExtension K L] [IsIntegralClosure 𝒪[L] 𝒪[K] L]
    [Module.Finite 𝒪[K] 𝒪[L]]
    [LocalFieldTheory.IsNonarchimedeanLocalField.IsUnramifiedValuedExtension K L] (n : Nat) :
    principalUnits L n →* principalUnits K n where
  toFun u :=
    ⟨normIntegerUnits K L u.1,
      normIntegerUnits_mem_principalUnits_of_unramifiedValuation_of_isIntegralClosure
        K L n u.1 u.2⟩
  map_one' := by
    ext
    simp
  map_mul' := by
    intro u v
    ext
    simp

/-- States the theorem `principalUnitsNormOfUnramifiedValuationOfIsIntegralClosure_apply`. -/
@[simp]
theorem principalUnitsNormOfUnramifiedValuationOfIsIntegralClosure_apply
    (K L : Type u)
    [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
    [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]
    [LocalFieldTheory.ValuativeExtension K L] [IsIntegralClosure 𝒪[L] 𝒪[K] L]
    [Module.Finite 𝒪[K] 𝒪[L]]
    [LocalFieldTheory.IsNonarchimedeanLocalField.IsUnramifiedValuedExtension K L] (n : Nat)
    (u : principalUnits L n) :
    ((principalUnitsNormOfUnramifiedValuationOfIsIntegralClosure K L n u :
        principalUnits K n) : 𝒪[K]ˣ) =
      normIntegerUnits K L u.1 :=
  rfl

/-- Base-extending the integral-closure unramified
principal-unit norm recovers the extension-side norm expressed through the
integral-closure Galois product. -/
theorem principalUnitsMap_normOfUnramifiedValuationOfIsIntegralClosure_eq_normExtensionSide
    (K L : Type u)
    [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
    [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]
    [LocalFieldTheory.ValuativeExtension K L] [IsIntegralClosure 𝒪[L] 𝒪[K] L]
    [Module.Finite 𝒪[K] 𝒪[L]]
    [LocalFieldTheory.IsNonarchimedeanLocalField.IsUnramifiedValuedExtension K L]
    (n : Nat) (u : principalUnits L n) :
    principalUnitsMapOfUnramifiedValuation K L n
        (principalUnitsNormOfUnramifiedValuationOfIsIntegralClosure K L n u) =
      principalUnitsNormExtensionSideOfIsIntegralClosure K L n u := by
  ext
  rfl

namespace UnramifiedPrincipalUnits

/-- The integral-closure norm-product calculation before residue trace
identification. -/
theorem norm_oneAdd_sub_galoisSum_mem_next
    (K L : Type u)
    [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
    [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]
    [LocalFieldTheory.ValuativeExtension K L] [IsIntegralClosure 𝒪[L] 𝒪[K] L]
    [Module.Finite 𝒪[K] 𝒪[L]]
    [LocalFieldTheory.IsNonarchimedeanLocalField.IsUnramifiedValuedExtension K L]
    (n : Nat) (hn : 1 ≤ n) (a : (𝓂[L] ^ n : Ideal 𝒪[L])) :
    (((principalUnitsMapOfUnramifiedValuation K L n
          (principalUnitsNormOfUnramifiedValuationOfIsIntegralClosure K L n
            (principalUnitOneAddOfMemPowSubgroup L hn (a : 𝒪[L]) a.2)) :
        principalUnits L n) : 𝒪[L]ˣ) : 𝒪[L]) - 1 -
      (Finset.univ.sum fun σ : Gal(L / K) =>
        galoisGroupIntegerRingEquivOfIsIntegralClosure K L σ (a : 𝒪[L])) ∈
        (𝓂[L] ^ (n + 1) : Ideal 𝒪[L]) := by
  rw [principalUnitsMap_normOfUnramifiedValuationOfIsIntegralClosure_eq_normExtensionSide
    K L n (principalUnitOneAddOfMemPowSubgroup L hn (a : 𝒪[L]) a.2)]
  exact
      principalUnitsNormExtensionSideOfIsIntegralClosure_oneAdd_sub_one_sub_sum_mem_maximalIdeal_pow_succ
      K L n hn a

end UnramifiedPrincipalUnits

/-- The integral-closure norm on successive principal-unit
quotients.  This is the quotient map used in the unramified norm calculation before
identifying the associated graded map with residue trace. -/
noncomputable def principalUnitsSuccQuotNormOfUnramifiedValuationOfIsIntegralClosure
    (K L : Type u)
    [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
    [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]
    [LocalFieldTheory.ValuativeExtension K L] [IsIntegralClosure 𝒪[L] 𝒪[K] L]
    [Module.Finite 𝒪[K] 𝒪[L]]
    [LocalFieldTheory.IsNonarchimedeanLocalField.IsUnramifiedValuedExtension K L] (n : Nat) :
    PrincipalUnitsSuccQuot L n →* PrincipalUnitsSuccQuot K n :=
  principalUnitsSuccQuotLift n
    ((principalUnitsSuccQuotMk K n).comp
      (principalUnitsNormOfUnramifiedValuationOfIsIntegralClosure K L n))
    (by
      intro u hu
      rw [MonoidHom.mem_ker, MonoidHom.comp_apply,
        principalUnitsSuccQuotMk_eq_one_iff]
      change ((principalUnitsNormOfUnramifiedValuationOfIsIntegralClosure K L n u :
          principalUnits K n) : 𝒪[K]ˣ) ∈ principalUnits K (n + 1)
      simpa [principalUnitsNormOfUnramifiedValuationOfIsIntegralClosure_apply]
        using
          normIntegerUnits_mem_principalUnits_of_unramifiedValuation_of_isIntegralClosure
            K L (n + 1) u.1 hu)

/-- States the theorem `principalUnitsSuccQuotNormOfUnramifiedValuationOfIsIntegralClosure_mk`. -/
@[simp]
theorem principalUnitsSuccQuotNormOfUnramifiedValuationOfIsIntegralClosure_mk
    (K L : Type u)
    [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
    [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]
    [LocalFieldTheory.ValuativeExtension K L] [IsIntegralClosure 𝒪[L] 𝒪[K] L]
    [Module.Finite 𝒪[K] 𝒪[L]]
    [LocalFieldTheory.IsNonarchimedeanLocalField.IsUnramifiedValuedExtension K L] (n : Nat)
    (u : principalUnits L n) :
    principalUnitsSuccQuotNormOfUnramifiedValuationOfIsIntegralClosure K L n
        (principalUnitsSuccQuotMk L n u) =
      principalUnitsSuccQuotMk K n
        (principalUnitsNormOfUnramifiedValuationOfIsIntegralClosure K L n u) :=
  rfl

/-- The integral-closure associated-graded norm-product
calculation in the unramified norm calculation. -/
theorem principalUnitsSuccQuotMap_normOfUnramifiedValuationOfIsIntegralClosure_oneAdd_base_eq_sum
    (K L : Type u)
    [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
    [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]
    [LocalFieldTheory.ValuativeExtension K L] [IsIntegralClosure 𝒪[L] 𝒪[K] L]
    [Module.Finite 𝒪[K] 𝒪[L]]
    [LocalFieldTheory.IsNonarchimedeanLocalField.IsUnramifiedValuedExtension K L]
    (n : Nat) (hn : 1 ≤ n) (a : (𝓂[L] ^ n : Ideal 𝒪[L])) :
    let b : (𝓂[L] ^ n : Ideal 𝒪[L]) :=
      ⟨Finset.univ.sum fun σ : Gal(L / K) =>
          galoisGroupIntegerRingEquivOfIsIntegralClosure K L σ (a : 𝒪[L]),
        by
          classical
          exact Ideal.sum_mem _ fun σ _ =>
            (integerRingEquiv_mem_maximalIdeal_pow L
              (galoisGroupIntegerRingEquivOfIsIntegralClosure K L σ) n
              (a : 𝒪[L])).2 a.2⟩
    principalUnitsSuccQuotMapOfUnramifiedValuation K L n
        (principalUnitsSuccQuotNormOfUnramifiedValuationOfIsIntegralClosure K L n
          (principalUnitsSuccQuotMk L n
            (principalUnitOneAddOfMemPowSubgroup L hn (a : 𝒪[L]) a.2))) =
      principalUnitsSuccQuotOfIdealPow L n hn b := by
  classical
  intro b
  rw [principalUnitsSuccQuotNormOfUnramifiedValuationOfIsIntegralClosure_mk,
    principalUnitsSuccQuotMapOfUnramifiedValuation_mk]
  exact principalUnitsSuccQuotMk_eq_oneAdd_of_sub_one_sub_mem_succ L n hn
    (principalUnitsMapOfUnramifiedValuation K L n
      (principalUnitsNormOfUnramifiedValuationOfIsIntegralClosure K L n
        (principalUnitOneAddOfMemPowSubgroup L hn (a : 𝒪[L]) a.2)))
    b
    (by
      simpa [b] using
    UnramifiedPrincipalUnits.norm_oneAdd_sub_galoisSum_mem_next
          K L n hn a)


end LocalClassFieldTheory
end
end

section
-- module Solutions.OAIQ244_DUKE.LocalClassFieldTheory_Finite_Unramified_PrincipalUnits_Trace
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.residueFieldZModAlgebra _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.LubinTate.Valuations.exponentialValuationSubringIsLocalRing _root_.LubinTate.compatibleGroupFamiliesGroup _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionFixedSubring.instIsLocalRing _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionResidueField.instField _root_.RamificationTheory.HilbertRamification.ValuationSubring.selectedResidueField.instAlgebra _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.maximalIdealPowSuccQuotModule _root_.ValuationTheory.DiscreteValuationField.DVF.residueField.field _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.isDomain _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.isLocalRing _root_.CyclicCohomology.binaryCoefficientFamilyCommGroup _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.LocalClassFieldTheory.normalizationIntegerRingIsIntegralClosure _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.chosenFinitePlaceCompletionAlgebra _root_.finiteLocalUnitsOpen _root_.relativeAdeleRingIntermediateAlgebra _root_.relativeAdeleRingTopIntermediateAlgebra
attribute [-simp] _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.CyclicCohomology.galoisGroupIntegerUnitsModPrincipalUnitsMapEquivOfIsIntegralClosure_mk _root_.CyclicCohomology.integerUnitsModPrincipalUnitsAtLevelConcreteEquiv_mk _root_.CyclicCohomology.integerUnitsModPrincipalUnitsAtLevelLift_mk _root_.CyclicCohomology.integerUnitsModPrincipalUnitsAtLevelMk_eq_iff_div_mem _root_.CyclicCohomology.mem_chosenBaseUniformizerPowSubmodule_iff _root_.CyclicCohomology.principalUnitsSuccQuotToIntegerUnitsModPrincipalUnitsSucc_mk _root_.IsDiscreteValuationRing.addVal_ringEquiv _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.LocalClassFieldTheory.chosenNormalBasisIntegerLatticeMulPowLinearEquiv_apply _root_.LocalClassFieldTheory.chosenNormalBasisPrincipalUnitSequenceAsPrincipalUnits_val _root_.LocalClassFieldTheory.galoisGroupIntegerUnitsMulDistribMulActionOfIsIntegralClosure_smul _root_.LocalFieldTheory.galoisGroupEquivResidueAlgEquivOfUnramifiedValuationOfIsIntegralClosure_arithmeticFrobenius _root_.LocalFieldTheory.galoisGroupEquivZModOfUnramifiedValuationNormalized_arithmeticFrobenius _root_.LocalFieldTheory.galoisGroupEquivZModOfUnramifiedValuationNormalized_arithmeticFrobenius_zpow _root_.LocalFieldTheory.galoisGroupResidueAlgEquivOfIsIntegralClosure_arithmeticFrobenius _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.OAI.PrimeDegreePackets.ThetaConstruction.schwartzCM_apply _root_.infinitePlace_mult_smul
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false
/-! Provides the public declarations in the `LocalClassFieldTheory.Finite.Unramified.PrincipalUnits.Trace` Lean module. -/

noncomputable section

universe u

namespace LocalClassFieldTheory

open scoped ValuativeRel
open LocalFieldTheory
open LocalFieldTheory.IsNonarchimedeanLocalField
open Filter

namespace UnramifiedPrincipalUnits

/-- For the integral-closure base-uniformizer representative
`1 + rϖ_L^n`, the norm after base extension back to `L` is residue trace on
the associated graded quotient. -/
theorem quotientNorm_oneAdd_uniformizerPow_eq_trace
    (K L : Type u)
    [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
    [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]
    [LocalFieldTheory.ValuativeExtension K L] [IsIntegralClosure 𝒪[L] 𝒪[K] L]
    [Module.Finite 𝒪[K] 𝒪[L]]
    [LocalFieldTheory.IsNonarchimedeanLocalField.IsUnramifiedValuedExtension K L]
    (n : Nat) (hn : 1 ≤ n) (r : 𝒪[L]) :
    let πL := integerRingMapOfValuationExtension K L (chosenIntegerRingUniformizer K)
    let hπL := integerRingMap_uniformizer_irreducible_of_unramifiedValuation K L
    let a : (𝓂[L] ^ n : Ideal 𝒪[L]) :=
      maximalIdealPowMulUniformizerPowMap L πL hπL n r
    Additive.ofMul
        (principalUnitsSuccQuotMapOfUnramifiedValuation K L n
          (principalUnitsSuccQuotNormOfUnramifiedValuationOfIsIntegralClosure K L n
            (principalUnitsSuccQuotMk L n
              (principalUnitOneAddOfMemPowSubgroup L hn (a : 𝒪[L]) a.2)))) =
      (principalUnitsSuccQuotAddEquivResidueOfIrreducible L πL hπL n hn).symm
        (algebraMap 𝓀[K] 𝓀[L]
          (Algebra.trace 𝓀[K] 𝓀[L] (IsLocalRing.residue 𝒪[L] r))) := by
  classical
  intro πL hπL a
  let b : (𝓂[L] ^ n : Ideal 𝒪[L]) :=
    ⟨Finset.univ.sum fun σ : Gal(L / K) =>
        galoisGroupIntegerRingEquivOfIsIntegralClosure K L σ (a : 𝒪[L]),
      by
        exact Ideal.sum_mem _ fun σ _ =>
          (integerRingEquiv_mem_maximalIdeal_pow L
            (galoisGroupIntegerRingEquivOfIsIntegralClosure K L σ) n
            (a : 𝒪[L])).2 a.2⟩
  have hnorm :=
    principalUnitsSuccQuotMap_normOfUnramifiedValuationOfIsIntegralClosure_oneAdd_base_eq_sum
      K L n hn a
  change Additive.ofMul
      (principalUnitsSuccQuotMapOfUnramifiedValuation K L n
        (principalUnitsSuccQuotNormOfUnramifiedValuationOfIsIntegralClosure K L n
          (principalUnitsSuccQuotMk L n
            (principalUnitOneAddOfMemPowSubgroup L hn (a : 𝒪[L]) a.2)))) =
    (principalUnitsSuccQuotAddEquivResidueOfIrreducible L πL hπL n hn).symm
      (algebraMap 𝓀[K] 𝓀[L]
        (Algebra.trace 𝓀[K] 𝓀[L] (IsLocalRing.residue 𝒪[L] r)))
  rw [hnorm]
  rw [principalUnitsSuccQuotAddEquivResidueOfIrreducible_symm_apply]
  change Additive.ofMul (principalUnitsSuccQuotOfIdealPow L n hn b) =
    principalUnitsSuccQuotOfMaximalIdealPowSuccQuotAdd L n hn
      (residueAddEquivMaximalIdealPowSuccQuotOfIrreducible L πL hπL n
        (algebraMap 𝓀[K] 𝓀[L]
          (Algebra.trace 𝓀[K] 𝓀[L] (IsLocalRing.residue 𝒪[L] r))))
  rw [← principalUnitsSuccQuotOfMaximalIdealPowSuccQuot_mk L n hn b]
  change principalUnitsSuccQuotOfMaximalIdealPowSuccQuotAdd L n hn
      (maximalIdealPowSuccQuotMk L n b) =
    principalUnitsSuccQuotOfMaximalIdealPowSuccQuotAdd L n hn
      (residueAddEquivMaximalIdealPowSuccQuotOfIrreducible L πL hπL n
        (algebraMap 𝓀[K] 𝓀[L]
          (Algebra.trace 𝓀[K] 𝓀[L] (IsLocalRing.residue 𝒪[L] r))))
  congr 1
  have hb_eq :
      (b : 𝒪[L]) =
        (Finset.univ.sum fun σ : Gal(L / K) =>
          galoisGroupIntegerRingEquivOfIsIntegralClosure K L σ r) * πL ^ n := by
    simpa [b, a, πL] using
      galoisGroup_sum_mul_base_uniformizer_pow_eq_coeff_sum_of_isIntegralClosure K L n r
  rw [show maximalIdealPowSuccQuotMk L n b =
      maximalIdealPowSuccQuotMulUniformizerPowMap L πL hπL n
        (Finset.univ.sum fun σ : Gal(L / K) =>
          galoisGroupIntegerRingEquivOfIsIntegralClosure K L σ r) by
    rw [maximalIdealPowSuccQuotMulUniformizerPowMap_apply]
    apply congrArg (maximalIdealPowSuccQuotMk L n)
    apply Subtype.ext
    calc
      (b : 𝒪[L]) = (Finset.univ.sum fun σ : Gal(L / K) =>
            galoisGroupIntegerRingEquivOfIsIntegralClosure K L σ r) * πL ^ n := hb_eq
      _ =
          ((maximalIdealPowMulUniformizerPowMap L πL hπL n
            (Finset.univ.sum fun σ : Gal(L / K) =>
              galoisGroupIntegerRingEquivOfIsIntegralClosure K L σ r) :
            (𝓂[L] ^ n : Ideal 𝒪[L])) : 𝒪[L]) := by
        rw [maximalIdealPowMulUniformizerPowMap_apply]]
  exact
    galoisSum_uniformizerGraded_eq_residueTrace
      K L n r

end UnramifiedPrincipalUnits

/-- Actual integral-closure version: for the base-uniformizer representative
`1 + rϖ_L^n`, the norm on `U_L^n/U_L^(n+1)` is the residue-field trace class
on `U_K^n/U_K^(n+1)`. -/
theorem principalUnitsSuccQuotNormOfUnramifiedValuationOfIsIntegralClosure_oneAdd_uniformizer_pow_eq_trace
    (K L : Type u)
    [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
    [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]
    [LocalFieldTheory.ValuativeExtension K L] [IsIntegralClosure 𝒪[L] 𝒪[K] L]
    [Module.Finite 𝒪[K] 𝒪[L]]
    [LocalFieldTheory.IsNonarchimedeanLocalField.IsUnramifiedValuedExtension K L]
    (n : Nat) (hn : 1 ≤ n) (r : 𝒪[L]) :
    let πK := chosenIntegerRingUniformizer K
    let πL := integerRingMapOfValuationExtension K L πK
    let hπL := integerRingMap_uniformizer_irreducible_of_unramifiedValuation K L
    let a : (𝓂[L] ^ n : Ideal 𝒪[L]) :=
      maximalIdealPowMulUniformizerPowMap L πL hπL n r
    Additive.ofMul
        (principalUnitsSuccQuotNormOfUnramifiedValuationOfIsIntegralClosure K L n
          (principalUnitsSuccQuotMk L n
            (principalUnitOneAddOfMemPowSubgroup L hn (a : 𝒪[L]) a.2))) =
      (principalUnitsSuccQuotAddEquivResidueOfIrreducible K πK
        (chosenIntegerRingUniformizer_irreducible K) n hn).symm
        (Algebra.trace 𝓀[K] 𝓀[L] (IsLocalRing.residue 𝒪[L] r)) := by
  classical
  intro πK πL hπL a
  let x :=
    principalUnitsSuccQuotNormOfUnramifiedValuationOfIsIntegralClosure K L n
      (principalUnitsSuccQuotMk L n
        (principalUnitOneAddOfMemPowSubgroup L hn (a : 𝒪[L]) a.2))
  let y :=
    (principalUnitsSuccQuotAddEquivResidueOfIrreducible K πK
      (chosenIntegerRingUniformizer_irreducible K) n hn).symm
      (Algebra.trace 𝓀[K] 𝓀[L] (IsLocalRing.residue 𝒪[L] r))
  have hxmap :
      MonoidHom.toAdditive (principalUnitsSuccQuotMapOfUnramifiedValuation K L n)
          (Additive.ofMul x) =
        (principalUnitsSuccQuotAddEquivResidueOfIrreducible L πL hπL n hn).symm
          (algebraMap 𝓀[K] 𝓀[L]
            (Algebra.trace 𝓀[K] 𝓀[L] (IsLocalRing.residue 𝒪[L] r))) := by
    simpa [x, πK, πL, hπL, a] using
    UnramifiedPrincipalUnits.quotientNorm_oneAdd_uniformizerPow_eq_trace
        K L n hn r
  have hymap :
      MonoidHom.toAdditive (principalUnitsSuccQuotMapOfUnramifiedValuation K L n) y =
        (principalUnitsSuccQuotAddEquivResidueOfIrreducible L πL hπL n hn).symm
          (algebraMap 𝓀[K] 𝓀[L]
            (Algebra.trace 𝓀[K] 𝓀[L] (IsLocalRing.residue 𝒪[L] r))) := by
    simpa [y, πK, πL, hπL, residueFieldMapOfValuationExtension_eq_algebraMap] using
      principalUnitsSuccQuotAddEquivResidueOfIrreducible_symm_map K L n hn
        (Algebra.trace 𝓀[K] 𝓀[L] (IsLocalRing.residue 𝒪[L] r))
  have hmul : x = Additive.toMul y := by
    apply principalUnitsSuccQuotMapOfUnramifiedValuation_injective K L n hn
    apply Additive.ofMul.injective
    change MonoidHom.toAdditive (principalUnitsSuccQuotMapOfUnramifiedValuation K L n)
        (Additive.ofMul x) =
      MonoidHom.toAdditive (principalUnitsSuccQuotMapOfUnramifiedValuation K L n) y
    exact hxmap.trans hymap.symm
  change Additive.ofMul x = y
  simpa using congrArg Additive.ofMul hmul

/-- Actual integral-closure version: in residue coordinates, the norm on the
successive principal-unit quotient is the finite residue-field trace. -/
theorem principalUnitsSuccQuotNormOfUnramifiedValuationOfIsIntegralClosure_trace_coord
    (K L : Type u)
    [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
    [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]
    [LocalFieldTheory.ValuativeExtension K L] [IsIntegralClosure 𝒪[L] 𝒪[K] L]
    [Module.Finite 𝒪[K] 𝒪[L]]
    [LocalFieldTheory.IsNonarchimedeanLocalField.IsUnramifiedValuedExtension K L]
    (n : Nat) (hn : 1 ≤ n) (x : 𝓀[L]) :
    let πK := chosenIntegerRingUniformizer K
    let πL := integerRingMapOfValuationExtension K L πK
    let hπL := integerRingMap_uniformizer_irreducible_of_unramifiedValuation K L
    let eK := principalUnitsSuccQuotAddEquivResidueOfIrreducible K πK
      (chosenIntegerRingUniformizer_irreducible K) n hn
    let eL := principalUnitsSuccQuotAddEquivResidueOfIrreducible L πL hπL n hn
    MonoidHom.toAdditive
        (principalUnitsSuccQuotNormOfUnramifiedValuationOfIsIntegralClosure K L n)
        (eL.symm x) =
      eK.symm (Algebra.trace 𝓀[K] 𝓀[L] x) := by
  classical
  intro πK πL hπL eK eL
  obtain ⟨r, rfl⟩ := IsLocalRing.residue_surjective x
  have hrep :=
    principalUnitsSuccQuotNormOfUnramifiedValuationOfIsIntegralClosure_oneAdd_uniformizer_pow_eq_trace
      K L n hn r
  rw [principalUnitsSuccQuotAddEquivResidueOfIrreducible_symm_residue]
  change Additive.ofMul _ = _
  simpa only [eK, eL, πK, πL, hπL, toMul_ofMul] using hrep

/-- The residue-trace model for the actual unramified norm on
`U^n/U^(n+1)`, written in the base-uniformizer coordinates. -/
noncomputable def principalUnitsSuccQuotTraceOfUnramifiedValuation (K L : Type u)
    [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
    [Algebra K L] [FiniteDimensional K L]
    [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]
    [Module.Finite 𝒪[K] 𝒪[L]]
    [LocalFieldTheory.IsNonarchimedeanLocalField.IsUnramifiedValuedExtension K L]
    (n : Nat) (hn : 1 ≤ n) :
    Additive (PrincipalUnitsSuccQuot L n) →+ Additive (PrincipalUnitsSuccQuot K n) :=
  let πK := chosenIntegerRingUniformizer K
  let πL := integerRingMapOfValuationExtension K L πK
  let hπL := integerRingMap_uniformizer_irreducible_of_unramifiedValuation K L
  ((principalUnitsSuccQuotAddEquivResidueOfIrreducible K πK
    (chosenIntegerRingUniformizer_irreducible K) n hn).symm.toAddMonoidHom).comp
    ((Algebra.trace 𝓀[K] 𝓀[L]).toAddMonoidHom.comp
      (principalUnitsSuccQuotAddEquivResidueOfIrreducible L πL hπL n hn).toAddMonoidHom)

/-- States the theorem `principalUnitsSuccQuotTraceOfUnramifiedValuation_apply`. -/
@[simp]
theorem principalUnitsSuccQuotTraceOfUnramifiedValuation_apply
    (K L : Type u)
    [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
    [Algebra K L] [FiniteDimensional K L]
    [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]
    [Module.Finite 𝒪[K] 𝒪[L]]
    [LocalFieldTheory.IsNonarchimedeanLocalField.IsUnramifiedValuedExtension K L]
    (n : Nat) (hn : 1 ≤ n) (x : Additive (PrincipalUnitsSuccQuot L n)) :
    let πK := chosenIntegerRingUniformizer K
    let πL := integerRingMapOfValuationExtension K L πK
    let hπL := integerRingMap_uniformizer_irreducible_of_unramifiedValuation K L
    principalUnitsSuccQuotTraceOfUnramifiedValuation K L n hn x =
      (principalUnitsSuccQuotAddEquivResidueOfIrreducible K πK
        (chosenIntegerRingUniformizer_irreducible K) n hn).symm
        (Algebra.trace 𝓀[K] 𝓀[L]
          (principalUnitsSuccQuotAddEquivResidueOfIrreducible L πL hπL n hn x)) :=
  rfl

/-- The residue-trace model on successive principal-unit quotients is
surjective in the unramified valuation case. -/
theorem principalUnitsSuccQuotTraceOfUnramifiedValuation_surjective
    (K L : Type u)
    [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
    [Algebra K L] [FiniteDimensional K L]
    [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]
    [Module.Finite 𝒪[K] 𝒪[L]]
    [LocalFieldTheory.IsNonarchimedeanLocalField.IsUnramifiedValuedExtension K L]
    (n : Nat) (hn : 1 ≤ n) :
    Function.Surjective (principalUnitsSuccQuotTraceOfUnramifiedValuation K L n hn) := by
  classical
  intro y
  let πK := chosenIntegerRingUniformizer K
  let πL := integerRingMapOfValuationExtension K L πK
  let hπL := integerRingMap_uniformizer_irreducible_of_unramifiedValuation K L
  let eK := principalUnitsSuccQuotAddEquivResidueOfIrreducible K πK
    (chosenIntegerRingUniformizer_irreducible K) n hn
  let eL := principalUnitsSuccQuotAddEquivResidueOfIrreducible L πL hπL n hn
  obtain ⟨x, hx⟩ :=
    residueField_trace_surjective_of_valuationExtension K L (eK y)
  refine ⟨eL.symm x, ?_⟩
  change
    (((eK.symm.toAddMonoidHom).comp
      ((Algebra.trace 𝓀[K] 𝓀[L]).toAddMonoidHom.comp eL.toAddMonoidHom))
      (eL.symm x)) = y
  simp [hx]

/-- Actual integral-closure version: the unramified norm on every successive
principal-unit quotient is the finite residue-field trace in base-uniformizer
coordinates. -/
theorem principalUnitsSuccQuotNormOfUnramifiedValuationOfIsIntegralClosure_eq_trace
    (K L : Type u)
    [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
    [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]
    [LocalFieldTheory.ValuativeExtension K L] [IsIntegralClosure 𝒪[L] 𝒪[K] L]
    [Module.Finite 𝒪[K] 𝒪[L]]
    [LocalFieldTheory.IsNonarchimedeanLocalField.IsUnramifiedValuedExtension K L]
    (n : Nat) (hn : 1 ≤ n) :
    MonoidHom.toAdditive
        (principalUnitsSuccQuotNormOfUnramifiedValuationOfIsIntegralClosure K L n) =
      principalUnitsSuccQuotTraceOfUnramifiedValuation K L n hn := by
  apply AddMonoidHom.ext
  intro x
  let πK := chosenIntegerRingUniformizer K
  let πL := integerRingMapOfValuationExtension K L πK
  let hπL := integerRingMap_uniformizer_irreducible_of_unramifiedValuation K L
  let eL := principalUnitsSuccQuotAddEquivResidueOfIrreducible L πL hπL n hn
  have hcoord :=
    principalUnitsSuccQuotNormOfUnramifiedValuationOfIsIntegralClosure_trace_coord
      K L n hn (eL x)
  simpa [principalUnitsSuccQuotTraceOfUnramifiedValuation, πK, πL, hπL, eL]
    using hcoord

/-- Actual integral-closure version: on every successive principal-unit
quotient, the unramified norm is surjective after writing the quotient
additively. -/
theorem principalUnitsSuccQuotNormOfUnramifiedValuationOfIsIntegralClosure_toAdditive_surjective
    (K L : Type u)
    [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
    [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]
    [LocalFieldTheory.ValuativeExtension K L] [IsIntegralClosure 𝒪[L] 𝒪[K] L]
    [Module.Finite 𝒪[K] 𝒪[L]]
    [LocalFieldTheory.IsNonarchimedeanLocalField.IsUnramifiedValuedExtension K L]
    (n : Nat) (hn : 1 ≤ n) :
    Function.Surjective
      (MonoidHom.toAdditive
        (principalUnitsSuccQuotNormOfUnramifiedValuationOfIsIntegralClosure K L n)) := by
  rw [principalUnitsSuccQuotNormOfUnramifiedValuationOfIsIntegralClosure_eq_trace
    K L n hn]
  exact principalUnitsSuccQuotTraceOfUnramifiedValuation_surjective K L n hn

/-- Actual integral-closure version: on every successive principal-unit
quotient, the unramified norm is surjective. -/
theorem principalUnitsSuccQuotNormOfUnramifiedValuationOfIsIntegralClosure_surjective
    (K L : Type u)
    [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
    [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]
    [LocalFieldTheory.ValuativeExtension K L] [IsIntegralClosure 𝒪[L] 𝒪[K] L]
    [Module.Finite 𝒪[K] 𝒪[L]]
    [LocalFieldTheory.IsNonarchimedeanLocalField.IsUnramifiedValuedExtension K L]
    (n : Nat) (hn : 1 ≤ n) :
    Function.Surjective
      (principalUnitsSuccQuotNormOfUnramifiedValuationOfIsIntegralClosure K L n) := by
  intro y
  obtain ⟨x, hx⟩ :=
    principalUnitsSuccQuotNormOfUnramifiedValuationOfIsIntegralClosure_toAdditive_surjective
      K L n hn (Additive.ofMul y)
  refine ⟨Additive.toMul x, ?_⟩
  apply Additive.ofMul.injective
  change MonoidHom.toAdditive
      (principalUnitsSuccQuotNormOfUnramifiedValuationOfIsIntegralClosure K L n)
      (Additive.ofMul (Additive.toMul x)) = Additive.ofMul y
  simpa using hx

end LocalClassFieldTheory
end
end

section
-- module Solutions.OAIQ244_DUKE.LocalClassFieldTheory_Finite_Unramified_PrincipalUnits_Lift
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.DiscreteNthRootsSubgroup.instTopologicalSpaceSubtypeUnitsMemSubgroup _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.residueFieldZModAlgebra _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.LubinTate.compatibleGroupFamiliesGroup _root_.OAI.PrimeDegreePackets.instNonemptyLeafTestSpace _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.RamificationTheory.HilbertRamification.ValuationSubring.selectedResidueField.instAlgebra _root_.RayClass.approximationCompletionTopologicalSpace _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.maximalIdealPowSuccQuotModule _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.CyclicCohomology.binaryCoefficientFamilyCommGroup _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.LocalClassFieldTheory.normalizationIntegerRingIsIntegralClosure _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.chosenFinitePlaceCompletionAlgebra _root_.finiteLocalUnitsOpen _root_.relativeAdeleRingIntermediateAlgebra _root_.relativeAdeleRingTopIntermediateAlgebra
attribute [-simp] _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.CyclicCohomology.integerUnitsModPrincipalUnitsAtLevelConcreteEquiv_mk _root_.CyclicCohomology.integerUnitsModPrincipalUnitsAtLevelLift_mk _root_.CyclicCohomology.integerUnitsModPrincipalUnitsAtLevelMk_eq_iff_div_mem _root_.CyclicCohomology.principalUnitsSuccQuotToIntegerUnitsModPrincipalUnitsSucc_mk _root_.IsDiscreteValuationRing.addVal_ringEquiv _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.LocalClassFieldTheory.chosenNormalBasisPrincipalUnitSequenceAsPrincipalUnits_val _root_.LocalFieldTheory.galoisGroupEquivResidueAlgEquivOfUnramifiedValuationOfIsIntegralClosure_arithmeticFrobenius _root_.LocalFieldTheory.galoisGroupEquivZModOfUnramifiedValuationNormalized_arithmeticFrobenius _root_.LocalFieldTheory.galoisGroupEquivZModOfUnramifiedValuationNormalized_arithmeticFrobenius_zpow _root_.LocalFieldTheory.galoisGroupResidueAlgEquivOfIsIntegralClosure_arithmeticFrobenius _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.OAI.PrimeDegreePackets.ThetaConstruction.schwartzCM_apply _root_.infinitePlace_mult_smul
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false
/-! Provides the public declarations in the `LocalClassFieldTheory.Finite.Unramified.PrincipalUnits.Lift` Lean module. -/

noncomputable section

universe u

namespace LocalClassFieldTheory

open scoped ValuativeRel
open LocalFieldTheory
open LocalFieldTheory.IsNonarchimedeanLocalField
open Filter

/-- States the theorem `principalUnitsNormOfUnramifiedValuationOfIsIntegralClosure_lift_mod_succ`. -/
theorem principalUnitsNormOfUnramifiedValuationOfIsIntegralClosure_lift_mod_succ
    (K L : Type u)
    [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
    [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]
    [LocalFieldTheory.ValuativeExtension K L] [IsIntegralClosure 𝒪[L] 𝒪[K] L]
    [Module.Finite 𝒪[K] 𝒪[L]]
    [LocalFieldTheory.IsNonarchimedeanLocalField.IsUnramifiedValuedExtension K L]
    (n : Nat) (hn : 1 ≤ n) (y : principalUnits K n) :
    ∃ x : principalUnits L n,
      principalUnitsSuccQuotMk K n
          (principalUnitsNormOfUnramifiedValuationOfIsIntegralClosure K L n x) =
        principalUnitsSuccQuotMk K n y := by
  obtain ⟨q, hq⟩ :=
    principalUnitsSuccQuotNormOfUnramifiedValuationOfIsIntegralClosure_surjective
      K L n hn (principalUnitsSuccQuotMk K n y)
  obtain ⟨x, rfl⟩ := principalUnitsSuccQuotMk_surjective L n q
  refine ⟨x, ?_⟩
  simpa [principalUnitsSuccQuotNormOfUnramifiedValuationOfIsIntegralClosure_mk]
    using hq

/-- Actual integral-closure one-step correction form: the remaining error
after dividing the target by the chosen norm lies in the next principal-unit
filtration step. -/
theorem principalUnitsNormOfUnramifiedValuationOfIsIntegralClosure_div_lift_mem_succ
    (K L : Type u)
    [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
    [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]
    [LocalFieldTheory.ValuativeExtension K L] [IsIntegralClosure 𝒪[L] 𝒪[K] L]
    [Module.Finite 𝒪[K] 𝒪[L]]
    [LocalFieldTheory.IsNonarchimedeanLocalField.IsUnramifiedValuedExtension K L]
    (n : Nat) (hn : 1 ≤ n) (y : principalUnits K n) :
    ∃ x : principalUnits L n,
      y / principalUnitsNormOfUnramifiedValuationOfIsIntegralClosure K L n x ∈
        (principalUnits K (n + 1)).subgroupOf (principalUnits K n) := by
  obtain ⟨x, hx⟩ :=
    principalUnitsNormOfUnramifiedValuationOfIsIntegralClosure_lift_mod_succ K L n hn y
  refine ⟨x, ?_⟩
  exact (principalUnitsSuccQuotMk_eq_iff_div_mem K n y
    (principalUnitsNormOfUnramifiedValuationOfIsIntegralClosure K L n x)).1 hx.symm

/-- Actual integral-closure correction term selected from the current finite
approximation error. -/
noncomputable def chosenPrincipalUnitsNormOfUnramifiedValuationOfIsIntegralClosureApproxCorrection
    (K L : Type u)
    [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
    [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]
    [LocalFieldTheory.ValuativeExtension K L] [IsIntegralClosure 𝒪[L] 𝒪[K] L]
    [Module.Finite 𝒪[K] 𝒪[L]]
    [LocalFieldTheory.IsNonarchimedeanLocalField.IsUnramifiedValuedExtension K L]
    (n : Nat) (hn : 1 ≤ n) (y : principalUnits K n) (d : Nat)
    (s : {x : principalUnits L n //
        ((y : 𝒪[K]ˣ) / normIntegerUnits K L (x : 𝒪[L]ˣ)) ∈
          principalUnits K (n + d)}) :
    principalUnits L (n + d) :=
  let r : principalUnits K (n + d) :=
    ⟨(y : 𝒪[K]ˣ) / normIntegerUnits K L (s.1 : 𝒪[L]ˣ), s.2⟩
  have hnd : 1 ≤ n + d := le_trans hn (Nat.le_add_right n d)
  Classical.choose
    (principalUnitsNormOfUnramifiedValuationOfIsIntegralClosure_div_lift_mem_succ
      K L (n + d) hnd r)

/-- Actual integral-closure coherent update step for finite principal-unit
norm approximations. -/
noncomputable def principalUnitsNormOfUnramifiedValuationOfIsIntegralClosureApproxStep
    (K L : Type u)
    [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
    [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]
    [LocalFieldTheory.ValuativeExtension K L] [IsIntegralClosure 𝒪[L] 𝒪[K] L]
    [Module.Finite 𝒪[K] 𝒪[L]]
    [LocalFieldTheory.IsNonarchimedeanLocalField.IsUnramifiedValuedExtension K L]
    (n : Nat) (hn : 1 ≤ n) (y : principalUnits K n) (d : Nat)
    (s : {x : principalUnits L n //
        ((y : 𝒪[K]ˣ) / normIntegerUnits K L (x : 𝒪[L]ˣ)) ∈
          principalUnits K (n + d)}) :
    {x : principalUnits L n //
      ((y : 𝒪[K]ˣ) / normIntegerUnits K L (x : 𝒪[L]ˣ)) ∈
        principalUnits K (n + (d + 1))} := by
  let r : principalUnits K (n + d) :=
    ⟨(y : 𝒪[K]ˣ) / normIntegerUnits K L (s.1 : 𝒪[L]ˣ), s.2⟩
  let z : principalUnits L (n + d) :=
    chosenPrincipalUnitsNormOfUnramifiedValuationOfIsIntegralClosureApproxCorrection
      K L n hn y d s
  let x' : principalUnits L n :=
    ⟨(s.1 : 𝒪[L]ˣ) * (z : 𝒪[L]ˣ),
      (principalUnits L n).mul_mem s.1.2
        (principalUnits_antitone L (Nat.le_add_right n d) z.2)⟩
  have hz :
      (((r / principalUnitsNormOfUnramifiedValuationOfIsIntegralClosure K L
          (n + d) z : principalUnits K (n + d)) : 𝒪[K]ˣ) ∈
        principalUnits K ((n + d) + 1)) :=
    by
      have hnd : 1 ≤ n + d := le_trans hn (Nat.le_add_right n d)
      dsimp [z, chosenPrincipalUnitsNormOfUnramifiedValuationOfIsIntegralClosureApproxCorrection]
      exact Classical.choose_spec
        (principalUnitsNormOfUnramifiedValuationOfIsIntegralClosure_div_lift_mem_succ
          K L (n + d) hnd r)
  refine ⟨x', ?_⟩
  have hresEq :
      (y : 𝒪[K]ˣ) / normIntegerUnits K L (x' : 𝒪[L]ˣ) =
        ((r / principalUnitsNormOfUnramifiedValuationOfIsIntegralClosure K L
            (n + d) z : principalUnits K (n + d)) : 𝒪[K]ˣ) := by
    change
      (y : 𝒪[K]ˣ) / normIntegerUnits K L (x' : 𝒪[L]ˣ) =
        (r : 𝒪[K]ˣ) /
          ((principalUnitsNormOfUnramifiedValuationOfIsIntegralClosure K L
              (n + d) z : principalUnits K (n + d)) : 𝒪[K]ˣ)
    simp only [x', r, principalUnitsNormOfUnramifiedValuationOfIsIntegralClosure_apply,
      (normIntegerUnits K L).map_mul]
    exact div_mul_eq_div_div _ _ _
  rw [hresEq]
  simpa [Nat.add_assoc] using hz

/-- The quotient between successive actual integral-closure approximation
states lies in the expected depth. -/
theorem principalUnitsNormOfUnramifiedValuationOfIsIntegralClosureApproxStep_div_mem
    (K L : Type u)
    [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
    [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]
    [LocalFieldTheory.ValuativeExtension K L] [IsIntegralClosure 𝒪[L] 𝒪[K] L]
    [Module.Finite 𝒪[K] 𝒪[L]]
    [LocalFieldTheory.IsNonarchimedeanLocalField.IsUnramifiedValuedExtension K L]
    (n : Nat) (hn : 1 ≤ n) (y : principalUnits K n) (d : Nat)
    (s : {x : principalUnits L n //
        ((y : 𝒪[K]ˣ) / normIntegerUnits K L (x : 𝒪[L]ˣ)) ∈
          principalUnits K (n + d)}) :
    (((principalUnitsNormOfUnramifiedValuationOfIsIntegralClosureApproxStep
          K L n hn y d s).1 : 𝒪[L]ˣ) /
        (s.1 : 𝒪[L]ˣ)) ∈ principalUnits L (n + d) := by
  let z : principalUnits L (n + d) :=
    chosenPrincipalUnitsNormOfUnramifiedValuationOfIsIntegralClosureApproxCorrection
      K L n hn y d s
  change (((s.1 : 𝒪[L]ˣ) * (z : 𝒪[L]ˣ)) / (s.1 : 𝒪[L]ˣ)) ∈
    principalUnits L (n + d)
  rw [mul_div_cancel_left]
  exact z.2

/-- Actual integral-closure coherent finite principal-unit norm
approximations. -/
noncomputable def principalUnitsNormOfUnramifiedValuationOfIsIntegralClosureApproxState
    (K L : Type u)
    [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
    [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]
    [LocalFieldTheory.ValuativeExtension K L] [IsIntegralClosure 𝒪[L] 𝒪[K] L]
    [Module.Finite 𝒪[K] 𝒪[L]]
    [LocalFieldTheory.IsNonarchimedeanLocalField.IsUnramifiedValuedExtension K L]
    (n : Nat) (hn : 1 ≤ n) (y : principalUnits K n) :
    (d : Nat) →
      {x : principalUnits L n //
        ((y : 𝒪[K]ˣ) / normIntegerUnits K L (x : 𝒪[L]ˣ)) ∈
          principalUnits K (n + d)}
  | 0 => by
      refine ⟨1, ?_⟩
      change (y : 𝒪[K]ˣ) / normIntegerUnits K L (1 : 𝒪[L]ˣ) ∈
        principalUnits K (n + 0)
      rw [(normIntegerUnits K L).map_one, div_one, Nat.add_zero]
      exact y.2
  | d + 1 =>
      principalUnitsNormOfUnramifiedValuationOfIsIntegralClosureApproxStep K L n hn y d
        (principalUnitsNormOfUnramifiedValuationOfIsIntegralClosureApproxState
          K L n hn y d)

/-- Consecutive actual integral-closure approximation states differ by a
correction term in the expected depth. -/
theorem principalUnitsNormOfUnramifiedValuationOfIsIntegralClosureApproxState_succ_div_mem
    (K L : Type u)
    [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
    [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]
    [LocalFieldTheory.ValuativeExtension K L] [IsIntegralClosure 𝒪[L] 𝒪[K] L]
    [Module.Finite 𝒪[K] 𝒪[L]]
    [LocalFieldTheory.IsNonarchimedeanLocalField.IsUnramifiedValuedExtension K L]
    (n : Nat) (hn : 1 ≤ n) (y : principalUnits K n) (d : Nat) :
    ((((principalUnitsNormOfUnramifiedValuationOfIsIntegralClosureApproxState
          K L n hn y (d + 1)).1 : principalUnits L n) : 𝒪[L]ˣ) /
        (((principalUnitsNormOfUnramifiedValuationOfIsIntegralClosureApproxState
          K L n hn y d).1 : principalUnits L n) : 𝒪[L]ˣ)) ∈
      principalUnits L (n + d) := by
  change
    (((principalUnitsNormOfUnramifiedValuationOfIsIntegralClosureApproxStep K L n hn y d
          (principalUnitsNormOfUnramifiedValuationOfIsIntegralClosureApproxState
            K L n hn y d)).1 : 𝒪[L]ˣ) /
        ((principalUnitsNormOfUnramifiedValuationOfIsIntegralClosureApproxState
          K L n hn y d).1 : 𝒪[L]ˣ)) ∈ principalUnits L (n + d)
  exact principalUnitsNormOfUnramifiedValuationOfIsIntegralClosureApproxStep_div_mem
    K L n hn y d
    (principalUnitsNormOfUnramifiedValuationOfIsIntegralClosureApproxState
      K L n hn y d)

/-- The actual integral-closure correction sequence encoded by consecutive
coherent approximation states. -/
noncomputable def chosenPrincipalUnitsNormOfUnramifiedValuationOfIsIntegralClosureApproxCorrectionSeq
    (K L : Type u)
    [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
    [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]
    [LocalFieldTheory.ValuativeExtension K L] [IsIntegralClosure 𝒪[L] 𝒪[K] L]
    [Module.Finite 𝒪[K] 𝒪[L]]
    [LocalFieldTheory.IsNonarchimedeanLocalField.IsUnramifiedValuedExtension K L]
    (n : Nat) (hn : 1 ≤ n) (y : principalUnits K n) :
    ∀ d : Nat, principalUnits L (n + d) :=
  fun d =>
    ⟨(((principalUnitsNormOfUnramifiedValuationOfIsIntegralClosureApproxState
          K L n hn y (d + 1)).1 : principalUnits L n) : 𝒪[L]ˣ) /
        (((principalUnitsNormOfUnramifiedValuationOfIsIntegralClosureApproxState
          K L n hn y d).1 : principalUnits L n) : 𝒪[L]ˣ),
      principalUnitsNormOfUnramifiedValuationOfIsIntegralClosureApproxState_succ_div_mem
        K L n hn y d⟩

/-- The finite product of the actual integral-closure correction sequence is
the corresponding coherent approximation state. -/
theorem principalUnitsCorrectionProduct_approxCorrectionSeqOfIsIntegralClosure
    (K L : Type u)
    [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
    [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]
    [LocalFieldTheory.ValuativeExtension K L] [IsIntegralClosure 𝒪[L] 𝒪[K] L]
    [Module.Finite 𝒪[K] 𝒪[L]]
    [LocalFieldTheory.IsNonarchimedeanLocalField.IsUnramifiedValuedExtension K L]
    (n : Nat) (hn : 1 ≤ n) (y : principalUnits K n) (d : Nat) :
    principalUnitsCorrectionProduct L n
        (chosenPrincipalUnitsNormOfUnramifiedValuationOfIsIntegralClosureApproxCorrectionSeq
          K L n hn y) d =
      (((principalUnitsNormOfUnramifiedValuationOfIsIntegralClosureApproxState
          K L n hn y d).1 : principalUnits L n) : 𝒪[L]ˣ) := by
  induction d with
  | zero =>
      simp [principalUnitsCorrectionProduct_zero,
        principalUnitsNormOfUnramifiedValuationOfIsIntegralClosureApproxState]
  | succ d ih =>
      rw [principalUnitsCorrectionProduct_succ, ih]
      change
        (((principalUnitsNormOfUnramifiedValuationOfIsIntegralClosureApproxState
            K L n hn y d).1 : principalUnits L n) : 𝒪[L]ˣ) *
            ((((principalUnitsNormOfUnramifiedValuationOfIsIntegralClosureApproxState
              K L n hn y (d + 1)).1 : principalUnits L n) : 𝒪[L]ˣ) /
              (((principalUnitsNormOfUnramifiedValuationOfIsIntegralClosureApproxState
                K L n hn y d).1 : principalUnits L n) : 𝒪[L]ˣ)) =
          (((principalUnitsNormOfUnramifiedValuationOfIsIntegralClosureApproxState
            K L n hn y (d + 1)).1 : principalUnits L n) : 𝒪[L]ˣ)
      rw [mul_comm, div_mul_cancel]

/-- The actual integral-closure coherent finite approximation states have a
principal-unit limit.  This is the unramified infinite-product step specialized
to the actual correction terms generated above. -/
theorem exists_tendsto_principalUnitsNormOfUnramifiedValuationOfIsIntegralClosureApproxState
    (K L : Type u)
    [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    [Field L] [ValuativeRel L] [UniformSpace L] [IsUniformAddGroup L]
    [IsNonarchimedeanLocalField L]
    [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]
    [LocalFieldTheory.ValuativeExtension K L] [IsIntegralClosure 𝒪[L] 𝒪[K] L]
    [Module.Finite 𝒪[K] 𝒪[L]]
    [LocalFieldTheory.IsNonarchimedeanLocalField.IsUnramifiedValuedExtension K L]
    (n : Nat) (hn : 1 ≤ n) (y : principalUnits K n) :
    ∃ x : principalUnits L n, Filter.Tendsto
      (fun d : Nat =>
        ((((principalUnitsNormOfUnramifiedValuationOfIsIntegralClosureApproxState
          K L n hn y d).1 : principalUnits L n) : 𝒪[L]ˣ) : 𝒪[L]))
      Filter.atTop (nhds (((x : principalUnits L n) : 𝒪[L]ˣ) : 𝒪[L])) := by
  obtain ⟨x, hx⟩ :=
    exists_tendsto_principalUnitsCorrectionProduct_principalUnit L n hn
      (chosenPrincipalUnitsNormOfUnramifiedValuationOfIsIntegralClosureApproxCorrectionSeq
        K L n hn y)
  refine ⟨x, ?_⟩
  have hseq :
      (fun d : Nat =>
        ((principalUnitsCorrectionProduct L n
            (chosenPrincipalUnitsNormOfUnramifiedValuationOfIsIntegralClosureApproxCorrectionSeq
              K L n hn y) d : 𝒪[L]ˣ) : 𝒪[L])) =
        (fun d : Nat =>
          ((((principalUnitsNormOfUnramifiedValuationOfIsIntegralClosureApproxState
            K L n hn y d).1 : principalUnits L n) : 𝒪[L]ˣ) : 𝒪[L])) := by
    funext d
    rw [principalUnitsCorrectionProduct_approxCorrectionSeqOfIsIntegralClosure
      K L n hn y d]
  simpa [hseq] using hx

/-- The actual integral-closure coherent approximation state has the
advertised finite-depth error bound. -/
theorem principalUnitsNormOfUnramifiedValuationOfIsIntegralClosureApproxState_error_mem
    (K L : Type u)
    [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
    [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]
    [LocalFieldTheory.ValuativeExtension K L] [IsIntegralClosure 𝒪[L] 𝒪[K] L]
    [Module.Finite 𝒪[K] 𝒪[L]]
    [LocalFieldTheory.IsNonarchimedeanLocalField.IsUnramifiedValuedExtension K L]
    (n : Nat) (hn : 1 ≤ n) (y : principalUnits K n) (d : Nat) :
    ((y : 𝒪[K]ˣ) /
        normIntegerUnits K L
          ((principalUnitsNormOfUnramifiedValuationOfIsIntegralClosureApproxState
            K L n hn y d).1 : 𝒪[L]ˣ)) ∈
      principalUnits K (n + d) :=
  (principalUnitsNormOfUnramifiedValuationOfIsIntegralClosureApproxState
    K L n hn y d).2

/-- Actual integral-closure norm-continuity form used in principal-unit norm lifting.
It is derived from multiplicativity of the integer-unit norm and
the actual proof that the unramified norm preserves principal-unit levels. -/
theorem eventually_normIntegerUnits_div_mem_principalUnits_of_tendsto_units_of_isIntegralClosure
    (K L : Type u)
    [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    [Field L] [ValuativeRel L] [UniformSpace L] [IsUniformAddGroup L]
    [IsNonarchimedeanLocalField L]
    [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]
    [LocalFieldTheory.ValuativeExtension K L] [IsIntegralClosure 𝒪[L] 𝒪[K] L]
    [Module.Finite 𝒪[K] 𝒪[L]]
    [LocalFieldTheory.IsNonarchimedeanLocalField.IsUnramifiedValuedExtension K L]
    {f : Nat → 𝒪[L]ˣ} {x : 𝒪[L]ˣ} (n : Nat)
    (hf : Tendsto (fun d : Nat => ((f d : 𝒪[L]ˣ) : 𝒪[L])) atTop
      (nhds ((x : 𝒪[L]ˣ) : 𝒪[L]))) :
    ∀ᶠ d in atTop,
      normIntegerUnits K L (f d) / normIntegerUnits K L x ∈ principalUnits K n := by
  have hdiv := eventually_div_mem_principalUnits_of_tendsto_units L n hf
  filter_upwards [hdiv] with d hd
  have hnorm : normIntegerUnits K L (f d / x) ∈ principalUnits K n :=
    normIntegerUnits_mem_principalUnits_of_unramifiedValuation_of_isIntegralClosure
      K L n (f d / x) hd
  simpa [(normIntegerUnits K L).map_div] using hnorm

/-- The limit of the actual integral-closure coherent approximation states
preserves all finite-depth error bounds. -/
theorem principalUnitsNormOfUnramifiedValuationOfIsIntegralClosureApproxState_limit_error_mem_add_all
    (K L : Type u)
    [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    [Field L] [ValuativeRel L] [UniformSpace L] [IsUniformAddGroup L]
    [IsNonarchimedeanLocalField L]
    [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]
    [LocalFieldTheory.ValuativeExtension K L] [IsIntegralClosure 𝒪[L] 𝒪[K] L]
    [Module.Finite 𝒪[K] 𝒪[L]]
    [LocalFieldTheory.IsNonarchimedeanLocalField.IsUnramifiedValuedExtension K L]
    (n : Nat) (hn : 1 ≤ n) (y : principalUnits K n)
    (x : principalUnits L n)
    (hx : Tendsto
      (fun d : Nat =>
        ((((principalUnitsNormOfUnramifiedValuationOfIsIntegralClosureApproxState
          K L n hn y d).1 : principalUnits L n) : 𝒪[L]ˣ) : 𝒪[L]))
      atTop (nhds (((x : principalUnits L n) : 𝒪[L]ˣ) : 𝒪[L]))) :
    ∀ d : Nat,
      ((y : 𝒪[K]ˣ) / normIntegerUnits K L (x : 𝒪[L]ˣ)) ∈
        principalUnits K (n + d) := by
  intro d
  let f : Nat → 𝒪[L]ˣ := fun i =>
    (((principalUnitsNormOfUnramifiedValuationOfIsIntegralClosureApproxState
      K L n hn y i).1 : principalUnits L n) : 𝒪[L]ˣ)
  have hnormEv : ∀ᶠ i in atTop,
      normIntegerUnits K L (f i) / normIntegerUnits K L (x : 𝒪[L]ˣ) ∈
        principalUnits K (n + d) := by
    exact
      eventually_normIntegerUnits_div_mem_principalUnits_of_tendsto_units_of_isIntegralClosure
        K L (n + d) hx
  have hge : ∀ᶠ i : Nat in atTop, d ≤ i := eventually_ge_atTop d
  rcases (hnormEv.and hge).exists with ⟨i, hboth⟩
  rcases hboth with ⟨hnorm, hdi⟩
  have herrDeep :
      ((y : 𝒪[K]ˣ) /
          normIntegerUnits K L
            ((principalUnitsNormOfUnramifiedValuationOfIsIntegralClosureApproxState
              K L n hn y i).1 : 𝒪[L]ˣ)) ∈
        principalUnits K (n + i) :=
    principalUnitsNormOfUnramifiedValuationOfIsIntegralClosureApproxState_error_mem
      K L n hn y i
  have herr :
      ((y : 𝒪[K]ˣ) /
          normIntegerUnits K L
            ((principalUnitsNormOfUnramifiedValuationOfIsIntegralClosureApproxState
              K L n hn y i).1 : 𝒪[L]ˣ)) ∈
        principalUnits K (n + d) :=
    principalUnits_antitone K (Nat.add_le_add_left hdi n) herrDeep
  have heq :
      (y : 𝒪[K]ˣ) / normIntegerUnits K L (x : 𝒪[L]ˣ) =
        ((y : 𝒪[K]ˣ) /
          normIntegerUnits K L
            ((principalUnitsNormOfUnramifiedValuationOfIsIntegralClosureApproxState
              K L n hn y i).1 : 𝒪[L]ˣ)) *
        (normIntegerUnits K L
            ((principalUnitsNormOfUnramifiedValuationOfIsIntegralClosureApproxState
              K L n hn y i).1 : 𝒪[L]ˣ) /
          normIntegerUnits K L (x : 𝒪[L]ˣ)) := by
    simp [div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm]
  rw [heq]
  exact (principalUnits K (n + d)).mul_mem herr (by simpa [f] using hnorm)

/-- Actual integral-closure separatedness step: if the error of a candidate
principal-unit norm lift lies in every deeper principal-unit subgroup, the
candidate is exact. -/
theorem principalUnitsNormOfUnramifiedValuationOfIsIntegralClosure_eq_of_error_mem_add_all
    (K L : Type u)
    [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
    [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]
    [LocalFieldTheory.ValuativeExtension K L] [IsIntegralClosure 𝒪[L] 𝒪[K] L]
    [Module.Finite 𝒪[K] 𝒪[L]]
    [LocalFieldTheory.IsNonarchimedeanLocalField.IsUnramifiedValuedExtension K L]
    (n : Nat) (y : principalUnits K n) (x : principalUnits L n)
    (h : ∀ d : Nat,
      ((y : 𝒪[K]ˣ) / normIntegerUnits K L (x : 𝒪[L]ˣ)) ∈
        principalUnits K (n + d)) :
    (y : 𝒪[K]ˣ) = normIntegerUnits K L (x : 𝒪[L]ˣ) := by
  have hOne :
      (y : 𝒪[K]ˣ) / normIntegerUnits K L (x : 𝒪[L]ˣ) = 1 :=
    principalUnits_eq_one_of_mem_add_all K n
      ((y : 𝒪[K]ˣ) / normIntegerUnits K L (x : 𝒪[L]ˣ)) h
  exact div_eq_one.mp hOne

/-- Principal-unit norm surjectivity for actual integral closures: in a finite
unramified valuation extension, the integer-unit norm is
surjective on every `U^n`, `n ≥ 1`. -/
theorem principalUnitsNormOfUnramifiedValuationOfIsIntegralClosure_surjective
    (K L : Type u)
    [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    [Field L] [ValuativeRel L] [UniformSpace L] [IsUniformAddGroup L]
    [IsNonarchimedeanLocalField L]
    [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]
    [LocalFieldTheory.ValuativeExtension K L] [IsIntegralClosure 𝒪[L] 𝒪[K] L]
    [Module.Finite 𝒪[K] 𝒪[L]]
    [LocalFieldTheory.IsNonarchimedeanLocalField.IsUnramifiedValuedExtension K L]
    (n : Nat) (hn : 1 ≤ n) :
    Function.Surjective (principalUnitsNormOfUnramifiedValuationOfIsIntegralClosure K L n) := by
  intro y
  obtain ⟨x, hx⟩ :=
    exists_tendsto_principalUnitsNormOfUnramifiedValuationOfIsIntegralClosureApproxState
      K L n hn y
  refine ⟨x, ?_⟩
  have hmem :=
    principalUnitsNormOfUnramifiedValuationOfIsIntegralClosureApproxState_limit_error_mem_add_all
      K L n hn y x hx
  have hEq :
      (y : 𝒪[K]ˣ) = normIntegerUnits K L (x : 𝒪[L]ˣ) :=
    principalUnitsNormOfUnramifiedValuationOfIsIntegralClosure_eq_of_error_mem_add_all
      K L n y x hmem
  apply Subtype.ext
  simpa [principalUnitsNormOfUnramifiedValuationOfIsIntegralClosure_apply] using hEq.symm

end LocalClassFieldTheory
end
end

section
-- module Solutions.OAIQ244_DUKE.LocalClassFieldTheory_Finite_Unramified_ResidueNorm
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.residueFieldZModAlgebra _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.LubinTate.Valuations.exponentialValuationSubringIsLocalRing _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionFixedSubring.instIsLocalRing _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionResidueField.instField _root_.RamificationTheory.HilbertRamification.ValuationSubring.selectedResidueField.instAlgebra _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.maximalIdealPowSuccQuotModule _root_.ValuationTheory.DiscreteValuationField.DVF.residueField.field _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.isDomain _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.isLocalRing _root_.CyclicCohomology.binaryCoefficientFamilyCommGroup _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.LocalClassFieldTheory.normalizationIntegerRingIsIntegralClosure _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.chosenFinitePlaceCompletionAlgebra _root_.finiteLocalUnitsOpen _root_.relativeAdeleRingIntermediateAlgebra _root_.relativeAdeleRingTopIntermediateAlgebra
attribute [-simp] _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.CyclicCohomology.integerUnitsModPrincipalUnitsAtLevelConcreteEquiv_mk _root_.CyclicCohomology.integerUnitsModPrincipalUnitsAtLevelLift_mk _root_.CyclicCohomology.integerUnitsModPrincipalUnitsAtLevelMk_eq_iff_div_mem _root_.CyclicCohomology.principalUnitsSuccQuotToIntegerUnitsModPrincipalUnitsSucc_mk _root_.IsDiscreteValuationRing.addVal_ringEquiv _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.LocalClassFieldTheory.chosenNormalBasisPrincipalUnitSequenceAsPrincipalUnits_val _root_.LocalFieldTheory.galoisGroupEquivResidueAlgEquivOfUnramifiedValuationOfIsIntegralClosure_arithmeticFrobenius _root_.LocalFieldTheory.galoisGroupEquivZModOfUnramifiedValuationNormalized_arithmeticFrobenius _root_.LocalFieldTheory.galoisGroupEquivZModOfUnramifiedValuationNormalized_arithmeticFrobenius_zpow _root_.LocalFieldTheory.galoisGroupResidueAlgEquivOfIsIntegralClosure_arithmeticFrobenius _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.OAI.PrimeDegreePackets.ThetaConstruction.schwartzCM_apply _root_.infinitePlace_mult_smul
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false
/-! Provides the public declarations in the `LocalClassFieldTheory.Finite.Unramified.ResidueNorm` Lean module. -/

noncomputable section

universe u

namespace LocalClassFieldTheory

open scoped ValuativeRel
open LocalFieldTheory
open LocalFieldTheory.IsNonarchimedeanLocalField

/-- The integral-closure quotient norm on first
principal-unit quotients in an unramified valuation extension.  This is the
the unramified norm calculation residue-unit quotient before the later `U^1` lifting. -/
noncomputable def integerUnitsModPrincipalUnitsNormOfGaloisOfIsIntegralClosure
    (K L : Type u)
    [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
    [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]
    [LocalFieldTheory.ValuativeExtension K L] [IsIntegralClosure 𝒪[L] 𝒪[K] L]
    [Module.Finite 𝒪[K] 𝒪[L]]
    [LocalFieldTheory.IsNonarchimedeanLocalField.IsUnramifiedValuedExtension K L] :
    IntegerUnitsModPrincipalUnits L →* IntegerUnitsModPrincipalUnits K :=
  integerUnitsModPrincipalUnitsLift
    ((integerUnitsModPrincipalUnitsMk K).comp (normIntegerUnits K L))
    (by
      intro u hu
      rw [MonoidHom.mem_ker, MonoidHom.comp_apply,
        IntegerUnitsModPrincipalUnits_mk_eq_one_iff]
      exact normIntegerUnits_mem_principalUnits_of_unramifiedValuation_of_isIntegralClosure
        K L 1 u hu)

/-- States the theorem `integerUnitsModPrincipalUnitsNormOfGaloisOfIsIntegralClosure_mk`. -/
@[simp]
theorem integerUnitsModPrincipalUnitsNormOfGaloisOfIsIntegralClosure_mk
    (K L : Type u)
    [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
    [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]
    [LocalFieldTheory.ValuativeExtension K L] [IsIntegralClosure 𝒪[L] 𝒪[K] L]
    [Module.Finite 𝒪[K] 𝒪[L]]
    [LocalFieldTheory.IsNonarchimedeanLocalField.IsUnramifiedValuedExtension K L]
    (u : 𝒪[L]ˣ) :
    integerUnitsModPrincipalUnitsNormOfGaloisOfIsIntegralClosure K L
        (integerUnitsModPrincipalUnitsMk L u) =
      integerUnitsModPrincipalUnitsMk K (normIntegerUnits K L u) :=
  integerUnitsModPrincipalUnitsLift_mk
    ((integerUnitsModPrincipalUnitsMk K).comp (normIntegerUnits K L)) _ u

/-- After extending the residue of the integer-unit norm back to `𝓀[L]`, it
is the product of the integral-closure residue actions. -/
theorem residueUnitsMap_normIntegerUnits_eq_galoisGroup_residue_prod_of_isIntegralClosure
    (K L : Type u)
    [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
    [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]
    [LocalFieldTheory.ValuativeExtension K L] [IsIntegralClosure 𝒪[L] 𝒪[K] L]
    (u : 𝒪[L]ˣ) :
    residueUnitsMapOfValuationExtension K L
        (integerUnitsToResidueUnits K (normIntegerUnits K L u)) =
      Finset.univ.prod (fun σ : Gal(L / K) =>
        Units.mapEquiv
          (galoisGroupResidueFieldEquivOfIsIntegralClosure K L σ).toMulEquiv
          (integerUnitsToResidueUnits L u)) := by
  rw [residueUnitsMap_integerUnitsToResidueUnits K L (normIntegerUnits K L u)]
  rw [integerUnitsMap_normIntegerUnits_eq_galoisGroup_prod_of_isIntegralClosure K L u]
  rw [map_prod]
  apply Finset.prod_congr rfl
  intro σ _
  exact
    (galoisGroupResidueFieldEquivOfIsIntegralClosure_integerUnitsToResidueUnits
      K L σ u).symm

/-- AlgEquiv-typed form of
`residueUnitsMap_normIntegerUnits_eq_galoisGroup_residue_prod_of_isIntegralClosure`. -/
theorem residueUnitsMap_normIntegerUnits_eq_galoisGroup_residue_algEquiv_prod_of_isIntegralClosure
    (K L : Type u)
    [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
    [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]
    [LocalFieldTheory.ValuativeExtension K L] [IsIntegralClosure 𝒪[L] 𝒪[K] L]
    (u : 𝒪[L]ˣ) :
    residueUnitsMapOfValuationExtension K L
        (integerUnitsToResidueUnits K (normIntegerUnits K L u)) =
      Finset.univ.prod (fun σ : Gal(L / K) =>
        Units.mapEquiv
          (galoisGroupResidueAlgEquivOfIsIntegralClosure K L σ).toMulEquiv
          (integerUnitsToResidueUnits L u)) := by
  rw [residueUnitsMap_normIntegerUnits_eq_galoisGroup_residue_prod_of_isIntegralClosure
    K L u]
  apply Finset.prod_congr rfl
  intro σ _
  apply Units.ext
  rfl

/-- Quotient-level form of the residue product formula for the
integer-unit norm. -/
theorem integerUnitsModPrincipalUnitsNormOfGaloisOfIsIntegralClosure_residue_algEquiv_base_extend
    (K L : Type u)
    [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
    [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]
    [LocalFieldTheory.ValuativeExtension K L] [IsIntegralClosure 𝒪[L] 𝒪[K] L]
    [Module.Finite 𝒪[K] 𝒪[L]]
    [LocalFieldTheory.IsNonarchimedeanLocalField.IsUnramifiedValuedExtension K L]
    (x : IntegerUnitsModPrincipalUnits L) :
    residueUnitsMapOfValuationExtension K L
        (integerUnitsModPrincipalUnitsEquivResidueUnits K
          (integerUnitsModPrincipalUnitsNormOfGaloisOfIsIntegralClosure K L x)) =
      Finset.univ.prod (fun σ : Gal(L / K) =>
        Units.mapEquiv
          (galoisGroupResidueAlgEquivOfIsIntegralClosure K L σ).toMulEquiv
          (integerUnitsModPrincipalUnitsEquivResidueUnits L x)) := by
  refine IntegerUnitsModPrincipalUnits.inductionOn
    (motive := fun x =>
      residueUnitsMapOfValuationExtension K L
          (integerUnitsModPrincipalUnitsEquivResidueUnits K
            (integerUnitsModPrincipalUnitsNormOfGaloisOfIsIntegralClosure K L x)) =
        Finset.univ.prod (fun σ : Gal(L / K) =>
          Units.mapEquiv
            (galoisGroupResidueAlgEquivOfIsIntegralClosure K L σ).toMulEquiv
            (integerUnitsModPrincipalUnitsEquivResidueUnits L x)))
    x ?_
  intro u
  rw [integerUnitsModPrincipalUnitsNormOfGaloisOfIsIntegralClosure_mk]
  rw [integerUnitsModPrincipalUnitsEquivResidueUnits_mk]
  rw [integerUnitsModPrincipalUnitsEquivResidueUnits_mk]
  exact
    residueUnitsMap_normIntegerUnits_eq_galoisGroup_residue_algEquiv_prod_of_isIntegralClosure
      K L u

/-- In the unramified valuation case, the integral-closure quotient norm
agrees after base extension with the quotient-level finite residue norm model. -/
theorem integerUnitsModPrincipalUnitsNormOfGaloisOfIsIntegralClosure_residue_base_extend_eq_residueNorm
    (K L : Type u)
    [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
    [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]
    [LocalFieldTheory.ValuativeExtension K L] [IsIntegralClosure 𝒪[L] 𝒪[K] L]
    [Module.Finite 𝒪[K] 𝒪[L]]
    [LocalFieldTheory.IsNonarchimedeanLocalField.IsUnramifiedValuedExtension K L]
    (x : IntegerUnitsModPrincipalUnits L) :
    residueUnitsMapOfValuationExtension K L
        (integerUnitsModPrincipalUnitsEquivResidueUnits K
          (integerUnitsModPrincipalUnitsNormOfGaloisOfIsIntegralClosure K L x)) =
      residueUnitsMapOfValuationExtension K L
        (integerUnitsModPrincipalUnitsEquivResidueUnits K
          (integerUnitsModPrincipalUnitsResidueNormOfValuationExtension K L x)) := by
  rw [integerUnitsModPrincipalUnitsNormOfGaloisOfIsIntegralClosure_residue_algEquiv_base_extend]
  rw [integerUnitsModPrincipalUnitsResidueNorm_base_extend_eq_prod_algEquiv]
  exact
    galoisGroupResidueAlgEquivOfIsIntegralClosure_prod_eq_prod_algEquiv_of_unramifiedValuation
      K L (integerUnitsModPrincipalUnitsEquivResidueUnits L x)

/-- In the unramified valuation case, the actual integral-closure quotient norm
on `𝒪[L]ˣ/U_L¹` is the quotient-level finite-field residue norm model. -/
theorem integerUnitsModPrincipalUnitsNormOfGaloisOfIsIntegralClosure_eq_residueNorm_of_unramifiedValuation
    (K L : Type u)
    [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
    [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]
    [LocalFieldTheory.ValuativeExtension K L] [IsIntegralClosure 𝒪[L] 𝒪[K] L]
    [Module.Finite 𝒪[K] 𝒪[L]]
    [LocalFieldTheory.IsNonarchimedeanLocalField.IsUnramifiedValuedExtension K L] :
    integerUnitsModPrincipalUnitsNormOfGaloisOfIsIntegralClosure K L =
      integerUnitsModPrincipalUnitsResidueNormOfValuationExtension K L := by
  apply MonoidHom.ext
  intro x
  apply (integerUnitsModPrincipalUnitsEquivResidueUnits K).injective
  apply residueUnitsMapOfValuationExtension_injective K L
  exact
    integerUnitsModPrincipalUnitsNormOfGaloisOfIsIntegralClosure_residue_base_extend_eq_residueNorm
      K L x

/-- The actual integral-closure quotient norm on `𝒪[L]ˣ/U_L¹` is surjective in
the unramified valuation case. -/
theorem integerUnitsModPrincipalUnitsNormOfGaloisOfIsIntegralClosure_surjective_of_unramifiedValuation
    (K L : Type u)
    [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
    [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]
    [LocalFieldTheory.ValuativeExtension K L] [IsIntegralClosure 𝒪[L] 𝒪[K] L]
    [Module.Finite 𝒪[K] 𝒪[L]]
    [LocalFieldTheory.IsNonarchimedeanLocalField.IsUnramifiedValuedExtension K L] :
    Function.Surjective
      (integerUnitsModPrincipalUnitsNormOfGaloisOfIsIntegralClosure K L) := by
  rw [integerUnitsModPrincipalUnitsNormOfGaloisOfIsIntegralClosure_eq_residueNorm_of_unramifiedValuation
    K L]
  exact integerUnitsModPrincipalUnitsResidueNorm_surjective_of_valuationExtension K L

end LocalClassFieldTheory
end
end

section
-- module Solutions.OAIQ244_DUKE.LocalClassFieldTheory_Finite_Unramified_Norm
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.residueFieldZModAlgebra _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.LubinTate.compatibleGroupFamiliesGroup _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.RamificationTheory.HilbertRamification.ValuationSubring.selectedResidueField.instAlgebra _root_.RayClass.approximationCompletionTopologicalSpace _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.maximalIdealPowSuccQuotModule _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.CyclicCohomology.binaryCoefficientFamilyCommGroup _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.LocalClassFieldTheory.normalizationIntegerRingIsIntegralClosure _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.chosenFinitePlaceCompletionAlgebra _root_.finiteLocalUnitsOpen _root_.relativeAdeleRingIntermediateAlgebra _root_.relativeAdeleRingTopIntermediateAlgebra
attribute [-simp] _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.CyclicCohomology.integerUnitsModPrincipalUnitsAtLevelConcreteEquiv_mk _root_.CyclicCohomology.integerUnitsModPrincipalUnitsAtLevelLift_mk _root_.CyclicCohomology.integerUnitsModPrincipalUnitsAtLevelMk_eq_iff_div_mem _root_.CyclicCohomology.principalUnitsSuccQuotToIntegerUnitsModPrincipalUnitsSucc_mk _root_.IsDiscreteValuationRing.addVal_ringEquiv _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.LocalClassFieldTheory.chosenNormalBasisPrincipalUnitSequenceAsPrincipalUnits_val _root_.LocalFieldTheory.galoisGroupEquivResidueAlgEquivOfUnramifiedValuationOfIsIntegralClosure_arithmeticFrobenius _root_.LocalFieldTheory.galoisGroupEquivZModOfUnramifiedValuationNormalized_arithmeticFrobenius _root_.LocalFieldTheory.galoisGroupEquivZModOfUnramifiedValuationNormalized_arithmeticFrobenius_zpow _root_.LocalFieldTheory.galoisGroupResidueAlgEquivOfIsIntegralClosure_arithmeticFrobenius _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.OAI.PrimeDegreePackets.ThetaConstruction.schwartzCM_apply _root_.infinitePlace_mult_smul
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false
/-! Provides the public declarations in the `LocalClassFieldTheory.Finite.Unramified.Norm` Lean module. -/

noncomputable section

universe u

namespace LocalClassFieldTheory


open scoped ValuativeRel
open LocalFieldTheory
open LocalFieldTheory.IsNonarchimedeanLocalField

/-- For a finite unramified extension, actual integral-closure integer-unit
norm surjectivity: combine the quotient norm on `𝒪[L]ˣ/U_L¹` with the
actual `U_L¹ -> U_K¹` lifting. -/
theorem normIntegerUnits_surjective_unramified_of_isIntegralClosure
    (K L : Type u)
    [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    [Field L] [ValuativeRel L] [UniformSpace L] [IsUniformAddGroup L]
    [IsNonarchimedeanLocalField L]
    [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]
    [LocalFieldTheory.ValuativeExtension K L] [IsIntegralClosure 𝒪[L] 𝒪[K] L]
    [Module.Finite 𝒪[K] 𝒪[L]]
    [LocalFieldTheory.IsNonarchimedeanLocalField.IsUnramifiedValuedExtension K L] :
    Function.Surjective (normIntegerUnits K L) := by
  intro y
  obtain ⟨q, hq⟩ :=
    integerUnitsModPrincipalUnitsNormOfGaloisOfIsIntegralClosure_surjective_of_unramifiedValuation
      K L (QuotientGroup.mk y : IntegerUnitsModPrincipalUnits K)
  obtain ⟨u, rfl⟩ := Quotient.exists_rep q
  have hclass :
      (QuotientGroup.mk (normIntegerUnits K L u) : IntegerUnitsModPrincipalUnits K) =
        QuotientGroup.mk y := by
    change integerUnitsModPrincipalUnitsNormOfGaloisOfIsIntegralClosure K L
        (integerUnitsModPrincipalUnitsMk L u) =
      integerUnitsModPrincipalUnitsMk K y at hq
    rw [integerUnitsModPrincipalUnitsNormOfGaloisOfIsIntegralClosure_mk] at hq
    exact hq
  have hresInv : normIntegerUnits K L u / y ∈ principalUnits K 1 :=
    (IntegerUnitsModPrincipalUnits_mk_eq_mk_iff K (normIntegerUnits K L u) y).1 hclass
  have hres : y / normIntegerUnits K L u ∈ principalUnits K 1 := by
    have hinv : (normIntegerUnits K L u / y)⁻¹ ∈ principalUnits K 1 :=
      (principalUnits K 1).inv_mem hresInv
    simpa [div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm] using hinv
  let r : principalUnits K 1 := ⟨y / normIntegerUnits K L u, hres⟩
  obtain ⟨z, hz⟩ :=
    principalUnitsNormOfUnramifiedValuationOfIsIntegralClosure_surjective
      K L 1 (Nat.le_refl 1) r
  refine ⟨u * (z : 𝒪[L]ˣ), ?_⟩
  have hzUnits : normIntegerUnits K L (z : 𝒪[L]ˣ) = y / normIntegerUnits K L u := by
    have hzUnitsSub := congrArg (fun w : principalUnits K 1 => (w : 𝒪[K]ˣ)) hz
    simpa [principalUnitsNormOfUnramifiedValuationOfIsIntegralClosure_apply, r]
      using hzUnitsSub
  calc
    normIntegerUnits K L (u * (z : 𝒪[L]ˣ))
        = normIntegerUnits K L u * normIntegerUnits K L (z : 𝒪[L]ˣ) := by
          rw [(normIntegerUnits K L).map_mul]
    _ = normIntegerUnits K L u * (y / normIntegerUnits K L u) := by
          rw [hzUnits]
    _ = y := by
          simp [div_eq_mul_inv, mul_left_comm]

end LocalClassFieldTheory
end
end

section
-- module Solutions.OAIQ244_DUKE.LocalClassFieldTheory_Finite_Unramified_Cohomology
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.residueFieldZModAlgebra _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.LubinTate.compatibleGroupFamiliesGroup _root_.OAI.PrimeDegreePackets.diagonalLogAction _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.RamificationTheory.HilbertRamification.ValuationSubring.selectedResidueField.instAlgebra _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.RelativeIdeleGroup.relativeIdeleMulAction _root_.CyclicCohomology.binaryCoefficientFamilyCommGroup _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.LocalClassFieldTheory.normalizationIntegerRingIsIntegralClosure _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.chosenFinitePlaceCompletionAlgebra _root_.finiteLocalUnitsOpen _root_.relativeAdeleRingIntermediateAlgebra _root_.relativeAdeleRingTopIntermediateAlgebra
attribute [-simp] _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.IsDiscreteValuationRing.addVal_ringEquiv _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.OAI.PrimeDegreePackets.ThetaConstruction.schwartzCM_apply _root_.infinitePlace_mult_smul
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

/-- The actual integral-closure Galois action on `U_L^n`, packaged as the
multiplicative action used by low-degree Tate cohomology. -/
@[implicit_reducible]
def galoisGroupPrincipalUnitsMulDistribMulActionOfIsIntegralClosure
    (K L : Type u) [Field K] [ValuativeRel K] [Field L] [ValuativeRel L]
    [Algebra K L]
    [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]
    [IsIntegralClosure 𝒪[L] 𝒪[K] L] (n : Nat) :
    MulDistribMulAction Gal(L / K) (principalUnits L n) where
  smul sigma a := galoisGroupPrincipalUnitsMapEquivOfIsIntegralClosure K L n sigma a
  one_smul := by
    intro a
    change galoisGroupPrincipalUnitsMapEquivOfIsIntegralClosure K L n 1 a = a
    exact congrArg (fun e : principalUnits L n ≃* principalUnits L n => e a)
      (map_one (galoisGroupPrincipalUnitsMapEquivHomOfIsIntegralClosure K L n))
  mul_smul := by
    intro sigma tau a
    change galoisGroupPrincipalUnitsMapEquivOfIsIntegralClosure K L n (sigma * tau) a =
      galoisGroupPrincipalUnitsMapEquivOfIsIntegralClosure K L n sigma
        (galoisGroupPrincipalUnitsMapEquivOfIsIntegralClosure K L n tau a)
    exact congrArg (fun e : principalUnits L n ≃* principalUnits L n => e a)
      (map_mul (galoisGroupPrincipalUnitsMapEquivHomOfIsIntegralClosure K L n) sigma tau)
  smul_mul := by
    intro sigma a b
    exact map_mul (galoisGroupPrincipalUnitsMapEquivOfIsIntegralClosure K L n sigma) a b
  smul_one := by
    intro sigma
    exact map_one (galoisGroupPrincipalUnitsMapEquivOfIsIntegralClosure K L n sigma)

/-- States the theorem `galoisGroupPrincipalUnitsMulDistribMulActionOfIsIntegralClosure_smul`. -/
@[simp]
theorem galoisGroupPrincipalUnitsMulDistribMulActionOfIsIntegralClosure_smul
    (K L : Type u) [Field K] [ValuativeRel K] [Field L] [ValuativeRel L]
    [Algebra K L]
    [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]
    [IsIntegralClosure 𝒪[L] 𝒪[K] L] (n : Nat)
    (sigma : Gal(L / K)) (a : principalUnits L n) :
    letI := galoisGroupPrincipalUnitsMulDistribMulActionOfIsIntegralClosure K L n
    sigma • a = galoisGroupPrincipalUnitsMapEquivOfIsIntegralClosure K L n sigma a :=
  rfl

/-- Inclusion in the actual short exact sequence
`1 → U_L^n → 𝒪_Lˣ → 𝒪_Lˣ/U_L^n → 1`. -/
def principalUnitsIntegerUnitsInclusion
    (L : Type u) [Field L] [ValuativeRel L] (n : Nat) :
    principalUnits L n →* 𝒪[L]ˣ :=
  (principalUnits L n).subtype

/-- The standard principal-unit sequence is short exact and equivariant for
the actual integral-closure Galois actions. -/
theorem principalUnitsIntegerUnits_shortExact
    (K L : Type u) [Field K] [ValuativeRel K] [Field L] [ValuativeRel L]
    [Algebra K L]
    [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]
    [IsIntegralClosure 𝒪[L] 𝒪[K] L] (n : Nat) :
    letI := galoisGroupPrincipalUnitsMulDistribMulActionOfIsIntegralClosure K L n
    letI := galoisGroupIntegerUnitsMulDistribMulActionOfIsIntegralClosure K L
    letI := galoisGroupIntegerUnitsModPrincipalUnitsMulDistribMulActionOfIsIntegralClosure K L n
    (∀ (sigma : Gal(L / K)) (a : principalUnits L n),
        principalUnitsIntegerUnitsInclusion L n (sigma • a) =
          sigma • principalUnitsIntegerUnitsInclusion L n a) ∧
      (∀ (sigma : Gal(L / K)) (a : 𝒪[L]ˣ),
        integerUnitsPrincipalUnitsQuotientMap L n (sigma • a) =
          sigma • integerUnitsPrincipalUnitsQuotientMap L n a) ∧
      (∀ a : 𝒪[L]ˣ, integerUnitsPrincipalUnitsQuotientMap L n a = 1 ↔
        ∃ v : principalUnits L n,
          principalUnitsIntegerUnitsInclusion L n v = a) ∧
      Function.Injective (principalUnitsIntegerUnitsInclusion L n) ∧
      Function.Surjective (integerUnitsPrincipalUnitsQuotientMap L n) := by
  let := galoisGroupPrincipalUnitsMulDistribMulActionOfIsIntegralClosure K L n
  let := galoisGroupIntegerUnitsMulDistribMulActionOfIsIntegralClosure K L
  let := galoisGroupIntegerUnitsModPrincipalUnitsMulDistribMulActionOfIsIntegralClosure K L n
  refine ⟨?_, ?_, ?_, (principalUnits L n).subtype_injective,
    integerUnitsModPrincipalUnitsAtLevelMk_surjective L n⟩
  · intro sigma a
    rfl
  · intro sigma a
    rw [integerUnitsPrincipalUnitsQuotientMap,
      galoisGroupIntegerUnitsMulDistribMulActionOfIsIntegralClosure_smul,
      galoisGroupIntegerUnitsModPrincipalUnitsMulDistribMulActionOfIsIntegralClosure_smul,
      galoisGroupIntegerUnitsModPrincipalUnitsMapEquivOfIsIntegralClosure_mk]
  · intro a
    constructor
    · intro ha
      have ha' : a ∈ principalUnits L n := by
        exact (integerUnitsModPrincipalUnitsAtLevelMk_eq_one_iff L n a).1 ha
      exact ⟨⟨a, ha'⟩, rfl⟩
    · rintro ⟨v, rfl⟩
      exact (integerUnitsModPrincipalUnitsAtLevelMk_eq_one_iff L n
        (v : 𝒪[L]ˣ)).2 v.2

/-- A Galois-fixed actual integer unit descends to a base integer unit.  This
is valuation-ring descent, not an assumed comparison of fixed parts. -/
theorem exists_integerUnit_map_eq_of_galoisGroup_fixed
    (K L : Type u) [Field K] [ValuativeRel K] [Field L] [ValuativeRel L]
    [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]
    [IsIntegralClosure 𝒪[L] 𝒪[K] L]
    (a : 𝒪[L]ˣ)
    (ha : letI := galoisGroupIntegerUnitsMulDistribMulActionOfIsIntegralClosure K L
      ∀ sigma : Gal(L / K), sigma • a = a) :
    ∃ b : 𝒪[K]ˣ, integerUnitsMapOfValuationExtension K L b = a := by
  let := galoisGroupIntegerUnitsMulDistribMulActionOfIsIntegralClosure K L
  have hfixed : ∀ sigma : Gal(L / K),
      sigma ((((a : 𝒪[L]ˣ) : 𝒪[L]) : L)) = (((a : 𝒪[L]ˣ) : 𝒪[L]) : L) := by
    intro sigma
    have h := congrArg (fun z : 𝒪[L]ˣ => (((z : 𝒪[L]ˣ) : 𝒪[L]) : L)) (ha sigma)
    simpa [galoisGroupIntegerRingEquivOfIsIntegralClosure_apply] using h
  have hmem : ((((a : 𝒪[L]ˣ) : 𝒪[L]) : L)) ∈ Set.range (algebraMap K L) :=
    (IsGalois.mem_range_algebraMap_iff_fixed
      (F := K) (E := L) ((((a : 𝒪[L]ˣ) : 𝒪[L]) : L))).2 hfixed
  rcases hmem with ⟨y, hy⟩
  have hy0 : y ≠ 0 := by
    intro hzero
    have : (((a : 𝒪[L]ˣ) : 𝒪[L]) : L) = 0 := by
      rw [← hy, hzero, map_zero]
    exact a.ne_zero (Subtype.ext this)
  have hy_mem : ValuativeRel.valuation K y ≤ 1 := by
    apply (Valuation.HasExtension.val_map_le_one_iff
      (vR := ValuativeRel.valuation K) (vA := ValuativeRel.valuation L) y).1
    rw [hy]
    exact (a : 𝒪[L]ˣ).val.property
  have hy_inv_mem : ValuativeRel.valuation K y⁻¹ ≤ 1 := by
    apply (Valuation.HasExtension.val_map_le_one_iff
      (vR := ValuativeRel.valuation K) (vA := ValuativeRel.valuation L) y⁻¹).1
    rw [map_inv₀, hy]
    have hinv : ValuativeRel.valuation L (((a.inv : 𝒪[L])) : L) ≤ 1 :=
      a.inv.property
    have hmul : (((a.val : 𝒪[L])) : L) * (((a.inv : 𝒪[L])) : L) = 1 := by
      exact congrArg (fun z : 𝒪[L] => (z : L)) a.val_inv
    have hinvEq : (((a.inv : 𝒪[L])) : L) = (((a.val : 𝒪[L])) : L)⁻¹ :=
      eq_inv_of_mul_eq_one_right hmul
    rw [hinvEq] at hinv
    exact hinv
  let b : 𝒪[K]ˣ :=
    { val := ⟨y, hy_mem⟩
      inv := ⟨y⁻¹, hy_inv_mem⟩
      val_inv := by ext; simp [hy0]
      inv_val := by ext; simp [hy0] }
  refine ⟨b, ?_⟩
  apply Units.ext
  apply Subtype.ext
  exact hy

end LocalClassFieldTheory
end
end

section
-- module Solutions.OAIQ244_DUKE.AlgebraicNumberTheory_Idele_Cohomology_SPlaces_LocalBlocks
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.residueFieldZModAlgebra _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.CyclicCohomology.binaryCoefficientFamilyCommGroup _root_.LocalClassFieldTheory.normalizationIntegerRingIsIntegralClosure _root_.chosenFinitePlaceCompletionAlgebra _root_.chosenFinitePlaceCompletionContinuousSMul _root_.chosenFinitePlaceCompletionFiniteDimensional _root_.chosenFinitePlaceCompletionLocallyCompactSpace _root_.chosenFinitePlaceLocalizedFiniteDimensional _root_.chosenFinitePlaceLocalizedIntegerAlgebra _root_.chosenFinitePlaceLocalizedIntegerModuleFinite _root_.chosenFinitePlaceLocalizedIsGalois _root_.chosenFinitePlaceLocalizedIsIntegralClosure _root_.chosenFinitePlaceLocalizedIsNonarchimedeanLocalField _root_.chosenFinitePlaceLocalizedIsValuativeTopology _root_.chosenFinitePlaceLocalizedLocallyCompactSpace _root_.chosenFinitePlaceLocalizedValuationCompatible _root_.chosenFinitePlaceLocalizedValuationHasExtension _root_.chosenFinitePlaceLocalizedValuationIsNontrivial _root_.chosenFinitePlaceLocalizedValuativeRel _root_.chosenFinitePlaceLocalizedValuativeRelIsNontrivial _root_.chosenFinitePlaceLocalizedValued _root_.scaledRelativeIntegerLatticeQuotientFinite
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

/-- The chosen local-place data at every unrestricted place. -/
noncomputable def relativeUnrestrictedSPlaceDatum
    (S : Finset (HeightOneSpectrum (𝓞 K))) :
    RelativeUnrestrictedSPlaceIndex (K := K) S →
      LocalPlaceDatum K L
  | Sum.inl v =>
      { base := v.1
        base_isNontrivial := v.isNontrivial
        extension :=
          infinitePlaceAbsoluteValueExtension
            v (chosenInfinitePlaceAbove (L := L) v)
            (chosenInfinitePlaceAbove_comap
              (L := L) v) }
  | Sum.inr v =>
      { base := HeightOneSpectrum.adicAbv K v.1
        base_isNontrivial :=
          RayClass.adicAbv_isNontrivial v.1
        extension :=
          chosenFinitePlaceExtension
            (L := L) v.1 }

/-- The actual tensor-unit type attached to one unrestricted place. -/
abbrev RelativeUnrestrictedSPlaceFactor
    (S : Finset (HeightOneSpectrum (𝓞 K))) :
    RelativeUnrestrictedSPlaceIndex (K := K) S → Type
  | Sum.inl v => (v.Completion ⊗[K] L)ˣ
  | Sum.inr v => (v.1.adicCompletion K ⊗[K] L)ˣ

/-- Each unrestricted local tensor-unit factor is a commutative group. -/
noncomputable instance relativeUnrestrictedSPlaceFactorCommGroup
    (S : Finset (HeightOneSpectrum (𝓞 K)))
    (i : RelativeUnrestrictedSPlaceIndex (K := K) S) :
    CommGroup
      (RelativeUnrestrictedSPlaceFactor
        (K := K) (L := L) S i) := by
  cases i <;> infer_instance

/-- The finite family of actual unrestricted tensor factors. -/
abbrev RelativeUnrestrictedSPlaceFactors
    (S : Finset (HeightOneSpectrum (𝓞 K))) :=
  ∀ i : RelativeUnrestrictedSPlaceIndex (K := K) S,
    RelativeUnrestrictedSPlaceFactor
      (K := K) (L := L) S i

/-- The componentwise scalar-conjugation action on the unrestricted
tensor factors. -/
@[reducible]
noncomputable def relativeUnrestrictedSPlaceFactorsAction
    (S : Finset (HeightOneSpectrum (𝓞 K))) :
    MulDistribMulAction (L ≃ₐ[K] L)
      (RelativeUnrestrictedSPlaceFactors
        (K := K) (L := L) S) := by
  letI : ∀ i :
      RelativeUnrestrictedSPlaceIndex (K := K) S,
      MulDistribMulAction (L ≃ₐ[K] L)
        (RelativeUnrestrictedSPlaceFactor
          (K := K) (L := L) S i) :=
    fun i => by
      cases i with
      | inl v =>
          exact
            scalarTensorUnitsAction
              (K := K) (L := L)
              (A := v.Completion)
      | inr v =>
          exact
            scalarTensorUnitsAction
              (K := K) (L := L)
              (A := v.1.adicCompletion K)
  exact
    piMulDistribMulAction (L ≃ₐ[K] L)
      (RelativeUnrestrictedSPlaceFactor
        (K := K) (L := L) S)
end
end

section
-- module Solutions.OAIQ244_DUKE.AlgebraicNumberTheory_Idele_Cohomology_SPlaces_Herbrand_Factors
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalCyclotomicCompletionAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.LubinTate.compatibleGroupFamiliesGroup _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.CyclicCohomology.binaryCoefficientFamilyCommGroup _root_.LocalClassFieldTheory.normalizationIntegerRingIsIntegralClosure
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
@[reducible]
noncomputable def
    relativeUnrestrictedSPlaceFactorsActionProvider
    (S : Finset (HeightOneSpectrum (𝓞 K))) :
    MulDistribMulAction (L ≃ₐ[K] L)
      (RelativeUnrestrictedSPlaceFactors
        (K := K) (L := L) S) :=
  relativeUnrestrictedSPlaceFactorsAction
    (K := K) (L := L) S

omit [NumberField L] in
@[reducible]
noncomputable def
    relativeUnrestrictedSPlaceLocalBlockFamilyActionProvider
    (S : Finset (HeightOneSpectrum (𝓞 K))) :
    MulDistribMulAction (L ≃ₐ[K] L)
      (LocalBlockFamily
        (relativeUnrestrictedSPlaceDatum
          (K := K) (L := L) S)) :=
  localBlockFamilyAction
    (relativeUnrestrictedSPlaceDatum
      (K := K) (L := L) S)
end
end

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

/-- A completion belonging to a right coset, transported first by
Galois conjugation and then into the chosen algebraic localization. -/
noncomputable def rightCosetCompletionRingEquivLocalized
    (q : InducedRightCosets (absoluteValueDecompositionGroup K w.1)) :
    letI hK := AbsoluteValue.extensionCompletionAlgebra (K := K) w.1
    letI : SMul K w.1.Completion := hK.toSMul
    letI := AbsoluteValue.completionAlgebra vK w.1 w.2
    (rightCosetExtensionEquiv vK hvK w q).1.Completion ≃+*
      LocalizedCompletion vK w := by
  letI hK := AbsoluteValue.extensionCompletionAlgebra (K := K) w.1
  letI : SMul K w.1.Completion := hK.toSMul
  letI := AbsoluteValue.completionAlgebra vK w.1 w.2
  change
    (absoluteValueExtensionConjugate
      vK w (Quotient.out q)).1.Completion ≃+*
      LocalizedCompletion vK w
  exact
    (conjugateExtensionCompletionRingEquiv
      vK w (Quotient.out q)).trans
      (localizedCompletionEquivCompletion vK hvK w).symm.toRingEquiv

end CompletionTransport
end
end

section
-- module Solutions.OAIQ244_DUKE.AlgebraicNumberTheory_Idele_Relative_FiniteIntegralNormPreimage
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitQuotientCarrier_finite _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.residueFieldZModAlgebra _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.PrimeDegreePackets.boundedRealFields_finite _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_finite_residue _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.LocalClassFieldTheory.normalizationIntegerRingIsIntegralClosure
attribute [-simp] _root_.IsDiscreteValuationRing.addVal_ringEquiv _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.OAI.PrimeDegreePackets.ThetaConstruction.schwartzCM_apply _root_.infinitePlace_mult_smul
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

omit [NumberField L] [IsGalois K L] in
/-- The finite-place completion comparison restricts to an inclusion of
integer-unit groups: an integral unit on the adic-completion side has an
integer-unit preimage on the absolute-value-completion side. -/
theorem exists_finitePlaceCompletionIntegerUnit_of_unitsEquiv_eq
    (v₀ : HeightOneSpectrum (𝓞 K))
    (x₀ :
      (HeightOneSpectrum.adicAbv K v₀).Completionˣ)
    (x : (v₀.adicCompletion K)ˣ)
    (hx :
      finitePlaceCompletionUnitsContinuousMulEquiv v₀ x₀ = x)
    (hxUnit :
      x ∈ (v₀.adicCompletionIntegers K).units) :
    let vK := HeightOneSpectrum.adicAbv K v₀
    let hvKna : IsNonarchimedean (vK : K → ℝ) :=
      HeightOneSpectrum.isNonarchimedean_adicAbv K v₀
    letI : Valued vK.Completion ℝ≥0 :=
      finitePlaceCompletionValued vK hvKna
    letI : ValuativeRel vK.Completion :=
      finitePlaceCompletionValuativeRel vK hvKna
    ∃ x₀O : 𝒪[vK.Completion]ˣ,
      integerUnitsToFieldUnits vK.Completion x₀O = x₀ := by
  let vK := HeightOneSpectrum.adicAbv K v₀
  let hvKna : IsNonarchimedean (vK : K → ℝ) :=
    HeightOneSpectrum.isNonarchimedean_adicAbv K v₀
  let : Valued vK.Completion ℝ≥0 :=
    finitePlaceCompletionValued vK hvKna
  let : ValuativeRel vK.Completion :=
    finitePlaceCompletionValuativeRel vK hvKna
  rw [Submonoid.mem_units_iff] at hxUnit
  have hx₀norm :
      ‖(x₀ : vK.Completion)‖ ≤ 1 := by
    have hval :=
      congrArg
        (fun q : (v₀.adicCompletion K)ˣ =>
          (q : v₀.adicCompletion K)) hx
    have hnorm :
        ‖finitePlaceCompletionRingHom v₀
            (x₀ : vK.Completion)‖ =
          ‖(x₀ : vK.Completion)‖ :=
      (finitePlaceCompletionRingHom_isometry v₀).norm_map_of_map_zero
        (map_zero (finitePlaceCompletionRingHom v₀)) _
    rw [← hnorm]
    rw [show finitePlaceCompletionRingHom v₀
          (x₀ : vK.Completion) = (x : v₀.adicCompletion K) by
      exact hval]
    exact norm_le_one_of_mem_adicCompletionIntegers v₀ hxUnit.1
  have hx₀invnorm :
      ‖((x₀⁻¹ : vK.Completionˣ) : vK.Completion)‖ ≤ 1 := by
    have hval :=
      congrArg
        (fun q : (v₀.adicCompletion K)ˣ =>
          (q : v₀.adicCompletion K))
        (congrArg Inv.inv hx)
    have hnorm :
        ‖finitePlaceCompletionRingHom v₀
            ((x₀⁻¹ : vK.Completionˣ) : vK.Completion)‖ =
          ‖((x₀⁻¹ : vK.Completionˣ) : vK.Completion)‖ :=
      (finitePlaceCompletionRingHom_isometry v₀).norm_map_of_map_zero
        (map_zero (finitePlaceCompletionRingHom v₀)) _
    rw [← hnorm]
    rw [show finitePlaceCompletionRingHom v₀
          ((x₀⁻¹ : vK.Completionˣ) : vK.Completion) =
        ((x⁻¹ : (v₀.adicCompletion K)ˣ) :
          v₀.adicCompletion K) by
      exact hval]
    exact norm_le_one_of_mem_adicCompletionIntegers v₀ hxUnit.2
  let x₀O : 𝒪[vK.Completion]ˣ :=
    { val :=
        ⟨x₀,
          (finitePlaceCompletion_mem_integers_iff_norm_le_one
            vK hvKna (x₀ : vK.Completion)).2 hx₀norm⟩
      inv :=
        ⟨x₀⁻¹,
          by
            simpa using
              (finitePlaceCompletion_mem_integers_iff_norm_le_one
                vK hvKna
                ((x₀⁻¹ : vK.Completionˣ) :
                  vK.Completion)).2 hx₀invnorm⟩
      val_inv := by
        apply Subtype.ext
        simp
      inv_val := by
        apply Subtype.ext
        simp }
  refine ⟨x₀O, ?_⟩
  apply Units.ext
  rfl

/-- If the norm of an extension-field unit comes from a base valuation-ring
unit, then the extension-field unit has normalized valuation zero. -/
theorem v_eq_zero_of_normUnits_eq_integerUnitsToFieldUnits
    (F E : Type u)
    [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    [Field E] [ValuativeRel E] [TopologicalSpace E]
    [IsNonarchimedeanLocalField E]
    [Algebra F E] [FiniteDimensional F E] [IsGalois F E]
    [Valuation.HasExtension
      (ValuativeRel.valuation F) (ValuativeRel.valuation E)]
    [IsIntegralClosure 𝒪[E] 𝒪[F] E]
    (xO : 𝒪[F]ˣ)
    (y : Eˣ)
    (hy :
      LocalFieldTheory.normUnits F E y =
        integerUnitsToFieldUnits F xO) :
    v E (Additive.ofMul y) = 0 := by
  have hNormValuation :=
    v_normUnits_eq_residue_finrank_mul_of_isGalois F E y
  rw [hy, v_integerUnitsToFieldUnits] at hNormValuation
  have hf :
      (Module.finrank 𝓀[F] 𝓀[E] : Int) ≠ 0 := by
    exact_mod_cast
      (Module.finrank_pos :
        0 < Module.finrank 𝓀[F] 𝓀[E]).ne'
  exact
    (mul_eq_zero.mp hNormValuation.symm).resolve_left hf
end
end

section
-- module Solutions.OAIQ244_DUKE.AlgebraicNumberTheory_Ramification_Splitting_FinitePlace
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.LocalClassFieldTheory.normalizationIntegerRingIsIntegralClosure
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

/-!
# Decomposition groups and complete splitting at finite places

For a finite Galois extension of number fields `L / K`, this file
attaches an actual decomposition subgroup to every finite place of
`K`.  The extension of the adic absolute value is the one constructed
in `LocalNormApproximation`; no place above `v` is supplied as an
additional hypothesis.

The stabilizer is identified with the automorphism group of the algebraic
localization. The finite-localization theorem supplies finite dimensionality,
so the order of
the decomposition group is exactly the local degree.  Consequently
complete splitting is equivalent both to cardinality one and to local
degree one.
-/

open scoped NumberField Classical
open NumberField IsDedekindDomain

noncomputable section

open AlgebraicNumberTheory.Valuations
open HilbertRamification
open LocalClassFieldTheory

variable {K L : Type}
    [Field K] [NumberField K]
    [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]

omit [FiniteDimensional K L] in
/-- A finite place splits completely exactly when its decomposition
group has one element. -/
theorem finitePlaceSplitsCompletely_iff_card_eq_one
    (v : HeightOneSpectrum (𝓞 K)) :
    FinitePlaceSplitsCompletely
        (K := K) (L := L) v ↔
      Nat.card
          (finitePlaceDecompositionGroup
            (K := K) (L := L) v) = 1 := by
  unfold FinitePlaceSplitsCompletely
  exact
    (finitePlaceDecompositionGroup
      (K := K) (L := L) v).eq_bot_iff_card

/-- Complete splitting is equivalent to local degree one. -/
theorem finitePlaceSplitsCompletely_iff_localDegree_eq_one
    (v : HeightOneSpectrum (𝓞 K)) :
    FinitePlaceSplitsCompletely
        (K := K) (L := L) v ↔
      finitePlaceLocalDegree
          (K := K) (L := L) v = 1 := by
  rw [finitePlaceSplitsCompletely_iff_card_eq_one,
    finitePlaceDecompositionGroup_card_eq_localDegree]
end
end

section
-- module Solutions.OAIQ244_DUKE.AlgebraicNumberTheory_Ramification_Splitting_NormalClosure
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.residueFieldZModAlgebra _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.PrimeDegreePackets.diagonalLogAction _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.LocalClassFieldTheory.normalizationIntegerRingIsIntegralClosure _root_.chosenFinitePlaceCompletionAlgebra _root_.chosenFinitePlaceCompletionContinuousSMul _root_.chosenFinitePlaceCompletionFiniteDimensional _root_.chosenFinitePlaceCompletionLocallyCompactSpace _root_.chosenFinitePlaceLocalizedFiniteDimensional _root_.chosenFinitePlaceLocalizedIntegerAlgebra _root_.chosenFinitePlaceLocalizedIntegerModuleFinite _root_.chosenFinitePlaceLocalizedIsGalois _root_.chosenFinitePlaceLocalizedIsIntegralClosure _root_.chosenFinitePlaceLocalizedIsNonarchimedeanLocalField _root_.chosenFinitePlaceLocalizedIsValuativeTopology _root_.chosenFinitePlaceLocalizedLocallyCompactSpace _root_.chosenFinitePlaceLocalizedValuationCompatible _root_.chosenFinitePlaceLocalizedValuationHasExtension _root_.chosenFinitePlaceLocalizedValuationIsNontrivial _root_.chosenFinitePlaceLocalizedValuativeRel _root_.chosenFinitePlaceLocalizedValuativeRelIsNontrivial _root_.chosenFinitePlaceLocalizedValued _root_.scaledRelativeIntegerLatticeQuotientFinite
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

section FinitePlaces

variable {K M : Type}
    [Field K] [NumberField K]
    [Field M] [Algebra K M]
    [FiniteDimensional K M] [IsGalois K M]

local notation "G" => M ≃ₐ[K] M

/-- The double-coset criterion for an actual finite place and
the decomposition group attached to the standard chosen extension to
`M`. -/
theorem finitePlaceSplitsCompletelyInExtension_iff_doubleCoset_card_eq
    (L : IntermediateField K M)
    (v : HeightOneSpectrum (𝓞 K)) :
    FinitePlaceSplitsCompletelyInExtension
        (K := K) (E := L) v ↔
      Nat.card
          (DoubleCoset.Quotient
            (L.fixingSubgroup : Set G)
            (finitePlaceDecompositionGroup
              (K := K) (L := M) v)) =
        Nat.card
          (DoubleCoset.Quotient
            (L.fixingSubgroup : Set G)
            (⊥ : Subgroup G)) := by
  exact
    absoluteValueSplitsCompletelyInExtension_iff_doubleCoset_card_eq
      (NumberField.HeightOneSpectrum.adicAbv K v)
      (chosenFinitePlaceExtension (L := M) v)
      L
      (RayClass.adicAbv_isNontrivial v)

end FinitePlaces
end
end

section
-- module Solutions.OAIQ244_DUKE.LubinTate_FormalModule_StandardFormalGroup
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_isCompleteDiscrete _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.AdicPrincipalUnits.instAddCommGroup _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.AdicPrincipalUnits.instTopologicalSpace _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.DiscretePrincipalUnitQuotient.instAddCommGroup _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitInverseLimitCarrierPadicModule _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitInverseLimitCarrierPadicSMul _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitQuotientCarrierPadicModule _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitQuotientCarrier_finite _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.PrincipalUnitProdiscreteLimit.instAddCommGroup _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.PrincipalUnitProdiscreteLimit.instTopologicalSpace _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.adicPrincipalUnitsContinuousAdd _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.adicPrincipalUnitsPadicModule _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.discretePrincipalUnitQuotientFinite _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.discretePrincipalUnitQuotientPadicModule _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitPadicModule _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitPadicSMul _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitProdiscreteLimitContinuousAdd _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitProdiscreteLimitPadicModule _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitSuccQuotCommGroup _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.residueFieldZModAlgebra _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedQPadicContextAlgebra _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedQPadicContextFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.RamificationTheory.HilbertRamification.Higher.lowerRamificationGroup.instNormal _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.LocalClassFieldTheory.normalizationIntegerRingIsIntegralClosure _root_.RamificationTheory.HilbertRamification.CompleteDVF.decompositionGroupMulSemiringAction _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

/-!
# The standard Lubin--Tate formal group

The recursive same-uniformizer intertwiner applied to the standard
Lubin--Tate series produces the formal group law and all of its scalar
endomorphisms.  The structural identities are proved from the uniqueness of
an intertwiner with prescribed linear term.

This file also records the substitution closure properties of
`SameUniformizer.Intertwines`.  They are useful independently of the
standard series: intertwiners remain intertwiners after a change of
variables, after substituting an intertwining family, and after
one-variable power-series composition.
-/

noncomputable section

open scoped BigOperators
attribute [local instance] Classical.propDecidable

universe u v w w'

namespace LubinTate
namespace SameUniformizer

open LocalFieldTheory.DiscreteValuationField

variable {K : Type u} [Field K]
variable {F : LocalField.{u, v} K} {π : F.valuationSubring}

section StandardFormalGroup

variable (hπ :
  F.toCompleteDVF.valuation.IsUniformizer (π : K))

/-- The unique two-variable series with linear term `X + Y` commuting with
the standard Lubin--Tate series. -/
noncomputable def standardFormalGroupPowerSeries :
    MvPowerSeries (Fin 2) F.valuationSubring :=
  recursiveIntertwiner hπ (standardSeries hπ)
    (standardSeries hπ) (fun _ => 1)

end StandardFormalGroup

end SameUniformizer
end LubinTate

end
end


