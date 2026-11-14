-- Prove2me | Definitions.Def_OAIQ244Duke050
-- name    : OAIQ244Duke050
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-13T06:52:57.765725+00:00
-- url     : https://prove2.me/theorems/d8063d4f-6815-436f-8c5b-22161a491cc4
-- title:
--   Definitions bundle OAIQ244Duke050 of the split of OpenAI, Equidistribution of Prime-Degree Torus Packets with Arbitrary Local Type
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.DukePrimeDegree.prime_degree_packet_measure_equidistribution_unconditional` and `OAI.DukePrimeDegree.prime_degree_packet_measures_tendsto_haar_unconditional`, carved from OpenAI's openai/math development (OpenAI, *Equidistribution of Prime-Degree Torus Packets with Arbitrary Local Type*, OpenAI Math Release, September 24, 2026, result family 15, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 41 declarations of OpenAI's Lean: 13 definitions, 1 instance and 27 theorems. The definitions and types are `KummerTheory.sUnitLocalPowerKernel`, `KummerTheory.sUnitLocalPowerMap`, `LocalClassFieldTheory.absoluteCompletionNormQuotientEquivRealComplex`, `LocalClassFieldTheory.localHerbrandH0EquivUnitsTateH0`, `LocalClassFieldTheory.localHerbrandHMinusOneEquivUnitsTateHminusOne`, `LocalClassFieldTheory.localTensorUnitsEquivLocalPlaceBlock`, `LocalClassFieldTheory.localizedCompletionNormQuotientEquivAbsoluteCompletions`, `LocalClassFieldTheory.normQuotientEquivOfRingEquiv`, `LocalClassFieldTheory.normQuotientMapOfRingEquiv`, `LocalClassFieldTheory.realComplexNormQuotientEquivSign`, `finitePlaceTensorUnitsEquivLocalPlaceBlock`, `infinitePlaceLocalTensorUnitsAction`, `infinitePlaceTensorUnitsEquivLocalPlaceBlock`.
--
--   **Sources.** They come from these modules of lean/OAI/NumberTheory, in whole or in part: `AlgebraicNumberTheory_Adele_FinitePlaceTensorBlock`, `AlgebraicNumberTheory_Adele_InfinitePlaceTensorBlock`, `AlgebraicNumberTheory_Idele_Cohomology_Herbrand`, `AlgebraicNumberTheory_Idele_Cohomology_SPlaces_Herbrand_Local`, `AlgebraicNumberTheory_Ramification_Splitting_NormalClosure`, `AlgebraicNumberTheory_SUnit_Herbrand`, `GlobalClassFieldTheory_ClassFieldAxiom_SUnitKummerPrimeSelection_FinitePlaceDecomposition`, `KummerTheory_Concrete_SUnitPreparation_SUnitLocalPowerKernel`, `LocalClassFieldTheory_ClassFormation_ArchimedeanHilbert90`, `LocalClassFieldTheory_ClassFormation_ArchimedeanNormQuotient`, `LocalClassFieldTheory_ClassFormation_LocalBlocks_Tensor`, `LocalClassFieldTheory_ClassFormation_LocalizedCompletionCohomology_Algebra`, `LocalClassFieldTheory_ClassFormation_LocalizedCompletionCohomology_HerbrandEquiv`, `LubinTate_FormalModule_StandardFormalGroup`.
--
--   **Imports.** It imports the bundles `OAIQ244Duke037`, `OAIQ244Duke038`, `OAIQ244Duke039`, `OAIQ244Duke040`, `OAIQ244Duke042` and `OAIQ244Duke043` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ244Duke058`, `OAIQ244Duke059`, `OAIQ244Duke060` and `OAIQ244Duke061`.
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
-- module Solutions.OAIQ244_DUKE.AlgebraicNumberTheory_Idele_Cohomology_Herbrand
attribute [-instance] _root_.ClassFormation.DegreeData.FrobeniusFixedFieldTower.extensionNormal _root_.ClassFormation.DegreeData.GaloisSubextension.extensionSubgroup_normalInstance _root_.ClassFormation.FiniteAbstractField.toFiniteResidueAbstractField_extensionNormal _root_.ClassFormation.FiniteCyclicSubextension.instNormalSubtypeMemSubgroupFieldExtensionSubgroupField _root_.ClassFormation.FiniteGaloisSubextension.extensionSubgroup_normalInstance _root_.ClassFormation.FiniteGaloisSubextension.extensionSubgroup_over_intermediate_normalInstance _root_.ClassFormation.FiniteGaloisSubextension.intermediateField_normalInstance _root_.ClassFormation.FiniteIntermediateField.galoisRefinement_normal _root_.ClassFormation.FiniteUnramifiedCyclicExtension.instNormalSubtypeMemSubgroupFieldExtensionSubgroupField _root_.ClassFormation.conjugateExtension_normal _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalClassFieldTheory.extensionSubgroupBase_normal _root_.LocalClassFieldTheory.finiteGaloisExtensionSubgroupOfEmbedding_normal _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.residueFieldZModAlgebra _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionResidueField.instField _root_.RamificationTheory.HilbertRamification.ValuationSubring.inertiaGroup_normal _root_.RamificationTheory.HilbertRamification.ValuationSubring.ramificationGroupInInertiaAut_normal _root_.RamificationTheory.HilbertRamification.ValuationSubring.selectedResidueField.instAlgebra _root_.RayClass.Modulus.congruenceSubgroup_normal _root_.RayClass.Modulus.infiniteCongruenceSubgroupFiniteIndex _root_.RayClass.narrowInfiniteCongruenceSubgroupFiniteIndex _root_.RayClass.ordinaryIdealClassSubgroupFiniteIndex _root_.ValuationTheory.DiscreteValuationField.DVF.residueField.field _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.CyclicCohomology.binaryCoefficientFamilyCommGroup _root_.CyclicCohomology.instMulDistribMulActionBinaryCoefficientFamily _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.LocalClassFieldTheory.normalizationIntegerRingIsIntegralClosure _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.chosenFinitePlaceCompletionAlgebra _root_.finiteIdeleGroupIsTopologicalGroup _root_.finiteLocalUnitsOpen _root_.ideleGroupIsTopologicalGroup _root_.relativeAdeleRingIntermediateAlgebra _root_.relativeAdeleRingTopIntermediateAlgebra
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

/-!
# Herbrand cohomology of the relative idele class group

This file realizes the low-degree exact sequence on the actual relative
idele group

`1 → Lˣ → I_L → C_L → 1`.

The Galois actions are the concrete conjugation actions from the
tensor-product model of relative adeles.  The class norm is descended from
the determinant norm on relative ideles, and its relation with the Tate
norm is proved from the Galois product formula.
-/

open scoped BigOperators NumberField
open NumberField

noncomputable section


open CyclicCohomology.ProfiniteCohomology.Herbrand
open CyclicCohomology

namespace RelativeIdeleGroup
namespace Cohomology

variable
    (K L : Type) [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]

section Actions

section NormQuotientIdentification

attribute [local instance] RelativeIdeleGroup.Cohomology.instMulDistribMulActionAlgEquiv
attribute [local instance] RelativeIdeleGroup.Cohomology.instMulDistribMulActionAlgEquivClassGroup
local instance instMulDistribMulActionAlgEquivSubtypeMemSubgroupPrincipalSubgroup_rb03dac_1 :
    MulDistribMulAction (L ≃ₐ[K] L)
      (RelativeIdeleGroup.principalSubgroup K L) :=
  principalIdeleMulDistribMulAction K L
attribute [local instance] RelativeIdeleGroup.Cohomology.ideleClassNormQuotient_baseIsMulCommutative
omit [NumberField L] in
/-- The norm index is the cardinality of the actual degree-zero Tate
cohomology group.  This statement is valid without silently assigning a
positive finite index to an infinite quotient. -/
theorem ideleClassNorm_index_eq_herbrandH0_card :
    (ideleClassNorm K L).range.index =
      Nat.card
        (HerbrandH0 (L ≃ₐ[K] L)
          (RelativeIdeleGroup.ClassGroup K L)) := by
  rw [Subgroup.index_eq_card]
  exact
    (Nat.card_congr
      (ideleClassHerbrandH0EquivNormQuotient
        K L).toEquiv).symm

end NormQuotientIdentification

end Actions

end Cohomology
end RelativeIdeleGroup
end
end

section
-- module Solutions.OAIQ244_DUKE.LocalClassFieldTheory_ClassFormation_LocalizedCompletionCohomology_Algebra
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalCyclotomicCompletionAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.residueFieldZModAlgebra _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.PrimeDegreePackets.diagonalLogAction _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionResidueField.instField _root_.RamificationTheory.HilbertRamification.ValuationSubring.selectedResidueField.instAlgebra _root_.RayClass.approximationCompletionTopologicalSpace _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.RelativeIdeleGroup.relativeIdeleMulAction _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.LocalClassFieldTheory.normalizationIntegerRingIsIntegralClosure _root_.adicCompletionProperSpace _root_.chosenFinitePlaceCompletionAlgebra _root_.chosenFinitePlaceCompletionContinuousSMul _root_.chosenFinitePlaceCompletionFiniteDimensional _root_.chosenFinitePlaceCompletionLocallyCompactSpace _root_.chosenFinitePlaceLocalizedFiniteDimensional _root_.chosenFinitePlaceLocalizedIntegerAlgebra _root_.chosenFinitePlaceLocalizedIntegerModuleFinite _root_.chosenFinitePlaceLocalizedIsGalois _root_.chosenFinitePlaceLocalizedIsIntegralClosure _root_.chosenFinitePlaceLocalizedIsNonarchimedeanLocalField _root_.chosenFinitePlaceLocalizedIsValuativeTopology _root_.chosenFinitePlaceLocalizedLocallyCompactSpace _root_.chosenFinitePlaceLocalizedValuationCompatible _root_.chosenFinitePlaceLocalizedValuationHasExtension _root_.chosenFinitePlaceLocalizedValuationIsNontrivial _root_.chosenFinitePlaceLocalizedValuativeRel _root_.chosenFinitePlaceLocalizedValuativeRelIsNontrivial _root_.chosenFinitePlaceLocalizedValued _root_.finiteLocalUnitsOpen _root_.relativeAdeleRingIntermediateAlgebra _root_.relativeAdeleRingTopIntermediateAlgebra
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

/-!
# Algebra for localized completion cohomology

This file provides named algebra, finite-dimensional, Galois, scalar-tower, and
global-to-local embedding providers for localized completions.
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

universe u v

variable {K : Type u} {L : Type v}
    [Field K] [Field L] [Algebra K L]

variable [IsGalois K L]

/-- The elements of `L` whose images in the algebraic localization come
from the completed base field are exactly the fixed field of the
decomposition group at `w`. -/
theorem localizedCompletion_baseField_comap_eq_fixedField_decompositionGroup
    (vK : AbsoluteValue K ℝ) (hvK : vK.IsNontrivial)
    (w : AbsoluteValueExtension vK L) :
    letI hK := AbsoluteValue.extensionCompletionAlgebra (K := K) w.1
    letI : SMul K w.1.Completion := hK.toSMul
    letI : Algebra vK.Completion w.1.Completion :=
      AbsoluteValue.completionAlgebra vK w.1 w.2
    letI := localizedCompletionGlobalAlgebra vK w
    letI := localizedCompletionIsScalarTower vK w
    ((algebraMap vK.Completion
        (LocalizedCompletion vK w)).fieldRange).comap
      (AbsoluteValue.toAlgebraicLocalization vK w.1 w.2) =
        (IntermediateField.fixedField
          (absoluteValueDecompositionGroup K w.1)).toSubfield := by
  let _ := localizedCompletionBaseAlgebra vK w
  let _ := localizedCompletionGlobalAlgebra vK w
  let _ := localizedCompletionIsScalarTower vK w
  let _ : IsGalois vK.Completion
      (LocalizedCompletion vK w) :=
    localizedCompletionIsGalois vK w
  ext x
  change
    AbsoluteValue.toAlgebraicLocalization vK w.1 w.2 x ∈
        Set.range
          (algebraMap vK.Completion
            (LocalizedCompletion vK w)) ↔
      x ∈ IntermediateField.fixedField
        (absoluteValueDecompositionGroup K w.1)
  rw [InfiniteGalois.mem_range_algebraMap_iff_fixed,
    IntermediateField.mem_fixedField_iff]
  constructor
  · intro hfixed σ hσ
    let δ : absoluteValueDecompositionGroup K w.1 := ⟨σ, hσ⟩
    apply
      (AbsoluteValue.toAlgebraicLocalization
        vK w.1 w.2).injective
    calc
      AbsoluteValue.toAlgebraicLocalization
          vK w.1 w.2 (σ x) =
        decompositionGroupEquivAlgebraicLocalizationAut
            vK hvK w δ
          (AbsoluteValue.toAlgebraicLocalization
            vK w.1 w.2 x) :=
        (localizationRamificationGroups_decompositionGroupEquiv_toLocalization
          vK hvK w δ x).symm
      _ = AbsoluteValue.toAlgebraicLocalization
            vK w.1 w.2 x :=
        hfixed _
  · intro hZ τ
    let δ : absoluteValueDecompositionGroup K w.1 :=
      (decompositionGroupEquivAlgebraicLocalizationAut
        vK hvK w).symm τ
    have hδ : ((δ : L ≃ₐ[K] L) x) = x :=
      hZ δ δ.property
    calc
      τ (AbsoluteValue.toAlgebraicLocalization
          vK w.1 w.2 x) =
        decompositionGroupEquivAlgebraicLocalizationAut
            vK hvK w δ
          (AbsoluteValue.toAlgebraicLocalization
            vK w.1 w.2 x) := by
        rw [MulEquiv.apply_symm_apply]
      _ = AbsoluteValue.toAlgebraicLocalization
            vK w.1 w.2 ((δ : L ≃ₐ[K] L) x) :=
        localizationRamificationGroups_decompositionGroupEquiv_toLocalization
          vK hvK w δ x
      _ = AbsoluteValue.toAlgebraicLocalization
            vK w.1 w.2 x :=
        congrArg
          (AbsoluteValue.toAlgebraicLocalization
            vK w.1 w.2) hδ


end LocalClassFieldTheory
end
end

section
-- module Solutions.OAIQ244_DUKE.LocalClassFieldTheory_ClassFormation_LocalizedCompletionCohomology_HerbrandEquiv
attribute [-instance] _root_.ClassFormation.DegreeData.FrobeniusFixedFieldTower.extensionNormal _root_.ClassFormation.DegreeData.GaloisSubextension.extensionSubgroup_normalInstance _root_.ClassFormation.FiniteAbstractField.toFiniteResidueAbstractField_extensionNormal _root_.ClassFormation.FiniteCyclicSubextension.instNormalSubtypeMemSubgroupFieldExtensionSubgroupField _root_.ClassFormation.FiniteGaloisSubextension.extensionSubgroup_normalInstance _root_.ClassFormation.FiniteGaloisSubextension.extensionSubgroup_over_intermediate_normalInstance _root_.ClassFormation.FiniteGaloisSubextension.intermediateField_normalInstance _root_.ClassFormation.FiniteIntermediateField.galoisRefinement_normal _root_.ClassFormation.FiniteUnramifiedCyclicExtension.instNormalSubtypeMemSubgroupFieldExtensionSubgroupField _root_.ClassFormation.conjugateExtension_normal _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalCyclotomicCompletionAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.DiscreteNthRootsSubgroup.instCommGroupSubtypeUnitsMemSubgroup _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalClassFieldTheory.extensionSubgroupBase_normal _root_.LocalClassFieldTheory.finiteGaloisExtensionSubgroupOfEmbedding_normal _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitQuotientCarrier_finite _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.residueFieldZModAlgebra _root_.LocalFieldTheory.DiscreteValuationField.finite_nsmulAddKernel_padicInt_pi _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_multiplicative_nthPowerKernel _root_.LocalFieldTheory.finite_nsmulAddKernel_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.LubinTate.compatibleGroupFamiliesCommGroup _root_.LubinTate.compatibleGroupFamiliesGroup _root_.OAI.PrimeDegreePackets.boundedRealFields_finite _root_.OAI.PrimeDegreePackets.diagonalLogAction _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionResidueField.instField _root_.RamificationTheory.HilbertRamification.ValuationSubring.ramificationGroupInInertiaAut_normal _root_.RamificationTheory.HilbertRamification.ValuationSubring.selectedResidueField.instAlgebra _root_.RayClass.Modulus.congruenceSubgroup_normal _root_.RayClass.approximationCompletionTopologicalSpace _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.RelativeIdeleGroup.relativeIdeleMulAction _root_.CyclicCohomology.binaryCoefficientFamilyCommGroup _root_.CyclicCohomology.instMulDistribMulActionBinaryCoefficientFamily _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.LocalClassFieldTheory.normalizationIntegerRingIsIntegralClosure _root_.adicCompletionProperSpace _root_.chosenFinitePlaceCompletionAlgebra _root_.chosenFinitePlaceCompletionContinuousSMul _root_.chosenFinitePlaceCompletionFiniteDimensional _root_.chosenFinitePlaceCompletionLocallyCompactSpace _root_.chosenFinitePlaceLocalizedFiniteDimensional _root_.chosenFinitePlaceLocalizedIntegerAlgebra _root_.chosenFinitePlaceLocalizedIntegerModuleFinite _root_.chosenFinitePlaceLocalizedIsGalois _root_.chosenFinitePlaceLocalizedIsIntegralClosure _root_.chosenFinitePlaceLocalizedIsNonarchimedeanLocalField _root_.chosenFinitePlaceLocalizedIsValuativeTopology _root_.chosenFinitePlaceLocalizedLocallyCompactSpace _root_.chosenFinitePlaceLocalizedValuationCompatible _root_.chosenFinitePlaceLocalizedValuationHasExtension _root_.chosenFinitePlaceLocalizedValuationIsNontrivial _root_.chosenFinitePlaceLocalizedValuativeRel _root_.chosenFinitePlaceLocalizedValuativeRelIsNontrivial _root_.chosenFinitePlaceLocalizedValued _root_.finiteLocalUnitsOpen _root_.relativeAdeleRingIntermediateAlgebra _root_.relativeAdeleRingTopIntermediateAlgebra
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

/-- Degree-zero multiplicative Herbrand cohomology for a decomposition group
identified with degree-zero Tate cohomology of the localized field units. -/
noncomputable def localHerbrandH0EquivUnitsTateH0
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
      Multiplicative
        (tateCohomology
          (Rep.ofAlgebraAutOnUnits vK.Completion
            (LocalizedCompletion vK w)) 0) := by
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
  letI :
      MulDistribMulAction
        (LocalizedCompletion vK w ≃ₐ[vK.Completion]
          LocalizedCompletion vK w)
        (LocalizedCompletion vK w)ˣ :=
    galoisGroupFieldUnitsMulDistribMulAction
      vK.Completion (LocalizedCompletion vK w)
  let e :=
    decompositionGroupEquivAlgebraicLocalizationAut
      vK hvK w
  let eTate :
      (unitsInvariantSubmodule vK.Completion
          (LocalizedCompletion vK w) ⧸
        unitsTateH0NormSubmodule vK.Completion
          (LocalizedCompletion vK w)) ≃+
        tateCohomology
          (Rep.ofAlgebraAutOnUnits vK.Completion
            (LocalizedCompletion vK w)) 0 :=
    (tateUnitsH0IsoInvariantsQuotient
      vK.Completion
      (LocalizedCompletion vK w)).symm.toLinearEquiv.toAddEquiv
  exact
    (herbrandH0CompMulEquiv
      (A := (LocalizedCompletion vK w)ˣ) e).trans
      ((herbrandH0MulEquivInvariantsNormQuotient
        vK.Completion (LocalizedCompletion vK w)).trans
          eTate.toMultiplicative)

/-- Degree-minus-one multiplicative Herbrand cohomology for a decomposition
group identified with degree-minus-one Tate cohomology of localized units. -/
noncomputable def localHerbrandHMinusOneEquivUnitsTateHminusOne
    (vK : AbsoluteValue k ℝ) (hvK : vK.IsNontrivial)
    (w : AbsoluteValueExtension vK ell)
    (σ : ell ≃ₐ[k] ell)
    (hgen : ∀ τ : ell ≃ₐ[k] ell,
      τ ∈ Subgroup.zpowers σ) :
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
    HerbrandHMinusOne
        (absoluteValueDecompositionGroup k w.1)
        (LocalizedCompletion vK w)ˣ
        (subgroupGeneratorOfGenerator
          (absoluteValueDecompositionGroup k w.1) σ hgen) ≃
      tateCohomology
        (Rep.ofAlgebraAutOnUnits vK.Completion
          (LocalizedCompletion vK w)) (-1) := by
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
  letI :
      MulDistribMulAction
        (LocalizedCompletion vK w ≃ₐ[vK.Completion]
          LocalizedCompletion vK w)
        (LocalizedCompletion vK w)ˣ :=
    galoisGroupFieldUnitsMulDistribMulAction
      vK.Completion (LocalizedCompletion vK w)
  let e :=
    decompositionGroupEquivAlgebraicLocalizationAut
      vK hvK w
  let δ :=
    subgroupGeneratorOfGenerator
      (absoluteValueDecompositionGroup k w.1) σ hgen
  let g :=
    localizedCompletionGaloisGenerator
      vK hvK w σ hgen
  let hg :=
    localizedCompletionGaloisGenerator_generates
      vK hvK w σ hgen
  exact
    (herbrandHMinusOneCompMulEquiv
      (A := (LocalizedCompletion vK w)ˣ)
      e δ).toEquiv.trans
      (herbrandHminusOneEquivUnitsTateHminusOne
        vK.Completion (LocalizedCompletion vK w)
        g hg)


end LocalTateComparison

end LocalClassFieldTheory
end
end

section
-- module Solutions.OAIQ244_DUKE.LocalClassFieldTheory_ClassFormation_LocalBlocks_Tensor
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalCyclotomicCompletionAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.HilbertRamification.decompositionField_decompositionField_integerMap_isLocalHom _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.residueFieldZModAlgebra _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.LubinTate.compatibleGroupFamiliesGroup _root_.OAI.PrimeDegreePackets.diagonalLogAction _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionResidueField.instField _root_.RamificationTheory.HilbertRamification.ValuationSubring.selectedResidueField.instAlgebra _root_.RayClass.approximationCompletionTopologicalSpace _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.RelativeIdeleGroup.relativeIdeleMulAction _root_.CyclicCohomology.binaryCoefficientFamilyCommGroup _root_.CyclicCohomology.instMulDistribMulActionBinaryCoefficientFamily _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.LocalClassFieldTheory.normalizationIntegerRingIsIntegralClosure _root_.adicCompletionProperSpace _root_.chosenFinitePlaceCompletionAlgebra _root_.chosenFinitePlaceCompletionContinuousSMul _root_.chosenFinitePlaceCompletionFiniteDimensional _root_.chosenFinitePlaceCompletionLocallyCompactSpace _root_.chosenFinitePlaceLocalizedFiniteDimensional _root_.chosenFinitePlaceLocalizedIntegerAlgebra _root_.chosenFinitePlaceLocalizedIntegerModuleFinite _root_.chosenFinitePlaceLocalizedIsGalois _root_.chosenFinitePlaceLocalizedIsIntegralClosure _root_.chosenFinitePlaceLocalizedIsNonarchimedeanLocalField _root_.chosenFinitePlaceLocalizedIsValuativeTopology _root_.chosenFinitePlaceLocalizedLocallyCompactSpace _root_.chosenFinitePlaceLocalizedValuationCompatible _root_.chosenFinitePlaceLocalizedValuationHasExtension _root_.chosenFinitePlaceLocalizedValuationIsNontrivial _root_.chosenFinitePlaceLocalizedValuativeRel _root_.chosenFinitePlaceLocalizedValuativeRelIsNontrivial _root_.chosenFinitePlaceLocalizedValued _root_.finiteLocalUnitsOpen _root_.relativeAdeleRingIntermediateAlgebra _root_.relativeAdeleRingTopIntermediateAlgebra
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

/-!
# The tensor-product realization of a local induced block

This file connects the induced module in `LocalBlock` with the actual local
factor of the scalar-extended adele algebra.  The natural Galois action on
`K_v ⊗[K] L` is conjugation on the second tensor factor. The completion tensor-product theorem
identifies this algebra with the product of the completions above `v`.

The first part records the natural tensor action and the canonical
identifications between completions at conjugate absolute values.  These
identifications are the concrete source of the induced-module covariance in
the induced local-block calculation.
-/

open scoped TensorProduct

noncomputable section

namespace LocalClassFieldTheory

open AlgebraicNumberTheory.Valuations
open HilbertRamification
open CyclicCohomology

universe u v

variable {K : Type u} {L : Type v}
    [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L]
    [IsGalois K L]

/-- After transporting the completion at `w ∘ g` back to the chosen
completion at `w`, the corresponding component of the tensor-product decomposition is
evaluation of the `g`-conjugate tensor. -/
theorem conjugateExtensionCompletionRingEquiv_completionTensorDecomposition_left
    (vK : AbsoluteValue K ℝ) (hvK : vK.IsNontrivial)
    (w : AbsoluteValueExtension vK L)
    (g : L ≃ₐ[K] L)
    (z : LocalTensorAlgebra (L := L) vK) :
    letI : ∀ w' : AbsoluteValueExtension vK L,
        Algebra vK.Completion w'.1.Completion :=
      fun w' ↦ AbsoluteValue.completionAlgebra vK w'.1 w'.2
    conjugateExtensionCompletionRingEquiv vK w g
        (completionTensorDecomposition_left (K := K) (L := L) vK hvK z
          (absoluteValueExtensionConjugate vK w g)) =
      absoluteValueExtension_localizationTensorHom vK w
        (localTensorConjugation vK g z) := by
  let _ : ∀ w' : AbsoluteValueExtension vK L,
      Algebra vK.Completion w'.1.Completion :=
    fun w' ↦ AbsoluteValue.completionAlgebra vK w'.1 w'.2
  induction z using OAI.tensorInductionOn with
  | add x y hx hy =>
      simpa only [map_add, Pi.add_apply] using
        congrArg₂ (· + ·) hx hy
  | tmul b x =>
      rw [completionTensorDecomposition_left_tmul_apply,
        map_mul,
        conjugateExtensionCompletionRingEquiv_algebraMap]
      change
        algebraMap vK.Completion w.1.Completion b *
            conjugateExtensionCompletionRingEquiv vK w g
              (AbsoluteValue.toCompletion
                (absoluteValueExtensionConjugate vK w g).1 x) =
          absoluteValueExtension_localizationTensorHom vK w
            (localTensorConjugation vK g (b ⊗ₜ[K] x))
      rw [conjugateExtensionCompletionRingEquiv_toCompletion,
        localTensorConjugation_tmul,
        absoluteValueExtension_localizationTensorHom_tmul]
      change
        algebraMap vK.Completion w.1.Completion b *
            AbsoluteValue.toCompletion w.1 (g x) =
          algebraMap vK.Completion w.1.Completion b *
            AbsoluteValue.toCompletion w.1 (g x)
      rfl

section ProductEquivalences

variable (vK : AbsoluteValue K ℝ) (hvK : vK.IsNontrivial)
    (w : AbsoluteValueExtension vK L)

/-- Concrete tensor realization of the induced local block: the actual local unit group
`(K_v ⊗[K] L)ˣ` is multiplicatively equivalent to the induced block from
the decomposition group at a chosen extension `w`. -/
noncomputable def localTensorUnitsEquivLocalPlaceBlock :
    letI :=
      decompositionGroupLocalUnitsAction vK hvK w
    letI hK := AbsoluteValue.extensionCompletionAlgebra (K := K) w.1
    letI : SMul K w.1.Completion := hK.toSMul
    letI := AbsoluteValue.completionAlgebra vK w.1 w.2
    letI : ∀ w' : AbsoluteValueExtension vK L,
        Algebra vK.Completion w'.1.Completion :=
      fun w' ↦ AbsoluteValue.completionAlgebra vK w'.1 w'.2
    (LocalTensorAlgebra (L := L) vK)ˣ ≃*
      LocalPlaceBlock vK hvK w := by
  letI :=
    decompositionGroupLocalUnitsAction vK hvK w
  letI hK := AbsoluteValue.extensionCompletionAlgebra (K := K) w.1
  letI : SMul K w.1.Completion := hK.toSMul
  letI := AbsoluteValue.completionAlgebra vK w.1 w.2
  letI : ∀ w' : AbsoluteValueExtension vK L,
      Algebra vK.Completion w'.1.Completion :=
    fun w' ↦ AbsoluteValue.completionAlgebra vK w'.1 w'.2
  exact
    (localTensorUnitsEquivCompletionProduct vK hvK).trans
      (completionProductUnitsEquivLocalPlaceBlock vK hvK w)

/-- On the chosen representative of a right coset, the concrete
The tensor-product equivalence is the canonical orbit-evaluation map. -/
theorem localTensorUnitsEquivLocalPlaceBlock_apply_out_coe
    (z : (LocalTensorAlgebra (L := L) vK)ˣ)
    (q : InducedRightCosets
      (absoluteValueDecompositionGroup K w.1)) :
    letI :=
      decompositionGroupLocalUnitsAction vK hvK w
    letI hK := AbsoluteValue.extensionCompletionAlgebra (K := K) w.1
    letI : SMul K w.1.Completion := hK.toSMul
    letI := AbsoluteValue.completionAlgebra vK w.1 w.2
    letI : ∀ w' : AbsoluteValueExtension vK L,
        Algebra vK.Completion w'.1.Completion :=
      fun w' ↦ AbsoluteValue.completionAlgebra vK w'.1 w'.2
    (((localTensorUnitsEquivLocalPlaceBlock vK hvK w z).1
        (Quotient.out q) :
          (LocalizedCompletion vK w)ˣ) :
      LocalizedCompletion vK w) =
      localTensorEvaluation vK hvK w
        (localTensorConjugation vK (Quotient.out q)
          (z : LocalTensorAlgebra (L := L) vK)) := by
  let _ :=
    decompositionGroupLocalUnitsAction vK hvK w
  let hK := AbsoluteValue.extensionCompletionAlgebra (K := K) w.1
  let _ : SMul K w.1.Completion := hK.toSMul
  let _ := AbsoluteValue.completionAlgebra vK w.1 w.2
  let _ : ∀ w' : AbsoluteValueExtension vK L,
      Algebra vK.Completion w'.1.Completion :=
    fun w' ↦ AbsoluteValue.completionAlgebra vK w'.1 w'.2
  have hcoord :
      inducedRightCosetCoordinates
          (absoluteValueDecompositionGroup K w.1)
          (localTensorUnitsEquivLocalPlaceBlock vK hvK w z) q =
        completionProductUnitsEquivRightCosets vK hvK w
          (localTensorUnitsEquivCompletionProduct vK hvK z) q := by
    change
      inducedRightCosetCoordinates
          (absoluteValueDecompositionGroup K w.1)
          ((inducedRightCosetCoordinates
            (absoluteValueDecompositionGroup K w.1)).symm
            (completionProductUnitsEquivRightCosets vK hvK w
              (localTensorUnitsEquivCompletionProduct vK hvK z))) q =
        completionProductUnitsEquivRightCosets vK hvK w
          (localTensorUnitsEquivCompletionProduct vK hvK z) q
    rw [MulEquiv.apply_symm_apply]
  have hval := congrArg
    (fun u : (LocalizedCompletion vK w)ˣ =>
      (u : LocalizedCompletion vK w)) hcoord
  change
    (((localTensorUnitsEquivLocalPlaceBlock vK hvK w z).1
        (Quotient.out q) :
          (LocalizedCompletion vK w)ˣ) :
      LocalizedCompletion vK w) =
      ((completionProductUnitsEquivRightCosets vK hvK w
          (localTensorUnitsEquivCompletionProduct vK hvK z) q :
            (LocalizedCompletion vK w)ˣ) :
        LocalizedCompletion vK w) at hval
  rw [hval,
    completionProductUnitsEquivRightCosets_apply_coe,
    localTensorUnitsEquivCompletionProduct_apply_coe]
  change
    (localizedCompletionEquivCompletion vK hvK w).symm
        (conjugateExtensionCompletionRingEquiv
          vK w (Quotient.out q)
          (completionTensorDecomposition_left (K := K) (L := L) vK hvK
            (z : LocalTensorAlgebra (L := L) vK)
            (absoluteValueExtensionConjugate
              vK w (Quotient.out q)))) =
      localTensorEvaluation vK hvK w
        (localTensorConjugation vK (Quotient.out q)
          (z : LocalTensorAlgebra (L := L) vK))
  rw [conjugateExtensionCompletionRingEquiv_completionTensorDecomposition_left]
  rfl

/-- The multiplicative equivalence obtained from the tensor-product decomposition is
literally the canonical orbit-evaluation homomorphism. -/
theorem localTensorUnitsEquivLocalPlaceBlock_eq_orbitHom_apply
    (z : (LocalTensorAlgebra (L := L) vK)ˣ) :
    letI :=
      decompositionGroupLocalUnitsAction vK hvK w
    letI hK := AbsoluteValue.extensionCompletionAlgebra (K := K) w.1
    letI : SMul K w.1.Completion := hK.toSMul
    letI := AbsoluteValue.completionAlgebra vK w.1 w.2
    letI : ∀ w' : AbsoluteValueExtension vK L,
        Algebra vK.Completion w'.1.Completion :=
      fun w' ↦ AbsoluteValue.completionAlgebra vK w'.1 w'.2
    localTensorUnitsEquivLocalPlaceBlock vK hvK w z =
      localTensorOrbitHom vK hvK w z := by
  let _ :=
    decompositionGroupLocalUnitsAction vK hvK w
  let hK := AbsoluteValue.extensionCompletionAlgebra (K := K) w.1
  let _ : SMul K w.1.Completion := hK.toSMul
  let _ := AbsoluteValue.completionAlgebra vK w.1 w.2
  let _ : ∀ w' : AbsoluteValueExtension vK L,
      Algebra vK.Completion w'.1.Completion :=
    fun w' ↦ AbsoluteValue.completionAlgebra vK w'.1 w'.2
  apply
    (inducedRightCosetCoordinates
      (absoluteValueDecompositionGroup K w.1)).injective
  funext q
  apply Units.ext
  change
    (((localTensorUnitsEquivLocalPlaceBlock vK hvK w z).1
        (Quotient.out q) :
          (LocalizedCompletion vK w)ˣ) :
      LocalizedCompletion vK w) =
      localTensorEvaluation vK hvK w
        (localTensorConjugation vK (Quotient.out q)
          (z : LocalTensorAlgebra (L := L) vK))
  exact
    localTensorUnitsEquivLocalPlaceBlock_apply_out_coe
      vK hvK w z q

/-- Equivariant concrete form: the actual tensor local factor
and the induced local block are equivalent compatibly with the full
Galois action. -/
theorem localTensorUnitsEquivLocalPlaceBlock_smul
    (τ : L ≃ₐ[K] L)
    (z : (LocalTensorAlgebra (L := L) vK)ˣ) :
    letI :=
      decompositionGroupLocalUnitsAction vK hvK w
    letI hK := AbsoluteValue.extensionCompletionAlgebra (K := K) w.1
    letI : SMul K w.1.Completion := hK.toSMul
    letI := AbsoluteValue.completionAlgebra vK w.1 w.2
    letI : ∀ w' : AbsoluteValueExtension vK L,
        Algebra vK.Completion w'.1.Completion :=
      fun w' ↦ AbsoluteValue.completionAlgebra vK w'.1 w'.2
    letI := localTensorUnitsAction (K := K) (L := L) vK
    localTensorUnitsEquivLocalPlaceBlock vK hvK w (τ • z) =
      τ • localTensorUnitsEquivLocalPlaceBlock vK hvK w z := by
  let _ :=
    decompositionGroupLocalUnitsAction vK hvK w
  let hK := AbsoluteValue.extensionCompletionAlgebra (K := K) w.1
  let _ : SMul K w.1.Completion := hK.toSMul
  let _ := AbsoluteValue.completionAlgebra vK w.1 w.2
  let _ : ∀ w' : AbsoluteValueExtension vK L,
      Algebra vK.Completion w'.1.Completion :=
    fun w' ↦ AbsoluteValue.completionAlgebra vK w'.1 w'.2
  let _ := localTensorUnitsAction (K := K) (L := L) vK
  rw [localTensorUnitsEquivLocalPlaceBlock_eq_orbitHom_apply,
    localTensorUnitsEquivLocalPlaceBlock_eq_orbitHom_apply]
  exact localTensorOrbitHom_smul vK hvK w τ z

end ProductEquivalences

end LocalClassFieldTheory
end
end

section
-- module Solutions.OAIQ244_DUKE.AlgebraicNumberTheory_Adele_FinitePlaceTensorBlock
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalCyclotomicCompletionAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.residueFieldZModAlgebra _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.LubinTate.compatibleGroupFamiliesGroup _root_.OAI.PrimeDegreePackets.diagonalLogAction _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.CyclicCohomology.binaryCoefficientFamilyCommGroup _root_.CyclicCohomology.instMulDistribMulActionBinaryCoefficientFamily _root_.LocalClassFieldTheory.normalizationIntegerRingIsIntegralClosure _root_.chosenFinitePlaceCompletionAlgebra _root_.chosenFinitePlaceCompletionContinuousSMul _root_.chosenFinitePlaceCompletionFiniteDimensional _root_.chosenFinitePlaceCompletionLocallyCompactSpace _root_.chosenFinitePlaceLocalizedFiniteDimensional _root_.chosenFinitePlaceLocalizedIntegerAlgebra _root_.chosenFinitePlaceLocalizedIntegerModuleFinite _root_.chosenFinitePlaceLocalizedIsGalois _root_.chosenFinitePlaceLocalizedIsIntegralClosure _root_.chosenFinitePlaceLocalizedIsNonarchimedeanLocalField _root_.chosenFinitePlaceLocalizedIsValuativeTopology _root_.chosenFinitePlaceLocalizedLocallyCompactSpace _root_.chosenFinitePlaceLocalizedValuationCompatible _root_.chosenFinitePlaceLocalizedValuationHasExtension _root_.chosenFinitePlaceLocalizedValuationIsNontrivial _root_.chosenFinitePlaceLocalizedValuativeRel _root_.chosenFinitePlaceLocalizedValuativeRelIsNontrivial _root_.chosenFinitePlaceLocalizedValued _root_.scaledRelativeIntegerLatticeQuotientFinite
attribute [-simp] _root_.IsDiscreteValuationRing.addVal_ringEquiv _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.OAI.PrimeDegreePackets.ThetaConstruction.schwartzCM_apply _root_.infinitePlaceLocalTensorAlgEquiv_tmul _root_.infinitePlace_mult_smul
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

/-!
# Finite-place tensor factors as induced local blocks

This file is the finite-place counterpart of
`InfinitePlaceTensorBlock`.  It compares the concrete completion
`K_v` used by the idele restricted product with the absolute-value
completion used by the canonical local tensor decomposition, and records equivariance for
conjugation on the second tensor factor.
-/

open scoped NumberField TensorProduct
open NumberField IsDedekindDomain

noncomputable section

open LocalClassFieldTheory


open AlgebraicNumberTheory.Valuations
open HilbertRamification

variable {K L : Type}
    [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]

omit [NumberField L] [FiniteDimensional K L] [IsGalois K L] in
/-- Base change from the absolute-value completion to the concrete
adic completion commutes with conjugation on `L`. -/
theorem finitePlaceLocalTensorAlgEquiv_conjugation
    (v : HeightOneSpectrum (𝓞 K))
    (σ : L ≃ₐ[K] L)
    (z :
      LocalTensorAlgebra (L := L)
        (HeightOneSpectrum.adicAbv K v)) :
    finitePlaceLocalTensorAlgEquiv
        (K := K) (L := L) v
        (localTensorConjugation
          (K := K) (L := L)
          (HeightOneSpectrum.adicAbv K v) σ z) =
      scalarTensorConjugation
        (K := K) (L := L)
        (A := v.adicCompletion K) σ
        (finitePlaceLocalTensorAlgEquiv
          (K := K) (L := L) v z) := by
  induction z using OAI.tensorInductionOn with
  | tmul a x => rfl
  | add x y hx hy => simp [hx, hy]

omit [NumberField L] [FiniteDimensional K L] [IsGalois K L] in
/-- The finite-completion comparison on tensor units is equivariant. -/
theorem finitePlaceLocalTensorUnitsEquiv_smul
    (v : HeightOneSpectrum (𝓞 K))
    (σ : L ≃ₐ[K] L)
    (z :
      (LocalTensorAlgebra (L := L)
        (HeightOneSpectrum.adicAbv K v))ˣ) :
    letI :=
      localTensorUnitsAction
        (K := K) (L := L)
        (HeightOneSpectrum.adicAbv K v)
    letI :=
      scalarTensorUnitsAction
        (K := K) (L := L)
        (A := v.adicCompletion K)
    finitePlaceLocalTensorUnitsEquiv
        (K := K) (L := L) v (σ • z) =
      σ • finitePlaceLocalTensorUnitsEquiv
        (K := K) (L := L) v z := by
  let :=
    localTensorUnitsAction
      (K := K) (L := L)
      (HeightOneSpectrum.adicAbv K v)
  let :=
    scalarTensorUnitsAction
      (K := K) (L := L)
      (A := v.adicCompletion K)
  apply Units.ext
  exact finitePlaceLocalTensorAlgEquiv_conjugation
    (K := K) (L := L) v σ
      (z :
        LocalTensorAlgebra (L := L)
          (HeightOneSpectrum.adicAbv K v))

omit [NumberField L] [FiniteDimensional K L] [IsGalois K L] in
/-- Equivariance of the inverse finite-completion comparison. -/
theorem finitePlaceLocalTensorUnitsEquiv_symm_smul
    (v : HeightOneSpectrum (𝓞 K))
    (σ : L ≃ₐ[K] L)
    (z : (v.adicCompletion K ⊗[K] L)ˣ) :
    letI :=
      localTensorUnitsAction
        (K := K) (L := L)
        (HeightOneSpectrum.adicAbv K v)
    letI :=
      scalarTensorUnitsAction
        (K := K) (L := L)
        (A := v.adicCompletion K)
    (finitePlaceLocalTensorUnitsEquiv
        (K := K) (L := L) v).symm (σ • z) =
      σ •
        (finitePlaceLocalTensorUnitsEquiv
          (K := K) (L := L) v).symm z := by
  let :=
    localTensorUnitsAction
      (K := K) (L := L)
      (HeightOneSpectrum.adicAbv K v)
  let :=
    scalarTensorUnitsAction
      (K := K) (L := L)
      (A := v.adicCompletion K)
  apply
    (finitePlaceLocalTensorUnitsEquiv
      (K := K) (L := L) v).injective
  rw [MulEquiv.apply_symm_apply,
    finitePlaceLocalTensorUnitsEquiv_smul,
    MulEquiv.apply_symm_apply]

/-- The local tensor decomposition for the concrete finite component type used by relative
ideles. -/
noncomputable def finitePlaceTensorUnitsEquivLocalPlaceBlock
    (v : HeightOneSpectrum (𝓞 K))
    (w : AbsoluteValueExtension
      (HeightOneSpectrum.adicAbv K v) L) :
    letI :=
      decompositionGroupLocalUnitsAction
        (HeightOneSpectrum.adicAbv K v)
        (RayClass.adicAbv_isNontrivial v) w
    letI hK :=
      AbsoluteValue.extensionCompletionAlgebra
        (K := K) w.1
    letI : SMul K w.1.Completion := hK.toSMul
    letI :=
      AbsoluteValue.completionAlgebra
        (HeightOneSpectrum.adicAbv K v) w.1 w.2
    letI : ∀ w' : AbsoluteValueExtension
        (HeightOneSpectrum.adicAbv K v) L,
      Algebra
        (HeightOneSpectrum.adicAbv K v).Completion
        w'.1.Completion :=
      fun w' =>
        AbsoluteValue.completionAlgebra
          (HeightOneSpectrum.adicAbv K v)
          w'.1 w'.2
    (v.adicCompletion K ⊗[K] L)ˣ ≃*
      LocalPlaceBlock
        (HeightOneSpectrum.adicAbv K v)
        (RayClass.adicAbv_isNontrivial v) w :=
  (finitePlaceLocalTensorUnitsEquiv
      (K := K) (L := L) v).symm.trans
    (localTensorUnitsEquivLocalPlaceBlock
      (HeightOneSpectrum.adicAbv K v)
      (RayClass.adicAbv_isNontrivial v) w)

section Equivariance

variable
    (v : HeightOneSpectrum (𝓞 K))
    (w : AbsoluteValueExtension
      (HeightOneSpectrum.adicAbv K v) L)

local instance finitePlaceDecompositionGroupAction_rb03dac_1 :
    MulDistribMulAction
      (absoluteValueDecompositionGroup K w.1)
      (AlgebraicNumberTheory.Valuations.LocalizedCompletion
        (HeightOneSpectrum.adicAbv K v) w)ˣ :=
  decompositionGroupLocalUnitsAction
    (HeightOneSpectrum.adicAbv K v)
    (RayClass.adicAbv_isNontrivial v) w
local instance finitePlaceExtensionCompletionAlgebra_rb03dac_1 :
    Algebra K w.1.Completion :=
  AbsoluteValue.extensionCompletionAlgebra (K := K) w.1
local instance finitePlaceLocalizedCompletionAlgebra_rb03dac_1 :
    Algebra
      (HeightOneSpectrum.adicAbv K v).Completion
      w.1.Completion :=
  AbsoluteValue.completionAlgebra
    (HeightOneSpectrum.adicAbv K v) w.1 w.2
local instance finitePlaceAllCompletionAlgebra_rb03dac_1
    (w' : AbsoluteValueExtension
      (HeightOneSpectrum.adicAbv K v) L) :
    Algebra
      (HeightOneSpectrum.adicAbv K v).Completion
      w'.1.Completion :=
  AbsoluteValue.completionAlgebra
    (HeightOneSpectrum.adicAbv K v) w'.1 w'.2
attribute [local instance] finitePlaceScalarTensorUnitsAction
attribute [local instance] finitePlaceLocalTensorUnitsAction
omit [NumberField L] in
/-- The concrete finite-place local tensor decomposition is equivariant for the
full global Galois action. -/
theorem finitePlaceTensorUnitsEquivLocalPlaceBlock_smul
    (σ : L ≃ₐ[K] L)
    (z : (v.adicCompletion K ⊗[K] L)ˣ) :
    finitePlaceTensorUnitsEquivLocalPlaceBlock
        (K := K) (L := L) v w (σ • z) =
      σ •
        finitePlaceTensorUnitsEquivLocalPlaceBlock
          (K := K) (L := L) v w z := by
  have hsource :
      (finitePlaceLocalTensorUnitsEquiv
          (K := K) (L := L) v).symm (σ • z) =
        σ •
          (finitePlaceLocalTensorUnitsEquiv
            (K := K) (L := L) v).symm z :=
    finitePlaceLocalTensorUnitsEquiv_symm_smul
      (K := K) (L := L) v σ z
  calc
    finitePlaceTensorUnitsEquivLocalPlaceBlock
        (K := K) (L := L) v w (σ • z) =
      localTensorUnitsEquivLocalPlaceBlock
        (HeightOneSpectrum.adicAbv K v)
        (RayClass.adicAbv_isNontrivial v) w
        (σ •
          (finitePlaceLocalTensorUnitsEquiv
            (K := K) (L := L) v).symm z) :=
      congrArg
        (localTensorUnitsEquivLocalPlaceBlock
          (HeightOneSpectrum.adicAbv K v)
          (RayClass.adicAbv_isNontrivial v) w)
        hsource
    _ =
      σ •
        finitePlaceTensorUnitsEquivLocalPlaceBlock
          (K := K) (L := L) v w z :=
      localTensorUnitsEquivLocalPlaceBlock_smul
        (HeightOneSpectrum.adicAbv K v)
        (RayClass.adicAbv_isNontrivial v) w σ
        ((finitePlaceLocalTensorUnitsEquiv
          (K := K) (L := L) v).symm z)

end Equivariance
end
end

section
-- module Solutions.OAIQ244_DUKE.AlgebraicNumberTheory_Adele_InfinitePlaceTensorBlock
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalCyclotomicCompletionAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.HilbertRamification.decompositionField_decompositionField_integerMap_isLocalHom _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.residueFieldZModAlgebra _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.LubinTate.compatibleGroupFamiliesGroup _root_.OAI.PrimeDegreePackets.diagonalLogAction _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionResidueField.instField _root_.RamificationTheory.HilbertRamification.ValuationSubring.selectedResidueField.instAlgebra _root_.CyclicCohomology.binaryCoefficientFamilyCommGroup _root_.CyclicCohomology.instMulDistribMulActionBinaryCoefficientFamily _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.LocalClassFieldTheory.normalizationIntegerRingIsIntegralClosure _root_.adicCompletionProperSpace _root_.chosenFinitePlaceCompletionAlgebra _root_.chosenFinitePlaceCompletionContinuousSMul _root_.chosenFinitePlaceCompletionFiniteDimensional _root_.chosenFinitePlaceCompletionLocallyCompactSpace _root_.chosenFinitePlaceLocalizedFiniteDimensional _root_.chosenFinitePlaceLocalizedIntegerAlgebra _root_.chosenFinitePlaceLocalizedIntegerModuleFinite _root_.chosenFinitePlaceLocalizedIsGalois _root_.chosenFinitePlaceLocalizedIsIntegralClosure _root_.chosenFinitePlaceLocalizedIsNonarchimedeanLocalField _root_.chosenFinitePlaceLocalizedIsValuativeTopology _root_.chosenFinitePlaceLocalizedLocallyCompactSpace _root_.chosenFinitePlaceLocalizedValuationCompatible _root_.chosenFinitePlaceLocalizedValuationHasExtension _root_.chosenFinitePlaceLocalizedValuationIsNontrivial _root_.chosenFinitePlaceLocalizedValuativeRel _root_.chosenFinitePlaceLocalizedValuativeRelIsNontrivial _root_.chosenFinitePlaceLocalizedValued _root_.finiteLocalUnitsOpen _root_.relativeAdeleRingIntermediateAlgebra _root_.relativeAdeleRingTopIntermediateAlgebra
attribute [-simp] _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.IsDiscreteValuationRing.addVal_ringEquiv _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.LocalFieldTheory.residueField_algebraMap_residue _root_.OAI.PrimeDegreePackets.ThetaConstruction.schwartzCM_apply _root_.infinitePlace_mult_smul
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

/-!
# Archimedean relative-idele factors as induced local blocks

The concrete archimedean completion `w.Completion` used by the adele
library is canonically the completion of the underlying absolute value
`w.1`.  Base change along this equivalence connects the actual
archimedean component of a relative idele to the local tensor block of
the local tensor decomposition, equivariantly for the full Galois action.
-/

open scoped NumberField TensorProduct NumberField.LiesOver
open NumberField

noncomputable section

open LocalClassFieldTheory


open AlgebraicNumberTheory.Valuations
open HilbertRamification

universe u v

variable
    {K : Type u} {L : Type v}
    [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L]

omit [NumberField K] [NumberField L] [FiniteDimensional K L] in
/-- Completion comparison commutes with conjugation on the second
tensor factor. -/
theorem infinitePlaceLocalTensorAlgEquiv_conjugation
    (w : InfinitePlace K)
    (σ : L ≃ₐ[K] L)
    (z : w.Completion ⊗[K] L) :
    infinitePlaceLocalTensorAlgEquiv
        (K := K) (L := L) w
        (scalarTensorConjugation
          (K := K) (L := L)
          (A := w.Completion) σ z) =
      localTensorConjugation
        (K := K) (L := L) w.1 σ
        (infinitePlaceLocalTensorAlgEquiv
          (K := K) (L := L) w z) := by
  induction z using OAI.tensorInductionOn with
  | tmul a x => rfl
  | add x y hx hy => simp [hx, hy]

omit [NumberField K] [NumberField L] [FiniteDimensional K L] in
/-- The completion comparison on units is equivariant. -/
theorem infinitePlaceLocalTensorUnitsEquiv_smul
    (w : InfinitePlace K)
    (σ : L ≃ₐ[K] L)
    (z : (w.Completion ⊗[K] L)ˣ) :
    letI := scalarTensorUnitsAction
      (K := K) (L := L) (A := w.Completion)
    letI := localTensorUnitsAction
      (K := K) (L := L) w.1
    infinitePlaceLocalTensorUnitsEquiv
        (K := K) (L := L) w (σ • z) =
      σ • infinitePlaceLocalTensorUnitsEquiv
        (K := K) (L := L) w z := by
  let := scalarTensorUnitsAction
    (K := K) (L := L) (A := w.Completion)
  let := localTensorUnitsAction
    (K := K) (L := L) w.1
  apply Units.ext
  exact infinitePlaceLocalTensorAlgEquiv_conjugation
    (K := K) (L := L) w σ
      (z : w.Completion ⊗[K] L)

section Galois

variable [IsGalois K L]

/-- The local tensor decomposition for the actual archimedean component type used by the
relative idele restricted product. -/
noncomputable def
    infinitePlaceTensorUnitsEquivLocalPlaceBlock
    (w : InfinitePlace K)
    (hw : w.1.IsNontrivial)
    (u : AbsoluteValueExtension w.1 L) :
    letI :=
      decompositionGroupLocalUnitsAction w.1 hw u
    letI hK :=
      AbsoluteValue.extensionCompletionAlgebra
        (K := K) u.1
    letI : SMul K u.1.Completion := hK.toSMul
    letI :=
      AbsoluteValue.completionAlgebra
        w.1 u.1 u.2
    letI : ∀ u' : AbsoluteValueExtension w.1 L,
        Algebra w.1.Completion u'.1.Completion :=
      fun u' =>
        AbsoluteValue.completionAlgebra
          w.1 u'.1 u'.2
    (w.Completion ⊗[K] L)ˣ ≃*
      LocalPlaceBlock w.1 hw u := by
  letI :=
    decompositionGroupLocalUnitsAction w.1 hw u
  letI hK :=
    AbsoluteValue.extensionCompletionAlgebra
      (K := K) u.1
  letI : SMul K u.1.Completion := hK.toSMul
  letI :=
    AbsoluteValue.completionAlgebra
      w.1 u.1 u.2
  letI : ∀ u' : AbsoluteValueExtension w.1 L,
      Algebra w.1.Completion u'.1.Completion :=
    fun u' =>
      AbsoluteValue.completionAlgebra
        w.1 u'.1 u'.2
  exact
    (infinitePlaceLocalTensorUnitsEquiv
      (K := K) (L := L) w).trans
      (localTensorUnitsEquivLocalPlaceBlock
        w.1 hw u)

section Equivariance

variable
    (w : InfinitePlace K)
    (hw : w.1.IsNontrivial)
    (u : AbsoluteValueExtension w.1 L)

attribute [local instance] infinitePlaceScalarTensorUnitsAction
local instance infinitePlaceLocalTensorUnitsAction :
    MulDistribMulAction
      (L ≃ₐ[K] L)
      (LocalTensorAlgebra (L := L) w.1)ˣ :=
  localTensorUnitsAction (K := K) (L := L) w.1

local instance infinitePlaceExtensionCompletionAlgebra_rb03dac_1 :
    Algebra K u.1.Completion :=
  AbsoluteValue.extensionCompletionAlgebra (K := K) u.1
local instance infinitePlaceLocalizedCompletionAlgebra_rb03dac_1 :
    Algebra w.1.Completion u.1.Completion :=
  AbsoluteValue.completionAlgebra w.1 u.1 u.2
local instance infinitePlaceAllCompletionAlgebra_rb03dac_1
    (u' : AbsoluteValueExtension w.1 L) :
    Algebra w.1.Completion u'.1.Completion :=
  AbsoluteValue.completionAlgebra w.1 u'.1 u'.2
omit [NumberField K] [NumberField L] in
/-- The actual archimedean local tensor equivalence is equivariant for the
full Galois action. -/
theorem
    infinitePlaceTensorUnitsEquivLocalPlaceBlock_smul
    (σ : L ≃ₐ[K] L)
    (z : (w.Completion ⊗[K] L)ˣ) :
    letI :=
      decompositionGroupLocalUnitsAction w.1 hw u
    infinitePlaceTensorUnitsEquivLocalPlaceBlock
        (K := K) (L := L) w hw u (σ • z) =
      σ •
        infinitePlaceTensorUnitsEquivLocalPlaceBlock
          (K := K) (L := L) w hw u z := by
  let :=
    decompositionGroupLocalUnitsAction w.1 hw u
  have hsource :
      infinitePlaceLocalTensorUnitsEquiv
          (K := K) (L := L) w (σ • z) =
        σ • infinitePlaceLocalTensorUnitsEquiv
          (K := K) (L := L) w z :=
    infinitePlaceLocalTensorUnitsEquiv_smul
      (K := K) (L := L) w σ z
  calc
    infinitePlaceTensorUnitsEquivLocalPlaceBlock
        (K := K) (L := L) w hw u (σ • z) =
      localTensorUnitsEquivLocalPlaceBlock w.1 hw u
        (σ • infinitePlaceLocalTensorUnitsEquiv
          (K := K) (L := L) w z) :=
      congrArg
        (localTensorUnitsEquivLocalPlaceBlock w.1 hw u)
        hsource
    _ =
      σ • infinitePlaceTensorUnitsEquivLocalPlaceBlock
        (K := K) (L := L) w hw u z :=
      localTensorUnitsEquivLocalPlaceBlock_smul
        w.1 hw u σ
        (infinitePlaceLocalTensorUnitsEquiv
          (K := K) (L := L) w z)

end Equivariance

end Galois
end
end

section
-- module Solutions.OAIQ244_DUKE.LocalClassFieldTheory_ClassFormation_ArchimedeanHilbert90
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalCyclotomicCompletionAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitQuotientCarrier_finite _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.residueFieldZModAlgebra _root_.LocalFieldTheory.DiscreteValuationField.finite_nsmulAddKernel_padicInt_pi _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_multiplicative_nthPowerKernel _root_.LocalFieldTheory.finite_nsmulAddKernel_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.LubinTate.compatibleGroupFamiliesGroup _root_.OAI.PrimeDegreePackets.boundedRealFields_finite _root_.OAI.PrimeDegreePackets.diagonalLogAction _root_.OAI.PrimeDegreePackets.instNonemptyLeafTestSpace _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionResidueField.instField _root_.RamificationTheory.HilbertRamification.ValuationSubring.selectedResidueField.instAlgebra _root_.RayClass.approximationCompletionTopologicalSpace _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.RelativeIdeleGroup.relativeIdeleMulAction _root_.CyclicCohomology.binaryCoefficientFamilyCommGroup _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.LocalClassFieldTheory.normalizationIntegerRingIsIntegralClosure _root_.adicCompletionProperSpace _root_.chosenFinitePlaceCompletionAlgebra _root_.chosenFinitePlaceCompletionContinuousSMul _root_.chosenFinitePlaceCompletionFiniteDimensional _root_.chosenFinitePlaceCompletionLocallyCompactSpace _root_.chosenFinitePlaceLocalizedFiniteDimensional _root_.chosenFinitePlaceLocalizedIntegerAlgebra _root_.chosenFinitePlaceLocalizedIntegerModuleFinite _root_.chosenFinitePlaceLocalizedIsGalois _root_.chosenFinitePlaceLocalizedIsIntegralClosure _root_.chosenFinitePlaceLocalizedIsNonarchimedeanLocalField _root_.chosenFinitePlaceLocalizedIsValuativeTopology _root_.chosenFinitePlaceLocalizedLocallyCompactSpace _root_.chosenFinitePlaceLocalizedValuationCompatible _root_.chosenFinitePlaceLocalizedValuationHasExtension _root_.chosenFinitePlaceLocalizedValuationIsNontrivial _root_.chosenFinitePlaceLocalizedValuativeRel _root_.chosenFinitePlaceLocalizedValuativeRelIsNontrivial _root_.chosenFinitePlaceLocalizedValued _root_.finiteLocalUnitsOpen _root_.relativeAdeleRingIntermediateAlgebra _root_.relativeAdeleRingTopIntermediateAlgebra
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

/-!
# The Hilbert-90 half of the local class-field axiom at every place

The degree-minus-one assertion for the archimedean local block is independent of
the nonarchimedean local reciprocity theorem.  It follows directly from
Hilbert 90 for the algebraic localization, and therefore applies also
at archimedean places.
-/

open AlgebraicNumberTheory.Valuations
open HilbertRamification
open CyclicCohomology
open CyclicCohomology.ProfiniteCohomology.Herbrand

noncomputable section

namespace LocalClassFieldTheory

variable {K L : Type}
    [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]

/-- Hilbert 90 makes the local `H⁻¹` group trivial for an arbitrary
nontrivial absolute value, including an infinite place. -/
theorem localHerbrandHMinusOne_subsingleton
    (vK : AbsoluteValue K ℝ) (hvK : vK.IsNontrivial)
    (w : AbsoluteValueExtension vK L)
    (σ : L ≃ₐ[K] L)
    (hgen : ∀ τ : L ≃ₐ[K] L,
      τ ∈ Subgroup.zpowers σ) :
    letI hK :=
      AbsoluteValue.extensionCompletionAlgebra
        (K := K) w.1
    letI : SMul K w.1.Completion := hK.toSMul
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
    letI : Fintype (absoluteValueDecompositionGroup K w.1) :=
      Fintype.ofFinite _
    letI :=
      decompositionGroupLocalUnitsAction vK hvK w
    Subsingleton
      (HerbrandHMinusOne
        (absoluteValueDecompositionGroup K w.1)
        (LocalizedCompletion vK w)ˣ
        (subgroupGeneratorOfGenerator
          (absoluteValueDecompositionGroup K w.1)
          σ hgen)) := by
  let hK :=
    AbsoluteValue.extensionCompletionAlgebra
      (K := K) w.1
  let : SMul K w.1.Completion := hK.toSMul
  let : Algebra vK.Completion w.1.Completion :=
    AbsoluteValue.completionAlgebra vK w.1 w.2
  let := localizedCompletionGlobalAlgebra vK w
  let := localizedCompletionIsScalarTower vK w
  let : FiniteDimensional vK.Completion
      (LocalizedCompletion vK w) :=
    localizedCompletionModuleFinite vK hvK w
  let : IsGalois vK.Completion
      (LocalizedCompletion vK w) :=
    HilbertRamification.algebraicLocalization_isGalois vK w
  let : Fintype (absoluteValueDecompositionGroup K w.1) :=
    Fintype.ofFinite _
  let :=
    decompositionGroupLocalUnitsAction vK hvK w
  let E :=
    localHerbrandHMinusOneEquivUnitsTateHminusOne
      vK hvK w σ hgen
  let g :=
    localizedCompletionGaloisGenerator
      vK hvK w σ hgen
  let hg :=
    localizedCompletionGaloisGenerator_generates
      vK hvK w σ hgen
  have hzero :
      CategoryTheory.Limits.IsZero
        (tateCohomology
          (Rep.ofAlgebraAutOnUnits vK.Completion
            (LocalizedCompletion vK w)) (-1)) :=
    hilbert90_unitsTateHminusOne_isZero
      vK.Completion (LocalizedCompletion vK w) g hg
  let :
      Subsingleton
        (tateCohomology
          (Rep.ofAlgebraAutOnUnits vK.Completion
            (LocalizedCompletion vK w)) (-1)) :=
    ModuleCat.subsingleton_of_isZero hzero
  exact
    ⟨fun x y =>
      E.injective (Subsingleton.elim (E x) (E y))⟩

/-- The same universal Hilbert-90 conclusion as a finite-cardinality
statement. -/
theorem localHerbrandHMinusOne_card_eq_one_of_absoluteValue
    (vK : AbsoluteValue K ℝ) (hvK : vK.IsNontrivial)
    (w : AbsoluteValueExtension vK L)
    (σ : L ≃ₐ[K] L)
    (hgen : ∀ τ : L ≃ₐ[K] L,
      τ ∈ Subgroup.zpowers σ) :
    letI hK :=
      AbsoluteValue.extensionCompletionAlgebra
        (K := K) w.1
    letI : SMul K w.1.Completion := hK.toSMul
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
    letI : Fintype (absoluteValueDecompositionGroup K w.1) :=
      Fintype.ofFinite _
    letI :=
      decompositionGroupLocalUnitsAction vK hvK w
    Nat.card
      (HerbrandHMinusOne
        (absoluteValueDecompositionGroup K w.1)
        (LocalizedCompletion vK w)ˣ
        (subgroupGeneratorOfGenerator
          (absoluteValueDecompositionGroup K w.1)
          σ hgen)) = 1 := by
  let hK :=
    AbsoluteValue.extensionCompletionAlgebra
      (K := K) w.1
  let : SMul K w.1.Completion := hK.toSMul
  let : Algebra vK.Completion w.1.Completion :=
    AbsoluteValue.completionAlgebra vK w.1 w.2
  let := localizedCompletionGlobalAlgebra vK w
  let := localizedCompletionIsScalarTower vK w
  let : FiniteDimensional vK.Completion
      (LocalizedCompletion vK w) :=
    localizedCompletionModuleFinite vK hvK w
  let : IsGalois vK.Completion
      (LocalizedCompletion vK w) :=
    HilbertRamification.algebraicLocalization_isGalois vK w
  let : Fintype (absoluteValueDecompositionGroup K w.1) :=
    Fintype.ofFinite _
  let :=
    decompositionGroupLocalUnitsAction vK hvK w
  let :
      Subsingleton
        (HerbrandHMinusOne
          (absoluteValueDecompositionGroup K w.1)
          (LocalizedCompletion vK w)ˣ
          (subgroupGeneratorOfGenerator
            (absoluteValueDecompositionGroup K w.1)
            σ hgen)) :=
    localHerbrandHMinusOne_subsingleton
      vK hvK w σ hgen
  exact Nat.card_unique

end LocalClassFieldTheory
end
end

section
-- module Solutions.OAIQ244_DUKE.LocalClassFieldTheory_ClassFormation_ArchimedeanNormQuotient
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalCyclotomicCompletionAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitQuotientCarrier_finite _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.residueFieldZModAlgebra _root_.LocalFieldTheory.DiscreteValuationField.finite_nsmulAddKernel_padicInt_pi _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_multiplicative_nthPowerKernel _root_.LocalFieldTheory.finite_nsmulAddKernel_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.LubinTate.compatibleGroupFamiliesGroup _root_.OAI.PrimeDegreePackets.boundedRealFields_finite _root_.OAI.PrimeDegreePackets.diagonalLogAction _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.OAI.PrimeDegreePackets.xT2Space _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionResidueField.instField _root_.RamificationTheory.HilbertRamification.ValuationSubring.selectedResidueField.instAlgebra _root_.RayClass.approximationCompletionTopologicalSpace _root_.CyclicCohomology.binaryCoefficientFamilyCommGroup _root_.LocalClassFieldTheory.intrinsicAbsoluteGaloisT2 _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.LocalClassFieldTheory.normalizationIntegerRingIsIntegralClosure _root_.adicCompletionProperSpace _root_.chosenFinitePlaceCompletionAlgebra _root_.chosenFinitePlaceCompletionContinuousSMul _root_.chosenFinitePlaceCompletionFiniteDimensional _root_.chosenFinitePlaceCompletionLocallyCompactSpace _root_.chosenFinitePlaceLocalizedFiniteDimensional _root_.chosenFinitePlaceLocalizedIntegerAlgebra _root_.chosenFinitePlaceLocalizedIntegerModuleFinite _root_.chosenFinitePlaceLocalizedIsGalois _root_.chosenFinitePlaceLocalizedIsIntegralClosure _root_.chosenFinitePlaceLocalizedIsNonarchimedeanLocalField _root_.chosenFinitePlaceLocalizedIsValuativeTopology _root_.chosenFinitePlaceLocalizedLocallyCompactSpace _root_.chosenFinitePlaceLocalizedValuationCompatible _root_.chosenFinitePlaceLocalizedValuationHasExtension _root_.chosenFinitePlaceLocalizedValuationIsNontrivial _root_.chosenFinitePlaceLocalizedValuativeRel _root_.chosenFinitePlaceLocalizedValuativeRelIsNontrivial _root_.chosenFinitePlaceLocalizedValued _root_.finiteLocalUnitsOpen _root_.relativeAdeleRingIntermediateAlgebra _root_.relativeAdeleRingTopIntermediateAlgebra
attribute [-simp] _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.GlobalClassFieldTheory.Reciprocity.rationalCyclotomicGlobalToLocalizedAlgHom_apply _root_.GlobalClassFieldTheory.Reciprocity.rationalCyclotomicGlobalToLocalizedAlgHom_primitiveRoot _root_.IsDiscreteValuationRing.addVal_ringEquiv _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.LocalClassFieldTheory.mem_decompositionRightCosetsFinset _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.OAI.PrimeDegreePackets.ThetaConstruction.schwartzCM_apply _root_.doubleCosetExtension_mk _root_.extendAbsoluteValueExtensionFromIntermediate_apply _root_.finitePlaceLocalTensorDecompositionComponentRingHom_apply _root_.finitePlaceLocalTensorDecompositionComponent_add _root_.finitePlaceLocalTensorDecompositionComponent_tmul _root_.finitePlaceLocalTensorDecompositionComponent_zero _root_.finitePlaceLocalTensorDecompositionUnitsComponent_coe _root_.finitePlaceLocalTensorDecompositionUnitsEquiv_apply _root_.infinitePlace_mult_smul _root_.mem_finitePlaceDecompositionGroup_iff _root_.restrictAbsoluteValueExtensionToIntermediate_apply
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

/-- Field norms commute with compatible changes of both the base and
extension fields. -/
theorem normUnits_map_ringEquiv
    {K : Type u} {L : Type v} {K' : Type w} {L' : Type z}
    [Field K] [Field L] [Field K'] [Field L']
    [Algebra K L] [Algebra K' L']
    (eK : K ≃+* K') (eL : L ≃+* L')
    (he :
      RingHom.comp (algebraMap K' L') eK =
        RingHom.comp eL (algebraMap K L))
    (x : Lˣ) :
    Units.mapEquiv eK.toMulEquiv (normUnits K L x) =
      normUnits K' L'
        (Units.mapEquiv eL.toMulEquiv x) := by
  apply Units.ext
  change
    eK (Algebra.norm K (x : L)) =
      Algebra.norm K' (eL (x : L))
  rw [Algebra.norm_eq_of_equiv_equiv eK eL he]
  exact eK.apply_symm_apply _

/-- A compatible pair of field equivalences induces a map of norm
quotients. -/
def normQuotientMapOfRingEquiv
    {K L K' L' : Type}
    [Field K] [Field L] [Field K'] [Field L']
    [Algebra K L] [Algebra K' L']
    (eK : K ≃+* K') (eL : L ≃+* L')
    (he :
      RingHom.comp (algebraMap K' L') eK =
        RingHom.comp eL (algebraMap K L)) :
    NormQuotient K L →* NormQuotient K' L' :=
  normQuotientLift
    ((normClass K' L').comp
      (Units.mapEquiv eK.toMulEquiv).toMonoidHom)
    (by
      rintro x ⟨y, rfl⟩
      rw [MonoidHom.mem_ker]
      change
        normClass K' L'
          (Units.mapEquiv eK.toMulEquiv
            (normUnits K L y)) = 1
      rw [normUnits_map_ringEquiv eK eL he]
      exact mk_normUnits_eq_one K' L'
        (Units.mapEquiv eL.toMulEquiv y))

/-- Transporting a norm class through compatible field equivalences agrees
with transporting its representative unit. -/
@[simp]
theorem normQuotientMapOfRingEquiv_normClass
    {K L K' L' : Type}
    [Field K] [Field L] [Field K'] [Field L']
    [Algebra K L] [Algebra K' L']
    (eK : K ≃+* K') (eL : L ≃+* L')
    (he :
      RingHom.comp (algebraMap K' L') eK =
        RingHom.comp eL (algebraMap K L))
    (x : Kˣ) :
    normQuotientMapOfRingEquiv eK eL he
        (normClass K L x) =
      normClass K' L'
        (Units.mapEquiv eK.toMulEquiv x) :=
  normQuotientLift_normClass _ _ x

/-- Norm quotients are invariant under compatible equivalences of the
base and extension fields. -/
def normQuotientEquivOfRingEquiv
    {K L K' L' : Type}
    [Field K] [Field L] [Field K'] [Field L']
    [Algebra K L] [Algebra K' L']
    (eK : K ≃+* K') (eL : L ≃+* L')
    (he :
      RingHom.comp (algebraMap K' L') eK =
        RingHom.comp eL (algebraMap K L)) :
    NormQuotient K L ≃* NormQuotient K' L' where
  toFun := normQuotientMapOfRingEquiv eK eL he
  invFun :=
    normQuotientMapOfRingEquiv eK.symm eL.symm
      (ringEquiv_compat_symm eK eL he)
  left_inv q := by
    refine NormQuotient.inductionOn
      (motive := fun q =>
        normQuotientMapOfRingEquiv eK.symm eL.symm
            (ringEquiv_compat_symm eK eL he)
            (normQuotientMapOfRingEquiv eK eL he q) =
          q)
      q ?_
    intro x
    rw [normQuotientMapOfRingEquiv_normClass,
      normQuotientMapOfRingEquiv_normClass]
    congr 1
    exact (Units.mapEquiv eK.toMulEquiv).symm_apply_apply x
  right_inv q := by
    refine NormQuotient.inductionOn
      (motive := fun q =>
        normQuotientMapOfRingEquiv eK eL he
            (normQuotientMapOfRingEquiv eK.symm eL.symm
              (ringEquiv_compat_symm eK eL he) q) =
          q)
      q ?_
    intro x
    rw [normQuotientMapOfRingEquiv_normClass,
      normQuotientMapOfRingEquiv_normClass]
    congr 1
    exact (Units.mapEquiv eK.toMulEquiv).apply_symm_apply x
  map_mul' := fun x y =>
    map_mul (normQuotientMapOfRingEquiv eK eL he) x y

/-- The algebraic localization used in the local cohomology block is
canonically the whole absolute-value completion, also at an infinite
place. -/
def localizedCompletionNormQuotientEquivAbsoluteCompletions
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
    letI : Algebra v.1.Completion w.1.Completion :=
      AbsoluteValue.completionAlgebra v.1 w.1
        (infinitePlaceAbsoluteValueExtension v w hw).2
    NormQuotient v.1.Completion
        (LocalizedCompletion v.1 u) ≃*
      NormQuotient v.1.Completion w.1.Completion := by
  let u :=
    infinitePlaceAbsoluteValueExtension v w hw
  letI hL :=
    AbsoluteValue.extensionCompletionAlgebra
      (K := K) u.1
  letI : SMul K u.1.Completion := hL.toSMul
  letI : Algebra v.1.Completion u.1.Completion :=
    AbsoluteValue.completionAlgebra v.1 u.1 u.2
  letI : Algebra v.1.Completion w.1.Completion :=
    AbsoluteValue.completionAlgebra v.1 w.1
      (infinitePlaceAbsoluteValueExtension v w hw).2
  let eLAlg :
      LocalizedCompletion v.1 u ≃ₐ[v.1.Completion]
        w.1.Completion :=
    localizedCompletionEquivCompletion
      v.1 v.isNontrivial u
  let eL : LocalizedCompletion v.1 u ≃+* w.1.Completion :=
    eLAlg.toRingEquiv
  exact
    normQuotientEquivOfRingEquiv
      (RingEquiv.refl v.1.Completion) eL
      (by
        ext x
        exact eLAlg.commutes x)

/-- Written using the underlying absolute-value completions, the norm
quotient at a complex place above a real place is again the concrete
quotient for `ℂ/ℝ`. -/
def absoluteCompletionNormQuotientEquivRealComplex
    (v : InfinitePlace K) (w : InfinitePlace L)
    (hw : w.comap (algebraMap K L) = v)
    (hv : v.IsReal) (hwc : w.IsComplex) :
    let u :=
      infinitePlaceAbsoluteValueExtension v w hw
    letI hL :=
      AbsoluteValue.extensionCompletionAlgebra
        (K := K) u.1
    letI : SMul K u.1.Completion := hL.toSMul
    letI : Algebra v.1.Completion u.1.Completion :=
      AbsoluteValue.completionAlgebra v.1 u.1 u.2
    letI : Algebra v.1.Completion w.1.Completion :=
      AbsoluteValue.completionAlgebra v.1 w.1
        (infinitePlaceAbsoluteValueExtension v w hw).2
    NormQuotient v.1.Completion w.1.Completion ≃*
      NormQuotient ℝ ℂ := by
  let u :=
    infinitePlaceAbsoluteValueExtension v w hw
  letI hL :=
    AbsoluteValue.extensionCompletionAlgebra
      (K := K) u.1
  letI : SMul K u.1.Completion := hL.toSMul
  letI : Algebra v.1.Completion u.1.Completion :=
    AbsoluteValue.completionAlgebra v.1 u.1 u.2
  letI : Algebra v.1.Completion w.1.Completion :=
    AbsoluteValue.completionAlgebra v.1 w.1
      (infinitePlaceAbsoluteValueExtension v w hw).2
  letI : w.1.LiesOver v.1 :=
    ⟨congrArg (fun q : InfinitePlace K => q.1) hw⟩
  have hEmbedding :
      w.embedding.comp (algebraMap K L) =
        v.embedding :=
    (InfinitePlace.LiesOver.embedding_liesOver_of_isReal
      w hv).over
  have hCompletionEmbedding :
      ∀ x : v.1.Completion,
        InfinitePlace.Completion.extensionEmbedding w
            ((InfinitePlace.Completion.equiv w).symm
              (AbsoluteValue.completionMap
                v.1 w.1
                (infinitePlaceAbsoluteValueExtension
                  v w hw).2 x)) =
          InfinitePlace.Completion.extensionEmbedding v
            ((InfinitePlace.Completion.equiv v).symm x) := by
    intro x
    refine
      UniformSpace.Completion.induction_on
        (α := WithAbs v.1) x ?_ ?_
    · exact
        isClosed_eq
          ((InfinitePlace.Completion.isometry_extensionEmbedding
              w).continuous.comp
            ((InfinitePlace.Completion.continuous_ofCompletion
              w).comp
              (AbsoluteValue.completionMap_isometry
                v.1 w.1
                (infinitePlaceAbsoluteValueExtension
                  v w hw).2).continuous))
          ((InfinitePlace.Completion.isometry_extensionEmbedding
              v).continuous.comp
            (InfinitePlace.Completion.continuous_ofCompletion v))
    · intro y
      have hy :
          (y : v.1.Completion) =
            algebraMap K v.1.Completion
              (WithAbs.equiv v.1 y) := by
        rw [← AbsoluteValue.toCompletion_eq_algebraMap]
        simp
      have hmap :
          AbsoluteValue.completionMap v.1 w.1
              (infinitePlaceAbsoluteValueExtension v w hw).2
              (y : v.1.Completion) =
            AbsoluteValue.toCompletion w.1
              (algebraMap K L (WithAbs.equiv v.1 y)) :=
        (congrArg
          (AbsoluteValue.completionMap v.1 w.1
            (infinitePlaceAbsoluteValueExtension v w hw).2) hy).trans
          (AbsoluteValue.completionMap_coe v.1 w.1
            (infinitePlaceAbsoluteValueExtension v w hw).2
            (WithAbs.equiv v.1 y))
      have hwEmbedding :
          InfinitePlace.Completion.extensionEmbedding w
              ((InfinitePlace.Completion.equiv w).symm
                (AbsoluteValue.toCompletion w.1
                  (algebraMap K L (WithAbs.equiv v.1 y)))) =
            w.embedding (algebraMap K L (WithAbs.equiv v.1 y)) :=
        (InfinitePlace.Completion.extensionEmbedding_coe w
          ((WithAbs.equiv w.1).symm
            (algebraMap K L (WithAbs.equiv v.1 y)))).trans
          (congrArg w.embedding
            ((WithAbs.equiv w.1).apply_symm_apply
              (algebraMap K L (WithAbs.equiv v.1 y))))
      exact
        (congrArg (fun z : w.1.Completion =>
          InfinitePlace.Completion.extensionEmbedding w
            ((InfinitePlace.Completion.equiv w).symm z)) hmap).trans
          (hwEmbedding.trans
            ((DFunLike.congr_fun hEmbedding (WithAbs.equiv v.1 y)).trans
              (InfinitePlace.Completion.extensionEmbedding_coe v y).symm))
  exact
    normQuotientEquivOfRingEquiv
      (absoluteCompletionRingEquivReal v hv)
      (absoluteCompletionRingEquivComplex w hwc)
      (by
        ext x
        exact
          (InfinitePlace.Completion.extensionEmbeddingOfIsReal_apply hv
            ((InfinitePlace.Completion.equiv v).symm x)).trans
            (hCompletionEmbedding x).symm)

/-- The norms from `ℂˣ` are precisely the positive real units. -/
theorem realUnitsSign_ker_eq_complexNormSubgroup :
    realUnitsSign.ker = localNormSubgroup ℝ ℂ := by
  ext x
  rw [mem_realUnitsSign_ker_iff]
  change 0 < (x : ℝ) ↔
    ∃ u : ℂˣ, normUnits ℝ ℂ u = x
  constructor
  · intro hx
    let z : ℂ :=
      (Real.sqrt (x : ℝ) : ℝ)
    have hz : z ≠ 0 := by
      exact Complex.ofReal_ne_zero.mpr
        (ne_of_gt (Real.sqrt_pos.2 hx))
    let u : ℂˣ := Units.mk0 z hz
    refine ⟨u, ?_⟩
    apply Units.ext
    change Algebra.norm ℝ (u : ℂ) = (x : ℝ)
    rw [Algebra.norm_complex_apply]
    simpa [u, z, Complex.normSq_ofReal] using
      Real.mul_self_sqrt hx.le
  · rintro ⟨u, rfl⟩
    change 0 < Algebra.norm ℝ (u : ℂ)
    rw [Algebra.norm_complex_apply, Complex.normSq_pos]
    exact Units.ne_zero u

/-- The norm quotient for `ℂ/ℝ` is the two-element sign group. -/
def realComplexNormQuotientEquivSign :
    NormQuotient ℝ ℂ ≃* ℤˣ :=
  normQuotientEquivOfSurjective
    realUnitsSign
    realUnitsSign_surjective
    realUnitsSign_ker_eq_complexNormSubgroup

/-- The real/complex norm quotient is finite via its equivalence with
the integral sign group. -/
noncomputable instance realComplexNormQuotientFinite :
    Finite (NormQuotient ℝ ℂ) :=
  Finite.of_equiv ℤˣ
    realComplexNormQuotientEquivSign.symm.toEquiv

/-- The real/complex local norm quotient has order two. -/
theorem realComplexNormQuotient_card_eq_two :
    Nat.card (NormQuotient ℝ ℂ) = 2 := by
  rw [Nat.card_congr realComplexNormQuotientEquivSign.toEquiv,
    Nat.card_eq_fintype_card, Fintype.card_units_int]

omit [NumberField K] [NumberField L] in
/-- Finiteness of the archimedean degree-minus-one local Herbrand
group. -/
theorem infinitePlaceLocalHerbrandHMinusOneFinite
    (v : InfinitePlace K) (w : InfinitePlace L)
    (hw : w.comap (algebraMap K L) = v)
    (σ : L ≃ₐ[K] L)
    (hgen : ∀ τ : L ≃ₐ[K] L,
      τ ∈ Subgroup.zpowers σ) :
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
      (HerbrandHMinusOne
        (absoluteValueDecompositionGroup K w.1)
        (LocalizedCompletion v.1 u)ˣ
        (subgroupGeneratorOfGenerator
          (absoluteValueDecompositionGroup K w.1)
          σ hgen)) := by
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
      (HerbrandHMinusOne
        (absoluteValueDecompositionGroup K w.1)
        (LocalizedCompletion v.1 u)ˣ
        (subgroupGeneratorOfGenerator
          (absoluteValueDecompositionGroup K w.1)
          σ hgen))
  let :
      Subsingleton
        (HerbrandHMinusOne
          (absoluteValueDecompositionGroup K w.1)
          (LocalizedCompletion v.1 u)ˣ
          (subgroupGeneratorOfGenerator
            (absoluteValueDecompositionGroup K w.1)
            σ hgen)) :=
    localHerbrandHMinusOne_subsingleton
      v.1 v.isNontrivial u σ hgen
  exact
    Finite.of_injective
      (fun _ => false)
      (fun x y _ => Subsingleton.elim x y)

end LocalClassFieldTheory
end
end

section
-- module Solutions.OAIQ244_DUKE.AlgebraicNumberTheory_Idele_Cohomology_SPlaces_Herbrand_Local
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalCyclotomicCompletionAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.residueFieldZModAlgebra _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.PrimeDegreePackets.diagonalLogAction _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.LocalClassFieldTheory.normalizationIntegerRingIsIntegralClosure
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

omit [NumberField K] [NumberField L] in
/-- The decomposition-group localization equivalence identifies the order of a decomposition group with
the degree of its localized completion. -/
theorem absoluteValueDecompositionGroup_card_eq_localizedDegree
    (vK : AbsoluteValue K ℝ) (hvK : vK.IsNontrivial)
    (w : AbsoluteValueExtension vK L) :
    letI hK :=
      AbsoluteValue.extensionCompletionAlgebra
        (K := K) w.1
    letI : SMul K w.1.Completion := hK.toSMul
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
    Nat.card (absoluteValueDecompositionGroup K w.1) =
      Module.finrank vK.Completion
        (LocalizedCompletion vK w) := by
  let hK :=
    AbsoluteValue.extensionCompletionAlgebra
      (K := K) w.1
  let : SMul K w.1.Completion := hK.toSMul
  let : Algebra vK.Completion w.1.Completion :=
    AbsoluteValue.completionAlgebra vK w.1 w.2
  let := localizedCompletionGlobalAlgebra vK w
  let := localizedCompletionIsScalarTower vK w
  let : FiniteDimensional vK.Completion
      (LocalizedCompletion vK w) :=
    localizedCompletionModuleFinite vK hvK w
  let : IsGalois vK.Completion
      (LocalizedCompletion vK w) :=
    HilbertRamification.algebraicLocalization_isGalois vK w
  calc
    Nat.card (absoluteValueDecompositionGroup K w.1) =
        Nat.card
          (LocalizedCompletion vK w ≃ₐ[vK.Completion]
            LocalizedCompletion vK w) :=
      Nat.card_congr
        (decompositionGroupEquivAlgebraicLocalizationAut
          vK hvK w).toEquiv
    _ = Module.finrank vK.Completion
        (LocalizedCompletion vK w) :=
      IsGalois.card_aut_eq_finrank
        vK.Completion (LocalizedCompletion vK w)
end
end

section
-- module Solutions.OAIQ244_DUKE.AlgebraicNumberTheory_Ramification_Splitting_NormalClosure
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.residueFieldZModAlgebra _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.LocalClassFieldTheory.normalizationIntegerRingIsIntegralClosure _root_.chosenFinitePlaceCompletionAlgebra _root_.scaledRelativeIntegerLatticeQuotientFinite
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

section SplittingTransport

variable
    {K E E' : Type}
    [Field K]
    [Field E] [Algebra K E]
    [Field E'] [Algebra K E']

variable [FiniteDimensional K E]
    [FiniteDimensional K E']

variable [NumberField K]

omit [FiniteDimensional K E] [FiniteDimensional K E'] in
/-- Finite-place complete splitting is invariant under a
`K`-algebra equivalence. -/
theorem finitePlaceSplitsCompletelyInExtension_algEquiv
    (e : E ≃ₐ[K] E')
    (v : HeightOneSpectrum (𝓞 K)) :
    FinitePlaceSplitsCompletelyInExtension
        (K := K) (E := E) v ↔
      FinitePlaceSplitsCompletelyInExtension
        (K := K) (E := E') v :=
  absoluteValueSplitsCompletelyInExtension_algEquiv
    (NumberField.HeightOneSpectrum.adicAbv K v) e

end SplittingTransport
end
end

section
-- module Solutions.OAIQ244_DUKE.AlgebraicNumberTheory_SUnit_Herbrand
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.DiscreteNthRootsSubgroup.instCommGroupSubtypeUnitsMemSubgroup _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.KummerTheory.finite_sUnit_nthPowerQuotient _root_.KummerTheory.nthRootsSubgroupFintype _root_.KummerTheory.primeCyclotomicBaseFiniteDimensional _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitQuotientCarrier_finite _root_.LocalFieldTheory.DiscreteValuationField.finite_nsmulAddKernel_padicInt_pi _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_multiplicative_nthPowerKernel _root_.LocalFieldTheory.finite_nsmulAddKernel_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.LubinTate.compatibleGroupFamiliesCommGroup _root_.LubinTate.compatibleGroupFamiliesGroup _root_.OAI.PrimeDegreePackets.ThetaConstruction.coordinateLattice_discrete _root_.OAI.PrimeDegreePackets.boundedRealFields_finite _root_.OAI.PrimeDegreePackets.diagonalLogAction _root_.OAI.PrimeDegreePackets.instNonemptyLeafTestSpace _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.integralGroup_discrete _root_.OAI.PrimeDegreePackets.logSubgroup_discrete _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.OAI.PrimeDegreePackets.orderedLogSubgroup_discrete _root_.CyclicCohomology.binaryCoefficientFamilyCommGroup _root_.LocalClassFieldTheory.normalizationIntegerRingIsIntegralClosure _root_.chosenFinitePlaceCompletionFiniteDimensional _root_.chosenFinitePlaceLocalizedFiniteDimensional
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

/-!
# The Herbrand quotient of the global S-unit group

This file computes the Herbrand quotient of the global `S`-unit group. It connects the actual
`S`-unit group to its logarithmic lattice, adds the invariant diagonal
integer direction, and combines the resulting exact sequences with the
permutation-lattice calculation.
-/

open scoped BigOperators Classical NumberField nonZeroDivisors Pointwise
open IsDedekindDomain Module

noncomputable section

open CyclicCohomology.ProfiniteCohomology.Herbrand
open CyclicCohomology

variable
    (K L : Type*) [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]

section LogLatticeHerbrand

/-- For the genuine sum-zero logarithmic lattice, adjoining
the invariant diagonal multiplies the Herbrand quotient by `|G|`. -/
theorem fullLogLattice_herbrandQuotient_eq_stabilizerProduct_div_card
    (K L : Type)
    [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    {S : Finset (HeightOneSpectrum (𝓞 L))}
    (hS : IsGaloisStableFinitePlaces K L S)
    (σ : L ≃ₐ[K] L)
    (hgen : ∀ τ : L ≃ₐ[K] L,
      τ ∈ Subgroup.zpowers σ) :
    let ρ :=
      logPlacePermutationHom K L S hS
    letI _indexAction :
        MulAction (L ≃ₐ[K] L)
          (SUnitGroup.LogPlace (K := L) S) :=
      permutationMulAction ρ
    letI _latticeAction :
        DistribMulAction (L ≃ₐ[K] L)
          (SUnitGroup.fullLogLattice (K := L) S) :=
      fullLogLatticeDistribMulAction K L S hS
    letI _latticeMultiplicativeAction :
        MulDistribMulAction (L ≃ₐ[K] L)
          (Multiplicative
            (SUnitGroup.fullLogLattice (K := L) S)) :=
      multiplicativeDistribMulAction
    letI _orbitFintype :
        Fintype
          (MulAction.orbitRel.Quotient
            (L ≃ₐ[K] L)
            (SUnitGroup.LogPlace (K := L) S)) :=
      Fintype.ofFinite _
    letI _stabilizerFintype :
        ∀ ω :
            MulAction.orbitRel.Quotient
              (L ≃ₐ[K] L)
              (SUnitGroup.LogPlace (K := L) S),
          Fintype (permutationOrbitStabilizer ω) :=
      fun _ => Fintype.ofFinite _
    ∃ h :
        HerbrandQuotientDefined
          (L ≃ₐ[K] L)
          (Multiplicative
            (SUnitGroup.fullLogLattice (K := L) S)) σ,
      @herbrandQuotient
          (L ≃ₐ[K] L)
          (Multiplicative
            (SUnitGroup.fullLogLattice (K := L) S))
          _ _ _ _ σ h.1 h.2 =
        (∏ ω :
            MulAction.orbitRel.Quotient
              (L ≃ₐ[K] L)
              (SUnitGroup.LogPlace (K := L) S),
          (Fintype.card
            (permutationOrbitStabilizer ω) : ℚ)) /
          (Fintype.card (L ≃ₐ[K] L) : ℚ) := by
  dsimp only
  let ρ :=
    logPlacePermutationHom K L S hS
  let indexAction :
      MulAction (L ≃ₐ[K] L)
        (SUnitGroup.LogPlace (K := L) S) :=
    permutationMulAction ρ
  let latticeAction :
      DistribMulAction (L ≃ₐ[K] L)
        (SUnitGroup.fullLogLattice (K := L) S) :=
    fullLogLatticeDistribMulAction K L S hS
  let latticeMultiplicativeAction :
      MulDistribMulAction (L ≃ₐ[K] L)
        (Multiplicative
          (SUnitGroup.fullLogLattice (K := L) S)) :=
    multiplicativeDistribMulAction
  let productAction :
      DistribMulAction (L ≃ₐ[K] L)
        (SUnitGroup.fullLogLattice (K := L) S × ℤ) :=
    fullLogLatticeProdIntDistribMulAction K L S hS
  let productMultiplicativeAction :
      MulDistribMulAction (L ≃ₐ[K] L)
        (Multiplicative
          (SUnitGroup.fullLogLattice (K := L) S × ℤ)) :=
    multiplicativeDistribMulAction
  let integerAction :
      MulDistribMulAction (L ≃ₐ[K] L)
        (Multiplicative ℤ) :=
    trivialIntMulDistribMulAction (L ≃ₐ[K] L)
  let extendedAction :
      DistribMulAction (L ≃ₐ[K] L)
        (extendedFullLogLattice L S) :=
    completePermutationLatticeDistribMulAction
      ρ (extendedFullLogLattice L S)
      (extendedFullLogLattice_permutation_stable
        K L hS)
  let extendedMultiplicativeAction :
      MulDistribMulAction (L ≃ₐ[K] L)
        (Multiplicative
          (extendedFullLogLattice L S)) :=
    multiplicativeDistribMulAction
  let orbitFintype :
      Fintype
        (MulAction.orbitRel.Quotient
          (L ≃ₐ[K] L)
          (SUnitGroup.LogPlace (K := L) S)) :=
    Fintype.ofFinite _
  let stabilizerFintype :
      ∀ ω :
          MulAction.orbitRel.Quotient
            (L ≃ₐ[K] L)
            (SUnitGroup.LogPlace (K := L) S),
        Fintype (permutationOrbitStabilizer ω) :=
    fun _ => Fintype.ofFinite _
  obtain ⟨hExtended, hExtendedValue⟩ :=
    extendedFullLogLattice_herbrandQuotient_eq_stabilizerProduct
      K L hS σ hgen
  let extendedH0Finite :
      Finite
        (HerbrandH0
          (L ≃ₐ[K] L)
          (Multiplicative
            (extendedFullLogLattice L S))) :=
    hExtended.1
  let extendedHMinusOneFinite :
      Finite
        (HerbrandHMinusOne
          (L ≃ₐ[K] L)
          (Multiplicative
            (extendedFullLogLattice L S)) σ) :=
    hExtended.2
  let e :=
    extendedFullLogLatticeMulEquivProdInt L S
  have he :
      ∀ (τ : L ≃ₐ[K] L)
        (x : Multiplicative (extendedFullLogLattice L S)),
        e (τ • x) = τ • e x :=
    extendedFullLogLatticeMulEquivProdInt_equivariant
      K L hS
  let hProduct :
      HerbrandQuotientDefined
        (L ≃ₐ[K] L)
        (Multiplicative
          (SUnitGroup.fullLogLattice (K := L) S × ℤ)) σ :=
    ⟨herbrandH0Finite_of_equivariantMulEquiv e he,
      herbrandHMinusOneFinite_of_equivariantMulEquiv
        e he σ⟩
  let productH0Finite :
      Finite
        (HerbrandH0
          (L ≃ₐ[K] L)
          (Multiplicative
            (SUnitGroup.fullLogLattice (K := L) S × ℤ))) :=
    hProduct.1
  let productHMinusOneFinite :
      Finite
        (HerbrandHMinusOne
          (L ≃ₐ[K] L)
          (Multiplicative
            (SUnitGroup.fullLogLattice (K := L) S × ℤ)) σ) :=
    hProduct.2
  let hInteger :
      HerbrandQuotientDefined
        (L ≃ₐ[K] L) (Multiplicative ℤ) σ :=
    ⟨trivialIntHerbrandH0Finite,
      trivialIntHerbrandHMinusOneFinite σ⟩
  let integerH0Finite :
      Finite
        (HerbrandH0
          (L ≃ₐ[K] L) (Multiplicative ℤ)) :=
    hInteger.1
  let integerHMinusOneFinite :
      Finite
        (HerbrandHMinusOne
          (L ≃ₐ[K] L) (Multiplicative ℤ) σ) :=
    hInteger.2
  let hLattice :=
    herbrandQuotientDefined_left_of_middle_right
      (fullLogLatticeProdIntIncl L S)
      (fullLogLatticeProdIntProj L S)
      (fullLogLatticeProdIntIncl_equivariant K L hS)
      (fullLogLatticeProdIntProj_equivariant K L hS)
      (fullLogLatticeProdInt_exact L S)
      (fullLogLatticeProdIntIncl_injective L S)
      (fullLogLatticeProdIntProj_surjective L S)
      σ hgen hProduct hInteger
  let latticeH0Finite :
      Finite
        (HerbrandH0
          (L ≃ₐ[K] L)
          (Multiplicative
            (SUnitGroup.fullLogLattice (K := L) S))) :=
    hLattice.1
  let latticeHMinusOneFinite :
      Finite
        (HerbrandHMinusOne
          (L ≃ₐ[K] L)
          (Multiplicative
            (SUnitGroup.fullLogLattice (K := L) S)) σ) :=
    hLattice.2
  have hMultiplicative :
      herbrandQuotient
          (G := L ≃ₐ[K] L)
          (A := Multiplicative
            (SUnitGroup.fullLogLattice (K := L) S × ℤ)) σ =
        herbrandQuotient
            (G := L ≃ₐ[K] L)
            (A := Multiplicative
              (SUnitGroup.fullLogLattice (K := L) S)) σ *
          herbrandQuotient
            (G := L ≃ₐ[K] L)
            (A := Multiplicative ℤ) σ :=
    herbrandQuotient_multiplicative_of_shortExact
      (fullLogLatticeProdIntIncl L S)
      (fullLogLatticeProdIntProj L S)
      (fullLogLatticeProdIntIncl_equivariant K L hS)
      (fullLogLatticeProdIntProj_equivariant K L hS)
      (fullLogLatticeProdInt_exact L S)
      (fullLogLatticeProdIntIncl_injective L S)
      (fullLogLatticeProdIntProj_surjective L S)
      σ hgen
  have hIntegerValue :
      herbrandQuotient
          (G := L ≃ₐ[K] L)
          (A := Multiplicative ℤ) σ =
        (Fintype.card (L ≃ₐ[K] L) : ℚ) :=
    trivialInt_herbrandQuotient_eq_card σ
  have hExtendedProduct :
      herbrandQuotient
          (G := L ≃ₐ[K] L)
          (A := Multiplicative
            (extendedFullLogLattice L S)) σ =
        herbrandQuotient
          (G := L ≃ₐ[K] L)
          (A := Multiplicative
            (SUnitGroup.fullLogLattice (K := L) S × ℤ)) σ := by
    exact
      herbrandQuotient_eq_of_equivariantMulEquiv
        e he σ
  refine ⟨hLattice, ?_⟩
  have hcard :
      (Fintype.card (L ≃ₐ[K] L) : ℚ) ≠ 0 := by
    exact_mod_cast
      (Fintype.card_ne_zero :
        Fintype.card (L ≃ₐ[K] L) ≠ 0)
  rw [eq_div_iff hcard]
  calc
    @herbrandQuotient
          (L ≃ₐ[K] L)
          (Multiplicative
            (SUnitGroup.fullLogLattice (K := L) S))
          _ _ _ _ σ hLattice.1 hLattice.2 *
        (Fintype.card (L ≃ₐ[K] L) : ℚ) =
        @herbrandQuotient
          (L ≃ₐ[K] L)
          (Multiplicative
            (SUnitGroup.fullLogLattice (K := L) S × ℤ))
          _ _ _ _ σ hProduct.1 hProduct.2 := by
      rw [← hIntegerValue]
      exact hMultiplicative.symm
    _ =
        @herbrandQuotient
          (L ≃ₐ[K] L)
          (Multiplicative
            (extendedFullLogLattice L S))
          _ _ _ _ σ hExtended.1 hExtended.2 :=
      hExtendedProduct.symm
    _ =
        ∏ ω :
            MulAction.orbitRel.Quotient
              (L ≃ₐ[K] L)
              (SUnitGroup.LogPlace (K := L) S),
          (Fintype.card
            (permutationOrbitStabilizer ω) : ℚ) :=
      hExtendedValue

end LogLatticeHerbrand

section ActualSUnitHerbrand

/-- For the actual `S`-unit group, the finite
roots-of-unity kernel has Herbrand quotient one, so the logarithmic
lattice formula transfers unchanged. -/
theorem sUnit_herbrandQuotient_eq_stabilizerProduct_div_card
    (K L : Type)
    [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    {S : Finset (HeightOneSpectrum (𝓞 L))}
    (hS : IsGaloisStableFinitePlaces K L S)
    (σ : L ≃ₐ[K] L)
    (hgen : ∀ τ : L ≃ₐ[K] L,
      τ ∈ Subgroup.zpowers σ) :
    let ρ :=
      logPlacePermutationHom K L S hS
    letI _indexAction :
        MulAction (L ≃ₐ[K] L)
          (SUnitGroup.LogPlace (K := L) S) :=
      permutationMulAction ρ
    letI _sUnitAction :
        MulDistribMulAction (L ≃ₐ[K] L)
          (SUnitGroup (K := L) S) :=
      sUnitMulDistribMulAction K L S hS
    letI _orbitFintype :
        Fintype
          (MulAction.orbitRel.Quotient
            (L ≃ₐ[K] L)
            (SUnitGroup.LogPlace (K := L) S)) :=
      Fintype.ofFinite _
    letI _stabilizerFintype :
        ∀ ω :
            MulAction.orbitRel.Quotient
              (L ≃ₐ[K] L)
              (SUnitGroup.LogPlace (K := L) S),
          Fintype (permutationOrbitStabilizer ω) :=
      fun _ => Fintype.ofFinite _
    ∃ h :
        HerbrandQuotientDefined
          (L ≃ₐ[K] L)
          (SUnitGroup (K := L) S) σ,
      @herbrandQuotient
          (L ≃ₐ[K] L)
          (SUnitGroup (K := L) S)
          _ _ _ _ σ h.1 h.2 =
        (∏ ω :
            MulAction.orbitRel.Quotient
              (L ≃ₐ[K] L)
              (SUnitGroup.LogPlace (K := L) S),
          (Fintype.card
            (permutationOrbitStabilizer ω) : ℚ)) /
          (Fintype.card (L ≃ₐ[K] L) : ℚ) := by
  dsimp only
  let ρ :=
    logPlacePermutationHom K L S hS
  let indexAction :
      MulAction (L ≃ₐ[K] L)
        (SUnitGroup.LogPlace (K := L) S) :=
    permutationMulAction ρ
  let sUnitAction :
      MulDistribMulAction (L ≃ₐ[K] L)
        (SUnitGroup (K := L) S) :=
    sUnitMulDistribMulAction K L S hS
  let latticeAction :
      DistribMulAction (L ≃ₐ[K] L)
        (SUnitGroup.fullLogLattice (K := L) S) :=
    fullLogLatticeDistribMulAction K L S hS
  let latticeMultiplicativeAction :
      MulDistribMulAction (L ≃ₐ[K] L)
        (Multiplicative
          (SUnitGroup.fullLogLattice (K := L) S)) :=
    multiplicativeDistribMulAction
  let orbitFintype :
      Fintype
        (MulAction.orbitRel.Quotient
          (L ≃ₐ[K] L)
          (SUnitGroup.LogPlace (K := L) S)) :=
    Fintype.ofFinite _
  let stabilizerFintype :
      ∀ ω :
          MulAction.orbitRel.Quotient
            (L ≃ₐ[K] L)
            (SUnitGroup.LogPlace (K := L) S),
        Fintype (permutationOrbitStabilizer ω) :=
    fun _ => Fintype.ofFinite _
  let torsionAction :
      MulDistribMulAction (L ≃ₐ[K] L)
        (CommGroup.torsion
          (SUnitGroup (K := L) S)) :=
    stableSubgroupMulDistribMulAction
      (CommGroup.torsion
        (SUnitGroup (K := L) S))
      (sUnitTorsion_stable K L hS)
  let torsionFinite :
      Finite
        (CommGroup.torsion
          (SUnitGroup (K := L) S)) :=
    sUnitTorsionFinite L S
  obtain ⟨hLattice, hLatticeValue⟩ :=
    fullLogLattice_herbrandQuotient_eq_stabilizerProduct_div_card
      K L hS σ hgen
  let latticeH0Finite :
      Finite
        (HerbrandH0
          (L ≃ₐ[K] L)
          (Multiplicative
            (SUnitGroup.fullLogLattice (K := L) S))) :=
    hLattice.1
  let latticeHMinusOneFinite :
      Finite
        (HerbrandHMinusOne
          (L ≃ₐ[K] L)
          (Multiplicative
            (SUnitGroup.fullLogLattice (K := L) S)) σ) :=
    hLattice.2
  let hTorsion :
      HerbrandQuotientDefined
        (L ≃ₐ[K] L)
        (CommGroup.torsion
          (SUnitGroup (K := L) S)) σ :=
    ⟨inferInstance, inferInstance⟩
  let torsionH0Finite :
      Finite
        (HerbrandH0
          (L ≃ₐ[K] L)
          (CommGroup.torsion
            (SUnitGroup (K := L) S))) :=
    hTorsion.1
  let torsionHMinusOneFinite :
      Finite
        (HerbrandHMinusOne
          (L ≃ₐ[K] L)
          (CommGroup.torsion
            (SUnitGroup (K := L) S)) σ) :=
    hTorsion.2
  let hSUnit :=
    herbrandQuotientDefined_middle_of_left_right
      (CommGroup.torsion
        (SUnitGroup (K := L) S)).subtype
      (sUnitFullLogMulHom L S)
      (stableSubgroup_subtype_equivariant
        (CommGroup.torsion
          (SUnitGroup (K := L) S))
        (sUnitTorsion_stable K L hS))
      (sUnitFullLogMulHom_equivariant K L hS)
      (sUnitTorsion_fullLog_exact L S)
      (CommGroup.torsion
        (SUnitGroup (K := L) S)).subtype_injective
      (sUnitFullLogMulHom_surjective L S)
      σ hgen hTorsion hLattice
  let sUnitH0Finite :
      Finite
        (HerbrandH0
          (L ≃ₐ[K] L)
          (SUnitGroup (K := L) S)) :=
    hSUnit.1
  let sUnitHMinusOneFinite :
      Finite
        (HerbrandHMinusOne
          (L ≃ₐ[K] L)
          (SUnitGroup (K := L) S) σ) :=
    hSUnit.2
  have hMultiplicative :
      herbrandQuotient
          (G := L ≃ₐ[K] L)
          (A := SUnitGroup (K := L) S) σ =
        herbrandQuotient
            (G := L ≃ₐ[K] L)
            (A := CommGroup.torsion
              (SUnitGroup (K := L) S)) σ *
          herbrandQuotient
            (G := L ≃ₐ[K] L)
            (A := Multiplicative
              (SUnitGroup.fullLogLattice (K := L) S)) σ :=
    herbrandQuotient_multiplicative_of_shortExact
      (CommGroup.torsion
        (SUnitGroup (K := L) S)).subtype
      (sUnitFullLogMulHom L S)
      (stableSubgroup_subtype_equivariant
        (CommGroup.torsion
          (SUnitGroup (K := L) S))
        (sUnitTorsion_stable K L hS))
      (sUnitFullLogMulHom_equivariant K L hS)
      (sUnitTorsion_fullLog_exact L S)
      (CommGroup.torsion
        (SUnitGroup (K := L) S)).subtype_injective
      (sUnitFullLogMulHom_surjective L S)
      σ hgen
  have hTorsionValue :
      herbrandQuotient
          (G := L ≃ₐ[K] L)
          (A := CommGroup.torsion
            (SUnitGroup (K := L) S)) σ = 1 :=
    herbrandQuotient_eq_one_of_finite_module
      σ hgen
  refine ⟨hSUnit, ?_⟩
  calc
    @herbrandQuotient
          (L ≃ₐ[K] L)
          (SUnitGroup (K := L) S)
          _ _ _ _ σ hSUnit.1 hSUnit.2 =
        @herbrandQuotient
            (L ≃ₐ[K] L)
            (CommGroup.torsion
              (SUnitGroup (K := L) S))
            _ _ _ _ σ hTorsion.1 hTorsion.2 *
          @herbrandQuotient
            (L ≃ₐ[K] L)
            (Multiplicative
              (SUnitGroup.fullLogLattice (K := L) S))
            _ _ _ _ σ hLattice.1 hLattice.2 :=
      hMultiplicative
    _ =
        @herbrandQuotient
          (L ≃ₐ[K] L)
          (Multiplicative
            (SUnitGroup.fullLogLattice (K := L) S))
          _ _ _ _ σ hLattice.1 hLattice.2 := by
      rw [hTorsionValue, one_mul]
    _ =
        (∏ ω :
            MulAction.orbitRel.Quotient
              (L ≃ₐ[K] L)
              (SUnitGroup.LogPlace (K := L) S),
          (Fintype.card
            (permutationOrbitStabilizer ω) : ℚ)) /
          (Fintype.card (L ≃ₐ[K] L) : ℚ) :=
      hLatticeValue

end ActualSUnitHerbrand

section LocalDegreeInterpretation

/-- The Herbrand quotient in local-degree form:
`h(G, L^S) = |G|⁻¹ ∏_{p ∈ S} [L_P : K_p]`, with the
archimedean places included in the logarithmic place set. -/
theorem sUnit_herbrandQuotient_eq_localDegreeProduct_div_card
    (K L : Type)
    [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    [IsGalois K L]
    {S : Finset (HeightOneSpectrum (𝓞 L))}
    (hS : IsGaloisStableFinitePlaces K L S)
    (σ : L ≃ₐ[K] L)
    (hgen : ∀ τ : L ≃ₐ[K] L,
      τ ∈ Subgroup.zpowers σ) :
    let ρ :=
      logPlacePermutationHom K L S hS
    letI _indexAction :
        MulAction (L ≃ₐ[K] L)
          (SUnitGroup.LogPlace (K := L) S) :=
      permutationMulAction ρ
    letI _sUnitAction :
        MulDistribMulAction (L ≃ₐ[K] L)
          (SUnitGroup (K := L) S) :=
      sUnitMulDistribMulAction K L S hS
    letI _orbitFintype :
        Fintype
          (MulAction.orbitRel.Quotient
            (L ≃ₐ[K] L)
            (SUnitGroup.LogPlace (K := L) S)) :=
      Fintype.ofFinite _
    letI _stabilizerFintype :
        ∀ ω :
            MulAction.orbitRel.Quotient
              (L ≃ₐ[K] L)
              (SUnitGroup.LogPlace (K := L) S),
          Fintype (permutationOrbitStabilizer ω) :=
      fun _ => Fintype.ofFinite _
    ∃ h :
        HerbrandQuotientDefined
          (L ≃ₐ[K] L)
          (SUnitGroup (K := L) S) σ,
      @herbrandQuotient
          (L ≃ₐ[K] L)
          (SUnitGroup (K := L) S)
          _ _ _ _ σ h.1 h.2 =
        (∏ ω :
            MulAction.orbitRel.Quotient
              (L ≃ₐ[K] L)
              (SUnitGroup.LogPlace (K := L) S),
          (logPlaceLocalDegree K L S ω.out : ℚ)) /
          (Fintype.card (L ≃ₐ[K] L) : ℚ) := by
  dsimp only
  let ρ :=
    logPlacePermutationHom K L S hS
  let indexAction :
      MulAction (L ≃ₐ[K] L)
        (SUnitGroup.LogPlace (K := L) S) :=
    permutationMulAction ρ
  let sUnitAction :
      MulDistribMulAction (L ≃ₐ[K] L)
        (SUnitGroup (K := L) S) :=
    sUnitMulDistribMulAction K L S hS
  let orbitFintype :
      Fintype
        (MulAction.orbitRel.Quotient
          (L ≃ₐ[K] L)
          (SUnitGroup.LogPlace (K := L) S)) :=
    Fintype.ofFinite _
  let stabilizerFintype :
      ∀ ω :
          MulAction.orbitRel.Quotient
            (L ≃ₐ[K] L)
            (SUnitGroup.LogPlace (K := L) S),
        Fintype (permutationOrbitStabilizer ω) :=
    fun _ => Fintype.ofFinite _
  obtain ⟨hSUnit, hSUnitValue⟩ :=
    sUnit_herbrandQuotient_eq_stabilizerProduct_div_card
      K L hS σ hgen
  refine ⟨hSUnit, ?_⟩
  calc
    @herbrandQuotient
          (L ≃ₐ[K] L)
          (SUnitGroup (K := L) S)
          _ _ _ _ σ hSUnit.1 hSUnit.2 =
        (∏ ω :
            MulAction.orbitRel.Quotient
              (L ≃ₐ[K] L)
              (SUnitGroup.LogPlace (K := L) S),
          (Fintype.card
            (permutationOrbitStabilizer ω) : ℚ)) /
          (Fintype.card (L ≃ₐ[K] L) : ℚ) :=
      hSUnitValue
    _ =
        (∏ ω :
            MulAction.orbitRel.Quotient
              (L ≃ₐ[K] L)
              (SUnitGroup.LogPlace (K := L) S),
          (logPlaceLocalDegree K L S ω.out : ℚ)) /
          (Fintype.card (L ≃ₐ[K] L) : ℚ) := by
      congr 1
      apply Finset.prod_congr rfl
      intro ω _
      norm_cast
      rw [← Nat.card_eq_fintype_card]
      exact
        permutationOrbitStabilizer_card_eq_logPlaceLocalDegree
          K L hS ω

end LocalDegreeInterpretation
end
end

section
-- module Solutions.OAIQ244_DUKE.GlobalClassFieldTheory_ClassFieldAxiom_SUnitKummerPrimeSelection_FinitePlaceDecomposition
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalCyclotomicCompletionAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.DiscreteNthRootsSubgroup.instTopologicalSpaceSubtypeUnitsMemSubgroup _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.KummerTheory.primeCyclotomicBaseFiniteDimensional _root_.KummerTheory.primeCyclotomicBaseIsGalois _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.residueFieldZModAlgebra _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.LubinTate.compatibleGroupFamiliesGroup _root_.OAI.PrimeDegreePackets.diagonalLogAction _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.LocalClassFieldTheory.normalizationIntegerRingIsIntegralClosure _root_.cyclicPrimeDegreeIntermediate_isGalois
attribute [-simp] _root_.GlobalClassFieldTheory.Reciprocity.rationalCyclotomicGlobalToLocalizedAlgHom_apply _root_.GlobalClassFieldTheory.Reciprocity.rationalCyclotomicGlobalToLocalizedAlgHom_primitiveRoot _root_.IsDiscreteValuationRing.addVal_ringEquiv _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.OAI.PrimeDegreePackets.ThetaConstruction.schwartzCM_apply _root_.doubleCosetExtension_mk _root_.extendAbsoluteValueExtensionFromIntermediate_apply _root_.finitePlaceCompletionRingEquiv_toCompletion _root_.finitePlaceIdealResidueEquivCompletion_apply_mk _root_.finitePlaceIntegerToCompletion_coe
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

/-- An unramified chosen finite-place decomposition group is cyclic. -/
theorem finitePlaceDecompositionGroup_isCyclic_of_chosenUnramified
    {F L : Type}
    [Field F] [NumberField F]
    [Field L] [NumberField L] [Algebra F L]
    [FiniteDimensional F L] [IsGalois F L]
    (v : HeightOneSpectrum (𝓞 F))
    (hunram :
      _root_.ChosenFinitePlaceIsUnramified
        (K := F) (L := L) v) :
    IsCyclic
      (_root_.finitePlaceDecompositionGroup
        (K := F) (L := L) v) := by
  let Fv :=
    _root_.ChosenFinitePlaceBaseCompletion
      (K := F) v
  let Lv :=
    _root_.ChosenFinitePlaceLocalizedCompletion
      (K := F) (L := L) v
  let :
      LocalFieldTheory.IsNonarchimedeanLocalField.IsUnramifiedValuedExtension
        Fv Lv := by
    simpa [Fv, Lv, _root_.ChosenFinitePlaceIsUnramified] using hunram
  let eLocal :
      _root_.finitePlaceDecompositionGroup
          (K := F) (L := L) v ≃*
        (Lv ≃ₐ[Fv] Lv) :=
    HilbertRamification.decompositionGroupEquivAlgebraicLocalizationAut
        (HeightOneSpectrum.adicAbv F v)
        (RayClass.adicAbv_isNontrivial v)
        (_root_.chosenFinitePlaceExtension
          (L := L) v)
  exact
    eLocal.isCyclic.mpr
      (LocalFieldTheory.isCyclic_galoisGroup_of_unramifiedValuation
        Fv Lv)

end GlobalClassFieldTheory.ClassFieldAxiom
end
end

section
-- module Solutions.OAIQ244_DUKE.KummerTheory_Concrete_SUnitPreparation_SUnitLocalPowerKernel
attribute [-instance] _root_.ClassFormation.DegreeData.FrobeniusFixedFieldTower.extensionNormal _root_.ClassFormation.DegreeData.GaloisSubextension.extensionSubgroup_normalInstance _root_.ClassFormation.FiniteAbstractField.toFiniteResidueAbstractField_extensionNormal _root_.ClassFormation.FiniteCyclicSubextension.instNormalSubtypeMemSubgroupFieldExtensionSubgroupField _root_.ClassFormation.FiniteGaloisSubextension.extensionSubgroup_normalInstance _root_.ClassFormation.FiniteGaloisSubextension.extensionSubgroup_over_intermediate_normalInstance _root_.ClassFormation.FiniteGaloisSubextension.intermediateField_normalInstance _root_.ClassFormation.FiniteIntermediateField.galoisRefinement_normal _root_.ClassFormation.FiniteUnramifiedCyclicExtension.instNormalSubtypeMemSubgroupFieldExtensionSubgroupField _root_.ClassFormation.conjugateExtension_normal _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalClassFieldTheory.extensionSubgroupBase_normal _root_.LocalClassFieldTheory.finiteGaloisExtensionSubgroupOfEmbedding_normal _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.residueFieldZModAlgebra _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LubinTate.compatibleGroupFamiliesGroup _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionResidueField.instField _root_.RamificationTheory.HilbertRamification.ValuationSubring.inertiaGroup_normal _root_.RamificationTheory.HilbertRamification.ValuationSubring.ramificationGroupInInertiaAut_normal _root_.RamificationTheory.HilbertRamification.ValuationSubring.selectedResidueField.instAlgebra _root_.ValuationTheory.DiscreteValuationField.DVF.residueField.field _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.CyclicCohomology.binaryCoefficientFamilyCommGroup _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.LocalClassFieldTheory.normalizationIntegerRingIsIntegralClosure _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.chosenFinitePlaceCompletionAlgebra
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

/-- The diagonal localization map
`Kˢ → ∏ v ∈ T, K_vˣ / K_vˣⁿ`. -/
noncomputable def sUnitLocalPowerMap
    (n : ℕ+)
    (S T : Finset (HeightOneSpectrum (𝓞 K))) :
    SUnitGroup (K := K) S →*
      ∀ v : T,
        ((v : HeightOneSpectrum (𝓞 K)).adicCompletion K)ˣ ⧸
          (powMonoidHom (n : ℕ) :
            ((v : HeightOneSpectrum (𝓞 K)).adicCompletion K)ˣ →*
              ((v : HeightOneSpectrum (𝓞 K)).adicCompletion K)ˣ).range :=
  (IdeleGroup.principalLocalQuotientMap
      (K := K) T
      (fun v =>
        (powMonoidHom (n : ℕ) :
          (v.1.adicCompletion K)ˣ →*
            (v.1.adicCompletion K)ˣ).range)).comp
    (SUnitGroup (K := K) S).subtype

/-- The subgroup `Δ` of `S`-units which are local `n`-th powers at every
place in `T`. -/
def sUnitLocalPowerKernel
    (n : ℕ+)
    (S T : Finset (HeightOneSpectrum (𝓞 K))) :
    Subgroup (SUnitGroup (K := K) S) :=
  MonoidHom.ker (sUnitLocalPowerMap (K := K) n S T)

end KummerTheory
end
end

section
-- module Solutions.OAIQ244_DUKE.LubinTate_FormalModule_StandardFormalGroup
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.LocalClassFieldTheory.normalizationIntegerRingIsIntegralClosure _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen
attribute [-simp] _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.IsDiscreteValuationRing.addVal_ringEquiv _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.LocalFieldTheory.residueField_algebraMap_residue _root_.OAI.PrimeDegreePackets.ThetaConstruction.schwartzCM_apply _root_.infinitePlace_mult_smul
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

section LinearTerms

variable {R : Type*} [CommRing R]
variable {σ : Type w} [Fintype σ]
variable {τ : Type w'} [Fintype τ]

/-- Zero has zero linear term. -/
theorem hasLinearTerm_zero :
    HasLinearTerm (0 : MvPowerSeries σ R) (fun _ => 0) := by
  simp [HasLinearTerm, linearForm]

end LinearTerms

end SameUniformizer
end LubinTate

end
end


