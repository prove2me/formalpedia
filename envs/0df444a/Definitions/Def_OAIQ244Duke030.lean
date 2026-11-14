-- Prove2me | Definitions.Def_OAIQ244Duke030
-- name    : OAIQ244Duke030
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-13T06:32:28.614143+00:00
-- url     : https://prove2.me/theorems/8b433043-5fca-46ed-bfb8-bd6b39b90d4d
-- title:
--   Definitions bundle OAIQ244Duke030 of the split of OpenAI, Equidistribution of Prime-Degree Torus Packets with Arbitrary Local Type
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.DukePrimeDegree.prime_degree_packet_measure_equidistribution_unconditional` and `OAI.DukePrimeDegree.prime_degree_packet_measures_tendsto_haar_unconditional`, carved from OpenAI's openai/math development (OpenAI, *Equidistribution of Prime-Degree Torus Packets with Arbitrary Local Type*, OpenAI Math Release, September 24, 2026, result family 15, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 129 declarations of OpenAI's Lean: 27 definitions and 102 theorems. The definitions and types are `IdeleSPlaceFactors`, `LocalClassFieldTheory.chosenNormalBasisCoordinateQuotPiLinearEquiv`, `LocalClassFieldTheory.chosenNormalBasisIntegerLatticeBasis`, `LocalClassFieldTheory.chosenNormalBasisIntegerLatticeMulPowLinearEquiv`, `LocalClassFieldTheory.chosenNormalBasisIntegerLatticeMulPowLinearMap`, `LocalClassFieldTheory.chosenNormalBasisIntegerLatticeQuotCoordinateQuotLinearEquiv`, `LocalClassFieldTheory.chosenNormalBasisIntegerLatticeUniformizerSubmodule`, `LocalClassFieldTheory.chosenNormalBasisLatticeSuccQuotRightRegularAddEquiv`, `LocalClassFieldTheory.chosenNormalBasisLatticeSuccQuotToIntegerLatticeQuotLinearEquiv`, `LocalClassFieldTheory.chosenNormalBasisPiResidueInverseIndexAddEquiv`, `LocalClassFieldTheory.chosenNormalBasisPrincipalUnitSequenceAsPrincipalUnits`, `LocalClassFieldTheory.chosenNormalBasisPrincipalUnitSuccQuotMulDistribMulAction`, `LocalClassFieldTheory.chosenNormalBasisPrincipalUnitSuccQuotMulEquivLatticeSuccQuot`, `LocalClassFieldTheory.galoisGroupChosenNormalBasisIntegerLatticeLinearEquiv`, `LocalClassFieldTheory.galoisGroupChosenNormalBasisIntegerLatticeQuotLinearEquiv`, `LocalClassFieldTheory.galoisGroupChosenNormalBasisLatticeSuccQuotAddEquiv`, `LocalClassFieldTheory.galoisGroupChosenNormalBasisLatticeSuccQuotDistribMulAction`, `LocalClassFieldTheory.herbrandH0EquivTateCohomologyZero`, `LocalClassFieldTheory.herbrandH0MulEquivInvariantsNormQuotient`, `LocalFieldTheory.Padic.padicPrimeInteger`, `RelativeIdeleGroup.Cohomology.IdeleClassNormQuotient`, `ValuationTheory.DiscreteValuationField.ValuedExtension.CanonicalIntegralClosure.maximalIdeal`, `ValuationTheory.DiscreteValuationField.ValuedExtension.IsDefectless`, `finiteIdeleOfSPlaceFactors`, `finiteSupportedAtEquivSPlaceFactors`, `ideleSupportedAtEquivInfiniteProd`, `ideleSupportedAtEquivSPlaceFactors`.
--
--   **Sources.** They come from these modules of lean/OAI/NumberTheory, in whole or in part: `AlgebraicNumberTheory_Idele_Cohomology_Decomposition`, `AlgebraicNumberTheory_Idele_Cohomology_Herbrand`, `AlgebraicNumberTheory_Idele_Extension_GaloisNorm`, `AlgebraicNumberTheory_Idele_IdealMap`, `KummerTheory_Concrete_SUnitPreparation_FullSUnitKummerExtension`, `LocalClassFieldTheory_ClassFormation_CohomologyBridge`, `LocalClassFieldTheory_ClassFormation_NormalBasis`, `LocalClassFieldTheory_ClassFormation_NormalBasisGradedLifting`, `LocalClassFieldTheory_ClassFormation_NormalBasisInfiniteProduct`, `LocalClassFieldTheory_ClassFormation_PrincipalUnitGraded`, `LocalClassFieldTheory_ClassFormation_ValuationHerbrand`, `LocalClassFieldTheory_ClassFormation_ValueGroupCohomology`, `LocalField_DiscreteValuationField_MixedCharacteristicQp`, `LocalField_DiscreteValuationField_RamificationIdeal`, `LocalField_DiscreteValuationField_ValuationSubringUnits_CompleteRangeRestriction`, `LocalField_DiscreteValuationField_ValuationSubringUnits_LocalFieldRangeRestriction`, `LocalField_DiscreteValuationField_ValuationSubringUnits_RangeRestrictedTopology`, `LocalField_DiscreteValuationField_WithZeroValuationTopology`, `LocalField_GroupTheory_PowerIndex`, `LocalField_NonarchimedeanLocalField_PrincipalUnitQuotients`, `LocalField_Padic_PrincipalUnits`, `Valuation_DiscreteValuationField_Basic`, `Valuation_DiscreteValuationField_Complete`, `Valuation_DiscreteValuationField_Extensions`, `Valuation_DiscreteValuationField_FiniteExtension_Defectless`, `Valuation_DiscreteValuationField_FiniteExtension_Degree`, `Valuation_DiscreteValuationField_FiniteIntegralClosure`, `Valuation_DiscreteValuationField_IntegralClosure`.
--
--   **Imports.** It imports the bundles `OAIQ244Duke015`, `OAIQ244Duke016`, `OAIQ244Duke017`, `OAIQ244Duke018` and `OAIQ244Duke019` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ244Duke039`, `OAIQ244Duke040`, `OAIQ244Duke042`, `OAIQ244Duke043` and `OAIQ244Duke044`.
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
import Mathlib.Algebra.Group.Equiv.TypeTags
import Mathlib.Algebra.Group.Hom.Basic
import Mathlib.Algebra.Group.Int.TypeTags
import Mathlib.Algebra.Group.Pi.Basic
import Mathlib.Algebra.Group.Pi.Units
import Mathlib.Algebra.Group.Subgroup.Basic
import Mathlib.Algebra.Group.Subgroup.Ker
import Mathlib.Algebra.Group.Subgroup.Map
import Mathlib.Algebra.Group.Units.Equiv
import Mathlib.Algebra.Group.Units.Hom
import Mathlib.Algebra.Module.Equiv.Basic
import Mathlib.Algebra.Module.LinearMap.Polynomial
import Mathlib.Algebra.Module.PID
import Mathlib.Algebra.Module.Shrink
import Mathlib.Algebra.Module.ZLattice.Basic
import Mathlib.Algebra.Module.ZMod
import Mathlib.Algebra.Order.Field.Power
import Mathlib.Algebra.Order.Group.Cyclic
import Mathlib.Algebra.Order.Ring.IsNonarchimedean
import Mathlib.Algebra.Order.WithTop.Untop0
import Mathlib.Algebra.Polynomial.Div
import Mathlib.Algebra.Polynomial.FieldDivision
import Mathlib.Algebra.Polynomial.Lifts
import Mathlib.Analysis.AbsoluteValue.Equivalence
import Mathlib.Analysis.Normed.Algebra.GelfandMazur
import Mathlib.Analysis.Normed.Field.Instances
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
import Mathlib.FieldTheory.IsSepClosed
import Mathlib.FieldTheory.Minpoly.IsConjRoot
import Mathlib.FieldTheory.Minpoly.IsIntegrallyClosed
import Mathlib.FieldTheory.Normal.Basic
import Mathlib.FieldTheory.Perfect
import Mathlib.FieldTheory.PrimeField
import Mathlib.FieldTheory.PrimitiveElement
import Mathlib.FieldTheory.Separable
import Mathlib.FieldTheory.SeparableClosure
import Mathlib.GroupTheory.Coset.Card
import Mathlib.GroupTheory.FiniteAbelian.Basic
import Mathlib.GroupTheory.FiniteAbelian.Duality
import Mathlib.GroupTheory.GroupAction.Basic
import Mathlib.GroupTheory.GroupAction.Defs
import Mathlib.GroupTheory.GroupAction.Quotient
import Mathlib.GroupTheory.Index
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.GroupTheory.QuotientGroup.Basic
import Mathlib.GroupTheory.SpecificGroups.Cyclic
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
import Mathlib.LinearAlgebra.Quotient.Pi
import Mathlib.LinearAlgebra.StdBasis
import Mathlib.LinearAlgebra.TensorProduct.Basis
import Mathlib.LinearAlgebra.TensorProduct.RightExactness
import Mathlib.LinearAlgebra.Trace
import Mathlib.Logic.Equiv.Fin.Rotate
import Mathlib.NumberTheory.LocalField.Basic
import Mathlib.NumberTheory.NumberField.AdeleRing
import Mathlib.NumberTheory.NumberField.ClassNumber
import Mathlib.NumberTheory.NumberField.Completion.FinitePlace
import Mathlib.NumberTheory.NumberField.Cyclotomic.Basic
import Mathlib.NumberTheory.NumberField.ProductFormula
import Mathlib.NumberTheory.NumberField.Units.Regulator
import Mathlib.NumberTheory.Ostrowski
import Mathlib.NumberTheory.Padics.PadicNumbers
import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Mathlib.NumberTheory.Padics.ProperSpace
import Mathlib.NumberTheory.Padics.RingHoms
import Mathlib.NumberTheory.Padics.ValuativeRel
import Mathlib.NumberTheory.Padics.WithVal
import Mathlib.NumberTheory.RamificationInertia.Galois
import Mathlib.NumberTheory.RamificationInertia.Inertia
import Mathlib.NumberTheory.RamificationInertia.Ramification
import Mathlib.Order.Filter.AtTopBot.Tendsto
import Mathlib.RepresentationTheory.Homological.FiniteCyclic
import Mathlib.RepresentationTheory.Homological.GroupCohomology.FiniteCyclic
import Mathlib.RepresentationTheory.Homological.GroupCohomology.Hilbert90
import Mathlib.RepresentationTheory.Homological.GroupHomology.FiniteCyclic
import Mathlib.RepresentationTheory.Homological.TateCohomology.Basic
import Mathlib.RepresentationTheory.Invariants
import Mathlib.RingTheory.AdicCompletion.AsTensorProduct
import Mathlib.RingTheory.AdicCompletion.Basic
import Mathlib.RingTheory.AdicCompletion.Functoriality
import Mathlib.RingTheory.AdicCompletion.Noetherian
import Mathlib.RingTheory.AdicCompletion.Topology
import Mathlib.RingTheory.Adjoin.PowerBasis
import Mathlib.RingTheory.AdjoinRoot
import Mathlib.RingTheory.Algebraic.Integral
import Mathlib.RingTheory.ClassGroup.Basic
import Mathlib.RingTheory.Complex
import Mathlib.RingTheory.DedekindDomain.Factorization
import Mathlib.RingTheory.DedekindDomain.IntegralClosure
import Mathlib.RingTheory.DedekindDomain.SInteger
import Mathlib.RingTheory.DiscreteValuationRing.Basic
import Mathlib.RingTheory.DiscreteValuationRing.TFAE
import Mathlib.RingTheory.Filtration
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Ideal.GoingUp
import Mathlib.RingTheory.Ideal.IsPrincipalPowQuotient
import Mathlib.RingTheory.Ideal.Norm.AbsNorm
import Mathlib.RingTheory.Ideal.Quotient.Index
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.RingTheory.IntegralClosure.IsIntegralClosure.Basic
import Mathlib.RingTheory.LocalRing.Basic
import Mathlib.RingTheory.LocalRing.Module
import Mathlib.RingTheory.LocalRing.ResidueField.Basic
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
import Mathlib.Topology.Algebra.ContinuousMonoidHom
import Mathlib.Topology.Algebra.Field
import Mathlib.Topology.Algebra.Group.ClosedSubgroup
import Mathlib.Topology.Algebra.Group.Units
import Mathlib.Topology.Algebra.InfiniteSum.Nonarchimedean
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.Topology.Algebra.Order.Field
import Mathlib.Topology.Algebra.UniformRing
import Mathlib.Topology.Algebra.Valued.LocallyCompact
import Mathlib.Topology.Algebra.Valued.NormedValued
import Mathlib.Topology.Algebra.Valued.ValuativeRel
import Mathlib.Topology.Algebra.Valued.ValuedField
import Mathlib.Topology.Algebra.Valued.WithZeroMulInt
import Mathlib.Topology.UniformSpace.AbsoluteValue
import Definitions.Def_OAIQ244Duke015
import Definitions.Def_OAIQ244Duke016
import Definitions.Def_OAIQ244Duke017
import Definitions.Def_OAIQ244Duke018
import Definitions.Def_OAIQ244Duke019

section
-- module Solutions.OAIQ244_DUKE.AlgebraicNumberTheory_Idele_IdealMap
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionResidueField.instField _root_.RamificationTheory.HilbertRamification.ValuationSubring.selectedResidueField.instAlgebra _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.residueField.field _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.isDomain _root_.CyclicCohomology.binaryCoefficientFamilyCommGroup _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.relativeAdeleRingIntermediateAlgebra _root_.relativeAdeleRingTopIntermediateAlgebra
attribute [-simp] _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.FiniteIdeleGroup.mem_supportedAt_iff _root_.IdeleGroup.finiteComponentContinuous_apply _root_.IdeleGroup.finiteComponent_principalIdele _root_.IdeleGroup.infiniteComponentContinuous_apply _root_.IdeleGroup.infiniteComponent_principalIdele _root_.IdeleGroup.mem_supportedAt_iff _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.LocalFieldTheory.residueField_algebraMap_residue _root_.RelativeIdeleGroup.Cohomology.ideleClassNorm_mk _root_.RelativeIdeleGroup.classInclusion_mk _root_.RelativeIdeleGroup.classNorm_mk _root_.RelativeIdeleGroup.finiteComponent_inclusion _root_.RelativeIdeleGroup.finiteComponent_norm _root_.RelativeIdeleGroup.inclusion_principalIdele _root_.RelativeIdeleGroup.infiniteComponent_inclusion _root_.RelativeIdeleGroup.infiniteComponent_norm _root_.RelativeIdeleGroup.norm_inclusion _root_.RelativeIdeleGroup.norm_principalIdele _root_.RelativeIdeleGroup.smul_inclusion _root_.compositeToBaseNormQuotient_mk _root_.intermediateToCompositeNormQuotient_mk
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

/-!
# The ideal attached to an idele

This file formalizes the ideal map from ideles. Its construction
is explicit: local discrete valuations form a finitely supported integer
vector, and unique factorization of fractional ideals identifies that vector
with a nonzero fractional ideal.  We prove both stages surjective and identify
the kernel with the ideles integral at every finite place.
-/

open scoped NumberField RestrictedProduct WithZero
open NumberField IsDedekindDomain

noncomputable section


variable {K : Type*} [Field K] [NumberField K]

namespace IdeleGroup

theorem fractionalIdeal_surjective :
    Function.Surjective (fractionalIdeal (K := K)) := by
  intro I
  obtain ⟨a, rfl⟩ :=
    FiniteIdeleGroup.fractionalIdeal_surjective (K := K) I
  exact ⟨(1, a), rfl⟩

theorem idealClass_surjective :
    Function.Surjective (idealClass (K := K)) := by
  intro c
  induction c using ClassGroup.induction (R := 𝓞 K) K with
  | h I =>
      obtain ⟨a, ha⟩ := fractionalIdeal_surjective (K := K) I
      exact ⟨a, by simp [idealClass, ha]⟩

end IdeleGroup
end
end

section
-- module Solutions.OAIQ244_DUKE.Valuation_DiscreteValuationField_Basic
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.LocalFieldTheory.DiscreteValuationField.Examples.Qp.padicDVRValuation_isRankOneDiscrete _root_.LocalFieldTheory.DiscreteValuationField.LocalField.residueField_charP_residueCharacteristic _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.RamificationTheory.HilbertRamification.ValuationSubring.selectedResidueField.instAlgebra _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.RelativeIdeleGroup.relativeIdeleMulAction _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.relativeAdeleRingIntermediateAlgebra _root_.relativeAdeleRingTopIntermediateAlgebra
attribute [-simp] _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.coe_valuationSubringUnitsToFieldUnits_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.multiplicativeIntegerValuationOfUniformizer_val _root_.LocalFieldTheory.residueField_algebraMap_residue _root_.ValuationTheory.DiscreteValuationField.ValuedExtension.Henselian.integralClosureValuationSubringIntegerMapOfMemOrInv_apply _root_.ValuationTheory.DiscreteValuationField.ValuedExtension.degree_eq_finrank _root_.ValuationTheory.DiscreteValuationField.ValuedExtension.integerMap_apply _root_.ValuationTheory.DiscreteValuationField.ValuedExtension.integralClosureRingEquivTargetValuationSubringOfModuleFinite_apply _root_.ValuationTheory.DiscreteValuationField.ValuedExtension.integralClosureToTargetValuationSubringOfHasExtension_apply _root_.ValuationTheory.DiscreteValuationField.ValuedExtension.integralClosureValuationSubringIntegerMapOfMemOrInv_apply _root_.ValuationTheory.DiscreteValuationField.ValuedExtension.residueFieldEquivOfSurjective_apply _root_.ValuationTheory.DiscreteValuationField.ValuedExtension.residueFieldEquivOfSurjective_apply_residue _root_.ValuationTheory.DiscreteValuationField.ValuedExtension.residueFieldEquivOfSurjective_symm_apply_residueMap _root_.ValuationTheory.DiscreteValuationField.ValuedExtension.residueFieldEquivOfSurjective_symm_apply_target_residue _root_.ValuationTheory.DiscreteValuationField.ValuedExtension.residueMap_residue _root_.ValuationTheory.DiscreteValuationField.ValuedExtension.residueMap_residueFieldEquivOfSurjective_symm_apply _root_.ValuationTheory.DiscreteValuationField.ValuedExtension.residueUnitsEquivOfResidueMapSurjective_apply _root_.ValuationTheory.DiscreteValuationField.ValuedExtension.targetValuationSubringToIntegralClosureOfModuleFinite_apply _root_.ValuationTheory.DiscreteValuationField.ValuedExtension.unitMap_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

namespace ValuationTheory

/-!
# Discretely valued fields

This is the basic one-dimensional API for fields equipped with a chosen
rank-one discrete valuation.
-/

noncomputable section

universe u v

namespace DiscreteValuationField

namespace DVF

variable {K : Type u} [Field K]

/-- Every nonzero ideal in the valuation ring of a DVF is a power of the maximal
ideal. -/
theorem nonzero_ideal_eq_maximalIdeal_pow (F : DVF.{u, v} K)
    (I : Ideal F.valuationSubring) (hI : I ≠ ⊥) :
    ∃ n : ℕ, I = F.maximalIdeal ^ n := by
  obtain ⟨pi, hpi⟩ :=
    IsDiscreteValuationRing.exists_irreducible F.valuationSubring
  obtain ⟨n, hn⟩ :=
    IsDiscreteValuationRing.ideal_eq_span_pow_irreducible hI hpi
  refine ⟨n, ?_⟩
  rw [hn]
  rw [← Ideal.span_singleton_pow]
  rw [← hpi.maximalIdeal_eq]

/-- The maximal ideal of a DVF valuation ring is nonzero. -/
theorem maximalIdeal_ne_bot (F : DVF.{u, v} K) :
    F.maximalIdeal ≠ ⊥ := by
  rcases F.exists_uniformizer with ⟨pi, hpi⟩
  intro hbot
  have hmem : pi ∈ (⊥ : Ideal F.valuationSubring) := by
    rw [← hbot]
    exact F.uniformizer_mem_maximalIdeal hpi
  have hzero_sub : pi = 0 := by
    simpa using hmem
  apply hpi.ne_zero
  exact Subtype.ext_iff.mp hzero_sub

/-! ### Successive quotients of powers of the maximal ideal -/

end DVF
end DiscreteValuationField

end

end ValuationTheory
end

section
-- module Solutions.OAIQ244_DUKE.Valuation_DiscreteValuationField_Complete
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_isCompleteDiscrete _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.LocalFieldTheory.DiscreteValuationField.Examples.Qp.padicDVRValuation_isRankOneDiscrete _root_.LocalFieldTheory.DiscreteValuationField.LocalField.residueField_charP_residueCharacteristic _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.LubinTate.Valuations.exponentialValuationSubringIsLocalRing _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionFixedSubring.instIsLocalRing _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionResidueField.instField _root_.RamificationTheory.HilbertRamification.ValuationSubring.selectedResidueField.instAlgebra _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.relativeAdeleRingIntermediateAlgebra _root_.relativeAdeleRingTopIntermediateAlgebra
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

namespace ValuationTheory

/-!
# Complete discretely valued fields
-/

noncomputable section

universe u v w

namespace DiscreteValuationField

namespace Valuation

end Valuation

namespace CompleteDVF

variable {K : Type u} [Field K]

/-- Membership in the maximal ideal is characterized by strictly positive valuation. -/
theorem mem_maximalIdeal_iff (F : CompleteDVF.{u, v} K)
    (x : F.valuationSubring) :
    x ∈ F.maximalIdeal ↔ F.valuation (x : K) < 1 :=
  F.toDVF.mem_maximalIdeal_iff x

/-- An integral element has zero residue exactly when it lies in the maximal ideal. -/
theorem residue_eq_zero_iff (F : CompleteDVF.{u, v} K)
    (x : F.valuationSubring) :
    F.residueMap x = 0 ↔ x ∈ F.maximalIdeal :=
  IsLocalRing.residue_eq_zero_iff x

/-- Powers of the maximal ideal are generated by powers of any chosen
uniformizer. -/
theorem maximalIdeal_pow_eq_span_uniformizer_pow (F : CompleteDVF.{u, v} K)
    {pi : F.valuationSubring} (hpi : F.valuation.IsUniformizer (pi : K))
    (n : ℕ) :
    F.maximalIdeal ^ n = Ideal.span ({pi ^ n} : Set F.valuationSubring) :=
  F.toDVF.maximalIdeal_pow_eq_span_uniformizer_pow hpi n

/-- Membership in a power of the maximal ideal is divisibility by the
corresponding power of a uniformizer. -/
theorem mem_maximalIdeal_pow_iff_uniformizer_pow_dvd (F : CompleteDVF.{u, v} K)
    {pi x : F.valuationSubring}
    (hpi : F.valuation.IsUniformizer (pi : K)) (n : ℕ) :
    x ∈ F.maximalIdeal ^ n ↔ pi ^ n ∣ x :=
  F.toDVF.mem_maximalIdeal_pow_iff_uniformizer_pow_dvd hpi n

/-- Every nonzero ideal in the valuation ring of a complete DVF is a power of
the maximal ideal. -/
theorem nonzero_ideal_eq_maximalIdeal_pow (F : CompleteDVF.{u, v} K)
    (I : Ideal F.valuationSubring) (hI : I ≠ ⊥) :
    ∃ n : ℕ, I = F.maximalIdeal ^ n :=
  F.toDVF.nonzero_ideal_eq_maximalIdeal_pow I hI

/-- No power of a uniformizer lies one step deeper in the maximal-ideal
filtration. -/
theorem uniformizer_pow_not_mem_maximalIdeal_pow_succ
    (F : CompleteDVF.{u, v} K)
    {pi : F.valuationSubring} (hpi : F.valuation.IsUniformizer (pi : K))
    (n : ℕ) :
    pi ^ n ∉ F.maximalIdeal ^ (n + 1) :=
  F.toDVF.uniformizer_pow_not_mem_maximalIdeal_pow_succ hpi n

end CompleteDVF
end DiscreteValuationField

end

end ValuationTheory
end

section
-- module Solutions.OAIQ244_DUKE.Valuation_DiscreteValuationField_Extensions
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.LocalFieldTheory.DiscreteValuationField.LocalField.residueField_charP_residueCharacteristic _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

namespace ValuationTheory

/-!
# Finite extensions of discretely valued fields

The extension relation is ambient data: an algebra, finite-dimensionality, and
mathlib's `Valuation.HasExtension` property.  There is deliberately no
proof-irrelevant marker object.  All invariants and maps are defined once for
`DVF` values and can therefore be used unchanged for Henselian and complete
discretely valued fields through their canonical `toDVF` projections.
-/

noncomputable section

universe u v w x

namespace DiscreteValuationField
namespace ValuedExtension

variable {K : Type u} {L : Type w} [Field K] [Field L]
variable [Algebra K L] [FiniteDimensional K L]
variable (base : DVF.{u, v} K) (target : DVF.{w, x} L)
variable [base.valuation.HasExtension target.valuation]

omit [FiniteDimensional K L] in
/-- The image of the source maximal ideal in the target valuation ring is nonzero. -/
theorem maximalIdeal_map_integerMap_ne_bot :
    Ideal.map (integerMap base target) base.maximalIdeal ≠ ⊥ := by
  intro h
  exact base.maximalIdeal_ne_bot
    ((Ideal.map_eq_bot_iff_of_injective
      (integerMap_injective base target)).1 h)

/-- Defectlessness is the exact fundamental equality. -/
def IsDefectless : Prop :=
  degree base target =
    ramificationIndex base target * residueDegree base target

end ValuedExtension
end DiscreteValuationField
end
end ValuationTheory
end

section
-- module Solutions.OAIQ244_DUKE.Valuation_DiscreteValuationField_FiniteExtension_Defectless
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.HilbertRamification.Dedekind.basePrime_isPrime _root_.LocalFieldTheory.DiscreteValuationField.Examples.Qp.padicDVRValuation_isRankOneDiscrete _root_.LocalFieldTheory.DiscreteValuationField.LocalField.residueField_charP_residueCharacteristic _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionFixedMaximalIdeal.instIsMaximal _root_.RamificationTheory.HilbertRamification.ValuationSubring.selectedResidueField.instAlgebra _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.relativeAdeleRingIntermediateAlgebra _root_.relativeAdeleRingTopIntermediateAlgebra
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

/-!
# Defectlessness from a finite extension of valuation rings

The local Dedekind fundamental identity only needs discretely valued fields.
Completeness and Henselianity play no role once the target valuation ring is a
finite module over the base valuation ring.
-/

noncomputable section

namespace ValuationTheory.DiscreteValuationField.ValuedExtension

universe u v w x

variable {K : Type u} {L : Type w} [Field K] [Field L] [Algebra K L]

/-- A valued extension of discretely valued fields is defectless when its
target valuation ring is finite over the base valuation ring. -/
theorem isDefectless_of_moduleFinite
    (base : DVF.{u, v} K) (target : DVF.{w, x} L)
    [base.valuation.HasExtension target.valuation]
    [Module.Finite base.valuationSubring target.valuationSubring]
    [IsScalarTower base.valuationSubring target.valuationSubring L] :
    IsDefectless base target := by
  classical
  let : FaithfulSMul base.valuationSubring target.valuationSubring :=
    FaithfulSMul.of_field_isFractionRing
      base.valuationSubring target.valuationSubring K L
  have hprimes :=
    IsLocalRing.primesOver_eq target.valuationSubring base.maximalIdeal_ne_bot
  have hq : target.maximalIdeal ∈ base.maximalIdeal.primesOver target.valuationSubring := by
    rw [hprimes]
    exact Set.mem_singleton target.maximalIdeal
  let : target.maximalIdeal.LiesOver base.maximalIdeal := hq.2
  let : Subsingleton (base.maximalIdeal.primesOver target.valuationSubring) :=
    Set.Subsingleton.coe_sort (by
      rw [hprimes]
      exact Set.subsingleton_singleton)
  have hsum :=
    Ideal.sum_ramification_inertia_eq_finrank base.maximalIdeal target.valuationSubring
  rw [Fintype.sum_subsingleton _ ⟨target.maximalIdeal, hq⟩] at hsum
  change Module.finrank K L =
    Ideal.ramificationIdx' base.maximalIdeal target.maximalIdeal *
      target.maximalIdeal.inertiaDeg base.valuationSubring
  rw [Ideal.ramificationIdx'_eq_ramificationIdx
      base.maximalIdeal target.maximalIdeal base.maximalIdeal_ne_bot,
    IsFractionRing.finrank_eq base.valuationSubring K target.valuationSubring L]
  exact hsum.symm

end ValuationTheory.DiscreteValuationField.ValuedExtension

end
end

section
-- module Solutions.OAIQ244_DUKE.Valuation_DiscreteValuationField_IntegralClosure
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.LocalFieldTheory.DiscreteValuationField.LocalField.residueField_charP_residueCharacteristic _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.LubinTate.Valuations.exponentialValuationSubringIsLocalRing _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionFixedSubring.instIsLocalRing _root_.RamificationTheory.HilbertRamification.ValuationSubring.selectedResidueField.instAlgebra _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.relativeAdeleRingIntermediateAlgebra _root_.relativeAdeleRingTopIntermediateAlgebra
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

namespace ValuationTheory

/-!
# Integral closures of valuation rings

This module uses the actual mathlib integral closure
`integralClosure base.toDVF.valuationSubring L`.  It does not introduce a replacement
structure.
-/

noncomputable section

universe u v w x

namespace DiscreteValuationField
namespace ValuedExtension

variable {K : Type u} {L : Type w} [Field K] [Field L]
variable [Algebra K L] [FiniteDimensional K L]
variable (base : CompleteDVF.{u, v} K) (target : CompleteDVF.{w, x} L)
variable [base.valuation.HasExtension target.valuation]

/-- If a chosen extension valuation ring is already proved to be the integral
closure of the base valuation ring in a finite separable field extension, then
it is finite over the base valuation ring. -/
theorem moduleFinite_target_valuationSubring_of_isIntegralClosure
    (base : CompleteDVF.{u, v} K) (target : CompleteDVF.{w, x} L)
    [base.valuation.HasExtension target.valuation]
    [Algebra.IsSeparable K L]
    [IsScalarTower base.toDVF.valuationSubring target.toDVF.valuationSubring L]
    [IsIntegralClosure target.toDVF.valuationSubring base.toDVF.valuationSubring L] :
    Module.Finite base.toDVF.valuationSubring target.toDVF.valuationSubring := by
  let : IsFractionRing base.toDVF.valuationSubring K :=
    base_valuationSubring_isFractionRing (K := K) base
  let : IsIntegrallyClosed base.toDVF.valuationSubring :=
    base_valuationSubring_isIntegrallyClosed (K := K) base
  let : IsNoetherianRing base.toDVF.valuationSubring :=
    base_valuationSubring_isNoetherianRing (K := K) base
  exact IsIntegralClosure.finite base.toDVF.valuationSubring K L target.toDVF.valuationSubring

omit [FiniteDimensional K L] in
/-- The target maximal ideal lies over the base maximal ideal for an actual
extension of valuations.  This is the prime-theoretic input for replacing
certificate-style choices of a prime above the base maximal ideal. -/
theorem target_maximalIdeal_liesOver_base_maximal_of_hasExtension
    (base : CompleteDVF.{u, v} K) (target : CompleteDVF.{w, x} L)
    [base.valuation.HasExtension target.valuation] :
    target.maximalIdeal.LiesOver base.maximalIdeal := by
  exact inferInstanceAs
    ((IsLocalRing.maximalIdeal target.valuation.valuationSubring).LiesOver
      (IsLocalRing.maximalIdeal base.valuation.valuationSubring))

end ValuedExtension

end DiscreteValuationField

end

end ValuationTheory
end

section
-- module Solutions.OAIQ244_DUKE.Valuation_DiscreteValuationField_FiniteExtension_Degree
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.LocalFieldTheory.DiscreteValuationField.LocalField.residueField_charP_residueCharacteristic _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionFixedMaximalIdeal.instIsMaximal _root_.RamificationTheory.HilbertRamification.ValuationSubring.selectedMaximalIdeal.instLiesOver _root_.RamificationTheory.HilbertRamification.ValuationSubring.selectedResidueField.instAlgebra _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.relativeAdeleRingIntermediateAlgebra _root_.relativeAdeleRingTopIntermediateAlgebra
attribute [-simp] _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.coe_valuationSubringUnitsToFieldUnits_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.fieldUnitValueUnit_mul _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.fieldUnitValueUnit_one _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.mrangeRestrict_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.multiplicativeIntegerValuationOfUniformizer_val _root_.LocalFieldTheory.residueField_algebraMap_residue _root_.ValuationTheory.DiscreteValuationField.ValuedExtension.Henselian.integralClosureValuationSubringIntegerMapOfMemOrInv_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

namespace ValuationTheory

/-!
# Finite valued extension consequences

This file collects theorem-level consequences around finite valued extensions:
canonical local-Dedekind degree formulas, uniqueness criteria for extended
valuations, and the algebra equivalence identifying an actual integral-closure
valuation ring with mathlib's `integralClosure`.
-/

noncomputable section

universe u v w x y

namespace DiscreteValuationField
namespace ValuedExtension

open ValuationTheory.DiscreteValuationField.Valuation

variable {K : Type u} {L : Type w} [Field K] [Field L]
variable [Algebra K L] [FiniteDimensional K L]
variable (base : CompleteDVF.{u, v} K) (target : CompleteDVF.{w, x} L)
variable [base.valuation.HasExtension target.valuation]

omit [FiniteDimensional K L] in
/-- The target maximal ideal lies over the base maximal ideal for any actual
extension of the chosen valuations.  This is the record-free form of the local
map property used by finite-extension invariants. -/
theorem maximalIdeal_liesOver_of_hasExtension
    (base : CompleteDVF.{u, v} K) (target : CompleteDVF.{w, x} L)
    [base.valuation.HasExtension target.valuation] :
    target.maximalIdeal.LiesOver base.maximalIdeal :=
  target_maximalIdeal_liesOver_base_maximal_of_hasExtension base target

omit [FiniteDimensional K L] in
/-- The local-Dedekind fundamental identity in record-free form: for the actual
valuation rings attached to a finite valued field extension, mathlib's
ramification index times mathlib's inertia degree is the field degree. -/
theorem ideal_ramificationIdx_mul_inertiaDeg_eq_finrank_of_hasExtension
    (base : CompleteDVF.{u, v} K) (target : CompleteDVF.{w, x} L)
    [base.valuation.HasExtension target.valuation]
    [Module.Finite base.valuationSubring target.valuationSubring]
    [IsScalarTower base.valuationSubring target.valuationSubring L] :
    Ideal.ramificationIdx' base.maximalIdeal target.maximalIdeal *
      target.maximalIdeal.inertiaDeg base.valuationSubring = Module.finrank K L := by
  exact (isDefectless_of_moduleFinite base.toDVF target.toDVF).symm

/-- If the target valuation ring is the integral closure of the base valuation
ring in a finite separable field extension, then the local-Dedekind
ramification identity holds without separately assuming module-finiteness. -/
theorem ideal_ramificationIdx_mul_inertiaDeg_eq_finrank_of_isIntegralClosure
    (base : CompleteDVF.{u, v} K) (target : CompleteDVF.{w, x} L)
    [base.valuation.HasExtension target.valuation]
    [Algebra.IsSeparable K L]
    [IsScalarTower base.valuationSubring target.valuationSubring L]
    [IsIntegralClosure target.valuationSubring base.valuationSubring L] :
    Ideal.ramificationIdx' base.maximalIdeal target.maximalIdeal *
      target.maximalIdeal.inertiaDeg base.valuationSubring = Module.finrank K L := by
  let : Module.Finite base.valuationSubring target.valuationSubring :=
    moduleFinite_target_valuationSubring_of_isIntegralClosure
      (K := K) (L := L) base target
  exact ideal_ramificationIdx_mul_inertiaDeg_eq_finrank_of_hasExtension
    (K := K) (L := L) base target

/-- A valued extension whose target is the integral closure is defectless. -/
theorem isDefectless_of_isIntegralClosure
    (base : CompleteDVF.{u, v} K) (target : CompleteDVF.{w, x} L)
    [base.valuation.HasExtension target.valuation]
    [Algebra.IsSeparable K L]
    [IsScalarTower base.valuationSubring target.valuationSubring L]
    [IsIntegralClosure target.valuationSubring base.valuationSubring L] :
    ValuedExtension.IsDefectless base.toDVF target.toDVF := by
  change Module.finrank K L =
    Ideal.ramificationIdx' base.maximalIdeal target.maximalIdeal *
      target.maximalIdeal.inertiaDeg base.valuationSubring
  exact (ideal_ramificationIdx_mul_inertiaDeg_eq_finrank_of_isIntegralClosure
    (K := K) (L := L) base target).symm

omit [FiniteDimensional K L] in
/-- The target maximal ideal lies over the base maximal ideal for a valued
extension. -/
theorem maximalIdeal_liesOver :
    target.maximalIdeal.LiesOver base.maximalIdeal :=
  maximalIdeal_liesOver_of_hasExtension (K := K) (L := L) base target

omit [FiniteDimensional K L] in
/-- Residue degree is the linear rank of the target residue field over the source residue field. -/
theorem residueDegree_eq_finrank_quotient
     :
    letI : target.maximalIdeal.LiesOver base.maximalIdeal :=
      (maximalIdeal_liesOver base target)
    (ValuedExtension.residueDegree base.toDVF target.toDVF) =
      Module.finrank
        (base.valuationSubring ⧸ base.maximalIdeal)
        (target.valuationSubring ⧸ target.maximalIdeal) := by
  exact Ideal.inertiaDeg_eq_of_isMaximal base.maximalIdeal target.maximalIdeal

/-- Integral-closure form of the local-Dedekind degree identity for a valued
finite separable extension. -/
theorem ramificationIndex_mul_residueDegree_eq_degree_of_isIntegralClosure
    [Algebra.IsSeparable K L]
    [IsScalarTower base.valuationSubring target.valuationSubring L]
    [IsIntegralClosure target.valuationSubring base.valuationSubring L] :
    (ValuedExtension.ramificationIndex base.toDVF target.toDVF) *
        ValuedExtension.residueDegree base.toDVF target.toDVF =
      ValuedExtension.degree base.toDVF target.toDVF := by
  simpa [ramificationIndex, residueDegree,
    ramificationIndex, residueDegree, degree] using
    (ideal_ramificationIdx_mul_inertiaDeg_eq_finrank_of_isIntegralClosure
      (K := K) (L := L) base target)

end ValuedExtension
end DiscreteValuationField

end

end ValuationTheory
end

section
-- module Solutions.OAIQ244_DUKE.LocalClassFieldTheory_ClassFormation_CohomologyBridge
attribute [-instance] _root_.ClassFormation.DegreeData.GaloisSubextension.extensionSubgroup_normalInstance _root_.ClassFormation.FiniteCyclicSubextension.instNormalSubtypeMemSubgroupFieldExtensionSubgroupField _root_.ClassFormation.FiniteGaloisSubextension.extensionSubgroup_normalInstance _root_.ClassFormation.FiniteGaloisSubextension.extensionSubgroup_over_intermediate_normalInstance _root_.ClassFormation.FiniteGaloisSubextension.intermediateField_normalInstance _root_.ClassFormation.FiniteUnramifiedCyclicExtension.instNormalSubtypeMemSubgroupFieldExtensionSubgroupField _root_.ClassFormation.conjugateExtension_normal _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.LocalClassFieldTheory.extensionSubgroupBase_normal _root_.LocalClassFieldTheory.finiteGaloisExtensionSubgroupOfEmbedding_normal _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.LubinTate.compatibleGroupFamiliesCommGroup _root_.LubinTate.compatibleGroupFamiliesGroup _root_.RamificationTheory.HilbertRamification.ValuationSubring.inertiaGroup_normal _root_.RamificationTheory.HilbertRamification.ValuationSubring.ramificationGroupInInertiaAut_normal _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.maximalIdealPowSuccQuotModule _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.CyclicCohomology.binaryCoefficientFamilyCommGroup _root_.CyclicCohomology.instMulDistribMulActionBinaryCoefficientFamily _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace
attribute [-simp] _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.CyclicCohomology.fixedPiEquiv_apply_coe _root_.CyclicCohomology.herbrandH0EquivariantMulEquiv_mk _root_.CyclicCohomology.inducedFixedEquiv_apply_coe _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.LocalClassFieldTheory.chosenNormalBasisPrincipalUnitSubgroup_tateNorm_coe _root_.LocalFieldTheory.residueField_algebraMap_residue
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

namespace LocalClassFieldTheory

open CyclicCohomology

/-!
# The actual low-degree Tate quotients as Herbrand quotients

This file compares the concrete multiplicative Herbrand quotients from
low-degree cyclic cohomology with the Tate objects built from mathlib's actual
Galois representation on `Lˣ`.  The comparison uses the standard Galois action
on units; it does not introduce a replacement coefficient object.
-/

noncomputable section

open scoped BigOperators

open CyclicCohomology.ProfiniteCohomology.Herbrand
open CategoryTheory

variable (K L : Type) [Field K] [Field L] [Algebra K L]

/-- The kernel of the fixed-unit quotient map is exactly
the Herbrand norm subgroup inside the fixed subgroup. -/
theorem fixedUnitToInvariantsNormQuotientMonoidHom_ker
    [Fintype (Gal(L / K))] :
    kernelOfAdditiveQuotientHom (unitsTateH0NormSubmodule K L)
        (fixedUnitToInvariantsNormQuotientMonoidHom K L) =
      (tateNormSubgroup (Gal(L / K)) Lˣ).subgroupOf
        (fixedSubgroup (Gal(L / K)) Lˣ) := by
  ext x
  constructor
  · intro hx
    have hx0 := congrArg Multiplicative.toAdd hx
    change
      (unitsTateH0NormSubmodule K L).mkQ
        (additiveFixedUnitsEquivInvariants K L (Additive.ofMul x)) = 0 at hx0
    have hxmem :
        additiveFixedUnitsEquivInvariants K L (Additive.ofMul x) ∈
          unitsTateH0NormSubmodule K L :=
      (Submodule.Quotient.mk_eq_zero (unitsTateH0NormSubmodule K L)).1 hx0
    rcases hxmem with ⟨y, hy⟩
    change (x : Lˣ) ∈ tateNormSubgroup (Gal(L / K)) Lˣ
    refine ⟨Additive.toMul y, ?_⟩
    have hy' := congrArg
      (fun z : unitsInvariantSubmodule K L =>
        Additive.toMul (z : Additive Lˣ)) hy
    change Additive.toMul (unitsNormLinearMap K L y) = (x : Lˣ) at hy'
    rw [tateNormHom_apply,
      ← unitsNormLinearMap_toMul_eq_tateNorm K L (Additive.toMul y)]
    simpa using hy'
  · intro hx
    change (x : Lˣ) ∈ tateNormSubgroup (Gal(L / K)) Lˣ at hx
    rcases hx with ⟨y, hy⟩
    apply Multiplicative.toAdd.injective
    change
      (unitsTateH0NormSubmodule K L).mkQ
        (additiveFixedUnitsEquivInvariants K L (Additive.ofMul x)) = 0
    apply (Submodule.Quotient.mk_eq_zero (unitsTateH0NormSubmodule K L)).2
    change additiveFixedUnitsEquivInvariants K L (Additive.ofMul x) ∈
      LinearMap.range (unitsNormToInvariantsLinearMap K L)
    refine ⟨Additive.ofMul y, ?_⟩
    apply Subtype.ext
    apply Additive.toMul.injective
    change Additive.toMul
      (unitsNormLinearMap K L (Additive.ofMul y)) = (x : Lˣ)
    rw [unitsNormLinearMap_toMul_eq_tateNorm K L y]
    exact hy

/-- Every invariant-unit class modulo norms has a multiplicatively fixed representative. -/
theorem fixedUnitToInvariantsNormQuotientMonoidHom_surjective
    [Fintype (Gal(L / K))] :
    Function.Surjective (fixedUnitToInvariantsNormQuotientMonoidHom K L) := by
  intro q
  rcases Submodule.mkQ_surjective (unitsTateH0NormSubmodule K L)
      (Multiplicative.toAdd q) with ⟨z, hz⟩
  let x : fixedSubgroup (Gal(L / K)) Lˣ :=
    Additive.toMul ((additiveFixedUnitsEquivInvariants K L).symm z)
  refine ⟨x, ?_⟩
  apply Multiplicative.toAdd.injective
  change
    (unitsTateH0NormSubmodule K L).mkQ
      (additiveFixedUnitsEquivInvariants K L (Additive.ofMul x)) =
        Multiplicative.toAdd q
  calc
    _ = (unitsTateH0NormSubmodule K L).mkQ z := by
      apply congrArg (unitsTateH0NormSubmodule K L).mkQ
      change additiveFixedUnitsEquivInvariants K L
        ((additiveFixedUnitsEquivInvariants K L).symm z) = z
      exact (additiveFixedUnitsEquivInvariants K L).apply_symm_apply z
    _ = Multiplicative.toAdd q := hz

/-- The multiplicative Herbrand quotient is the invariant-unit quotient by norms. -/
def herbrandH0MulEquivInvariantsNormQuotient
    [Fintype (Gal(L / K))] :=
  quotientMulEquivOfSurjectiveAdditiveQuotient
    (unitsTateH0NormSubmodule K L)
    ((tateNormSubgroup (Gal(L / K)) Lˣ).subgroupOf
      (fixedSubgroup (Gal(L / K)) Lˣ))
    (fixedUnitToInvariantsNormQuotientMonoidHom K L)
    (fixedUnitToInvariantsNormQuotientMonoidHom_ker K L)
    (fixedUnitToInvariantsNormQuotientMonoidHom_surjective K L)

/-- The multiplicative Herbrand quotient of field units is mathlib's
degree-zero Tate cohomology. -/
def herbrandH0EquivTateCohomologyZero [Fintype (Gal(L / K))] :
    HerbrandH0 (Gal(L / K)) Lˣ ≃
      tateCohomology (Rep.ofAlgebraAutOnUnits K L) 0 :=
  (mulEquivMultiplicativeToEquiv
      (herbrandH0MulEquivInvariantsNormQuotient K L)).trans
    (tateUnitsH0IsoInvariantsQuotient K L).symm.toLinearEquiv.toEquiv

end
end LocalClassFieldTheory
end

section
-- module Solutions.OAIQ244_DUKE.LocalField_NonarchimedeanLocalField_PrincipalUnitQuotients
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.LubinTate.Valuations.exponentialValuationSubringIsLocalRing _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionFixedSubring.instIsLocalRing _root_.RamificationTheory.HilbertRamification.ValuationSubring.selectedResidueField.instAlgebra _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.maximalIdealPowSuccQuotModule _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.isDomain _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.isLocalRing _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.relativeAdeleRingIntermediateAlgebra _root_.relativeAdeleRingTopIntermediateAlgebra
attribute [-simp] _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.CyclicCohomology.integerUnitsModPrincipalUnitsAtLevelConcreteEquiv_mk _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.LocalFieldTheory.integerUnitsModPrincipalUnitsConcreteEquiv_mk _root_.LocalFieldTheory.integerUnitsModPrincipalUnitsLift_mk _root_.LocalFieldTheory.principalUnitsMapOfUnramifiedValuation_apply _root_.LocalFieldTheory.principalUnitsSuccQuotAddEquivResidueOfIrreducible_symm_residue _root_.LocalFieldTheory.principalUnitsSuccQuotMapOfUnramifiedValuation_mk _root_.LocalFieldTheory.residueField_algebraMap_residue
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI
/-!
# Successive principal-unit quotients

Develops `U^n/U^(n+1)` and identifies it with the additive ideal quotient
`𝓂^n/𝓂^(n+1)` through the first-order map `a ↦ 1 + a`.
-/

set_option autoImplicit false

namespace LocalFieldTheory

noncomputable section

universe u

open scoped ValuativeRel

open Filter

/-! ### Separatedness of the principal-unit filtration -/

/-! ### Maximal-ideal powers as local neighborhoods -/

/-! ### Finite correction products for complete lifting -/

/-- Every finite correction product stays in the initial principal-unit level
`U^n`. -/
theorem principalUnitsCorrectionProduct_mem
    (K : Type u) [Field K] [ValuativeRel K] (n : Nat)
    (z : ∀ d : Nat, principalUnits K (n + d)) (d : Nat) :
    principalUnitsCorrectionProduct K n z d ∈ principalUnits K n := by
  induction d with
  | zero =>
      simp [principalUnitsCorrectionProduct]
  | succ d ih =>
      rw [principalUnitsCorrectionProduct_succ]
      exact (principalUnits K n).mul_mem ih
        (principalUnits_antitone K (Nat.le_add_right n d) (z d).2)

/-- The tail quotient of two finite correction products lies in the principal
unit level controlled by the earlier index. This is the filtration input for
the later Cauchy argument. -/
theorem principalUnitsCorrectionProduct_div_mem
    (K : Type u) [Field K] [ValuativeRel K] (n m d : Nat)
    (z : ∀ d : Nat, principalUnits K (n + d)) :
    principalUnitsCorrectionProduct K n z (m + d) /
        principalUnitsCorrectionProduct K n z m ∈
      principalUnits K (n + m) := by
  induction d with
  | zero =>
      simp
  | succ d ih =>
      have hprod :
          principalUnitsCorrectionProduct K n z (m + (d + 1)) =
            principalUnitsCorrectionProduct K n z (m + d) *
              (z (m + d) : 𝒪[K]ˣ) := by
        rw [Nat.add_succ]
        rfl
      rw [hprod]
      have hz :
          (z (m + d) : 𝒪[K]ˣ) ∈ principalUnits K (n + m) := by
        exact principalUnits_antitone K
          (Nat.add_le_add_left (Nat.le_add_right m d) n) (z (m + d)).2
      have hEq :
          principalUnitsCorrectionProduct K n z (m + d) *
              (z (m + d) : 𝒪[K]ˣ) /
              principalUnitsCorrectionProduct K n z m =
            (principalUnitsCorrectionProduct K n z (m + d) /
              principalUnitsCorrectionProduct K n z m) *
              (z (m + d) : 𝒪[K]ˣ) := by
        simp [div_eq_mul_inv, mul_assoc, mul_comm]
      rw [hEq]
      exact (principalUnits K (n + m)).mul_mem ih hz

/-- Ring-valued form of the tail-control statement: the two finite correction
products are congruent modulo `𝓂^(n+m)`. -/
theorem principalUnitsCorrectionProduct_div_sub_one_mem
    (K : Type u) [Field K] [ValuativeRel K] (n m d : Nat)
    (z : ∀ d : Nat, principalUnits K (n + d)) :
    ((principalUnitsCorrectionProduct K n z (m + d) /
          principalUnitsCorrectionProduct K n z m : 𝒪[K]ˣ) : 𝒪[K]) - 1 ∈
      (𝓂[K] ^ (n + m) : Ideal 𝒪[K]) := by
  exact (mem_principalUnits_iff K
    (principalUnitsCorrectionProduct K n z (m + d) /
      principalUnitsCorrectionProduct K n z m) (n + m)).1
    (principalUnitsCorrectionProduct_div_mem K n m d z)

end
end LocalFieldTheory
end

section
-- module Solutions.OAIQ244_DUKE.LocalClassFieldTheory_ClassFormation_ValueGroupCohomology
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.LubinTate.compatibleGroupFamiliesGroup _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.CyclicCohomology.binaryCoefficientFamilyCommGroup _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false
/-! Provides the public declarations in the `LocalClassFieldTheory.ClassFormation.ValueGroupCohomology` Lean module. -/

namespace LocalClassFieldTheory

open LocalFieldTheory

open CyclicCohomology

noncomputable section

open scoped BigOperators

universe u

open CyclicCohomology.ProfiniteCohomology.Herbrand

variable (K L : Type u) [Field K] [Field L] [Algebra K L]
  [FiniteDimensional K L]

/-- The norm kernel of the trivial torsion-free value group is zero. -/
theorem galoisGroupValueGroup_normKernelSubgroup_eq_bot :
    letI := galoisGroupValueGroupMulDistribMulAction K L
    normKernelSubgroup (Gal(L / K)) (Multiplicative Int) = ⊥ := by
  let := galoisGroupValueGroupMulDistribMulAction K L
  apply le_antisymm
  · intro x hx
    rw [Subgroup.mem_bot]
    exact congrArg Multiplicative.ofAdd (by
      change Multiplicative.toAdd (x : Multiplicative Int) = 0
      have hnorm :
          (Fintype.card (Gal(L / K)) : Int) *
              Multiplicative.toAdd (x : Multiplicative Int) = 0 := by
        rw [← galoisGroupValueGroup_tateNorm_toAdd K L]
        exact congrArg Multiplicative.toAdd hx
      exact (mul_eq_zero.mp hnorm).resolve_left (by
        exact_mod_cast Fintype.card_ne_zero))
  · exact bot_le

/-- Finiteness of value-group `H⁻¹`, derived from the vanishing of its
norm kernel. -/
theorem galoisGroupValueGroupHerbrandHMinusOneFinite
    (σ : Gal(L / K)) :
    letI := galoisGroupValueGroupMulDistribMulAction K L
    Finite
      (HerbrandHMinusOne (Gal(L / K)) (Multiplicative Int) σ) := by
  let := galoisGroupValueGroupMulDistribMulAction K L
  have : Subsingleton
      (normKernelSubgroup (Gal(L / K)) (Multiplicative Int)) := by
    rw [galoisGroupValueGroup_normKernelSubgroup_eq_bot K L]
    infer_instance
  let : Subsingleton
      (HerbrandHMinusOne (Gal(L / K)) (Multiplicative Int) σ) :=
    ⟨fun q =>
      HerbrandHMinusOne.inductionOn σ
        (motive := fun q => ∀ r, q = r) q fun x r =>
          HerbrandHMinusOne.inductionOn σ
            (motive := fun r => HerbrandHMinusOne.mk σ x = r) r fun y =>
              congrArg (fun z => HerbrandHMinusOne.mk σ z)
                (Subsingleton.elim x y)⟩
  exact Finite.of_injective
    (fun _ : HerbrandHMinusOne (Gal(L / K))
      (Multiplicative Int) σ => false)
    (fun x y _ => Subsingleton.elim x y)

end
end LocalClassFieldTheory
end

section
-- module Solutions.OAIQ244_DUKE.LocalClassFieldTheory_ClassFormation_ValuationHerbrand
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.RamificationTheory.HilbertRamification.ValuationSubring.selectedResidueField.instAlgebra _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.CyclicCohomology.binaryCoefficientFamilyCommGroup _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.relativeAdeleRingIntermediateAlgebra _root_.relativeAdeleRingTopIntermediateAlgebra
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

namespace LocalClassFieldTheory

open LocalFieldTheory

open CyclicCohomology

/-!
# The valuation sequence and Herbrand quotients

This file applies the Herbrand-quotient multiplicativity theorem to the actual
valuation sequence from integer units through field units to the value group.

All three actions are the concrete actions from `ValuationReal`: the Galois
action on integer and field units, and the trivial action on the value group.
-/

noncomputable section

open scoped ValuativeRel
open CyclicCohomology.ProfiniteCohomology.Herbrand
open IsNonarchimedeanLocalField

variable (K L : Type) [Field K] [ValuativeRel K]
  [Field L] [ValuativeRel L] [TopologicalSpace L]
  [IsNonarchimedeanLocalField L] [Algebra K L] [FiniteDimensional K L]
  [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]
  [IsIntegralClosure (ValuativeRel.valuation L).integer
    (ValuativeRel.valuation K).integer L]

omit [ValuativeRel K] [ValuativeRel L] [TopologicalSpace L]
    [IsNonarchimedeanLocalField L]
    [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]
    [IsIntegralClosure (ValuativeRel.valuation L).integer
      (ValuativeRel.valuation K).integer L] in
/-- The Herbrand quotient of the trivially acted-on value group is defined:
its degree-zero group is finite cyclic and its degree-minus-one group is
trivial. -/
theorem galoisGroupValueGroup_herbrandQuotientDefined
    (g : Gal(L / K)) :
    letI := galoisGroupValueGroupMulDistribMulAction K L
    HerbrandQuotientDefined (Gal(L / K)) (Multiplicative Int) g := by
  exact ⟨galoisGroupValueGroupHerbrandH0Finite K L,
    galoisGroupValueGroupHerbrandHMinusOneFinite K L g⟩

end
end LocalClassFieldTheory
end

section
-- module Solutions.OAIQ244_DUKE.LocalClassFieldTheory_ClassFormation_NormalBasisInfiniteProduct
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.LubinTate.Valuations.exponentialValuationSubringIsLocalRing _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionFixedSubring.instIsLocalRing _root_.RamificationTheory.HilbertRamification.ValuationSubring.selectedResidueField.instAlgebra _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.maximalIdealPowSuccQuotModule _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.isDomain _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.isLocalRing _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.relativeAdeleRingIntermediateAlgebra _root_.relativeAdeleRingTopIntermediateAlgebra
attribute [-simp] _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.CyclicCohomology.integerUnitsModPrincipalUnitsAtLevelConcreteEquiv_mk _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.LocalClassFieldTheory.chosenNormalBasisPrincipalUnitSubgroupMulDistribMulAction_smul _root_.LocalClassFieldTheory.chosenNormalBasisPrincipalUnitSubgroup_sigmaMinusOne_coe _root_.LocalClassFieldTheory.chosenNormalBasisPrincipalUnitSubgroup_tateNorm_coe _root_.LocalFieldTheory.maximalIdealPowMapOfUnramifiedValuation_apply _root_.LocalFieldTheory.principalUnitsMapOfUnramifiedValuation_apply _root_.LocalFieldTheory.principalUnitsSuccQuotMapOfUnramifiedValuation_mk
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false
/-! Provides the public declarations in the `LocalClassFieldTheory.ClassFormation.NormalBasisInfiniteProduct` Lean module. -/

namespace LocalClassFieldTheory
open CyclicCohomology

open CyclicCohomology LocalFieldTheory

noncomputable section

universe u

open scoped BigOperators
open scoped ValuativeRel
open Filter IsNonarchimedeanLocalField
open CyclicCohomology.ProfiniteCohomology.Herbrand

variable (K L : Type u) [Field K] [Field L] [Algebra K L]
  [FiniteDimensional K L] [IsGalois K L]
  [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [ValuativeRel L]
  [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]

omit [FiniteDimensional K L] [IsGalois K L] in
/-- An element of `π_K^m 𝒪_L`, viewed in `L`, is represented by an
element of `𝓂_L^m`.  This is the valuation-extension bridge needed to turn
normal-basis corrections into the usual principal-unit corrections. -/
theorem chosenBaseUniformizerPow_integerRingFieldSubmodule_exists_mem_maximalIdeal_pow
    (m : Nat) {x : L}
    (hx : x ∈ chosenBaseUniformizerPowSubmodule K L m
      (integerRingFieldSubmodule K L)) :
    ∃ a : 𝒪[L], a ∈ (𝓂[L] ^ m : Ideal 𝒪[L]) ∧ (a : L) = x := by
  rcases (mem_chosenBaseUniformizerPowSubmodule_iff
      (K := K) (L := L) m (integerRingFieldSubmodule K L) x).1 hx with
    ⟨y, hy, rfl⟩
  let yInt : 𝒪[L] := ⟨y,
    (mem_integerRingFieldSubmodule_iff (K := K) (L := L) y).1 hy⟩
  let πL : 𝒪[L] :=
    integerRingMapOfValuationExtension K L (chosenIntegerRingUniformizer K)
  have hπL : πL ∈ (𝓂[L] : Ideal 𝒪[L]) := by
    exact integerRingMap_uniformizer_mem_maximalIdeal_of_valuationExtension
      (K := K) (L := L)
  refine ⟨πL ^ m * yInt, ?_, ?_⟩
  · exact Ideal.mul_mem_right yInt _ (Ideal.pow_mem_pow hπL m)
  · dsimp [πL, yInt]
    rw [map_pow]
    rfl

/-- Once `π_K^bM ⊆ 𝒪_L` and `b+1 ≤ n`, a correction in
`V^(n+i)` is an honest element of the usual principal-unit group `U_L^(i+1)`. -/
theorem chosenNormalBasisPrincipalUnitSet_mem_principalUnits_succ_of_lattice_bound
    {b n i : Nat}
    (hb : chosenBaseUniformizerPowSubmodule K L b
        (chosenNormalBasisIntegerLattice K L) ≤
      integerRingFieldSubmodule K L)
    (hbn : b + 1 ≤ n) {z : 𝒪[L]ˣ}
    (hz : z ∈ chosenNormalBasisPrincipalUnitSet K L (n + i)) :
    z ∈ principalUnits L (1 + i) := by
  rcases Nat.exists_eq_add_of_le hbn with ⟨r, rfl⟩
  let x : L := ((((z : 𝒪[L]ˣ) : 𝒪[L]) - 1 : 𝒪[L]) : L)
  have hxdeep : x ∈ chosenBaseUniformizerPowSubmodule K L
      (b + ((1 + r) + i)) (chosenNormalBasisIntegerLattice K L) := by
    simpa [x, Nat.add_assoc] using hz
  have hxint : x ∈ chosenBaseUniformizerPowSubmodule K L ((1 + r) + i)
      (integerRingFieldSubmodule K L) :=
    chosenBaseUniformizerPowSubmodule_add_le_chosenBaseUniformizerPowSubmodule_of_le
      (K := K) (L := L) (a := b) (n := (1 + r) + i) hb hxdeep
  rcases chosenBaseUniformizerPow_integerRingFieldSubmodule_exists_mem_maximalIdeal_pow
      (K := K) (L := L) ((1 + r) + i) hxint with ⟨a, ha, hax⟩
  have hpow : (𝓂[L] ^ ((1 + r) + i) : Ideal 𝒪[L]) ≤
      (𝓂[L] ^ (1 + i) : Ideal 𝒪[L]) := by
    apply Ideal.pow_le_pow_right
    exact Nat.add_le_add_right (Nat.le_add_right 1 r) i
  have ha' : a ∈ (𝓂[L] ^ (1 + i) : Ideal 𝒪[L]) := hpow ha
  rw [mem_principalUnits_iff]
  have haeq : a = ((z : 𝒪[L]ˣ) : 𝒪[L]) - 1 := by
    apply Subtype.ext
    simpa [x] using hax
  simpa [haeq] using ha'

/-- Regard a normal-basis correction sequence as the usual sequence of
successively deeper principal units. -/
def chosenNormalBasisPrincipalUnitSequenceAsPrincipalUnits
    {b n : Nat}
    (hb : chosenBaseUniformizerPowSubmodule K L b
        (chosenNormalBasisIntegerLattice K L) ≤
      integerRingFieldSubmodule K L)
    (hbn : b + 1 ≤ n) (z : Nat → 𝒪[L]ˣ)
    (hz : ∀ i : Nat, z i ∈ chosenNormalBasisPrincipalUnitSet K L (n + i))
    (i : Nat) : principalUnits L (1 + i) :=
  ⟨z i,
    chosenNormalBasisPrincipalUnitSet_mem_principalUnits_succ_of_lattice_bound
      (K := K) (L := L) hb hbn (hz i)⟩

/-- Coercing the principal-unit sequence returns the original normal-basis correction term. -/
@[simp]
theorem chosenNormalBasisPrincipalUnitSequenceAsPrincipalUnits_val
    {b n : Nat}
    (hb : chosenBaseUniformizerPowSubmodule K L b
        (chosenNormalBasisIntegerLattice K L) ≤
      integerRingFieldSubmodule K L)
    (hbn : b + 1 ≤ n) (z : Nat → 𝒪[L]ˣ)
    (hz : ∀ i : Nat, z i ∈ chosenNormalBasisPrincipalUnitSet K L (n + i))
    (i : Nat) :
    (chosenNormalBasisPrincipalUnitSequenceAsPrincipalUnits K L hb hbn z hz i : 𝒪[L]ˣ) = z i :=
  rfl

/-- The empty normal-basis correction product is the identity unit. -/
@[simp]
theorem chosenNormalBasisPrincipalUnitCorrectionProduct_zero (z : Nat → 𝒪[L]ˣ) :
    chosenNormalBasisPrincipalUnitCorrectionProduct (L := L) z 0 = 1 :=
  rfl

/-- A successor correction product appends the correction at the preceding index. -/
@[simp]
theorem chosenNormalBasisPrincipalUnitCorrectionProduct_succ
    (z : Nat → 𝒪[L]ˣ) (d : Nat) :
    chosenNormalBasisPrincipalUnitCorrectionProduct (L := L) z (d + 1) =
      chosenNormalBasisPrincipalUnitCorrectionProduct (L := L) z d * z d :=
  rfl

/-- The normal-basis partial products are definitionally the standard
principal-unit correction products after the lattice-to-ideal bridge. -/
theorem chosenNormalBasisPrincipalUnitCorrectionProduct_eq_principalUnitsCorrectionProduct
    {b n : Nat}
    (hb : chosenBaseUniformizerPowSubmodule K L b
        (chosenNormalBasisIntegerLattice K L) ≤
      integerRingFieldSubmodule K L)
    (hbn : b + 1 ≤ n) (z : Nat → 𝒪[L]ˣ)
    (hz : ∀ i : Nat, z i ∈ chosenNormalBasisPrincipalUnitSet K L (n + i))
    (d : Nat) :
    chosenNormalBasisPrincipalUnitCorrectionProduct (L := L) z d =
      principalUnitsCorrectionProduct L 1
        (chosenNormalBasisPrincipalUnitSequenceAsPrincipalUnits K L hb hbn z hz) d := by
  induction d with
  | zero => rfl
  | succ d ih =>
      rw [chosenNormalBasisPrincipalUnitCorrectionProduct_succ,
        principalUnitsCorrectionProduct_succ, ih]
      rfl

omit [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)] in

/-- If `V^n` is multiplicatively closed, every finite correction product
stays in `V^n`. -/
theorem chosenNormalBasisPrincipalUnitCorrectionProduct_mem
    {n : Nat}
    (hmul : ∀ u : 𝒪[L]ˣ, u ∈ chosenNormalBasisPrincipalUnitSet K L n →
      ∀ v : 𝒪[L]ˣ, v ∈ chosenNormalBasisPrincipalUnitSet K L n →
        u * v ∈ chosenNormalBasisPrincipalUnitSet K L n)
    (z : Nat → 𝒪[L]ˣ)
    (hz : ∀ i : Nat, z i ∈ chosenNormalBasisPrincipalUnitSet K L (n + i))
    (d : Nat) :
    chosenNormalBasisPrincipalUnitCorrectionProduct (L := L) z d ∈
      chosenNormalBasisPrincipalUnitSet K L n := by
  induction d with
  | zero =>
      exact chosenNormalBasisPrincipalUnitSet_one_mem (K := K) (L := L) n
  | succ d ih =>
      rw [chosenNormalBasisPrincipalUnitCorrectionProduct_succ]
      apply hmul _ ih (z d)
      exact chosenBaseUniformizerPowSubmodule_antitone
        (K := K) (L := L) (chosenNormalBasisIntegerLattice K L)
        (Nat.le_add_right n d) (hz d)

omit [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)] in

/-- A unit-valued limit of partial products remains in the initial
normal-basis filtration level whenever that lattice is closed. -/
theorem chosenNormalBasisPrincipalUnitCorrectionProduct_limit_mem
    [UniformSpace L] [IsUniformAddGroup L] [IsNonarchimedeanLocalField L]
    {n : Nat}
    (hclosed : IsClosed
      ((chosenBaseUniformizerPowSubmodule K L n
        (chosenNormalBasisIntegerLattice K L) : Set L)))
    (hmul : ∀ u : 𝒪[L]ˣ, u ∈ chosenNormalBasisPrincipalUnitSet K L n →
      ∀ v : 𝒪[L]ˣ, v ∈ chosenNormalBasisPrincipalUnitSet K L n →
        u * v ∈ chosenNormalBasisPrincipalUnitSet K L n)
    (z : Nat → 𝒪[L]ˣ)
    (hz : ∀ i : Nat, z i ∈ chosenNormalBasisPrincipalUnitSet K L (n + i))
    (x : 𝒪[L]ˣ)
    (hx : Tendsto
      (fun d : Nat =>
        ((chosenNormalBasisPrincipalUnitCorrectionProduct (L := L) z d : 𝒪[L]ˣ) :
          𝒪[L]))
      atTop (nhds ((x : 𝒪[L]ˣ) : 𝒪[L]))) :
    x ∈ chosenNormalBasisPrincipalUnitSet K L n := by
  have hxL : Tendsto
      (fun d : Nat =>
        (((chosenNormalBasisPrincipalUnitCorrectionProduct (L := L) z d : 𝒪[L]ˣ) :
          𝒪[L]) : L))
      atTop (nhds ((((x : 𝒪[L]ˣ) : 𝒪[L])) : L)) :=
    (continuous_subtype_val.tendsto ((x : 𝒪[L]ˣ) : 𝒪[L])).comp hx
  have hsub : Tendsto
      (fun d : Nat =>
        (((((chosenNormalBasisPrincipalUnitCorrectionProduct (L := L) z d : 𝒪[L]ˣ) :
          𝒪[L]) - 1 : 𝒪[L]) : L)))
      atTop (nhds (((((x : 𝒪[L]ˣ) : 𝒪[L]) - 1 : 𝒪[L]) : L))) := by
    simpa using hxL.sub (tendsto_const_nhds (x := (1 : L)))
  rw [mem_chosenNormalBasisPrincipalUnitSet_iff]
  exact submodule_mem_of_tendsto_of_forall_mem_of_closed
    (K := K) (L := L) hclosed hsub
    (fun d => chosenNormalBasisPrincipalUnitCorrectionProduct_mem
      (K := K) (L := L) hmul z hz d)

end
end LocalClassFieldTheory
end

section
-- module Solutions.OAIQ244_DUKE.LocalClassFieldTheory_ClassFormation_NormalBasis
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.LubinTate.Valuations.exponentialValuationSubringIsLocalRing _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionFixedSubring.instIsLocalRing _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionResidueField.instField _root_.RamificationTheory.HilbertRamification.ValuationSubring.selectedResidueField.instAlgebra _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.RelativeIdeleGroup.relativeIdeleMulAction _root_.ValuationTheory.DiscreteValuationField.DVF.maximalIdealPowSuccQuotModule _root_.ValuationTheory.DiscreteValuationField.DVF.residueField.field _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.isDomain _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.isLocalRing _root_.CyclicCohomology.binaryCoefficientFamilyCommGroup _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.relativeAdeleRingIntermediateAlgebra _root_.relativeAdeleRingTopIntermediateAlgebra
attribute [-simp] _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.LocalClassFieldTheory.chosenNormalBasisPrincipalUnitSequenceAsPrincipalUnits_val
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false
/-! Provides the public declarations in the `LocalClassFieldTheory.ClassFormation.NormalBasis` Lean module. -/

namespace LocalClassFieldTheory

open LocalFieldTheory

open CyclicCohomology

noncomputable section

universe u

open scoped ValuativeRel

variable (K L : Type u) [Field K] [ValuativeRel K] [Field L]
  [Algebra K L] [FiniteDimensional K L] [IsGalois K L]

/-- The two descriptions of the standard lattice use the same normal-basis orbit. -/
theorem span_normalBasis_eq_chosenNormalBasisIntegerLattice :
    Submodule.span 𝒪[K] (Set.range (IsGalois.normalBasis K L)) =
      chosenNormalBasisIntegerLattice K L := by
  rw [chosenNormalBasisIntegerLattice_eq_span]
  congr 1
  ext y
  constructor
  · rintro ⟨σ, rfl⟩
    exact ⟨σ, (IsGalois.normalBasis_apply (K := K) (L := L) σ).symm⟩
  · rintro ⟨σ, rfl⟩
    exact ⟨σ, IsGalois.normalBasis_apply (K := K) (L := L) σ⟩

/-- The normal-basis orbit is an `𝒪_K`-basis of the standard lattice `M`.
This is the coordinate source for the induced-module calculation in the local
class-field-axiom proof. -/
noncomputable def chosenNormalBasisIntegerLatticeBasis :
    Module.Basis Gal(L / K) 𝒪[K] (chosenNormalBasisIntegerLattice K L) :=
  ((IsGalois.normalBasis K L).restrictScalars 𝒪[K]).map
    (LinearEquiv.ofEq _ _
      (span_normalBasis_eq_chosenNormalBasisIntegerLattice K L))

/-- The integral lattice basis has the same underlying vectors as the chosen normal basis. -/
@[simp]
theorem chosenNormalBasisIntegerLatticeBasis_apply (σ : Gal(L / K)) :
    ((chosenNormalBasisIntegerLatticeBasis K L σ :
      chosenNormalBasisIntegerLattice K L) : L) = IsGalois.normalBasis K L σ := by
  simp [chosenNormalBasisIntegerLatticeBasis, LinearEquiv.coe_ofEq_apply]

section GradedCoordinates

variable [TopologicalSpace K] [IsNonarchimedeanLocalField K]

/-- Multiplication by `π_K^n`, from the normal-basis lattice onto its
`n`-th dilate. -/
def chosenNormalBasisIntegerLatticeMulPowLinearMap (n : Nat) :
    chosenNormalBasisIntegerLattice K L →ₗ[𝒪[K]]
      chosenBaseUniformizerPowSubmodule K L n (chosenNormalBasisIntegerLattice K L) where
  toFun x :=
    ⟨algebraMap 𝒪[K] L (chosenIntegerRingUniformizer K ^ n) * (x : L),
      (mem_chosenBaseUniformizerPowSubmodule_iff
        (K := K) (L := L) n (chosenNormalBasisIntegerLattice K L) _).2
        ⟨x, x.2, rfl⟩⟩
  map_add' := by
    intro x y
    ext
    exact mul_add _ _ _
  map_smul' := by
    intro a x
    ext
    simp [Algebra.smul_def, mul_assoc, mul_comm, mul_left_comm]

/-- Uniformizer-power scaling bijects the integral lattice with its scaled copy. -/
theorem chosenNormalBasisIntegerLatticeMulPowLinearMap_bijective (n : Nat) :
    Function.Bijective (chosenNormalBasisIntegerLatticeMulPowLinearMap K L n) := by
  constructor
  · intro x y hxy
    apply Subtype.ext
    have hxy' := congrArg Subtype.val hxy
    change algebraMap 𝒪[K] L (chosenIntegerRingUniformizer K ^ n) * (x : L) =
      algebraMap 𝒪[K] L (chosenIntegerRingUniformizer K ^ n) * (y : L) at hxy'
    have hπ : chosenIntegerRingUniformizer K ^ n ≠ 0 :=
      pow_ne_zero n (chosenIntegerRingUniformizer_irreducible K).ne_zero
    have hπL : algebraMap 𝒪[K] L (chosenIntegerRingUniformizer K ^ n) ≠ 0 := by
      change algebraMap K L
          ((chosenIntegerRingUniformizer K ^ n : 𝒪[K]) : K) ≠ 0
      apply (map_ne_zero (algebraMap K L)).2
      intro h
      exact hπ ((IsFractionRing.injective 𝒪[K] K) h)
    exact mul_left_cancel₀ hπL hxy'
  · intro x
    rcases (mem_chosenBaseUniformizerPowSubmodule_iff
      (K := K) (L := L) n (chosenNormalBasisIntegerLattice K L) (x : L)).1 x.2 with
      ⟨y, hy, hxy⟩
    refine ⟨⟨y, hy⟩, ?_⟩
    apply Subtype.ext
    exact hxy

/-- Multiplication by `π_K^n` as an `𝒪_K`-linear equivalence of the
normal-basis lattice with its `n`-th dilate. -/
noncomputable def chosenNormalBasisIntegerLatticeMulPowLinearEquiv (n : Nat) :
    chosenNormalBasisIntegerLattice K L ≃ₗ[𝒪[K]]
      chosenBaseUniformizerPowSubmodule K L n (chosenNormalBasisIntegerLattice K L) :=
  LinearEquiv.ofBijective (chosenNormalBasisIntegerLatticeMulPowLinearMap K L n)
    (chosenNormalBasisIntegerLatticeMulPowLinearMap_bijective K L n)

/-- The scaling equivalence acts by multiplication by the chosen uniformizer power. -/
@[simp]
theorem chosenNormalBasisIntegerLatticeMulPowLinearEquiv_apply
    (n : Nat) (x : chosenNormalBasisIntegerLattice K L) :
    ((chosenNormalBasisIntegerLatticeMulPowLinearEquiv K L n x :
      chosenBaseUniformizerPowSubmodule K L n (chosenNormalBasisIntegerLattice K L)) : L) =
      algebraMap 𝒪[K] L (chosenIntegerRingUniformizer K ^ n) * (x : L) :=
  rfl

/-- The first uniformizer layer `π_K M`, regarded as a submodule of the
normal-basis lattice `M`. -/
def chosenNormalBasisIntegerLatticeUniformizerSubmodule :
    Submodule 𝒪[K] (chosenNormalBasisIntegerLattice K L) :=
  (chosenBaseUniformizerPowSubmodule K L 1
      (chosenNormalBasisIntegerLattice K L)).comap
    (chosenNormalBasisIntegerLattice K L).subtype

/-- Membership in the lattice uniformizer submodule is detected after coercion to the field. -/
@[simp]
theorem mem_chosenNormalBasisIntegerLatticeUniformizerSubmodule_iff
    (x : chosenNormalBasisIntegerLattice K L) :
    x ∈ chosenNormalBasisIntegerLatticeUniformizerSubmodule K L ↔
      (x : L) ∈ chosenBaseUniformizerPowSubmodule K L 1
        (chosenNormalBasisIntegerLattice K L) :=
  Iff.rfl

/-- Scaling maps the uniformizer submodule onto the next normal-basis lattice. -/
theorem chosenNormalBasisIntegerLatticeUniformizerSubmodule_map_mulPow
    (n : Nat) :
    (chosenNormalBasisIntegerLatticeUniformizerSubmodule K L).map
        (chosenNormalBasisIntegerLatticeMulPowLinearEquiv K L n :
          chosenNormalBasisIntegerLattice K L →ₗ[𝒪[K]]
            chosenBaseUniformizerPowSubmodule K L n
              (chosenNormalBasisIntegerLattice K L)) =
      chosenNormalBasisLatticeSuccSubmodule K L n := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    change algebraMap 𝒪[K] L (chosenIntegerRingUniformizer K ^ n) * (y : L) ∈
      chosenBaseUniformizerPowSubmodule K L (n + 1)
        (chosenNormalBasisIntegerLattice K L)
    rcases (mem_chosenBaseUniformizerPowSubmodule_iff
      (K := K) (L := L) 1 (chosenNormalBasisIntegerLattice K L) (y : L)).1 hy with
      ⟨z, hz, hzy⟩
    refine (mem_chosenBaseUniformizerPowSubmodule_iff
      (K := K) (L := L) (n + 1) (chosenNormalBasisIntegerLattice K L) _).2
      ⟨z, hz, ?_⟩
    rw [← hzy]
    simp only [pow_succ, pow_zero, map_mul, one_mul]
    ring
  · intro hx
    change (x : L) ∈ chosenBaseUniformizerPowSubmodule K L (n + 1)
      (chosenNormalBasisIntegerLattice K L) at hx
    rcases (mem_chosenBaseUniformizerPowSubmodule_iff
      (K := K) (L := L) (n + 1) (chosenNormalBasisIntegerLattice K L) (x : L)).1 hx with
      ⟨z, hz, hzx⟩
    let y : chosenNormalBasisIntegerLattice K L :=
      ⟨algebraMap 𝒪[K] L (chosenIntegerRingUniformizer K) * z, by
        simpa [Algebra.smul_def] using
          (chosenNormalBasisIntegerLattice K L).smul_mem
            (chosenIntegerRingUniformizer K) hz⟩
    have hy : y ∈ chosenNormalBasisIntegerLatticeUniformizerSubmodule K L := by
      refine (mem_chosenBaseUniformizerPowSubmodule_iff
        (K := K) (L := L) 1 (chosenNormalBasisIntegerLattice K L) (y : L)).2
        ⟨z, hz, ?_⟩
      simp [y]
    refine ⟨y, hy, ?_⟩
    apply Subtype.ext
    change algebraMap 𝒪[K] L (chosenIntegerRingUniformizer K ^ n) * (y : L) =
      (x : L)
    rw [← hzx]
    simp only [y, pow_succ, map_mul]
    ring

/-- Removing the common factor `π_K^n` identifies the `n`-th lattice graded
piece with the fixed quotient `M / π_K M`. -/
noncomputable def chosenNormalBasisLatticeSuccQuotToIntegerLatticeQuotLinearEquiv
    (n : Nat) :
    chosenNormalBasisLatticeSuccQuot K L n ≃ₗ[𝒪[K]]
      (chosenNormalBasisIntegerLattice K L ⧸
        chosenNormalBasisIntegerLatticeUniformizerSubmodule K L) :=
  (chosenNormalBasisLatticeSuccQuotConcreteLinearEquiv K L n).trans
    (Submodule.Quotient.equiv
      (chosenNormalBasisIntegerLatticeUniformizerSubmodule K L)
      (chosenNormalBasisLatticeSuccSubmodule K L n)
      (chosenNormalBasisIntegerLatticeMulPowLinearEquiv K L n)
      (chosenNormalBasisIntegerLatticeUniformizerSubmodule_map_mulPow K L n)).symm

/-- Removing the common uniformizer power sends a scaled representative to its integral class. -/
@[simp]
theorem chosenNormalBasisLatticeSuccQuotToIntegerLatticeQuotLinearEquiv_mk_mulPow
    (n : Nat) (x : chosenNormalBasisIntegerLattice K L) :
    chosenNormalBasisLatticeSuccQuotToIntegerLatticeQuotLinearEquiv K L n
        (chosenNormalBasisLatticeSuccQuotMk K L n
          (chosenNormalBasisIntegerLatticeMulPowLinearEquiv K L n x)) =
      Submodule.Quotient.mk x := by
  let e := Submodule.Quotient.equiv
    (chosenNormalBasisIntegerLatticeUniformizerSubmodule K L)
    (chosenNormalBasisLatticeSuccSubmodule K L n)
    (chosenNormalBasisIntegerLatticeMulPowLinearEquiv K L n)
    (chosenNormalBasisIntegerLatticeUniformizerSubmodule_map_mulPow K L n)
  change
    e.symm
        (chosenNormalBasisLatticeSuccQuotConcreteLinearEquiv K L n
          (chosenNormalBasisLatticeSuccQuotMk K L n
            (chosenNormalBasisIntegerLatticeMulPowLinearEquiv K L n x))) =
      Submodule.Quotient.mk x
  rw [chosenNormalBasisLatticeSuccQuotConcreteLinearEquiv_mk]
  apply e.injective
  rw [LinearEquiv.apply_symm_apply]
  rfl

omit [FiniteDimensional K L] [IsGalois K L] in
/-- A coordinate function lies in the maximal submodule exactly when every value is nonunit. -/
@[simp]
theorem mem_chosenNormalBasisCoordinateMaximalSubmodule_iff
    (f : Gal(L / K) → 𝒪[K]) :
    f ∈ chosenNormalBasisCoordinateMaximalSubmodule K L ↔
      ∀ σ : Gal(L / K), f σ ∈ (𝓂[K] : Ideal 𝒪[K]) := by
  simp [chosenNormalBasisCoordinateMaximalSubmodule]

/-- Normal-basis coordinates identify the uniformizer submodule with pointwise maximal-ideal values. -/
theorem chosenNormalBasisIntegerLatticeUniformizerSubmodule_map_equivFun :
    (chosenNormalBasisIntegerLatticeUniformizerSubmodule K L).map
        ((chosenNormalBasisIntegerLatticeBasis K L).equivFun :
          chosenNormalBasisIntegerLattice K L →ₗ[𝒪[K]] (Gal(L / K) → 𝒪[K])) =
      chosenNormalBasisCoordinateMaximalSubmodule K L := by
  ext f
  constructor
  · rintro ⟨x, hx, rfl⟩
    rw [chosenNormalBasisCoordinateMaximalSubmodule, Submodule.mem_pi]
    intro σ _
    rcases (mem_chosenBaseUniformizerPowSubmodule_iff
      (K := K) (L := L) 1 (chosenNormalBasisIntegerLattice K L) (x : L)).1 hx with
      ⟨z, hz, hzx⟩
    let zM : chosenNormalBasisIntegerLattice K L := ⟨z, hz⟩
    have hx_eq : x = chosenIntegerRingUniformizer K • zM := by
      apply Subtype.ext
      simpa [Algebra.smul_def, zM] using hzx.symm
    rw [chosenIntegerRingUniformizer_maximalIdeal_eq,
      Ideal.mem_span_singleton']
    refine ⟨(chosenNormalBasisIntegerLatticeBasis K L).equivFun zM σ, ?_⟩
    rw [hx_eq]
    simp [mul_comm]
  · intro hf
    have hf' : ∀ σ : Gal(L / K),
        ∃ c : 𝒪[K], c * chosenIntegerRingUniformizer K = f σ := by
      intro σ
      have hσ := (Submodule.mem_pi.mp hf) σ (Set.mem_univ σ)
      rw [chosenIntegerRingUniformizer_maximalIdeal_eq,
        Ideal.mem_span_singleton'] at hσ
      exact hσ
    let c : Gal(L / K) → 𝒪[K] := fun σ => Classical.choose (hf' σ)
    have hc (σ : Gal(L / K)) :
        c σ * chosenIntegerRingUniformizer K = f σ :=
      Classical.choose_spec (hf' σ)
    let z : chosenNormalBasisIntegerLattice K L :=
      (chosenNormalBasisIntegerLatticeBasis K L).equivFun.symm c
    let x : chosenNormalBasisIntegerLattice K L :=
      chosenIntegerRingUniformizer K • z
    have hx : x ∈ chosenNormalBasisIntegerLatticeUniformizerSubmodule K L := by
      refine (mem_chosenBaseUniformizerPowSubmodule_iff
        (K := K) (L := L) 1 (chosenNormalBasisIntegerLattice K L) (x : L)).2
        ⟨z, z.2, ?_⟩
      simp [x, Algebra.smul_def]
    refine ⟨x, hx, ?_⟩
    funext σ
    have hzcoord :
        (chosenNormalBasisIntegerLatticeBasis K L).equivFun z = c :=
      (chosenNormalBasisIntegerLatticeBasis K L).equivFun.apply_symm_apply c
    calc
      (chosenNormalBasisIntegerLatticeBasis K L).equivFun x σ =
          chosenIntegerRingUniformizer K *
            (chosenNormalBasisIntegerLatticeBasis K L).equivFun z σ := by
        simp [x]
      _ = chosenIntegerRingUniformizer K * c σ := by rw [hzcoord]
      _ = f σ := by rw [mul_comm, hc]

/-- Normal-basis coordinates identify `M / π_K M` with the coordinatewise
maximal-ideal quotient. -/
noncomputable def chosenNormalBasisIntegerLatticeQuotCoordinateQuotLinearEquiv :
    (chosenNormalBasisIntegerLattice K L ⧸
        chosenNormalBasisIntegerLatticeUniformizerSubmodule K L) ≃ₗ[𝒪[K]]
      ((Gal(L / K) → 𝒪[K]) ⧸ chosenNormalBasisCoordinateMaximalSubmodule K L) :=
  Submodule.Quotient.equiv
    (chosenNormalBasisIntegerLatticeUniformizerSubmodule K L)
    (chosenNormalBasisCoordinateMaximalSubmodule K L)
    (chosenNormalBasisIntegerLatticeBasis K L).equivFun
    (chosenNormalBasisIntegerLatticeUniformizerSubmodule_map_equivFun K L)

/-- Quotienting coordinate functions by the pointwise maximal ideal is the
function space with values in `𝒪_K / 𝓂_K`. -/
noncomputable def chosenNormalBasisCoordinateQuotPiLinearEquiv :
    ((Gal(L / K) → 𝒪[K]) ⧸ chosenNormalBasisCoordinateMaximalSubmodule K L) ≃ₗ[𝒪[K]]
      (Gal(L / K) → (𝒪[K] ⧸ (𝓂[K] : Ideal 𝒪[K]))) := by
  classical
  exact Submodule.quotientPi (fun _ : Gal(L / K) => (𝓂[K] : Ideal 𝒪[K]))

omit [IsGalois K L] in
/-- The coordinate quotient equivalence sends a representative to its pointwise residue classes. -/
@[simp]
theorem chosenNormalBasisCoordinateQuotPiLinearEquiv_mk
    (f : Gal(L / K) → 𝒪[K]) :
    chosenNormalBasisCoordinateQuotPiLinearEquiv K L
        (Submodule.Quotient.mk f) =
      fun σ : Gal(L / K) => Submodule.Quotient.mk (f σ) :=
  rfl

/-- Apply `𝒪_K / 𝓂_K ≃ 𝓀_K` pointwise and reverse the Galois index.  The
inverse index converts the natural left-regular coordinate rule into the
right-regular convention used in the Herbrand calculation. -/
def chosenNormalBasisPiResidueInverseIndexAddEquiv :
    (Gal(L / K) → (𝒪[K] ⧸ (𝓂[K] : Ideal 𝒪[K]))) ≃+
      (Gal(L / K) → 𝓀[K]) where
  toFun f σ := integerRingModMaximalIdealAddEquivResidue K (f σ⁻¹)
  invFun f σ := (integerRingModMaximalIdealAddEquivResidue K).symm (f σ⁻¹)
  left_inv := by
    intro f
    funext σ
    simp
  right_inv := by
    intro f
    funext σ
    simp
  map_add' := by
    intro f g
    funext σ
    simp

omit [FiniteDimensional K L] [IsGalois K L] in
/-- The inverse-index equivalence evaluates a residue function at the inverse Galois element. -/
@[simp]
theorem chosenNormalBasisPiResidueInverseIndexAddEquiv_apply
    (f : Gal(L / K) → (𝒪[K] ⧸ (𝓂[K] : Ideal 𝒪[K])))
    (σ : Gal(L / K)) :
    chosenNormalBasisPiResidueInverseIndexAddEquiv K L f σ =
      integerRingModMaximalIdealAddEquivResidue K (f σ⁻¹) :=
  rfl

/-- The honest additive normal-basis model of the lattice graded piece
`π_K^n M / π_K^(n+1) M` as the right-regular function module over the residue
field. -/
noncomputable def chosenNormalBasisLatticeSuccQuotRightRegularAddEquiv (n : Nat) :
    chosenNormalBasisLatticeSuccQuot K L n ≃+ (Gal(L / K) → 𝓀[K]) :=
  (chosenNormalBasisLatticeSuccQuotToIntegerLatticeQuotLinearEquiv K L n).toAddEquiv.trans
    ((chosenNormalBasisIntegerLatticeQuotCoordinateQuotLinearEquiv K L).toAddEquiv.trans
      ((chosenNormalBasisCoordinateQuotPiLinearEquiv K L).toAddEquiv.trans
        (chosenNormalBasisPiResidueInverseIndexAddEquiv K L)))

/-- Computes right-regular residue coordinates of a scaled lattice representative. -/
@[simp]
theorem chosenNormalBasisLatticeSuccQuotRightRegularAddEquiv_mk_mulPow
    (n : Nat) (x : chosenNormalBasisIntegerLattice K L) (σ : Gal(L / K)) :
    chosenNormalBasisLatticeSuccQuotRightRegularAddEquiv K L n
        (chosenNormalBasisLatticeSuccQuotMk K L n
          (chosenNormalBasisIntegerLatticeMulPowLinearEquiv K L n x)) σ =
      IsLocalRing.residue 𝒪[K]
        ((chosenNormalBasisIntegerLatticeBasis K L).equivFun x σ⁻¹) := by
  rw [chosenNormalBasisLatticeSuccQuotRightRegularAddEquiv]
  simp [chosenNormalBasisIntegerLatticeQuotCoordinateQuotLinearEquiv,
    chosenNormalBasisCoordinateQuotPiLinearEquiv,
    chosenNormalBasisPiResidueInverseIndexAddEquiv]
  change integerRingModMaximalIdealAddEquivResidue K
      (Ideal.Quotient.mk (𝓂[K] : Ideal 𝒪[K])
        ((chosenNormalBasisIntegerLatticeBasis K L).equivFun x σ⁻¹)) = _
  rfl

/-! ### The actual `Gal(L / K)` action and right-regular equivariance -/

/-- The actual Galois action restricted to the stable normal-basis lattice. -/
def galoisGroupChosenNormalBasisIntegerLatticeLinearEquiv (τ : Gal(L / K)) :
    chosenNormalBasisIntegerLattice K L ≃ₗ[𝒪[K]]
      chosenNormalBasisIntegerLattice K L where
  toFun x := ⟨τ (x : L),
    galoisGroup_apply_mem_chosenNormalBasisIntegerLattice (K := K) (L := L) τ x.2⟩
  invFun x := ⟨τ⁻¹ (x : L),
    galoisGroup_apply_mem_chosenNormalBasisIntegerLattice (K := K) (L := L) τ⁻¹ x.2⟩
  left_inv x := by
    apply Subtype.ext
    exact τ.symm_apply_apply (x : L)
  right_inv x := by
    apply Subtype.ext
    exact τ.apply_symm_apply (x : L)
  map_add' x y := by
    apply Subtype.ext
    exact map_add τ (x : L) (y : L)
  map_smul' a x := by
    apply Subtype.ext
    have ha : τ (algebraMap 𝒪[K] L a) = algebraMap 𝒪[K] L a := by
      change τ (algebraMap K L (a : K)) = algebraMap K L (a : K)
      exact τ.commutes (a : K)
    change τ (((a • x : chosenNormalBasisIntegerLattice K L) : L)) =
      ((a • (⟨τ (x : L), galoisGroup_apply_mem_chosenNormalBasisIntegerLattice
        (K := K) (L := L) τ x.2⟩ : chosenNormalBasisIntegerLattice K L) :
          chosenNormalBasisIntegerLattice K L) : L)
    rw [Submodule.coe_smul, Submodule.coe_smul]
    rw [Algebra.smul_def, Algebra.smul_def]
    rw [map_mul, ha]

omit [TopologicalSpace K] [IsNonarchimedeanLocalField K] in
/-- The restricted lattice equivalence agrees with the ambient Galois action. -/
@[simp]
theorem galoisGroupChosenNormalBasisIntegerLatticeLinearEquiv_apply_coe
    (τ : Gal(L / K)) (x : chosenNormalBasisIntegerLattice K L) :
    ((galoisGroupChosenNormalBasisIntegerLatticeLinearEquiv K L τ x :
      chosenNormalBasisIntegerLattice K L) : L) = τ (x : L) :=
  rfl

omit [TopologicalSpace K] [IsNonarchimedeanLocalField K] in
/-- The identity Galois element acts trivially on the normal-basis lattice. -/
@[simp]
theorem galoisGroupChosenNormalBasisIntegerLatticeLinearEquiv_one_apply
    (x : chosenNormalBasisIntegerLattice K L) :
    galoisGroupChosenNormalBasisIntegerLatticeLinearEquiv K L 1 x = x := by
  apply Subtype.ext
  rfl

omit [TopologicalSpace K] [IsNonarchimedeanLocalField K] in
/-- Multiplication in the Galois group acts by composition on the normal-basis lattice. -/
@[simp]
theorem galoisGroupChosenNormalBasisIntegerLatticeLinearEquiv_mul_apply
    (τ υ : Gal(L / K)) (x : chosenNormalBasisIntegerLattice K L) :
    galoisGroupChosenNormalBasisIntegerLatticeLinearEquiv K L (τ * υ) x =
      galoisGroupChosenNormalBasisIntegerLatticeLinearEquiv K L τ
        (galoisGroupChosenNormalBasisIntegerLatticeLinearEquiv K L υ x) := by
  apply Subtype.ext
  rfl

omit [TopologicalSpace K] [IsNonarchimedeanLocalField K] in

/-- Normal-basis lattice coordinates obey the left-regular rule before the
inverse-index reindexing. -/
theorem chosenNormalBasisIntegerLatticeBasis_equivFun_galoisGroup
    (τ σ : Gal(L / K)) (x : chosenNormalBasisIntegerLattice K L) :
    (chosenNormalBasisIntegerLatticeBasis K L).equivFun
        (galoisGroupChosenNormalBasisIntegerLatticeLinearEquiv K L τ x) σ =
      (chosenNormalBasisIntegerLatticeBasis K L).equivFun x (τ⁻¹ * σ) := by
  let b := chosenNormalBasisIntegerLatticeBasis K L
  let f := galoisGroupChosenNormalBasisIntegerLatticeLinearEquiv K L τ
  let e : Gal(L / K) ≃ Gal(L / K) := Equiv.mulLeft τ⁻¹
  have hbmap : b.map f = b.reindex e := by
    ext ρ
    rw [Module.Basis.map_apply, Module.Basis.reindex_apply]
    have he : e.symm ρ = τ * ρ := by
      simp [e]
    rw [he]
    simp only [f, b, galoisGroupChosenNormalBasisIntegerLatticeLinearEquiv_apply_coe,
      chosenNormalBasisIntegerLatticeBasis_apply]
    rw [IsGalois.normalBasis_apply (K := K) (L := L) (τ * ρ),
      IsGalois.normalBasis_apply (K := K) (L := L) ρ]
    rfl
  have hcoord (ρ : Gal(L / K)) :
      b.equivFun (f x) (τ * ρ) = b.equivFun x ρ := by
    calc
      b.equivFun (f x) (τ * ρ) =
          (b.reindex e).equivFun (f x) ρ := by
            rw [Module.Basis.equivFun_apply, Module.Basis.equivFun_apply,
              Module.Basis.repr_reindex_apply]
            simp [e]
      _ = (b.map f).equivFun (f x) ρ := by rw [hbmap]
      _ = b.equivFun x ρ := by
        rw [Module.Basis.map_equivFun]
        simp [f]
  simpa using hcoord (τ⁻¹ * σ)

/-- The lattice uniformizer submodule is stable under every Galois automorphism. -/
theorem chosenNormalBasisIntegerLatticeUniformizerSubmodule_map_galoisGroup
    (τ : Gal(L / K)) :
    (chosenNormalBasisIntegerLatticeUniformizerSubmodule K L).map
        (galoisGroupChosenNormalBasisIntegerLatticeLinearEquiv K L τ :
          chosenNormalBasisIntegerLattice K L →ₗ[𝒪[K]]
            chosenNormalBasisIntegerLattice K L) =
      chosenNormalBasisIntegerLatticeUniformizerSubmodule K L := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    rcases (mem_chosenBaseUniformizerPowSubmodule_iff
      (K := K) (L := L) 1 (chosenNormalBasisIntegerLattice K L) (y : L)).1 hy with
      ⟨z, hz, hzy⟩
    refine (mem_chosenBaseUniformizerPowSubmodule_iff
      (K := K) (L := L) 1 (chosenNormalBasisIntegerLattice K L) _).2
      ⟨τ z, galoisGroup_apply_mem_chosenNormalBasisIntegerLattice
        (K := K) (L := L) τ hz, ?_⟩
    change algebraMap 𝒪[K] L (chosenIntegerRingUniformizer K ^ 1) * τ z = τ (y : L)
    rw [← hzy, map_mul]
    congr 1
    change algebraMap K L
        ((chosenIntegerRingUniformizer K ^ 1 : 𝒪[K]) : K) =
      τ (algebraMap K L
        ((chosenIntegerRingUniformizer K ^ 1 : 𝒪[K]) : K))
    exact (τ.commutes _).symm
  · intro hx
    let y := galoisGroupChosenNormalBasisIntegerLatticeLinearEquiv K L τ⁻¹ x
    have hy : y ∈ chosenNormalBasisIntegerLatticeUniformizerSubmodule K L := by
      rcases (mem_chosenBaseUniformizerPowSubmodule_iff
        (K := K) (L := L) 1 (chosenNormalBasisIntegerLattice K L) (x : L)).1 hx with
        ⟨z, hz, hzx⟩
      refine (mem_chosenBaseUniformizerPowSubmodule_iff
        (K := K) (L := L) 1 (chosenNormalBasisIntegerLattice K L) (y : L)).2
        ⟨τ⁻¹ z, galoisGroup_apply_mem_chosenNormalBasisIntegerLattice
          (K := K) (L := L) τ⁻¹ hz, ?_⟩
      change algebraMap 𝒪[K] L (chosenIntegerRingUniformizer K ^ 1) * τ⁻¹ z =
        τ⁻¹ (x : L)
      rw [← hzx, map_mul]
      congr 1
      change algebraMap K L
          ((chosenIntegerRingUniformizer K ^ 1 : 𝒪[K]) : K) =
        τ⁻¹ (algebraMap K L
          ((chosenIntegerRingUniformizer K ^ 1 : 𝒪[K]) : K))
      exact ((τ⁻¹).commutes _).symm
    refine ⟨y, hy, ?_⟩
    apply Subtype.ext
    exact τ.apply_symm_apply (x : L)

/-- The actual Galois action on the fixed quotient `M / π_K M`. -/
noncomputable def galoisGroupChosenNormalBasisIntegerLatticeQuotLinearEquiv
    (τ : Gal(L / K)) :
    (chosenNormalBasisIntegerLattice K L ⧸
        chosenNormalBasisIntegerLatticeUniformizerSubmodule K L) ≃ₗ[𝒪[K]]
      (chosenNormalBasisIntegerLattice K L ⧸
        chosenNormalBasisIntegerLatticeUniformizerSubmodule K L) :=
  Submodule.Quotient.equiv
    (chosenNormalBasisIntegerLatticeUniformizerSubmodule K L)
    (chosenNormalBasisIntegerLatticeUniformizerSubmodule K L)
    (galoisGroupChosenNormalBasisIntegerLatticeLinearEquiv K L τ)
    (chosenNormalBasisIntegerLatticeUniformizerSubmodule_map_galoisGroup K L τ)

/-- The induced quotient action sends a class to the class of its Galois transform. -/
@[simp]
theorem galoisGroupChosenNormalBasisIntegerLatticeQuotLinearEquiv_mk
    (τ : Gal(L / K)) (x : chosenNormalBasisIntegerLattice K L) :
    galoisGroupChosenNormalBasisIntegerLatticeQuotLinearEquiv K L τ
        (Submodule.Quotient.mk x) =
      Submodule.Quotient.mk
        (galoisGroupChosenNormalBasisIntegerLatticeLinearEquiv K L τ x) :=
  rfl

/-- The actual Galois action on `π_K^n M / π_K^(n+1) M`, transported through
removal of the common factor `π_K^n`. -/
noncomputable def galoisGroupChosenNormalBasisLatticeSuccQuotAddEquiv
    (n : Nat) (τ : Gal(L / K)) :
    chosenNormalBasisLatticeSuccQuot K L n ≃+
      chosenNormalBasisLatticeSuccQuot K L n :=
  (chosenNormalBasisLatticeSuccQuotToIntegerLatticeQuotLinearEquiv K L n).toAddEquiv.trans
    ((galoisGroupChosenNormalBasisIntegerLatticeQuotLinearEquiv K L τ).toAddEquiv.trans
      (chosenNormalBasisLatticeSuccQuotToIntegerLatticeQuotLinearEquiv K L n).symm.toAddEquiv)

/-- The transported Galois action transforms the integral part of a scaled representative. -/
@[simp]
theorem galoisGroupChosenNormalBasisLatticeSuccQuotAddEquiv_mk_mulPow
    (n : Nat) (τ : Gal(L / K)) (x : chosenNormalBasisIntegerLattice K L) :
    galoisGroupChosenNormalBasisLatticeSuccQuotAddEquiv K L n τ
        (chosenNormalBasisLatticeSuccQuotMk K L n
          (chosenNormalBasisIntegerLatticeMulPowLinearEquiv K L n x)) =
      chosenNormalBasisLatticeSuccQuotMk K L n
        (chosenNormalBasisIntegerLatticeMulPowLinearEquiv K L n
          (galoisGroupChosenNormalBasisIntegerLatticeLinearEquiv K L τ x)) := by
  let e := chosenNormalBasisLatticeSuccQuotToIntegerLatticeQuotLinearEquiv K L n
  change e.symm
      (galoisGroupChosenNormalBasisIntegerLatticeQuotLinearEquiv K L τ
        (e (chosenNormalBasisLatticeSuccQuotMk K L n
          (chosenNormalBasisIntegerLatticeMulPowLinearEquiv K L n x)))) = _
  rw [chosenNormalBasisLatticeSuccQuotToIntegerLatticeQuotLinearEquiv_mk_mulPow,
    galoisGroupChosenNormalBasisIntegerLatticeQuotLinearEquiv_mk]
  apply e.injective
  rw [LinearEquiv.apply_symm_apply,
    chosenNormalBasisLatticeSuccQuotToIntegerLatticeQuotLinearEquiv_mk_mulPow]

/-- Removing the common uniformizer power intertwines the two quotient Galois actions. -/
@[simp]
theorem chosenNormalBasisLatticeSuccQuotToIntegerLatticeQuotLinearEquiv_galoisGroup
    (n : Nat) (τ : Gal(L / K))
    (q : chosenNormalBasisLatticeSuccQuot K L n) :
    chosenNormalBasisLatticeSuccQuotToIntegerLatticeQuotLinearEquiv K L n
        (galoisGroupChosenNormalBasisLatticeSuccQuotAddEquiv K L n τ q) =
      galoisGroupChosenNormalBasisIntegerLatticeQuotLinearEquiv K L τ
        (chosenNormalBasisLatticeSuccQuotToIntegerLatticeQuotLinearEquiv K L n q) := by
  let e := chosenNormalBasisLatticeSuccQuotToIntegerLatticeQuotLinearEquiv K L n
  change e (e.symm
    (galoisGroupChosenNormalBasisIntegerLatticeQuotLinearEquiv K L τ (e q))) = _
  exact e.apply_symm_apply _

/-- On representatives, the transported action is multiplication by `π_K^n`
followed by the actual field automorphism. -/
theorem chosenNormalBasisIntegerLatticeMulPowLinearEquiv_galoisGroup_apply_coe
    (n : Nat) (τ : Gal(L / K)) (x : chosenNormalBasisIntegerLattice K L) :
    ((chosenNormalBasisIntegerLatticeMulPowLinearEquiv K L n
      (galoisGroupChosenNormalBasisIntegerLatticeLinearEquiv K L τ x) :
        chosenBaseUniformizerPowSubmodule K L n
          (chosenNormalBasisIntegerLattice K L)) : L) =
      τ ((chosenNormalBasisIntegerLatticeMulPowLinearEquiv K L n x :
        chosenBaseUniformizerPowSubmodule K L n
          (chosenNormalBasisIntegerLattice K L)) : L) := by
  change algebraMap 𝒪[K] L (chosenIntegerRingUniformizer K ^ n) * τ (x : L) =
    τ (algebraMap 𝒪[K] L (chosenIntegerRingUniformizer K ^ n) * (x : L))
  rw [map_mul]
  congr 1
  change algebraMap K L ((chosenIntegerRingUniformizer K ^ n : 𝒪[K]) : K) =
    τ (algebraMap K L ((chosenIntegerRingUniformizer K ^ n : 𝒪[K]) : K))
  exact (τ.commutes _).symm

/-- The additive `Gal(L / K)`-action on the lattice graded piece induced by
the actual action on the extension field. -/
@[implicit_reducible]
noncomputable def galoisGroupChosenNormalBasisLatticeSuccQuotDistribMulAction
    (n : Nat) :
    DistribMulAction Gal(L / K) (chosenNormalBasisLatticeSuccQuot K L n) where
  smul τ q := galoisGroupChosenNormalBasisLatticeSuccQuotAddEquiv K L n τ q
  one_smul := by
    intro q
    change galoisGroupChosenNormalBasisLatticeSuccQuotAddEquiv K L n 1 q = q
    let e := chosenNormalBasisLatticeSuccQuotToIntegerLatticeQuotLinearEquiv K L n
    apply e.injective
    rw [chosenNormalBasisLatticeSuccQuotToIntegerLatticeQuotLinearEquiv_galoisGroup]
    refine Submodule.Quotient.induction_on
      (chosenNormalBasisIntegerLatticeUniformizerSubmodule K L) (e q) ?_
    intro x
    rw [galoisGroupChosenNormalBasisIntegerLatticeQuotLinearEquiv_mk,
      galoisGroupChosenNormalBasisIntegerLatticeLinearEquiv_one_apply]
  mul_smul := by
    intro τ υ q
    change galoisGroupChosenNormalBasisLatticeSuccQuotAddEquiv K L n (τ * υ) q =
      galoisGroupChosenNormalBasisLatticeSuccQuotAddEquiv K L n τ
        (galoisGroupChosenNormalBasisLatticeSuccQuotAddEquiv K L n υ q)
    let e := chosenNormalBasisLatticeSuccQuotToIntegerLatticeQuotLinearEquiv K L n
    apply e.injective
    rw [chosenNormalBasisLatticeSuccQuotToIntegerLatticeQuotLinearEquiv_galoisGroup,
      chosenNormalBasisLatticeSuccQuotToIntegerLatticeQuotLinearEquiv_galoisGroup,
      chosenNormalBasisLatticeSuccQuotToIntegerLatticeQuotLinearEquiv_galoisGroup]
    refine Submodule.Quotient.induction_on
      (chosenNormalBasisIntegerLatticeUniformizerSubmodule K L) (e q) ?_
    intro x
    rw [galoisGroupChosenNormalBasisIntegerLatticeQuotLinearEquiv_mk,
      galoisGroupChosenNormalBasisIntegerLatticeQuotLinearEquiv_mk,
      galoisGroupChosenNormalBasisIntegerLatticeQuotLinearEquiv_mk,
      galoisGroupChosenNormalBasisIntegerLatticeLinearEquiv_mul_apply]
  smul_zero := by
    intro τ
    exact (galoisGroupChosenNormalBasisLatticeSuccQuotAddEquiv K L n τ).map_zero
  smul_add := by
    intro τ q r
    exact (galoisGroupChosenNormalBasisLatticeSuccQuotAddEquiv K L n τ).map_add q r

/-- The graded-piece scalar action applies the Galois automorphism to a scaled representative. -/
@[simp]
theorem galoisGroupChosenNormalBasisLatticeSuccQuotDistribMulAction_smul_mk_mulPow
    (n : Nat) (τ : Gal(L / K)) (x : chosenNormalBasisIntegerLattice K L) :
    letI := galoisGroupChosenNormalBasisLatticeSuccQuotDistribMulAction K L n
    τ • chosenNormalBasisLatticeSuccQuotMk K L n
        (chosenNormalBasisIntegerLatticeMulPowLinearEquiv K L n x) =
      chosenNormalBasisLatticeSuccQuotMk K L n
        (chosenNormalBasisIntegerLatticeMulPowLinearEquiv K L n
          (galoisGroupChosenNormalBasisIntegerLatticeLinearEquiv K L τ x)) :=
  galoisGroupChosenNormalBasisLatticeSuccQuotAddEquiv_mk_mulPow K L n τ x

/-- The inverse-indexed residue coordinates intertwine the Galois
action with the pointwise right-regular action. -/
theorem chosenNormalBasisLatticeSuccQuotRightRegularAddEquiv_commutes
    (n : Nat) (τ : Gal(L / K))
    (q : chosenNormalBasisLatticeSuccQuot K L n) (σ : Gal(L / K)) :
    letI := galoisGroupChosenNormalBasisLatticeSuccQuotDistribMulAction K L n
    chosenNormalBasisLatticeSuccQuotRightRegularAddEquiv K L n (τ • q) σ =
      chosenNormalBasisLatticeSuccQuotRightRegularAddEquiv K L n q (σ * τ) := by
  let := galoisGroupChosenNormalBasisLatticeSuccQuotDistribMulAction K L n
  refine chosenNormalBasisLatticeSuccQuot.inductionOn K L n
    (motive := fun q =>
      chosenNormalBasisLatticeSuccQuotRightRegularAddEquiv K L n (τ • q) σ =
        chosenNormalBasisLatticeSuccQuotRightRegularAddEquiv K L n q (σ * τ))
    q ?_
  intro z
  let x : chosenNormalBasisIntegerLattice K L :=
    (chosenNormalBasisIntegerLatticeMulPowLinearEquiv K L n).symm z
  have hz : chosenNormalBasisIntegerLatticeMulPowLinearEquiv K L n x = z :=
    (chosenNormalBasisIntegerLatticeMulPowLinearEquiv K L n).apply_symm_apply z
  rw [← hz,
    galoisGroupChosenNormalBasisLatticeSuccQuotDistribMulAction_smul_mk_mulPow,
    chosenNormalBasisLatticeSuccQuotRightRegularAddEquiv_mk_mulPow,
    chosenNormalBasisLatticeSuccQuotRightRegularAddEquiv_mk_mulPow,
    chosenNormalBasisIntegerLatticeBasis_equivFun_galoisGroup]
  congr 1

/-- Herbrand `H⁰` vanishes on every additive normal-basis lattice graded
piece. -/
theorem chosenNormalBasisLatticeSuccQuot_herbrandH0_subsingleton (n : Nat) :
    letI := galoisGroupChosenNormalBasisLatticeSuccQuotDistribMulAction K L n
    letI :=
      CyclicCohomology.ProfiniteCohomology.Herbrand.multiplicativeMulDistribMulActionOfDistribMulAction
        Gal(L / K) (chosenNormalBasisLatticeSuccQuot K L n)
    Subsingleton (CyclicCohomology.ProfiniteCohomology.Herbrand.HerbrandH0
      Gal(L / K) (Multiplicative (chosenNormalBasisLatticeSuccQuot K L n))) := by
  let := galoisGroupChosenNormalBasisLatticeSuccQuotDistribMulAction K L n
  exact
    CyclicCohomology.ProfiniteCohomology.Herbrand.herbrandH0_subsingleton_of_addEquiv_rightRegularFunction
      (G := Gal(L / K)) (M := chosenNormalBasisLatticeSuccQuot K L n) (D := 𝓀[K])
      (chosenNormalBasisLatticeSuccQuotRightRegularAddEquiv K L n)
      (chosenNormalBasisLatticeSuccQuotRightRegularAddEquiv_commutes K L n)

end GradedCoordinates

end
end LocalClassFieldTheory
end

section
-- module Solutions.OAIQ244_DUKE.LocalClassFieldTheory_ClassFormation_PrincipalUnitGraded
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.LubinTate.Valuations.exponentialValuationSubringIsLocalRing _root_.LubinTate.compatibleGroupFamiliesGroup _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionFixedSubring.instIsLocalRing _root_.RamificationTheory.HilbertRamification.ValuationSubring.selectedResidueField.instAlgebra _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.maximalIdealPowSuccQuotModule _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.isDomain _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.isLocalRing _root_.CyclicCohomology.binaryCoefficientFamilyCommGroup _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.relativeAdeleRingIntermediateAlgebra _root_.relativeAdeleRingTopIntermediateAlgebra
attribute [-simp] _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.LocalClassFieldTheory.chosenNormalBasisIntegerLatticeBasis_apply _root_.LocalClassFieldTheory.chosenNormalBasisIntegerLatticeMulPowLinearEquiv_apply _root_.LocalClassFieldTheory.chosenNormalBasisLatticeSuccQuotRightRegularAddEquiv_mk_mulPow _root_.LocalClassFieldTheory.chosenNormalBasisLatticeSuccQuotToIntegerLatticeQuotLinearEquiv_galoisGroup _root_.LocalClassFieldTheory.chosenNormalBasisLatticeSuccQuotToIntegerLatticeQuotLinearEquiv_mk_mulPow _root_.LocalClassFieldTheory.chosenNormalBasisPrincipalUnitSequenceAsPrincipalUnits_val _root_.LocalClassFieldTheory.chosenNormalBasisPrincipalUnitSubgroupMulDistribMulAction_smul _root_.LocalClassFieldTheory.chosenNormalBasisPrincipalUnitSubgroup_sigmaMinusOne_coe _root_.LocalClassFieldTheory.chosenNormalBasisPrincipalUnitSubgroup_tateNorm_coe _root_.LocalClassFieldTheory.galoisGroupChosenNormalBasisIntegerLatticeLinearEquiv_apply_coe _root_.LocalClassFieldTheory.galoisGroupChosenNormalBasisIntegerLatticeLinearEquiv_mul_apply _root_.LocalClassFieldTheory.galoisGroupChosenNormalBasisIntegerLatticeLinearEquiv_one_apply _root_.LocalClassFieldTheory.galoisGroupChosenNormalBasisIntegerLatticeQuotLinearEquiv_mk _root_.LocalClassFieldTheory.galoisGroupChosenNormalBasisLatticeSuccQuotAddEquiv_mk_mulPow _root_.LocalClassFieldTheory.galoisGroupChosenNormalBasisLatticeSuccQuotDistribMulAction_smul_mk_mulPow _root_.LocalClassFieldTheory.mem_chosenNormalBasisIntegerLatticeUniformizerSubmodule_iff
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false
/-! Provides the public declarations in the `LocalClassFieldTheory.ClassFormation.PrincipalUnitGraded` Lean module. -/

namespace LocalClassFieldTheory

open CyclicCohomology LocalFieldTheory

noncomputable section

universe u

open scoped ValuativeRel
open IsNonarchimedeanLocalField

variable (K L : Type u) [Field K] [Field L] [Algebra K L]
  [FiniteDimensional K L] [IsGalois K L]
  [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [ValuativeRel L]
  [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]

omit [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)] in

/-- The map `u ↦ u - 1` on successive normal-basis principal-unit quotients
is injective.  Its kernel calculation is exactly the statement that
`u - 1 ∈ π_K^(n+1)M` if and only if `u ∈ V^(n+1)`. -/
theorem chosenNormalBasisPrincipalUnitSuccQuotToLatticeSuccQuotHom_injective
    {n : Nat} {Vn Vsucc : Subgroup 𝒪[L]ˣ}
    (hVn : (Vn : Set 𝒪[L]ˣ) = chosenNormalBasisPrincipalUnitSet K L n)
    (hVsucc : (Vsucc : Set 𝒪[L]ˣ) =
      chosenNormalBasisPrincipalUnitSet K L (n + 1))
    (hV : Vsucc ≤ Vn)
    (hmul_error : ∀ u : 𝒪[L]ˣ, u ∈ chosenNormalBasisPrincipalUnitSet K L n →
      ∀ v : 𝒪[L]ˣ, v ∈ chosenNormalBasisPrincipalUnitSet K L n →
        (((((u * v : 𝒪[L]ˣ) : 𝒪[L]) - 1 : 𝒪[L]) : L) -
            (((((u : 𝒪[L]ˣ) : 𝒪[L]) - 1 : 𝒪[L]) : L) +
              ((((v : 𝒪[L]ˣ) : 𝒪[L]) - 1 : 𝒪[L]) : L))) ∈
          chosenBaseUniformizerPowSubmodule K L (n + 1)
            (chosenNormalBasisIntegerLattice K L)) :
    Function.Injective
      (chosenNormalBasisPrincipalUnitSuccQuotToLatticeSuccQuotHom
        K L n hVn hVsucc hV hmul_error) := by
  rw [← MonoidHom.ker_eq_bot_iff]
  apply le_antisymm
  · intro q hq
    rw [Subgroup.mem_bot]
    revert hq
    refine
      chosenNormalBasisPrincipalUnitSuccQuot.inductionOn
        (L := L) hV
        (motive := fun q =>
          q ∈ (chosenNormalBasisPrincipalUnitSuccQuotToLatticeSuccQuotHom
            K L n hVn hVsucc hV hmul_error).ker → q = 1)
        q ?_
    intro u hu
    rw [MonoidHom.mem_ker] at hu
    change chosenNormalBasisPrincipalUnitSuccQuotToLatticeSuccQuotHom
        K L n hVn hVsucc hV hmul_error
        (chosenNormalBasisPrincipalUnitSuccQuotMk (L := L) hV u) = 1 at hu
    rw [chosenNormalBasisPrincipalUnitSuccQuotToLatticeSuccQuotHom_mk] at hu
    have hu_n : (u : 𝒪[L]ˣ) ∈ chosenNormalBasisPrincipalUnitSet K L n := by
      exact hVn ▸ u.2
    have hzero :
        chosenNormalBasisPrincipalUnitLatticeClass K L n (u : 𝒪[L]ˣ) hu_n = 0 := by
      have h := congrArg
        (fun x : Multiplicative (chosenNormalBasisLatticeSuccQuot K L n) => x.toAdd) hu
      change
        chosenNormalBasisPrincipalUnitLatticeClass K L n (u : 𝒪[L]ˣ) hu_n = 0 at h
      exact h
    have hu_succ :
        (u : 𝒪[L]ˣ) ∈ chosenNormalBasisPrincipalUnitSet K L (n + 1) :=
      (chosenNormalBasisPrincipalUnitLatticeClass_eq_zero_iff
        (K := K) (L := L) (u : 𝒪[L]ˣ) hu_n).1 hzero
    change chosenNormalBasisPrincipalUnitSuccQuotMk (L := L) hV u = 1
    rw [chosenNormalBasisPrincipalUnitSuccQuotMk_eq_one_iff]
    change (u : 𝒪[L]ˣ) ∈ (Vsucc : Set 𝒪[L]ˣ)
    rw [hVsucc]
    exact hu_succ
  · exact bot_le

/-- If the high normal-basis lattice lies in the maximal ideal, every additive
successive-quotient class is represented by a unit `1 + x`; hence the
map `u ↦ u - 1` is surjective. -/
theorem chosenNormalBasisPrincipalUnitSuccQuotToLatticeSuccQuotHom_surjective_of_le_maximalIdeal
    {n : Nat} {Vn Vsucc : Subgroup 𝒪[L]ˣ}
    (hVn : (Vn : Set 𝒪[L]ˣ) = chosenNormalBasisPrincipalUnitSet K L n)
    (hVsucc : (Vsucc : Set 𝒪[L]ˣ) =
      chosenNormalBasisPrincipalUnitSet K L (n + 1))
    (hV : Vsucc ≤ Vn)
    (hmul_error : ∀ u : 𝒪[L]ˣ, u ∈ chosenNormalBasisPrincipalUnitSet K L n →
      ∀ v : 𝒪[L]ˣ, v ∈ chosenNormalBasisPrincipalUnitSet K L n →
        (((((u * v : 𝒪[L]ˣ) : 𝒪[L]) - 1 : 𝒪[L]) : L) -
            (((((u : 𝒪[L]ˣ) : 𝒪[L]) - 1 : 𝒪[L]) : L) +
              ((((v : 𝒪[L]ˣ) : 𝒪[L]) - 1 : 𝒪[L]) : L))) ∈
          chosenBaseUniformizerPowSubmodule K L (n + 1)
            (chosenNormalBasisIntegerLattice K L))
    (hle : chosenBaseUniformizerPowSubmodule K L n
        (chosenNormalBasisIntegerLattice K L) ≤
      maximalIdealFieldSubmodule K L) :
    Function.Surjective
      (chosenNormalBasisPrincipalUnitSuccQuotToLatticeSuccQuotHom
        K L n hVn hVsucc hV hmul_error) := by
  intro y
  let yadd : chosenNormalBasisLatticeSuccQuot K L n := Multiplicative.toAdd y
  suffices ∃ q : chosenNormalBasisPrincipalUnitSuccQuot (L := L) hV,
      chosenNormalBasisPrincipalUnitSuccQuotToLatticeSuccQuotHom
          K L n hVn hVsucc hV hmul_error q = Multiplicative.ofAdd yadd by
    simpa [yadd] using this
  refine chosenNormalBasisLatticeSuccQuot.inductionOn K L n
    (motive := fun yadd =>
      ∃ q : chosenNormalBasisPrincipalUnitSuccQuot (L := L) hV,
        chosenNormalBasisPrincipalUnitSuccQuotToLatticeSuccQuotHom
            K L n hVn hVsucc hV hmul_error q =
          Multiplicative.ofAdd yadd)
    yadd ?_
  intro x
  have hxmax : (x : L) ∈ maximalIdealFieldSubmodule K L := hle x.2
  rcases (mem_maximalIdealFieldSubmodule_iff
      (K := K) (L := L) (x : L)).1 hxmax with ⟨a, ha, hax⟩
  have ha_pow : a ∈ (𝓂[L] ^ (1 : Nat) : Ideal 𝒪[L]) := by
    simpa using ha
  let hunit : IsUnit (1 + a) :=
    isUnit_one_add_of_mem_maximalIdeal_pow L (n := 1) (by rfl) a ha_pow
  let u : 𝒪[L]ˣ := hunit.unit
  have huval : ((u : 𝒪[L]ˣ) : 𝒪[L]) = 1 + a := by
    exact IsUnit.unit_spec hunit
  have hu_sub_one :
      (((((u : 𝒪[L]ˣ) : 𝒪[L]) - 1 : 𝒪[L]) : L) = (x : L)) := by
    rw [huval]
    simpa using hax
  have hu_set : u ∈ chosenNormalBasisPrincipalUnitSet K L n := by
    rw [mem_chosenNormalBasisPrincipalUnitSet_iff, hu_sub_one]
    exact x.2
  have huVn : u ∈ Vn := by
    change u ∈ (Vn : Set 𝒪[L]ˣ)
    rw [hVn]
    exact hu_set
  let ux : Vn := ⟨u, huVn⟩
  refine ⟨chosenNormalBasisPrincipalUnitSuccQuotMk (L := L) hV ux, ?_⟩
  rw [chosenNormalBasisPrincipalUnitSuccQuotToLatticeSuccQuotHom_mk]
  change Multiplicative.ofAdd
      (chosenNormalBasisPrincipalUnitLatticeClass K L n u hu_set) =
    Multiplicative.ofAdd (chosenNormalBasisLatticeSuccQuotMk K L n x)
  congr 1
  rw [chosenNormalBasisPrincipalUnitLatticeClass]
  exact congrArg (chosenNormalBasisLatticeSuccQuotMk K L n)
    (Subtype.ext hu_sub_one)

/-- The actual isomorphism
`V^n/V^(n+1) ≃ π_K^nM/π_K^(n+1)M` once the high-lattice bound and
multiplicative-error estimate hold. -/
noncomputable def chosenNormalBasisPrincipalUnitSuccQuotMulEquivLatticeSuccQuot
    {n : Nat} {Vn Vsucc : Subgroup 𝒪[L]ˣ}
    (hVn : (Vn : Set 𝒪[L]ˣ) = chosenNormalBasisPrincipalUnitSet K L n)
    (hVsucc : (Vsucc : Set 𝒪[L]ˣ) =
      chosenNormalBasisPrincipalUnitSet K L (n + 1))
    (hV : Vsucc ≤ Vn)
    (hmul_error : ∀ u : 𝒪[L]ˣ, u ∈ chosenNormalBasisPrincipalUnitSet K L n →
      ∀ v : 𝒪[L]ˣ, v ∈ chosenNormalBasisPrincipalUnitSet K L n →
        (((((u * v : 𝒪[L]ˣ) : 𝒪[L]) - 1 : 𝒪[L]) : L) -
            (((((u : 𝒪[L]ˣ) : 𝒪[L]) - 1 : 𝒪[L]) : L) +
              ((((v : 𝒪[L]ˣ) : 𝒪[L]) - 1 : 𝒪[L]) : L))) ∈
          chosenBaseUniformizerPowSubmodule K L (n + 1)
            (chosenNormalBasisIntegerLattice K L))
    (hle : chosenBaseUniformizerPowSubmodule K L n
        (chosenNormalBasisIntegerLattice K L) ≤
      maximalIdealFieldSubmodule K L) :
    chosenNormalBasisPrincipalUnitSuccQuot (L := L) hV ≃*
      Multiplicative (chosenNormalBasisLatticeSuccQuot K L n) :=
  MulEquiv.ofBijective
    (chosenNormalBasisPrincipalUnitSuccQuotToLatticeSuccQuotHom
      K L n hVn hVsucc hV hmul_error)
    ⟨chosenNormalBasisPrincipalUnitSuccQuotToLatticeSuccQuotHom_injective
        (K := K) (L := L) hVn hVsucc hV hmul_error,
      chosenNormalBasisPrincipalUnitSuccQuotToLatticeSuccQuotHom_surjective_of_le_maximalIdeal
        (K := K) (L := L) hVn hVsucc hV hmul_error hle⟩

/-- States the theorem `chosenNormalBasisPrincipalUnitSuccQuotMulEquivLatticeSuccQuot_mk`. -/
@[simp]
theorem chosenNormalBasisPrincipalUnitSuccQuotMulEquivLatticeSuccQuot_mk
    {n : Nat} {Vn Vsucc : Subgroup 𝒪[L]ˣ}
    (hVn : (Vn : Set 𝒪[L]ˣ) = chosenNormalBasisPrincipalUnitSet K L n)
    (hVsucc : (Vsucc : Set 𝒪[L]ˣ) =
      chosenNormalBasisPrincipalUnitSet K L (n + 1))
    (hV : Vsucc ≤ Vn)
    (hmul_error : ∀ u : 𝒪[L]ˣ, u ∈ chosenNormalBasisPrincipalUnitSet K L n →
      ∀ v : 𝒪[L]ˣ, v ∈ chosenNormalBasisPrincipalUnitSet K L n →
        (((((u * v : 𝒪[L]ˣ) : 𝒪[L]) - 1 : 𝒪[L]) : L) -
            (((((u : 𝒪[L]ˣ) : 𝒪[L]) - 1 : 𝒪[L]) : L) +
              ((((v : 𝒪[L]ˣ) : 𝒪[L]) - 1 : 𝒪[L]) : L))) ∈
          chosenBaseUniformizerPowSubmodule K L (n + 1)
            (chosenNormalBasisIntegerLattice K L))
    (hle : chosenBaseUniformizerPowSubmodule K L n
        (chosenNormalBasisIntegerLattice K L) ≤
      maximalIdealFieldSubmodule K L)
    (u : Vn) :
    chosenNormalBasisPrincipalUnitSuccQuotMulEquivLatticeSuccQuot
        K L hVn hVsucc hV hmul_error hle
        (chosenNormalBasisPrincipalUnitSuccQuotMk (L := L) hV u) =
      Multiplicative.ofAdd
        (chosenNormalBasisPrincipalUnitLatticeClass K L n (u : 𝒪[L]ˣ)
          (by exact hVn ▸ u.2)) :=
  rfl

end
end LocalClassFieldTheory
end

section
-- module Solutions.OAIQ244_DUKE.LocalClassFieldTheory_ClassFormation_NormalBasisGradedLifting
attribute [-instance] _root_.ClassFormation.DegreeData.GaloisSubextension.extensionSubgroup_normalInstance _root_.ClassFormation.FiniteCyclicSubextension.instNormalSubtypeMemSubgroupFieldExtensionSubgroupField _root_.ClassFormation.FiniteGaloisSubextension.extensionSubgroup_normalInstance _root_.ClassFormation.FiniteGaloisSubextension.extensionSubgroup_over_intermediate_normalInstance _root_.ClassFormation.FiniteGaloisSubextension.intermediateField_normalInstance _root_.ClassFormation.FiniteUnramifiedCyclicExtension.instNormalSubtypeMemSubgroupFieldExtensionSubgroupField _root_.ClassFormation.conjugateExtension_normal _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.LocalClassFieldTheory.extensionSubgroupBase_normal _root_.LocalClassFieldTheory.finiteGaloisExtensionSubgroupOfEmbedding_normal _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.LubinTate.compatibleGroupFamiliesCommGroup _root_.LubinTate.compatibleGroupFamiliesGroup _root_.RamificationTheory.HilbertRamification.ValuationSubring.inertiaGroup_normal _root_.RamificationTheory.HilbertRamification.ValuationSubring.ramificationGroupInInertiaAut_normal _root_.RamificationTheory.HilbertRamification.ValuationSubring.selectedResidueField.instAlgebra _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.RelativeIdeleGroup.relativeIdeleMulAction _root_.ValuationTheory.DiscreteValuationField.DVF.maximalIdealPowSuccQuotModule _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.CyclicCohomology.binaryCoefficientFamilyCommGroup _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.relativeAdeleRingIntermediateAlgebra _root_.relativeAdeleRingTopIntermediateAlgebra
attribute [-simp] _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.LocalClassFieldTheory.chosenNormalBasisPrincipalUnitSequenceAsPrincipalUnits_val
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false
/-! Provides the public declarations in the `LocalClassFieldTheory.ClassFormation.NormalBasisGradedLifting` Lean module. -/

namespace LocalClassFieldTheory

open LocalFieldTheory

open CyclicCohomology

noncomputable section

universe u

open scoped BigOperators ValuativeRel
open IsNonarchimedeanLocalField
open CyclicCohomology.ProfiniteCohomology.Herbrand

variable (K L : Type u) [Field K] [Field L] [Algebra K L]
  [FiniteDimensional K L] [IsGalois K L]
  [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [ValuativeRel L]
  [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]
  [IsIntegralClosure 𝒪[L] 𝒪[K] L]

/-- The class `u - 1` in the normal-basis lattice graded piece is equivariant
for the actual Galois action on integer units and the transported action on
the lattice quotient. -/
theorem chosenNormalBasisPrincipalUnitLatticeClass_galoisGroup
    (n : Nat) (sigma : Gal(L / K)) (u : 𝒪[L]ˣ)
    (hu : u ∈ chosenNormalBasisPrincipalUnitSet K L n) :
    letI := galoisGroupIntegerUnitsMulDistribMulActionOfIsIntegralClosure K L
    letI := galoisGroupChosenNormalBasisLatticeSuccQuotDistribMulAction K L n
    chosenNormalBasisPrincipalUnitLatticeClass K L n (sigma • u)
        (galoisGroup_smul_mem_chosenNormalBasisPrincipalUnitSet
          (K := K) (L := L) n sigma hu) =
      sigma • chosenNormalBasisPrincipalUnitLatticeClass K L n u hu := by
  let := galoisGroupIntegerUnitsMulDistribMulActionOfIsIntegralClosure K L
  let := galoisGroupChosenNormalBasisLatticeSuccQuotDistribMulAction K L n
  let y : chosenBaseUniformizerPowSubmodule K L n
      (chosenNormalBasisIntegerLattice K L) :=
    ⟨((((u : 𝒪[L]ˣ) : 𝒪[L]) - 1 : 𝒪[L]) : L), hu⟩
  let x : chosenNormalBasisIntegerLattice K L :=
    (chosenNormalBasisIntegerLatticeMulPowLinearEquiv K L n).symm y
  have hxy : chosenNormalBasisIntegerLatticeMulPowLinearEquiv K L n x = y :=
    (chosenNormalBasisIntegerLatticeMulPowLinearEquiv K L n).apply_symm_apply y
  rw [chosenNormalBasisPrincipalUnitLatticeClass,
    chosenNormalBasisPrincipalUnitLatticeClass]
  change chosenNormalBasisLatticeSuccQuotMk K L n _ =
    sigma • chosenNormalBasisLatticeSuccQuotMk K L n y
  rw [← hxy,
    galoisGroupChosenNormalBasisLatticeSuccQuotDistribMulAction_smul_mk_mulPow]
  apply congrArg (chosenNormalBasisLatticeSuccQuotMk K L n)
  apply Subtype.ext
  have hfield := chosenNormalBasisIntegerLatticeMulPowLinearEquiv_galoisGroup_apply_coe
    K L n sigma x
  rw [hxy] at hfield
  simpa [y, galoisGroupIntegerUnitsMulDistribMulActionOfIsIntegralClosure_smul,
    map_sub, map_one] using hfield.symm

/-- The actual action on `V^n` descends to the successive quotient
`V^n / V^(n+1)`. -/
@[implicit_reducible]
def chosenNormalBasisPrincipalUnitSuccQuotMulDistribMulAction
    (n : Nat) {Vn Vsucc : Subgroup 𝒪[L]ˣ} (hV : Vsucc ≤ Vn)
    (hVn : (Vn : Set 𝒪[L]ˣ) = chosenNormalBasisPrincipalUnitSet K L n)
    (hVsucc : (Vsucc : Set 𝒪[L]ˣ) =
      chosenNormalBasisPrincipalUnitSet K L (n + 1)) :
    MulDistribMulAction (Gal(L / K))
      (chosenNormalBasisPrincipalUnitSuccQuot (L := L) hV) := by
  letI := galoisGroupIntegerUnitsMulDistribMulActionOfIsIntegralClosure K L
  letI := chosenNormalBasisPrincipalUnitSubgroupMulDistribMulAction
    K L n Vn hVn
  change MulDistribMulAction (Gal(L / K))
    (Vn ⧸ chosenNormalBasisPrincipalUnitSuccSubgroup (L := L) hV)
  exact quotientMulDistribMulActionOfSubgroupStable
    (Gal(L / K)) Vn
    (chosenNormalBasisPrincipalUnitSuccSubgroup (L := L) hV) (by
      intro sigma a ha
      apply (mem_chosenNormalBasisPrincipalUnitSuccSubgroup_iff
        (L := L) hV (sigma • a)).2
      change (sigma • (a : 𝒪[L]ˣ)) ∈ (Vsucc : Set 𝒪[L]ˣ)
      rw [hVsucc]
      apply galoisGroup_smul_mem_chosenNormalBasisPrincipalUnitSet
        (K := K) (L := L) (n + 1) sigma
      rw [← hVsucc]
      exact (mem_chosenNormalBasisPrincipalUnitSuccSubgroup_iff
        (L := L) hV a).1 ha)

/-- States the theorem `chosenNormalBasisPrincipalUnitSuccQuotMulDistribMulAction_smul_mk`. -/
@[simp]
theorem chosenNormalBasisPrincipalUnitSuccQuotMulDistribMulAction_smul_mk
    (n : Nat) {Vn Vsucc : Subgroup 𝒪[L]ˣ} (hV : Vsucc ≤ Vn)
    (hVn : (Vn : Set 𝒪[L]ˣ) = chosenNormalBasisPrincipalUnitSet K L n)
    (hVsucc : (Vsucc : Set 𝒪[L]ˣ) =
      chosenNormalBasisPrincipalUnitSet K L (n + 1))
    (sigma : Gal(L / K)) (u : Vn) :
    letI := chosenNormalBasisPrincipalUnitSubgroupMulDistribMulAction
      K L n Vn hVn
    letI := chosenNormalBasisPrincipalUnitSuccQuotMulDistribMulAction
      K L n hV hVn hVsucc
    sigma • chosenNormalBasisPrincipalUnitSuccQuotMk (L := L) hV u =
      chosenNormalBasisPrincipalUnitSuccQuotMk (L := L) hV (sigma • u) :=
  rfl

/-- Any graded-piece equivalence whose value on representatives is `u - 1`
is equivariant for the actual quotient action and the lattice action. -/
theorem chosenNormalBasisPrincipalUnitSuccQuotMulEquiv_galoisGroup
    (n : Nat) {Vn Vsucc : Subgroup 𝒪[L]ˣ} (hV : Vsucc ≤ Vn)
    (hVn : (Vn : Set 𝒪[L]ˣ) = chosenNormalBasisPrincipalUnitSet K L n)
    (hVsucc : (Vsucc : Set 𝒪[L]ˣ) =
      chosenNormalBasisPrincipalUnitSet K L (n + 1))
    (Phi : chosenNormalBasisPrincipalUnitSuccQuot (L := L) hV ≃*
      Multiplicative (chosenNormalBasisLatticeSuccQuot K L n))
    (hPhi : ∀ u : Vn,
      Phi (chosenNormalBasisPrincipalUnitSuccQuotMk (L := L) hV u) =
        Multiplicative.ofAdd
          (chosenNormalBasisPrincipalUnitLatticeClass K L n (u : 𝒪[L]ˣ)
            (by exact hVn ▸ u.2)))
    (sigma : Gal(L / K))
    (q : chosenNormalBasisPrincipalUnitSuccQuot (L := L) hV) :
    letI := chosenNormalBasisPrincipalUnitSubgroupMulDistribMulAction
      K L n Vn hVn
    letI := chosenNormalBasisPrincipalUnitSuccQuotMulDistribMulAction
      K L n hV hVn hVsucc
    letI := galoisGroupChosenNormalBasisLatticeSuccQuotDistribMulAction K L n
    letI := multiplicativeMulDistribMulActionOfDistribMulAction
      (Gal(L / K)) (chosenNormalBasisLatticeSuccQuot K L n)
    Phi (sigma • q) = sigma • Phi q := by
  let := galoisGroupIntegerUnitsMulDistribMulActionOfIsIntegralClosure K L
  let := chosenNormalBasisPrincipalUnitSubgroupMulDistribMulAction
    K L n Vn hVn
  let := chosenNormalBasisPrincipalUnitSuccQuotMulDistribMulAction
    K L n hV hVn hVsucc
  let := galoisGroupChosenNormalBasisLatticeSuccQuotDistribMulAction K L n
  let := multiplicativeMulDistribMulActionOfDistribMulAction
    (Gal(L / K)) (chosenNormalBasisLatticeSuccQuot K L n)
  refine
    chosenNormalBasisPrincipalUnitSuccQuot.inductionOn
      (L := L) hV
      (motive := fun q => Phi (sigma • q) = sigma • Phi q)
      q ?_
  intro u
  rw [chosenNormalBasisPrincipalUnitSuccQuotMulDistribMulAction_smul_mk,
    hPhi, hPhi]
  exact congrArg Multiplicative.ofAdd
    (chosenNormalBasisPrincipalUnitLatticeClass_galoisGroup
      (K := K) (L := L) n sigma (u : 𝒪[L]ˣ) (by exact hVn ▸ u.2))

end
end LocalClassFieldTheory
end

section
-- module Solutions.OAIQ244_DUKE.AlgebraicNumberTheory_Idele_Cohomology_Decomposition
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.LubinTate.compatibleGroupFamiliesGroup _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionResidueField.instField _root_.RamificationTheory.HilbertRamification.ValuationSubring.selectedResidueField.instAlgebra _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.adicCompletionProperSpace _root_.relativeAdeleRingIntermediateAlgebra _root_.relativeAdeleRingTopIntermediateAlgebra
attribute [-simp] _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.IdeleGroup.finiteComponent_principalIdele _root_.IdeleGroup.infiniteComponent_principalIdele _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.RelativeIdeleGroup.Cohomology.ideleClassNorm_mk _root_.RelativeIdeleGroup.classInclusion_mk _root_.RelativeIdeleGroup.classNorm_mk _root_.RelativeIdeleGroup.finiteComponent_inclusion _root_.RelativeIdeleGroup.finiteComponent_norm _root_.RelativeIdeleGroup.inclusion_principalIdele _root_.RelativeIdeleGroup.infiniteComponent_inclusion _root_.RelativeIdeleGroup.infiniteComponent_norm _root_.RelativeIdeleGroup.norm_inclusion _root_.RelativeIdeleGroup.norm_principalIdele _root_.RelativeIdeleGroup.smul_inclusion _root_.compositeToBaseNormQuotient_mk _root_.intermediateToCompositeNormQuotient_mk
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

/-- The complete product model for `I_F^S`, including every
archimedean component. -/
abbrev IdeleSPlaceFactors
    (S : Finset (HeightOneSpectrum (𝓞 F))) :=
  InfiniteIdeleGroup F × FiniteSPlaceFactors (F := F) S

/-- Assemble prescribed local factors into a finite idele.  Restricted
product membership follows because the only possibly nonintegral
components lie in the finite set `S`. -/
noncomputable def finiteIdeleOfSPlaceFactors
    (S : Finset (HeightOneSpectrum (𝓞 F)))
    (x : FiniteSPlaceFactors (F := F) S) :
    FiniteIdeleGroup F := by
  classical
  let f : ∀ v : HeightOneSpectrum (𝓞 F),
      (v.adicCompletion F)ˣ :=
    fun v ↦ if hv : v ∈ S then
      x.1 ⟨v, hv⟩
    else
      (x.2 ⟨v, hv⟩ :
        (v.adicCompletion F)ˣ)
  refine ⟨f, S.eventually_cofinite_notMem.mono ?_⟩
  intro v hv
  simp only [f, dite_eq_right hv]
  exact (x.2 ⟨v, hv⟩).2

@[simp]
theorem finiteIdeleOfSPlaceFactors_apply_mem
    (S : Finset (HeightOneSpectrum (𝓞 F)))
    (x : FiniteSPlaceFactors (F := F) S)
    (v : HeightOneSpectrum (𝓞 F)) (hv : v ∈ S) :
    finiteIdeleOfSPlaceFactors S x v = x.1 ⟨v, hv⟩ := by
  simp [finiteIdeleOfSPlaceFactors, hv]

@[simp]
theorem finiteIdeleOfSPlaceFactors_apply_notMem
    (S : Finset (HeightOneSpectrum (𝓞 F)))
    (x : FiniteSPlaceFactors (F := F) S)
    (v : HeightOneSpectrum (𝓞 F)) (hv : v ∉ S) :
    finiteIdeleOfSPlaceFactors S x v =
      (x.2 ⟨v, hv⟩ : (v.adicCompletion F)ˣ) := by
  simp [finiteIdeleOfSPlaceFactors, hv]

/-- The finite part of the actual `S`-idele group is exactly the
displayed product of local multiplicative groups and local unit groups. -/
noncomputable def finiteSupportedAtEquivSPlaceFactors
    (S : Finset (HeightOneSpectrum (𝓞 F))) :
    FiniteIdeleGroup.supportedAt (K := F) (S : Set _) ≃*
      FiniteSPlaceFactors (F := F) S where
  toFun a :=
    ⟨fun v ↦ a.1 v.1,
      fun v ↦ ⟨a.1 v.1, a.2 v.1 v.2⟩⟩
  invFun x :=
    ⟨finiteIdeleOfSPlaceFactors S x, by
      intro v hv
      rw [finiteIdeleOfSPlaceFactors_apply_notMem S x v hv]
      exact (x.2 ⟨v, hv⟩).2⟩
  left_inv a := by
    apply Subtype.ext
    ext v
    by_cases hv : v ∈ S
    · simp [finiteIdeleOfSPlaceFactors_apply_mem, hv]
    · simp [finiteIdeleOfSPlaceFactors_apply_notMem, hv]
  right_inv x := by
    apply Prod.ext
    · funext v
      exact finiteIdeleOfSPlaceFactors_apply_mem S x v.1 v.2
    · funext v
      apply Subtype.ext
      exact finiteIdeleOfSPlaceFactors_apply_notMem S x v.1 v.2
  map_mul' a b := by
    apply Prod.ext
    · funext v
      rfl
    · funext v
      apply Subtype.ext
      rfl

/-- The actual finite-support decomposition:

`I_F^S ≃ I_{F,∞} × (∏_{v∈S} F_vˣ) ×
  (∏_{v∉S} O_vˣ)`.
-/
noncomputable def ideleSupportedAtEquivInfiniteProd
    (S : Finset (HeightOneSpectrum (𝓞 F))) :
    IdeleGroup.supportedAt (K := F) (S : Set _) ≃*
      InfiniteIdeleGroup F ×
        FiniteIdeleGroup.supportedAt (K := F) (S : Set _) where
  toFun a := ⟨a.1.1, ⟨a.1.2, a.2⟩⟩
  invFun x := ⟨⟨x.1, x.2.1⟩, x.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl

/-- The actual `S`-idele group identified with its complete family of
archimedean, unrestricted finite, and integral finite local factors. -/
noncomputable def ideleSupportedAtEquivSPlaceFactors
    (S : Finset (HeightOneSpectrum (𝓞 F))) :
    IdeleGroup.supportedAt (K := F) (S : Set _) ≃*
      IdeleSPlaceFactors (F := F) S :=
  (ideleSupportedAtEquivInfiniteProd S).trans
    ((MulEquiv.refl (InfiniteIdeleGroup F)).prodCongr
      (finiteSupportedAtEquivSPlaceFactors S))

@[simp]
theorem ideleSupportedAtEquivSPlaceFactors_infinite
    (S : Finset (HeightOneSpectrum (𝓞 F)))
    (a : IdeleGroup.supportedAt (K := F) (S : Set _)) :
    (ideleSupportedAtEquivSPlaceFactors S a).1 = a.1.1 :=
  rfl

@[simp]
theorem ideleSupportedAtEquivSPlaceFactors_inside
    (S : Finset (HeightOneSpectrum (𝓞 F)))
    (a : IdeleGroup.supportedAt (K := F) (S : Set _))
    (v : {v : HeightOneSpectrum (𝓞 F) // v ∈ S}) :
    (ideleSupportedAtEquivSPlaceFactors S a).2.1 v =
      a.1.2 v.1 :=
  rfl

@[simp]
theorem ideleSupportedAtEquivSPlaceFactors_outside_coe
    (S : Finset (HeightOneSpectrum (𝓞 F)))
    (a : IdeleGroup.supportedAt (K := F) (S : Set _))
    (v : {v : HeightOneSpectrum (𝓞 F) // v ∉ S}) :
    ((ideleSupportedAtEquivSPlaceFactors S a).2.2 v :
        (v.1.adicCompletion F)ˣ) =
      a.1.2 v.1 :=
  rfl
end
end

section
-- module Solutions.OAIQ244_DUKE.AlgebraicNumberTheory_Idele_Extension_GaloisNorm
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionResidueExtension_normal _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionResidueField.instField _root_.RamificationTheory.HilbertRamification.ValuationSubring.selectedResidueField.instAlgebra _root_.RelativeIdeleGroup.principalQuotientAction _root_.ValuationTheory.DiscreteValuationField.DVF.maximalIdealPowSuccQuotModule _root_.ValuationTheory.DiscreteValuationField.DVF.residueField.field _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.isDomain _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.isLocalRing _root_.CyclicCohomology.binaryCoefficientFamilyCommGroup _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.relativeAdeleRingIntermediateAlgebra _root_.relativeAdeleRingTopIntermediateAlgebra
attribute [-simp] _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.LocalFieldTheory.residueField_algebraMap_residue
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

/-!
# The Galois product formula for the relative idele norm

This file proves that, in the tensor-product presentation
`𝔸_L = 𝔸_K ⊗_K L`, extension of the determinant norm back to `𝔸_L`
is the product of all Galois conjugates.
-/

open scoped BigOperators TensorProduct
open NumberField

noncomputable section


namespace RelativeIdeleGroup

universe u v w

variable
    {K : Type u} {L : Type v}
    [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L]

/-- The full scalar-extension formula: extending
the determinant norm back to a Galois algebra is the product of all
Galois conjugates.  The coefficient algebra `A` is arbitrary. -/
theorem includeLeft_norm_eq_prod_scalarConjugations
    [IsGalois K L] [Infinite K]
    (A : Type*) [CommRing A] [Algebra K A] [Nontrivial A]
    (z : A ⊗[K] L) :
    (Algebra.TensorProduct.includeLeft
      (R := K) (S := K) (A := A) (B := L))
        (Algebra.norm A z) =
      ∏ σ : L ≃ₐ[K] L,
        scalarConjugation (K := K) (L := L) A σ z := by
  classical
  let b := Module.Free.chooseBasis K L
  let c : Module.Free.ChooseBasisIndex K L → A :=
    fun i ↦ (Algebra.TensorProduct.basis A b).repr z i
  let iL : A →+* A ⊗[K] L :=
    (Algebra.TensorProduct.includeLeft
      (R := K) (S := K) (A := A) (B := L)).toRingHom
  let iR : L →+* A ⊗[K] L :=
    (Algebra.TensorProduct.includeRight
      (R := K) (A := A) (B := L)).toRingHom
  have hmaps :
      iL.comp (algebraMap K A) =
        iR.comp (algebraMap K L) := by
    ext x
    simp [iL, iR]
  have hleft :
      MvPolynomial.eval₂ iR (fun i ↦ iL (c i))
          (MvPolynomial.map (algebraMap K L)
            (normPolynomial b)) =
        iL (Algebra.norm A z) := by
    rw [MvPolynomial.eval₂_map]
    rw [← hmaps]
    rw [← MvPolynomial.hom_eval₂]
    rw [eval₂_normPolynomial_baseChange]
  have hright :
      MvPolynomial.eval₂ iR (fun i ↦ iL (c i))
          (galoisProductPolynomial b) =
        ∏ σ : L ≃ₐ[K] L,
          scalarConjugation (K := K) (L := L) A σ z := by
    rw [galoisProductPolynomial,
      MvPolynomial.eval₂_prod]
    apply Finset.prod_congr rfl
    intro σ hσ
    exact eval₂_conjugatePolynomial_baseChange
      (K := K) (L := L) A b σ z
  change iL (Algebra.norm A z) =
    ∏ σ : L ≃ₐ[K] L,
      scalarConjugation (K := K) (L := L) A σ z
  rw [← hright, ← hleft,
    map_normPolynomial_eq_galoisProductPolynomial b]

/-- In full adèle form, the base extension of the
determinant norm of an arbitrary relative adèle is the product of all of
its Galois conjugates. -/
theorem adeleInclusion_norm_eq_prod_conjugates
    [NumberField K] [IsGalois K L]
    (z : RelativeAdeleRing K L) :
    adeleInclusion K L
        (Algebra.norm
          (NumberField.AdeleRing (𝓞 K) K) z) =
      ∏ σ : L ≃ₐ[K] L, conjugation K L σ z := by
  change
    (Algebra.TensorProduct.includeLeft
      (R := K) (S := K)
      (A := NumberField.AdeleRing (𝓞 K) K) (B := L))
        (Algebra.norm
          (NumberField.AdeleRing (𝓞 K) K) z) =
      _
  simpa only [scalarConjugation_baseAdele_apply] using
    (includeLeft_norm_eq_prod_scalarConjugations
      (K := K) (L := L)
      (NumberField.AdeleRing (𝓞 K) K) z)

/-- In full idèle form,
`i_{L/K}(N_{L/K}(a)) = ∏_{σ ∈ Gal(L/K)} σ(a)` for every relative
idèle `a`. -/
theorem inclusion_norm_eq_prod_conjugates
    [NumberField K] [IsGalois K L]
    (a : RelativeIdeleGroup K L) :
    inclusion K L (norm K L a) =
      ∏ σ : L ≃ₐ[K] L, σ • a := by
  apply Units.ext
  simp only [inclusion, norm, MonoidHom.comp_apply,
    Units.coe_map, Units.coe_prod,
    smul_def, conjugationIdele_coe]
  exact adeleInclusion_norm_eq_prod_conjugates
    (K := K) (L := L) (a : RelativeAdeleRing K L)

end RelativeIdeleGroup
end
end

section
-- module Solutions.OAIQ244_DUKE.AlgebraicNumberTheory_Idele_Cohomology_Herbrand
attribute [-instance] _root_.ClassFormation.DegreeData.GaloisSubextension.extensionSubgroup_normalInstance _root_.ClassFormation.FiniteCyclicSubextension.instNormalSubtypeMemSubgroupFieldExtensionSubgroupField _root_.ClassFormation.FiniteGaloisSubextension.extensionSubgroup_normalInstance _root_.ClassFormation.FiniteGaloisSubextension.extensionSubgroup_over_intermediate_normalInstance _root_.ClassFormation.FiniteGaloisSubextension.intermediateField_normalInstance _root_.ClassFormation.FiniteUnramifiedCyclicExtension.instNormalSubtypeMemSubgroupFieldExtensionSubgroupField _root_.ClassFormation.conjugateExtension_normal _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.LocalClassFieldTheory.extensionSubgroupBase_normal _root_.LocalClassFieldTheory.finiteGaloisExtensionSubgroupOfEmbedding_normal _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionResidueField.instField _root_.RamificationTheory.HilbertRamification.ValuationSubring.inertiaGroup_normal _root_.RamificationTheory.HilbertRamification.ValuationSubring.ramificationGroupInInertiaAut_normal _root_.RamificationTheory.HilbertRamification.ValuationSubring.selectedResidueField.instAlgebra _root_.ValuationTheory.DiscreteValuationField.DVF.residueField.field _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.CyclicCohomology.binaryCoefficientFamilyCommGroup _root_.CyclicCohomology.instMulDistribMulActionBinaryCoefficientFamily _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.relativeAdeleRingIntermediateAlgebra _root_.relativeAdeleRingTopIntermediateAlgebra
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

/-- The concrete norm quotient `C_K / N_{L/K} C_L`. -/
abbrev IdeleClassNormQuotient :=
  IdeleClassGroup K ⧸ (ideleClassNorm K L).range

section Actions

local instance instMulDistribMulActionAlgEquiv_r582600_1 :
    MulDistribMulAction (L ≃ₐ[K] L)
      (RelativeIdeleGroup K L) :=
  relativeIdeleMulDistribMulAction K L
attribute [local instance] RelativeIdeleGroup.Cohomology.instMulDistribMulActionAlgEquivClassGroup
local instance instMulDistribMulActionAlgEquivSubtypeMemSubgroupPrincipalSubgroup_r582600_1 :
    MulDistribMulAction (L ≃ₐ[K] L)
      (RelativeIdeleGroup.principalSubgroup K L) :=
  principalIdeleMulDistribMulAction K L
omit [NumberField L] in
/-- The class norm agrees, after Galois descent, with the Tate norm on
the actual relative idele class group. -/
theorem classInclusion_ideleClassNorm_eq_tateNorm
    (c : RelativeIdeleGroup.ClassGroup K L) :
    RelativeIdeleGroup.classInclusion K L
        (ideleClassNorm K L c) =
      tateNorm (L ≃ₐ[K] L)
        (RelativeIdeleGroup.ClassGroup K L) c := by
  refine QuotientGroup.induction_on c ?_
  intro a
  change
    QuotientGroup.mk'
        (RelativeIdeleGroup.principalSubgroup K L)
        (RelativeIdeleGroup.inclusion K L
          (RelativeIdeleGroup.norm K L a)) =
      ∏ σ : L ≃ₐ[K] L,
        QuotientGroup.mk'
          (RelativeIdeleGroup.principalSubgroup K L)
          (σ • a)
  rw [← map_prod]
  exact congrArg
    (QuotientGroup.mk'
      (RelativeIdeleGroup.principalSubgroup K L))
    (RelativeIdeleGroup.inclusion_norm_eq_prod_conjugates
      (K := K) (L := L) a)

end Actions

end Cohomology
end RelativeIdeleGroup
end
end

section
-- module Solutions.OAIQ244_DUKE.LocalField_GroupTheory_PowerIndex
attribute [-instance] _root_.ClassFormation.DegreeData.FiniteAbstractExtension.ramificationQuotientFinite _root_.ClassFormation.DegreeData.FiniteAbstractExtension.representedQuotientFinite _root_.ClassFormation.DegreeData.FiniteAbstractExtension.residueQuotientFinite _root_.ClassFormation.DegreeData.FiniteResidueAbstractExtension.instFiniteQuotientSubtypeMemSubgroupFieldBaseExtensionSubgroupField _root_.ClassFormation.DegreeData.FiniteTower.baseQuotientFinite _root_.ClassFormation.DegreeData.FiniteTower.topQuotientFinite _root_.ClassFormation.DegreeData.FiniteTower.totalQuotientFinite _root_.ClassFormation.DegreeData.GaloisSubextension.extensionSubgroup_normalInstance _root_.ClassFormation.FiniteAbstractField.instFiniteQuotientSubtypeMemSubgroupBaseFieldExtensionSubgroupField _root_.ClassFormation.FiniteAbstractFieldExtension.instFiniteQuotientSubtypeMemSubgroupFieldBaseExtensionSubgroupField _root_.ClassFormation.FiniteCyclicSubextension.instFiniteQuotientSubtypeMemSubgroupFieldExtensionSubgroupField _root_.ClassFormation.FiniteCyclicSubextension.instNormalSubtypeMemSubgroupFieldExtensionSubgroupField _root_.ClassFormation.FiniteGaloisSubextension.extensionSubgroup_normalInstance _root_.ClassFormation.FiniteGaloisSubextension.extensionSubgroup_over_intermediate_normalInstance _root_.ClassFormation.FiniteGaloisSubextension.intermediateField_normalInstance _root_.ClassFormation.FiniteUnramifiedCyclicExtension.instFiniteQuotientSubtypeMemSubgroupBaseFieldExtensionSubgroupField _root_.ClassFormation.FiniteUnramifiedCyclicExtension.instFiniteQuotientSubtypeMemSubgroupFieldExtensionSubgroupField _root_.ClassFormation.FiniteUnramifiedCyclicExtension.instNormalSubtypeMemSubgroupFieldExtensionSubgroupField _root_.ClassFormation.conjugateExtension_normal _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.KummerTheory.finite_finsupp_nsmulQuotient _root_.LocalClassFieldTheory.baseFixingExtensionQuotient_finite _root_.LocalClassFieldTheory.extensionSubgroupBase_normal _root_.LocalClassFieldTheory.finiteGaloisExtensionSubgroupOfEmbedding_normal _root_.LocalFieldTheory.DiscreteValuationField.finite_padicInt_finPi_nsmulQuotient _root_.RamificationTheory.HilbertRamification.ValuationSubring.inertiaGroup_normal _root_.RamificationTheory.HilbertRamification.ValuationSubring.ramificationGroupInInertiaAut_normal _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.CyclicCohomology.binaryCoefficientFamilyCommGroup _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

/-!
# Power indices in commutative groups

Reusable kernel, quotient, product, and additive-transport formulas for
`n`-th powers in commutative groups.  The basic power map and its image and
kernel are mathlib's `powMonoidHom`, `MonoidHom.range`, and `MonoidHom.ker`.
-/

noncomputable section

namespace LocalFieldTheory

open LocalFieldTheory.DiscreteValuationField
open scoped Int

section NthPowers

universe uG uH uU

variable (G : Type uG) (H : Type uH) (U : Type uU)
variable [CommGroup G] [CommGroup H] [CommGroup U]


/-- An explicit `G ≃ U × ℤ` decomposition transports finiteness of the
unit-factor power quotient to the full group.  This is deliberately a
constructor rather than a global instance: callers must expose the
decomposition and the exact finite boundary. -/
theorem finite_nthPowerQuotient_of_mulEquiv_units_prod_int
    {n : ℕ} [NeZero n] (e : G ≃* U × Multiplicative ℤ)
    [Finite (U ⧸ (powMonoidHom n : U →* U).range)] :
    Finite (G ⧸ (powMonoidHom n : G →* G).range) := by
  let : Finite
      (Multiplicative ℤ ⧸
        (powMonoidHom n : (Multiplicative ℤ) →* (Multiplicative ℤ)).range) :=
    finite_multiplicativeInt_nthPowerQuotient (NeZero.ne n)
  exact finite_nthPowerQuotient_of_mulEquiv
    G (U × Multiplicative ℤ) n e

/-- If a commutative group splits as `U × Multiplicative ℤ`, its `n`-th-power
quotient index is `n` times the corresponding quotient index for `U`. -/
theorem card_nthPowerQuotient_eq_mul_of_mulEquiv_units_prod_int
    {n : ℕ} (hn : n ≠ 0) (e : G ≃* U × Multiplicative ℤ)
    [Finite (G ⧸ (powMonoidHom n : G →* G).range)]
    [Finite (U ⧸ (powMonoidHom n : U →* U).range)] :
    Nat.card (G ⧸ (powMonoidHom n : G →* G).range) =
      n * Nat.card (U ⧸ (powMonoidHom n : U →* U).range) := by
  let := finite_multiplicativeInt_nthPowerQuotient hn
  calc
    Nat.card (G ⧸ (powMonoidHom n : G →* G).range) =
        Nat.card ((U × Multiplicative ℤ) ⧸
          (powMonoidHom n : (U × Multiplicative ℤ) →* (U × Multiplicative ℤ)).range) := by
      rw [Nat.card_congr
        (nthPowerQuotientEquivOfMulEquiv G (U × Multiplicative ℤ) n e).toEquiv]
    _ =
        Nat.card (U ⧸ (powMonoidHom n : U →* U).range) *
          Nat.card (Multiplicative ℤ ⧸
            (powMonoidHom n : (Multiplicative ℤ) →* (Multiplicative ℤ)).range) :=
      card_nthPowerProductQuotient U (Multiplicative ℤ) n
    _ = Nat.card (U ⧸ (powMonoidHom n : U →* U).range) * n := by
      rw [card_multiplicativeInt_nthPowerQuotient hn]
    _ = n * Nat.card (U ⧸ (powMonoidHom n : U →* U).range) := by
      rw [Nat.mul_comm]

end NthPowers

end LocalFieldTheory

end
end

section
-- module Solutions.OAIQ244_DUKE.KummerTheory_Concrete_SUnitPreparation_FullSUnitKummerExtension
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionResidueField.instField _root_.RamificationTheory.HilbertRamification.ValuationSubring.selectedResidueField.instAlgebra _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.RelativeIdeleGroup.relativeIdeleMulAction _root_.ValuationTheory.DiscreteValuationField.DVF.maximalIdealPowSuccQuotModule _root_.ValuationTheory.DiscreteValuationField.DVF.residueField.field _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.relativeAdeleRingIntermediateAlgebra _root_.relativeAdeleRingTopIntermediateAlgebra
set_option synthInstance.maxHeartbeats 400000
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

/-!
# The full S-unit Kummer extension

Construction, finite generation, Galois structure, cardinality, and coordinates for the Kummer extension generated by all `S`-unit roots.
-/

open scoped NumberField Classical IsMulCommutative NNReal ValuativeRel
open NumberField IsDedekindDomain
open LocalFieldTheory

noncomputable section

namespace KummerTheory

variable {K : Type*} [Field K]
    [numberFieldK : NumberField K]

/-- The field `N = K(√[n]{Kˢ})` is Galois over `K`. -/
theorem fullSUnitKummerExtension_isGalois
    {Omega : Type*} [Field Omega] [Algebra K Omega]
    [IsSepClosure K Omega]
    (n : ℕ+)
    (S : Finset (HeightOneSpectrum (𝓞 K))) :
    IsGalois K
      (fullSUnitKummerExtension (K := K) (Omega := Omega) n S) :=
  KummerTheory.kummerRadicalExtension_isGalois n
    (fullSUnitKummerSubgroup (K := K) n S).1

end KummerTheory
end
end

section
-- module Solutions.OAIQ244_DUKE.LocalField_DiscreteValuationField_RamificationIdeal
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_isCompleteDiscrete _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.LocalFieldTheory.DiscreteValuationField.Examples.Qp.padicDVRValuation_isRankOneDiscrete _root_.LocalFieldTheory.DiscreteValuationField.LocalField.residueField_charP_residueCharacteristic _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.RamificationTheory.HilbertRamification.ValuationSubring.selectedResidueField.instAlgebra _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.relativeAdeleRingIntermediateAlgebra _root_.relativeAdeleRingTopIntermediateAlgebra
attribute [-simp] _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.coe_valuationSubringUnitsToFieldUnits_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.fieldUnitValueUnit_mul _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.fieldUnitValueUnit_one _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.mrangeRestrict_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.multiplicativeIntegerValuationOfUniformizer_val _root_.LocalFieldTheory.residueField_algebraMap_residue
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

/-!
# Ramification ideals in finite complete-DVF extensions

This file records the ideal-theoretic source behind the local-field structure theory.
The base maximal ideal maps to the `e`-th power of the target maximal ideal, where
`e` is the canonical ramification index.  Every statement is expressed directly
in the ambient valued-extension context; no extension marker is involved.
-/

noncomputable section

universe u v w x

namespace LocalFieldTheory.DiscreteValuationField
open ValuationTheory.DiscreteValuationField
namespace ValuedExtension
open ValuationTheory.DiscreteValuationField.ValuedExtension

variable {K : Type u} {L : Type w} [Field K] [Field L]
variable [Algebra K L]
variable (base : CompleteDVF.{u, v} K) (target : CompleteDVF.{w, x} L)
variable [base.valuation.HasExtension target.valuation]

/-- No power of the target maximal ideal is contained in the next power.

This is the ideal-level form of the uniformizer-power separation lemma. -/
theorem target_maximalIdeal_pow_not_le_pow_succ
    {π : target.valuationSubring}
    (hπ : target.valuation.IsUniformizer (π : L)) (n : ℕ) :
    ¬ target.maximalIdeal ^ n ≤ target.maximalIdeal ^ (n + 1) := by
  intro hle
  have hπpow_mem : π ^ n ∈ target.maximalIdeal ^ n := by
    rw [target.maximalIdeal_pow_eq_span_uniformizer_pow hπ n]
    exact Ideal.mem_span_singleton_self (π ^ n)
  exact target.uniformizer_pow_not_mem_maximalIdeal_pow_succ hπ n
    (hle hπpow_mem)

/-- The image of the base maximal ideal is the `e`-th power of the target
maximal ideal. -/
theorem maximalIdeal_map_eq_target_maximalIdeal_pow_ramificationIndex :
    Ideal.map (integerMap base.toDVF target.toDVF) base.maximalIdeal =
      target.maximalIdeal ^ ramificationIndex base.toDVF target.toDVF := by
  rcases target.nonzero_ideal_eq_maximalIdeal_pow
      (Ideal.map (integerMap base.toDVF target.toDVF) base.maximalIdeal)
      (maximalIdeal_map_integerMap_ne_bot base.toDVF target.toDVF) with
    ⟨n, hn⟩
  have hle :
      Ideal.map (integerMap base.toDVF target.toDVF) base.maximalIdeal ≤
        target.maximalIdeal ^ n := by
    rw [hn]
  have hnot :
      ¬ Ideal.map (integerMap base.toDVF target.toDVF) base.maximalIdeal ≤
        target.maximalIdeal ^ (n + 1) := by
    intro hle_succ
    rcases target.exists_uniformizer with ⟨π, hπ⟩
    exact target_maximalIdeal_pow_not_le_pow_succ target hπ n
      (by simpa [hn] using hle_succ)
  have he : ramificationIndex base.toDVF target.toDVF = n := by
    simpa [ramificationIndex, integerMap] using
      (Ideal.ramificationIdx'_spec
        (p := base.maximalIdeal) (P := target.maximalIdeal) hle hnot)
  rw [he]
  exact hn

end ValuedExtension
end LocalFieldTheory.DiscreteValuationField

end
end

section
-- module Solutions.OAIQ244_DUKE.LocalField_DiscreteValuationField_ValuationSubringUnits_CompleteRangeRestriction
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.LubinTate.Valuations.exponentialValuationSubringIsLocalRing _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionFixedSubring.instIsLocalRing _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace
attribute [-simp] _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.coe_valuationSubringUnitsToFieldUnits_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.fieldUnitValueUnit_mul _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.fieldUnitValueUnit_one _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.multiplicativeIntegerValuationOfUniformizer_val _root_.LocalFieldTheory.residueField_algebraMap_residue
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

/-!
# Range restriction for complete discretely valued fields

This file specializes multiplicative-range restriction to `CompleteDVF` and
transports residue finiteness, adic completeness, cyclicity, and discreteness.
-/

noncomputable section

universe u v

open WithZero
open scoped NNReal Valued WithZero

namespace LocalFieldTheory.DiscreteValuationField
open ValuationTheory.DiscreteValuationField

namespace CompleteDVF

variable {K : Type u} [Field K]

/-- The range-restricted valuation ring is adically complete because it is
identified with the original complete-DVF valuation ring and the maximal ideal
is preserved by that identification. -/
theorem mrangeRestrict_isAdicComplete
    (F : CompleteDVF.{u, v} K) :
    IsAdicComplete
      (IsLocalRing.maximalIdeal (LocalFieldTheory.DiscreteValuationField.CompleteDVF.mrangeRestrict F).valuationSubring)
      (LocalFieldTheory.DiscreteValuationField.CompleteDVF.mrangeRestrict F).valuationSubring := by
  let e : F.valuationSubring ≃+* (LocalFieldTheory.DiscreteValuationField.CompleteDVF.mrangeRestrict F).valuationSubring :=
    WithZeroValuation.valuationSubringEquivMrangeRestrict
      F.valuation
  let : Algebra F.valuationSubring (LocalFieldTheory.DiscreteValuationField.CompleteDVF.mrangeRestrict F).valuationSubring :=
    e.toRingHom.toAlgebra
  let eLin :
      F.valuationSubring ≃ₗ[F.valuationSubring]
        (LocalFieldTheory.DiscreteValuationField.CompleteDVF.mrangeRestrict F).valuationSubring :=
    { toFun := e
      invFun := e.symm
      left_inv := e.left_inv
      right_inv := e.right_inv
      map_add' := e.map_add
      map_smul' := by
        intro a x
        change e (a * x) =
          (algebraMap F.valuationSubring
            (LocalFieldTheory.DiscreteValuationField.CompleteDVF.mrangeRestrict F).valuationSubring a) * e x
        simp [RingHom.algebraMap_toAlgebra] }
  have hcompleteBase : IsAdicComplete F.maximalIdeal F.valuationSubring :=
    F.isAdicComplete
  let : IsAdicComplete F.maximalIdeal F.valuationSubring := hcompleteBase
  have hcompleteAsBase :
      IsAdicComplete F.maximalIdeal (LocalFieldTheory.DiscreteValuationField.CompleteDVF.mrangeRestrict F).valuationSubring :=
    isAdicComplete_of_linearEquiv
      (M := F.valuationSubring)
      (N := (LocalFieldTheory.DiscreteValuationField.CompleteDVF.mrangeRestrict F).valuationSubring)
      F.maximalIdeal eLin
  have hcompleteMap :
      IsAdicComplete
        (F.maximalIdeal.map
          (algebraMap F.valuationSubring (LocalFieldTheory.DiscreteValuationField.CompleteDVF.mrangeRestrict F).valuationSubring))
        (LocalFieldTheory.DiscreteValuationField.CompleteDVF.mrangeRestrict F).valuationSubring :=
    (isAdicComplete_map_algebraMap_iff
      (I := F.maximalIdeal)
      (S := (LocalFieldTheory.DiscreteValuationField.CompleteDVF.mrangeRestrict F).valuationSubring)).2 hcompleteAsBase
  have hmap :
      F.maximalIdeal.map
          (algebraMap F.valuationSubring (LocalFieldTheory.DiscreteValuationField.CompleteDVF.mrangeRestrict F).valuationSubring) =
        IsLocalRing.maximalIdeal (LocalFieldTheory.DiscreteValuationField.CompleteDVF.mrangeRestrict F).valuationSubring := by
    change
      F.maximalIdeal.map
          (e : F.valuationSubring →+*
            (LocalFieldTheory.DiscreteValuationField.CompleteDVF.mrangeRestrict F).valuationSubring) =
        IsLocalRing.maximalIdeal
          (LocalFieldTheory.DiscreteValuationField.CompleteDVF.mrangeRestrict F).valuationSubring
    exact IsLocalRing.map_ringEquiv_maximalIdeal e
  simpa [hmap] using hcompleteMap

end CompleteDVF
end LocalFieldTheory.DiscreteValuationField

end
end

section
-- module Solutions.OAIQ244_DUKE.LocalField_DiscreteValuationField_ValuationSubringUnits_RangeRestrictedTopology
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.LubinTate.Valuations.exponentialValuationSubringIsLocalRing _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionFixedSubring.instIsLocalRing _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.chosenFinitePlaceBaseNontriviallyNormedField
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

/-!
# Topology of range-restricted complete discretely valued fields

This file equips the multiplicative-range valuation with its valued and normed
field structures and transports adic completeness, compactness, properness,
and completeness.
-/

noncomputable section

universe u v

open Filter WithZero
open scoped NNReal Valued Filter WithZero

namespace LocalFieldTheory.DiscreteValuationField
open ValuationTheory.DiscreteValuationField

namespace CompleteDVF

variable {K : Type u} [Field K]

/-- The valuation ring of a range-restricted complete DVF is complete for the
subspace topology coming from the corresponding normed-field topology. -/
theorem mrangeRestrict_integer_completeSpace
    (F : CompleteDVF.{u, v} K) :
    letI : Valued K
        (MonoidHom.mrange F.valuation.toMonoidWithZeroHom) :=
      (LocalFieldTheory.DiscreteValuationField.CompleteDVF.mrangeRestrictValued F)
    letI : NontriviallyNormedField K :=
      (LocalFieldTheory.DiscreteValuationField.CompleteDVF.mrangeRestrict_nontriviallyNormedField F)
    CompleteSpace 𝒪[K] := by
  let Γ : Type v :=
    MonoidHom.mrange F.valuation.toMonoidWithZeroHom
  let : Valued K Γ := (LocalFieldTheory.DiscreteValuationField.CompleteDVF.mrangeRestrictValued F)
  have : (Valued.v : _root_.Valuation K Γ).IsRankOneDiscrete := by
    change
      (LocalFieldTheory.DiscreteValuationField.CompleteDVF.mrangeRestrict F).IsRankOneDiscrete
    exact
      (LocalFieldTheory.DiscreteValuationField.CompleteDVF.mrangeRestrict_isRankOneDiscrete F)
  have : (Valued.v : _root_.Valuation K Γ).RankOne := by
    change
      (LocalFieldTheory.DiscreteValuationField.CompleteDVF.mrangeRestrict F).RankOne
    exact
      (LocalFieldTheory.DiscreteValuationField.CompleteDVF.mrangeRestrict_rankOne F)
  let : NontriviallyNormedField K :=
    Valued.toNontriviallyNormedField
      (L := K)
      (Γ₀ := MonoidHom.mrange
        F.valuation.toMonoidWithZeroHom)
  have : IsUltrametricDist K := by infer_instance
  have : IsDiscreteValuationRing 𝒪[K] := by
    change IsDiscreteValuationRing (Valued.v : _root_.Valuation K Γ).valuationSubring
    infer_instance
  have hadic : IsAdic (𝓂[K]) :=
    (LocalFieldTheory.DiscreteValuationField.CompleteDVF.mrangeRestrict_integer_isAdic F)
  have hcomplete : IsAdicComplete (𝓂[K]) 𝒪[K] := by
    change
      IsAdicComplete
        (IsLocalRing.maximalIdeal (LocalFieldTheory.DiscreteValuationField.CompleteDVF.mrangeRestrict F).valuationSubring)
        (LocalFieldTheory.DiscreteValuationField.CompleteDVF.mrangeRestrict F).valuationSubring
    exact (LocalFieldTheory.DiscreteValuationField.CompleteDVF.mrangeRestrict_isAdicComplete F)
  exact (hadic.isAdicComplete_iff.mp hcomplete).1

/-- The valuation ring of a range-restricted complete DVF with finite residue
field is compact.  This is the compactness input in the local-field structure theory,
the local compactness criterion. -/
theorem mrangeRestrict_integer_compactSpace_of_residueField_finite
    (F : CompleteDVF.{u, v} K) [Finite F.residueField] :
    letI : Valued K
        (MonoidHom.mrange F.valuation.toMonoidWithZeroHom) :=
      (LocalFieldTheory.DiscreteValuationField.CompleteDVF.mrangeRestrictValued F)
    letI : NontriviallyNormedField K :=
      (LocalFieldTheory.DiscreteValuationField.CompleteDVF.mrangeRestrict_nontriviallyNormedField F)
    CompactSpace 𝒪[K] := by
  let : Valued K
      (MonoidHom.mrange F.valuation.toMonoidWithZeroHom) :=
    (LocalFieldTheory.DiscreteValuationField.CompleteDVF.mrangeRestrictValued F)
  have :
      (Valued.v :
        _root_.Valuation K
          (MonoidHom.mrange
            F.valuation.toMonoidWithZeroHom)).IsRankOneDiscrete :=
    (LocalFieldTheory.DiscreteValuationField.CompleteDVF.mrangeRestrict_isRankOneDiscrete F)
  have :
      (Valued.v :
        _root_.Valuation K
          (MonoidHom.mrange
            F.valuation.toMonoidWithZeroHom)).RankOne :=
    mrangeRestrictValued_rankOne F
  let : NontriviallyNormedField K :=
    Valued.toNontriviallyNormedField
      (L := K)
      (Γ₀ := MonoidHom.mrange
        F.valuation.toMonoidWithZeroHom)
  have : IsUltrametricDist K := by infer_instance
  have : IsDiscreteValuationRing 𝒪[K] := by
    change
      IsDiscreteValuationRing
        (Valued.v :
          _root_.Valuation K
            (MonoidHom.mrange
              F.valuation.toMonoidWithZeroHom)).valuationSubring
    infer_instance
  have : Finite 𝓀[K] := by
    change
      Finite
        (IsLocalRing.ResidueField (LocalFieldTheory.DiscreteValuationField.CompleteDVF.mrangeRestrict F).valuationSubring)
    exact (LocalFieldTheory.DiscreteValuationField.CompleteDVF.mrangeRestrict_residueField_finite F)
  have hcomplete : CompleteSpace 𝒪[K] :=
    (LocalFieldTheory.DiscreteValuationField.CompleteDVF.mrangeRestrict_integer_completeSpace F)
  exact
    (Valued.integer.compactSpace_iff_completeSpace_and_isDiscreteValuationRing_and_finite_residueField
      (K := K)
      (Γ₀ := MonoidHom.mrange F.valuation.toMonoidWithZeroHom)).2
      ⟨hcomplete, inferInstance, inferInstance⟩

/-- A range-restricted complete DVF with finite residue field is proper for
the associated normed-field topology. -/
theorem mrangeRestrict_properSpace_of_residueField_finite
    (F : CompleteDVF.{u, v} K) [Finite F.residueField] :
    letI : Valued K
        (MonoidHom.mrange F.valuation.toMonoidWithZeroHom) :=
      (LocalFieldTheory.DiscreteValuationField.CompleteDVF.mrangeRestrictValued F)
    letI : NontriviallyNormedField K :=
      (LocalFieldTheory.DiscreteValuationField.CompleteDVF.mrangeRestrict_nontriviallyNormedField F)
    ProperSpace K := by
  let : Valued K
      (MonoidHom.mrange F.valuation.toMonoidWithZeroHom) :=
    (LocalFieldTheory.DiscreteValuationField.CompleteDVF.mrangeRestrictValued F)
  have :
      (Valued.v :
        _root_.Valuation K
          (MonoidHom.mrange
            F.valuation.toMonoidWithZeroHom)).RankOne :=
    mrangeRestrictValued_rankOne F
  let : NontriviallyNormedField K :=
    (LocalFieldTheory.DiscreteValuationField.CompleteDVF.mrangeRestrict_nontriviallyNormedField F)
  have hcompact : CompactSpace 𝒪[K] :=
    (LocalFieldTheory.DiscreteValuationField.CompleteDVF.mrangeRestrict_integer_compactSpace_of_residueField_finite F)
  unfold mrangeRestrict_nontriviallyNormedField
  unfold Valued.toNontriviallyNormedField
  change @ProperSpace K
    (Valued.toNormedField K
      (MonoidHom.mrange F.valuation.toMonoidWithZeroHom)
      (val := LocalFieldTheory.DiscreteValuationField.CompleteDVF.mrangeRestrictValued F)
      (hv := mrangeRestrictValued_rankOne F)).toPseudoMetricSpace
  exact
    (@Valued.integer.properSpace_iff_compactSpace_integer
      K
      (MonoidHom.mrange F.valuation.toMonoidWithZeroHom)
      inferInstance inferInstance
      (LocalFieldTheory.DiscreteValuationField.CompleteDVF.mrangeRestrictValued F)
      (mrangeRestrictValued_rankOne F)).2 hcompact

/-- A range-restricted complete DVF with finite residue field is complete for
the associated normed-field topology. -/
theorem mrangeRestrict_completeSpace_of_residueField_finite
    (F : CompleteDVF.{u, v} K) [Finite F.residueField] :
    letI : Valued K
        (MonoidHom.mrange F.valuation.toMonoidWithZeroHom) :=
      (LocalFieldTheory.DiscreteValuationField.CompleteDVF.mrangeRestrictValued F)
    letI : NontriviallyNormedField K :=
      (LocalFieldTheory.DiscreteValuationField.CompleteDVF.mrangeRestrict_nontriviallyNormedField F)
    CompleteSpace K := by
  let Γ : Type v :=
    MonoidHom.mrange F.valuation.toMonoidWithZeroHom
  let : Valued K Γ := (LocalFieldTheory.DiscreteValuationField.CompleteDVF.mrangeRestrictValued F)
  let : NontriviallyNormedField K :=
    (LocalFieldTheory.DiscreteValuationField.CompleteDVF.mrangeRestrict_nontriviallyNormedField F)
  have : ProperSpace K :=
    (LocalFieldTheory.DiscreteValuationField.CompleteDVF.mrangeRestrict_properSpace_of_residueField_finite F)
  exact complete_of_proper

end CompleteDVF
end LocalFieldTheory.DiscreteValuationField

end
end

section
-- module Solutions.OAIQ244_DUKE.LocalField_DiscreteValuationField_ValuationSubringUnits_LocalFieldRangeRestriction
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

/-!
# Multiplicative-range restriction for local fields

This file packages range restriction as a `LocalField` and exposes the
properness and completeness of the resulting topology.
-/

noncomputable section

universe u v

open scoped Valued

namespace LocalFieldTheory.DiscreteValuationField
open ValuationTheory.DiscreteValuationField

namespace LocalField

variable {K : Type u} [Field K]

/-- The range-restricted topology attached to a local-field package is proper. -/
theorem mrangeRestrict_properSpace
    (F : LocalField.{u, v} K) :
    letI : Valued K
        (MonoidHom.mrange
          F.toCompleteDVF.valuation.toMonoidWithZeroHom) :=
      (LocalFieldTheory.DiscreteValuationField.CompleteDVF.mrangeRestrictValued F.toCompleteDVF)
    letI : NontriviallyNormedField K :=
      (LocalFieldTheory.DiscreteValuationField.CompleteDVF.mrangeRestrict_nontriviallyNormedField F.toCompleteDVF)
    ProperSpace K := by
  exact
    (LocalFieldTheory.DiscreteValuationField.CompleteDVF.mrangeRestrict_properSpace_of_residueField_finite F.toCompleteDVF)

/-- The range-restricted topology attached to a local-field package is complete. -/
theorem mrangeRestrict_completeSpace
    (F : LocalField.{u, v} K) :
    letI : Valued K
        (MonoidHom.mrange
          F.toCompleteDVF.valuation.toMonoidWithZeroHom) :=
      (LocalFieldTheory.DiscreteValuationField.CompleteDVF.mrangeRestrictValued F.toCompleteDVF)
    letI : NontriviallyNormedField K :=
      (LocalFieldTheory.DiscreteValuationField.CompleteDVF.mrangeRestrict_nontriviallyNormedField F.toCompleteDVF)
    CompleteSpace K := by
  exact
    (LocalFieldTheory.DiscreteValuationField.CompleteDVF.mrangeRestrict_completeSpace_of_residueField_finite F.toCompleteDVF)


end LocalField
end LocalFieldTheory.DiscreteValuationField

end
end

section
-- module Solutions.OAIQ244_DUKE.LocalField_DiscreteValuationField_MixedCharacteristicQp
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

/-!
# Mixed-characteristic input for the `Qp` branch of the local-field structure classification

This file keeps the converse direction of the local-field structure theory, the local-field structure classification focused on the mixed-characteristic case.  The key point proved here is
that the actual range-restricted local-field valuation still restricts on
`ℚ` to the usual `p`-adic valuation, where `p` is the residue characteristic.
-/

noncomputable section

universe u v

open LocalFieldTheory.DiscreteValuationField

namespace LocalFieldTheory.DiscreteValuationField
namespace LocalField

open scoped WithZero

variable {K : Type u} [Field K]

/-- The `p`-adic closure subfield is complete for the restricted valuation topology. -/
theorem qpadicClosureSubfield_completeSpace
    (F : LocalField.{u, v} K) [CharZero K] :
    letI : Valued K F.mrangeValueGroup :=
      _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.mrangeRestrictValued F.toCompleteDVF
    letI : NontriviallyNormedField K :=
      _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.mrangeRestrict_nontriviallyNormedField F.toCompleteDVF
    CompleteSpace F.qpadicClosureSubfield := by
  let : Valued K F.mrangeValueGroup :=
    _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.mrangeRestrictValued F.toCompleteDVF
  let : NontriviallyNormedField K :=
    _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.mrangeRestrict_nontriviallyNormedField F.toCompleteDVF
  have : CompleteSpace K :=
    F.mrangeRestrict_completeSpace
  exact
    (F.qpadicClosureSubfield_isClosed).completeSpace_coe

end LocalField
end LocalFieldTheory.DiscreteValuationField
end
end

section
-- module Solutions.OAIQ244_DUKE.LocalField_DiscreteValuationField_WithZeroValuationTopology
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_isCompleteDiscrete _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.LubinTate.Valuations.exponentialValuationSubringIsLocalRing _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionFixedSubring.instIsLocalRing _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

/-!
# The direct topology of a standard multiplicative integer valuation

This file transfers completeness from the actual-range restriction of a
complete discrete valuation back to the topology obtained directly from
`Valued.mk' v`.
-/

noncomputable section

universe u

open Filter
open scoped Valued
open LocalFieldTheory.DiscreteValuationField
open ValuationTheory.DiscreteValuationField

namespace LocalFieldTheory.DiscreteValuationField
namespace WithZeroValuationTopology

variable {K : Type u} [Field K]

/-- A standard complete discrete valuation with finite residue field makes the
field complete for the topology obtained directly from `Valued.mk' v`. -/
theorem completeSpace_ofWithZeroValuation
    (v : _root_.Valuation K (WithZero (Multiplicative ℤ)))
    [Valuation.IsCompleteDiscrete v]
    [Finite (IsLocalRing.ResidueField v.valuationSubring)] :
    letI : Valued K (WithZero (Multiplicative ℤ)) := Valued.mk' v
    CompleteSpace K := by
  let F : CompleteDVF.{u, 0} K := completeDVF v
  let direct : Valued K (WithZero (Multiplicative ℤ)) := Valued.mk' v
  let restrictedNormed : NontriviallyNormedField K :=
    _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.mrangeRestrict_nontriviallyNormedField F
  have : Finite F.residueField := by
    change Finite (IsLocalRing.ResidueField v.valuationSubring)
    infer_instance
  have hcomplete : @CompleteSpace K restrictedNormed.toUniformSpace := by
    exact _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.mrangeRestrict_completeSpace_of_residueField_finite F
  have huniform : direct.toUniformSpace = restrictedNormed.toUniformSpace := by
    change
      (Valued.mk' v).toUniformSpace =
        (_root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.mrangeRestrict_nontriviallyNormedField
          (completeDVF v)).toUniformSpace
    calc
      (Valued.mk' v).toUniformSpace =
          (_root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.mrangeRestrictValued
            (completeDVF v)).toUniformSpace :=
        valuedMk_uniformSpace_eq_mrangeRestrict v
      _ =
          (_root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.mrangeRestrict_nontriviallyNormedField
            (completeDVF v)).toUniformSpace := by
        rfl
  let : Valued K (WithZero (Multiplicative ℤ)) := direct
  change @CompleteSpace K direct.toUniformSpace
  rw [huniform]
  exact hcomplete

end WithZeroValuationTopology
end LocalFieldTheory.DiscreteValuationField
end
end

section
-- module Solutions.OAIQ244_DUKE.LocalField_Padic_PrincipalUnits
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionResidueField.instField _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

/-!
# Principal units of the p-adic field

This file identifies the standard p-adic integer and complete-DVF models,
computes their principal-unit quotients, and records the logarithm/exponential
power formulas used by local cyclotomic norm calculations.
-/

noncomputable section

open scoped ValuativeRel WithZero

namespace LocalFieldTheory.Padic

open LocalFieldTheory
open ValuationTheory
open LocalFieldTheory.IsNonarchimedeanLocalField

variable (p : ℕ) [Fact p.Prime]

/-- The rational prime `p`, regarded as an element of the p-adic integer
ring. -/
noncomputable def padicPrimeInteger : 𝒪[ℚ_[p]] :=
  (integerRingEquivPadicInt p).symm (p : ℤ_[p])

end LocalFieldTheory.Padic

end
end

section
-- module Solutions.OAIQ244_DUKE.Valuation_DiscreteValuationField_FiniteIntegralClosure
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_isCompleteDiscrete _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.HilbertRamification.Dedekind.basePrime_isPrime _root_.LocalFieldTheory.DiscreteValuationField.Examples.Qp.padicDVRValuation_isRankOneDiscrete _root_.LocalFieldTheory.DiscreteValuationField.LocalField.residueField_charP_residueCharacteristic _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.LubinTate.Valuations.exponentialValuationSubringIsLocalRing _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionFixedMaximalIdeal.instIsMaximal _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionFixedSubring.instIsLocalRing _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionResidueField.instField _root_.RamificationTheory.HilbertRamification.ValuationSubring.selectedResidueField.instAlgebra _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.RelativeIdeleGroup.relativeIdeleMulAction _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.relativeAdeleRingIntermediateAlgebra _root_.relativeAdeleRingTopIntermediateAlgebra
attribute [-simp] _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.coe_valuationSubringUnitsToFieldUnits_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.fieldUnitValueUnit_mul _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.fieldUnitValueUnit_one _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.mrangeRestrict_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.multiplicativeIntegerValuationOfUniformizer_val _root_.LocalFieldTheory.residueField_algebraMap_residue
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

namespace ValuationTheory

/-!
# Finite integral closures over complete DVFs

This file provides record-free theorems for the integral closure
of a complete-DVF valuation ring in a finite separable field extension.
-/

noncomputable section

universe u v w

namespace DiscreteValuationField
namespace ValuedExtension

open _root_.ValuationTheory.DiscreteValuationField.Valuation

variable {K : Type u} {L : Type w} [Field K] [Field L]
variable [Algebra K L] [FiniteDimensional K L]

/- The algebra map from the base valuation ring into the integral
closure is injective. -/

/-- In a finite separable extension of a complete DVF, the actual integral
closure is complete for the ideal generated by the base maximal ideal. -/
theorem integralClosure_base_maximal_map_isAdicComplete_of_finite_separable
    (base : CompleteDVF.{u, v} K)
    [Algebra.IsSeparable K L] :
    IsAdicComplete
      (base.maximalIdeal.map
        (algebraMap base.valuationSubring
          (integralClosure base.valuationSubring L)))
      (integralClosure base.valuationSubring L) := by
  let : IsNoetherianRing base.valuationSubring :=
    base_valuationSubring_isNoetherianRing (K := K) base
  let : IsFractionRing base.valuationSubring K :=
    base_valuationSubring_isFractionRing (K := K) base
  let : IsIntegrallyClosed base.valuationSubring :=
    base_valuationSubring_isIntegrallyClosed (K := K) base
  let : Module.Finite base.valuationSubring
      (integralClosure base.valuationSubring L) :=
    IsIntegralClosure.finite base.valuationSubring K L
      (integralClosure base.valuationSubring L)
  have : IsAdicComplete base.maximalIdeal base.valuationSubring :=
    base.isAdicComplete
  have hcomplete :
      IsAdicComplete base.maximalIdeal
        (integralClosure base.valuationSubring L) :=
    ValuationTheory.DiscreteValuationField.isAdicComplete_of_moduleFinite
      (I := base.maximalIdeal)
  exact
    (isAdicComplete_map_algebraMap_iff
      (I := base.maximalIdeal)
      (S := integralClosure base.valuationSubring L)).mpr hcomplete

/-- In a finite separable extension of a complete DVF, the actual integral
closure of the base valuation ring is Henselian along the ideal generated by
the base maximal ideal.

This is independent of any pre-existing `Extension` record.  It is the
source-producing input used before canonical ramification and residue
invariants have been packaged. -/
theorem integralClosure_henselianRing_of_finite_separable
    (base : CompleteDVF.{u, v} K)
    [Algebra.IsSeparable K L] :
    HenselianRing (integralClosure base.valuationSubring L)
      (base.maximalIdeal.map
        (algebraMap base.valuationSubring
          (integralClosure base.valuationSubring L))) := by
  let :
      IsAdicComplete
        (base.maximalIdeal.map
          (algebraMap base.valuationSubring
            (integralClosure base.valuationSubring L)))
        (integralClosure base.valuationSubring L) :=
    integralClosure_base_maximal_map_isAdicComplete_of_finite_separable
      (K := K) (L := L) base
  infer_instance

/-- In a finite separable extension of a complete DVF, the residue fiber of the
actual integral closure over the base maximal ideal has at most one prime.

The proof combines finite Artinian residue fibers with Henselian idempotent
lifting from `integralClosure_henselianRing_of_finite_separable`. -/
theorem integralClosure_base_maximal_fiber_subsingleton_of_finite_separable
    (base : CompleteDVF.{u, v} K)
    [Algebra.IsSeparable K L] :
    Subsingleton
      (PrimeSpectrum
        (base.maximalIdeal.Fiber (integralClosure base.valuationSubring L))) := by
  let B := integralClosure base.valuationSubring L
  let : IsNoetherianRing base.valuationSubring :=
    base_valuationSubring_isNoetherianRing (K := K) base
  let : IsFractionRing base.valuationSubring K :=
    base_valuationSubring_isFractionRing (K := K) base
  let : IsIntegrallyClosed base.valuationSubring :=
    base_valuationSubring_isIntegrallyClosed (K := K) base
  let : Module.Finite base.valuationSubring B :=
    IsIntegralClosure.finite base.valuationSubring K L B
  let : Algebra.QuasiFinite base.valuationSubring B := by
    infer_instance
  let : IsArtinianRing (base.maximalIdeal.Fiber B) := by
    infer_instance
  refine primeSpectrum_subsingleton_of_isArtinianRing_of_idempotents_trivial ?_
  intro e he
  let : HenselianRing B
      (base.maximalIdeal.map (algebraMap base.valuationSubring B)) :=
    integralClosure_henselianRing_of_finite_separable (K := K) (L := L) base
  let : HenselianRing B
      (RingHom.ker
        ((Algebra.TensorProduct.includeRight :
          B →ₐ[base.valuationSubring] base.maximalIdeal.Fiber B) :
          B →+* base.maximalIdeal.Fiber B)) := by
    rw [maximalIdeal_fiber_includeRight_ker_eq_maximalIdeal_map
      (R := base.valuationSubring) (S := B)]
    infer_instance
  let φ : B →+* base.maximalIdeal.Fiber B :=
    (Algebra.TensorProduct.includeRight :
      B →ₐ[base.valuationSubring] base.maximalIdeal.Fiber B)
  have hsurj : Function.Surjective φ := by
    simpa [φ] using
      (maximalIdeal_fiber_includeRight_surjective
        (R := base.valuationSubring) (S := B))
  rcases exists_idempotent_lift_of_surjective_henselianRing_ker
      φ hsurj e he with
    ⟨b, hbidem, hbmap⟩
  let : IsDomain B := by
    change IsDomain (integralClosure base.valuationSubring L)
    infer_instance
  rcases IsIdempotentElem.iff_eq_zero_or_one.mp hbidem with rfl | rfl
  · left
    rw [← hbmap]
    simp [φ]
  · right
    rw [← hbmap]
    exact (Algebra.TensorProduct.includeRight :
      B →ₐ[base.valuationSubring] base.maximalIdeal.Fiber B).map_one

/-- In a finite separable extension of a complete DVF, the actual integral
closure of the base valuation ring is local.

This is the record-free localness form of the Henselian finite-extension
frontier.  It uses the residue-fiber singleton theorem above and integral
lies-over, without assuming a chosen target
valuation ring. -/
theorem integralClosure_isLocalRing_of_finite_separable
    (base : CompleteDVF.{u, v} K)
    [Algebra.IsSeparable K L] :
    IsLocalRing (integralClosure base.valuationSubring L) := by
  let B := integralClosure base.valuationSubring L
  let : Algebra.IsIntegral base.valuationSubring B := by
    change Algebra.IsIntegral base.valuationSubring
      (integralClosure base.valuationSubring L)
    infer_instance
  let : FaithfulSMul base.valuationSubring B :=
    CanonicalIntegralClosure.faithfulSMul (K := K) (L := L) base
  have hNonempty :
      Nonempty (Ideal.primesOver base.maximalIdeal B) := by
    rcases Ideal.exists_maximal_ideal_liesOver_of_isIntegral
        (S := B) base.maximalIdeal with
      ⟨P, hPmax, hPover⟩
    exact ⟨⟨P, hPmax.isPrime, hPover⟩⟩
  let : Subsingleton (PrimeSpectrum (base.maximalIdeal.Fiber B)) :=
    integralClosure_base_maximal_fiber_subsingleton_of_finite_separable
      (K := K) (L := L) base
  have hPrimeSub :
      Subsingleton (Ideal.primesOver base.maximalIdeal B) := by
    constructor
    intro P Q
    let e := PrimeSpectrum.primesOverOrderIsoFiber
      base.valuationSubring B base.maximalIdeal
    exact e.injective (Subsingleton.elim (e P) (e Q))
  rcases hNonempty with ⟨P⟩
  have hPrimesSingleton :
      Ideal.primesOver base.maximalIdeal B = {P.1} := by
    let : Subsingleton (Ideal.primesOver base.maximalIdeal B) := hPrimeSub
    refine Set.eq_singleton_iff_unique_mem.mpr ⟨P.2, ?_⟩
    intro Q hQ
    exact congrArg Subtype.val
      (Subsingleton.elim
        (⟨Q, hQ⟩ : Ideal.primesOver base.maximalIdeal B) P)
  have hPmem : P.1 ∈ Ideal.primesOver base.maximalIdeal B := P.2
  let : Nonempty (MaximalSpectrum B) :=
    ⟨⟨P.1, Ideal.isMaximal_of_mem_primesOver hPmem⟩⟩
  have hMaxSub : Subsingleton (MaximalSpectrum B) := by
    constructor
    intro M N
    apply MaximalSpectrum.ext
    have hMcomap :
        (M.asIdeal.comap (algebraMap base.valuationSubring B)) =
          base.maximalIdeal :=
      IsLocalRing.eq_maximalIdeal
        (Ideal.isMaximal_comap_of_isIntegral_of_isMaximal'
          (algebraMap base.valuationSubring B)
          (algebraMap_isIntegral_iff.mpr inferInstance) M.asIdeal)
    have hNcomap :
        (N.asIdeal.comap (algebraMap base.valuationSubring B)) =
          base.maximalIdeal :=
      IsLocalRing.eq_maximalIdeal
        (Ideal.isMaximal_comap_of_isIntegral_of_isMaximal'
          (algebraMap base.valuationSubring B)
          (algebraMap_isIntegral_iff.mpr inferInstance) N.asIdeal)
    have hMmem :
        M.asIdeal ∈ Ideal.primesOver base.maximalIdeal B :=
      ⟨M.isMaximal.isPrime, ⟨hMcomap.symm⟩⟩
    have hNmem :
        N.asIdeal ∈ Ideal.primesOver base.maximalIdeal B :=
      ⟨N.isMaximal.isPrime, ⟨hNcomap.symm⟩⟩
    have hMeq : M.asIdeal = P.1 := by
      simpa [hPrimesSingleton] using hMmem
    have hNeq : N.asIdeal = P.1 := by
      simpa [hPrimesSingleton] using hNmem
    exact hMeq.trans hNeq.symm
  exact IsLocalRing.of_singleton_maximalSpectrum

/-- The maximal ideal of the integral closure, using the finite
separable localness theorem above. -/
noncomputable def CanonicalIntegralClosure.maximalIdeal
    (base : CompleteDVF.{u, v} K)
    [Algebra.IsSeparable K L] :
    Ideal (integralClosure base.valuationSubring L) :=
  letI : IsLocalRing (integralClosure base.valuationSubring L) :=
    integralClosure_isLocalRing_of_finite_separable (K := K) (L := L) base
  IsLocalRing.maximalIdeal (integralClosure base.valuationSubring L)

/-- In the actual integral closure, the ideal generated by the base maximal
ideal is contained in the upstairs maximal ideal. -/
theorem integralClosure_base_maximal_map_le_maximalIdeal_of_finite_separable
    (base : CompleteDVF.{u, v} K)
    [Algebra.IsSeparable K L] :
    base.maximalIdeal.map
        (algebraMap base.valuationSubring
          (integralClosure base.valuationSubring L)) ≤
      CanonicalIntegralClosure.maximalIdeal (K := K) (L := L) base := by
  let B := integralClosure base.valuationSubring L
  let : IsLocalRing B :=
    integralClosure_isLocalRing_of_finite_separable (K := K) (L := L) base
  change
    base.maximalIdeal.map (algebraMap base.valuationSubring B) ≤
      IsLocalRing.maximalIdeal B
  let : Algebra.IsIntegral base.valuationSubring B := by
    change Algebra.IsIntegral base.valuationSubring
      (integralClosure base.valuationSubring L)
    infer_instance
  have hlocal : IsLocalHom (algebraMap base.valuationSubring B) :=
    (algebraMap_isIntegral_iff.mpr
      (show Algebra.IsIntegral base.valuationSubring B from inferInstance)
    ).isLocalHom
      (CanonicalIntegralClosure.algebraMap_injective (K := K) (L := L) base)
  exact
    ((IsLocalRing.local_hom_TFAE
      (algebraMap base.valuationSubring B)).out (1-1) (3-1)).mp hlocal

/- In the actual integral closure, the ideal generated by the base maximal
ideal is nonzero. -/
omit [FiniteDimensional K L] in
/-- In a finite separable extension, the image of the base maximal ideal is nonzero. -/
theorem integralClosure_base_maximal_map_ne_bot_of_finite_separable
    (base : CompleteDVF.{u, v} K)
    [Algebra.IsSeparable K L] :
    base.maximalIdeal.map
      (algebraMap base.valuationSubring
        (integralClosure base.valuationSubring L)) ≠ ⊥ := by
  intro hbot
  exact base.maximalIdeal_ne_bot
    ((Ideal.map_eq_bot_iff_of_injective
      (CanonicalIntegralClosure.algebraMap_injective (K := K) (L := L) base)).1
      hbot)

/- In a finite separable extension of a complete DVF, the actual integral
closure of the base valuation ring is not a field. -/

/-- In a finite separable extension of a complete DVF, the actual integral
closure of the base valuation ring is a DVR. -/
theorem integralClosure_isDiscreteValuationRing_of_finite_separable
    (base : CompleteDVF.{u, v} K)
    [Algebra.IsSeparable K L] :
    IsDiscreteValuationRing (integralClosure base.valuationSubring L) := by
  let : IsLocalRing (integralClosure base.valuationSubring L) :=
    integralClosure_isLocalRing_of_finite_separable (K := K) (L := L) base
  let : IsFractionRing base.valuationSubring K :=
    base_valuationSubring_isFractionRing (K := K) base
  let : IsDomain (integralClosure base.valuationSubring L) := by
    infer_instance
  let : IsDedekindDomain (integralClosure base.valuationSubring L) := by
    exact integralClosure.isDedekindDomain base.valuationSubring K L
  let : IsNoetherianRing (integralClosure base.valuationSubring L) := by
    exact integralClosure.isNoetherianRing (A := base.valuationSubring) (K := K) L
  have hnot :
      ¬ IsField (integralClosure base.valuationSubring L) :=
    integralClosure_not_isField_of_finite_separable
      (K := K) (L := L) base
  exact
    ((IsDiscreteValuationRing.TFAE
      (integralClosure base.valuationSubring L) hnot).out (3-1) (1-1)).mp
      (show IsDedekindDomain (integralClosure base.valuationSubring L) from
        inferInstance)

/-- In the actual integral closure, the ideal generated by the base maximal
ideal is a power of the upstairs maximal ideal. -/
theorem exists_integralClosure_base_maximal_map_eq_maximalIdeal_pow
    (base : CompleteDVF.{u, v} K)
    [Algebra.IsSeparable K L] :
    ∃ n : ℕ,
      base.maximalIdeal.map
          (algebraMap base.valuationSubring
            (integralClosure base.valuationSubring L)) =
        CanonicalIntegralClosure.maximalIdeal (K := K) (L := L) base ^ n := by
  let B := integralClosure base.valuationSubring L
  let : IsLocalRing B :=
    integralClosure_isLocalRing_of_finite_separable (K := K) (L := L) base
  change
    ∃ n : ℕ,
      base.maximalIdeal.map (algebraMap base.valuationSubring B) =
        IsLocalRing.maximalIdeal B ^ n
  let : IsDomain B := by
    change IsDomain (integralClosure base.valuationSubring L)
    infer_instance
  let : IsDiscreteValuationRing B :=
    integralClosure_isDiscreteValuationRing_of_finite_separable
      (K := K) (L := L) base
  have hI :
      base.maximalIdeal.map
          (algebraMap base.valuationSubring B) ≠ ⊥ :=
    integralClosure_base_maximal_map_ne_bot_of_finite_separable
      (K := K) (L := L) base
  obtain ⟨pi, hpi⟩ := IsDiscreteValuationRing.exists_irreducible B
  obtain ⟨n, hn⟩ :=
    IsDiscreteValuationRing.ideal_eq_span_pow_irreducible hI hpi
  refine ⟨n, ?_⟩
  rw [hn, ← Ideal.span_singleton_pow, ← hpi.maximalIdeal_eq]

/-- In the actual integral closure, the ideal generated by the base maximal
ideal is a positive power of the upstairs maximal ideal. -/
theorem exists_integralClosure_base_maximal_map_eq_maximalIdeal_pow_pos
    (base : CompleteDVF.{u, v} K)
    [Algebra.IsSeparable K L] :
    ∃ n : ℕ,
      0 < n ∧
        base.maximalIdeal.map
            (algebraMap base.valuationSubring
              (integralClosure base.valuationSubring L)) =
          CanonicalIntegralClosure.maximalIdeal (K := K) (L := L) base ^ n := by
  let B := integralClosure base.valuationSubring L
  let : IsLocalRing B :=
    integralClosure_isLocalRing_of_finite_separable (K := K) (L := L) base
  change
    ∃ n : ℕ,
      0 < n ∧
        base.maximalIdeal.map (algebraMap base.valuationSubring B) =
          IsLocalRing.maximalIdeal B ^ n
  obtain ⟨n, hn⟩ :=
    exists_integralClosure_base_maximal_map_eq_maximalIdeal_pow
      (K := K) (L := L) base
  refine ⟨n, ?_, hn⟩
  by_contra hnot
  have hn0 : n = 0 := Nat.eq_zero_of_not_pos hnot
  have htop :
      base.maximalIdeal.map (algebraMap base.valuationSubring B) = ⊤ := by
    simpa [hn0] using hn
  have hle :
      base.maximalIdeal.map (algebraMap base.valuationSubring B) ≤
        IsLocalRing.maximalIdeal B :=
    integralClosure_base_maximal_map_le_maximalIdeal_of_finite_separable
      (K := K) (L := L) base
  have htop_le : (⊤ : Ideal B) ≤ IsLocalRing.maximalIdeal B := by
    simpa [htop] using hle
  exact
    (IsLocalRing.maximalIdeal.isMaximal B).ne_top
      (top_le_iff.mp htop_le)

/-- In a finite separable extension of a complete DVF, the actual integral
closure is complete for its own maximal ideal. -/
theorem integralClosure_maximalIdeal_isAdicComplete_of_finite_separable
    (base : CompleteDVF.{u, v} K)
    [Algebra.IsSeparable K L] :
    IsAdicComplete
      (CanonicalIntegralClosure.maximalIdeal (K := K) (L := L) base)
      (integralClosure base.valuationSubring L) := by
  let B := integralClosure base.valuationSubring L
  let : IsLocalRing B :=
    integralClosure_isLocalRing_of_finite_separable (K := K) (L := L) base
  change IsAdicComplete (IsLocalRing.maximalIdeal B) B
  obtain ⟨n, hnpos, hn⟩ :=
    exists_integralClosure_base_maximal_map_eq_maximalIdeal_pow_pos
      (K := K) (L := L) base
  have hmap :
      IsAdicComplete
        (base.maximalIdeal.map (algebraMap base.valuationSubring B)) B :=
    integralClosure_base_maximal_map_isAdicComplete_of_finite_separable
      (K := K) (L := L) base
  let :
      IsAdicComplete ((IsLocalRing.maximalIdeal B) ^ n) B := by
    have hn' :
        base.maximalIdeal.map (algebraMap base.valuationSubring B) =
          IsLocalRing.maximalIdeal B ^ n := by
      simpa [CanonicalIntegralClosure.maximalIdeal] using hn
    simpa [hn'] using hmap
  exact
    isAdicComplete_of_isAdicComplete_pow
      (M := B) (IsLocalRing.maximalIdeal B) hnpos

/-- The actual integral closure supplies a complete-DVF target whose valuation
subring is ring-equivalent to the actual integral closure. -/
theorem exists_integralClosure_standard_completeDVF
    (base : CompleteDVF.{u, v} K)
    [Algebra.IsSeparable K L] :
    ∃ target : CompleteDVF.{w, 0} L,
      (∀ z : L,
        z ∈ target.valuation.valuationSubring ↔
          z ∈ (integralClosure base.valuationSubring L).toSubring) ∧
          ∃ _ : (integralClosure base.valuationSubring L) ≃+*
            target.valuationSubring,
            True := by
  let B := integralClosure base.valuationSubring L
  let : IsLocalRing B :=
    integralClosure_isLocalRing_of_finite_separable (K := K) (L := L) base
  let : IsDomain B := by
    change IsDomain (integralClosure base.valuationSubring L)
    infer_instance
  let : IsDiscreteValuationRing B :=
    integralClosure_isDiscreteValuationRing_of_finite_separable
      (K := K) (L := L) base
  let : IsFractionRing B L := by
    change IsFractionRing (integralClosure base.valuationSubring L) L
    exact integralClosure.isFractionRing_of_finite_extension K L
  let vL := (IsDiscreteValuationRing.maximalIdeal B).valuation L
  let e : B ≃+* vL.valuationSubring :=
    IsDiscreteValuationRing.equivValuationSubring (A := B) (K := L)
  let : Algebra B vL.valuationSubring := e.toRingHom.toAlgebra
  let eLin : B ≃ₗ[B] vL.valuationSubring :=
    { toFun := e
      invFun := e.symm
      left_inv := e.left_inv
      right_inv := e.right_inv
      map_add' := e.map_add
      map_smul' := by
        intro r x
        change e (r * x) = (algebraMap B vL.valuationSubring r) * e x
        simp [RingHom.algebraMap_toAlgebra] }
  have :
      IsAdicComplete (IsLocalRing.maximalIdeal B) B :=
    integralClosure_maximalIdeal_isAdicComplete_of_finite_separable
      (K := K) (L := L) base
  have hcompleteAsB :
      IsAdicComplete (IsLocalRing.maximalIdeal B) vL.valuationSubring :=
    isAdicComplete_of_linearEquiv
      (M := B) (N := vL.valuationSubring)
      (IsLocalRing.maximalIdeal B) eLin
  have hcompleteMap :
      IsAdicComplete
        ((IsLocalRing.maximalIdeal B).map
          (algebraMap B vL.valuationSubring))
        vL.valuationSubring :=
    (isAdicComplete_map_algebraMap_iff
      (I := IsLocalRing.maximalIdeal B)
      (S := vL.valuationSubring)).2 hcompleteAsB
  have hmem (x : B) :
      algebraMap B vL.valuationSubring x ∈
          IsLocalRing.maximalIdeal vL.valuationSubring ↔
        x ∈ IsLocalRing.maximalIdeal B := by
    simp only [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
    constructor
    · intro hx hunit
      exact hx (hunit.map (algebraMap B vL.valuationSubring))
    · intro hx hunit
      apply hx
      have hpre := hunit.map e.symm.toRingHom
      simpa [RingHom.algebraMap_toAlgebra] using hpre
  have hmapMax :
      (IsLocalRing.maximalIdeal B).map
          (algebraMap B vL.valuationSubring) =
        IsLocalRing.maximalIdeal vL.valuationSubring := by
    apply le_antisymm
    · rw [Ideal.map_le_iff_le_comap]
      intro x hx
      exact (hmem x).2 hx
    · intro y hy
      have hx :
          e.symm y ∈ IsLocalRing.maximalIdeal B := by
        apply (hmem (e.symm y)).1
        simpa [RingHom.algebraMap_toAlgebra] using hy
      have hmap :=
        Ideal.mem_map_of_mem (algebraMap B vL.valuationSubring) hx
      simpa [RingHom.algebraMap_toAlgebra] using hmap
  have hcompletev :
      IsAdicComplete
        (IsLocalRing.maximalIdeal vL.valuationSubring)
        vL.valuationSubring := by
    simpa [hmapMax] using hcompleteMap
  have hmapSub :
      Subring.map (algebraMap B L) ⊤ =
        vL.valuationSubring.toSubring :=
    IsDiscreteValuationRing.map_algebraMap_eq_valuationSubring
      (A := B) (K := L)
  have hmemStandard (z : L) :
      z ∈ vL.valuationSubring ↔ z ∈ B.toSubring := by
    constructor
    · intro hz
      have hzmap :
          z ∈ Subring.map (algebraMap B L) ⊤ := by
        simpa [hmapSub] using hz
      rcases hzmap with ⟨b, _hbtop, hb⟩
      rw [← hb]
      exact b.2
    · intro hz
      have hzmap :
          z ∈ Subring.map (algebraMap B L) ⊤ :=
        ⟨⟨z, hz⟩, trivial, rfl⟩
      simpa [hmapSub] using hzmap
  let : Valuation.IsCompleteDiscrete vL :=
    { isRankOneDiscrete := inferInstance
      isAdicComplete := hcompletev }
  let target : CompleteDVF.{w, 0} L :=
    { ValueGroup := WithZero (Multiplicative ℤ)
      instValueGroup := inferInstance
      valuation := vL
      instCompleteDiscrete := inferInstance }
  refine ⟨target, ?_, e, trivial⟩
  intro z
  exact hmemStandard z

/-- The standard complete-DVF target supplied by the actual integral closure,
together with its valuation-extension property, integral-closure comparison,
and the fundamental ramification identity. -/
theorem exists_integralClosure_standard_fundamental_identity
    (base : CompleteDVF.{u, v} K)
    [Algebra.IsSeparable K L] :
    ∃ target : CompleteDVF.{w, 0} L,
      ∃ hExt : base.valuation.HasExtension target.valuation,
        letI : base.valuation.HasExtension target.valuation := hExt
        IsIntegralClosure target.valuationSubring
          base.valuationSubring L ∧
          ValuedExtension.degree base.toDVF target.toDVF =
            ValuedExtension.ramificationIndex base.toDVF target.toDVF *
              ValuedExtension.residueDegree base.toDVF target.toDVF := by
  obtain ⟨target, hmem, _hequiv⟩ :=
    exists_integralClosure_standard_completeDVF
      (K := K) (L := L) base
  have hExt : base.valuation.HasExtension target.valuation := by
    apply _root_.Valuation.HasExtension.ofComapInteger
    ext a
    change
      algebraMap K L a ∈ target.valuation.valuationSubring ↔
        a ∈ base.valuation.valuationSubring
    rw [hmem]
    exact algebraMap_mem_integralClosure_valuationSubring_iff
      (L := L) base.valuation a
  refine ⟨target, hExt, ?_⟩
  let : base.valuation.HasExtension target.valuation := hExt
  have hIntegralClosure :
      IsIntegralClosure target.valuationSubring
        base.valuationSubring L := by
    refine
      { algebraMap_injective := ?_
        isIntegral_iff := ?_ }
    · intro x y hxy
      exact Subtype.ext hxy
    · intro z
      constructor
      · intro hz
        have hzmem :
            z ∈ (integralClosure base.valuationSubring L).toSubring := hz
        exact ⟨⟨z, (hmem z).2 hzmem⟩, rfl⟩
      · rintro ⟨y, rfl⟩
        exact (hmem (y : L)).1 y.2
  refine ⟨hIntegralClosure, ?_⟩
  let :
      IsIntegralClosure target.valuationSubring
        base.valuationSubring L := hIntegralClosure
  let : IsScalarTower base.valuationSubring
      target.valuationSubring L := by
    apply IsScalarTower.of_algebraMap_eq
    intro x
    rfl
  exact isDefectless_of_isIntegralClosure
    (K := K) (L := L) base target

end ValuedExtension
end DiscreteValuationField

end

end ValuationTheory
end


