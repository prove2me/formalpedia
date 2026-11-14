-- Prove2me | Definitions.Def_OAIQ244Duke031
-- name    : OAIQ244Duke031
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-13T06:29:33.81121+00:00
-- url     : https://prove2.me/theorems/598b98ec-e3f0-4eb6-92d9-97a4dfc56853
-- title:
--   Definitions bundle OAIQ244Duke031 of the split of OpenAI, Equidistribution of Prime-Degree Torus Packets with Arbitrary Local Type
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.DukePrimeDegree.prime_degree_packet_measure_equidistribution_unconditional` and `OAI.DukePrimeDegree.prime_degree_packet_measures_tendsto_haar_unconditional`, carved from OpenAI's openai/math development (OpenAI, *Equidistribution of Prime-Degree Torus Packets with Arbitrary Local Type*, OpenAI Math Release, September 24, 2026, result family 15, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 137 declarations of OpenAI's Lean: 45 definitions, 6 instances and 86 theorems. The definitions and types are `KummerTheory.chosenFullSUnitKummerExtensionGaloisEquivSUnitQuotient`, `KummerTheory.fullSUnitKummerExtensionGaloisCoordinates`, `KummerTheory.kummerRadicalExtensionRestrictedTranspose`, `KummerTheory.kummerRadicalExtensionRestrictedTransposeMulEquiv`, `KummerTheory.multiplicativeFinsuppNthPowerQuotientEquivPiZMod`, `KummerTheory.restrictedKummerEvaluationLocus`, `KummerTheory.sUnitNthPowerQuotientCoordinates`, `KummerTheory.sUnitNthPowerQuotientEquivFullSUnitRadicalQuotient`, `KummerTheory.sUnitNthPowerQuotientToFullSUnitRadicalQuotient`, `KummerTheory.sUnitToFullSUnitKummerSubgroup`, `KummerTheory.sUnitToFullSUnitRadicalQuotient`, `LocalClassFieldTheory.additiveNormKernelEquivUnitsNormKer`, `LocalClassFieldTheory.additiveNormKernelToUnitsBoundaryQuotientHom`, `LocalClassFieldTheory.fixedSubgroupCompMulEquiv`, `LocalClassFieldTheory.herbrandH0CompMulEquiv`, `LocalClassFieldTheory.herbrandHMinusOneCompMulEquiv`, `LocalClassFieldTheory.herbrandHminusOneEquivUnitsBoundaryQuotient`, `LocalClassFieldTheory.herbrandHminusOneEquivUnitsTateHminusOne`, `LocalClassFieldTheory.herbrandHminusOneMulEquivUnitsBoundaryQuotient`, `LocalClassFieldTheory.normKernelCompMulEquiv`, `LocalClassFieldTheory.normKernelToUnitsBoundaryQuotientMonoidHom`, `LocalClassFieldTheory.towerAbsoluteGalois`, `LocalFieldTheory.arithmeticFrobeniusOfUnramifiedValuation`, `LocalFieldTheory.galoisGroupEquivZModOfUnramifiedValuationNormalized`, `LocalFieldTheory.integerUnitsModPrincipalUnitsResidueNormOfValuationExtension`, `LocalFieldTheory.maximalIdealPowSuccQuotMapOfUnramifiedValuation`, `RelativeIdeleGroup.Cohomology.instMulDistribMulActionAlgEquiv`, `SUnitGroup.basisFreeQuotient`, `SUnitGroup.decomposition`, `SUnitGroup.decompositionLinearEquiv`, `SUnitGroup.rootsOfUnityEquivTorsion`, `SUnitGroup.torsionProdFreeQuotientEquiv`, `SUnitGroup.torsionQuotientSection`, `finitePlaceScalarTensorUnitsAction`, `fullLogHyperplaneDiagonalBasis`, `fullLogHyperplaneDiagonalLattice`, `fullLogLatticeDistribMulAction`, `fullLogLatticeProdIntDistribMulAction`, `fullLogLatticeRealBasis`, `fullLogSpaceDistribMulAction` and 5 more.
--
--   **Sources.** They come from these modules of lean/OAI/NumberTheory, in whole or in part: `AlgebraicNumberTheory_Adele_FinitePlaceTensorBlock`, `AlgebraicNumberTheory_Adele_InfinitePlaceTensorBlock`, `AlgebraicNumberTheory_Idele_Cohomology_Herbrand`, `AlgebraicNumberTheory_Idele_SPlaces`, `AlgebraicNumberTheory_SUnit_GaloisAction`, `AlgebraicNumberTheory_SUnit_Herbrand`, `AlgebraicNumberTheory_SUnit_LogLattice`, `AlgebraicNumberTheory_SUnit_Rank`, `KummerTheory_Concrete_SUnitPreparation_FullSUnitKummerExtension`, `KummerTheory_Concrete_SUnitPreparation_SUnitPowerQuotient`, `Kummer_Concrete_InfiniteContinuity`, `Kummer_Concrete_KummerCorrespondenceFormula`, `Kummer_Concrete_RadicalExtension`, `LocalClassFieldTheory_ClassFormation_ArchimedeanNormQuotient`, `LocalClassFieldTheory_ClassFormation_CohomologyBridge`, `LocalClassFieldTheory_ClassFormation_Hilbert90`, `LocalClassFieldTheory_ClassFormation_IntegerUnitsHerbrand`, `LocalClassFieldTheory_ClassFormation_LocalizedCompletionCohomology_CompMulEquiv`, `LocalClassFieldTheory_Finite_LocalReciprocity_GeneralTowerNaturality`, `LocalClassFieldTheory_Finite_Unramified_Cohomology`, `LocalField_NonarchimedeanLocalField_FiniteUnramified`, `LocalField_NonarchimedeanLocalField_PrincipalUnitActions`, `LocalField_NonarchimedeanLocalField_PrincipalUnitQuotients`, `LocalField_NonarchimedeanLocalField_ResidueExtension`, `LocalField_NonarchimedeanLocalField_ResidueGalois`, `LocalField_NonarchimedeanLocalField_UnramifiedFrobenius`.
--
--   **Imports.** It imports the bundles `OAIQ244Duke015`, `OAIQ244Duke016`, `OAIQ244Duke017`, `OAIQ244Duke018`, `OAIQ244Duke019`, `OAIQ244Duke020` and `OAIQ244Duke021` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ244Duke040`, `OAIQ244Duke042` and `OAIQ244Duke044`.
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
import Mathlib.Algebra.Group.Equiv.TypeTags
import Mathlib.Algebra.Group.Hom.Basic
import Mathlib.Algebra.Group.Int.TypeTags
import Mathlib.Algebra.Group.Pi.Basic
import Mathlib.Algebra.Group.Pi.Units
import Mathlib.Algebra.Group.Subgroup.Basic
import Mathlib.Algebra.Group.Subgroup.Ker
import Mathlib.Algebra.Group.Subgroup.Map
import Mathlib.Algebra.Group.TransferInstance
import Mathlib.Algebra.Group.Units.Equiv
import Mathlib.Algebra.Group.Units.Hom
import Mathlib.Algebra.Module.Equiv.Basic
import Mathlib.Algebra.Module.LinearMap.Polynomial
import Mathlib.Algebra.Module.PID
import Mathlib.Algebra.Module.Shrink
import Mathlib.Algebra.Module.ZLattice.Basic
import Mathlib.Algebra.Module.ZMod
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
import Mathlib.Data.Finsupp.Fintype
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
import Mathlib.FieldTheory.IntermediateField.Basic
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
import Mathlib.GroupTheory.Sylow
import Mathlib.GroupTheory.Transfer
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
import Mathlib.RingTheory.ClassGroup.Basic
import Mathlib.RingTheory.Complex
import Mathlib.RingTheory.DedekindDomain.Factorization
import Mathlib.RingTheory.DedekindDomain.IntegralClosure
import Mathlib.RingTheory.DedekindDomain.SInteger
import Mathlib.RingTheory.DiscreteValuationRing.Basic
import Mathlib.RingTheory.DiscreteValuationRing.TFAE
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
import Mathlib.RingTheory.LocalRing.Module
import Mathlib.RingTheory.LocalRing.ResidueField.Basic
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
import Definitions.Def_OAIQ244Duke015
import Definitions.Def_OAIQ244Duke016
import Definitions.Def_OAIQ244Duke017
import Definitions.Def_OAIQ244Duke018
import Definitions.Def_OAIQ244Duke019
import Definitions.Def_OAIQ244Duke020
import Definitions.Def_OAIQ244Duke021

section
-- module Solutions.OAIQ244_DUKE.AlgebraicNumberTheory_Idele_Cohomology_Herbrand
attribute [-instance] _root_.ClassFormation.DegreeData.GaloisSubextension.extensionSubgroup_normalInstance _root_.ClassFormation.FiniteCyclicSubextension.instNormalSubtypeMemSubgroupFieldExtensionSubgroupField _root_.ClassFormation.FiniteGaloisSubextension.extensionSubgroup_normalInstance _root_.ClassFormation.FiniteGaloisSubextension.extensionSubgroup_over_intermediate_normalInstance _root_.ClassFormation.FiniteGaloisSubextension.intermediateField_normalInstance _root_.ClassFormation.FiniteUnramifiedCyclicExtension.instNormalSubtypeMemSubgroupFieldExtensionSubgroupField _root_.ClassFormation.conjugateExtension_normal _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalClassFieldTheory.extensionSubgroupBase_normal _root_.LocalClassFieldTheory.finiteGaloisExtensionSubgroupOfEmbedding_normal _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.PrimeDegreePackets.diagonalLogAction _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.RamificationTheory.HilbertRamification.ValuationSubring.inertiaGroup_normal _root_.RamificationTheory.HilbertRamification.ValuationSubring.ramificationGroupInInertiaAut_normal _root_.RamificationTheory.HilbertRamification.ValuationSubring.selectedResidueField.instAlgebra _root_.ValuationTheory.DiscreteValuationField.DVF.maximalIdealPowSuccQuotModule _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.CyclicCohomology.binaryCoefficientFamilyCommGroup _root_.CyclicCohomology.instMulDistribMulActionBinaryCoefficientFamily _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen _root_.relativeAdeleRingIntermediateAlgebra _root_.relativeAdeleRingTopIntermediateAlgebra
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

local instance instMulDistribMulActionAlgEquiv :
    MulDistribMulAction (L ≃ₐ[K] L)
      (RelativeIdeleGroup K L) :=
  relativeIdeleMulDistribMulAction K L

attribute [local instance] RelativeIdeleGroup.Cohomology.instMulDistribMulActionAlgEquivClassGroup
local instance instMulDistribMulActionAlgEquivSubtypeMemSubgroupPrincipalSubgroup_re9b3c1_1 :
    MulDistribMulAction (L ≃ₐ[K] L)
      (RelativeIdeleGroup.principalSubgroup K L) :=
  principalIdeleMulDistribMulAction K L
omit [NumberField L] [FiniteDimensional K L] [IsGalois K L] in
/-- Equivariance of the actual quotient map `I_L → C_L`. -/
theorem ideleClassQuotientMap_equivariant :
    ∀ (σ : L ≃ₐ[K] L)
      (a : RelativeIdeleGroup K L),
      QuotientGroup.mk'
          (RelativeIdeleGroup.principalSubgroup K L)
          (σ • a) =
        σ • QuotientGroup.mk'
          (RelativeIdeleGroup.principalSubgroup K L) a :=
  stableSubgroup_quotientMap_equivariant
    (RelativeIdeleGroup.principalSubgroup K L)
    (principalRelativeIdele_smul_mem K L)

end Actions

end Cohomology
end RelativeIdeleGroup
end
end

section
-- module Solutions.OAIQ244_DUKE.LocalField_NonarchimedeanLocalField_PrincipalUnitQuotients
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen
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

/-- Variant tailored to finite-depth approximation statements: if a unit lies
in `U^(n+d)` for every `d`, then it is `1`. -/
theorem principalUnits_eq_one_of_mem_add_all
    (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] (n : Nat) (u : 𝒪[K]ˣ)
    (hu : ∀ d : Nat, u ∈ principalUnits K (n + d)) :
    u = 1 := by
  refine principalUnits_eq_one_of_mem_all K u ?_
  intro m
  by_cases hm : m ≤ n
  · exact principalUnits_antitone K hm (hu 0)
  · have hnm : n ≤ m := Nat.le_of_not_ge hm
    obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hnm
    exact hu d

/-! ### Maximal-ideal powers as local neighborhoods -/

/-! ### Finite correction products for complete lifting -/

end
end LocalFieldTheory
end

section
-- module Solutions.OAIQ244_DUKE.LocalField_NonarchimedeanLocalField_PrincipalUnitActions
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen
attribute [-simp] _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.IsDiscreteValuationRing.addVal_ringEquiv _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.LocalFieldTheory.maximalIdealPowSuccQuotMulUniformizerPowMap_apply _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.LocalFieldTheory.principalUnitsSuccQuotAddEquivResidueOfIrreducible_symm_apply _root_.LocalFieldTheory.residueAddEquivMaximalIdealPowSuccQuotOfIrreducible_residue _root_.LocalFieldTheory.residueField_algebraMap_residue _root_.OAI.PrimeDegreePackets.ThetaConstruction.schwartzCM_apply _root_.infinitePlace_mult_smul
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI
/-!
# Actions on principal-unit quotients

Transports valuation-ring automorphisms to maximal-ideal powers, principal
units, and their successive quotients, together with the resulting actions.
-/

set_option autoImplicit false

namespace LocalFieldTheory

noncomputable section

universe u

open scoped ValuativeRel

/-- The multiplicative encoding of a successive ideal-quotient equivalence applies the original
additive transport map. -/
@[simp]
theorem maximalIdealPowSuccQuotMultiplicativeMapEquivOfIntegerRingEquiv_apply
    (K : Type u) [Field K] [ValuativeRel K]
    (n : Nat) (e : 𝒪[K] ≃+* 𝒪[K]) (x : MaximalIdealPowSuccQuot K n) :
    maximalIdealPowSuccQuotMultiplicativeMapEquivOfIntegerRingEquiv K n e
        (Multiplicative.ofAdd x) =
      Multiplicative.ofAdd (maximalIdealPowSuccQuotMapEquivOfIntegerRingEquiv K n e x) :=
  rfl

end
end LocalFieldTheory
end

section
-- module Solutions.OAIQ244_DUKE.LocalField_NonarchimedeanLocalField_ResidueExtension
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.LubinTate.Valuations.exponentialValuationSubringIsLocalRing _root_.OAI.PrimeDegreePackets.boundedRealFields_finite _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_finite_residue _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionFixedSubring.instIsLocalRing _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionResidueField.instField _root_.RamificationTheory.HilbertRamification.ValuationSubring.selectedResidueField.instAlgebra _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.maximalIdealPowSuccQuotModule _root_.ValuationTheory.DiscreteValuationField.DVF.residueField.field _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.isDomain _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.isLocalRing _root_.CyclicCohomology.binaryCoefficientFamilyCommGroup _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen _root_.relativeAdeleRingIntermediateAlgebra _root_.relativeAdeleRingTopIntermediateAlgebra
attribute [-simp] _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.IsDiscreteValuationRing.addVal_ringEquiv _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.OAI.PrimeDegreePackets.ThetaConstruction.schwartzCM_apply _root_.infinitePlace_mult_smul
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI
/-!
# Residue extensions

Constructs the maps induced on valuation rings, residue fields, and residue
units by a valued extension, with degree, trace, norm, and Frobenius results.
-/

set_option autoImplicit false

namespace LocalFieldTheory

noncomputable section

universe u

open scoped ValuativeRel

/-- The residue-field norm transported to the integer-unit quotients
`𝒪[L]ˣ/U_L¹ → 𝒪[K]ˣ/U_K¹`.

This is not the local field norm on integer units; it is the quotient-level
residue norm model used before proving compatibility with `normIntegerUnits`. -/
def integerUnitsModPrincipalUnitsResidueNormOfValuationExtension (K L : Type u)
    [Field K] [ValuativeRel K] [Field L] [ValuativeRel L] [Algebra K L]
    [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)] :
    IntegerUnitsModPrincipalUnits L →* IntegerUnitsModPrincipalUnits K :=
  (integerUnitsModPrincipalUnitsEquivResidueUnits K).symm.toMonoidHom.comp
    ((Units.map (Algebra.norm 𝓀[K] (S := 𝓀[L]))).comp
      (integerUnitsModPrincipalUnitsEquivResidueUnits L).toMonoidHom)

/-- The residue norm on classes modulo first principal units agrees with the finite residue-field
norm. -/
theorem integerUnitsModPrincipalUnitsResidueNorm_residue (K L : Type u)
    [Field K] [ValuativeRel K] [Field L] [ValuativeRel L] [Algebra K L]
    [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]
    (x : IntegerUnitsModPrincipalUnits L) :
    integerUnitsModPrincipalUnitsEquivResidueUnits K
        (integerUnitsModPrincipalUnitsResidueNormOfValuationExtension K L x) =
      Units.map (Algebra.norm 𝓀[K] (S := 𝓀[L]))
        (integerUnitsModPrincipalUnitsEquivResidueUnits L x) := by
  change
    integerUnitsModPrincipalUnitsEquivResidueUnits K
        ((integerUnitsModPrincipalUnitsEquivResidueUnits K).symm
          (Units.map (Algebra.norm 𝓀[K] (S := 𝓀[L]))
            (integerUnitsModPrincipalUnitsEquivResidueUnits L x))) =
      Units.map (Algebra.norm 𝓀[K] (S := 𝓀[L]))
        (integerUnitsModPrincipalUnitsEquivResidueUnits L x)
  exact (integerUnitsModPrincipalUnitsEquivResidueUnits K).apply_symm_apply _

/-- The finite-field residue norm, after base extension to `𝓀[L]`, is the
product over all residue-field automorphisms. -/
theorem residueUnitsMap_residueField_norm_eq_prod_algEquiv (K L : Type u)
    [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
    [Algebra K L]
    [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]
    (u : 𝓀[L]ˣ) :
    residueUnitsMapOfValuationExtension K L
        (Units.map (Algebra.norm 𝓀[K] (S := 𝓀[L])) u) =
      Finset.univ.prod (fun τ : 𝓀[L] ≃ₐ[𝓀[K]] 𝓀[L] =>
        Units.mapEquiv τ.toMulEquiv u) := by
  ext
  change algebraMap 𝓀[K] 𝓀[L] (Algebra.norm 𝓀[K] (u : 𝓀[L])) =
    ↑(Finset.univ.prod (fun τ : 𝓀[L] ≃ₐ[𝓀[K]] 𝓀[L] =>
      Units.mapEquiv τ.toMulEquiv u))
  rw [Algebra.norm_eq_prod_automorphisms]
  simp

/-- Quotient-level form of
`residueUnitsMap_residueField_norm_eq_prod_algEquiv`. -/
theorem integerUnitsModPrincipalUnitsResidueNorm_base_extend_eq_prod_algEquiv
    (K L : Type u)
    [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
    [Algebra K L]
    [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]
    (x : IntegerUnitsModPrincipalUnits L) :
    residueUnitsMapOfValuationExtension K L
        (integerUnitsModPrincipalUnitsEquivResidueUnits K
          (integerUnitsModPrincipalUnitsResidueNormOfValuationExtension K L x)) =
      Finset.univ.prod (fun τ : 𝓀[L] ≃ₐ[𝓀[K]] 𝓀[L] =>
        Units.mapEquiv τ.toMulEquiv (integerUnitsModPrincipalUnitsEquivResidueUnits L x)) := by
  rw [integerUnitsModPrincipalUnitsResidueNorm_residue]
  exact residueUnitsMap_residueField_norm_eq_prod_algEquiv K L
    (integerUnitsModPrincipalUnitsEquivResidueUnits L x)

/-- The residue norm on integer units modulo first principal units is surjective. -/
theorem integerUnitsModPrincipalUnitsResidueNorm_surjective_of_valuationExtension
    (K L : Type u)
    [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
    [Algebra K L]
    [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)] :
    Function.Surjective
      (integerUnitsModPrincipalUnitsResidueNormOfValuationExtension K L) := by
  intro y
  obtain ⟨v, hv⟩ := residueField_units_norm_surjective_of_valuationExtension K L
    (integerUnitsModPrincipalUnitsEquivResidueUnits K y)
  refine ⟨(integerUnitsModPrincipalUnitsEquivResidueUnits L).symm v, ?_⟩
  apply (integerUnitsModPrincipalUnitsEquivResidueUnits K).injective
  rw [integerUnitsModPrincipalUnitsResidueNorm_residue]
  exact (congrArg (Units.map (Algebra.norm 𝓀[K] (S := 𝓀[L])))
    ((integerUnitsModPrincipalUnitsEquivResidueUnits L).apply_symm_apply v)).trans hv

end
end LocalFieldTheory
end

section
-- module Solutions.OAIQ244_DUKE.AlgebraicNumberTheory_Idele_SPlaces
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionResidueField.instField _root_.RamificationTheory.HilbertRamification.ValuationSubring.selectedResidueField.instAlgebra _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.residueField.field _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.relativeAdeleRingIntermediateAlgebra _root_.relativeAdeleRingTopIntermediateAlgebra
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

/-!
# Ideles and units with finite support

This file formalizes finite-support objects for ideles and units. Since every
archimedean place is always included, a finite set
`S` below records only its finite places.
-/

open scoped NumberField RestrictedProduct
open NumberField IsDedekindDomain

noncomputable section


variable {K : Type*} [Field K] [NumberField K]

namespace IdeleGroup

/-- Every idele lies in `I_K^S` for some finite set `S`. -/
theorem exists_finset_supportedAt (a : IdeleGroup K) :
    ∃ S : Finset (HeightOneSpectrum (𝓞 K)),
      a ∈ supportedAt (K := K) (S : Set _) :=
  FiniteIdeleGroup.exists_finset_supportedAt a.2

end IdeleGroup
end
end

section
-- module Solutions.OAIQ244_DUKE.LocalClassFieldTheory_ClassFormation_CohomologyBridge
attribute [-instance] _root_.ClassFormation.DegreeData.GaloisSubextension.extensionSubgroup_normalInstance _root_.ClassFormation.FiniteCyclicSubextension.instNormalSubtypeMemSubgroupFieldExtensionSubgroupField _root_.ClassFormation.FiniteGaloisSubextension.extensionSubgroup_normalInstance _root_.ClassFormation.FiniteGaloisSubextension.extensionSubgroup_over_intermediate_normalInstance _root_.ClassFormation.FiniteGaloisSubextension.intermediateField_normalInstance _root_.ClassFormation.FiniteUnramifiedCyclicExtension.instNormalSubtypeMemSubgroupFieldExtensionSubgroupField _root_.ClassFormation.conjugateExtension_normal _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.HilbertRamification.Dedekind.inertiaSubgroupOfDecomposition_normal _root_.KummerTheory.DiscreteNthRootsSubgroup.instCommGroupSubtypeUnitsMemSubgroup _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalClassFieldTheory.extensionSubgroupBase_normal _root_.LocalClassFieldTheory.finiteGaloisExtensionSubgroupOfEmbedding_normal _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.LubinTate.compatibleGroupFamiliesCommGroup _root_.LubinTate.compatibleGroupFamiliesGroup _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.RamificationTheory.HilbertRamification.ValuationSubring.inertiaGroup_normal _root_.RamificationTheory.HilbertRamification.ValuationSubring.ramificationGroupInInertiaAut_normal _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.maximalIdealPowSuccQuotModule _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.CyclicCohomology.binaryCoefficientFamilyCommGroup _root_.CyclicCohomology.instMulDistribMulActionBinaryCoefficientFamily _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen
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

/-- Multiplicative norm-one units and the kernel of the norm on the actual
unit representation are the same additive group. -/
def additiveNormKernelEquivUnitsNormKer [Fintype (Gal(L / K))] :
    Additive (normKernelSubgroup (Gal(L / K)) Lˣ) ≃+
      LinearMap.ker (unitsNormLinearMap K L) where
  toFun x := ⟨Additive.ofMul
      ((Additive.toMul x : normKernelSubgroup (Gal(L / K)) Lˣ) : Lˣ), by
    apply Additive.toMul.injective
    change Additive.toMul
      (unitsNormLinearMap K L (Additive.ofMul
        ((Additive.toMul x : normKernelSubgroup (Gal(L / K)) Lˣ) : Lˣ))) = 1
    rw [unitsNormLinearMap_toMul_eq_tateNorm K L
      ((Additive.toMul x : normKernelSubgroup (Gal(L / K)) Lˣ) : Lˣ)]
    exact (Additive.toMul x).property⟩
  invFun x := Additive.ofMul ⟨Additive.toMul (x : Additive Lˣ), by
    change tateNorm (Gal(L / K)) Lˣ (Additive.toMul (x : Additive Lˣ)) = 1
    rw [← unitsNormLinearMap_toMul_eq_tateNorm K L
      (Additive.toMul (x : Additive Lˣ))]
    have hx := congrArg Additive.toMul x.property
    exact hx⟩
  left_inv x := rfl
  right_inv x := rfl
  map_add' x y := rfl

/-- Additive quotient map from the multiplicative norm kernel to the
standard boundary presentation of degree-minus-one Tate cohomology. -/
def additiveNormKernelToUnitsBoundaryQuotientHom
    [Fintype (Gal(L / K))] (g : Gal(L / K)) :
    Additive (normKernelSubgroup (Gal(L / K)) Lˣ) →+
      LinearMap.ker (unitsNormLinearMap K L) ⧸
        LinearMap.range (unitsRhoSubToNormKerLinearMap K L g) :=
  additiveEquivToQuotientHom
    (additiveNormKernelEquivUnitsNormKer K L)
    (LinearMap.range (unitsRhoSubToNormKerLinearMap K L g))

/-- Multiplicative form of the standard boundary quotient map. -/
def normKernelToUnitsBoundaryQuotientMonoidHom
    [Fintype (Gal(L / K))] (g : Gal(L / K)) :
    normKernelSubgroup (Gal(L / K)) Lˣ →*
      Multiplicative
        (LinearMap.ker (unitsNormLinearMap K L) ⧸
          LinearMap.range (unitsRhoSubToNormKerLinearMap K L g)) :=
  additiveHomToMultiplicativeHom
    (additiveNormKernelToUnitsBoundaryQuotientHom K L g)

/-- The kernel of the standard boundary quotient map is the augmentation
subgroup generated by `ρ(g)-1`. -/
theorem normKernelToUnitsBoundaryQuotientMonoidHom_ker
    [Fintype (Gal(L / K))] (g : Gal(L / K)) :
    kernelOfAdditiveQuotientHom
        (LinearMap.range (unitsRhoSubToNormKerLinearMap K L g))
        (normKernelToUnitsBoundaryQuotientMonoidHom K L g) =
      (augmentationSubgroup (Gal(L / K)) Lˣ g).subgroupOf
        (normKernelSubgroup (Gal(L / K)) Lˣ) := by
  ext x
  constructor
  · intro hx
    have hx0 := congrArg Multiplicative.toAdd hx
    change
      (LinearMap.range (unitsRhoSubToNormKerLinearMap K L g)).mkQ
          (additiveNormKernelEquivUnitsNormKer K L (Additive.ofMul x)) =
        0 at hx0
    have hxmem :
        additiveNormKernelEquivUnitsNormKer K L (Additive.ofMul x) ∈
          LinearMap.range (unitsRhoSubToNormKerLinearMap K L g) :=
      (Submodule.Quotient.mk_eq_zero
        (LinearMap.range (unitsRhoSubToNormKerLinearMap K L g))).1 hx0
    rcases hxmem with ⟨y, hy⟩
    change (x : Lˣ) ∈ augmentationSubgroup (Gal(L / K)) Lˣ g
    refine ⟨Additive.toMul y, ?_⟩
    have hy' := congrArg
      (fun z : LinearMap.ker (unitsNormLinearMap K L) =>
        Additive.toMul (z : Additive Lˣ)) hy
    simp only [unitsRhoSubToNormKerLinearMap,
      additiveNormKernelEquivUnitsNormKer] at hy'
    change
      (Additive.toMul ((Rep.ofAlgebraAutOnUnits K L).ρ g y) : Lˣ) *
        (Additive.toMul y)⁻¹ = (x : Lˣ) at hy'
    rw [sigmaMinusOneHom_apply,
      ← unitsRhoSub_toMul_eq_sigmaMinusOne K L g (Additive.toMul y)]
    exact hy'
  · intro hx
    change (x : Lˣ) ∈ augmentationSubgroup (Gal(L / K)) Lˣ g at hx
    rcases hx with ⟨y, hy⟩
    apply Multiplicative.toAdd.injective
    change
      (LinearMap.range (unitsRhoSubToNormKerLinearMap K L g)).mkQ
          (additiveNormKernelEquivUnitsNormKer K L (Additive.ofMul x)) =
        0
    apply (Submodule.Quotient.mk_eq_zero
      (LinearMap.range (unitsRhoSubToNormKerLinearMap K L g))).2
    refine ⟨Additive.ofMul y, ?_⟩
    apply Subtype.ext
    apply Additive.toMul.injective
    simp only [unitsRhoSubToNormKerLinearMap,
      additiveNormKernelEquivUnitsNormKer]
    change
      (Additive.toMul ((Rep.ofAlgebraAutOnUnits K L).ρ g (Additive.ofMul y)) : Lˣ) * y⁻¹ =
        (x : Lˣ)
    rw [unitsRhoSub_toMul_eq_sigmaMinusOne K L g y]
    exact hy

/-- Every class of the standard boundary quotient has a representative in
the multiplicative norm kernel. -/
theorem normKernelToUnitsBoundaryQuotientMonoidHom_surjective
    [Fintype (Gal(L / K))] (g : Gal(L / K)) :
    Function.Surjective
      (normKernelToUnitsBoundaryQuotientMonoidHom K L g) := by
  intro q
  rcases Submodule.mkQ_surjective
      (LinearMap.range (unitsRhoSubToNormKerLinearMap K L g))
      (Multiplicative.toAdd q) with ⟨z, hz⟩
  let x : normKernelSubgroup (Gal(L / K)) Lˣ :=
    Additive.toMul ((additiveNormKernelEquivUnitsNormKer K L).symm z)
  refine ⟨x, ?_⟩
  apply Multiplicative.toAdd.injective
  change
    (LinearMap.range (unitsRhoSubToNormKerLinearMap K L g)).mkQ
        (additiveNormKernelEquivUnitsNormKer K L (Additive.ofMul x)) =
        Multiplicative.toAdd q
  calc
    _ = (LinearMap.range (unitsRhoSubToNormKerLinearMap K L g)).mkQ z := by
      apply congrArg
        (LinearMap.range (unitsRhoSubToNormKerLinearMap K L g)).mkQ
      change additiveNormKernelEquivUnitsNormKer K L
        ((additiveNormKernelEquivUnitsNormKer K L).symm z) = z
      exact (additiveNormKernelEquivUnitsNormKer K L).apply_symm_apply z
    _ = Multiplicative.toAdd q := hz

/-- The multiplicative Herbrand quotient is the standard additive boundary
quotient used by mathlib's finite-cyclic Tate complex. -/
def herbrandHminusOneMulEquivUnitsBoundaryQuotient
    [Fintype (Gal(L / K))] (g : Gal(L / K)) :
    HerbrandHMinusOne (Gal(L / K)) Lˣ g ≃*
      Multiplicative
        (LinearMap.ker (unitsNormLinearMap K L) ⧸
          LinearMap.range (unitsRhoSubToNormKerLinearMap K L g)) :=
  (HerbrandHMinusOne.equiv (G := Gal(L / K)) (A := Lˣ) g).trans
    (quotientMulEquivOfSurjectiveAdditiveQuotient
      (LinearMap.range (unitsRhoSubToNormKerLinearMap K L g))
      ((augmentationSubgroup (Gal(L / K)) Lˣ g).subgroupOf
        (normKernelSubgroup (Gal(L / K)) Lˣ))
      (normKernelToUnitsBoundaryQuotientMonoidHom K L g)
      (normKernelToUnitsBoundaryQuotientMonoidHom_ker K L g)
      (normKernelToUnitsBoundaryQuotientMonoidHom_surjective K L g))

/-- Type-level comparison with the standard boundary quotient. -/
def herbrandHminusOneEquivUnitsBoundaryQuotient
    [Fintype (Gal(L / K))] (g : Gal(L / K)) :
    HerbrandHMinusOne (Gal(L / K)) Lˣ g ≃
      LinearMap.ker (unitsNormLinearMap K L) ⧸
        LinearMap.range (unitsRhoSubToNormKerLinearMap K L g) :=
  mulEquivMultiplicativeToEquiv
    (herbrandHminusOneMulEquivUnitsBoundaryQuotient K L g)

/-- Genuine comparison of the multiplicative `H⁻¹` quotient
for field units with Mathlib's actual Tate `H⁻¹` object. -/
noncomputable def herbrandHminusOneEquivUnitsTateHminusOne
    [FiniteDimensional K L] (g : Gal(L / K))
    (hg : ∀ x : Gal(L / K), x ∈ Subgroup.zpowers g) :
    HerbrandHMinusOne (Gal(L / K)) Lˣ g ≃
      tateCohomology (Rep.ofAlgebraAutOnUnits K L) (-1) :=
  (herbrandHminusOneEquivUnitsBoundaryQuotient K L g).trans
    (unitsTateHminusOneIsoBoundaryQuotient K L g hg).symm.toLinearEquiv.toEquiv

end
end LocalClassFieldTheory
end

section
-- module Solutions.OAIQ244_DUKE.LocalClassFieldTheory_ClassFormation_Hilbert90
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.PrimeDegreePackets.instNonemptyLeafTestSpace _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.maximalIdealPowSuccQuotModule _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false
/-!
Provides the public declarations in the
`LocalClassFieldTheory.ClassFormation.Hilbert90` Lean module.
-/

namespace LocalClassFieldTheory

open CyclicCohomology

noncomputable section

/-- The `i = -1` half of the local class-field-axiom theorem on the actual field-unit
representation.  This is Hilbert 90 transported through the cyclic
`H¹ ≃ H⁻¹` comparison. -/
theorem unitsTateHminusOne_card_eq_one
    (K L : Type) [Field K] [Field L] [Algebra K L] [FiniteDimensional K L]
    (g : Gal(L / K)) (hg : ∀ σ : Gal(L / K), σ ∈ Subgroup.zpowers g) :
    Nat.card (tateCohomology (Rep.ofAlgebraAutOnUnits K L) (-1)) = 1 := by
  calc
    Nat.card (tateCohomology (Rep.ofAlgebraAutOnUnits K L) (-1)) =
        Nat.card (groupCohomology.H1 (Rep.ofAlgebraAutOnUnits K L)) :=
      Nat.card_congr
        (unitsH1IsoTateHminusOne K L g hg).symm.toLinearEquiv.toEquiv
    _ = 1 := Nat.card_unique

end
end LocalClassFieldTheory
end

section
-- module Solutions.OAIQ244_DUKE.LocalClassFieldTheory_ClassFormation_IntegerUnitsHerbrand
attribute [-instance] _root_.ClassFormation.DegreeData.GaloisSubextension.extensionSubgroup_normalInstance _root_.ClassFormation.FiniteCyclicSubextension.instNormalSubtypeMemSubgroupFieldExtensionSubgroupField _root_.ClassFormation.FiniteGaloisSubextension.extensionSubgroup_normalInstance _root_.ClassFormation.FiniteGaloisSubextension.extensionSubgroup_over_intermediate_normalInstance _root_.ClassFormation.FiniteGaloisSubextension.intermediateField_normalInstance _root_.ClassFormation.FiniteUnramifiedCyclicExtension.instNormalSubtypeMemSubgroupFieldExtensionSubgroupField _root_.ClassFormation.conjugateExtension_normal _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.DiscreteNthRootsSubgroup.instCommGroupSubtypeUnitsMemSubgroup _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalClassFieldTheory.extensionSubgroupBase_normal _root_.LocalClassFieldTheory.finiteGaloisExtensionSubgroupOfEmbedding_normal _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.LubinTate.compatibleGroupFamiliesCommGroup _root_.LubinTate.compatibleGroupFamiliesGroup _root_.OAI.PrimeDegreePackets.boundedRealFields_finite _root_.OAI.PrimeDegreePackets.diagonalLogAction _root_.OAI.PrimeDegreePackets.instNonemptyLeafTestSpace _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.RamificationTheory.HilbertRamification.ValuationSubring.inertiaGroup_normal _root_.RamificationTheory.HilbertRamification.ValuationSubring.ramificationGroupInInertiaAut_normal _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.RelativeIdeleGroup.relativeIdeleMulAction _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.CyclicCohomology.binaryCoefficientFamilyCommGroup _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen
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
# The Herbrand quotient of the integer-unit group

This file proves the final integer-unit Herbrand-quotient calculation.  For a
sufficiently deep normal-basis neighbourhood
`V = 1 + π_K^n M`, the exact sequence

`1 → V → 𝒪_Lˣ → 𝒪_Lˣ / V → 1`

has the actual `Gal(L / K)` actions.  Vanishing of the two low-degree
Herbrand groups of `V`, together with finiteness of the quotient, gives
`h(G, 𝒪_Lˣ) = 1` by the Herbrand-quotient multiplicativity theorem.
-/

noncomputable section

open scoped ValuativeRel
open CyclicCohomology.ProfiniteCohomology.Herbrand
open IsNonarchimedeanLocalField

variable (K L : Type) [Field K] [Field L] [Algebra K L]
  [FiniteDimensional K L] [IsGalois K L]
  [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [ValuativeRel L]
  [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]
  [IsIntegralClosure 𝒪[L] 𝒪[K] L]

/-- Integer-unit Herbrand calculation at one chosen normal-basis
level.  The only low-degree cohomology input is the proved vanishing of
`H⁰(G,V)` and `H⁻¹(G,V)`; finiteness of `𝒪_Lˣ/V` is the other honest
input. -/
theorem integerUnits_herbrandQuotient_eq_one_of_chosenNormalBasis
    (n : Nat) (V : Subgroup 𝒪[L]ˣ)
    (hV : (V : Set 𝒪[L]ˣ) = chosenNormalBasisPrincipalUnitSet K L n)
    (hfinite : Finite (𝒪[L]ˣ ⧸ V))
    (g : Gal(L / K))
    (hg : ∀ sigma : Gal(L / K), sigma ∈ Subgroup.zpowers g)
    (hH0 :
      letI := chosenNormalBasisPrincipalUnitSubgroupMulDistribMulAction K L n V hV
      Subsingleton (HerbrandH0 (Gal(L / K)) V))
    (hHminusOne :
      letI := chosenNormalBasisPrincipalUnitSubgroupMulDistribMulAction K L n V hV
      Subsingleton (HerbrandHMinusOne (Gal(L / K)) V g)) :
    letI := chosenNormalBasisPrincipalUnitSubgroupMulDistribMulAction K L n V hV
    letI := galoisGroupIntegerUnitsMulDistribMulActionOfIsIntegralClosure K L
    letI := chosenNormalBasisIntegerUnitsQuotMulDistribMulAction K L n V hV
    ∃ hU : HerbrandQuotientDefined (Gal(L / K)) 𝒪[L]ˣ g,
      @herbrandQuotient (Gal(L / K)) 𝒪[L]ˣ _ _ _
        (galoisGroupIntegerUnitsMulDistribMulActionOfIsIntegralClosure K L)
        g hU.1 hU.2 = 1 := by
  let := chosenNormalBasisPrincipalUnitSubgroupMulDistribMulAction K L n V hV
  let := galoisGroupIntegerUnitsMulDistribMulActionOfIsIntegralClosure K L
  let := chosenNormalBasisIntegerUnitsQuotMulDistribMulAction K L n V hV
  let : Finite (𝒪[L]ˣ ⧸ V) := hfinite
  let : Subsingleton (HerbrandH0 (Gal(L / K)) V) := hH0
  let : Subsingleton (HerbrandHMinusOne (Gal(L / K)) V g) := hHminusOne
  let hVdefined : HerbrandQuotientDefined (Gal(L / K)) V g :=
    ⟨inferInstance, inferInstance⟩
  let hQdefined : HerbrandQuotientDefined (Gal(L / K)) (𝒪[L]ˣ ⧸ V) g :=
    ⟨inferInstance, inferInstance⟩
  let hseq := chosenNormalBasisIntegerUnitsHerbrand_shortExact K L n V hV
  have hsurj : ∀ c : 𝒪[L]ˣ ⧸ V, ∃ b : 𝒪[L]ˣ,
      chosenNormalBasisIntegerUnitsQuotientMap (L := L) V b = c := by
    intro c
    exact hseq.2.2.2.2 c
  let hU := herbrandQuotientDefined_middle_of_left_right
    (G := Gal(L / K)) (A := V) (B := 𝒪[L]ˣ) (C := 𝒪[L]ˣ ⧸ V)
    (chosenNormalBasisPrincipalUnitSubgroupInclusion (L := L) V)
    (chosenNormalBasisIntegerUnitsQuotientMap (L := L) V)
    hseq.1 hseq.2.1 hseq.2.2.1 hseq.2.2.2.1 hsurj
    g hg hVdefined hQdefined
  refine ⟨hU, ?_⟩
  let : Finite (HerbrandH0 (Gal(L / K)) 𝒪[L]ˣ) := hU.1
  let : Finite (HerbrandHMinusOne (Gal(L / K)) 𝒪[L]ˣ g) := hU.2
  have hVone : herbrandQuotient (G := Gal(L / K)) (A := V) g = 1 := by
    exact herbrandQuotient_eq_one_of_card_eq
      (G := Gal(L / K)) (A := V) g
      (by simp only [Nat.card_unique])
  have hQone :
      herbrandQuotient (G := Gal(L / K)) (A := 𝒪[L]ˣ ⧸ V) g = 1 := by
    exact herbrandQuotient_eq_one_of_finite_module
      (G := Gal(L / K)) (A := 𝒪[L]ˣ ⧸ V) g hg
  have hmul : herbrandQuotient (G := Gal(L / K)) (A := 𝒪[L]ˣ) g =
      herbrandQuotient (G := Gal(L / K)) (A := V) g *
        herbrandQuotient (G := Gal(L / K)) (A := 𝒪[L]ˣ ⧸ V) g :=
    herbrandQuotient_multiplicative_of_shortExact
      (G := Gal(L / K)) (A := V) (B := 𝒪[L]ˣ) (C := 𝒪[L]ˣ ⧸ V)
      (chosenNormalBasisPrincipalUnitSubgroupInclusion (L := L) V)
      (chosenNormalBasisIntegerUnitsQuotientMap (L := L) V)
      hseq.1 hseq.2.1 hseq.2.2.1 hseq.2.2.2.1 hsurj g hg
  exact hmul.trans (by rw [hVone, hQone, one_mul])

end
end LocalClassFieldTheory
end

section
-- module Solutions.OAIQ244_DUKE.LocalClassFieldTheory_ClassFormation_LocalizedCompletionCohomology_CompMulEquiv
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.DiscreteNthRootsSubgroup.instCommGroupSubtypeUnitsMemSubgroup _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.LubinTate.compatibleGroupFamiliesCommGroup _root_.LubinTate.compatibleGroupFamiliesGroup _root_.OAI.PrimeDegreePackets.diagonalLogAction _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.RelativeIdeleGroup.relativeIdeleMulAction _root_.CyclicCohomology.binaryCoefficientFamilyCommGroup _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen
attribute [-simp] _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.CyclicCohomology.fixedPiEquiv_apply_coe _root_.CyclicCohomology.herbrandH0EquivariantMulEquiv_mk _root_.IsDiscreteValuationRing.addVal_ringEquiv _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.OAI.PrimeDegreePackets.ThetaConstruction.schwartzCM_apply _root_.infinitePlace_mult_smul
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

/-!
# The local class-field axiom for decomposition-group blocks

This file supplies the localized-completion input for the class formation. First it
proves change-of-group equivalences for low-degree multiplicative Tate
cohomology. It then applies the canonical algebraic-localization results:
the algebraic localization of a finite Galois extension is finite Galois over
the completed base, and the localization equivalence identifies its Galois group with the
decomposition group.

For a nonarchimedean locally compact base completion, the concrete local
class-field axiom then gives:

* `H⁰` is the actual field-norm quotient;
* `H⁻¹` is trivial;
* the cardinality and Herbrand quotient equal the local degree.
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

universe uH uG uA

variable {H : Type uH} {G : Type uG} {A : Type uA}
    [Group H] [Fintype H] [Group G] [Fintype G]
    [CommGroup A] [MulDistribMulAction G A]

/-- Transport of the fixed subgroup along an isomorphism of acting groups. -/
noncomputable def fixedSubgroupCompMulEquiv (e : H ≃* G) :
    letI := MulDistribMulAction.compHom A e.toMonoidHom
    fixedSubgroup H A ≃* fixedSubgroup G A := by
  letI := MulDistribMulAction.compHom A e.toMonoidHom
  exact
    { toFun := fun x ↦ ⟨x.1, fun g ↦ by
          have hx := x.2 (e.symm g)
          change e (e.symm g) • x.1 = x.1 at hx
          simpa using hx⟩
      invFun := fun x ↦ ⟨x.1, fun h ↦ x.2 (e h)⟩
      left_inv := fun _ ↦ rfl
      right_inv := fun _ ↦ rfl
      map_mul' := fun _ _ ↦ rfl }

/-- Transport of the Tate norm kernel along an isomorphism of acting groups. -/
noncomputable def normKernelCompMulEquiv (e : H ≃* G) :
    letI := MulDistribMulAction.compHom A e.toMonoidHom
    normKernelSubgroup H A ≃* normKernelSubgroup G A := by
  letI := MulDistribMulAction.compHom A e.toMonoidHom
  exact
    { toFun := fun x ↦ ⟨x.1, by
          change tateNorm G A x.1 = 1
          rw [← tateNorm_compMulEquiv e]
          exact x.2⟩
      invFun := fun x ↦ ⟨x.1, by
          change tateNorm H A x.1 = 1
          rw [tateNorm_compMulEquiv e]
          exact x.2⟩
      left_inv := fun _ ↦ rfl
      right_inv := fun _ ↦ rfl
      map_mul' := fun _ _ ↦ rfl }

/-- Change of acting group for multiplicative degree-zero Herbrand
cohomology. -/
noncomputable def herbrandH0CompMulEquiv (e : H ≃* G) :
    letI := MulDistribMulAction.compHom A e.toMonoidHom
    HerbrandH0 H A ≃* HerbrandH0 G A := by
  letI := MulDistribMulAction.compHom A e.toMonoidHom
  let f := fixedSubgroupCompMulEquiv (A := A) e
  let N :=
    (tateNormSubgroup H A).subgroupOf (fixedSubgroup H A)
  let M :=
    (tateNormSubgroup G A).subgroupOf (fixedSubgroup G A)
  exact quotientMulEquivOfSplit N M
    f.toMonoidHom f.symm.toMonoidHom
    (fun y ↦ f.apply_symm_apply y)
    (fun x hx ↦ by
      rw [Subgroup.mem_subgroupOf] at hx ⊢
      rcases hx with ⟨a, ha⟩
      refine ⟨a, ?_⟩
      change tateNorm G A a = x.1
      rw [← tateNorm_compMulEquiv e]
      exact ha)
    (fun y hy ↦ by
      rw [Subgroup.mem_subgroupOf] at hy ⊢
      rcases hy with ⟨a, ha⟩
      refine ⟨a, ?_⟩
      change tateNorm H A a = y.1
      rw [tateNorm_compMulEquiv e]
      exact ha)
    (fun x hx ↦ by
      have hx1 : x = 1 := by
        apply f.injective
        simpa [f] using hx
      rw [hx1]
      exact N.one_mem)

/-- Change of acting group for multiplicative degree-minus-one Herbrand
cohomology. -/
noncomputable def herbrandHMinusOneCompMulEquiv
    (e : H ≃* G) (σ : H) :
    letI := MulDistribMulAction.compHom A e.toMonoidHom
    HerbrandHMinusOne H A σ ≃*
      HerbrandHMinusOne G A (e σ) := by
  letI := MulDistribMulAction.compHom A e.toMonoidHom
  let f := normKernelCompMulEquiv (A := A) e
  let N :=
    (augmentationSubgroup H A σ).subgroupOf
      (normKernelSubgroup H A)
  let M :=
    (augmentationSubgroup G A (e σ)).subgroupOf
      (normKernelSubgroup G A)
  exact quotientMulEquivOfSplit N M
    f.toMonoidHom f.symm.toMonoidHom
    (fun y ↦ f.apply_symm_apply y)
    (fun x hx ↦ by
      rw [Subgroup.mem_subgroupOf] at hx ⊢
      rcases hx with ⟨a, ha⟩
      refine ⟨a, ?_⟩
      exact ha)
    (fun y hy ↦ by
      rw [Subgroup.mem_subgroupOf] at hy ⊢
      rcases hy with ⟨a, ha⟩
      refine ⟨a, ?_⟩
      exact ha)
    (fun x hx ↦ by
      have hx1 : x = 1 := by
        apply f.injective
        simpa [f] using hx
      rw [hx1]
      exact N.one_mem)

end LocalClassFieldTheory
end
end

section
-- module Solutions.OAIQ244_DUKE.LocalField_NonarchimedeanLocalField_ResidueGalois
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.LubinTate.Valuations.exponentialValuationSubringIsLocalRing _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionFixedSubring.instIsLocalRing _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionResidueField.instField _root_.RamificationTheory.HilbertRamification.ValuationSubring.selectedResidueField.instAlgebra _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.maximalIdealPowSuccQuotModule _root_.ValuationTheory.DiscreteValuationField.DVF.residueField.field _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.isDomain _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.isLocalRing _root_.CyclicCohomology.binaryCoefficientFamilyCommGroup _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen _root_.relativeAdeleRingIntermediateAlgebra _root_.relativeAdeleRingTopIntermediateAlgebra
attribute [-simp] _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.IsDiscreteValuationRing.addVal_ringEquiv _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.LocalClassFieldTheory.galoisGroupIntegerUnitsMulDistribMulActionOfIsIntegralClosure_smul _root_.LocalFieldTheory.galoisGroupEquivResidueAlgEquivOfUnramifiedValuationOfIsIntegralClosure_apply _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.OAI.PrimeDegreePackets.ThetaConstruction.schwartzCM_apply _root_.infinitePlace_mult_smul
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false
/-!
# Galois actions on residue fields

Restricts field automorphisms to residue-field automorphisms and identifies
the resulting kernels and stabilizers with inertia subgroups.
-/

namespace LocalFieldTheory

noncomputable section

universe u

open scoped ValuativeRel
open _root_.LocalFieldTheory.IsNonarchimedeanLocalField

/-- The Galois action on residue units agrees with reducing the conjugate of an integer unit. -/
theorem galoisGroupResidueFieldEquivOfIsIntegralClosure_integerUnitsToResidueUnits
    (K L : Type u)
    [Field K] [ValuativeRel K] [Field L] [ValuativeRel L] [Algebra K L]
    [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]
    [IsIntegralClosure 𝒪[L] 𝒪[K] L] (σ : Gal(L / K)) (u : 𝒪[L]ˣ) :
    Units.mapEquiv (galoisGroupResidueFieldEquivOfIsIntegralClosure K L σ).toMulEquiv
        (integerUnitsToResidueUnits L u) =
      integerUnitsToResidueUnits L
        (Units.mapEquiv
          (galoisGroupIntegerRingEquivOfIsIntegralClosure K L σ).toMulEquiv u) := by
  ext
  rfl

/-- Reducing the sum of the actual integral-closure Galois conjugates gives the
sum of the induced residue-field conjugates. -/
theorem galoisGroup_sum_residue_eq_residueAlgEquiv_sum_of_isIntegralClosure
    (K L : Type u)
    [Field K] [ValuativeRel K] [Field L] [ValuativeRel L] [Algebra K L]
    [FiniteDimensional K L]
    [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]
    [IsIntegralClosure 𝒪[L] 𝒪[K] L] (a : 𝒪[L]) :
    IsLocalRing.residue 𝒪[L]
        (Finset.univ.sum fun σ : Gal(L / K) =>
          galoisGroupIntegerRingEquivOfIsIntegralClosure K L σ a) =
      Finset.univ.sum fun σ : Gal(L / K) =>
        galoisGroupResidueAlgEquivOfIsIntegralClosure K L σ
          (IsLocalRing.residue 𝒪[L] a) := by
  rw [map_sum]
  refine Finset.sum_congr rfl ?_
  intro σ _
  simp [galoisGroupResidueAlgEquivOfIsIntegralClosure]


end
end LocalFieldTheory
end

section
-- module Solutions.OAIQ244_DUKE.LocalField_NonarchimedeanLocalField_FiniteUnramified
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.KummerTheory.primeCyclotomicBaseIsGalois _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.LubinTate.Valuations.exponentialValuationSubringIsLocalRing _root_.LubinTate.compatibleGroupFamiliesGroup _root_.OAI.PrimeDegreePackets.boundedRealFields_finite _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_finite_residue _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionFixedSubring.instIsLocalRing _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionResidueField.instField _root_.RamificationTheory.HilbertRamification.ValuationSubring.selectedResidueField.instAlgebra _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.maximalIdealPowSuccQuotModule _root_.ValuationTheory.DiscreteValuationField.DVF.residueField.field _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.isDomain _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.isLocalRing _root_.CyclicCohomology.binaryCoefficientFamilyCommGroup _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen _root_.relativeAdeleRingIntermediateAlgebra _root_.relativeAdeleRingTopIntermediateAlgebra
attribute [-simp] _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.CyclicCohomology.integerUnitsModPrincipalUnitsAtLevelConcreteEquiv_mk _root_.CyclicCohomology.mem_chosenBaseUniformizerPowSubmodule_iff _root_.IsDiscreteValuationRing.addVal_ringEquiv _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.OAI.PrimeDegreePackets.ThetaConstruction.schwartzCM_apply _root_.infinitePlace_mult_smul
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false
/-!
# Finite unramified valued extensions

Develops the ideal, residue-field, Galois, trace, and norm consequences of a
finite valued extension with ramification index one and full residue degree.
-/

namespace LocalFieldTheory

noncomputable section

universe u

open scoped ValuativeRel
open _root_.LocalFieldTheory.IsNonarchimedeanLocalField
open Filter

/-- The induced additive map on `𝓂^n/𝓂^(n+1)` in an actual unramified
valuation extension. -/
def maximalIdealPowSuccQuotMapOfUnramifiedValuation (K L : Type u)
    [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
    [Algebra K L] [FiniteDimensional K L]
    [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]
    [Module.Finite 𝒪[K] 𝒪[L]]
    [LocalFieldTheory.IsNonarchimedeanLocalField.IsUnramifiedValuedExtension K L]
    (n : Nat) :
    MaximalIdealPowSuccQuot K n →+ MaximalIdealPowSuccQuot L n :=
  QuotientAddGroup.map
    (maximalIdealPowSuccSubmodule K n).toAddSubgroup
    (maximalIdealPowSuccSubmodule L n).toAddSubgroup
    (maximalIdealPowMapOfUnramifiedValuation K L n)
    (by
      intro a ha
      exact (mem_maximalIdealPowSuccSubmodule_iff L n
        (maximalIdealPowMapOfUnramifiedValuation K L n a)).2
        (integerRingMap_mem_maximalIdeal_pow_of_unramifiedValuation K L (n + 1)
          ((mem_maximalIdealPowSuccSubmodule_iff K n a).1 ha)))

/-- The induced map on successive maximal-ideal quotients sends a representative to its image under
the integer-ring inclusion. -/
theorem maximalIdealPowSuccQuotMapOfUnramifiedValuation_mk (K L : Type u)
    [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
    [Algebra K L] [FiniteDimensional K L]
    [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]
    [Module.Finite 𝒪[K] 𝒪[L]]
    [LocalFieldTheory.IsNonarchimedeanLocalField.IsUnramifiedValuedExtension K L]
    (n : Nat) (a : ((𝓂[K] ^ n : Ideal 𝒪[K]) : Type u)) :
    maximalIdealPowSuccQuotMapOfUnramifiedValuation K L n
        (maximalIdealPowSuccQuotMk K n a) =
      maximalIdealPowSuccQuotMk L n
        (maximalIdealPowMapOfUnramifiedValuation K L n a) :=
  QuotientAddGroup.map_mk _ _ _ _ a

/-- Base extension on `𝓂^n` sends the representative `r * ϖ_K^n` to the
corresponding upstairs representative using the image of the base uniformizer. -/
theorem maximalIdealPowMapOfUnramifiedValuation_mul_uniformizer_pow
    (K L : Type u)
    [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
    [Algebra K L] [FiniteDimensional K L]
    [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]
    [Module.Finite 𝒪[K] 𝒪[L]]
    [LocalFieldTheory.IsNonarchimedeanLocalField.IsUnramifiedValuedExtension K L]
    (n : Nat) (r : 𝒪[K]) :
    maximalIdealPowMapOfUnramifiedValuation K L n
        (maximalIdealPowMulUniformizerPowMap K (chosenIntegerRingUniformizer K)
          (chosenIntegerRingUniformizer_irreducible K) n r) =
      maximalIdealPowMulUniformizerPowMap L
        (integerRingMapOfValuationExtension K L (chosenIntegerRingUniformizer K))
        (integerRingMap_uniformizer_irreducible_of_unramifiedValuation K L) n
        (integerRingMapOfValuationExtension K L r) := by
  ext
  simp [maximalIdealPowMulUniformizerPowMap, integerRingMapOfValuationExtension, map_pow]

/-- On `𝓂^n/𝓂^(n+1)`, base extension commutes with the representative map
`r ↦ r * ϖ_K^n` when the upstairs uniformizer is the image of `ϖ_K`. -/
theorem maximalIdealPowSuccQuotMapOfUnramifiedValuation_mul_uniformizer_pow
    (K L : Type u)
    [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
    [Algebra K L] [FiniteDimensional K L]
    [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]
    [Module.Finite 𝒪[K] 𝒪[L]]
    [LocalFieldTheory.IsNonarchimedeanLocalField.IsUnramifiedValuedExtension K L]
    (n : Nat) (r : 𝒪[K]) :
    maximalIdealPowSuccQuotMapOfUnramifiedValuation K L n
        (maximalIdealPowSuccQuotMulUniformizerPowMap K (chosenIntegerRingUniformizer K)
          (chosenIntegerRingUniformizer_irreducible K) n r) =
      maximalIdealPowSuccQuotMulUniformizerPowMap L
        (integerRingMapOfValuationExtension K L (chosenIntegerRingUniformizer K))
        (integerRingMap_uniformizer_irreducible_of_unramifiedValuation K L) n
        (integerRingMapOfValuationExtension K L r) := by
  rw [maximalIdealPowSuccQuotMulUniformizerPowMap_apply,
    maximalIdealPowSuccQuotMapOfUnramifiedValuation_mk,
    maximalIdealPowSuccQuotMulUniformizerPowMap_apply]
  exact congrArg (maximalIdealPowSuccQuotMk L n)
    (maximalIdealPowMapOfUnramifiedValuation_mul_uniformizer_pow K L n r)

/-- With the upstairs uniformizer chosen as the image of the base uniformizer,
the associated-graded base-extension map is compatible with reduction on
integer-ring representatives. -/
theorem residueAddEquivMaximalIdealPowSuccQuotOfIrreducible_map_residue
    (K L : Type u)
    [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
    [Algebra K L] [FiniteDimensional K L]
    [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]
    [Module.Finite 𝒪[K] 𝒪[L]]
    [LocalFieldTheory.IsNonarchimedeanLocalField.IsUnramifiedValuedExtension K L]
    (n : Nat) (r : 𝒪[K]) :
    maximalIdealPowSuccQuotMapOfUnramifiedValuation K L n
        (residueAddEquivMaximalIdealPowSuccQuotOfIrreducible K
          (chosenIntegerRingUniformizer K) (chosenIntegerRingUniformizer_irreducible K) n
          (IsLocalRing.residue 𝒪[K] r)) =
      residueAddEquivMaximalIdealPowSuccQuotOfIrreducible L
        (integerRingMapOfValuationExtension K L (chosenIntegerRingUniformizer K))
        (integerRingMap_uniformizer_irreducible_of_unramifiedValuation K L) n
        (residueFieldMapOfValuationExtension K L (IsLocalRing.residue 𝒪[K] r)) := by
  rw [residueAddEquivMaximalIdealPowSuccQuotOfIrreducible_residue,
    maximalIdealPowSuccQuotMapOfUnramifiedValuation_mul_uniformizer_pow]
  rw [residueFieldMapOfValuationExtension_residue]
  rw [residueAddEquivMaximalIdealPowSuccQuotOfIrreducible_residue]

/-- The base-uniformizer comparison `𝓀[K] ≃ 𝓂_K^n/𝓂_K^(n+1)` commutes with
base extension of residue fields in an actual unramified valuation extension.

The upstairs comparison deliberately uses `algebraMap ϖ_K` as uniformizer, not
the independently chosen canonical uniformizer of `L`; this is the twist-free
form needed before the principal-unit norm/trace calculation. -/
theorem residueAddEquivMaximalIdealPowSuccQuotOfIrreducible_map
    (K L : Type u)
    [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
    [Algebra K L] [FiniteDimensional K L]
    [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]
    [Module.Finite 𝒪[K] 𝒪[L]]
    [LocalFieldTheory.IsNonarchimedeanLocalField.IsUnramifiedValuedExtension K L]
    (n : Nat) (x : 𝓀[K]) :
    maximalIdealPowSuccQuotMapOfUnramifiedValuation K L n
        (residueAddEquivMaximalIdealPowSuccQuotOfIrreducible K
          (chosenIntegerRingUniformizer K) (chosenIntegerRingUniformizer_irreducible K) n x) =
      residueAddEquivMaximalIdealPowSuccQuotOfIrreducible L
        (integerRingMapOfValuationExtension K L (chosenIntegerRingUniformizer K))
        (integerRingMap_uniformizer_irreducible_of_unramifiedValuation K L) n
        (residueFieldMapOfValuationExtension K L x) := by
  refine Quotient.inductionOn' x ?_
  intro r
  exact residueAddEquivMaximalIdealPowSuccQuotOfIrreducible_map_residue K L n r

/-- Base extension carries the concrete unit `1 + a` to the concrete upstairs
unit `1 + algebraMap a`. -/
theorem principalUnitsMapOfUnramifiedValuation_oneAdd (K L : Type u)
    [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
    [Algebra K L] [FiniteDimensional K L]
    [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]
    [Module.Finite 𝒪[K] 𝒪[L]]
    [LocalFieldTheory.IsNonarchimedeanLocalField.IsUnramifiedValuedExtension K L]
    (n : Nat) (hn : 1 ≤ n) (a : (𝓂[K] ^ n : Ideal 𝒪[K])) :
    principalUnitsMapOfUnramifiedValuation K L n
        (principalUnitOneAddOfMemPowSubgroup K hn (a : 𝒪[K]) a.2) =
      principalUnitOneAddOfMemPowSubgroup L hn
        (integerRingMapOfValuationExtension K L (a : 𝒪[K]))
        (integerRingMap_mem_maximalIdeal_pow_of_unramifiedValuation K L n a.2) := by
  ext
  simp [principalUnitsMapOfUnramifiedValuation, principalUnitOneAddOfMemPowSubgroup,
    principalUnitOneAddOfMemPow_val, integerRingMapOfValuationExtension]

/-- Base extension on `𝓂^n/𝓂^(n+1)` is compatible with the comparison
`a ↦ 1 + a` to successive principal-unit quotients. -/
theorem principalUnitsSuccQuotOfMaximalIdealPowSuccQuot_map
    (K L : Type u)
    [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
    [Algebra K L] [FiniteDimensional K L]
    [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]
    [Module.Finite 𝒪[K] 𝒪[L]]
    [LocalFieldTheory.IsNonarchimedeanLocalField.IsUnramifiedValuedExtension K L]
    (n : Nat) (hn : 1 ≤ n) (x : MaximalIdealPowSuccQuot K n) :
    principalUnitsSuccQuotMapOfUnramifiedValuation K L n
        (principalUnitsSuccQuotOfMaximalIdealPowSuccQuot K n hn x) =
    principalUnitsSuccQuotOfMaximalIdealPowSuccQuot L n hn
        (maximalIdealPowSuccQuotMapOfUnramifiedValuation K L n x) := by
  refine MaximalIdealPowSuccQuot.inductionOn n
    (motive := fun x =>
      principalUnitsSuccQuotMapOfUnramifiedValuation K L n
          (principalUnitsSuccQuotOfMaximalIdealPowSuccQuot K n hn x) =
        principalUnitsSuccQuotOfMaximalIdealPowSuccQuot L n hn
          (maximalIdealPowSuccQuotMapOfUnramifiedValuation K L n x))
    x ?_
  intro a
  rw [maximalIdealPowSuccQuotMapOfUnramifiedValuation_mk,
    principalUnitsSuccQuotOfMaximalIdealPowSuccQuot_mk,
    principalUnitsSuccQuotOfMaximalIdealPowSuccQuot_mk]
  rw [principalUnitsSuccQuotOfIdealPow_apply, principalUnitsSuccQuotOfIdealPow_apply,
    principalUnitsSuccQuotMapOfUnramifiedValuation_mk]
  congr 1
  exact principalUnitsMapOfUnramifiedValuation_oneAdd K L n hn a

/-- Additive form of compatibility between base extension and the comparison
`𝓂^n/𝓂^(n+1) ≃ U^n/U^(n+1)`. -/
theorem principalUnitsSuccQuotOfMaximalIdealPowSuccQuotAdd_map
    (K L : Type u)
    [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
    [Algebra K L] [FiniteDimensional K L]
    [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]
    [Module.Finite 𝒪[K] 𝒪[L]]
    [LocalFieldTheory.IsNonarchimedeanLocalField.IsUnramifiedValuedExtension K L]
    (n : Nat) (hn : 1 ≤ n) (x : MaximalIdealPowSuccQuot K n) :
    MonoidHom.toAdditive (principalUnitsSuccQuotMapOfUnramifiedValuation K L n)
        (principalUnitsSuccQuotOfMaximalIdealPowSuccQuotAdd K n hn x) =
      principalUnitsSuccQuotOfMaximalIdealPowSuccQuotAdd L n hn
        (maximalIdealPowSuccQuotMapOfUnramifiedValuation K L n x) := by
  change Additive.ofMul
      (principalUnitsSuccQuotMapOfUnramifiedValuation K L n
        (principalUnitsSuccQuotOfMaximalIdealPowSuccQuot K n hn x)) =
    Additive.ofMul
      (principalUnitsSuccQuotOfMaximalIdealPowSuccQuot L n hn
        (maximalIdealPowSuccQuotMapOfUnramifiedValuation K L n x))
  rw [principalUnitsSuccQuotOfMaximalIdealPowSuccQuot_map]

/-- The base-uniformizer identification `U^n/U^(n+1) ≃ 𝓀` commutes with
base extension in an actual unramified valuation extension, when the upstairs
uniformizer is chosen as the image of the base uniformizer. -/
theorem principalUnitsSuccQuotAddEquivResidueOfIrreducible_symm_map
    (K L : Type u)
    [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
    [Algebra K L] [FiniteDimensional K L]
    [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]
    [Module.Finite 𝒪[K] 𝒪[L]]
    [LocalFieldTheory.IsNonarchimedeanLocalField.IsUnramifiedValuedExtension K L]
    (n : Nat) (hn : 1 ≤ n) (x : 𝓀[K]) :
    MonoidHom.toAdditive (principalUnitsSuccQuotMapOfUnramifiedValuation K L n)
        ((principalUnitsSuccQuotAddEquivResidueOfIrreducible K
          (chosenIntegerRingUniformizer K) (chosenIntegerRingUniformizer_irreducible K)
          n hn).symm x) =
      (principalUnitsSuccQuotAddEquivResidueOfIrreducible L
        (integerRingMapOfValuationExtension K L (chosenIntegerRingUniformizer K))
        (integerRingMap_uniformizer_irreducible_of_unramifiedValuation K L)
        n hn).symm (residueFieldMapOfValuationExtension K L x) := by
  change MonoidHom.toAdditive (principalUnitsSuccQuotMapOfUnramifiedValuation K L n)
      (principalUnitsSuccQuotOfMaximalIdealPowSuccQuotAdd K n hn
        (residueAddEquivMaximalIdealPowSuccQuotOfIrreducible K
          (chosenIntegerRingUniformizer K) (chosenIntegerRingUniformizer_irreducible K) n x)) =
    principalUnitsSuccQuotOfMaximalIdealPowSuccQuotAdd L n hn
      (residueAddEquivMaximalIdealPowSuccQuotOfIrreducible L
        (integerRingMapOfValuationExtension K L (chosenIntegerRingUniformizer K))
        (integerRingMap_uniformizer_irreducible_of_unramifiedValuation K L)
        n (residueFieldMapOfValuationExtension K L x))
  rw [principalUnitsSuccQuotOfMaximalIdealPowSuccQuotAdd_map]
  rw [residueAddEquivMaximalIdealPowSuccQuotOfIrreducible_map]

/-- Base extension on successive principal-unit quotients is injective in an
actual unramified valuation extension. -/
theorem principalUnitsSuccQuotMapOfUnramifiedValuation_injective
    (K L : Type u)
    [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
    [Algebra K L] [FiniteDimensional K L]
    [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]
    [Module.Finite 𝒪[K] 𝒪[L]]
    [LocalFieldTheory.IsNonarchimedeanLocalField.IsUnramifiedValuedExtension K L]
    (n : Nat) (hn : 1 ≤ n) :
    Function.Injective (principalUnitsSuccQuotMapOfUnramifiedValuation K L n) := by
  intro x y hxy
  let eK :=
    principalUnitsSuccQuotAddEquivResidueOfIrreducible K
      (chosenIntegerRingUniformizer K) (chosenIntegerRingUniformizer_irreducible K) n hn
  let eL :=
    principalUnitsSuccQuotAddEquivResidueOfIrreducible L
      (integerRingMapOfValuationExtension K L (chosenIntegerRingUniformizer K))
      (integerRingMap_uniformizer_irreducible_of_unramifiedValuation K L) n hn
  let xκ : 𝓀[K] := eK (Additive.ofMul x)
  let yκ : 𝓀[K] := eK (Additive.ofMul y)
  have hxmap :
      MonoidHom.toAdditive (principalUnitsSuccQuotMapOfUnramifiedValuation K L n)
          (Additive.ofMul x) =
        eL.symm (residueFieldMapOfValuationExtension K L xκ) := by
    simpa [eK, eL, xκ] using
      principalUnitsSuccQuotAddEquivResidueOfIrreducible_symm_map K L n hn xκ
  have hymap :
      MonoidHom.toAdditive (principalUnitsSuccQuotMapOfUnramifiedValuation K L n)
          (Additive.ofMul y) =
        eL.symm (residueFieldMapOfValuationExtension K L yκ) := by
    simpa [eK, eL, yκ] using
      principalUnitsSuccQuotAddEquivResidueOfIrreducible_symm_map K L n hn yκ
  have hxyAdd :
      MonoidHom.toAdditive (principalUnitsSuccQuotMapOfUnramifiedValuation K L n)
          (Additive.ofMul x) =
        MonoidHom.toAdditive (principalUnitsSuccQuotMapOfUnramifiedValuation K L n)
          (Additive.ofMul y) := by
    change Additive.ofMul
        (principalUnitsSuccQuotMapOfUnramifiedValuation K L n x) =
      Additive.ofMul (principalUnitsSuccQuotMapOfUnramifiedValuation K L n y)
    exact congrArg Additive.ofMul hxy
  have hres :
      residueFieldMapOfValuationExtension K L xκ =
        residueFieldMapOfValuationExtension K L yκ :=
    eL.symm.injective (hxmap.symm.trans (hxyAdd.trans hymap))
  have hκ : xκ = yκ :=
    (RingHom.injective (residueFieldMapOfValuationExtension K L)) hres
  have hadd : Additive.ofMul x = Additive.ofMul y :=
    eK.injective (by simpa [xκ, yκ] using hκ)
  exact Additive.ofMul.injective hadd

/-- Principal-unit contraction for an actual unramified valuation extension.

If a base integer unit becomes an `n`-th principal unit upstairs, then it was
already an `n`-th principal unit downstairs. -/
theorem principalUnits_of_integerUnitsMap_mem_principalUnits_of_unramifiedValuation
    (K L : Type u)
    [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
    [Algebra K L] [FiniteDimensional K L]
    [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]
    [Module.Finite 𝒪[K] 𝒪[L]]
    [LocalFieldTheory.IsNonarchimedeanLocalField.IsUnramifiedValuedExtension K L]
    (n : Nat) {a : 𝒪[K]ˣ}
    (haL : integerUnitsMapOfValuationExtension K L a ∈ principalUnits L n) :
    a ∈ principalUnits K n := by
  let xK : 𝒪[K] := (a : 𝒪[K]) - 1
  let πK : 𝒪[K] := chosenIntegerRingUniformizer K
  have hxLpow : integerRingMapOfValuationExtension K L xK ∈ (𝓂[L] ^ n : Ideal 𝒪[L]) := by
    have haLpow :=
      (mem_principalUnits_iff L (integerUnitsMapOfValuationExtension K L a) n).1 haL
    simpa [xK, integerRingMapOfValuationExtension, sub_eq_add_neg] using haLpow
  have hπL : Irreducible (integerRingMapOfValuationExtension K L πK) := by
    simpa [πK] using integerRingMap_uniformizer_irreducible_of_unramifiedValuation K L
  have hvalL :
      ValuativeRel.valuation L
          ((integerRingMapOfValuationExtension K L xK : 𝒪[L]) : L) ≤
        ValuativeRel.valuation L
          ((integerRingMapOfValuationExtension K L πK : 𝒪[L]) : L) ^ n := by
    have hset := Irreducible.maximalIdeal_pow_eq_setOfPred_le_v_coe_pow
      (ValuativeRel.valuation L) hπL n
    exact (show integerRingMapOfValuationExtension K L xK ∈
        ({y : 𝒪[L] | ValuativeRel.valuation L (y : L) ≤
          ValuativeRel.valuation L
            ((integerRingMapOfValuationExtension K L πK : 𝒪[L]) : L) ^ n}) from by
      rw [← hset]
      exact hxLpow)
  have hvalL' :
      ValuativeRel.valuation L (algebraMap K L (xK : K)) ≤
        ValuativeRel.valuation L (algebraMap K L (((πK ^ n : 𝒪[K]) : K))) := by
    simpa [integerRingMapOfValuationExtension, map_pow] using hvalL
  have hvalKpow :
      ValuativeRel.valuation K (xK : K) ≤
        ValuativeRel.valuation K (((πK ^ n : 𝒪[K]) : K)) :=
    (Valuation.HasExtension.val_map_le_iff
      (ValuativeRel.valuation K) (ValuativeRel.valuation L)
      (xK : K) (((πK ^ n : 𝒪[K]) : K))).1 hvalL'
  rw [mem_principalUnits_iff]
  change xK ∈ (𝓂[K] ^ n : Ideal 𝒪[K])
  have hsetK := Irreducible.maximalIdeal_pow_eq_setOfPred_le_v_coe_pow
    (ValuativeRel.valuation K) (chosenIntegerRingUniformizer_irreducible K) n
  have hvalK : xK ∈
      ({y : 𝒪[K] | ValuativeRel.valuation K (y : K) ≤
        ValuativeRel.valuation K ((πK : 𝒪[K]) : K) ^ n}) := by
    simpa [πK, map_pow] using hvalKpow
  change xK ∈ ((𝓂[K] ^ n : Ideal 𝒪[K]) : Set 𝒪[K])
  rw [hsetK]
  exact hvalK


/-- In the unramified valuation case, products over the actual
integral-closure real Galois residue action can be reindexed as products over
the full residue-field automorphism group. -/
theorem galoisGroupResidueAlgEquivOfIsIntegralClosure_prod_eq_prod_algEquiv_of_unramifiedValuation
    (K L : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] [Field L] [ValuativeRel L] [TopologicalSpace L]
    [IsNonarchimedeanLocalField L] [Algebra K L] [FiniteDimensional K L]
    [IsGalois K L]
    [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]
    [IsIntegralClosure 𝒪[L] 𝒪[K] L] [Module.Finite 𝒪[K] 𝒪[L]]
    [LocalFieldTheory.IsNonarchimedeanLocalField.IsUnramifiedValuedExtension K L]
    (u : 𝓀[L]ˣ) :
    Finset.univ.prod (fun σ : Gal(L / K) =>
      Units.mapEquiv
        (galoisGroupResidueAlgEquivOfIsIntegralClosure K L σ).toMulEquiv u) =
    Finset.univ.prod (fun τ : 𝓀[L] ≃ₐ[𝓀[K]] 𝓀[L] =>
      Units.mapEquiv τ.toMulEquiv u) :=
  Fintype.prod_equiv
    (galoisGroupEquivResidueAlgEquivOfUnramifiedValuationOfIsIntegralClosure K L).toEquiv
    (fun σ : Gal(L / K) =>
      Units.mapEquiv
        (galoisGroupResidueAlgEquivOfIsIntegralClosure K L σ).toMulEquiv u)
    (fun τ : 𝓀[L] ≃ₐ[𝓀[K]] 𝓀[L] => Units.mapEquiv τ.toMulEquiv u)
    (by intro σ; rfl)

/-- In the unramified valuation case, sums over the actual integral-closure
real Galois residue action can be reindexed as sums over the full residue-field
automorphism group. -/
theorem galoisGroupResidueAlgEquivOfIsIntegralClosure_sum_eq_sum_algEquiv_of_unramifiedValuation
    (K L : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] [Field L] [ValuativeRel L] [TopologicalSpace L]
    [IsNonarchimedeanLocalField L] [Algebra K L] [FiniteDimensional K L]
    [IsGalois K L]
    [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]
    [IsIntegralClosure 𝒪[L] 𝒪[K] L] [Module.Finite 𝒪[K] 𝒪[L]]
    [LocalFieldTheory.IsNonarchimedeanLocalField.IsUnramifiedValuedExtension K L]
    (x : 𝓀[L]) :
    Finset.univ.sum (fun σ : Gal(L / K) =>
      galoisGroupResidueAlgEquivOfIsIntegralClosure K L σ x) =
    Finset.univ.sum (fun τ : 𝓀[L] ≃ₐ[𝓀[K]] 𝓀[L] => τ x) :=
  Fintype.sum_equiv
    (galoisGroupEquivResidueAlgEquivOfUnramifiedValuationOfIsIntegralClosure K L).toEquiv
    (fun σ : Gal(L / K) => galoisGroupResidueAlgEquivOfIsIntegralClosure K L σ x)
    (fun τ : 𝓀[L] ≃ₐ[𝓀[K]] 𝓀[L] => τ x)
    (by intro σ; rfl)

/-- In the unramified valuation case, reducing the actual integral-closure
Galois sum gives the base extension of the finite residue-field trace. -/
theorem galoisGroup_sum_residue_eq_algebraMap_trace_of_unramifiedValuation_of_isIntegralClosure
    (K L : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] [Field L] [ValuativeRel L] [TopologicalSpace L]
    [IsNonarchimedeanLocalField L] [Algebra K L] [FiniteDimensional K L]
    [IsGalois K L]
    [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]
    [IsIntegralClosure 𝒪[L] 𝒪[K] L] [Module.Finite 𝒪[K] 𝒪[L]]
    [LocalFieldTheory.IsNonarchimedeanLocalField.IsUnramifiedValuedExtension K L]
    (a : 𝒪[L]) :
    IsLocalRing.residue 𝒪[L]
        (Finset.univ.sum fun σ : Gal(L / K) =>
          galoisGroupIntegerRingEquivOfIsIntegralClosure K L σ a) =
      algebraMap 𝓀[K] 𝓀[L]
        (Algebra.trace 𝓀[K] 𝓀[L] (IsLocalRing.residue 𝒪[L] a)) := by
  rw [galoisGroup_sum_residue_eq_residueAlgEquiv_sum_of_isIntegralClosure K L a]
  rw [galoisGroupResidueAlgEquivOfIsIntegralClosure_sum_eq_sum_algEquiv_of_unramifiedValuation
    K L]
  exact (trace_eq_sum_automorphisms
    (K := 𝓀[K]) (L := 𝓀[L]) (IsLocalRing.residue 𝒪[L] a)).symm

/-- Actual integral-closure version of the base-uniformizer coefficient
calculation for the real Galois sum. -/
theorem galoisGroup_sum_mul_base_uniformizer_pow_eq_coeff_sum_of_isIntegralClosure
    (K L : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] [Field L] [ValuativeRel L]
    [Algebra K L] [FiniteDimensional K L]
    [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]
    [IsIntegralClosure 𝒪[L] 𝒪[K] L]
    (n : Nat) (r : 𝒪[L]) :
    let πL := integerRingMapOfValuationExtension K L (chosenIntegerRingUniformizer K)
    Finset.univ.sum (fun σ : Gal(L / K) =>
        galoisGroupIntegerRingEquivOfIsIntegralClosure K L σ (r * πL ^ n)) =
      (Finset.univ.sum fun σ : Gal(L / K) =>
        galoisGroupIntegerRingEquivOfIsIntegralClosure K L σ r) * πL ^ n := by
  intro πL
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl ?_
  intro σ _
  rw [map_mul, map_pow]
  change galoisGroupIntegerRingEquivOfIsIntegralClosure K L σ r *
      (galoisGroupIntegerRingEquivOfIsIntegralClosure K L σ
        (integerRingMapOfValuationExtension K L (chosenIntegerRingUniformizer K))) ^ n =
    galoisGroupIntegerRingEquivOfIsIntegralClosure K L σ r * πL ^ n
  rw [galoisGroupIntegerRingEquivOfIsIntegralClosure_integerRingMap]

/-- On the associated graded piece defined by the base uniformizer, the
coefficient of the Galois sum is the finite residue-field trace. -/
theorem galoisSum_uniformizerGraded_eq_residueTrace
    (K L : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] [Field L] [ValuativeRel L] [TopologicalSpace L]
    [IsNonarchimedeanLocalField L] [Algebra K L] [FiniteDimensional K L]
    [IsGalois K L]
    [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]
    [IsIntegralClosure 𝒪[L] 𝒪[K] L] [Module.Finite 𝒪[K] 𝒪[L]]
    [LocalFieldTheory.IsNonarchimedeanLocalField.IsUnramifiedValuedExtension K L]
    (n : Nat) (r : 𝒪[L]) :
    let πL := integerRingMapOfValuationExtension K L (chosenIntegerRingUniformizer K)
    let hπL := integerRingMap_uniformizer_irreducible_of_unramifiedValuation K L
    maximalIdealPowSuccQuotMulUniformizerPowMap L πL hπL n
        (Finset.univ.sum fun σ : Gal(L / K) =>
          galoisGroupIntegerRingEquivOfIsIntegralClosure K L σ r) =
      residueAddEquivMaximalIdealPowSuccQuotOfIrreducible L πL hπL n
        (algebraMap 𝓀[K] 𝓀[L]
          (Algebra.trace 𝓀[K] 𝓀[L] (IsLocalRing.residue 𝒪[L] r))) := by
  intro πL hπL
  rw [← residueAddEquivMaximalIdealPowSuccQuotOfIrreducible_residue L πL hπL n
    (Finset.univ.sum fun σ : Gal(L / K) =>
      galoisGroupIntegerRingEquivOfIsIntegralClosure K L σ r)]
  rw [galoisGroup_sum_residue_eq_algebraMap_trace_of_unramifiedValuation_of_isIntegralClosure
    K L r]

end
end LocalFieldTheory
end

section
-- module Solutions.OAIQ244_DUKE.AlgebraicNumberTheory_Adele_FinitePlaceTensorBlock
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable
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

section Equivariance

variable
    (v : HeightOneSpectrum (𝓞 K))
    (w : AbsoluteValueExtension
      (HeightOneSpectrum.adicAbv K v) L)

local instance finitePlaceScalarTensorUnitsAction :
    MulDistribMulAction
      (L ≃ₐ[K] L)
      (v.adicCompletion K ⊗[K] L)ˣ :=
  scalarTensorUnitsAction
    (K := K) (L := L) (A := v.adicCompletion K)

end Equivariance
end
end

section
-- module Solutions.OAIQ244_DUKE.AlgebraicNumberTheory_Adele_InfinitePlaceTensorBlock
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionResidueField.instField _root_.RamificationTheory.HilbertRamification.ValuationSubring.selectedResidueField.instAlgebra _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen _root_.relativeAdeleRingIntermediateAlgebra _root_.relativeAdeleRingTopIntermediateAlgebra
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

section Galois

variable [IsGalois K L]

section Equivariance

variable
    (w : InfinitePlace K)
    (hw : w.1.IsNontrivial)
    (u : AbsoluteValueExtension w.1 L)

local instance infinitePlaceScalarTensorUnitsAction :
    MulDistribMulAction (L ≃ₐ[K] L) (w.Completion ⊗[K] L)ˣ :=
  scalarTensorUnitsAction (K := K) (L := L) (A := w.Completion)

end Equivariance

end Galois
end
end

section
-- module Solutions.OAIQ244_DUKE.AlgebraicNumberTheory_SUnit_Rank
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.DiscreteNthRootsSubgroup.instCommGroupSubtypeUnitsMemSubgroup _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.KummerTheory.nthRootsSubgroupFintype _root_.LocalFieldTheory.DiscreteValuationField.finite_nsmulAddKernel_padicInt_pi _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_multiplicative_nthPowerKernel _root_.LocalFieldTheory.finite_nsmulAddKernel_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.LubinTate.compatibleGroupFamiliesCommGroup _root_.OAI.PrimeDegreePackets.boundedRealFields_finite _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.maximalIdealPowSuccQuotModule _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.isDomain _root_.CyclicCohomology.binaryCoefficientFamilyCommGroup _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

/-!
# Torsion and rank sources for `S`-units

This file supplies the algebraic rank and torsion input for `S`-units.
The finite set `S` contains the finite places; all infinite places are
understood to be present.
-/

noncomputable section

open IsDedekindDomain
open scoped NumberField nonZeroDivisors


variable {K : Type*} [Field K] [NumberField K]

namespace SUnitGroup

section Rank

variable (S : Finset (HeightOneSpectrum (𝓞 K)))

/-- The free rank of the `S`-unit group is the ordinary Dirichlet rank plus
the number of finite places in `S`. -/
theorem finrank :
    Module.finrank ℤ (Additive (SUnitGroup (K := K) S)) =
      NumberField.Units.rank K + S.card := by
  let : Module.Finite ℤ
      (Additive (SUnitGroup (K := K) S)) :=
    moduleFinite (K := K) S
  let : Module.Finite ℤ (S → ℤ) := inferInstance
  let : Module.Finite ℤ
      (LinearMap.range (divisorLinearMap (K := K) S)) :=
    Module.Finite.of_fg
      (IsNoetherian.noetherian
        (LinearMap.range (divisorLinearMap (K := K) S)))
  let : Module.Finite ℤ
      (LinearMap.ker (divisorLinearMap (K := K) S)) :=
    Module.Finite.of_fg
      (IsNoetherian.noetherian
        (LinearMap.ker (divisorLinearMap (K := K) S)))
  have hrank :
      Module.rank ℤ (Additive (SUnitGroup (K := K) S)) =
        Module.rank ℤ
            (LinearMap.range (divisorLinearMap (K := K) S)) +
          Module.rank ℤ
            (LinearMap.ker (divisorLinearMap (K := K) S)) := by
    have h :=
      LinearMap.rank_eq_of_surjective
        (f := (divisorLinearMap (K := K) S).rangeRestrict)
        (divisorLinearMap (K := K) S).surjective_rangeRestrict
    rw [LinearMap.ker_rangeRestrict] at h
    exact h
  have hcard :
      (Module.finrank ℤ
          (Additive (SUnitGroup (K := K) S)) : Cardinal) =
        (Module.finrank ℤ
            (LinearMap.range (divisorLinearMap (K := K) S)) : Cardinal) +
          (Module.finrank ℤ
            (LinearMap.ker (divisorLinearMap (K := K) S)) : Cardinal) := by
    rw [Module.finrank_eq_rank, Module.finrank_eq_rank,
      (LinearMap.ker (divisorLinearMap (K := K) S)).finrank_eq_rank]
    exact hrank
  rw [← Nat.cast_inj (R := Cardinal), Nat.cast_add]
  calc
    (Module.finrank ℤ
        (Additive (SUnitGroup (K := K) S)) : Cardinal) =
      (Module.finrank ℤ
          (LinearMap.range (divisorLinearMap (K := K) S)) : Cardinal) +
        (Module.finrank ℤ
          (LinearMap.ker (divisorLinearMap (K := K) S)) : Cardinal) :=
      hcard
    _ = (S.card : Cardinal) +
        (NumberField.Units.rank K : Cardinal) := by
      rw [finrank_divisor_range (K := K) S,
        finrank_divisor_ker (K := K) S]
    _ = (NumberField.Units.rank K : Cardinal) +
        (S.card : Cardinal) := by rw [add_comm]

end Rank

end SUnitGroup
end
end

section
-- module Solutions.OAIQ244_DUKE.AlgebraicNumberTheory_SUnit_LogLattice
attribute [-instance] _root_.CyclicCohomology.permutationSublattice_discreteTopology _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.DiscreteNthRootsSubgroup.instCommGroupSubtypeUnitsMemSubgroup _root_.KummerTheory.DiscreteNthRootsSubgroup.instTopologicalSpaceSubtypeUnitsMemSubgroup _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.KummerTheory.nthRootsSubgroupFintype _root_.KummerTheory.primeCyclotomicBaseFiniteDimensional _root_.LocalFieldTheory.DiscreteValuationField.finite_nsmulAddKernel_padicInt_pi _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_multiplicative_nthPowerKernel _root_.LocalFieldTheory.finite_nsmulAddKernel_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.LubinTate.compatibleGroupFamiliesCommGroup _root_.LubinTate.compatibleGroupFamiliesGroup _root_.OAI.PrimeDegreePackets.ThetaConstruction.coordinateLattice_discrete _root_.OAI.PrimeDegreePackets.boundedRealFields_finite _root_.OAI.PrimeDegreePackets.diagonalLogAction _root_.OAI.PrimeDegreePackets.instNonemptyLeafTestSpace _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.integralGroup_discrete _root_.OAI.PrimeDegreePackets.logSubgroup_discrete _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.OAI.PrimeDegreePackets.orderedLogSubgroup_discrete _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionResidueField.instField _root_.RamificationTheory.HilbertRamification.ValuationSubring.selectedResidueField.instAlgebra _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.RelativeIdeleGroup.relativeIdeleMulAction _root_.ValuationTheory.DiscreteValuationField.DVF.maximalIdealPowSuccQuotModule _root_.ValuationTheory.DiscreteValuationField.DVF.residueField.field _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.isDomain _root_.CyclicCohomology.binaryCoefficientFamilyCommGroup _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.relativeAdeleRingIntermediateAlgebra _root_.relativeAdeleRingTopIntermediateAlgebra
attribute [-simp] _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.IsDiscreteValuationRing.addVal_ringEquiv _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.KummerTheory.mem_sUnitFiniteKummerRadical_iff _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.LocalFieldTheory.residueField_algebraMap_residue _root_.OAI.PrimeDegreePackets.ThetaConstruction.schwartzCM_apply _root_.infinitePlace_mult_smul _root_.sUnit_smul_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

/-!
# The logarithmic lattice of `S`-units

This file develops the logarithmic lattice of `S`-units. The
finite set `S` consists of the finite places; all infinite places are
understood to belong to the set of places used in the theorem.

The first construction uses the usual reduced archimedean logarithmic
space (one infinite coordinate is omitted) together with the integral
principal-divisor coordinates at `S`.  Its image is proved directly to
be a complete `ℤ`-lattice.  The normalized, all-place logarithmic map
and its coordinate-sum-zero hyperplane are constructed below from this
lattice.
-/

noncomputable section

open IsDedekindDomain Module
open scoped Classical NumberField nonZeroDivisors


variable {K : Type*} [Field K] [NumberField K]

namespace SUnitGroup

variable (S : Finset (HeightOneSpectrum (𝓞 K)))

/-- The reduced logarithm vanishes precisely on the roots of unity. -/
theorem reducedLog_eq_zero_iff
    (x : Additive (SUnitGroup (K := K) S)) :
    reducedLog (K := K) S x = 0 ↔
      x ∈ AddCommGroup.torsion
        (Additive (SUnitGroup (K := K) S)) := by
  constructor
  · intro hx
    have hxdiv :
        x ∈ LinearMap.ker
          (divisorLinearMap (K := K) S) := by
      apply LinearMap.mem_ker.mpr
      ext v
      have hv := congrFun (congrArg Prod.snd hx) v
      simpa [reducedLog, divisorLinearMap, divisor] using
        (show
          (divisorCoordinate (K := K) S
            (Additive.toMul x) v : ℝ) = 0 from hv)
    rw [← range_fromNumberFieldUnitsLinearMap_eq_ker_divisorLinearMap
      (K := K) S] at hxdiv
    obtain ⟨u, hu⟩ := hxdiv
    have hxu :
        x =
          fromNumberFieldUnitsLinearMap (K := K) S u :=
      hu.symm
    have hlog :
        NumberField.Units.logEmbedding K u = 0 := by
      have hfst := congrArg Prod.fst hx
      rw [hxu] at hfst
      simpa [fromNumberFieldUnitsLinearMap] using hfst
    have hutors :
        Additive.toMul u ∈ NumberField.Units.torsion K := by
      exact
        NumberField.Units.dirichletUnitTheorem.logEmbedding_eq_zero_iff.mp
          hlog
    change
      Additive.toMul x ∈
        CommGroup.torsion (SUnitGroup (K := K) S)
    rw [torsion_eq_rootsOfUnity_range (K := K) S]
    refine ⟨Additive.toMul u, hutors, ?_⟩
    exact (congrArg Additive.toMul hxu).symm
  · intro hx
    change
      Additive.toMul x ∈
        CommGroup.torsion (SUnitGroup (K := K) S) at hx
    rw [torsion_eq_rootsOfUnity_range (K := K) S] at hx
    obtain ⟨u, hu, hux⟩ := hx
    have hxadd :
        x =
          Additive.ofMul
            (fromNumberFieldUnits (K := K) S u) := by
      apply Additive.toMul.injective
      exact hux.symm
    rw [hxadd]
    apply Prod.ext
    ·
      simpa using
        (NumberField.Units.dirichletUnitTheorem.logEmbedding_eq_zero_iff.mpr
          hu)
    ·
      exact reducedLog_snd_fromNumberFieldUnits
        (K := K) S u

/-- The kernel of the reduced logarithmic map is the additive torsion
submodule. -/
theorem reducedLogLinearMap_ker :
    LinearMap.ker (reducedLogLinearMap (K := K) S) =
      (AddCommGroup.torsion
        (Additive (SUnitGroup (K := K) S))).toIntSubmodule := by
  ext x
  rw [LinearMap.mem_ker]
  exact reducedLog_eq_zero_iff (K := K) S x

/-- The reduced logarithmic image is discrete.  Near the origin the
integral finite coordinates must vanish, reducing the assertion to the
ordinary Dirichlet unit lattice. -/
instance instDiscreteTopology_reducedLogLattice :
    DiscreteTopology (reducedLogLattice (K := K) S) := by
  classical
  let :
      DiscreteTopology
        {x :
          NumberField.Units.dirichletUnitTheorem.logSpace K //
          x ∈ NumberField.Units.unitLattice K} := by
    infer_instance
  obtain ⟨ε, hεpos, hε⟩ :=
    Metric.exists_ball_inter_eq_singleton_of_mem_discrete
      (s := (NumberField.Units.unitLattice K :
        Set
          (NumberField.Units.dirichletUnitTheorem.logSpace K)))
      DiscreteTopology.isDiscrete
      (show
        (0 :
          NumberField.Units.dirichletUnitTheorem.logSpace K) ∈
        NumberField.Units.unitLattice K by simp)
  let δ : ℝ := min ε 1
  have hδpos : 0 < δ := lt_min hεpos zero_lt_one
  refine discreteTopology_iff_isOpen_singleton_zero.mpr
    ⟨Metric.ball 0 δ, Metric.isOpen_ball, ?_⟩
  ext z
  constructor
  · intro hz
    have hzlt : ‖(z : ReducedLogSpace (K := K) S)‖ < δ := by
      simpa [Metric.mem_ball, dist_eq_norm] using hz
    obtain ⟨x, hx⟩ := z.property
    have hxlog :
        reducedLog (K := K) S x =
          (z : ReducedLogSpace (K := K) S) := hx
    have hfin :
        (reducedLog (K := K) S x).2 = 0 := by
      apply norm_reducedLog_finite_lt_one_implies_zero
        (K := K) S
      rw [hxlog]
      exact hzlt.trans_le (min_le_right _ _)
    have hxdiv :
        x ∈ LinearMap.ker
          (divisorLinearMap (K := K) S) := by
      apply LinearMap.mem_ker.mpr
      ext v
      have hv := congrFun hfin v
      change
        divisorCoordinate (K := K) S
          (Additive.toMul x) v = 0
      have hvreal :
          (divisorCoordinate (K := K) S
            (Additive.toMul x) v : ℝ) = 0 := by
        simpa [reducedLog] using hv
      exact_mod_cast hvreal
    rw [← range_fromNumberFieldUnitsLinearMap_eq_ker_divisorLinearMap
      (K := K) S] at hxdiv
    obtain ⟨u, hu⟩ := hxdiv
    have hinf :
        NumberField.Units.logEmbedding K u =
          (z : ReducedLogSpace (K := K) S).1 := by
      rw [← hxlog, ← hu]
      simp [fromNumberFieldUnitsLinearMap]
    have hunitmem :
        NumberField.Units.logEmbedding K u ∈
          NumberField.Units.unitLattice K := by
      exact ⟨u, trivial, rfl⟩
    have hunitball :
        NumberField.Units.logEmbedding K u ∈
          Metric.ball 0 ε := by
      rw [Metric.mem_ball, dist_zero_right]
      rw [hinf]
      exact
        (norm_fst_le
          (z : ReducedLogSpace (K := K) S)).trans_lt
            (hzlt.trans_le (min_le_left _ _))
    have hunitzero :
        NumberField.Units.logEmbedding K u = 0 := by
      have :
          NumberField.Units.logEmbedding K u ∈
            Metric.ball 0 ε ∩
              (NumberField.Units.unitLattice K :
                Set
                  (NumberField.Units.dirichletUnitTheorem.logSpace K)) :=
        ⟨hunitball, hunitmem⟩
      rw [hε] at this
      exact this
    apply Subtype.ext
    rw [← hxlog]
    apply Prod.ext
    · rw [← hu]
      simpa [fromNumberFieldUnitsLinearMap] using hunitzero
    · exact hfin
  · intro hz
    have hz0 : z = 0 := by
      simpa using hz
    subst z
    simp [Metric.mem_ball, hδpos]

/-- The integral rank of the reduced logarithmic lattice is the
Dirichlet unit rank plus the number of finite places in `S`. -/
theorem finrank_reducedLogLattice :
    Module.finrank ℤ (reducedLogLattice (K := K) S) =
      NumberField.Units.rank K + S.card := by
  let f := reducedLogLinearMap (K := K) S
  calc
    Module.finrank ℤ (reducedLogLattice (K := K) S) =
        Module.finrank ℤ
          (Additive (SUnitGroup (K := K) S) ⧸
            LinearMap.ker f) :=
      f.quotKerEquivRange.symm.finrank_eq
    _ = Module.finrank ℤ
          (Additive (SUnitGroup (K := K) S) ⧸
            (AddCommGroup.torsion
              (Additive
                (SUnitGroup (K := K) S))).toIntSubmodule) := by
      rw [show LinearMap.ker f =
        (AddCommGroup.torsion
          (Additive
            (SUnitGroup (K := K) S))).toIntSubmodule from
          reducedLogLinearMap_ker (K := K) S]
    _ = Module.finrank ℤ
          (Additive (SUnitGroup (K := K) S)) := by
      exact finrank_quotient_torsion_eq
    _ = NumberField.Units.rank K + S.card :=
      finrank (K := K) S

/-- The reduced logarithmic lattice spans its whole real ambient
space. -/
theorem reducedLogLattice_span_eq_top :
    Submodule.span ℝ
      (reducedLogLattice (K := K) S :
        Set (ReducedLogSpace (K := K) S)) = ⊤ := by
  classical
  let :
      DiscreteTopology
        (Submodule.span ℤ
          (reducedLogLattice (K := K) S :
            Set (ReducedLogSpace (K := K) S))) := by
    rw [Submodule.span_eq]
    infer_instance
  apply Submodule.eq_top_of_finrank_eq
  change
    Set.finrank ℝ
      (reducedLogLattice (K := K) S :
        Set (ReducedLogSpace (K := K) S)) =
      Module.finrank ℝ (ReducedLogSpace (K := K) S)
  calc
    Set.finrank ℝ
        (reducedLogLattice (K := K) S :
          Set (ReducedLogSpace (K := K) S)) =
        Set.finrank ℤ
          (reducedLogLattice (K := K) S :
            Set (ReducedLogSpace (K := K) S)) :=
      Real.finrank_eq_int_finrank_of_discrete inferInstance
    _ = Module.finrank ℤ
          (reducedLogLattice (K := K) S) := by
      rw [Set.finrank, Submodule.span_eq]
    _ = NumberField.Units.rank K + S.card :=
      finrank_reducedLogLattice (K := K) S
    _ = Module.finrank ℝ
          (ReducedLogSpace (K := K) S) :=
      (finrank_reducedLogSpace (K := K) S).symm

/-- The reduced logarithmic image of the `S`-units is a complete
`ℤ`-lattice. -/
instance instIsZLattice_reducedLogLattice :
    IsZLattice ℝ (reducedLogLattice (K := K) S) where
  span_top := reducedLogLattice_span_eq_top (K := K) S

section FullLogarithmicSpace

instance instDiscreteTopology_fullLogLattice :
    DiscreteTopology (fullLogLattice (K := K) S) :=
  by
    change
      DiscreteTopology
        (ZLattice.comap ℝ
          (reducedLogLattice (K := K) S)
          (logHyperplaneContinuousEquivReduced
            (K := K) S).toLinearMap)
    infer_instance

/-- The image of the normalized all-place logarithmic embedding is a
complete `ℤ`-lattice in the coordinate-sum-zero hyperplane. -/
instance instIsZLattice_fullLogLattice :
    IsZLattice ℝ (fullLogLattice (K := K) S) :=
  by
    change
      IsZLattice ℝ
        (ZLattice.comap ℝ
          (reducedLogLattice (K := K) S)
          (logHyperplaneContinuousEquivReduced
            (K := K) S).toLinearMap)
    infer_instance

end FullLogarithmicSpace

section Decomposition

theorem torsionAdditive_eq :
    TorsionAdditive (K := K) S =
      (AddCommGroup.torsion
        (Additive
          (SUnitGroup (K := K) S))).toIntSubmodule := by
  apply Submodule.toAddSubgroup_injective
  rw [Submodule.torsion_int,
    AddSubgroup.toIntSubmodule_toAddSubgroup]

attribute [local instance] SUnitGroup.instModuleFinite_additiveSUnit
attribute [local instance] SUnitGroup.instModule_freeQuotient
local instance instModuleFinite_freeQuotient :
    Module.Finite ℤ (FreeQuotient (K := K) S) :=
  Module.Finite.quotient ℤ
    (TorsionAdditive (K := K) S)

local instance instModuleFree_freeQuotient :
    Module.Free ℤ (FreeQuotient (K := K) S) :=
  Module.free_of_finite_type_torsion_free'

/-- The free quotient has rank `#S - 1`, where `S` here includes all
infinite places. -/
theorem finrank_freeQuotient :
    Module.finrank ℤ (FreeQuotient (K := K) S) =
      logRank (K := K) S := by
  calc
    Module.finrank ℤ (FreeQuotient (K := K) S) =
        Module.finrank ℤ
          (Additive (SUnitGroup (K := K) S)) := by
      exact finrank_quotient_eq_of_le_torsion le_rfl
    _ = NumberField.Units.rank K + S.card :=
      finrank (K := K) S
    _ = logRank (K := K) S := by
      rw [NumberField.Units.rank]
      dsimp [logRank]
      have hpos :
          0 <
            Fintype.card
              (NumberField.InfinitePlace K) :=
        Fintype.card_pos
      omega

/-- A basis of the free quotient, indexed by its logarithmic rank. -/
noncomputable def basisFreeQuotient :
    Basis (Fin (logRank (K := K) S)) ℤ
      (FreeQuotient (K := K) S) :=
  Basis.reindex
    (Module.Free.chooseBasis ℤ
      (FreeQuotient (K := K) S))
    (Fintype.equivOfCardEq <| by
      rw [← Module.finrank_eq_card_chooseBasisIndex,
        finrank_freeQuotient (K := K) S,
        Fintype.card_fin])

/-- The ordinary roots of unity map linearly and bijectively onto the
torsion in the `S`-unit group. -/
noncomputable def rootsOfUnityEquivTorsion :
    RootsOfUnityAdditive (K := K) ≃ₗ[ℤ]
      TorsionAdditive (K := K) S := by
  let f :
      RootsOfUnityAdditive (K := K) →ₗ[ℤ]
        TorsionAdditive (K := K) S :=
    ((fromNumberFieldUnitsLinearMap (K := K) S).domRestrict
      (RootsOfUnityAdditive (K := K))).codRestrict
        (TorsionAdditive (K := K) S) fun u => by
          rw [torsionAdditive_eq (K := K) S]
          change
            Additive.toMul
                (fromNumberFieldUnitsLinearMap (K := K) S
                  (u :
                    Additive (𝓞 K)ˣ)) ∈
              CommGroup.torsion
                (SUnitGroup (K := K) S)
          rw [torsion_eq_rootsOfUnity_range (K := K) S]
          refine
            ⟨Additive.toMul
                (u : Additive (𝓞 K)ˣ), ?_, rfl⟩
          exact u.property
  apply LinearEquiv.ofBijective f
  constructor
  · intro x y hxy
    apply Subtype.ext
    apply fromNumberFieldUnitsLinearMap_injective
      (K := K) S
    exact congrArg Subtype.val hxy
  · intro y
    have hyadd :
        (y :
          Additive (SUnitGroup (K := K) S)) ∈
          AddCommGroup.torsion
            (Additive (SUnitGroup (K := K) S)) := by
      have hy' :
          (y :
            Additive (SUnitGroup (K := K) S)) ∈
            (AddCommGroup.torsion
              (Additive
                (SUnitGroup (K := K) S))).toIntSubmodule := by
        rw [← torsionAdditive_eq (K := K) S]
        exact y.property
      exact hy'
    have hy :
        Additive.toMul
            (y :
              Additive (SUnitGroup (K := K) S)) ∈
          CommGroup.torsion
            (SUnitGroup (K := K) S) :=
      hyadd
    rw [torsion_eq_rootsOfUnity_range (K := K) S] at hy
    obtain ⟨u, hu, huy⟩ := hy
    let x : RootsOfUnityAdditive (K := K) :=
      ⟨Additive.ofMul u, hu⟩
    refine ⟨x, ?_⟩
    apply Subtype.ext
    apply Additive.toMul.injective
    exact huy

/-- A linear section of the quotient by torsion.  It exists because
the quotient is a free, hence projective, `ℤ`-module. -/
noncomputable def torsionQuotientSection :
    FreeQuotient (K := K) S →ₗ[ℤ]
      Additive (SUnitGroup (K := K) S) :=
  (Module.projective_lifting_property
    (TorsionAdditive (K := K) S).mkQ
    LinearMap.id
    (TorsionAdditive (K := K) S).mkQ_surjective).choose

theorem torsionQuotientSection_spec :
    (TorsionAdditive (K := K) S).mkQ.comp
        (torsionQuotientSection (K := K) S) =
      LinearMap.id :=
  (Module.projective_lifting_property
    (TorsionAdditive (K := K) S).mkQ
    LinearMap.id
    (TorsionAdditive (K := K) S).mkQ_surjective).choose_spec

/-- Splitting the exact sequence consisting of torsion, the `S`-unit
group, and its torsion-free quotient. -/
noncomputable def torsionProdFreeQuotientEquiv :
    Additive (SUnitGroup (K := K) S) ≃ₗ[ℤ]
      TorsionAdditive (K := K) S ×
        FreeQuotient (K := K) S :=
  (lequivProdOfRightSplitExact
    (TorsionAdditive (K := K) S).injective_subtype
    (by
      rw [Submodule.range_subtype, Submodule.ker_mkQ])
    (torsionQuotientSection_spec (K := K) S)).symm

/-- **`S`-unit theorem, decomposition form.**  Additively, the
`S`-unit group is the product of the roots of unity and a free
`ℤ`-module of rank `#S - 1`. -/
noncomputable def decompositionLinearEquiv :
    Additive (SUnitGroup (K := K) S) ≃ₗ[ℤ]
      RootsOfUnityAdditive (K := K) ×
        (Fin (logRank (K := K) S) →₀ ℤ) :=
  (torsionProdFreeQuotientEquiv (K := K) S).trans
    ((rootsOfUnityEquivTorsion (K := K) S).symm.prodCongr
      (basisFreeQuotient (K := K) S).repr)

/-- **`S`-unit theorem, group form.**

Writing `S` for all infinite places together with the supplied finite
places, the `S`-unit group is `μ(K) × ℤ^(#S-1)`. -/
noncomputable def decomposition :
    SUnitGroup (K := K) S ≃*
      NumberField.Units.torsion K ×
        Multiplicative
          (Fin (logRank (K := K) S) →₀ ℤ) :=
  (AddEquiv.toMultiplicativeRight
      (decompositionLinearEquiv
        (K := K) S).toAddEquiv).trans
    (((MulEquiv.prodMultiplicative
        (RootsOfUnityAdditive (K := K))
        (Fin (logRank (K := K) S) →₀ ℤ)) :
        Multiplicative
            (RootsOfUnityAdditive (K := K) ×
              (Fin (logRank (K := K) S) →₀ ℤ)) ≃*
          Multiplicative (RootsOfUnityAdditive (K := K)) ×
            Multiplicative
              (Fin (logRank (K := K) S) →₀ ℤ)).trans
      ((multiplicativeRootsOfUnityEquiv
        (K := K)).prodCongr
          (MulEquiv.refl
            (Multiplicative
              (Fin (logRank (K := K) S) →₀ ℤ)))))

end Decomposition

end SUnitGroup
end
end

section
-- module Solutions.OAIQ244_DUKE.AlgebraicNumberTheory_SUnit_GaloisAction
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.DiscreteNthRootsSubgroup.instCommGroupSubtypeUnitsMemSubgroup _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.KummerTheory.nthRootsSubgroupFintype _root_.KummerTheory.primeCyclotomicBaseFiniteDimensional _root_.LocalFieldTheory.DiscreteValuationField.finite_nsmulAddKernel_padicInt_pi _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_multiplicative_nthPowerKernel _root_.LocalFieldTheory.finite_nsmulAddKernel_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.LubinTate.compatibleGroupFamiliesCommGroup _root_.LubinTate.compatibleGroupFamiliesGroup _root_.OAI.PrimeDegreePackets.ThetaConstruction.coordinateLattice_discrete _root_.OAI.PrimeDegreePackets.boundedRealFields_finite _root_.OAI.PrimeDegreePackets.diagonalLogAction _root_.OAI.PrimeDegreePackets.instNonemptyLeafTestSpace _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.integralGroup_discrete _root_.OAI.PrimeDegreePackets.logSubgroup_discrete _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.OAI.PrimeDegreePackets.orderedLogSubgroup_discrete _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionResidueField.instField _root_.RamificationTheory.HilbertRamification.ValuationSubring.selectedResidueField.instAlgebra _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.RelativeIdeleGroup.relativeIdeleMulAction _root_.ValuationTheory.DiscreteValuationField.DVF.maximalIdealPowSuccQuotModule _root_.ValuationTheory.DiscreteValuationField.DVF.residueField.field _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.isDomain _root_.CyclicCohomology.binaryCoefficientFamilyCommGroup _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.relativeAdeleRingIntermediateAlgebra _root_.relativeAdeleRingTopIntermediateAlgebra
attribute [-simp] _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.IsDiscreteValuationRing.addVal_ringEquiv _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.KummerTheory.mem_sUnitFiniteKummerRadical_iff _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.LocalFieldTheory.residueField_algebraMap_residue _root_.OAI.PrimeDegreePackets.ThetaConstruction.schwartzCM_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

/-!
# Galois actions on `S`-units and their logarithmic lattice

This file supplies the equivariant input for the `S`-unit calculation. A Galois
automorphism acts on finite places through its restriction to the ring of
integers, on infinite places by precomposition, and on field units in the
usual way.  For a stable finite set of finite places these actions restrict
to the actual `S`-unit group.
-/

open scoped BigOperators Classical NumberField nonZeroDivisors
open IsDedekindDomain Module
open CyclicCohomology.ProfiniteCohomology.Herbrand
open CyclicCohomology

noncomputable section

variable
    (K L : Type*) [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]

omit [NumberField K] in
/-- The normalized finite absolute value is invariant under simultaneous
transport of its finite place and its field element. -/
theorem adicAbv_finitePlaceEquiv
    (σ : L ≃ₐ[K] L)
    (v : HeightOneSpectrum (𝓞 L))
    (x : L) :
    NumberField.HeightOneSpectrum.adicAbv L
        (finitePlaceEquiv K L σ v) (σ x) =
      NumberField.HeightOneSpectrum.adicAbv L v x := by
  rw [NumberField.HeightOneSpectrum.adicAbv_def,
    NumberField.HeightOneSpectrum.adicAbv_def,
    valuation_finitePlaceEquiv]
  have hnorm :
      Ideal.absNorm (finitePlaceEquiv K L σ v).asIdeal =
        Ideal.absNorm v.asIdeal := by
    rw [finitePlaceEquiv_asIdeal, absNorm_map_ringEquiv]
  have hnorm_nnreal :
      (Ideal.absNorm
          (finitePlaceEquiv K L σ v).asIdeal : NNReal) =
        (Ideal.absNorm v.asIdeal : NNReal) := by
    exact_mod_cast hnorm
  exact toNNReal_apply_congr
    (NumberField.HeightOneSpectrum.absNorm_ne_zero
      (finitePlaceEquiv K L σ v))
    (NumberField.HeightOneSpectrum.absNorm_ne_zero v)
    hnorm_nnreal (v.valuation L x)

section FinitePlaceAction

attribute [local instance] instMulActionAlgEquivHeightOneSpectrumRingOfIntegers_solutions
/-- The contragredient coordinate-permutation action on the full
logarithmic coordinate space. -/
@[reducible]
noncomputable def fullLogSpaceDistribMulAction
    (S : Finset (HeightOneSpectrum (𝓞 L)))
    (hS : IsGaloisStableFinitePlaces K L S) :
    DistribMulAction (L ≃ₐ[K] L)
      (SUnitGroup.FullLogSpace (K := L) S) := by
  letI := logPlaceMulAction K L S hS
  exact
    { smul := fun σ z p => z (σ⁻¹ • p)
      one_smul := by
        intro z
        funext p
        change z ((1 : L ≃ₐ[K] L)⁻¹ • p) = z p
        rw [inv_one, one_smul]
      mul_smul := by
        intro σ τ z
        funext p
        change z ((σ * τ)⁻¹ • p) =
          z (τ⁻¹ • (σ⁻¹ • p))
        rw [mul_inv_rev, mul_smul]
      smul_zero := by
        intro σ
        rfl
      smul_add := by
        intro σ z z'
        rfl }

omit [NumberField K] [NumberField L] in
@[simp]
theorem fullLogSpace_smul_apply
    {S : Finset (HeightOneSpectrum (𝓞 L))}
    (hS : IsGaloisStableFinitePlaces K L S)
    (σ : L ≃ₐ[K] L)
    (z : SUnitGroup.FullLogSpace (K := L) S)
    (p : SUnitGroup.LogPlace (K := L) S) :
    letI := logPlaceMulAction K L S hS
    letI := fullLogSpaceDistribMulAction K L S hS
    (σ • z) p = z (σ⁻¹ • p) :=
  rfl

/-- The permutation representation on the set of logarithmic places. -/
noncomputable def logPlacePermutationHom
    (S : Finset (HeightOneSpectrum (𝓞 L)))
    (hS : IsGaloisStableFinitePlaces K L S) :
    (L ≃ₐ[K] L) →*
      Equiv.Perm (SUnitGroup.LogPlace (K := L) S) := by
  letI := logPlaceMulAction K L S hS
  exact MulAction.toPermHom
    (L ≃ₐ[K] L) (SUnitGroup.LogPlace (K := L) S)

omit [NumberField K] [NumberField L] in
@[simp]
theorem logPlacePermutationHom_apply
    {S : Finset (HeightOneSpectrum (𝓞 L))}
    (hS : IsGaloisStableFinitePlaces K L S)
    (σ : L ≃ₐ[K] L)
    (p : SUnitGroup.LogPlace (K := L) S) :
    letI := logPlaceMulAction K L S hS
    logPlacePermutationHom K L S hS σ p = σ • p :=
  rfl

omit [NumberField K] [NumberField L] in
/-- The concrete contragredient action is the coordinate permutation
representation associated to the action on logarithmic places. -/
theorem permutationRepresentation_logPlace
    {S : Finset (HeightOneSpectrum (𝓞 L))}
    (hS : IsGaloisStableFinitePlaces K L S)
    (σ : L ≃ₐ[K] L)
    (z : SUnitGroup.FullLogSpace (K := L) S) :
    letI := logPlaceMulAction K L S hS
    letI := fullLogSpaceDistribMulAction K L S hS
    permutationRepresentation
        (logPlacePermutationHom K L S hS) σ z =
      σ • z := by
  let := logPlaceMulAction K L S hS
  let := fullLogSpaceDistribMulAction K L S hS
  ext p
  rfl

omit [NumberField K] in
/-- Coordinate sum is invariant under the place permutation. -/
theorem coordinateSum_smul
    {S : Finset (HeightOneSpectrum (𝓞 L))}
    (hS : IsGaloisStableFinitePlaces K L S)
    (σ : L ≃ₐ[K] L)
    (z : SUnitGroup.FullLogSpace (K := L) S) :
    letI := logPlaceMulAction K L S hS
    letI := fullLogSpaceDistribMulAction K L S hS
    SUnitGroup.coordinateSum (K := L) S (σ • z) =
      SUnitGroup.coordinateSum (K := L) S z := by
  let := logPlaceMulAction K L S hS
  let := fullLogSpaceDistribMulAction K L S hS
  change
    (∑ p : SUnitGroup.LogPlace (K := L) S,
      z (σ⁻¹ • p)) = ∑ p, z p
  exact
    Fintype.sum_equiv (MulAction.toPerm σ⁻¹)
      (fun p : SUnitGroup.LogPlace (K := L) S =>
        z (σ⁻¹ • p))
      z (fun _ => rfl)

/-- The constant vector whose coordinate sum is one. -/
noncomputable def normalizedLogDiagonal
    (S : Finset (HeightOneSpectrum (𝓞 L))) :
    SUnitGroup.FullLogSpace (K := L) S :=
  fun _ =>
    (Fintype.card
      (SUnitGroup.LogPlace (K := L) S) : ℝ)⁻¹

@[simp]
theorem coordinateSum_normalizedLogDiagonal
    (S : Finset (HeightOneSpectrum (𝓞 L))) :
    SUnitGroup.coordinateSum (K := L) S
        (normalizedLogDiagonal L S) = 1 := by
  change
    (∑ _ : SUnitGroup.LogPlace (K := L) S,
      (Fintype.card
        (SUnitGroup.LogPlace (K := L) S) : ℝ)⁻¹) = 1
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  exact mul_inv_cancel₀
    (by exact_mod_cast
      (Fintype.card_ne_zero :
        Fintype.card (SUnitGroup.LogPlace (K := L) S) ≠ 0))

/-- A real basis of the logarithmic hyperplane obtained from an
integral basis of the complete logarithmic lattice. -/
noncomputable def fullLogLatticeRealBasis
    (S : Finset (HeightOneSpectrum (𝓞 L))) :
    Basis
      (Module.Free.ChooseBasisIndex ℤ
        (SUnitGroup.fullLogLattice (K := L) S))
      ℝ (SUnitGroup.LogHyperplane (K := L) S) :=
  (Module.Free.chooseBasis ℤ
      (SUnitGroup.fullLogLattice (K := L) S)).ofZLatticeBasis
        ℝ (SUnitGroup.fullLogLattice (K := L) S)

/-- A basis of the product of the logarithmic hyperplane with the
one-dimensional diagonal direction. -/
noncomputable def fullLogHyperplaneDiagonalBasis
    (S : Finset (HeightOneSpectrum (𝓞 L))) :
    Basis
      (Module.Free.ChooseBasisIndex ℤ
          (SUnitGroup.fullLogLattice (K := L) S) ⊕ Unit)
      ℝ (SUnitGroup.LogHyperplane (K := L) S × ℝ) :=
  (fullLogLatticeRealBasis L S).prod (Basis.singleton Unit ℝ)

/-- The product lattice formed from the logarithmic lattice and one
integral diagonal direction. -/
noncomputable def fullLogHyperplaneDiagonalLattice
    (S : Finset (HeightOneSpectrum (𝓞 L))) :
    Submodule ℤ
      (SUnitGroup.LogHyperplane (K := L) S × ℝ) :=
  Submodule.span ℤ
    (Set.range (fullLogHyperplaneDiagonalBasis L S))

omit [NumberField K] in
/-- The normalized all-place logarithm is equivariant for the actual
`S`-unit and place-permutation actions. -/
theorem fullLogAmbient_smul
    {S : Finset (HeightOneSpectrum (𝓞 L))}
    (hS : IsGaloisStableFinitePlaces K L S)
    (σ : L ≃ₐ[K] L)
    (x : Additive (SUnitGroup (K := L) S)) :
    letI := sUnitMulDistribMulAction K L S hS
    letI := additiveSUnitDistribMulAction K L S hS
    letI := logPlaceMulAction K L S hS
    letI := fullLogSpaceDistribMulAction K L S hS
    SUnitGroup.fullLogAmbient (K := L) S (σ • x) =
      σ • SUnitGroup.fullLogAmbient (K := L) S x := by
  let := sUnitMulDistribMulAction K L S hS
  let := additiveSUnitDistribMulAction K L S hS
  let := logPlaceMulAction K L S hS
  let := fullLogSpaceDistribMulAction K L S hS
  let y : L :=
    (((Additive.toMul x :
      SUnitGroup (K := L) S) : Lˣ) : L)
  funext p
  cases p with
  | inl w =>
      change
        w.mult *
            Real.log (w (σ y)) =
          (σ⁻¹ • w).mult *
            Real.log ((σ⁻¹ • w) y)
      rw [infinitePlace_mult_smul]
      rfl
  | inr v =>
      change
        Real.log
            (NumberField.HeightOneSpectrum.adicAbv L
              (v : HeightOneSpectrum (𝓞 L))
              (σ y)) =
          Real.log
            (NumberField.HeightOneSpectrum.adicAbv L
              (finitePlaceEquiv K L σ⁻¹
                (v : HeightOneSpectrum (𝓞 L)))
              y)
      congr 1
      have h :=
        adicAbv_finitePlaceEquiv K L σ
          (finitePlaceEquiv K L σ⁻¹
            (v : HeightOneSpectrum (𝓞 L)))
          y
      simpa using h

/-- The coordinate-permutation action restricted to the
coordinate-sum-zero hyperplane. -/
@[reducible]
noncomputable def logHyperplaneDistribMulAction
    (S : Finset (HeightOneSpectrum (𝓞 L)))
    (hS : IsGaloisStableFinitePlaces K L S) :
    DistribMulAction (L ≃ₐ[K] L)
      (SUnitGroup.LogHyperplane (K := L) S) := by
  letI := logPlaceMulAction K L S hS
  letI := fullLogSpaceDistribMulAction K L S hS
  exact
    { smul := fun σ z =>
        ⟨σ • (z :
            SUnitGroup.FullLogSpace (K := L) S), by
          apply LinearMap.mem_ker.mpr
          rw [coordinateSum_smul K L hS]
          exact LinearMap.mem_ker.mp z.property⟩
      one_smul := by
        intro z
        apply Subtype.ext
        exact one_smul (L ≃ₐ[K] L)
          (z : SUnitGroup.FullLogSpace (K := L) S)
      mul_smul := by
        intro σ τ z
        apply Subtype.ext
        exact mul_smul σ τ
          (z : SUnitGroup.FullLogSpace (K := L) S)
      smul_zero := by
        intro σ
        apply Subtype.ext
        exact DistribMulAction.smul_zero σ
      smul_add := by
        intro σ z z'
        apply Subtype.ext
        exact DistribMulAction.smul_add σ
          (z : SUnitGroup.FullLogSpace (K := L) S)
          (z' : SUnitGroup.FullLogSpace (K := L) S) }

omit [NumberField K] in
/-- Equivariance of the logarithmic map after restricting its codomain
to the coordinate-sum-zero hyperplane. -/
theorem fullLog_smul
    {S : Finset (HeightOneSpectrum (𝓞 L))}
    (hS : IsGaloisStableFinitePlaces K L S)
    (σ : L ≃ₐ[K] L)
    (x : Additive (SUnitGroup (K := L) S)) :
    letI := sUnitMulDistribMulAction K L S hS
    letI := additiveSUnitDistribMulAction K L S hS
    letI := logPlaceMulAction K L S hS
    letI := fullLogSpaceDistribMulAction K L S hS
    letI := logHyperplaneDistribMulAction K L S hS
    SUnitGroup.fullLog (K := L) S (σ • x) =
      σ • SUnitGroup.fullLog (K := L) S x := by
  let := sUnitMulDistribMulAction K L S hS
  let := additiveSUnitDistribMulAction K L S hS
  let := logPlaceMulAction K L S hS
  let := fullLogSpaceDistribMulAction K L S hS
  let := logHyperplaneDistribMulAction K L S hS
  apply Subtype.ext
  exact fullLogAmbient_smul K L hS σ x

omit [NumberField K] in
/-- The complete logarithmic lattice is stable under the concrete
Galois action. -/
theorem fullLogLattice_smul_mem
    {S : Finset (HeightOneSpectrum (𝓞 L))}
    (hS : IsGaloisStableFinitePlaces K L S)
    (σ : L ≃ₐ[K] L)
    (z : SUnitGroup.LogHyperplane (K := L) S)
    (hz : z ∈ SUnitGroup.fullLogLattice (K := L) S) :
    letI := sUnitMulDistribMulAction K L S hS
    letI := additiveSUnitDistribMulAction K L S hS
    letI := logPlaceMulAction K L S hS
    letI := fullLogSpaceDistribMulAction K L S hS
    letI := logHyperplaneDistribMulAction K L S hS
    σ • z ∈ SUnitGroup.fullLogLattice (K := L) S := by
  let := sUnitMulDistribMulAction K L S hS
  let := additiveSUnitDistribMulAction K L S hS
  let := logPlaceMulAction K L S hS
  let := fullLogSpaceDistribMulAction K L S hS
  let := logHyperplaneDistribMulAction K L S hS
  rw [SUnitGroup.fullLogLattice_eq_range] at hz ⊢
  obtain ⟨x, hx⟩ := hz
  change SUnitGroup.fullLog (K := L) S x = z at hx
  refine ⟨σ • x, ?_⟩
  change
    SUnitGroup.fullLog (K := L) S (σ • x) = σ • z
  rw [fullLog_smul K L hS, hx]

end FinitePlaceAction
end
end

section
-- module Solutions.OAIQ244_DUKE.AlgebraicNumberTheory_SUnit_Herbrand
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.PrimeDegreePackets.diagonalLogAction _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable
attribute [-simp] _root_.IsDiscreteValuationRing.addVal_ringEquiv _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.OAI.PrimeDegreePackets.ThetaConstruction.schwartzCM_apply
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

section LogarithmicQuotient

/-- The additive Galois action restricted to the actual full
logarithmic lattice. -/
@[reducible]
noncomputable def fullLogLatticeDistribMulAction
    (S : Finset (HeightOneSpectrum (𝓞 L)))
    (hS : IsGaloisStableFinitePlaces K L S) :
    DistribMulAction (L ≃ₐ[K] L)
      (SUnitGroup.fullLogLattice (K := L) S) := by
  letI := sUnitMulDistribMulAction K L S hS
  letI := additiveSUnitDistribMulAction K L S hS
  letI := logPlaceMulAction K L S hS
  letI := fullLogSpaceDistribMulAction K L S hS
  letI := logHyperplaneDistribMulAction K L S hS
  exact
    { smul := fun σ z =>
        ⟨σ • (z :
            SUnitGroup.LogHyperplane (K := L) S),
          fullLogLattice_smul_mem K L hS
            σ z.1 z.2⟩
      one_smul := by
        intro z
        apply Subtype.ext
        exact one_smul (L ≃ₐ[K] L)
          (z : SUnitGroup.LogHyperplane (K := L) S)
      mul_smul := by
        intro σ τ z
        apply Subtype.ext
        exact mul_smul σ τ
          (z : SUnitGroup.LogHyperplane (K := L) S)
      smul_zero := by
        intro σ
        apply Subtype.ext
        exact DistribMulAction.smul_zero σ
      smul_add := by
        intro σ z z'
        apply Subtype.ext
        exact DistribMulAction.smul_add σ
          (z : SUnitGroup.LogHyperplane (K := L) S)
          (z' : SUnitGroup.LogHyperplane (K := L) S) }

end LogarithmicQuotient

section DiagonalExtension

/-- The componentwise action on the logarithmic lattice paired with
the invariant integer diagonal. -/
@[reducible]
noncomputable def fullLogLatticeProdIntDistribMulAction
    (S : Finset (HeightOneSpectrum (𝓞 L)))
    (hS : IsGaloisStableFinitePlaces K L S) :
    DistribMulAction (L ≃ₐ[K] L)
      (SUnitGroup.fullLogLattice (K := L) S × ℤ) := by
  letI :=
    fullLogLatticeDistribMulAction K L S hS
  exact
    { smul := fun σ z => (σ • z.1, z.2)
      one_smul := by
        intro z
        apply Prod.ext
        · exact one_smul (L ≃ₐ[K] L) z.1
        · rfl
      mul_smul := by
        intro σ τ z
        apply Prod.ext
        · exact mul_smul σ τ z.1
        · rfl
      smul_zero := by
        intro σ
        apply Prod.ext
        · exact DistribMulAction.smul_zero σ
        · rfl
      smul_add := by
        intro σ z z'
        apply Prod.ext
        · exact DistribMulAction.smul_add σ z.1 z'.1
        · rfl }

end DiagonalExtension

section LocalDegreeInterpretation

/-- Passing to a stable finite set does not change the stabilizer or
the finite local degree of one of its places. -/
theorem stableFinitePlace_stabilizer_card_eq_localDegree
    [IsGalois K L]
    {S : Finset (HeightOneSpectrum (𝓞 L))}
    (hS : IsGaloisStableFinitePlaces K L S)
    (v : S) :
    letI _stableAction :=
      stableFinitePlaceMulAction K L S hS
    Nat.card
        (MulAction.stabilizer (L ≃ₐ[K] L) v) =
      finiteLogPlaceLocalDegree K L v := by
  let stableAction :=
    stableFinitePlaceMulAction K L S hS
  let finitePlaceAction :=
    finitePlaceMulAction K L
  rw [show
    MulAction.stabilizer (L ≃ₐ[K] L) v =
        MulAction.stabilizer
          (L ≃ₐ[K] L)
          (v : HeightOneSpectrum (𝓞 L)) by
      ext σ
      simp only [MulAction.mem_stabilizer_iff]
      change
        (⟨finitePlaceEquiv K L σ v, _⟩ : S) = v ↔
          finitePlaceEquiv K L σ v = v
      exact Subtype.ext_iff]
  exact
    finitePlace_stabilizer_card_eq_localDegree
      K L v

/-- The local degree attached to a logarithmic place.  At an
archimedean place it is `1` or `2`; at a finite place it is
`e(P/p) f(P/p)`. -/
noncomputable def logPlaceLocalDegree
    (S : Finset (HeightOneSpectrum (𝓞 L)))
    (q : SUnitGroup.LogPlace (K := L) S) : ℕ :=
  match q with
  | Sum.inl w =>
      if NumberField.InfinitePlace.IsUnramified K w
      then 1 else 2
  | Sum.inr v =>
      finiteLogPlaceLocalDegree K L v

/-- For every actual logarithmic place, the order of its Galois
stabilizer is its local degree. -/
theorem logPlace_stabilizer_card_eq_localDegree
    [IsGalois K L]
    {S : Finset (HeightOneSpectrum (𝓞 L))}
    (hS : IsGaloisStableFinitePlaces K L S)
    (q : SUnitGroup.LogPlace (K := L) S) :
    letI _logPlaceAction :=
      logPlaceMulAction K L S hS
    Nat.card
        (MulAction.stabilizer (L ≃ₐ[K] L) q) =
      logPlaceLocalDegree K L S q := by
  let stableAction :=
    stableFinitePlaceMulAction K L S hS
  let logPlaceAction :=
    logPlaceMulAction K L S hS
  cases q with
  | inl w =>
      unfold logPlaceLocalDegree
      rw [show
        MulAction.stabilizer
              (L ≃ₐ[K] L)
              (Sum.inl w :
                SUnitGroup.LogPlace (K := L) S) =
            MulAction.stabilizer (L ≃ₐ[K] L) w by
          ext σ
          simp only [MulAction.mem_stabilizer_iff]
          change Sum.inl (σ • w) = Sum.inl w ↔
            σ • w = w
          simp]
      exact
        NumberField.InfinitePlace.card_stabilizer
  | inr v =>
      unfold logPlaceLocalDegree
      rw [show
        MulAction.stabilizer
              (L ≃ₐ[K] L)
              (Sum.inr v :
                SUnitGroup.LogPlace (K := L) S) =
            MulAction.stabilizer (L ≃ₐ[K] L) v by
          ext σ
          simp only [MulAction.mem_stabilizer_iff]
          change Sum.inr (σ • v) = Sum.inr v ↔
            σ • v = v
          simp]
      exact
        stableFinitePlace_stabilizer_card_eq_localDegree
          K L hS v

/-- The canonical representative of every logarithmic-place orbit has
stabilizer order equal to its local degree. -/
theorem permutationOrbitStabilizer_card_eq_logPlaceLocalDegree
    [IsGalois K L]
    {S : Finset (HeightOneSpectrum (𝓞 L))}
    (hS : IsGaloisStableFinitePlaces K L S) :
    let ρ :=
      logPlacePermutationHom K L S hS
    letI _indexAction :
        MulAction (L ≃ₐ[K] L)
          (SUnitGroup.LogPlace (K := L) S) :=
      permutationMulAction ρ
    ∀ ω :
        MulAction.orbitRel.Quotient
          (L ≃ₐ[K] L)
          (SUnitGroup.LogPlace (K := L) S),
      Nat.card (permutationOrbitStabilizer ω) =
        logPlaceLocalDegree K L S ω.out := by
  dsimp only
  intro ω
  exact
    logPlace_stabilizer_card_eq_localDegree
      K L hS ω.out

end LocalDegreeInterpretation
end
end

section
-- module Solutions.OAIQ244_DUKE.Kummer_Concrete_RadicalExtension
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.KummerTheory.finiteSupportKummerQuotient_commGroupInstance _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.PrimeDegreePackets.diagonalLogAction _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionResidueField.instField _root_.RamificationTheory.HilbertRamification.ValuationSubring.selectedResidueField.instAlgebra _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.RelativeIdeleGroup.relativeIdeleMulAction _root_.ValuationTheory.DiscreteValuationField.DVF.maximalIdealPowSuccQuotModule _root_.ValuationTheory.DiscreteValuationField.DVF.residueField.field _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.isDomain _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.isLocalRing _root_.CyclicCohomology.instMulDistribMulActionBinaryCoefficientFamily _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen _root_.relativeAdeleRingIntermediateAlgebra _root_.relativeAdeleRingTopIntermediateAlgebra
attribute [-simp] _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.IsDiscreteValuationRing.addVal_ringEquiv _root_.KummerTheory.chosenSimpleKummerRootCharacter_apply _root_.KummerTheory.finiteSupportKummerQuotientLift_mk _root_.KummerTheory.finiteSupportKummerQuotientMk_eq_iff _root_.KummerTheory.finiteSupportKummerQuotientMk_eq_one_iff _root_.KummerTheory.infiniteKummerRootCharacter_apply _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.LocalFieldTheory.residueField_algebraMap_residue _root_.OAI.PrimeDegreePackets.ThetaConstruction.schwartzCM_apply _root_.infinitePlace_mult_smul
set_option synthInstance.maxHeartbeats 400000
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

/-!
# the radical-extension construction

Let `Delta` be a subgroup of `Kˣ`.  Inside a fixed separable closure `Omega/K`,
we adjoin *all* roots `beta` of the equations `beta ^ n = a`, for `a ∈ Delta`.
Using all roots makes the construction independent of choices and visibly
stable under `Gal(Omega/K)`.

The hypothesis `(n : K) ≠ 0` is the usual assumption that `n` is prime to
the characteristic.  It is used exactly to make `X ^ n - a` separable.  The
primitive-root hypothesis is used later to make the resulting Galois group
abelian of exponent dividing `n`.
-/

noncomputable section

namespace KummerTheory

section RadicalExtension

open Polynomial

variable {K Omega : Type*} [Field K] [Field Omega] [Algebra K Omega]

/-- Every element of `Delta` acquires an `n`-th root in the constructed
field.  This is the elementary inclusion `Delta ≤ Delta_{K(√[n]{Delta})}`
in the Kummer correspondence. -/
theorem le_finiteKummerRadicalSubgroup_kummerRadicalExtension
    [IsSepClosure K Omega]
    (n : ℕ+) (hn : ((n : ℕ) : K) ≠ 0) (Delta : Subgroup Kˣ) :
    Delta ≤ finiteKummerRadicalSubgroup
      (K := K) (L := kummerRadicalExtension (K := K) (Omega := Omega) n Delta) n := by
  intro a ha
  let aDelta : Delta := ⟨a, ha⟩
  obtain ⟨beta, hbeta, hpow⟩ :=
    exists_kummerRootSet (K := K) (Omega := Omega) n hn Delta aDelta
  let E := kummerRadicalExtension (K := K) (Omega := Omega) n Delta
  let betaE : E :=
    ⟨beta, IntermediateField.subset_adjoin K
      (kummerRootSet (K := K) (Omega := Omega) n Delta) hbeta⟩
  have hbetaE : betaE ≠ 0 := by
    intro hzero
    have hbeta_zero : beta = 0 := congrArg Subtype.val hzero
    have hmap_zero : algebraMap K Omega (a : K) = 0 := by
      rw [← hpow, hbeta_zero, zero_pow n.ne_zero]
    exact ((_root_.map_ne_zero (algebraMap K Omega)).2 a.ne_zero) hmap_zero
  refine ⟨Units.mk0 betaE hbetaE, ?_⟩
  apply Units.ext
  apply Subtype.ext
  exact hpow

/-- On every radical generator, the `n`-th power of an automorphism is the
identity. -/
theorem kummerRadicalExtension_generator_pow_eq_one
    [IsSepClosure K Omega]
    (n : ℕ+) (hmu : (primitiveRoots (n : ℕ) K).Nonempty)
    (Delta : Subgroup Kˣ)
    (sigma : Gal(kummerRadicalExtension (K := K) (Omega := Omega) n Delta/K))
    {beta : Omega}
    (hbeta : beta ∈ kummerRootSet (K := K) (Omega := Omega) n Delta) :
    (sigma ^ (n : ℕ))
        ⟨beta, IntermediateField.subset_adjoin K
          (kummerRootSet (K := K) (Omega := Omega) n Delta) hbeta⟩ =
      ⟨beta, IntermediateField.subset_adjoin K
        (kummerRootSet (K := K) (Omega := Omega) n Delta) hbeta⟩ := by
  let E := kummerRadicalExtension (K := K) (Omega := Omega) n Delta
  let betaE : E :=
    ⟨beta, IntermediateField.subset_adjoin K
      (kummerRootSet (K := K) (Omega := Omega) n Delta) hbeta⟩
  let betaUnit : Eˣ := Units.mk0 betaE (by
    intro hzero
    apply kummerRootSet_ne_zero n Delta hbeta
    exact congrArg Subtype.val hzero)
  obtain ⟨a, ha⟩ := hbeta
  have hpow : betaUnit ^ (n : ℕ) =
      Units.map (algebraMap K E).toMonoidHom a.1 := by
    apply Units.ext
    apply Subtype.ext
    exact ha
  have hpow_fixed : ∀ rho : Gal(E/K),
      rho • (betaUnit ^ (n : ℕ)) = betaUnit ^ (n : ℕ) := by
    intro rho
    rw [hpow]
    exact RadicalDatum.smul_algebraMap_unit (K := K) (L := E) rho a.1
  let hbase : NthRootsOfUnityInBase (K := K) (L := E) n :=
    nthRootsOfUnityInBase_of_primitiveRoots (K := K) (L := E) n hmu
  let q : Eˣ := rootQuotient (K := K) (L := E) betaUnit sigma
  have hq_pow : q ^ (n : ℕ) = 1 :=
    rootQuotient_pow_eq_one_of_pow_fixed (K := K) (L := E) hpow_fixed sigma
  have hq_fixed (rho : Gal(E/K)) : rho • q = q :=
    nthRootsOfUnity_fixed (K := K) (L := E) n hbase rho q hq_pow
  have hquot_pow : ∀ m : ℕ,
      rootQuotient (K := K) (L := E) betaUnit (sigma ^ m) = q ^ m := by
    intro m
    induction m with
    | zero => simp [q]
    | succ m ih =>
        rw [pow_succ, rootQuotient_mul, hq_fixed, ih]
        exact (pow_succ' q m).symm
  have hquot_one :
      rootQuotient (K := K) (L := E) betaUnit (sigma ^ (n : ℕ)) = 1 := by
    rw [hquot_pow, hq_pow]
  have hunit_fixed : (sigma ^ (n : ℕ)) • betaUnit = betaUnit :=
    (rootQuotient_eq_one_iff (K := K) (L := E) betaUnit
      (sigma ^ (n : ℕ))).1 hquot_one
  exact congrArg Units.val hunit_fixed

/-- Every element of the Galois group has `n`-th power one. -/
theorem kummerRadicalExtension_galois_pow_eq_one
    [IsSepClosure K Omega]
    (n : ℕ+) (hmu : (primitiveRoots (n : ℕ) K).Nonempty)
    (Delta : Subgroup Kˣ)
    (sigma : Gal(kummerRadicalExtension (K := K) (Omega := Omega) n Delta/K)) :
    sigma ^ (n : ℕ) = 1 := by
  apply AlgEquiv.coe_toAlgHom_injective
  apply IntermediateField.adjoin_algHom_ext K
  intro beta hbeta
  exact kummerRadicalExtension_generator_pow_eq_one n hmu Delta sigma hbeta

end RadicalExtension

end KummerTheory
end
end

section
-- module Solutions.OAIQ244_DUKE.Kummer_Concrete_InfiniteContinuity
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.KummerTheory.primeCyclotomicBaseFiniteDimensional _root_.LocalClassFieldTheory.finiteGaloisFieldRangeOfEmbedding_finiteDimensional _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.LubinTate.compatibleGroupFamiliesGroup _root_.OAI.PrimeDegreePackets.boundedRealFields_finite _root_.OAI.PrimeDegreePackets.diagonalLogAction _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.RelativeIdeleGroup.relativeIdeleMulAction _root_.CyclicCohomology.instMulDistribMulActionBinaryCoefficientFamily _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteIdeleGroupIsTopologicalGroup _root_.finiteLocalUnitsOpen _root_.ideleGroupIsTopologicalGroup
attribute [-simp] _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.IsDiscreteValuationRing.addVal_ringEquiv _root_.KummerTheory.chosenFiniteKummerRadicalRepresentative_spec _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.LocalFieldTheory.residueField_algebraMap_residue _root_.OAI.PrimeDegreePackets.ThetaConstruction.schwartzCM_apply _root_.infinitePlace_mult_smul
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

/-!
# continuity of Kummer characters for infinite extensions

For an infinite Galois extension `Ω/K`, a Kummer character attached to a
chosen root `β` is already determined on the finite Galois normal closure of
`K(β)`.  Equivalently, its kernel contains the fixing subgroup of that finite
Galois intermediate field.  This makes the kernel open in the Krull topology
and proves continuity into the discrete group of `n`-th roots of unity.

The final construction descends these continuous characters through the
ambient-power quotient `Δ / (Δ ∩ Kˣⁿ)`.  No surjectivity or lattice correspondence is
asserted here.
-/

noncomputable section

namespace KummerTheory

open scoped Topology
open Filter

section InfiniteKummerContinuity

variable {K Ω : Type*} [Field K] [Field Ω] [Algebra K Ω]

variable [IsGalois K Ω]

/-- The fixing subgroup of the finite Galois normal closure of the chosen
root lies in the kernel of its Kummer character. -/
theorem fixingSubgroup_adjoin_root_le_infiniteKummerRootCharacter_ker
    (n : ℕ+) (hmu : NthRootsOfUnityInBase (K := K) (L := Ω) n)
    (a : (chosenFiniteKummerRadicalDatum (K := K) (L := Ω) n).carrier) :
    (FiniteGaloisIntermediateField.adjoin K
      {((chosenFiniteKummerRadicalDatum (K := K) (L := Ω) n).root a : Ω)}).fixingSubgroup ≤
        MonoidHom.ker (infiniteKummerRootCharacter n hmu a) := by
  let D := chosenFiniteKummerRadicalDatum (K := K) (L := Ω) n
  let E := FiniteGaloisIntermediateField.adjoin K {(D.root a : Ω)}
  intro σ hσ
  rw [MonoidHom.mem_ker]
  apply Subtype.ext
  change D.rootCharacter a
      (nthRootsOfUnity_fixed (K := K) (L := Ω) n hmu) σ = 1
  rw [D.rootCharacter_apply]
  apply (rootQuotient_eq_one_iff (K := K) (L := Ω) (D.root a) σ).2
  apply Units.ext
  exact ((IntermediateField.mem_fixingSubgroup_iff E.toIntermediateField σ).mp hσ)
    (D.root a : Ω)
    (FiniteGaloisIntermediateField.subset_adjoin K {(D.root a : Ω)}
      (Set.mem_singleton (D.root a : Ω)))

/-- The kernel of an infinite Kummer root character is open in the Krull
topology. -/
theorem infiniteKummerRootCharacter_isOpen_ker
    (n : ℕ+) (hmu : NthRootsOfUnityInBase (K := K) (L := Ω) n)
    (a : (chosenFiniteKummerRadicalDatum (K := K) (L := Ω) n).carrier) :
    IsOpen (MonoidHom.ker (infiniteKummerRootCharacter n hmu a) :
      Set Gal(Ω/K)) := by
  exact Subgroup.isOpen_mono
    (fixingSubgroup_adjoin_root_le_infiniteKummerRootCharacter_ker n hmu a)
    (IntermediateField.fixingSubgroup_isOpen
      (FiniteGaloisIntermediateField.adjoin K
        {((chosenFiniteKummerRadicalDatum (K := K) (L := Ω) n).root a : Ω)}).toIntermediateField)

/-- Every Kummer root character for an infinite actual-field Galois extension
is continuous into the discrete group `μₙ(Ω)`. -/
theorem infiniteKummerRootCharacter_continuous
    (n : ℕ+) (hmu : NthRootsOfUnityInBase (K := K) (L := Ω) n)
    (a : (chosenFiniteKummerRadicalDatum (K := K) (L := Ω) n).carrier) :
    Continuous (infiniteKummerRootCharacter n hmu a) := by
  apply continuous_of_continuousAt_one (infiniteKummerRootCharacter n hmu a)
  rw [ContinuousAt, map_one]
  rw [show (𝓝 : DiscreteNthRootsSubgroup Ω (n : ℕ) →
      Filter (DiscreteNthRootsSubgroup Ω (n : ℕ))) = pure from nhds_discrete _,
    tendsto_pure]
  exact (infiniteKummerRootCharacter_isOpen_ker n hmu a).mem_nhds (by simp)

end InfiniteKummerContinuity

end KummerTheory
end
end

section
-- module Solutions.OAIQ244_DUKE.Kummer_Concrete_KummerCorrespondenceFormula
attribute [-instance] _root_.ClassFormation.DegreeData.GaloisSubextension.extensionSubgroup_normalInstance _root_.ClassFormation.FiniteCyclicSubextension.instNormalSubtypeMemSubgroupFieldExtensionSubgroupField _root_.ClassFormation.FiniteGaloisSubextension.extensionSubgroup_normalInstance _root_.ClassFormation.FiniteGaloisSubextension.extensionSubgroup_over_intermediate_normalInstance _root_.ClassFormation.FiniteGaloisSubextension.intermediateField_normalInstance _root_.ClassFormation.FiniteUnramifiedCyclicExtension.instNormalSubtypeMemSubgroupFieldExtensionSubgroupField _root_.ClassFormation.conjugateExtension_normal _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalClassFieldTheory.extensionSubgroupBase_normal _root_.LocalClassFieldTheory.finiteGaloisExtensionSubgroupOfEmbedding_normal _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.LubinTate.compatibleGroupFamiliesCommGroup _root_.LubinTate.compatibleGroupFamiliesGroup _root_.OAI.PrimeDegreePackets.boundedRealFields_finite _root_.OAI.PrimeDegreePackets.diagonalLogAction _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.OAI.PrimeDegreePackets.xT2Space _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionResidueField.instField _root_.RamificationTheory.HilbertRamification.ValuationSubring.inertiaGroup_normal _root_.RamificationTheory.HilbertRamification.ValuationSubring.ramificationGroupInInertiaAut_normal _root_.RamificationTheory.HilbertRamification.ValuationSubring.selectedResidueField.instAlgebra _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.RelativeIdeleGroup.relativeIdeleMulAction _root_.ValuationTheory.DiscreteValuationField.DVF.maximalIdealPowSuccQuotModule _root_.ValuationTheory.DiscreteValuationField.DVF.residueField.field _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.isDomain _root_.CyclicCohomology.binaryCoefficientFamilyCommGroup _root_.LocalClassFieldTheory.intrinsicAbsoluteGaloisT2 _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteIdeleGroupIsTopologicalGroup _root_.finiteLocalUnitsOpen _root_.ideleGroupIsTopologicalGroup _root_.relativeAdeleRingIntermediateAlgebra _root_.relativeAdeleRingTopIntermediateAlgebra
attribute [-simp] _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.IsDiscreteValuationRing.addVal_ringEquiv _root_.KummerTheory.chosenSimpleKummerRootCharacter_apply _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.LocalFieldTheory.residueField_algebraMap_residue _root_.OAI.PrimeDegreePackets.ThetaConstruction.schwartzCM_apply _root_.infinitePlace_mult_smul
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

/-!
# the Kummer pairing formula

For `E = K(√[n]{Delta})`, this file packages the canonical transposed
Kummer pairing

`Gal(E/K) → Hom(Delta / Kˣⁿ, mu_n(E))`.

Its Galois-side injectivity is obtained from the fact that the internal
Kummer roots generate `E`; this generation statement is proved below from
the definition of `kummerRadicalExtension` rather than assumed.

For surjectivity, finitely many character coordinates are factored through
the quotient by their common open kernel.  Finite roots-of-unity duality
solves that finite problem, and compactness of the profinite Galois group
then supplies one automorphism solving all coordinates simultaneously.
-/

noncomputable section

namespace KummerTheory

open scoped IsMulCommutative

variable {K Omega : Type*} [Field K] [Field Omega] [Algebra K Omega]

/-- The roots belonging to `Delta`, regarded inside their radical
extension, generate that extension. -/
theorem kummerRadicalExtension_internalRoots_adjoin_eq_top
    (n : ℕ+) (Delta : KummerSubgroup K n) :
    IntermediateField.adjoin K
      (kummerRootSet
        (K := K)
        (Omega := kummerRadicalExtension
          (K := K) (Omega := Omega) n Delta.1)
        n Delta.1) = ⊤ := by
  let E := kummerRadicalExtension
    (K := K) (Omega := Omega) n Delta.1
  let R : IntermediateField K E := IntermediateField.adjoin K
    (kummerRootSet (K := K) (Omega := E) n Delta.1)
  apply top_unique
  intro x _
  have hall : ∀ y : Omega, ∀ hy : y ∈ E, (⟨y, hy⟩ : E) ∈ R := by
    intro y hy
    change y ∈ IntermediateField.adjoin K
      (kummerRootSet (K := K) (Omega := Omega) n Delta.1) at hy
    induction hy using IntermediateField.adjoin_induction with
    | mem beta hbeta =>
        apply IntermediateField.subset_adjoin K
        obtain ⟨a, ha⟩ := hbeta
        refine ⟨a, ?_⟩
        apply Subtype.ext
        exact ha
    | algebraMap a => exact R.algebraMap_mem a
    | add x y hx hy ihx ihy => exact R.add_mem ihx ihy
    | inv x hx ihx => exact R.inv_mem ihx
    | mul x y hx hy ihx ihy => exact R.mul_mem ihx ihy
  exact hall x.1 x.property

/-- A finite set of coordinates of a nondegenerate continuous pairing is
simultaneously realizable.  The proof forms the finite quotient of the
compact source by the common open kernel and applies finite roots-of-unity
duality to that quotient and to the subgroup generated by the coordinates.
-/
theorem exists_pairing_element_matching_finset
    {G R L : Type*} [Field L] [Algebra K L]
    [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [CommGroup R]
    (n : ℕ+) (hmu : (primitiveRoots (n : ℕ) K).Nonempty)
    (hRexponent : ∀ r : R, r ^ (n : ℕ) = 1)
    (f : R →* (G →* DiscreteNthRootsSubgroup L (n : ℕ)))
    (t : G →* (R →* DiscreteNthRootsSubgroup L (n : ℕ)))
    (hpair : ∀ g r, t g r = f r g)
    (hf : Function.Injective f)
    (hcontinuous : ∀ r,
      Continuous (fun g : G => f r g))
    (S : Finset R)
    (chi : R →* DiscreteNthRootsSubgroup L (n : ℕ)) :
    ∃ g : G, ∀ r ∈ S, t g r = chi r := by
  let H : Subgroup G := ⨅ r : S, MonoidHom.ker (f r.1)
  have hHopen : IsOpen (H : Set G) := by
    dsimp only [H]
    rw [Subgroup.coe_iInf]
    change IsOpen (⋂ r : S, (MonoidHom.ker (f r.1) : Set G))
    apply isOpen_iInter_of_finite
    intro r
    rw [MonoidHom.coe_ker]
    exact (isOpen_discrete ({1} :
      Set (DiscreteNthRootsSubgroup L (n : ℕ)))).preimage
        (hcontinuous r.1)
  let : H.Normal := H.normal_of_isMulCommutative
  let Q := G ⧸ H
  let : Finite Q := H.quotient_finite_of_isOpen hHopen
  let R0 := Subgroup.closure (S : Set R)
  have hR0exponent : ∀ r : R0, r ^ (n : ℕ) = 1 := by
    intro r
    apply Subtype.ext
    exact hRexponent r.1
  let : Finite R0 := CommGroup.finite_of_fg_isMulTorsion (G := R0) (fun r =>
    isOfFinOrder_iff_pow_eq_one.mpr ⟨(n : ℕ), n.pos, hR0exponent r⟩)
  have hHker (r : R0) : H ≤ MonoidHom.ker (f r.1) := by
    intro g hg
    have hclosure : R0 ≤ MonoidHom.ker (t g) := by
      rw [Subgroup.closure_le]
      intro x hx
      change t g x = 1
      rw [hpair]
      exact (show g ∈ MonoidHom.ker (f x) from
        (iInf_le (fun r : S => MonoidHom.ker (f r.1)) ⟨x, hx⟩) hg)
    rw [MonoidHom.mem_ker, ← hpair]
    exact hclosure r.property
  let f0 : R0 →* (Q →* DiscreteNthRootsSubgroup L (n : ℕ)) :=
    { toFun := fun r => QuotientGroup.lift H (f r.1) (hHker r)
      map_one' := by
        apply MonoidHom.ext
        intro q
        obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective H q
        simp
      map_mul' := by
        intro r s
        apply MonoidHom.ext
        intro q
        obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective H q
        simp }
  have hf0 : Function.Injective f0 := by
    intro r s hrs
    apply Subtype.ext
    apply hf
    apply MonoidHom.ext
    intro g
    have hvalue := DFunLike.congr_fun hrs (QuotientGroup.mk' H g)
    exact hvalue
  let t0 : Q →* (R0 →* DiscreteNthRootsSubgroup L (n : ℕ)) :=
    { toFun := fun q =>
        { toFun := fun r => f0 r q
          map_one' := by simp
          map_mul' := by intro r s; exact DFunLike.congr_fun (map_mul f0 r s) q }
      map_one' := by
        apply MonoidHom.ext
        intro r
        exact map_one (f0 r)
      map_mul' := by
        intro q p
        apply MonoidHom.ext
        intro r
        exact map_mul (f0 r) q p }
  have ht0 : Function.Injective t0 := by
    intro q p hqp
    obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective H q
    obtain ⟨h, rfl⟩ := QuotientGroup.mk'_surjective H p
    apply (QuotientGroup.eq_iff_div_mem).2
    dsimp only [H]
    rw [Subgroup.mem_iInf]
    intro r
    rw [MonoidHom.mem_ker, map_div]
    have hvalue := DFunLike.congr_fun hqp
      (⟨r.1, Subgroup.subset_closure r.2⟩ : R0)
    change f r.1 g = f r.1 h at hvalue
    rw [hvalue]
    exact div_self' _
  have hQexponent : ∀ q : Q, q ^ (n : ℕ) = 1 := by
    intro q
    apply ht0
    rw [map_pow, map_one]
    apply MonoidHom.ext
    intro r
    apply Subtype.ext
    exact (t0 q r).2
  obtain ⟨dualQ⟩ := finiteNthRootsCharacterDuality
    (G := Q) (K := K) (L := L) n hmu hQexponent
  obtain ⟨dualR0⟩ := finiteNthRootsCharacterDuality
    (G := R0) (K := K) (L := L) n hmu hR0exponent
  let : NeZero (n : ℕ) := ⟨n.ne_zero⟩
  let : Finite (DiscreteNthRootsSubgroup L (n : ℕ)) :=
    inferInstanceAs (Finite (nthRootsSubgroup L (n : ℕ)))
  let : Fintype Q := Fintype.ofFinite Q
  let : Fintype R0 := Fintype.ofFinite R0
  let : Finite (R0 →* DiscreteNthRootsSubgroup L (n : ℕ)) :=
    Finite.of_injective
      (fun psi : R0 →* DiscreteNthRootsSubgroup L (n : ℕ) =>
        (psi : R0 → DiscreteNthRootsSubgroup L (n : ℕ)))
      DFunLike.coe_injective
  let : Fintype (R0 →* DiscreteNthRootsSubgroup L (n : ℕ)) :=
    Fintype.ofFinite _
  have hcardR0Q : Fintype.card R0 ≤ Fintype.card Q :=
    Fintype.card_le_of_injective
      (fun r : R0 => dualQ (f0 r)) (dualQ.injective.comp hf0)
  have hcardQR0 : Fintype.card Q ≤ Fintype.card R0 :=
    Fintype.card_le_of_injective
      (fun q : Q => dualR0 (t0 q)) (dualR0.injective.comp ht0)
  have hcardQTarget :
      Fintype.card Q =
        Fintype.card (R0 →* DiscreteNthRootsSubgroup L (n : ℕ)) := by
    calc
      Fintype.card Q = Fintype.card R0 := Nat.le_antisymm hcardQR0 hcardR0Q
      _ = Fintype.card (R0 →* DiscreteNthRootsSubgroup L (n : ℕ)) :=
        Fintype.card_congr dualR0.symm.toEquiv
  have ht0surjective : Function.Surjective t0 :=
    ht0.surjective_of_finite (Fintype.equivOfCardEq hcardQTarget)
  obtain ⟨q, hq⟩ := ht0surjective (chi.comp R0.subtype)
  obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective H q
  refine ⟨g, ?_⟩
  intro r hr
  have hvalue := DFunLike.congr_fun hq
    (⟨r, Subgroup.subset_closure hr⟩ : R0)
  change f r g = chi r at hvalue
  rw [hpair]
  exact hvalue

section RadicalExtensionPairing

variable [IsSepClosure K Omega]

/-- The canonical map in the displayed formula of the Kummer correspondence,
constructed by transposing the restricted Kummer character pairing. -/
def kummerRadicalExtensionRestrictedTranspose
    (n : ℕ+) (hn : ((n : ℕ) : K) ≠ 0)
    (hmu : (primitiveRoots (n : ℕ) K).Nonempty)
    (Delta : KummerSubgroup K n) :
    Gal(kummerRadicalExtension
        (K := K) (Omega := Omega) n Delta.1/K) →*
      (RestrictedRadicalQuotient n Delta →*
        nthRootsSubgroup
          (kummerRadicalExtension
            (K := K) (Omega := Omega) n Delta.1) (n : ℕ)) := by
  let E := kummerRadicalExtension
    (K := K) (Omega := Omega) n Delta.1
  letI : IsGalois K E := kummerRadicalExtension_isGalois n Delta.1
  exact restrictedKummerTranspose n hmu Delta
    (le_finiteKummerRadicalSubgroup_kummerRadicalExtension n hn Delta.1)

/-- The canonical map is injective.  The source is the internal-root
generation theorem above, so no generation hypothesis is exposed in this
statement. -/
theorem kummerRadicalExtensionRestrictedTranspose_injective
    (n : ℕ+) (hn : ((n : ℕ) : K) ≠ 0)
    (hmu : (primitiveRoots (n : ℕ) K).Nonempty)
    (Delta : KummerSubgroup K n) :
    Function.Injective
      (kummerRadicalExtensionRestrictedTranspose
        (K := K) (Omega := Omega) n hn hmu Delta) := by
  let E := kummerRadicalExtension
    (K := K) (Omega := Omega) n Delta.1
  let : IsGalois K E := kummerRadicalExtension_isGalois n Delta.1
  exact restrictedKummerTranspose_injective_of_adjoin n hmu Delta
    (le_finiteKummerRadicalSubgroup_kummerRadicalExtension n hn Delta.1)
    (kummerRadicalExtension_internalRoots_adjoin_eq_top n Delta)

/-- Each evaluation coordinate of the restricted transpose is continuous
for the Krull topology on the Galois group and the discrete topology on
`mu_n(E)`.  This is the closed-locus source for the compactness/FIP proof of
surjectivity. -/
theorem restrictedKummerTranspose_evaluation_continuous
    {L : Type*} [Field L] [Algebra K L] [IsGalois K L]
    (n : ℕ+) (hmu : (primitiveRoots (n : ℕ) K).Nonempty)
    (Delta : KummerSubgroup K n)
    (hDelta : Delta.1 ≤
      finiteKummerRadicalSubgroup (K := K) (L := L) n)
    (q : RestrictedRadicalQuotient n Delta) :
    @Continuous (Gal(L/K)) (DiscreteNthRootsSubgroup L (n : ℕ))
      inferInstance
      (DiscreteNthRootsSubgroup.instTopologicalSpaceSubtypeUnitsMemSubgroup
        L (n : ℕ))
      (fun sigma => restrictedKummerTranspose n hmu Delta hDelta sigma q) := by
  let D := chosenFiniteKummerRadicalDatum (K := K) (L := L) n
  let hbase : NthRootsOfUnityInBase (K := K) (L := L) n :=
    nthRootsOfUnityInBase_of_primitiveRoots (K := K) (L := L) n hmu
  obtain ⟨a, rfl⟩ :=
    restrictedRadicalQuotientMk_surjective n Delta q
  let aD : D.carrier := restrictedRadicalInclusion n Delta hDelta a
  have hcontinuous := infiniteKummerRootCharacter_continuous n hbase aD
  exact hcontinuous.congr (fun _ => rfl)

/-- The locus on which one evaluation coordinate takes a prescribed value.
These are the closed sets whose finite-intersection property yields the
surjectivity half of the displayed Kummer formula. -/
def restrictedKummerEvaluationLocus
    {L : Type*} [Field L] [Algebra K L] [IsGalois K L]
    (n : ℕ+) (hmu : (primitiveRoots (n : ℕ) K).Nonempty)
    (Delta : KummerSubgroup K n)
    (hDelta : Delta.1 ≤
      finiteKummerRadicalSubgroup (K := K) (L := L) n)
    (chi : RestrictedRadicalQuotient n Delta →*
      nthRootsSubgroup L (n : ℕ))
    (q : RestrictedRadicalQuotient n Delta) : Set Gal(L/K) :=
  {sigma | restrictedKummerTranspose n hmu Delta hDelta sigma q = chi q}

/-- Every evaluation locus is closed. -/
theorem restrictedKummerEvaluationLocus_isClosed
    {L : Type*} [Field L] [Algebra K L] [IsGalois K L]
    (n : ℕ+) (hmu : (primitiveRoots (n : ℕ) K).Nonempty)
    (Delta : KummerSubgroup K n)
    (hDelta : Delta.1 ≤
      finiteKummerRadicalSubgroup (K := K) (L := L) n)
    (chi : RestrictedRadicalQuotient n Delta →*
      nthRootsSubgroup L (n : ℕ))
    (q : RestrictedRadicalQuotient n Delta) :
    IsClosed (restrictedKummerEvaluationLocus n hmu Delta hDelta chi q) := by
  let : TopologicalSpace (nthRootsSubgroup L (n : ℕ)) :=
    DiscreteNthRootsSubgroup.instTopologicalSpaceSubtypeUnitsMemSubgroup
      L (n : ℕ)
  let : DiscreteTopology (nthRootsSubgroup L (n : ℕ)) :=
    DiscreteNthRootsSubgroup.instDiscreteTopologySubtypeUnitsMemSubgroup
      L (n : ℕ)
  let : T2Space (nthRootsSubgroup L (n : ℕ)) :=
    @DiscreteTopology.toT2Space (nthRootsSubgroup L (n : ℕ))
      (DiscreteNthRootsSubgroup.instTopologicalSpaceSubtypeUnitsMemSubgroup L (n : ℕ))
      (DiscreteNthRootsSubgroup.instDiscreteTopologySubtypeUnitsMemSubgroup L (n : ℕ))
  exact isClosed_eq
    (restrictedKummerTranspose_evaluation_continuous n hmu Delta hDelta q)
    continuous_const

/-- Membership in all evaluation loci is exactly equality with the target
character.  Together with compactness of `Gal(L/K)`, this identifies the
precise finite-intersection problem remaining in the surjectivity proof. -/
theorem mem_iInter_restrictedKummerEvaluationLocus_iff
    {L : Type*} [Field L] [Algebra K L] [IsGalois K L]
    (n : ℕ+) (hmu : (primitiveRoots (n : ℕ) K).Nonempty)
    (Delta : KummerSubgroup K n)
    (hDelta : Delta.1 ≤
      finiteKummerRadicalSubgroup (K := K) (L := L) n)
    (chi : RestrictedRadicalQuotient n Delta →*
      nthRootsSubgroup L (n : ℕ))
    (sigma : Gal(L/K)) :
    sigma ∈ ⋂ q, restrictedKummerEvaluationLocus
        n hmu Delta hDelta chi q ↔
      restrictedKummerTranspose n hmu Delta hDelta sigma = chi := by
  rw [Set.mem_iInter]
  constructor
  · intro h
    apply MonoidHom.ext
    exact h
  · intro h q
    exact DFunLike.congr_fun h q

/-- Every finite set of coordinates of a target character is realized by
one Galois automorphism of the radical extension. -/
theorem exists_kummerRadicalExtensionRestrictedTranspose_match_finset
    (n : ℕ+) (hn : ((n : ℕ) : K) ≠ 0)
    (hmu : (primitiveRoots (n : ℕ) K).Nonempty)
    (Delta : KummerSubgroup K n)
    (S : Finset (RestrictedRadicalQuotient n Delta))
    (chi : RestrictedRadicalQuotient n Delta →*
      nthRootsSubgroup
        (kummerRadicalExtension
          (K := K) (Omega := Omega) n Delta.1) (n : ℕ)) :
    ∃ sigma : Gal(kummerRadicalExtension
        (K := K) (Omega := Omega) n Delta.1/K),
      ∀ q ∈ S,
        kummerRadicalExtensionRestrictedTranspose
          n hn hmu Delta sigma q = chi q := by
  let E := kummerRadicalExtension
    (K := K) (Omega := Omega) n Delta.1
  let : IsGalois K E := kummerRadicalExtension_isGalois n Delta.1
  let : IsMulCommutative Gal(E/K) :=
    kummerRadicalExtension_isMulCommutative n hmu Delta.1
  let : CommGroup Gal(E/K) := by infer_instance
  let hDelta : Delta.1 ≤
      finiteKummerRadicalSubgroup (K := K) (L := E) n :=
    le_finiteKummerRadicalSubgroup_kummerRadicalExtension n hn Delta.1
  let f : RestrictedRadicalQuotient n Delta →*
      (Gal(E/K) →* DiscreteNthRootsSubgroup E (n : ℕ)) :=
    restrictedQuotientKummerCharacter n hmu Delta hDelta
  let t : Gal(E/K) →*
      (RestrictedRadicalQuotient n Delta →*
        DiscreteNthRootsSubgroup E (n : ℕ)) :=
    restrictedKummerTranspose n hmu Delta hDelta
  apply exists_pairing_element_matching_finset
    (K := K) n hmu
    (restrictedRadicalQuotient_pow_eq_one n Delta)
    f t (fun _ _ => rfl)
    (restrictedQuotientKummerCharacter_injective n hmu Delta hDelta)
    _ S chi
  intro q
  exact restrictedKummerTranspose_evaluation_continuous
    n hmu Delta hDelta q

/-- **the Kummer correspondence, displayed Kummer formula: surjectivity.**

Compactness of the profinite Galois group upgrades the finite-coordinate
realization theorem to a single automorphism realizing every coordinate.
-/
theorem kummerRadicalExtensionRestrictedTranspose_surjective
    (n : ℕ+) (hn : ((n : ℕ) : K) ≠ 0)
    (hmu : (primitiveRoots (n : ℕ) K).Nonempty)
    (Delta : KummerSubgroup K n) :
    Function.Surjective
      (kummerRadicalExtensionRestrictedTranspose
        (K := K) (Omega := Omega) n hn hmu Delta) := by
  let E := kummerRadicalExtension
    (K := K) (Omega := Omega) n Delta.1
  let : IsGalois K E := kummerRadicalExtension_isGalois n Delta.1
  let hDelta : Delta.1 ≤
      finiteKummerRadicalSubgroup (K := K) (L := E) n :=
    le_finiteKummerRadicalSubgroup_kummerRadicalExtension n hn Delta.1
  intro chi
  have hintersection :
      (⋂ q, restrictedKummerEvaluationLocus
        n hmu Delta hDelta chi q).Nonempty := by
    apply CompactSpace.iInter_nonempty
    · intro q
      exact restrictedKummerEvaluationLocus_isClosed
        n hmu Delta hDelta chi q
    · intro S
      obtain ⟨sigma, hsigma⟩ :=
        exists_kummerRadicalExtensionRestrictedTranspose_match_finset
          (K := K) (Omega := Omega) n hn hmu Delta S chi
      refine ⟨sigma, ?_⟩
      rw [Set.mem_iInter₂]
      intro q hq
      exact hsigma q hq
  obtain ⟨sigma, hsigma⟩ := hintersection
  refine ⟨sigma, ?_⟩
  exact (mem_iInter_restrictedKummerEvaluationLocus_iff
    n hmu Delta hDelta chi sigma).1 hsigma

/-- **the Kummer correspondence, displayed Kummer formula.**  The canonical Kummer
pairing identifies the Galois group of `K(√[n]{Delta})` with the full
character group of `Delta / Kˣⁿ`. -/
def kummerRadicalExtensionRestrictedTransposeMulEquiv
    (n : ℕ+) (hn : ((n : ℕ) : K) ≠ 0)
    (hmu : (primitiveRoots (n : ℕ) K).Nonempty)
    (Delta : KummerSubgroup K n) :
    Gal(kummerRadicalExtension
        (K := K) (Omega := Omega) n Delta.1/K) ≃*
      (RestrictedRadicalQuotient n Delta →*
        nthRootsSubgroup
          (kummerRadicalExtension
            (K := K) (Omega := Omega) n Delta.1) (n : ℕ)) :=
  MulEquiv.ofBijective
    (kummerRadicalExtensionRestrictedTranspose n hn hmu Delta)
    ⟨kummerRadicalExtensionRestrictedTranspose_injective n hn hmu Delta,
      kummerRadicalExtensionRestrictedTranspose_surjective n hn hmu Delta⟩

end RadicalExtensionPairing

end KummerTheory
end
end

section
-- module Solutions.OAIQ244_DUKE.KummerTheory_Concrete_SUnitPreparation_SUnitPowerQuotient
attribute [-instance] _root_.ClassFormation.DegreeData.FiniteAbstractExtension.ramificationQuotientFinite _root_.ClassFormation.DegreeData.FiniteAbstractExtension.representedQuotientFinite _root_.ClassFormation.DegreeData.FiniteAbstractExtension.residueQuotientFinite _root_.ClassFormation.DegreeData.FiniteResidueAbstractExtension.instFiniteQuotientSubtypeMemSubgroupFieldBaseExtensionSubgroupField _root_.ClassFormation.DegreeData.FiniteTower.baseQuotientFinite _root_.ClassFormation.DegreeData.FiniteTower.topQuotientFinite _root_.ClassFormation.DegreeData.FiniteTower.totalQuotientFinite _root_.ClassFormation.DegreeData.GaloisSubextension.extensionSubgroup_normalInstance _root_.ClassFormation.FiniteAbstractField.instFiniteQuotientSubtypeMemSubgroupBaseFieldExtensionSubgroupField _root_.ClassFormation.FiniteAbstractFieldExtension.instFiniteQuotientSubtypeMemSubgroupFieldBaseExtensionSubgroupField _root_.ClassFormation.FiniteCyclicSubextension.instFiniteQuotientSubtypeMemSubgroupFieldExtensionSubgroupField _root_.ClassFormation.FiniteCyclicSubextension.instNormalSubtypeMemSubgroupFieldExtensionSubgroupField _root_.ClassFormation.FiniteGaloisSubextension.extensionSubgroup_normalInstance _root_.ClassFormation.FiniteGaloisSubextension.extensionSubgroup_over_intermediate_normalInstance _root_.ClassFormation.FiniteGaloisSubextension.intermediateField_normalInstance _root_.ClassFormation.FiniteUnramifiedCyclicExtension.instFiniteQuotientSubtypeMemSubgroupBaseFieldExtensionSubgroupField _root_.ClassFormation.FiniteUnramifiedCyclicExtension.instFiniteQuotientSubtypeMemSubgroupFieldExtensionSubgroupField _root_.ClassFormation.FiniteUnramifiedCyclicExtension.instNormalSubtypeMemSubgroupFieldExtensionSubgroupField _root_.ClassFormation.conjugateExtension_normal _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalClassFieldTheory.baseFixingExtensionQuotient_finite _root_.LocalClassFieldTheory.extensionSubgroupBase_normal _root_.LocalClassFieldTheory.finiteGaloisExtensionSubgroupOfEmbedding_normal _root_.LocalFieldTheory.DiscreteValuationField.finite_nsmulAddKernel_padicInt_pi _root_.LocalFieldTheory.DiscreteValuationField.finite_padicInt_finPi_nsmulQuotient _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LubinTate.compatibleGroupFamiliesCommGroup _root_.LubinTate.compatibleGroupFamiliesGroup _root_.OAI.PrimeDegreePackets.boundedRealFields_finite _root_.OAI.PrimeDegreePackets.instNonemptyLeafTestSpace _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionResidueField.instField _root_.RamificationTheory.HilbertRamification.ValuationSubring.inertiaGroup_normal _root_.RamificationTheory.HilbertRamification.ValuationSubring.ramificationGroupInInertiaAut_normal _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.residueField.field _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.isDomain _root_.CyclicCohomology.binaryCoefficientFamilyCommGroup _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace
attribute [-simp] _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.IsDiscreteValuationRing.addVal_ringEquiv _root_.KummerTheory.mem_sUnitFiniteKummerRadical_iff _root_.LocalFieldTheory.residueField_algebraMap_residue _root_.OAI.PrimeDegreePackets.ThetaConstruction.schwartzCM_apply _root_.infinitePlace_mult_smul _root_.sUnit_smul_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

/-!
# Power quotients of S-unit groups

The finite `n`-th-power quotient of an `S`-unit group, its cardinality, and explicit `ZMod n` coordinates.
-/

open scoped NumberField Classical IsMulCommutative NNReal ValuativeRel
open NumberField IsDedekindDomain
open LocalFieldTheory

noncomputable section

namespace KummerTheory

variable {K : Type*} [Field K]
    [numberFieldK : NumberField K]

/-- In multiplicative notation, the free integral quotient by `n`-th
powers is a product of copies of `ZMod n`. -/
noncomputable def multiplicativeFinsuppNthPowerQuotientEquivPiZMod
    (d n : ℕ) :
    Multiplicative (Fin d →₀ ℤ) ⧸
        (powMonoidHom n :
          Multiplicative (Fin d →₀ ℤ) →*
            Multiplicative (Fin d →₀ ℤ)).range ≃*
      Multiplicative (Fin d → ZMod n) := by
  rw [
    LocalFieldTheory.powMonoidHom_range_multiplicative_eq_nsmulAddSubgroup_toSubgroup]
  exact (finsuppNsmulQuotientEquivPiZMod d n).toMultiplicative

/-- The cardinality of `(ℤ^d) / n(ℤ^d)` is `n ^ d`. -/
theorem card_finsupp_nsmulQuotient
    (d : ℕ) (n : ℕ+) :
    Nat.card
        ((Fin d →₀ ℤ) ⧸
          LocalFieldTheory.nsmulAddSubgroup
            (Fin d →₀ ℤ) (n : ℕ)) =
      (n : ℕ) ^ d := by
  let _ : NeZero (n : ℕ) := ⟨n.ne_zero⟩
  rw [Nat.card_congr
    (finsuppNsmulQuotientEquivPiZMod d n).toEquiv,
    Nat.card_pi]
  simp

/-- The `n`-th-power quotient of an `S`-unit group is finite. -/
noncomputable instance finite_sUnit_nthPowerQuotient
    (S : Finset (HeightOneSpectrum (𝓞 K))) (n : ℕ+) :
    Finite
      (SUnitGroup (K := K) S ⧸
        (powMonoidHom (n : ℕ) :
          SUnitGroup (K := K) S →*
            SUnitGroup (K := K) S).range) := by
  apply LocalFieldTheory.finite_nthPowerQuotient_of_mulEquiv
    (SUnitGroup (K := K) S)
    (NumberField.Units.torsion K ×
      Multiplicative
        (Fin (SUnitGroup.logRank (K := K) S) →₀ ℤ))
    (n : ℕ)
    (SUnitGroup.decomposition (K := K) S)

/-- The `S`-unit theorem in the form used in the finite S-unit preparation argument:

`#(Kˢ / Kˢⁿ) = n ^ (#InfinitePlace K + #S)`.
-/
theorem card_sUnit_nthPowerQuotient
    (S : Finset (HeightOneSpectrum (𝓞 K)))
    (n : ℕ+)
    (hmu : (primitiveRoots (n : ℕ) K).Nonempty) :
    Nat.card
        (SUnitGroup (K := K) S ⧸
          (powMonoidHom (n : ℕ) :
            SUnitGroup (K := K) S →*
              SUnitGroup (K := K) S).range) =
      (n : ℕ) ^ totalPlaceCard (K := K) S := by
  let F :=
    Fin (SUnitGroup.logRank (K := K) S) →₀ ℤ
  let _ : NeZero (n : ℕ) := ⟨n.ne_zero⟩
  have hfree :
      Nat.card
          (Multiplicative F ⧸
            (powMonoidHom (n : ℕ) :
              Multiplicative F →* Multiplicative F).range) =
        (n : ℕ) ^ SUnitGroup.logRank (K := K) S := by
    have htransport :=
      LocalFieldTheory.card_multiplicative_nthPowerQuotient_eq_additive_nsmulQuotient
        F (n : ℕ)
    rw [htransport]
    exact card_finsupp_nsmulQuotient
      (SUnitGroup.logRank (K := K) S) n
  have hplace :
      totalPlaceCard (K := K) S =
        SUnitGroup.logRank (K := K) S + 1 := by
    unfold totalPlaceCard SUnitGroup.logRank
    have hinfinite :
        0 < Fintype.card (InfinitePlace K) :=
      Fintype.card_pos
    omega
  calc
    Nat.card
        (SUnitGroup (K := K) S ⧸
          (powMonoidHom (n : ℕ) :
            SUnitGroup (K := K) S →*
              SUnitGroup (K := K) S).range) =
        Nat.card
          ((NumberField.Units.torsion K × Multiplicative F) ⧸
            (powMonoidHom (n : ℕ) :
              NumberField.Units.torsion K × Multiplicative F →*
                NumberField.Units.torsion K ×
                  Multiplicative F).range) := by
      exact Nat.card_congr
        (LocalFieldTheory.nthPowerQuotientEquivOfMulEquiv
          (SUnitGroup (K := K) S)
          (NumberField.Units.torsion K × Multiplicative F)
          (n : ℕ)
          (SUnitGroup.decomposition (K := K) S)).toEquiv
    _ =
        Nat.card
          ((NumberField.Units.torsion K ⧸
              (powMonoidHom (n : ℕ) :
                NumberField.Units.torsion K →*
                  NumberField.Units.torsion K).range) ×
            (Multiplicative F ⧸
              (powMonoidHom (n : ℕ) :
                Multiplicative F →* Multiplicative F).range)) := by
      exact Nat.card_congr
        (LocalFieldTheory.nthPowerProductQuotientEquiv
          (NumberField.Units.torsion K) (Multiplicative F)
          (n : ℕ)).toEquiv
    _ =
        (n : ℕ) *
          (n : ℕ) ^ SUnitGroup.logRank (K := K) S := by
      rw [Nat.card_prod,
        card_numberField_torsion_nthPowerQuotient (K := K) n hmu,
        hfree]
    _ = (n : ℕ) ^ totalPlaceCard (K := K) S := by
      rw [hplace, pow_succ']

/-- The full `S`-unit quotient has one torsion coordinate and one
coordinate for every logarithmic free generator. -/
noncomputable def sUnitNthPowerQuotientCoordinates
    (S : Finset (HeightOneSpectrum (𝓞 K)))
    (n : ℕ+)
    (hmu : (primitiveRoots (n : ℕ) K).Nonempty) :
    SUnitGroup (K := K) S ⧸
        (powMonoidHom (n : ℕ) :
          SUnitGroup (K := K) S →*
            SUnitGroup (K := K) S).range ≃*
      Multiplicative (ZMod (n : ℕ)) ×
        Multiplicative
          (Fin (SUnitGroup.logRank (K := K) S) →
            ZMod (n : ℕ)) :=
  (LocalFieldTheory.nthPowerQuotientEquivOfMulEquiv
      (SUnitGroup (K := K) S)
      (NumberField.Units.torsion K ×
        Multiplicative
          (Fin (SUnitGroup.logRank (K := K) S) →₀ ℤ))
      (n : ℕ)
      (SUnitGroup.decomposition (K := K) S)).trans <|
    (LocalFieldTheory.nthPowerProductQuotientEquiv
      (NumberField.Units.torsion K)
      (Multiplicative
        (Fin (SUnitGroup.logRank (K := K) S) →₀ ℤ))
      (n : ℕ)).trans <|
      MulEquiv.prodCongr
        (numberFieldTorsionNthPowerQuotientEquivZMod
          (K := K) n hmu)
        (multiplicativeFinsuppNthPowerQuotientEquivPiZMod
          (SUnitGroup.logRank (K := K) S) (n : ℕ))

/-- Include an `S`-unit in the full `S`-unit Kummer subgroup. -/
def sUnitToFullSUnitKummerSubgroup
    (n : ℕ+)
    (S : Finset (HeightOneSpectrum (𝓞 K))) :
    SUnitGroup (K := K) S →*
      (fullSUnitKummerSubgroup (K := K) n S).1 :=
  Subgroup.inclusion le_sup_left

/-- Map an `S`-unit to its class in
`(Kˢ · Kˣⁿ) / Kˣⁿ`. -/
def sUnitToFullSUnitRadicalQuotient
    (n : ℕ+)
    (S : Finset (HeightOneSpectrum (𝓞 K))) :
    SUnitGroup (K := K) S →*
      KummerTheory.RestrictedRadicalQuotient
        n (fullSUnitKummerSubgroup (K := K) n S) :=
  (KummerTheory.restrictedRadicalQuotientMk
      n (fullSUnitKummerSubgroup (K := K) n S)).comp
    (sUnitToFullSUnitKummerSubgroup (K := K) n S)

/-- `S`-unit `n`-th powers vanish in the full radical quotient. -/
theorem nthPowerSubgroup_le_ker_sUnitToFullSUnitRadicalQuotient
    (n : ℕ+)
    (S : Finset (HeightOneSpectrum (𝓞 K))) :
    (powMonoidHom (n : ℕ) :
        SUnitGroup (K := K) S →*
          SUnitGroup (K := K) S).range ≤
      MonoidHom.ker
        (sUnitToFullSUnitRadicalQuotient (K := K) n S) := by
  intro x hx
  obtain ⟨y, hy⟩ :=
    (MonoidHom.mem_range
      (G := SUnitGroup (K := K) S)).mp hx
  rw [powMonoidHom_apply] at hy
  subst x
  rw [MonoidHom.mem_ker, map_pow]
  apply
    (KummerTheory.restrictedRadicalQuotientMk_eq_one_iff
      n (fullSUnitKummerSubgroup (K := K) n S) _).2
  exact
    (KummerTheory.mem_restrictedNthPowersSubgroup_iff
      n (fullSUnitKummerSubgroup (K := K) n S)).2
      ⟨(y : Kˣ), rfl⟩

/-- The canonical comparison

`Kˢ / Kˢⁿ → (Kˢ · Kˣⁿ) / Kˣⁿ`. -/
def sUnitNthPowerQuotientToFullSUnitRadicalQuotient
    (n : ℕ+)
    (S : Finset (HeightOneSpectrum (𝓞 K))) :
    SUnitGroup (K := K) S ⧸
        (powMonoidHom (n : ℕ) :
          SUnitGroup (K := K) S →*
            SUnitGroup (K := K) S).range →*
      KummerTheory.RestrictedRadicalQuotient
        n (fullSUnitKummerSubgroup (K := K) n S) :=
  QuotientGroup.lift
    (powMonoidHom (n : ℕ) :
      SUnitGroup (K := K) S →*
        SUnitGroup (K := K) S).range
    (sUnitToFullSUnitRadicalQuotient (K := K) n S)
    (nthPowerSubgroup_le_ker_sUnitToFullSUnitRadicalQuotient
      (K := K) n S)

/-- Every class in `(Kˢ · Kˣⁿ) / Kˣⁿ` has an `S`-unit representative. -/
theorem sUnitNthPowerQuotientToFullSUnitRadicalQuotient_surjective
    (n : ℕ+)
    (S : Finset (HeightOneSpectrum (𝓞 K))) :
    Function.Surjective
      (sUnitNthPowerQuotientToFullSUnitRadicalQuotient
        (K := K) n S) := by
  intro q
  obtain ⟨x, rfl⟩ :=
    KummerTheory.restrictedRadicalQuotientMk_surjective
      n (fullSUnitKummerSubgroup (K := K) n S) q
  obtain ⟨y, hy, z, hz, hyz⟩ :=
    Subgroup.mem_sup.1 x.property
  let yS : SUnitGroup (K := K) S := ⟨y, hy⟩
  refine
    ⟨QuotientGroup.mk'
        (powMonoidHom (n : ℕ) :
          SUnitGroup (K := K) S →*
            SUnitGroup (K := K) S).range yS, ?_⟩
  change
    KummerTheory.restrictedRadicalQuotientMk
        n (fullSUnitKummerSubgroup (K := K) n S)
        (sUnitToFullSUnitKummerSubgroup (K := K) n S yS) =
      KummerTheory.restrictedRadicalQuotientMk
        n (fullSUnitKummerSubgroup (K := K) n S) x
  apply
    (KummerTheory.restrictedRadicalQuotientMk_eq_iff
      n (fullSUnitKummerSubgroup (K := K) n S) _ _).2
  change y / x.1 ∈ KummerTheory.unitNthPowersSubgroup K n
  rw [← hyz]
  simpa using
    (KummerTheory.unitNthPowersSubgroup K n).inv_mem hz

/-- The canonical comparison from `Kˢ / Kˢⁿ` is injective.  The only
arithmetic point is saturation of the `S`-unit group under positive
powers, proved above from valuations. -/
theorem sUnitNthPowerQuotientToFullSUnitRadicalQuotient_injective
    (n : ℕ+)
    (S : Finset (HeightOneSpectrum (𝓞 K))) :
    Function.Injective
      (sUnitNthPowerQuotientToFullSUnitRadicalQuotient
        (K := K) n S) := by
  intro q r hqr
  induction q using QuotientGroup.induction_on' with
  | _ x =>
      induction r using QuotientGroup.induction_on' with
      | _ y =>
          apply (QuotientGroup.eq_iff_div_mem).2
          have hglobal :
              ((x : Kˣ) / (y : Kˣ)) ∈
                KummerTheory.unitNthPowersSubgroup K n := by
            have hrestricted :=
              (KummerTheory.restrictedRadicalQuotientMk_eq_iff
                n (fullSUnitKummerSubgroup (K := K) n S) _ _).1 hqr
            exact
              (KummerTheory.mem_restrictedNthPowersSubgroup_iff
                n (fullSUnitKummerSubgroup (K := K) n S)).1 hrestricted
          obtain ⟨z, hz⟩ :=
            (KummerTheory.mem_unitNthPowersSubgroup_iff n).mp hglobal
          have hzpow :
              z ^ (n : ℕ) ∈ SUnitGroup (K := K) S := by
            rw [hz]
            exact (SUnitGroup (K := K) S).div_mem x.property y.property
          let zS : SUnitGroup (K := K) S :=
            ⟨z, mem_sUnitGroup_of_pow_mem (K := K) S n z hzpow⟩
          apply
            (MonoidHom.mem_range
              (G := SUnitGroup (K := K) S)).2
          refine ⟨zS, ?_⟩
          rw [powMonoidHom_apply]
          apply Subtype.ext
          exact hz

/-- The exact quotient identification used to define
`N = K(√[n]{Kˢ})`. -/
noncomputable def sUnitNthPowerQuotientEquivFullSUnitRadicalQuotient
    (n : ℕ+)
    (S : Finset (HeightOneSpectrum (𝓞 K))) :
    SUnitGroup (K := K) S ⧸
        (powMonoidHom (n : ℕ) :
          SUnitGroup (K := K) S →*
            SUnitGroup (K := K) S).range ≃*
      KummerTheory.RestrictedRadicalQuotient
        n (fullSUnitKummerSubgroup (K := K) n S) :=
  MulEquiv.ofBijective
    (sUnitNthPowerQuotientToFullSUnitRadicalQuotient
      (K := K) n S)
    ⟨sUnitNthPowerQuotientToFullSUnitRadicalQuotient_injective
        (K := K) n S,
      sUnitNthPowerQuotientToFullSUnitRadicalQuotient_surjective
        (K := K) n S⟩

/-- The full `S`-unit radical quotient is finite. -/
noncomputable instance finite_fullSUnitRadicalQuotient
    (n : ℕ+)
    (S : Finset (HeightOneSpectrum (𝓞 K))) :
    Finite
      (KummerTheory.RestrictedRadicalQuotient
        n (fullSUnitKummerSubgroup (K := K) n S)) :=
  Finite.of_equiv
    (SUnitGroup (K := K) S ⧸
      (powMonoidHom (n : ℕ) :
        SUnitGroup (K := K) S →*
          SUnitGroup (K := K) S).range)
    (sUnitNthPowerQuotientEquivFullSUnitRadicalQuotient
      (K := K) n S)

/-- The radical quotient defining `N` has cardinality `n ^ s`. -/
theorem card_fullSUnitRadicalQuotient
    (n : ℕ+)
    (S : Finset (HeightOneSpectrum (𝓞 K)))
    (hmu : (primitiveRoots (n : ℕ) K).Nonempty) :
    Nat.card
        (KummerTheory.RestrictedRadicalQuotient
          n (fullSUnitKummerSubgroup (K := K) n S)) =
      (n : ℕ) ^ totalPlaceCard (K := K) S := by
  rw [← card_sUnit_nthPowerQuotient (K := K) S n hmu]
  exact Nat.card_congr
    (sUnitNthPowerQuotientEquivFullSUnitRadicalQuotient
      (K := K) n S).symm.toEquiv

end KummerTheory
end
end

section
-- module Solutions.OAIQ244_DUKE.KummerTheory_Concrete_SUnitPreparation_FullSUnitKummerExtension
attribute [-instance] _root_.ClassFormation.DegreeData.GaloisSubextension.extensionSubgroup_normalInstance _root_.ClassFormation.FiniteCyclicSubextension.instNormalSubtypeMemSubgroupFieldExtensionSubgroupField _root_.ClassFormation.FiniteGaloisSubextension.extensionSubgroup_normalInstance _root_.ClassFormation.FiniteGaloisSubextension.extensionSubgroup_over_intermediate_normalInstance _root_.ClassFormation.FiniteGaloisSubextension.intermediateField_normalInstance _root_.ClassFormation.FiniteUnramifiedCyclicExtension.instNormalSubtypeMemSubgroupFieldExtensionSubgroupField _root_.ClassFormation.conjugateExtension_normal _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalClassFieldTheory.extensionSubgroupBase_normal _root_.LocalClassFieldTheory.finiteGaloisExtensionSubgroupOfEmbedding_normal _root_.LocalFieldTheory.DiscreteValuationField.finite_nsmulAddKernel_padicInt_pi _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LubinTate.compatibleGroupFamiliesCommGroup _root_.LubinTate.compatibleGroupFamiliesGroup _root_.OAI.PrimeDegreePackets.boundedRealFields_finite _root_.OAI.PrimeDegreePackets.diagonalLogAction _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionResidueField.instField _root_.RamificationTheory.HilbertRamification.ValuationSubring.inertiaGroup_normal _root_.RamificationTheory.HilbertRamification.ValuationSubring.ramificationGroupInInertiaAut_normal _root_.RamificationTheory.HilbertRamification.ValuationSubring.selectedResidueField.instAlgebra _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.RelativeIdeleGroup.relativeIdeleMulAction _root_.ValuationTheory.DiscreteValuationField.DVF.maximalIdealPowSuccQuotModule _root_.ValuationTheory.DiscreteValuationField.DVF.residueField.field _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.isDomain _root_.CyclicCohomology.binaryCoefficientFamilyCommGroup _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.relativeAdeleRingIntermediateAlgebra _root_.relativeAdeleRingTopIntermediateAlgebra
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

/-- The Galois group of `N/K` is finite. -/
theorem finite_fullSUnitKummerExtension_galois
    {Omega : Type*} [Field Omega] [Algebra K Omega]
    [IsSepClosure K Omega]
    (n : ℕ+) (hn : ((n : ℕ) : K) ≠ 0)
    (hmu : (primitiveRoots (n : ℕ) K).Nonempty)
    (S : Finset (HeightOneSpectrum (𝓞 K))) :
    Finite
      Gal(fullSUnitKummerExtension
        (K := K) (Omega := Omega) n S/K) := by
  let _ : NeZero (n : ℕ) := ⟨n.ne_zero⟩
  let E :=
    fullSUnitKummerExtension (K := K) (Omega := Omega) n S
  let Q :=
    KummerTheory.RestrictedRadicalQuotient
      n (fullSUnitKummerSubgroup (K := K) n S)
  let _ : Finite Q :=
    finite_fullSUnitRadicalQuotient (K := K) n S
  let _ : Finite (Q →* KummerTheory.nthRootsSubgroup E (n : ℕ)) :=
    Finite.of_injective
      (fun chi : Q →* KummerTheory.nthRootsSubgroup E (n : ℕ) =>
        (chi : Q → KummerTheory.nthRootsSubgroup E (n : ℕ)))
      DFunLike.coe_injective
  let e :
      Gal(E/K) ≃*
        (Q →* KummerTheory.nthRootsSubgroup E (n : ℕ)) :=
    KummerTheory.kummerRadicalExtensionRestrictedTransposeMulEquiv
      n hn hmu (fullSUnitKummerSubgroup (K := K) n S)
  exact Finite.of_equiv
    (Q →* KummerTheory.nthRootsSubgroup E (n : ℕ))
    e.symm.toEquiv

/-- The Galois group of `N/K` has cardinality `n ^ s`. -/
theorem card_fullSUnitKummerExtension_galois
    {Omega : Type*} [Field Omega] [Algebra K Omega]
    [IsSepClosure K Omega]
    (n : ℕ+) (hn : ((n : ℕ) : K) ≠ 0)
    (hmu : (primitiveRoots (n : ℕ) K).Nonempty)
    (S : Finset (HeightOneSpectrum (𝓞 K))) :
    Nat.card
        Gal(fullSUnitKummerExtension
          (K := K) (Omega := Omega) n S/K) =
      (n : ℕ) ^ totalPlaceCard (K := K) S := by
  let _ : NeZero (n : ℕ) := ⟨n.ne_zero⟩
  let E :=
    fullSUnitKummerExtension (K := K) (Omega := Omega) n S
  let Q :=
    KummerTheory.RestrictedRadicalQuotient
      n (fullSUnitKummerSubgroup (K := K) n S)
  let e :
      Gal(E/K) ≃*
        (Q →* KummerTheory.nthRootsSubgroup E (n : ℕ)) :=
    KummerTheory.kummerRadicalExtensionRestrictedTransposeMulEquiv
      n hn hmu (fullSUnitKummerSubgroup (K := K) n S)
  obtain ⟨dual⟩ :=
    KummerTheory.finiteNthRootsCharacterDuality
      (G := Q) (K := K) (L := E) n hmu
      (KummerTheory.restrictedRadicalQuotient_pow_eq_one
        n (fullSUnitKummerSubgroup (K := K) n S))
  calc
    Nat.card Gal(E/K) =
        Nat.card (Q →* KummerTheory.nthRootsSubgroup E (n : ℕ)) :=
      Nat.card_congr e.toEquiv
    _ = Nat.card Q := Nat.card_congr dual.toEquiv
    _ = (n : ℕ) ^ totalPlaceCard (K := K) S :=
      card_fullSUnitRadicalQuotient (K := K) n S hmu

/-- Every automorphism of the full `S`-unit Kummer extension has
`n`-th power one. -/
theorem fullSUnitKummerExtension_galois_pow_eq_one
    {Omega : Type*} [Field Omega] [Algebra K Omega]
    [IsSepClosure K Omega]
    (n : ℕ+)
    (hmu : (primitiveRoots (n : ℕ) K).Nonempty)
    (S : Finset (HeightOneSpectrum (𝓞 K)))
    (sigma :
      Gal(fullSUnitKummerExtension
        (K := K) (Omega := Omega) n S/K)) :
    sigma ^ (n : ℕ) = 1 :=
  KummerTheory.kummerRadicalExtension_galois_pow_eq_one
    n hmu (fullSUnitKummerSubgroup (K := K) n S).1 sigma

/-- A chosen Kummer-duality equivalence identifies the Galois group of the full
`S`-unit extension with the actual `S`-unit quotient. -/
noncomputable def
    chosenFullSUnitKummerExtensionGaloisEquivSUnitQuotient
    {Omega : Type*} [Field Omega] [Algebra K Omega]
    [IsSepClosure K Omega]
    (n : ℕ+) (hn : ((n : ℕ) : K) ≠ 0)
    (hmu : (primitiveRoots (n : ℕ) K).Nonempty)
    (S : Finset (HeightOneSpectrum (𝓞 K))) :
    Gal(fullSUnitKummerExtension
        (K := K) (Omega := Omega) n S/K) ≃*
      SUnitGroup (K := K) S ⧸
        (powMonoidHom (n : ℕ) :
          SUnitGroup (K := K) S →*
            SUnitGroup (K := K) S).range := by
  let Q :=
    KummerTheory.RestrictedRadicalQuotient
      n (fullSUnitKummerSubgroup (K := K) n S)
  let E :=
    fullSUnitKummerExtension
      (K := K) (Omega := Omega) n S
  let e :
      Gal(E/K) ≃*
        (Q →* KummerTheory.nthRootsSubgroup E (n : ℕ)) :=
    KummerTheory.kummerRadicalExtensionRestrictedTransposeMulEquiv
      n hn hmu (fullSUnitKummerSubgroup (K := K) n S)
  let dual :
      (Q →* KummerTheory.nthRootsSubgroup E (n : ℕ)) ≃* Q :=
    Classical.choice <|
      KummerTheory.finiteNthRootsCharacterDuality
        (G := Q) (K := K) (L := E) n hmu
        (KummerTheory.restrictedRadicalQuotient_pow_eq_one
          n (fullSUnitKummerSubgroup (K := K) n S))
  exact (e.trans dual).trans
    (sUnitNthPowerQuotientEquivFullSUnitRadicalQuotient
      (K := K) n S).symm

/-- `ZMod n` coordinates derived from the chosen duality equivalence on the Galois
group of the full `S`-unit Kummer extension. -/
noncomputable def fullSUnitKummerExtensionGaloisCoordinates
    {Omega : Type*} [Field Omega] [Algebra K Omega]
    [IsSepClosure K Omega]
    (n : ℕ+) (hn : ((n : ℕ) : K) ≠ 0)
    (hmu : (primitiveRoots (n : ℕ) K).Nonempty)
    (S : Finset (HeightOneSpectrum (𝓞 K))) :
    Gal(fullSUnitKummerExtension
        (K := K) (Omega := Omega) n S/K) ≃*
      Multiplicative (ZMod (n : ℕ)) ×
        Multiplicative
          (Fin (SUnitGroup.logRank (K := K) S) →
            ZMod (n : ℕ)) :=
  (chosenFullSUnitKummerExtensionGaloisEquivSUnitQuotient
    (K := K) (Omega := Omega) n hn hmu S).trans
      (sUnitNthPowerQuotientCoordinates
        (K := K) S n hmu)

/-- With its canonical exponent-`n` module structure, the full
`S`-unit Kummer Galois group is a free `ZMod n`-module. -/
theorem fullSUnitKummerExtension_galois_moduleFree
    {Omega : Type*} [Field Omega] [Algebra K Omega]
    [IsSepClosure K Omega]
    (n : ℕ+) (hn : ((n : ℕ) : K) ≠ 0)
    (hmu : (primitiveRoots (n : ℕ) K).Nonempty)
    (S : Finset (HeightOneSpectrum (𝓞 K))) :
    letI : IsMulCommutative
        Gal(fullSUnitKummerExtension
          (K := K) (Omega := Omega) n S/K) :=
      KummerTheory.kummerRadicalExtension_isMulCommutative
        n hmu (fullSUnitKummerSubgroup (K := K) n S).1
    letI : Module (ZMod (n : ℕ))
        (Additive
          Gal(fullSUnitKummerExtension
            (K := K) (Omega := Omega) n S/K)) :=
      additiveZModModuleOfPowEqOne (n : ℕ)
        (fullSUnitKummerExtension_galois_pow_eq_one
          (K := K) (Omega := Omega) n hmu S)
    Module.Free (ZMod (n : ℕ))
      (Additive
        Gal(fullSUnitKummerExtension
          (K := K) (Omega := Omega) n S/K)) := by
  let G :=
    Gal(fullSUnitKummerExtension
      (K := K) (Omega := Omega) n S/K)
  let _ : IsMulCommutative G :=
    KummerTheory.kummerRadicalExtension_isMulCommutative
      n hmu (fullSUnitKummerSubgroup (K := K) n S).1
  let _ : Module (ZMod (n : ℕ)) (Additive G) :=
    additiveZModModuleOfPowEqOne (n : ℕ)
      (fullSUnitKummerExtension_galois_pow_eq_one
        (K := K) (Omega := Omega) n hmu S)
  let e :
      Additive G ≃ₗ[ZMod (n : ℕ)]
        ZMod (n : ℕ) ×
          (Fin (SUnitGroup.logRank (K := K) S) →
            ZMod (n : ℕ)) :=
    additiveCoordinatesLinearEquiv (n : ℕ)
      (fullSUnitKummerExtensionGaloisCoordinates
        (K := K) (Omega := Omega) n hn hmu S)
  exact Module.Free.of_equiv e.symm

end KummerTheory
end
end

section
-- module Solutions.OAIQ244_DUKE.LocalClassFieldTheory_ClassFormation_ArchimedeanNormQuotient
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.PrimeDegreePackets.diagonalLogAction _root_.OAI.PrimeDegreePackets.instNonemptyLeafTestSpace _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.CyclicCohomology.binaryCoefficientFamilyCommGroup _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen
attribute [-simp] _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.CyclicCohomology.fixedPiEquiv_apply_coe _root_.CyclicCohomology.herbrandH0EquivariantMulEquiv_mk _root_.IsDiscreteValuationRing.addVal_ringEquiv _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.OAI.PrimeDegreePackets.ThetaConstruction.schwartzCM_apply _root_.infinitePlace_mult_smul
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

/-- A one-element acting group has trivial degree-zero Herbrand
cohomology. -/
theorem herbrandH0_card_eq_one_of_group_card_eq_one
    {G A : Type*}
    [Group G] [Fintype G]
    [CommGroup A] [MulDistribMulAction G A]
    (hG : Nat.card G = 1) :
    Nat.card (HerbrandH0 G A) = 1 := by
  let : Subsingleton G :=
    (Nat.card_eq_one_iff_unique.mp hG).1
  let : Subsingleton (HerbrandH0 G A) :=
    herbrandH0_subsingleton_of_fixed_le_tateNormSubgroup
      (G := G) (A := A) (by
        intro a ha
        refine ⟨a, ?_⟩
        rw [tateNormHom_apply]
        unfold tateNorm
        classical
        have huniv : (Finset.univ : Finset G) = {1} := by
          ext g
          simp [Subsingleton.elim g 1]
        rw [huniv]
        simp)
  exact Nat.card_unique

end LocalClassFieldTheory
end
end

section
-- module Solutions.OAIQ244_DUKE.LocalClassFieldTheory_Finite_LocalReciprocity_GeneralTowerNaturality
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

/-!
# Restriction naturality in an arbitrary finite abelian tower

The fixed-separable-closure form of finite local reciprocity naturality is
transported here to an arbitrary tower `K ⊂ E ⊂ L`.  The two extensions are
realized compatibly in the chosen separable closure by first embedding `L`
and then restricting that embedding to `E`.  Abstract norm--residue
naturality then becomes the actual restriction homomorphism
`Gal(L/K) → Gal(E/K)`.
-/

noncomputable section

namespace LocalClassFieldTheory

open LocalFieldTheory RamificationTheory CyclicCohomology KummerTheory
open ClassFormation LocalClassFieldTheory
open scoped IsMulCommutative

abbrev towerAbsoluteGalois (K : Type) [Field K] :=
  intrinsicAbsoluteGalois K

end LocalClassFieldTheory
end
end

section
-- module Solutions.OAIQ244_DUKE.LocalField_NonarchimedeanLocalField_UnramifiedFrobenius
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.LubinTate.Valuations.exponentialValuationSubringIsLocalRing _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionFixedSubring.instIsLocalRing _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionResidueField.instField _root_.RamificationTheory.HilbertRamification.ValuationSubring.selectedResidueField.instAlgebra _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen _root_.relativeAdeleRingIntermediateAlgebra _root_.relativeAdeleRingTopIntermediateAlgebra
attribute [-simp] _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.IsDiscreteValuationRing.addVal_ringEquiv _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.OAI.PrimeDegreePackets.ThetaConstruction.schwartzCM_apply _root_.infinitePlace_mult_smul
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

namespace LocalFieldTheory

/-!
# Actual unramified Frobenius

The arithmetic Frobenius is first defined as finite-field Frobenius on the
residue extension, then lifted to `Gal(L / K)` through the canonical
residue-action isomorphism for a finite unramified extension.
-/

noncomputable section

universe u

open scoped ValuativeRel
open _root_.LocalFieldTheory.IsNonarchimedeanLocalField

/-- For an unramified valued extension, residue arithmetic Frobenius has order equal to the
field-extension degree. -/
theorem orderOf_residueExtensionArithmeticFrobeniusOfUnramifiedValuation
    (K L : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] [Field L] [ValuativeRel L]
    [TopologicalSpace L] [IsNonarchimedeanLocalField L] [Algebra K L]
    [FiniteDimensional K L]
    [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]
    [Module.Finite 𝒪[K] 𝒪[L]]
    [LocalFieldTheory.IsNonarchimedeanLocalField.IsUnramifiedValuedExtension K L] :
    orderOf (residueExtensionArithmeticFrobeniusOfValuationExtension K L) =
      Module.finrank K L := by
  rw [orderOf_residueExtensionArithmeticFrobeniusOfValuationExtension K L,
    LocalFieldTheory.IsNonarchimedeanLocalField.unramifiedValuation_residue_finrank_eq_finrank K L]

/-- Actual arithmetic Frobenius in `Gal(L / K)`, obtained by lifting the residue
finite-field Frobenius through the already constructed unramified residue-action
isomorphism. -/
noncomputable def arithmeticFrobeniusOfUnramifiedValuation
    (K L : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] [Field L] [ValuativeRel L]
    [TopologicalSpace L] [IsNonarchimedeanLocalField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]
    [IsIntegralClosure 𝒪[L] 𝒪[K] L] [Module.Finite 𝒪[K] 𝒪[L]]
    [LocalFieldTheory.IsNonarchimedeanLocalField.IsUnramifiedValuedExtension K L] :
    Gal(L / K) :=
  (galoisGroupEquivResidueAlgEquivOfUnramifiedValuationOfIsIntegralClosure K L).symm
    (residueExtensionArithmeticFrobeniusOfValuationExtension K L)

/-- The unramified Galois-residue equivalence lifts residue arithmetic Frobenius to field arithmetic
Frobenius. -/
@[simp]
theorem galoisGroupEquivResidueAlgEquivOfUnramifiedValuationOfIsIntegralClosure_arithmeticFrobenius
    (K L : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] [Field L] [ValuativeRel L]
    [TopologicalSpace L] [IsNonarchimedeanLocalField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]
    [IsIntegralClosure 𝒪[L] 𝒪[K] L] [Module.Finite 𝒪[K] 𝒪[L]]
    [LocalFieldTheory.IsNonarchimedeanLocalField.IsUnramifiedValuedExtension K L] :
    galoisGroupEquivResidueAlgEquivOfUnramifiedValuationOfIsIntegralClosure K L
        (arithmeticFrobeniusOfUnramifiedValuation K L) =
      residueExtensionArithmeticFrobeniusOfValuationExtension K L := by
  simp [arithmeticFrobeniusOfUnramifiedValuation]

/-- The residue action of field arithmetic Frobenius is residue arithmetic Frobenius. -/
@[simp]
theorem galoisGroupResidueAlgEquivOfIsIntegralClosure_arithmeticFrobenius
    (K L : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] [Field L] [ValuativeRel L]
    [TopologicalSpace L] [IsNonarchimedeanLocalField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]
    [IsIntegralClosure 𝒪[L] 𝒪[K] L] [Module.Finite 𝒪[K] 𝒪[L]]
    [LocalFieldTheory.IsNonarchimedeanLocalField.IsUnramifiedValuedExtension K L] :
    galoisGroupResidueAlgEquivOfIsIntegralClosure K L
        (arithmeticFrobeniusOfUnramifiedValuation K L) =
      residueExtensionArithmeticFrobeniusOfValuationExtension K L := by
  simpa [galoisGroupEquivResidueAlgEquivOfUnramifiedValuationOfIsIntegralClosure_apply]
    using
      galoisGroupEquivResidueAlgEquivOfUnramifiedValuationOfIsIntegralClosure_arithmeticFrobenius
        K L

/-- Arithmetic Frobenius in an unramified Galois extension has order equal to the extension degree. -/
theorem orderOf_arithmeticFrobeniusOfUnramifiedValuation
    (K L : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] [Field L] [ValuativeRel L]
    [TopologicalSpace L] [IsNonarchimedeanLocalField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]
    [IsIntegralClosure 𝒪[L] 𝒪[K] L] [Module.Finite 𝒪[K] 𝒪[L]]
    [LocalFieldTheory.IsNonarchimedeanLocalField.IsUnramifiedValuedExtension K L] :
    orderOf (arithmeticFrobeniusOfUnramifiedValuation K L) =
      Module.finrank K L := by
  have horder :=
    (galoisGroupEquivResidueAlgEquivOfUnramifiedValuationOfIsIntegralClosure K L).orderOf_eq
      (arithmeticFrobeniusOfUnramifiedValuation K L)
  rw [galoisGroupEquivResidueAlgEquivOfUnramifiedValuationOfIsIntegralClosure_arithmeticFrobenius]
    at horder
  exact horder.symm.trans
    (orderOf_residueExtensionArithmeticFrobeniusOfUnramifiedValuation K L)

/-- Arithmetic Frobenius generates the Galois group of a finite unramified extension. -/
theorem arithmeticFrobeniusOfUnramifiedValuation_generates
    (K L : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] [Field L] [ValuativeRel L]
    [TopologicalSpace L] [IsNonarchimedeanLocalField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]
    [IsIntegralClosure 𝒪[L] 𝒪[K] L] [Module.Finite 𝒪[K] 𝒪[L]]
    [LocalFieldTheory.IsNonarchimedeanLocalField.IsUnramifiedValuedExtension K L] :
    ∀ σ : Gal(L / K),
      σ ∈ Subgroup.zpowers (arithmeticFrobeniusOfUnramifiedValuation K L) := by
  intro σ
  let e := galoisGroupEquivResidueAlgEquivOfUnramifiedValuationOfIsIntegralClosure K L
  rcases residueExtensionArithmeticFrobeniusOfValuationExtension_generates K L (e σ) with
    ⟨i, hi⟩
  refine ⟨i, ?_⟩
  apply e.injective
  simpa [e, map_zpow,
    galoisGroupEquivResidueAlgEquivOfUnramifiedValuationOfIsIntegralClosure_arithmeticFrobenius]
    using hi

/-- The subgroup of integral powers of arithmetic Frobenius is the full Galois group. -/
theorem arithmeticFrobeniusOfUnramifiedValuation_zpowers_eq_top
    (K L : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] [Field L] [ValuativeRel L]
    [TopologicalSpace L] [IsNonarchimedeanLocalField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]
    [IsIntegralClosure 𝒪[L] 𝒪[K] L] [Module.Finite 𝒪[K] 𝒪[L]]
    [LocalFieldTheory.IsNonarchimedeanLocalField.IsUnramifiedValuedExtension K L] :
    Subgroup.zpowers (arithmeticFrobeniusOfUnramifiedValuation K L) = ⊤ := by
  ext σ
  simp [arithmeticFrobeniusOfUnramifiedValuation_generates K L σ]

/-- The generator-normalized ZMod model of the actual unramified Galois group.
Unlike `galoisGroupEquivZModOfUnramifiedValuation`, this quotient construction uses
the specified arithmetic Frobenius as the generator, following the normalized Frobenius construction before the uniformizer/Frobenius calculation. -/
noncomputable def galoisGroupEquivZModOfUnramifiedValuationNormalized
    (K L : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] [Field L] [ValuativeRel L]
    [TopologicalSpace L] [IsNonarchimedeanLocalField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]
    [IsIntegralClosure 𝒪[L] 𝒪[K] L] [Module.Finite 𝒪[K] 𝒪[L]]
    [LocalFieldTheory.IsNonarchimedeanLocalField.IsUnramifiedValuedExtension K L] :
    Gal(L / K) ≃* Multiplicative (ZMod (Module.finrank K L)) :=
  (zmodCyclicMulEquivOfGenerator
    (arithmeticFrobeniusOfUnramifiedValuation K L)
    (orderOf_arithmeticFrobeniusOfUnramifiedValuation K L)
    (arithmeticFrobeniusOfUnramifiedValuation_zpowers_eq_top K L)).symm

/-- The normalized equivalence from the unramified Galois group to `ZMod` sends arithmetic Frobenius
to one. -/
@[simp]
theorem galoisGroupEquivZModOfUnramifiedValuationNormalized_arithmeticFrobenius
    (K L : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] [Field L] [ValuativeRel L]
    [TopologicalSpace L] [IsNonarchimedeanLocalField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]
    [IsIntegralClosure 𝒪[L] 𝒪[K] L] [Module.Finite 𝒪[K] 𝒪[L]]
    [LocalFieldTheory.IsNonarchimedeanLocalField.IsUnramifiedValuedExtension K L] :
    galoisGroupEquivZModOfUnramifiedValuationNormalized K L
        (arithmeticFrobeniusOfUnramifiedValuation K L) =
      Multiplicative.ofAdd (1 : ZMod (Module.finrank K L)) := by
  let e :=
    zmodCyclicMulEquivOfGenerator
      (arithmeticFrobeniusOfUnramifiedValuation K L)
      (orderOf_arithmeticFrobeniusOfUnramifiedValuation K L)
      (arithmeticFrobeniusOfUnramifiedValuation_zpowers_eq_top K L)
  change e.symm (arithmeticFrobeniusOfUnramifiedValuation K L) =
    Multiplicative.ofAdd (1 : ZMod (Module.finrank K L))
  rw [← zmodCyclicMulEquivOfGenerator_apply_one
    (arithmeticFrobeniusOfUnramifiedValuation K L)
    (orderOf_arithmeticFrobeniusOfUnramifiedValuation K L)
    (arithmeticFrobeniusOfUnramifiedValuation_zpowers_eq_top K L)]
  exact e.symm_apply_apply _

/-- Power form of the generator-normalized Frobenius model.  This is the
Frobenius-side model used before composing with the
valuation quotient. -/
@[simp]
theorem galoisGroupEquivZModOfUnramifiedValuationNormalized_arithmeticFrobenius_zpow
    (K L : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] [Field L] [ValuativeRel L]
    [TopologicalSpace L] [IsNonarchimedeanLocalField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]
    [IsIntegralClosure 𝒪[L] 𝒪[K] L] [Module.Finite 𝒪[K] 𝒪[L]]
    [LocalFieldTheory.IsNonarchimedeanLocalField.IsUnramifiedValuedExtension K L] (m : Int) :
    galoisGroupEquivZModOfUnramifiedValuationNormalized K L
        ((arithmeticFrobeniusOfUnramifiedValuation K L) ^ m) =
      Multiplicative.ofAdd (m : ZMod (Module.finrank K L)) := by
  rw [map_zpow, galoisGroupEquivZModOfUnramifiedValuationNormalized_arithmeticFrobenius]
  rw [← ofAdd_zsmul]
  simp [zsmul_eq_mul]

end
end LocalFieldTheory
end

section
-- module Solutions.OAIQ244_DUKE.LocalClassFieldTheory_Finite_Unramified_Cohomology
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.PrimeDegreePackets.instNonemptyLeafTestSpace _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionResidueField.instField _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.CyclicCohomology.binaryCoefficientFamilyCommGroup _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen
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

theorem herbrandHMinusOne_subsingleton_of_h0_subsingleton_of_quotient_eq_one
    (G A : Type u) [Group G] [Fintype G] [CommGroup A]
    [MulDistribMulAction G A] (g : G)
    [Finite (HerbrandH0 G A)] [Finite (HerbrandHMinusOne G A g)]
    [Subsingleton (HerbrandH0 G A)]
    (hquot : herbrandQuotient (G := G) (A := A) g = 1) :
    Subsingleton (HerbrandHMinusOne G A g) := by
  have hzero : Nat.card (HerbrandH0 G A) = 1 := by
    exact Nat.card_unique
  have hden : ((Nat.card (HerbrandHMinusOne G A g) : ℚ) ≠ 0) :=
    Nat.cast_ne_zero.mpr
      (Finite.card_pos (α := HerbrandHMinusOne G A g)).ne'
  have hcardQ : (1 : ℚ) = Nat.card (HerbrandHMinusOne G A g) := by
    unfold herbrandQuotient at hquot
    rw [hzero] at hquot
    exact (div_eq_one_iff_eq hden).1 hquot
  have hcard : Nat.card (HerbrandHMinusOne G A g) = 1 := by
    exact_mod_cast hcardQ.symm
  exact (Nat.card_eq_one_iff_unique.mp hcard).1

end LocalClassFieldTheory
end
end


