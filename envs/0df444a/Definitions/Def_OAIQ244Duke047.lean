-- Prove2me | Definitions.Def_OAIQ244Duke047
-- name    : OAIQ244Duke047
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-13T06:54:53.077846+00:00
-- url     : https://prove2.me/theorems/6f41384d-32e7-4512-9a43-602a8b9e716d
-- title:
--   Definitions bundle OAIQ244Duke047 of the split of OpenAI, Equidistribution of Prime-Degree Torus Packets with Arbitrary Local Type
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.DukePrimeDegree.prime_degree_packet_measure_equidistribution_unconditional` and `OAI.DukePrimeDegree.prime_degree_packet_measures_tendsto_haar_unconditional`, carved from OpenAI's openai/math development (OpenAI, *Equidistribution of Prime-Degree Torus Packets with Arbitrary Local Type*, OpenAI Math Release, September 24, 2026, result family 15, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 198 declarations of OpenAI's Lean: 31 definitions, 3 inductive types or structures, 10 instances and 154 theorems. The definitions and types are `LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.iwasawaGlobalInverseLimitCarrier`, `LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.fieldUnitUniformizerUnitPart`, `LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.fieldUnitsEquivRootsPrincipalUnitsUniformizer_of_completeDVF`, `LocalFieldTheory.DiscreteValuationField.Examples.Qp.padicCompleteDVF`, `LocalFieldTheory.DiscreteValuationField.LocalField.MixedIntegralAlgebraContext`, `LocalFieldTheory.DiscreteValuationField.LocalField.MixedIntegralLatticeContext`, `LocalFieldTheory.DiscreteValuationField.LocalField.MixedWithZeroValuationContext`, `LocalFieldTheory.DiscreteValuationField.LocalField.higherPrincipalUnitAddToFirst`, `LocalFieldTheory.DiscreteValuationField.LocalField.higherPrincipalUnitLinearEquivPadicSubmodule`, `LocalFieldTheory.DiscreteValuationField.LocalField.higherPrincipalUnitPadicModule`, `LocalFieldTheory.DiscreteValuationField.LocalField.higherPrincipalUnitPadicSMul`, `LocalFieldTheory.DiscreteValuationField.LocalField.higherPrincipalUnitPadicSubmodule`, `LocalFieldTheory.DiscreteValuationField.LocalField.higherPrincipalUnitToFirst`, `LocalFieldTheory.DiscreteValuationField.LocalField.mixedWithZeroValuationContext`, `LocalFieldTheory.DiscreteValuationField.LocalField.padicIntFieldAlgebra`, `LocalFieldTheory.DiscreteValuationField.LocalField.padicIntToValuationSubring`, `LocalFieldTheory.DiscreteValuationField.LocalField.padicIntValuationSubringAlgebra`, `LocalFieldTheory.DiscreteValuationField.MultiplicativeIntegerValuation.completeDVFOfWithZeroValuation`, `LocalFieldTheory.DiscreteValuationField.MultiplicativeIntegerValuation.fieldUnitDecompositionLogHomOfPrincipalUnitHom`, `LocalFieldTheory.DiscreteValuationField.MultiplicativeIntegerValuation.fieldUnitDecompositionLogHomWithUniformizerValue`, `LocalFieldTheory.DiscreteValuationField.MultiplicativeIntegerValuation.fieldUnitLogHomOfPrincipalUnitHom`, `LocalFieldTheory.DiscreteValuationField.MultiplicativeIntegerValuation.fieldUnitLogHomWithUniformizerValue`, `LocalFieldTheory.DiscreteValuationField.MultiplicativeIntegerValuation.principalUnitExpSeriesHomOfMaximalIdealPowOfWithZeroValuationScaled`, `LocalFieldTheory.DiscreteValuationField.MultiplicativeIntegerValuation.principalUnitExpSeriesHomOfWithZeroValuation`, `LocalFieldTheory.DiscreteValuationField.MultiplicativeIntegerValuation.principalUnitExpSeriesOfMaximalIdealPowOfWithZeroValuationScaled`, `LocalFieldTheory.DiscreteValuationField.MultiplicativeIntegerValuation.principalUnitExpSeriesOfWithZeroValuation`, `LocalFieldTheory.DiscreteValuationField.MultiplicativeIntegerValuation.principalUnitLogPartialSumOfWithZeroValuation`, `LocalFieldTheory.DiscreteValuationField.MultiplicativeIntegerValuation.principalUnitLogSeriesHomOfTendstoFieldDefect_ofWithZeroValuation`, `LocalFieldTheory.DiscreteValuationField.MultiplicativeIntegerValuation.principalUnitLogSeriesHomOfWithZeroValuationScaled`, `LocalFieldTheory.DiscreteValuationField.MultiplicativeIntegerValuation.principalUnitLogSeriesOfWithZeroValuation`, `LocalFieldTheory.DiscreteValuationField.MultiplicativeIntegerValuation.principalUnitSubOneOfWithZeroValuation`, `LocalFieldTheory.DiscreteValuationField.fieldNormFiltrationPreimageClassInQuotient`, `LocalFieldTheory.DiscreteValuationField.fieldNormFiltrationQuotientModuloPreimageClassEquivRange`, `LocalFieldTheory.Padic.integerRingEquivPadicDVRValuationSubring`.
--
--   **Sources.** They come from these modules of lean/OAI/NumberTheory, in whole or in part: `GlobalClassFieldTheory_ClassFieldAxiom_IdeleClassPowerLocalUnitQuotient_LocalResidueArithmetic`, `LocalField_Analytic_DenominatorValuation`, `LocalField_Analytic_FieldUnitLogExtension`, `LocalField_Analytic_LogExpAdditivity`, `LocalField_Analytic_LogExpComposition`, `LocalField_Analytic_LogExpContinuity`, `LocalField_Analytic_LogExpSeries_ExpConvergence`, `LocalField_Analytic_LogExpSeries_Homomorphisms`, `LocalField_Analytic_LogExpSeries_InverseEstimates`, `LocalField_Analytic_LogExpSeries_LogConvergence`, `LocalField_Analytic_LogExpSeries_PrincipalUnitExp`, `LocalField_Analytic_LogExpSeries_PrincipalUnitLog`, `LocalField_Analytic_LogExpSeries_SeriesTerms`, `LocalField_DiscreteValuationField_FieldNorm`, `LocalField_DiscreteValuationField_FieldUnitDecomposition`, `LocalField_DiscreteValuationField_IwasawaPrincipalUnits`, `LocalField_DiscreteValuationField_MixedCharacteristicStructure_DeepPrincipalUnits`, `LocalField_DiscreteValuationField_MixedCharacteristicStructure_IntegralLattice`, `LocalField_DiscreteValuationField_PadicField`, `LocalField_DiscreteValuationField_PrincipalUnitPadicAction_AdicPadicModule`, `LocalField_DiscreteValuationField_PrincipalUnitPadicAction_ProdiscretePadicModule`, `LocalField_DiscreteValuationField_PrincipalUnitPadicAction_WithZeroValuationTopology`, `LocalField_Padic_PrincipalUnits`, `LubinTate_FormalModule_StandardFormalGroup`.
--
--   **Imports.** It imports the bundles `OAIQ244Duke038`, `OAIQ244Duke039`, `OAIQ244Duke040` and `OAIQ244Duke043` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ244Duke054`, `OAIQ244Duke055`, `OAIQ244Duke058`, `OAIQ244Duke059`, `OAIQ244Duke060` and `OAIQ244Duke061`.
-- source:
--   OpenAI, Equidistribution of Prime-Degree Torus Packets with Arbitrary Local Type, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 15; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Equidistribution-of-Prime-Degree-Torus-Packets-with-Arbitrary-Local-Type-September-24-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/NumberTheory at commit 7ef5c0c

import Mathlib
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.CharP.Algebra
import Mathlib.Algebra.CharP.Lemmas
import Mathlib.Algebra.CharP.Subring
import Mathlib.Algebra.EuclideanDomain.Basic
import Mathlib.Algebra.Group.Hom.Basic
import Mathlib.Algebra.Group.Int.TypeTags
import Mathlib.Algebra.Group.Subgroup.Basic
import Mathlib.Algebra.Group.Subgroup.Ker
import Mathlib.Algebra.Group.Units.Equiv
import Mathlib.Algebra.Group.Units.Hom
import Mathlib.Algebra.Module.MinimalAxioms
import Mathlib.Algebra.Module.PID
import Mathlib.Algebra.Module.Shrink
import Mathlib.Algebra.Module.ZMod
import Mathlib.Algebra.Order.Field.Power
import Mathlib.Algebra.Order.Group.Cyclic
import Mathlib.Algebra.Order.Ring.IsNonarchimedean
import Mathlib.Algebra.Polynomial.FieldDivision
import Mathlib.Algebra.Ring.Pi
import Mathlib.Algebra.Ring.Subring.Basic
import Mathlib.Algebra.Ring.TransferInstance
import Mathlib.Analysis.AbsoluteValue.Equivalence
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Data.Finset.Finsupp
import Mathlib.Data.Int.ModEq
import Mathlib.Data.Int.WithZero
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Rat.Cast.CharZero
import Mathlib.Data.Rat.Lemmas
import Mathlib.Data.ZMod.QuotientGroup
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.FieldTheory.Perfect
import Mathlib.FieldTheory.PrimeField
import Mathlib.GroupTheory.Index
import Mathlib.GroupTheory.QuotientGroup.Basic
import Mathlib.GroupTheory.SpecificGroups.Cyclic
import Mathlib.LinearAlgebra.Determinant
import Mathlib.LinearAlgebra.Dimension.Basic
import Mathlib.LinearAlgebra.Dimension.Localization
import Mathlib.LinearAlgebra.Dimension.Torsion.Finite
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import Mathlib.LinearAlgebra.Finsupp.VectorSpace
import Mathlib.LinearAlgebra.FreeModule.IdealQuotient
import Mathlib.LinearAlgebra.Isomorphisms
import Mathlib.LinearAlgebra.Pi
import Mathlib.LinearAlgebra.TensorProduct.RightExactness
import Mathlib.NumberTheory.LocalField.Basic
import Mathlib.NumberTheory.NumberField.AdeleRing
import Mathlib.NumberTheory.NumberField.Completion.FinitePlace
import Mathlib.NumberTheory.NumberField.ProductFormula
import Mathlib.NumberTheory.Ostrowski
import Mathlib.NumberTheory.Padics.PadicNumbers
import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Mathlib.NumberTheory.Padics.ProperSpace
import Mathlib.NumberTheory.Padics.RingHoms
import Mathlib.NumberTheory.Padics.ValuativeRel
import Mathlib.NumberTheory.Padics.WithVal
import Mathlib.NumberTheory.RamificationInertia.Inertia
import Mathlib.NumberTheory.RamificationInertia.Ramification
import Mathlib.Order.Filter.AtTopBot.Tendsto
import Mathlib.RingTheory.AdicCompletion.AsTensorProduct
import Mathlib.RingTheory.AdicCompletion.Functoriality
import Mathlib.RingTheory.AdicCompletion.Noetherian
import Mathlib.RingTheory.AdicCompletion.Topology
import Mathlib.RingTheory.Algebraic.Integral
import Mathlib.RingTheory.DedekindDomain.IntegralClosure
import Mathlib.RingTheory.DiscreteValuationRing.Basic
import Mathlib.RingTheory.DiscreteValuationRing.TFAE
import Mathlib.RingTheory.Filtration
import Mathlib.RingTheory.Finiteness.Finsupp
import Mathlib.RingTheory.FormalGroup.Basic
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Ideal.GoingUp
import Mathlib.RingTheory.Ideal.IsPrincipalPowQuotient
import Mathlib.RingTheory.Ideal.Quotient.Index
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.RingTheory.IntegralClosure.IsIntegralClosure.Basic
import Mathlib.RingTheory.LaurentSeries
import Mathlib.RingTheory.LocalRing.Basic
import Mathlib.RingTheory.LocalRing.ResidueField.Basic
import Mathlib.RingTheory.Localization.Away.Basic
import Mathlib.RingTheory.MvPowerSeries.Expand
import Mathlib.RingTheory.MvPowerSeries.Order
import Mathlib.RingTheory.MvPowerSeries.Substitution
import Mathlib.RingTheory.MvPowerSeries.Trunc
import Mathlib.RingTheory.Nakayama
import Mathlib.RingTheory.Norm.Transitivity
import Mathlib.RingTheory.Polynomial.Cyclotomic.Roots
import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.RingTheory.PowerSeries.Evaluation
import Mathlib.RingTheory.PowerSeries.Log
import Mathlib.RingTheory.PowerSeries.Substitution
import Mathlib.RingTheory.PowerSeries.WellKnown
import Mathlib.RingTheory.QuasiFinite.Basic
import Mathlib.RingTheory.RamificationInertia.Basic
import Mathlib.RingTheory.RootsOfUnity.Basic
import Mathlib.RingTheory.SimpleRing.Basic
import Mathlib.RingTheory.Spectrum.Prime.Topology
import Mathlib.RingTheory.TensorProduct.Quotient
import Mathlib.RingTheory.Valuation.Archimedean
import Mathlib.RingTheory.Valuation.Discrete.Basic
import Mathlib.RingTheory.Valuation.Discrete.IsDiscreteValuationRing
import Mathlib.RingTheory.Valuation.Extension
import Mathlib.RingTheory.Valuation.Integral
import Mathlib.RingTheory.Valuation.LocalSubring
import Mathlib.RingTheory.Valuation.RankOne
import Mathlib.RingTheory.Valuation.ValuationSubring
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Tactic
import Mathlib.Topology.Algebra.Field
import Mathlib.Topology.Algebra.Group.Basic
import Mathlib.Topology.Algebra.Group.Units
import Mathlib.Topology.Algebra.InfiniteSum.Nonarchimedean
import Mathlib.Topology.Algebra.LinearTopology
import Mathlib.Topology.Algebra.Module.Basic
import Mathlib.Topology.Algebra.Module.Compact
import Mathlib.Topology.Algebra.Nonarchimedean.AdicTopology
import Mathlib.Topology.Algebra.Order.Field
import Mathlib.Topology.Algebra.UniformRing
import Mathlib.Topology.Algebra.Valued.LocallyCompact
import Mathlib.Topology.Algebra.Valued.NormedValued
import Mathlib.Topology.Algebra.Valued.ValuativeRel
import Mathlib.Topology.Algebra.Valued.ValuedField
import Mathlib.Topology.Algebra.Valued.WithZeroMulInt
import Mathlib.Topology.Homeomorph.Defs
import Mathlib.Topology.Homeomorph.Lemmas
import Mathlib.Topology.Homeomorph.TransferInstance
import Mathlib.Topology.Instances.ZMod
import Mathlib.Topology.MetricSpace.Ultra.Basic
import Mathlib.Topology.Order
import Mathlib.Topology.UniformSpace.AbsoluteValue
import Mathlib.Topology.WithTopology
import Definitions.Def_OAIQ244Duke038
import Definitions.Def_OAIQ244Duke039
import Definitions.Def_OAIQ244Duke040
import Definitions.Def_OAIQ244Duke043

section
-- module Solutions.OAIQ244_DUKE.LocalField_DiscreteValuationField_FieldNorm
attribute [-instance] _root_.ClassFormation.DegreeData.FrobeniusFixedFieldTower.extensionNormal _root_.ClassFormation.DegreeData.GaloisSubextension.extensionSubgroup_normalInstance _root_.ClassFormation.FiniteAbstractField.toFiniteResidueAbstractField_extensionNormal _root_.ClassFormation.FiniteCyclicSubextension.instNormalSubtypeMemSubgroupFieldExtensionSubgroupField _root_.ClassFormation.FiniteGaloisSubextension.extensionSubgroup_normalInstance _root_.ClassFormation.FiniteGaloisSubextension.extensionSubgroup_over_intermediate_normalInstance _root_.ClassFormation.FiniteGaloisSubextension.intermediateField_normalInstance _root_.ClassFormation.FiniteIntermediateField.galoisRefinement_normal _root_.ClassFormation.FiniteUnramifiedCyclicExtension.instNormalSubtypeMemSubgroupFieldExtensionSubgroupField _root_.ClassFormation.conjugateExtension_normal _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalClassFieldTheory.extensionSubgroupBase_normal _root_.LocalClassFieldTheory.finiteGaloisExtensionSubgroupOfEmbedding_normal _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitInverseLimitCarrierPadicModule _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitQuotientCarrierPadicModule _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.LubinTate.compatibleGroupFamiliesGroup _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.RamificationTheory.HilbertRamification.ValuationSubring.inertiaGroup_normal _root_.RamificationTheory.HilbertRamification.ValuationSubring.ramificationGroupInInertiaAut_normal _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.LocalClassFieldTheory.normalizationIntegerRingIsIntegralClosure _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen
attribute [-simp] _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.IsDiscreteValuationRing.addVal_ringEquiv _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.DiscretePrincipalUnitQuotient.addEquiv_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.DiscretePrincipalUnitQuotient.addEquiv_map_smul _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.DiscretePrincipalUnitQuotient.addEquiv_of _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.DiscretePrincipalUnitQuotient.addEquiv_symm_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.DiscretePrincipalUnitQuotient.val_transition _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitAddEquivInverseLimitCarrier_map_smul _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitAddHomeomorphInverseLimitCarrier_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitInverseLimitCarrierEval_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitInverseLimitCarrierPadic_smul_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitMulEquivInverseLimitCarrier_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitPadic_smul_carrier_coordinate _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitProdiscreteLimitHomeomorphUnderlying_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitQuotientCarrierPadicScalar_eq_smul _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitQuotientCarrierToFull_mk _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitQuotientCarrierTransition_mk _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.PrincipalUnitProdiscreteLimit.addEquiv_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.PrincipalUnitProdiscreteLimit.addEquiv_map_smul _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.PrincipalUnitProdiscreteLimit.addEquiv_symm_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.PrincipalUnitProdiscreteLimit.coordinate_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.adicPrincipalUnitsHomeomorphProdiscreteLimit_to_addEquiv _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitPadic_smul_def _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitSuccQuotEquivGradedPiece_mk _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.toPrincipalUnitFiltration_subgroup _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.LocalFieldTheory.residueField_algebraMap_residue _root_.OAI.PrimeDegreePackets.ThetaConstruction.schwartzCM_apply _root_.infinitePlace_mult_smul
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

namespace LocalFieldTheory

/-!
# Field norm on unit groups

This file connects mathlib's `Algebra.norm` with the unit-group and valued-norm
APIs used by local CFT.
-/

noncomputable section

universe u v w

namespace DiscreteValuationField

variable (K : Type u) (L : Type v)
variable [Field K] [Field L] [Algebra K L]

/--
The subgroup appearing in `(fieldNormFiltrationPreimageSubgroup K L UK targetLevel n).Normal` is
normal.
-/
instance fieldNormFiltrationPreimageSubgroup_normal
    (UK : AntitoneSubgroupFiltration Kˣ) (targetLevel : ℕ → ℕ) (n : ℕ)
    [(UK.principalUnitSubgroup (targetLevel n)).Normal] :
    (fieldNormFiltrationPreimageSubgroup K L UK targetLevel n).Normal := by
  dsimp [fieldNormFiltrationPreimageSubgroup]
  infer_instance

/-- The class of the field-norm preimage of the target filtration subgroup
inside the source filtration quotient. -/
def fieldNormFiltrationPreimageClassInQuotient
    (UK : AntitoneSubgroupFiltration Kˣ) (UL : AntitoneSubgroupFiltration Lˣ)
    (targetLevel : ℕ → ℕ) (n : ℕ)
    [(UL.principalUnitSubgroup n).Normal] :
    Subgroup (Lˣ ⧸ UL.principalUnitSubgroup n) :=
  Subgroup.map (QuotientGroup.mk' (UL.principalUnitSubgroup n))
    (fieldNormFiltrationPreimageSubgroup K L UK targetLevel n)

/--
The subgroup appearing in `(fieldNormFiltrationPreimageClassInQuotient K L UK UL targetLevel
n).Normal` is normal.
-/
instance fieldNormFiltrationPreimageClassInQuotient_normal
    (UK : AntitoneSubgroupFiltration Kˣ) (UL : AntitoneSubgroupFiltration Lˣ)
    (targetLevel : ℕ → ℕ) (n : ℕ)
    [(UL.principalUnitSubgroup n).Normal]
    [(UK.principalUnitSubgroup (targetLevel n)).Normal] :
    (fieldNormFiltrationPreimageClassInQuotient
      K L UK UL targetLevel n).Normal := by
  dsimp [fieldNormFiltrationPreimageClassInQuotient]
  infer_instance

/-- The kernel of the concrete field-norm filtration quotient map is the class
of the norm-preimage of the target filtration subgroup. -/
theorem fieldNormFiltrationQuotientMap_ker_eq_preimageClass
    (UK : AntitoneSubgroupFiltration Kˣ) (UL : AntitoneSubgroupFiltration Lˣ)
    (targetLevel : ℕ → ℕ)
    (hN : fieldNormMapsFiltrationLevels K L UK UL targetLevel) (n : ℕ)
    [(UL.principalUnitSubgroup n).Normal]
    [(UK.principalUnitSubgroup (targetLevel n)).Normal] :
    (fieldNormFiltrationQuotientMap K L UK UL targetLevel hN n).ker =
      fieldNormFiltrationPreimageClassInQuotient
        K L UK UL targetLevel n := by
  exact QuotientGroup.ker_map (UL.principalUnitSubgroup n)
    (UK.principalUnitSubgroup (targetLevel n)) (normUnits K L)
    (by intro x hx; exact hN n hx)

/-- First-isomorphism form of the concrete field-norm filtration quotient map,
with codomain the actual range when no surjectivity hypothesis is available. -/
noncomputable def fieldNormFiltrationQuotientModuloPreimageClassEquivRange
    (UK : AntitoneSubgroupFiltration Kˣ) (UL : AntitoneSubgroupFiltration Lˣ)
    (targetLevel : ℕ → ℕ)
    (hN : fieldNormMapsFiltrationLevels K L UK UL targetLevel) (n : ℕ)
    [(UL.principalUnitSubgroup n).Normal]
    [(UK.principalUnitSubgroup (targetLevel n)).Normal] :
    (Lˣ ⧸ UL.principalUnitSubgroup n) ⧸
        fieldNormFiltrationPreimageClassInQuotient
          K L UK UL targetLevel n ≃*
      (fieldNormFiltrationQuotientMap K L UK UL targetLevel hN n).range :=
  (QuotientGroup.quotientMulEquivOfEq
      (fieldNormFiltrationQuotientMap_ker_eq_preimageClass
        K L UK UL targetLevel hN n).symm).trans
    (QuotientGroup.quotientKerEquivRange
      (fieldNormFiltrationQuotientMap K L UK UL targetLevel hN n))

/--
Establishes the identity `fieldNormFiltrationQuotientModuloPreimageClassEquivRange K L UK UL
targetLevel hN n (QuotientGroup.mk' (fieldNormFiltrationPreimageClassInQuotient K L UK UL
targetLevel n) q) = (fieldNormFiltrationQuotientMap K L UK UL targetLevel hN n).rangeRestrict q`.
-/
@[simp] theorem fieldNormFiltrationQuotientModuloPreimageClassEquivRange_mk
    (UK : AntitoneSubgroupFiltration Kˣ) (UL : AntitoneSubgroupFiltration Lˣ)
    (targetLevel : ℕ → ℕ)
    (hN : fieldNormMapsFiltrationLevels K L UK UL targetLevel) (n : ℕ)
    [(UL.principalUnitSubgroup n).Normal]
    [(UK.principalUnitSubgroup (targetLevel n)).Normal]
    (q : Lˣ ⧸ UL.principalUnitSubgroup n) :
    fieldNormFiltrationQuotientModuloPreimageClassEquivRange
        K L UK UL targetLevel hN n
        (QuotientGroup.mk'
          (fieldNormFiltrationPreimageClassInQuotient
            K L UK UL targetLevel n) q) =
      (fieldNormFiltrationQuotientMap
        K L UK UL targetLevel hN n).rangeRestrict q :=
  rfl

/--
Establishes the identity `((fieldNormFiltrationQuotientModuloPreimageClassEquivRange K L UK UL
targetLevel hN n (QuotientGroup.mk' (fieldNormFiltrationPreimageClassInQuotient K L UK UL
targetLevel n) q) : (fieldNormFiltrationQuotientMap K L UK UL targetLevel hN n).range) : Kˣ ⧸
UK.principalUnitSubgroup (targetLevel n)) = fieldNormFiltrationQuotientMap K L UK UL targetLevel
hN n q`.
-/
@[simp] theorem coe_fieldNormFiltrationQuotientModuloPreimageClassEquivRange_mk
    (UK : AntitoneSubgroupFiltration Kˣ) (UL : AntitoneSubgroupFiltration Lˣ)
    (targetLevel : ℕ → ℕ)
    (hN : fieldNormMapsFiltrationLevels K L UK UL targetLevel) (n : ℕ)
    [(UL.principalUnitSubgroup n).Normal]
    [(UK.principalUnitSubgroup (targetLevel n)).Normal]
    (q : Lˣ ⧸ UL.principalUnitSubgroup n) :
    ((fieldNormFiltrationQuotientModuloPreimageClassEquivRange
        K L UK UL targetLevel hN n
        (QuotientGroup.mk'
          (fieldNormFiltrationPreimageClassInQuotient
            K L UK UL targetLevel n) q) :
      (fieldNormFiltrationQuotientMap
        K L UK UL targetLevel hN n).range) :
        Kˣ ⧸ UK.principalUnitSubgroup (targetLevel n)) =
      fieldNormFiltrationQuotientMap K L UK UL targetLevel hN n q := by
  rw [fieldNormFiltrationQuotientModuloPreimageClassEquivRange_mk]
  rfl

end DiscreteValuationField

end

end LocalFieldTheory
end

section
-- module Solutions.OAIQ244_DUKE.LocalField_Analytic_DenominatorValuation
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_isCompleteDiscrete _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.AdicPrincipalUnits.instAddCommGroup _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.AdicPrincipalUnits.instTopologicalSpace _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.DiscretePrincipalUnitQuotient.instAddCommGroup _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitInverseLimitCarrierPadicModule _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitInverseLimitCarrierPadicSMul _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitQuotientCarrierPadicModule _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitQuotientCarrier_finite _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.PrincipalUnitProdiscreteLimit.instAddCommGroup _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.PrincipalUnitProdiscreteLimit.instTopologicalSpace _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.adicPrincipalUnitsContinuousAdd _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.adicPrincipalUnitsPadicModule _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.discretePrincipalUnitQuotientFinite _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.discretePrincipalUnitQuotientPadicModule _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitPadicModule _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitPadicSMul _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitProdiscreteLimitContinuousAdd _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitProdiscreteLimitPadicModule _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitSuccQuotCommGroup _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.residueFieldZModAlgebra _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedQPadicContextAlgebra _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedQPadicContextFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.LubinTate.Valuations.exponentialValuationSubringIsLocalRing _root_.OAI.PrimeDegreePackets.instNonemptyLeafTestSpace _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionFixedSubring.instIsLocalRing _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.LocalClassFieldTheory.normalizationIntegerRingIsIntegralClosure _root_.RamificationTheory.HilbertRamification.CompleteDVF.decompositionGroupMulSemiringAction _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen
attribute [-simp] _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.IsDiscreteValuationRing.addVal_ringEquiv _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.EqualCharacteristicLaurent.coeffHom_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.EqualCharacteristicLaurent.powerSeriesEvalHom_C _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.EqualCharacteristicLaurent.powerSeriesEvalHom_X _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.EqualCharacteristicLaurent.powerSeriesEvalSubringHom_C _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.EqualCharacteristicLaurent.powerSeriesEvalSubringHom_X _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.coe_valuationSubringUnitsToFieldUnits_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.fieldUnitValueUnit_mul _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.fieldUnitValueUnit_one _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.AdicPrincipalUnits.addEquiv_map_smul _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.AdicPrincipalUnits.of_val _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.AdicPrincipalUnits.val_of _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.DiscretePrincipalUnitQuotient.addEquiv_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.DiscretePrincipalUnitQuotient.addEquiv_map_smul _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.DiscretePrincipalUnitQuotient.addEquiv_of _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.DiscretePrincipalUnitQuotient.addEquiv_symm_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.DiscretePrincipalUnitQuotient.of_val _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.DiscretePrincipalUnitQuotient.val_of _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.DiscretePrincipalUnitQuotient.val_transition _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.adicPrincipalUnitsHomeomorphUnderlying_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitAddEquivInverseLimitCarrier_map_smul _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitAddHomeomorphInverseLimitCarrier_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitInverseLimitCarrierEval_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitInverseLimitCarrierPadic_smul_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitMulEquivInverseLimitCarrier_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitPadic_smul_carrier_coordinate _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitProdiscreteLimitHomeomorphUnderlying_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitQuotientCarrierPadicScalar_eq_smul _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitQuotientCarrierToFull_mk _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitQuotientCarrierTransition_mk _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.uniformizerHigherUnitQuotientEquiv_mk _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.PrincipalUnitProdiscreteLimit.addEquiv_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.PrincipalUnitProdiscreteLimit.addEquiv_map_smul _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.PrincipalUnitProdiscreteLimit.addEquiv_symm_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.PrincipalUnitProdiscreteLimit.coordinate_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.PrincipalUnitProdiscreteLimit.coordinate_smul _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.PrincipalUnitProdiscreteLimit.of_val _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.PrincipalUnitProdiscreteLimit.val_of _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.adicPrincipalUnitsAddEquivProdiscreteLimit_map_smul _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.adicPrincipalUnitsContinuousAddEquivUnderlyingOfWithZeroValuation_map_smul _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.adicPrincipalUnitsHomeomorphProdiscreteLimit_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.adicPrincipalUnitsHomeomorphProdiscreteLimit_to_addEquiv _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.coe_valuationSubringUnitFieldUnitHom_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.fieldUnitsEquivRootsPrincipalUnitsUniformizer_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.iwasawaDegreeTerm_zero _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.iwasawaGn_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.iwasawaPartialProduct_zero_input _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.iwasawaSeedAtLevel_val _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.iwasawaSeedIdeal_val _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.iwasawaSeed_val _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.maximalIdealPowSuccQuotAddEquivPrincipalUnitSuccQuot_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.mem_iff _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitOneAddOfMemPowSubgroup_val _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitOneAddOfMemPow_val _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitPadic_natCast_smul _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitPadic_nsmul_eq_pow _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitPadic_smul_def _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitSuccQuotAddEquivResidueOfUniformizer_coord _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitSuccQuotAddEquivResidueOfUniformizer_symm_residue _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitSuccQuotAddEquivResidue_iwasawaSeed _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitSuccQuotConcreteEquiv_mk _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitSuccQuotEquivGradedPiece_mk _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitSuccQuotLift_mk _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitSuccQuotOfIdealPow_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitSuccQuotOfMaximalIdealPowSuccQuotAdd_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitSuccQuotOfMaximalIdealPowSuccQuot_map_zero _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitSuccQuotOfMaximalIdealPowSuccQuot_mk _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.quotientUnitHom_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.residueRootsOfUnityEquivResidueFieldUnits_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.residueTeichmullerFieldHomOfCharP_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.residueTeichmullerLift_one _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.residueTeichmullerLift_zero _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.residueTeichmullerRingHomOfCharP_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.residueUnitHom_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.rootsPrincipalUnitUniformizerMulHom_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.toPrincipalUnitFiltration_subgroup _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.unitsModOneEquivResidueFieldUnits_mk _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.unitsModPrincipalUnitEquivOfPreserves_mk _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.valuationSubringUnitEquivOfPreserves_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.valuationSubringUnitsEquivRootsTimesPrincipalUnits_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.zero_eq_top _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.mrangeRestrict_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.multiplicativeIntegerValuationOfUniformizer_val _root_.LocalFieldTheory.DiscreteValuationField.LocalField.laurentSeriesEquivLaurentImageSubfield_apply_coe _root_.LocalFieldTheory.DiscreteValuationField.LocalField.ratCastToQpadicClosureSubfield_apply _root_.LocalFieldTheory.DiscreteValuationField.LocalField.ratCastWithValToQpadicClosureSubfield_apply _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.LocalFieldTheory.residueField_algebraMap_residue _root_.LubinTate.LubinTateSeries.standardLubinTateSeries_toPowerSeries _root_.LubinTate.SameUniformizer.coeff_recursiveIntertwiner _root_.LubinTate.SameUniformizer.constantCoeff_inVariable _root_.LubinTate.SameUniformizer.intertwinerApproximation_zero _root_.LubinTate.SameUniformizer.standardLubinTateEndomorphism_coeff_one _root_.LubinTate.standardLubinTateBaseUniformizerUnit_coe _root_.LubinTate.standardLubinTateChangedUniformizerUnit_coe _root_.LubinTate.standardLubinTateLevelGenerator_coe _root_.LubinTate.standardLubinTatePolynomialIterateOverSeparableClosure_eval _root_.LubinTate.standardLubinTatePolynomialIterate_derivative_eval_zero _root_.LubinTate.standardLubinTatePolynomialIterate_eval_zero _root_.LubinTate.standardLubinTatePolynomialIterate_zero _root_.LubinTate.standardLubinTatePolynomial_derivative_eval_zero _root_.LubinTate.standardLubinTatePolynomial_eval _root_.LubinTate.standardLubinTatePolynomial_toPowerSeries _root_.LubinTate.standardLubinTatePolynomial_toPowerSeries_eq_series _root_.LubinTate.standardLubinTatePrimitivePointInteger_coe _root_.LubinTate.standardLubinTatePrimitivePolynomialOverField_coeff_zero _root_.LubinTate.standardLubinTatePrimitivePolynomial_coeff_zero _root_.LubinTate.standardLubinTateUnitFactorFieldUnit_coe _root_.OAI.PrimeDegreePackets.ThetaConstruction.schwartzCM_apply _root_.ValuationTheory.DiscreteValuationField.ValuedExtension.integralClosureRingEquivTargetValuationSubringOfModuleFinite_apply _root_.ValuationTheory.DiscreteValuationField.ValuedExtension.integralClosureToTargetValuationSubringOfHasExtension_apply _root_.ValuationTheory.DiscreteValuationField.ValuedExtension.integralClosureValuationSubringIntegerMapOfMemOrInv_apply _root_.ValuationTheory.DiscreteValuationField.ValuedExtension.targetValuationSubringToIntegralClosureOfModuleFinite_apply _root_.infinitePlace_mult_smul
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

/-!
# Valuations of natural-number denominators

For a complete discrete valuation with value group `WithZero (Multiplicative ℤ)`
and finite residue field, this file constructs the ramification index
`e = v_K(p)` from the valuation itself.  In mixed characteristic it then proves
the natural-number valuation formula used in the logarithm and exponential theorems.
-/

noncomputable section

universe u

namespace LocalFieldTheory.DiscreteValuationField
namespace LocalField

variable {K : Type u} [Field K]

/-- The natural ramification index recovers the normalized integer valuation
of the residue characteristic. -/
theorem ramificationIndexOfWithZeroValuation_intCast
    (v : _root_.Valuation K (WithZero (Multiplicative ℤ)))
    [ValuationTheory.DiscreteValuationField.Valuation.IsCompleteDiscrete v]
    [Finite (IsLocalRing.ResidueField v.valuationSubring)] [CharZero K] :
    (ramificationIndexOfWithZeroValuation v : ℤ) =
      -WithZero.log
        (v ((ofWithZeroValuation v).residueCharacteristic : K)) := by
  let F : LocalField.{u, 0} K := ofWithZeroValuation v
  have hpK : (F.residueCharacteristic : K) ≠ 0 :=
    F.natCast_residueCharacteristic_ne_zero_of_charZero
  have hpv_ne : v (F.residueCharacteristic : K) ≠ 0 :=
    (_root_.Valuation.ne_zero_iff v).2 hpK
  have hpv_lt :
      v (F.residueCharacteristic : K) <
        (1 : WithZero (Multiplicative ℤ)) := by
    exact F.valuation_natCast_residueCharacteristic_lt_one
  have hlogneg :
      WithZero.log (v (F.residueCharacteristic : K)) < (0 : ℤ) := by
    have hloglt :
        WithZero.log (v (F.residueCharacteristic : K)) <
          WithZero.log (1 : WithZero (Multiplicative ℤ)) := by
      rw [WithZero.log_lt_log hpv_ne one_ne_zero]
      exact hpv_lt
    simpa using hloglt
  have hnonneg :
      0 ≤ -WithZero.log (v (F.residueCharacteristic : K)) :=
    (neg_pos.mpr hlogneg).le
  simpa [ramificationIndexOfWithZeroValuation, F] using
    Int.toNat_of_nonneg hnonneg

/-- The ramification index of a mixed-characteristic local field is positive. -/
theorem ramificationIndexOfWithZeroValuation_pos
    (v : _root_.Valuation K (WithZero (Multiplicative ℤ)))
    [ValuationTheory.DiscreteValuationField.Valuation.IsCompleteDiscrete v]
    [Finite (IsLocalRing.ResidueField v.valuationSubring)] [CharZero K] :
    0 < ramificationIndexOfWithZeroValuation v := by
  let F : LocalField.{u, 0} K := ofWithZeroValuation v
  have hpK : (F.residueCharacteristic : K) ≠ 0 :=
    F.natCast_residueCharacteristic_ne_zero_of_charZero
  have hpv_ne : v (F.residueCharacteristic : K) ≠ 0 :=
    (_root_.Valuation.ne_zero_iff v).2 hpK
  have hpv_lt :
      v (F.residueCharacteristic : K) <
        (1 : WithZero (Multiplicative ℤ)) := by
    exact F.valuation_natCast_residueCharacteristic_lt_one
  have hlogneg :
      WithZero.log (v (F.residueCharacteristic : K)) < (0 : ℤ) := by
    have hloglt :
        WithZero.log (v (F.residueCharacteristic : K)) <
          WithZero.log (1 : WithZero (Multiplicative ℤ)) := by
      rw [WithZero.log_lt_log hpv_ne one_ne_zero]
      exact hpv_lt
    simpa using hloglt
  have heInt :
      (0 : ℤ) < (ramificationIndexOfWithZeroValuation v : ℤ) := by
    rw [ramificationIndexOfWithZeroValuation_intCast v]
    exact neg_pos.mpr hlogneg
  exact_mod_cast heInt

/-- The value of the residue characteristic is `exp (-e)`, where `e` is the
ramification index constructed from the valuation. -/
theorem valuation_residueCharacteristic_eq_exp_neg_ramificationIndex
    (v : _root_.Valuation K (WithZero (Multiplicative ℤ)))
    [ValuationTheory.DiscreteValuationField.Valuation.IsCompleteDiscrete v]
    [Finite (IsLocalRing.ResidueField v.valuationSubring)] [CharZero K] :
    v ((ofWithZeroValuation v).residueCharacteristic : K) =
      WithZero.exp (-(ramificationIndexOfWithZeroValuation v : ℤ)) := by
  let F : LocalField.{u, 0} K := ofWithZeroValuation v
  have hpK : (F.residueCharacteristic : K) ≠ 0 :=
    F.natCast_residueCharacteristic_ne_zero_of_charZero
  have hpv_ne : v (F.residueCharacteristic : K) ≠ 0 :=
    (_root_.Valuation.ne_zero_iff v).2 hpK
  have hpv_ne' :
      v ((ofWithZeroValuation v).residueCharacteristic : K) ≠ 0 := by
    simpa [F] using hpv_ne
  calc
    v ((ofWithZeroValuation v).residueCharacteristic : K) =
        WithZero.exp
          (WithZero.log
            (v ((ofWithZeroValuation v).residueCharacteristic : K))) :=
      (WithZero.exp_log hpv_ne').symm
    _ = WithZero.exp (-(ramificationIndexOfWithZeroValuation v : ℤ)) := by
      rw [ramificationIndexOfWithZeroValuation_intCast v]
      simp

/-- A nonzero natural number has valuation equal to the value of its
residue-characteristic power.  This is the denominator formula needed for the
logarithm and exponential estimates in the logarithm and exponential estimates. -/
theorem valuation_natCast_eq_exp_neg_ramificationIndex_mul_padicValNat
    (v : _root_.Valuation K (WithZero (Multiplicative ℤ)))
    [ValuationTheory.DiscreteValuationField.Valuation.IsCompleteDiscrete v]
    [Finite (IsLocalRing.ResidueField v.valuationSubring)] [CharZero K]
    (m : ℕ) (hm : m ≠ 0) :
    v (m : K) =
      WithZero.exp
        (-((ramificationIndexOfWithZeroValuation v : ℤ) *
          (padicValNat (ofWithZeroValuation v).residueCharacteristic m : ℤ))) := by
  let F : LocalField.{u, 0} K := ofWithZeroValuation v
  let p : ℕ := F.residueCharacteristic
  let e : ℕ := ramificationIndexOfWithZeroValuation v
  let k : ℕ := padicValNat p m
  let a : ℕ := m / p ^ k
  let : Fact p.Prime := by
    dsimp [p]
    infer_instance
  have hpow : p ^ k ∣ m := by
    exact pow_padicValNat_dvd
  have hmfac : p ^ k * a = m := by
    exact Nat.mul_div_cancel' hpow
  have ha : ¬ p ∣ a := by
    intro hpa
    have hnot : ¬ p ^ (k + 1) ∣ m := by
      simpa [k] using
        (pow_succ_padicValNat_not_dvd (p := p) hm)
    apply hnot
    rcases hpa with ⟨b, hb⟩
    refine ⟨b, ?_⟩
    calc
      m = p ^ k * a := hmfac.symm
      _ = p ^ k * (p * b) := by rw [hb]
      _ = p ^ (k + 1) * b := by rw [pow_succ]; ac_rfl
  have hpVal :
      v (p : K) = WithZero.exp (-(e : ℤ)) := by
    simpa [F, p, e] using
      valuation_residueCharacteristic_eq_exp_neg_ramificationIndex v
  have haVal : v (a : K) = 1 := by
    change F.toCompleteDVF.valuation (a : K) = 1
    exact F.valuation_natCast_eq_one_of_not_residueCharacteristic_dvd ha
  have hmK : (m : K) = (p : K) ^ k * (a : K) := by
    exact_mod_cast hmfac.symm
  calc
    v (m : K) = v ((p : K) ^ k * (a : K)) := by rw [hmK]
    _ = v (p : K) ^ k * v (a : K) := by rw [v.map_mul, v.map_pow]
    _ = WithZero.exp (-(e : ℤ)) ^ k := by rw [hpVal, haVal, mul_one]
    _ = WithZero.exp (k • (-(e : ℤ))) := by
      rw [WithZero.exp_nsmul]
    _ = WithZero.exp (-((e : ℤ) * (k : ℤ))) := by
      congr 1
      simp [mul_comm]
    _ = WithZero.exp
        (-((ramificationIndexOfWithZeroValuation v : ℤ) *
          (padicValNat (ofWithZeroValuation v).residueCharacteristic m : ℤ))) := by
      rfl

/-- Successor form of the natural-number valuation formula.  Unlike the main
formula, this needs no explicit nonzero hypothesis. -/
theorem valuation_natCast_succ_eq_exp_neg_ramificationIndex_mul_padicValNat
    (v : _root_.Valuation K (WithZero (Multiplicative ℤ)))
    [ValuationTheory.DiscreteValuationField.Valuation.IsCompleteDiscrete v]
    [Finite (IsLocalRing.ResidueField v.valuationSubring)] [CharZero K]
    (m : ℕ) :
    v ((m + 1 : ℕ) : K) =
      WithZero.exp
        (-((ramificationIndexOfWithZeroValuation v : ℤ) *
          (padicValNat
            (ofWithZeroValuation v).residueCharacteristic (m + 1) : ℤ))) :=
  valuation_natCast_eq_exp_neg_ramificationIndex_mul_padicValNat
    v (m + 1) (Nat.succ_ne_zero m)

/-- Factorial form of the natural-number valuation formula, used by the
exponential series in the deep exponential–logarithm equivalence. -/
theorem valuation_natCast_factorial_eq_exp_neg_ramificationIndex_mul_padicValNat
    (v : _root_.Valuation K (WithZero (Multiplicative ℤ)))
    [ValuationTheory.DiscreteValuationField.Valuation.IsCompleteDiscrete v]
    [Finite (IsLocalRing.ResidueField v.valuationSubring)] [CharZero K]
    (m : ℕ) :
    v ((m.factorial : ℕ) : K) =
      WithZero.exp
        (-((ramificationIndexOfWithZeroValuation v : ℤ) *
          (padicValNat
            (ofWithZeroValuation v).residueCharacteristic m.factorial : ℤ))) :=
  valuation_natCast_eq_exp_neg_ramificationIndex_mul_padicValNat
    v m.factorial (Nat.factorial_ne_zero m)

end LocalField
end LocalFieldTheory.DiscreteValuationField
end
end

section
-- module Solutions.OAIQ244_DUKE.LocalField_DiscreteValuationField_PrincipalUnitPadicAction_ProdiscretePadicModule
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.DiscreteNthRootsSubgroup.instTopologicalSpaceSubtypeUnitsMemSubgroup _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.adicPrincipalUnitsContinuousAdd _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.adicPrincipalUnitsPadicModule _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitPadicModule _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitPadicSMul _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.residueFieldZModAlgebra _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedQPadicContextAlgebra _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedQPadicContextFact _root_.LocalFieldTheory.DiscreteValuationField.ValuedNorm.filtrationPreimageClassInQuotient_normal _root_.LocalFieldTheory.DiscreteValuationField.ValuedNorm.filtrationPreimageSubgroup_normal _root_.LocalFieldTheory.DiscreteValuationField.fieldNormFiltrationPreimageClassInQuotient_normal _root_.LocalFieldTheory.DiscreteValuationField.fieldNormFiltrationPreimageSubgroup_normal _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.RamificationTheory.HilbertRamification.Higher.lowerRamificationGroup.instNormal _root_.RayClass.approximationCompletionTopologicalSpace _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.CyclicCohomology.binaryCoefficientFamilyCommGroup _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.LocalClassFieldTheory.normalizationIntegerRingIsIntegralClosure _root_.RamificationTheory.HilbertRamification.CompleteDVF.decompositionGroupMulSemiringAction _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

/-!
# The p-adic module on the prodiscrete principal-unit limit

Coordinatewise scalar multiplication makes the prodiscrete inverse limit a topological
module over the p-adic integers.
-/

noncomputable section

open scoped BigOperators

universe u v

namespace LocalFieldTheory.DiscreteValuationField
open LocalFieldTheory.DiscreteValuationField
open ValuationTheory.DiscreteValuationField
namespace CompleteDVF
open LocalFieldTheory.DiscreteValuationField.CompleteDVF
namespace higherPrincipalUnitGroup

open LubinTate
open LubinTate.Valuations

variable {K : Type u} [Field K]

open Internal

/-! ## The inverse-limit module and transport to `U^1` -/

/-- Joint continuity of the coordinatewise p-adic action on the inverse
limit of discrete finite quotients. -/
theorem Internal.continuous_principalUnitInverseLimitCarrierPadic_smul
    (F : LocalField.{u, v} K) :
    letI : (n : ℕ) → TopologicalSpace
        (Internal.principalUnitQuotientCarrier F.toCompleteDVF n) := fun _ => ⊥
    Continuous fun z : ℤ_[F.residueCharacteristic] ×
        Additive (Internal.principalUnitInverseLimitCarrier F.toCompleteDVF) =>
      z.1 • z.2 := by
  let : (n : ℕ) → TopologicalSpace
      (Internal.principalUnitQuotientCarrier F.toCompleteDVF n) := fun _ => ⊥
  let : (n : ℕ) → DiscreteTopology
      (Internal.principalUnitQuotientCarrier F.toCompleteDVF n) := fun _ => ⟨rfl⟩
  have hmul : Continuous fun z : ℤ_[F.residueCharacteristic] ×
      Additive (Internal.principalUnitInverseLimitCarrier F.toCompleteDVF) =>
      Additive.toMul (z.1 • z.2) := by
    exact Continuous.subtype_mk
      (continuous_pi fun n => by
        have hlimval : Continuous fun x : Additive
            (Internal.principalUnitInverseLimitCarrier F.toCompleteDVF) =>
            (Additive.toMul x).1 :=
          continuous_subtype_val
        have hcoord : Continuous fun z : ℤ_[F.residueCharacteristic] ×
            Additive (Internal.principalUnitInverseLimitCarrier F.toCompleteDVF) =>
            Additive.ofMul ((Additive.toMul z.2).1 n) :=
          ((continuous_apply n).comp hlimval).comp continuous_snd
        have hs := (Internal.continuous_principalUnitQuotientCarrierPadicScalar F n).comp
          (continuous_fst.prodMk hcoord)
        change Continuous fun z : ℤ_[F.residueCharacteristic] ×
            Additive (Internal.principalUnitInverseLimitCarrier F.toCompleteDVF) =>
          Additive.toMul
            (principalUnitQuotientCarrierPadicScalar F n z.1
              (Additive.ofMul ((Additive.toMul z.2).1 n)))
        exact hs)
      (fun z : ℤ_[F.residueCharacteristic] ×
          Additive (Internal.principalUnitInverseLimitCarrier F.toCompleteDVF) => by
        intro i j hij
        exact (Additive.toMul (z.1 • z.2)).2 hij)
  exact hmul

/--
The specified map is continuous: `Continuous fun z : ℤ_[F.residueCharacteristic] ×
PrincipalUnitProdiscreteLimit F.toCompleteDVF => z.1 • z.2`.
-/
theorem continuous_principalUnitProdiscreteLimitPadic_smul
    (F : LocalField.{u, v} K) :
    Continuous fun z : ℤ_[F.residueCharacteristic] ×
        PrincipalUnitProdiscreteLimit F.toCompleteDVF =>
      z.1 • z.2 := by
  let : (n : ℕ) → TopologicalSpace
      (Internal.principalUnitQuotientCarrier F.toCompleteDVF n) := fun _ => ⊥
  let e := (PrincipalUnitProdiscreteLimit.homeomorph F.toCompleteDVF).trans
    (WithTopology.homeomorph
      (α := Additive
        (Internal.principalUnitInverseLimitCarrier F.toCompleteDVF))
      (topology := principalUnitProdiscreteTopology F.toCompleteDVF))
  have hpair : Continuous fun z : ℤ_[F.residueCharacteristic] ×
      PrincipalUnitProdiscreteLimit F.toCompleteDVF =>
      (z.1, e z.2) :=
    continuous_fst.prodMk (e.continuous.comp continuous_snd)
  have h := e.continuous_symm.comp
    ((Internal.continuous_principalUnitInverseLimitCarrierPadic_smul F).comp hpair)
  exact h

/--
The scalar action in `ContinuousSMul ℤ_[F.residueCharacteristic] (PrincipalUnitProdiscreteLimit
F.toCompleteDVF)` is continuous.
-/
noncomputable instance principalUnitProdiscreteLimitContinuousSMul
    (F : LocalField.{u, v} K) :
    ContinuousSMul ℤ_[F.residueCharacteristic]
      (PrincipalUnitProdiscreteLimit F.toCompleteDVF) :=
  ⟨continuous_principalUnitProdiscreteLimitPadic_smul F⟩

end higherPrincipalUnitGroup
end CompleteDVF
end LocalFieldTheory.DiscreteValuationField
end
end

section
-- module Solutions.OAIQ244_DUKE.LocalField_DiscreteValuationField_PrincipalUnitPadicAction_AdicPadicModule
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.residueFieldZModAlgebra _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedQPadicContextAlgebra _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedQPadicContextFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.RayClass.approximationCompletionTopologicalSpace _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.LocalClassFieldTheory.normalizationIntegerRingIsIntegralClosure _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

/-!
# The p-adic module on adic principal units

The coordinatewise p-adic action is transported across the canonical adic/prodiscrete
comparison, producing its linear and topological forms on first principal units.
-/

noncomputable section

open scoped BigOperators

universe u v

namespace LocalFieldTheory.DiscreteValuationField
open LocalFieldTheory.DiscreteValuationField
open ValuationTheory.DiscreteValuationField
namespace CompleteDVF
open LocalFieldTheory.DiscreteValuationField.CompleteDVF
namespace higherPrincipalUnitGroup

open LubinTate
open LubinTate.Valuations

variable {K : Type u} [Field K]

open Internal

/--
The specified map is continuous: `Continuous fun z : ℤ_[F.residueCharacteristic] ×
AdicPrincipalUnits F.toCompleteDVF => z.1 • z.2`.
-/
theorem continuous_adicPrincipalUnitsPadic_smul
    (F : LocalField.{u, v} K) :
    Continuous fun z : ℤ_[F.residueCharacteristic] ×
        AdicPrincipalUnits F.toCompleteDVF =>
      z.1 • z.2 := by
  let e := adicPrincipalUnitsHomeomorphProdiscreteLimit F.toCompleteDVF
  have hpair : Continuous fun z : ℤ_[F.residueCharacteristic] ×
      AdicPrincipalUnits F.toCompleteDVF =>
      (z.1, e z.2) :=
    continuous_fst.prodMk (e.continuous.comp continuous_snd)
  have htransport := e.continuous_symm.comp (continuous_smul.comp hpair)
  exact htransport

/--
The scalar action in `ContinuousSMul ℤ_[F.residueCharacteristic] (AdicPrincipalUnits
F.toCompleteDVF)` is continuous.
-/
noncomputable instance adicPrincipalUnitsContinuousSMul
    (F : LocalField.{u, v} K) :
    ContinuousSMul ℤ_[F.residueCharacteristic]
      (AdicPrincipalUnits F.toCompleteDVF) :=
  ⟨continuous_adicPrincipalUnitsPadic_smul F⟩

end higherPrincipalUnitGroup
end CompleteDVF
end LocalFieldTheory.DiscreteValuationField
end
end

section
-- module Solutions.OAIQ244_DUKE.LocalField_DiscreteValuationField_PrincipalUnitPadicAction_WithZeroValuationTopology
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_isCompleteDiscrete _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.DiscreteNthRootsSubgroup.instTopologicalSpaceSubtypeUnitsMemSubgroup _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.residueFieldZModAlgebra _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedQPadicContextAlgebra _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedQPadicContextFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.RamificationTheory.HilbertRamification.Higher.lowerRamificationGroup.instNormal _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionFixedSubring.instIsLocalRing _root_.RayClass.approximationCompletionTopologicalSpace _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.LocalClassFieldTheory.normalizationIntegerRingIsIntegralClosure _root_.RamificationTheory.HilbertRamification.CompleteDVF.decompositionGroupMulSemiringAction _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

/-!
# Principal-unit topology from a normalized valuation

For a complete discrete valuation with value group `WithZero (Multiplicative ℤ)`, the
inherited topology agrees with the canonical adic model, so the p-adic action and addition are
continuous on the original principal-unit carrier.
-/

noncomputable section

open scoped BigOperators

universe u v

namespace LocalFieldTheory.DiscreteValuationField
open LocalFieldTheory.DiscreteValuationField
open ValuationTheory.DiscreteValuationField
namespace CompleteDVF
open LocalFieldTheory.DiscreteValuationField.CompleteDVF
namespace higherPrincipalUnitGroup

open LubinTate
open LubinTate.Valuations

variable {K : Type u} [Field K]

open Internal

/-- The same canonical action is jointly continuous for the topology carried
directly by a standard `ℤᵐ⁰`-valued complete discrete valuation.  The bridge
is the equality between the inherited valuation topology on the valuation
ring and its maximal-ideal adic topology. -/
theorem principalUnitPadicContinuousSMulOfWithZeroValuation
    (v : _root_.Valuation K (WithZero (Multiplicative ℤ)))
    [ValuationTheory.DiscreteValuationField.Valuation.IsCompleteDiscrete v]
    [Finite (IsLocalRing.ResidueField v.valuationSubring)] :
    let F : LocalField.{u, 0} K := LocalField.ofWithZeroValuation v
    letI : Valued K (WithZero (Multiplicative ℤ)) := Valued.mk' v
    ContinuousSMul ℤ_[F.residueCharacteristic]
      (Additive ((LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup F.toCompleteDVF) 1)) := by
  let F : LocalField.{u, 0} K := LocalField.ofWithZeroValuation v
  let : Valued K (WithZero (Multiplicative ℤ)) := Valued.mk' v
  let e :=
    adicPrincipalUnitsContinuousAddEquivUnderlyingOfWithZeroValuation v
  refine ⟨?_⟩
  have hpair : Continuous fun z : ℤ_[F.residueCharacteristic] ×
      Additive
        ((LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup F.toCompleteDVF) 1) =>
      (z.1, e.symm z.2) :=
    continuous_fst.prodMk (e.continuous_symm.comp continuous_snd)
  have htransport := e.continuous.comp (continuous_smul.comp hpair)
  exact htransport

/-- Continuous addition on `Additive U^1` for the direct normalized
valuation topology. -/
theorem principalUnitPadicContinuousAddOfWithZeroValuation
    (v : _root_.Valuation K (WithZero (Multiplicative ℤ)))
    [ValuationTheory.DiscreteValuationField.Valuation.IsCompleteDiscrete v]
    [Finite (IsLocalRing.ResidueField v.valuationSubring)] :
    let F : LocalField.{u, 0} K := LocalField.ofWithZeroValuation v
    letI : Valued K (WithZero (Multiplicative ℤ)) := Valued.mk' v
    ContinuousAdd (Additive
      ((LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup F.toCompleteDVF) 1)) := by
  let F : LocalField.{u, 0} K := LocalField.ofWithZeroValuation v
  let : Valued K (WithZero (Multiplicative ℤ)) := Valued.mk' v
  let e :=
    adicPrincipalUnitsContinuousAddEquivUnderlyingOfWithZeroValuation v
  refine ⟨?_⟩
  have hpair : Continuous fun z :
      Additive
          ((LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup F.toCompleteDVF) 1) ×
        Additive
          ((LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup F.toCompleteDVF) 1) =>
      (e.symm z.1, e.symm z.2) :=
    (e.continuous_symm.comp continuous_fst).prodMk
      (e.continuous_symm.comp continuous_snd)
  have htransport := e.continuous.comp (continuous_add.comp hpair)
  exact htransport

end higherPrincipalUnitGroup
end CompleteDVF
end LocalFieldTheory.DiscreteValuationField
end
end

section
-- module Solutions.OAIQ244_DUKE.LocalField_DiscreteValuationField_IwasawaPrincipalUnits
attribute [-instance] _root_.ClassFormation.DegreeData.FrobeniusFixedFieldTower.extensionNormal _root_.ClassFormation.DegreeData.GaloisSubextension.extensionSubgroup_normalInstance _root_.ClassFormation.FiniteAbstractField.toFiniteResidueAbstractField_extensionNormal _root_.ClassFormation.FiniteCyclicSubextension.instNormalSubtypeMemSubgroupFieldExtensionSubgroupField _root_.ClassFormation.FiniteGaloisSubextension.extensionSubgroup_normalInstance _root_.ClassFormation.FiniteGaloisSubextension.extensionSubgroup_over_intermediate_normalInstance _root_.ClassFormation.FiniteGaloisSubextension.intermediateField_normalInstance _root_.ClassFormation.FiniteIntermediateField.galoisRefinement_normal _root_.ClassFormation.FiniteUnramifiedCyclicExtension.instNormalSubtypeMemSubgroupFieldExtensionSubgroupField _root_.ClassFormation.conjugateExtension_normal _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_isCompleteDiscrete _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.HilbertRamification.Dedekind.inertiaSubgroupOfDecomposition_normal _root_.KummerTheory.DiscreteNthRootsSubgroup.instCommGroupSubtypeUnitsMemSubgroup _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalClassFieldTheory.extensionSubgroupBase_normal _root_.LocalClassFieldTheory.finiteGaloisExtensionSubgroupOfEmbedding_normal _root_.LocalFieldTheory.DiscreteValuationField.Examples.Qp.padicDVRValuation_isRankOneDiscrete _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedQPadicContextAlgebra _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedQPadicContextFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.RamificationTheory.HilbertRamification.Higher.lowerRamificationGroup.instNormal _root_.RamificationTheory.HilbertRamification.ValuationSubring.inertiaGroup_normal _root_.RamificationTheory.HilbertRamification.ValuationSubring.ramificationGroupInInertiaAut_normal _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.CyclicCohomology.binaryCoefficientFamilyCommGroup _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.LocalClassFieldTheory.normalizationIntegerRingIsIntegralClosure _root_.RamificationTheory.HilbertRamification.CompleteDVF.decompositionGroupMulSemiringAction _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen
attribute [-simp] _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.IsDiscreteValuationRing.addVal_ringEquiv _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.LocalFieldTheory.DiscreteValuationField.LocalField.ratCastToQpadicClosureSubfield_apply _root_.LocalFieldTheory.DiscreteValuationField.LocalField.ratCastWithValToQpadicClosureSubfield_apply _root_.LocalFieldTheory.localIntegerValuationSubringEquiv_apply_coe _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.LocalFieldTheory.residueField_algebraMap_residue _root_.LubinTate.LubinTateSeries.standardLubinTateSeries_toPowerSeries _root_.LubinTate.SameUniformizer.coeff_recursiveIntertwiner _root_.LubinTate.SameUniformizer.constantCoeff_inVariable _root_.LubinTate.SameUniformizer.intertwinerApproximation_zero _root_.LubinTate.SameUniformizer.standardLubinTateEndomorphism_coeff_one _root_.LubinTate.standardLubinTateBaseUniformizerUnit_coe _root_.LubinTate.standardLubinTateChangedUniformizerUnit_coe _root_.LubinTate.standardLubinTateLevelGenerator_coe _root_.LubinTate.standardLubinTatePolynomialIterateOverSeparableClosure_eval _root_.LubinTate.standardLubinTatePolynomialIterate_derivative_eval_zero _root_.LubinTate.standardLubinTatePolynomialIterate_eval_zero _root_.LubinTate.standardLubinTatePolynomialIterate_zero _root_.LubinTate.standardLubinTatePolynomial_derivative_eval_zero _root_.LubinTate.standardLubinTatePolynomial_eval _root_.LubinTate.standardLubinTatePolynomial_toPowerSeries _root_.LubinTate.standardLubinTatePolynomial_toPowerSeries_eq_series _root_.LubinTate.standardLubinTatePrimitivePointInteger_coe _root_.LubinTate.standardLubinTatePrimitivePolynomialOverField_coeff_zero _root_.LubinTate.standardLubinTatePrimitivePolynomial_coeff_zero _root_.LubinTate.standardLubinTateUnitFactorFieldUnit_coe _root_.OAI.PrimeDegreePackets.ThetaConstruction.schwartzCM_apply _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteResidueActionOfHenselianDVF_apply _root_.RamificationTheory.HilbertRamification.Higher.dvfValuationSubringUnitAut_apply _root_.RamificationTheory.HilbertRamification.Higher.lowerRamificationGroup_neg_one _root_.RamificationTheory.HilbertRamification.Higher.mem_dvfHigherPrincipalUnitGroup_iff _root_.RamificationTheory.HilbertRamification.Higher.mem_lowerRamificationGroup_iff _root_.RamificationTheory.HilbertRamification.Higher.mem_valuationSubringDisplacementSubalgebraOfUniqueExtension_iff _root_.RamificationTheory.HilbertRamification.Higher.realRamificationIdeal_nat _root_.RamificationTheory.HilbertRamification.Higher.realRamificationIdeal_neg_one _root_.RamificationTheory.HilbertRamification.Higher.valuationSubringAutOfUniqueExtension_apply_coe _root_.RamificationTheory.HilbertRamification.Higher.valuationSubringAutOfUniqueExtension_apply_inv_apply _root_.RamificationTheory.HilbertRamification.Higher.valuationSubringAutOfUniqueExtension_mul_apply _root_.RamificationTheory.HilbertRamification.Higher.valuationSubringAutOfUniqueExtension_one_apply _root_.infinitePlace_mult_smul
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

/-!
# The convergent Iwasawa product for principal units

This module assembles the finite-level Iwasawa factors into a compatible
family in the principal-unit inverse limit, proves continuity and bijectivity,
and packages the resulting topological additive equivalence.
-/

/-!
# Finite-level Iwasawa generators for principal units

This file develops an explicit topological product decomposition of principal units.  In equal characteristic, choose
a residue-field basis `omega_i` over `F_p`.  For a positive degree `n`, the
prime-to-`p` Iwasawa map is

`g_n(a_i) = product_i (1 + [omega_i] pi^n) ^ a_i`.

The powers by p-adic integers are the canonical powers constructed from the
finite principal-unit quotients in `PrincipalUnitPadicAction`.  This module
constructs each finite-level factor `g_n`, proves its filtration properties,
and establishes its algebraic injectivity.  The convergent global product is
assembled in `IwasawaPrincipalUnits`.
-/

noncomputable section

open scoped BigOperators

universe u v

open ValuationTheory.DiscreteValuationField
open LocalFieldTheory.DiscreteValuationField

namespace LocalFieldTheory.DiscreteValuationField
namespace CompleteDVF
namespace higherPrincipalUnitGroup

open LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup
open Internal

variable {K : Type u} [Field K]

/-! ## Reduction of p-adic exponents on one graded layer -/

/-- Every value of `g_n` belongs to `U^n`, as asserted by its codomain in
the canonical construction. -/
theorem iwasawaGn_mem_higher
    (F : LocalField.{u, v} K)
    {pi : F.valuationSubring}
    (hpi : F.valuation.IsUniformizer (pi : K))
    (n : ℕ) (hn : 1 ≤ n)
    (a : Fin (iwasawaResidueRank F) → ℤ_[F.residueCharacteristic]) :
    ((Additive.toMul (iwasawaGn F hpi n hn a) :
        ((LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup F.toCompleteDVF)) 1) : F.valuationSubringˣ) ∈
      ((LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup F.toCompleteDVF)) n := by
  classical
  rw [iwasawaGn_apply]
  induction (Finset.univ : Finset (Fin (iwasawaResidueRank F)))
      using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
      rw [Finset.sum_insert hi]
      change
        ((Additive.toMul
            (a i • Additive.ofMul (iwasawaSeed F hpi n hn i)) :
          ((LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup F.toCompleteDVF)) 1) : F.valuationSubringˣ) *
          ((Additive.toMul
            (∑ j ∈ s, a j • Additive.ofMul (iwasawaSeed F hpi n hn j)) :
          ((LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup F.toCompleteDVF)) 1) : F.valuationSubringˣ) ∈
            ((LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup F.toCompleteDVF)) n
      apply (((LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup F.toCompleteDVF)) n).mul_mem
      · exact LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitPadic_smul_mem_higher
          F hn (a i) (iwasawaSeed F hpi n hn i)
          (iwasawaSeedAtLevel F hpi n hn i).property
      · exact ih

/-! ## Algebraic injectivity of each Iwasawa factor -/

end higherPrincipalUnitGroup
end CompleteDVF
end LocalFieldTheory.DiscreteValuationField

noncomputable section

open scoped BigOperators

open ValuationTheory.DiscreteValuationField
open LocalFieldTheory.DiscreteValuationField

namespace LocalFieldTheory.DiscreteValuationField
namespace CompleteDVF
namespace higherPrincipalUnitGroup

open LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup
open Internal

variable {K : Type u} [Field K]

/-! ## The convergent product, constructed through finite quotients -/

/--
Establishes the membership statement `((iwasawaDegreeTerm F hpi a n :
((CompleteDVF.higherPrincipalUnitGroup F.toCompleteDVF)) 1) : F.valuationSubringˣ) ∈
((CompleteDVF.higherPrincipalUnitGroup F.toCompleteDVF)) n`.
-/
theorem iwasawaDegreeTerm_mem_higher
    (F : LocalField.{u, v} K)
    {pi : F.valuationSubring}
    (hpi : F.valuation.IsUniformizer (pi : K))
    (a : iwasawaDomain F) (n : ℕ) :
    ((iwasawaDegreeTerm F hpi a n : ((LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup F.toCompleteDVF)) 1) :
      F.valuationSubringˣ) ∈ ((LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup F.toCompleteDVF)) n := by
  classical
  unfold iwasawaDegreeTerm
  split_ifs with hn
  · exact iwasawaGn_mem_higher F hpi n hn.1
      (fun i => a (⟨n, hn⟩, i))
  · exact (((LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup F.toCompleteDVF)) n).one_mem

/-- Higher-degree factors disappear in every fixed finite quotient.  Thus
the partial products define a compatible family; this is the formal
convergence argument for the infinite product. -/
theorem Internal.principalUnitQuotientCarrier_mk_iwasawaPartialProduct_eq_of_le
    (F : LocalField.{u, v} K)
    {pi : F.valuationSubring}
    (hpi : F.valuation.IsUniformizer (pi : K))
    (a : iwasawaDomain F) {m r : ℕ} (hmr : m ≤ r) :
    (higherPrincipalUnitGroup.toPrincipalUnitFiltration
        F.toCompleteDVF).principalUnitSubquotientMk
          1 (m + 1) (iwasawaPartialProduct F hpi a r) =
      (higherPrincipalUnitGroup.toPrincipalUnitFiltration
        F.toCompleteDVF).principalUnitSubquotientMk
          1 (m + 1) (iwasawaPartialProduct F hpi a m) := by
  classical
  induction r, hmr using Nat.le_induction with
  | base => rfl
  | @succ r hmr ihr =>
      rw [iwasawaPartialProduct, Finset.prod_range_succ]
      let N :=
        (((LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup
          F.toCompleteDVF)) (m + 1)).subgroupOf
            (((LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup
              F.toCompleteDVF)) 1)
      change
        QuotientGroup.mk' N
            (iwasawaPartialProduct F hpi a r *
              iwasawaDegreeTerm F hpi a (r + 1)) =
          QuotientGroup.mk' N (iwasawaPartialProduct F hpi a m)
      change
        QuotientGroup.mk' N (iwasawaPartialProduct F hpi a r) =
          QuotientGroup.mk' N (iwasawaPartialProduct F hpi a m) at ihr
      rw [map_mul, ihr]
      have hterm :
          QuotientGroup.mk' N (iwasawaDegreeTerm F hpi a (r + 1)) = 1 := by
        apply (QuotientGroup.eq_one_iff
          (N := N) (iwasawaDegreeTerm F hpi a (r + 1))).2
        change
          ((iwasawaDegreeTerm F hpi a (r + 1) :
              ((LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup F.toCompleteDVF)) 1) : F.valuationSubringˣ) ∈
            ((LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup F.toCompleteDVF)) (m + 1)
        exact LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.antitone F.toCompleteDVF
          (Nat.succ_le_succ hmr)
          (iwasawaDegreeTerm_mem_higher F hpi a (r + 1))
      rw [hterm]
      exact mul_one
        (QuotientGroup.mk' N (iwasawaPartialProduct F hpi a m))

/-- The compatible family of all finite Iwasawa partial products. -/
noncomputable def Internal.iwasawaGlobalInverseLimitCarrier
    (F : LocalField.{u, v} K)
    {pi : F.valuationSubring}
    (hpi : F.valuation.IsUniformizer (pi : K))
    (a : iwasawaDomain F) :
    Internal.principalUnitInverseLimitCarrier F.toCompleteDVF :=
  ⟨fun r =>
      (higherPrincipalUnitGroup.toPrincipalUnitFiltration
        F.toCompleteDVF).principalUnitSubquotientMk
          1 (r + 1) (iwasawaPartialProduct F hpi a r), by
    intro m r hmr
    rw [principalUnitQuotientCarrierTransition_mk]
    exact
      principalUnitQuotientCarrier_mk_iwasawaPartialProduct_eq_of_le
        F hpi a hmr⟩

/--
The defining evaluation formula for `Internal.iwasawaGlobalInverseLimitCarrier` is
`(iwasawaGlobalInverseLimitCarrier F hpi a).1 r =
(higherPrincipalUnitGroup.toPrincipalUnitFiltration F.toCompleteDVF).principalUnitSubquotientMk 1
(r + 1) (iwasawaPartialProduct F hpi a r)`.
-/
@[simp] theorem Internal.iwasawaGlobalInverseLimitCarrier_apply
    (F : LocalField.{u, v} K)
    {pi : F.valuationSubring}
    (hpi : F.valuation.IsUniformizer (pi : K))
    (a : iwasawaDomain F) (r : ℕ) :
    (iwasawaGlobalInverseLimitCarrier F hpi a).1 r =
      (higherPrincipalUnitGroup.toPrincipalUnitFiltration
        F.toCompleteDVF).principalUnitSubquotientMk
          1 (r + 1) (iwasawaPartialProduct F hpi a r) :=
  rfl

end higherPrincipalUnitGroup
end CompleteDVF
end LocalFieldTheory.DiscreteValuationField
end
end
end

section
-- module Solutions.OAIQ244_DUKE.LocalField_DiscreteValuationField_FieldUnitDecomposition
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_isCompleteDiscrete _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.AdicPrincipalUnits.instAddCommGroup _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.AdicPrincipalUnits.instTopologicalSpace _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.DiscretePrincipalUnitQuotient.instAddCommGroup _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitInverseLimitCarrierPadicModule _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitQuotientCarrierPadicModule _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.PrincipalUnitProdiscreteLimit.instAddCommGroup _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.PrincipalUnitProdiscreteLimit.instTopologicalSpace _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitPadicModule _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitPadicSMul _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.residueFieldZModAlgebra _root_.LocalFieldTheory.DiscreteValuationField.Examples.Qp.padicDVRValuation_isRankOneDiscrete _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.RamificationTheory.HilbertRamification.Higher.lowerRamificationGroup.instNormal _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.LocalClassFieldTheory.normalizationIntegerRingIsIntegralClosure _root_.RamificationTheory.HilbertRamification.CompleteDVF.decompositionGroupMulSemiringAction _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen
attribute [-simp] _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.IsDiscreteValuationRing.addVal_ringEquiv _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.EqualCharacteristicLaurent.coeffHom_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.EqualCharacteristicLaurent.powerSeriesEvalHom_C _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.EqualCharacteristicLaurent.powerSeriesEvalHom_X _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.EqualCharacteristicLaurent.powerSeriesEvalSubringHom_C _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.EqualCharacteristicLaurent.powerSeriesEvalSubringHom_X _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.AdicPrincipalUnits.addEquiv_map_smul _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.AdicPrincipalUnits.of_val _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.AdicPrincipalUnits.val_of _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.DiscretePrincipalUnitQuotient.addEquiv_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.DiscretePrincipalUnitQuotient.addEquiv_map_smul _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.DiscretePrincipalUnitQuotient.addEquiv_of _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.DiscretePrincipalUnitQuotient.addEquiv_symm_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.DiscretePrincipalUnitQuotient.of_val _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.DiscretePrincipalUnitQuotient.val_of _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.DiscretePrincipalUnitQuotient.val_transition _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.adicPrincipalUnitsHomeomorphUnderlying_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.iwasawaGlobalInverseLimitCarrier_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitAddEquivInverseLimitCarrier_map_smul _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitAddHomeomorphInverseLimitCarrier_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitInverseLimitCarrierEval_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitInverseLimitCarrierPadic_smul_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitMulEquivInverseLimitCarrier_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitPadic_smul_carrier_coordinate _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitProdiscreteLimitHomeomorphUnderlying_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitQuotientCarrierPadicScalar_eq_smul _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitQuotientCarrierToFull_mk _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitQuotientCarrierTransition_mk _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.uniformizerHigherUnitQuotientEquiv_mk _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.PrincipalUnitProdiscreteLimit.addEquiv_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.PrincipalUnitProdiscreteLimit.addEquiv_map_smul _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.PrincipalUnitProdiscreteLimit.addEquiv_symm_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.PrincipalUnitProdiscreteLimit.coordinate_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.PrincipalUnitProdiscreteLimit.of_val _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.PrincipalUnitProdiscreteLimit.val_of _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.adicPrincipalUnitsContinuousAddEquivUnderlyingOfWithZeroValuation_map_smul _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.adicPrincipalUnitsHomeomorphProdiscreteLimit_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.adicPrincipalUnitsHomeomorphProdiscreteLimit_to_addEquiv _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.iwasawaDegreeTerm_zero _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.iwasawaGn_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.iwasawaPartialProduct_zero_input _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.iwasawaSeedAtLevel_val _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.iwasawaSeedIdeal_val _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.iwasawaSeed_val _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitPadic_natCast_smul _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitPadic_nsmul_eq_pow _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitPadic_smul_def _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitSuccQuotAddEquivResidue_iwasawaSeed _root_.LocalFieldTheory.DiscreteValuationField.LocalField.laurentSeriesEquivLaurentImageSubfield_apply_coe _root_.LocalFieldTheory.IsNonarchimedeanLocalField.multiplicativeIntegerValuation_val _root_.LocalFieldTheory.localIntegerValuationSubringEquiv_apply_coe _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.LocalFieldTheory.residueField_algebraMap_residue _root_.LubinTate.LubinTateSeries.standardLubinTateSeries_toPowerSeries _root_.LubinTate.SameUniformizer.coeff_recursiveIntertwiner _root_.LubinTate.SameUniformizer.constantCoeff_inVariable _root_.LubinTate.SameUniformizer.intertwinerApproximation_zero _root_.LubinTate.SameUniformizer.standardLubinTateEndomorphism_coeff_one _root_.LubinTate.standardLubinTateBaseUniformizerUnit_coe _root_.LubinTate.standardLubinTateChangedUniformizerUnit_coe _root_.LubinTate.standardLubinTateLevelGenerator_coe _root_.LubinTate.standardLubinTatePolynomialIterateOverSeparableClosure_eval _root_.LubinTate.standardLubinTatePolynomialIterate_derivative_eval_zero _root_.LubinTate.standardLubinTatePolynomialIterate_eval_zero _root_.LubinTate.standardLubinTatePolynomialIterate_zero _root_.LubinTate.standardLubinTatePolynomial_derivative_eval_zero _root_.LubinTate.standardLubinTatePolynomial_eval _root_.LubinTate.standardLubinTatePolynomial_toPowerSeries _root_.LubinTate.standardLubinTatePolynomial_toPowerSeries_eq_series _root_.LubinTate.standardLubinTatePrimitivePointInteger_coe _root_.LubinTate.standardLubinTatePrimitivePolynomialOverField_coeff_zero _root_.LubinTate.standardLubinTatePrimitivePolynomial_coeff_zero _root_.LubinTate.standardLubinTateUnitFactorFieldUnit_coe _root_.OAI.PrimeDegreePackets.ThetaConstruction.schwartzCM_apply _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteResidueActionOfHenselianDVF_apply _root_.RamificationTheory.HilbertRamification.Higher.dvfValuationSubringUnitAut_apply _root_.RamificationTheory.HilbertRamification.Higher.lowerRamificationGroup_neg_one _root_.RamificationTheory.HilbertRamification.Higher.mem_dvfHigherPrincipalUnitGroup_iff _root_.RamificationTheory.HilbertRamification.Higher.mem_lowerRamificationGroup_iff _root_.RamificationTheory.HilbertRamification.Higher.mem_valuationSubringDisplacementSubalgebraOfUniqueExtension_iff _root_.RamificationTheory.HilbertRamification.Higher.realRamificationIdeal_nat _root_.RamificationTheory.HilbertRamification.Higher.realRamificationIdeal_neg_one _root_.RamificationTheory.HilbertRamification.Higher.valuationSubringAutOfUniqueExtension_apply_coe _root_.RamificationTheory.HilbertRamification.Higher.valuationSubringAutOfUniqueExtension_apply_inv_apply _root_.RamificationTheory.HilbertRamification.Higher.valuationSubringAutOfUniqueExtension_mul_apply _root_.RamificationTheory.HilbertRamification.Higher.valuationSubringAutOfUniqueExtension_one_apply _root_.infinitePlace_mult_smul
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

/-!
# Principal-unit decomposition

This file connects the principal-unit decomposition proved in
`PrincipalUnits` to the standard integer-valued field-unit valuation attached
to a `ℤᵐ⁰`-valued complete discrete valuation.
-/

noncomputable section

open Filter
open scoped Topology
open ValuationTheory.DiscreteValuationField
open LocalFieldTheory.DiscreteValuationField
open LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup

universe u v

namespace LocalFieldTheory.DiscreteValuationField
namespace CompleteDVF
namespace higherPrincipalUnitGroup

variable {K : Type u} [Field K]

/-- The uniformizer–residue–principal-unit decomposition, group-isomorphism form for a complete
DVF with a fixed uniformizer:
`K^* ≃ μ_{q-1} × U^1 × ℤ`. -/
noncomputable def fieldUnitsEquivRootsPrincipalUnitsUniformizer_of_completeDVF
    (F : ValuationTheory.DiscreteValuationField.CompleteDVF.{u, v} K) [Finite F.residueField]
    {π : F.valuationSubring} (hπ : F.valuation.IsUniformizer (π : K)) :
    fieldUnitDecompositionFactors F ≃* Kˣ := by
  let V : MultiplicativeIntegerValuation Kˣ :=
    (_root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.multiplicativeIntegerValuationOfUniformizer F) hπ
  have hzero : V.zeroSubgroup = F.valuation.valuationSubring.unitGroup := by
    simpa [V] using
      (_root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.multiplicativeIntegerValuationOfUniformizer_zeroSubgroup_eq_unitGroup F)
        hπ
  have hπV :
      V.IsUniformizer (Units.mk0 (π : K) hπ.ne_zero) := by
    simpa [V] using
      (_root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.multiplicativeIntegerValuationOfUniformizer_isUniformizer F) hπ
  exact
    fieldUnitsEquivRootsPrincipalUnitsUniformizer_of_zeroSubgroup_eq_unitGroup
      (F := F) V hzero hπV

/--
The defining evaluation formula for `fieldUnitsEquivRootsPrincipalUnitsUniformizer_of_completeDVF`
is `fieldUnitsEquivRootsPrincipalUnitsUniformizer_of_completeDVF F hπ z =
valuationSubringUnitFieldUnitHom F (z.1.1 : F.valuationSubringˣ) *
valuationSubringUnitFieldUnitHom F (z.1.2 : F.valuationSubringˣ) * (Units.mk0 (π : K) hπ.ne_zero)
^ Multiplicative.toAdd z.2`.
-/
@[simp]
theorem fieldUnitsEquivRootsPrincipalUnitsUniformizer_of_completeDVF_apply
    (F : ValuationTheory.DiscreteValuationField.CompleteDVF.{u, v} K) [Finite F.residueField]
    {π : F.valuationSubring} (hπ : F.valuation.IsUniformizer (π : K))
    (z : fieldUnitDecompositionFactors F) :
    fieldUnitsEquivRootsPrincipalUnitsUniformizer_of_completeDVF
        F hπ z =
      valuationSubringUnitFieldUnitHom F
          (z.1.1 : F.valuationSubringˣ) *
        valuationSubringUnitFieldUnitHom F
          (z.1.2 : F.valuationSubringˣ) *
        (Units.mk0 (π : K) hπ.ne_zero) ^ Multiplicative.toAdd z.2 := by
  let V : MultiplicativeIntegerValuation Kˣ :=
    (_root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.multiplicativeIntegerValuationOfUniformizer F) hπ
  have hzero : V.zeroSubgroup = F.valuation.valuationSubring.unitGroup := by
    simpa [V] using
      (_root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.multiplicativeIntegerValuationOfUniformizer_zeroSubgroup_eq_unitGroup F)
        hπ
  have hπV :
      V.IsUniformizer (Units.mk0 (π : K) hπ.ne_zero) := by
    simpa [V] using
      (_root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.multiplicativeIntegerValuationOfUniformizer_isUniformizer F) hπ
  have happ :=
    fieldUnitsEquivRootsPrincipalUnitsUniformizer_apply
      F V
      (fun y =>
        mem_zeroSubgroup_iff_exists_valuationSubringUnitFieldUnitHom_eq
          (F := F) V hzero y)
      hπV z
  simp [fieldUnitsEquivRootsPrincipalUnitsUniformizer_of_completeDVF,
    fieldUnitsEquivRootsPrincipalUnitsUniformizer_of_zeroSubgroup_eq_unitGroup]

/--
Establishes the membership statement `x * (Units.mk0 (π : K) hπ.ne_zero) ^
(-((CompleteDVF.uniformizerValueExponent F) hπ x)) ∈ F.valuation.valuationSubring.unitGroup`.
-/
theorem fieldUnitsEquivRootsPrincipalUnitsUniformizer_unitPart_mem_unitGroup
    (F : ValuationTheory.DiscreteValuationField.CompleteDVF.{u, v} K)
    {π : F.valuationSubring} (hπ : F.valuation.IsUniformizer (π : K))
    (x : Kˣ) :
    x * (Units.mk0 (π : K) hπ.ne_zero) ^
        (-((_root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.uniformizerValueExponent F) hπ x)) ∈
      F.valuation.valuationSubring.unitGroup := by
  let V : MultiplicativeIntegerValuation Kˣ :=
    (_root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.multiplicativeIntegerValuationOfUniformizer F) hπ
  have hzero :
      V.zeroSubgroup = F.valuation.valuationSubring.unitGroup := by
    simpa [V] using
      (_root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.multiplicativeIntegerValuationOfUniformizer_zeroSubgroup_eq_unitGroup F) hπ
  have hπV :
      V.IsUniformizer (Units.mk0 (π : K) hπ.ne_zero) := by
    simpa [V] using
      (_root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.multiplicativeIntegerValuationOfUniformizer_isUniformizer F) hπ
  have hmem :
      x * (Units.mk0 (π : K) hπ.ne_zero) ^
          (-((_root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.uniformizerValueExponent F) hπ x)) ∈
        V.zeroSubgroup := by
    rw [V.mem_zeroSubgroup_iff, V.val_mul, V.val_uniformizer_zpow hπV]
    simp [V]
  simpa [hzero] using hmem

/-- The valuation-ring unit obtained by removing the uniformizer power from a
field unit. -/
noncomputable def fieldUnitUniformizerUnitPart
    (F : ValuationTheory.DiscreteValuationField.CompleteDVF.{u, v} K)
    {π : F.valuationSubring} (hπ : F.valuation.IsUniformizer (π : K))
    (x : Kˣ) : F.valuationSubringˣ :=
  F.valuation.valuationSubring.unitGroupMulEquiv
    ⟨x * (Units.mk0 (π : K) hπ.ne_zero) ^
        (-((_root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.uniformizerValueExponent F) hπ x)),
      fieldUnitsEquivRootsPrincipalUnitsUniformizer_unitPart_mem_unitGroup
        F hπ x⟩

/--
Establishes the identity `valuationSubringUnitFieldUnitHom F (fieldUnitUniformizerUnitPart F hπ x)
= x * (Units.mk0 (π : K) hπ.ne_zero) ^ (-((CompleteDVF.uniformizerValueExponent F) hπ x))`.
-/
@[simp]
theorem valuationSubringUnitFieldUnitHom_fieldUnitUniformizerUnitPart
    (F : ValuationTheory.DiscreteValuationField.CompleteDVF.{u, v} K)
    {π : F.valuationSubring} (hπ : F.valuation.IsUniformizer (π : K))
    (x : Kˣ) :
    valuationSubringUnitFieldUnitHom F
        (fieldUnitUniformizerUnitPart F hπ x) =
      x * (Units.mk0 (π : K) hπ.ne_zero) ^
        (-((_root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.uniformizerValueExponent F) hπ x)) := by
  apply Units.ext
  simp [valuationSubringUnitFieldUnitHom, fieldUnitUniformizerUnitPart]

end higherPrincipalUnitGroup
end CompleteDVF
end LocalFieldTheory.DiscreteValuationField

end
end

section
-- module Solutions.OAIQ244_DUKE.LocalField_Analytic_LogExpSeries_SeriesTerms
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.LubinTate.compatibleGroupFamiliesGroup _root_.OAI.PrimeDegreePackets.instNonemptyLeafTestSpace _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.RayClass.approximationCompletionTopologicalSpace _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.LocalClassFieldTheory.normalizationIntegerRingIsIntegralClosure _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen
attribute [-simp] _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.IsDiscreteValuationRing.addVal_ringEquiv _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.LocalFieldTheory.IsNonarchimedeanLocalField.multiplicativeIntegerValuation_val _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.LocalFieldTheory.residueField_algebraMap_residue _root_.OAI.PrimeDegreePackets.ThetaConstruction.schwartzCM_apply _root_.infinitePlace_mult_smul
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false
/-!
Defines the logarithm and exponential series terms and proves the valuation estimates used in
their convergence arguments.
-/

open Filter
open Polynomial
open scoped Topology
open scoped PowerSeries.WithPiTopology
noncomputable section

attribute [local instance] Classical.propDecidable

universe u

open ValuationTheory.DiscreteValuationField
open LocalFieldTheory.DiscreteValuationField

namespace LocalFieldTheory.DiscreteValuationField
namespace MultiplicativeIntegerValuation

variable {K : Type u} [Field K]

/-! ### Exponential-series terms -/

/-- If a nonzero field element has valuation strictly below one, then its
attached integer valuation as a field unit is positive. -/
theorem ofWithZeroValuation_val_mk0_pos_of_lt_one
    (v : _root_.Valuation K (WithZero (Multiplicative ℤ)))
    {x : K} (hx : x ≠ 0)
    (hvx : v x < (1 : WithZero (Multiplicative ℤ))) :
    0 < (ofWithZeroValuation v).val (Units.mk0 x hx) := by
  have hxv_ne : v x ≠ 0 := (_root_.Valuation.ne_zero_iff v).2 hx
  have hlogneg : WithZero.log (v x) < (0 : ℤ) := by
    have hloglt :
        WithZero.log (v x) <
          WithZero.log (1 : WithZero (Multiplicative ℤ)) := by
      rw [WithZero.log_lt_log hxv_ne one_ne_zero]
      exact hvx
    simpa using hloglt
  rw [ofWithZeroValuation_val]
  simpa using (neg_pos.mpr hlogneg)

/-- If a nonzero element lies below `exp (-1)` in the normalized
`ℤᵐ⁰`-valuation, then its attached integer valuation is strictly bigger than
one.  This is the field-element radius used for the exponential series. -/
theorem ofWithZeroValuation_val_mk0_one_lt_of_lt_exp_neg_one
    (v : _root_.Valuation K (WithZero (Multiplicative ℤ)))
    {x : K} (hx : x ≠ 0)
    (hvx : v x < WithZero.exp (-1 : ℤ)) :
    1 < ((ofWithZeroValuation v).val (Units.mk0 x hx) : ℝ) := by
  have hxv_ne : v x ≠ 0 := (_root_.Valuation.ne_zero_iff v).2 hx
  have hloglt : WithZero.log (v x) < (-1 : ℤ) := by
    simpa using
      ((WithZero.log_lt_log hxv_ne
        (WithZero.exp_ne_zero (a := (-1 : ℤ)))).2 hvx)
  have hint : (1 : ℤ) < -WithZero.log (v x) := by
    linarith
  have hreal : (1 : ℝ) < ((-WithZero.log (v x) : ℤ) : ℝ) := by
    exact_mod_cast hint
  simpa [ofWithZeroValuation_val] using hreal

/-- Positive attached integer valuation is the same direction as lying in the
open unit ball for the original `ℤᵐ⁰`-valued valuation. -/
theorem valuation_lt_one_of_ofWithZeroValuation_val_pos
    (v : _root_.Valuation K (WithZero (Multiplicative ℤ))) (x : Kˣ)
    (hpos : 0 < (ofWithZeroValuation v).val x) :
    v (x : K) < (1 : WithZero (Multiplicative ℤ)) := by
  have hxv_ne : v (x : K) ≠ 0 :=
    (_root_.Valuation.ne_zero_iff v).2 x.ne_zero
  have hlogneg : WithZero.log (v (x : K)) < (0 : ℤ) := by
    rw [ofWithZeroValuation_val] at hpos
    linarith
  rw [← WithZero.log_lt_log hxv_ne one_ne_zero]
  simpa using hlogneg

/-- Integer-valued valuation comparison, translated back to the original
`ℤᵐ⁰`-valued valuation.  Larger integer value means smaller `WithZero` value. -/
theorem valuation_lt_of_ofWithZeroValuation_val_lt
    (v : _root_.Valuation K (WithZero (Multiplicative ℤ))) {x y : Kˣ}
    (hxy : (ofWithZeroValuation v).val x <
      (ofWithZeroValuation v).val y) :
    v (y : K) < v (x : K) := by
  have hxv_ne : v (x : K) ≠ 0 :=
    (_root_.Valuation.ne_zero_iff v).2 x.ne_zero
  have hyv_ne : v (y : K) ≠ 0 :=
    (_root_.Valuation.ne_zero_iff v).2 y.ne_zero
  have hlog : WithZero.log (v (y : K)) < WithZero.log (v (x : K)) := by
    rw [ofWithZeroValuation_val, ofWithZeroValuation_val] at hxy
    linarith
  rw [← WithZero.log_lt_log hyv_ne hxv_ne]
  exact hlog

/-- Equal `ℤᵐ⁰`-valued valuations give equal integer valuations after passing
to `ofWithZeroValuation`. -/
theorem ofWithZeroValuation_val_eq_of_valuation_eq
    (v : _root_.Valuation K (WithZero (Multiplicative ℤ))) {x y : Kˣ}
    (hxy : v (x : K) = v (y : K)) :
    (ofWithZeroValuation v).val x = (ofWithZeroValuation v).val y := by
  simp [ofWithZeroValuation_val, hxy]

/-- The integer valuation attached to a nonarchimedean `ℤᵐ⁰`-valuation is
bounded below by the minimum under addition. -/
theorem ofWithZeroValuation_val_add_ge_min
    (v : _root_.Valuation K (WithZero (Multiplicative ℤ)))
    {x y : K} (hx : x ≠ 0) (hy : y ≠ 0) (hxy : x + y ≠ 0) :
    min ((ofWithZeroValuation v).val (Units.mk0 x hx))
        ((ofWithZeroValuation v).val (Units.mk0 y hy)) ≤
      (ofWithZeroValuation v).val (Units.mk0 (x + y) hxy) := by
  have hsum : v (x + y) ≤ max (v x) (v y) :=
    map_add_le_max v x y
  by_cases hxyv : v x ≤ v y
  · have hsum_y : v (x + y) ≤ v y := by
      simpa [max_eq_right hxyv] using hsum
    have hsum_ne : v (x + y) ≠ 0 :=
      (_root_.Valuation.ne_zero_iff v).2 hxy
    have hy_ne : v y ≠ 0 :=
      (_root_.Valuation.ne_zero_iff v).2 hy
    have hlog :
        WithZero.log (v (x + y)) ≤ WithZero.log (v y) :=
      (WithZero.log_le_log hsum_ne hy_ne).2 hsum_y
    have hy_le_sum :
        (ofWithZeroValuation v).val (Units.mk0 y hy) ≤
          (ofWithZeroValuation v).val (Units.mk0 (x + y) hxy) := by
      simp [ofWithZeroValuation_val]
      linarith
    exact le_trans (min_le_right _ _) hy_le_sum
  · have hyxv : v y ≤ v x := le_of_not_ge hxyv
    have hsum_x : v (x + y) ≤ v x := by
      simpa [max_eq_left hyxv] using hsum
    have hsum_ne : v (x + y) ≠ 0 :=
      (_root_.Valuation.ne_zero_iff v).2 hxy
    have hx_ne : v x ≠ 0 :=
      (_root_.Valuation.ne_zero_iff v).2 hx
    have hlog :
        WithZero.log (v (x + y)) ≤ WithZero.log (v x) :=
      (WithZero.log_le_log hsum_ne hx_ne).2 hsum_x
    have hx_le_sum :
        (ofWithZeroValuation v).val (Units.mk0 x hx) ≤
          (ofWithZeroValuation v).val (Units.mk0 (x + y) hxy) := by
      simp [ofWithZeroValuation_val]
      linarith
    exact le_trans (min_le_left _ _) hx_le_sum

/-- The field-unit logarithm theorem, logarithm-series valuation estimate:
if `x` has positive integer valuation, then the valuations of
`x^(n+1)/(n+1)` tend to `+∞`. -/
theorem ofWithZeroValuation_val_log_term_tendsto_atTop_of_pos
    (v : _root_.Valuation K (WithZero (Multiplicative ℤ)))
    {p : ℕ} [Fact p.Prime] (x : Kˣ)
    (hnK : ∀ n : ℕ, (((n + 1 : ℕ) : K) ≠ 0))
    (hnval : ∀ n : ℕ,
      v (((n + 1 : ℕ) : K)) =
        WithZero.exp (-(padicValNat p (n + 1) : ℤ)))
    (hxpos : 0 < (ofWithZeroValuation v).val x) :
    Tendsto
      (fun n : ℕ =>
        ((ofWithZeroValuation v).val
          (x ^ (n + 1) /
            Units.mk0 (((n + 1 : ℕ) : K)) (hnK n)) : ℝ))
      atTop atTop := by
  have hxone : (1 : ℤ) ≤ (ofWithZeroValuation v).val x := by
    omega
  have hxoneReal : (1 : ℝ) ≤ ((ofWithZeroValuation v).val x : ℝ) := by
    exact_mod_cast hxone
  exact
    ofWithZeroValuation_val_pow_succ_div_natCast_tendsto_atTop
      (v := v) (p := p) x hnK hnval
      (hcpos := by norm_num)
      (hc := hxoneReal)

/-- Eventually the logarithm-series terms have valuation at least any prescribed
integer bound. -/
theorem eventually_le_ofWithZeroValuation_val_log_term_of_pos
    (v : _root_.Valuation K (WithZero (Multiplicative ℤ)))
    {p : ℕ} [Fact p.Prime] (x : Kˣ)
    (hnK : ∀ n : ℕ, (((n + 1 : ℕ) : K) ≠ 0))
    (hnval : ∀ n : ℕ,
      v (((n + 1 : ℕ) : K)) =
        WithZero.exp (-(padicValNat p (n + 1) : ℤ)))
    (hxpos : 0 < (ofWithZeroValuation v).val x)
    (N : ℤ) :
    ∀ᶠ n : ℕ in atTop,
      N ≤
        (ofWithZeroValuation v).val
          (x ^ (n + 1) /
            Units.mk0 (((n + 1 : ℕ) : K)) (hnK n)) := by
  have htendsto :=
    ofWithZeroValuation_val_log_term_tendsto_atTop_of_pos
      (v := v) (p := p) x hnK hnval hxpos
  have hreal :
      ∀ᶠ n : ℕ in atTop,
        (N : ℝ) ≤
          ((ofWithZeroValuation v).val
            (x ^ (n + 1) /
              Units.mk0 (((n + 1 : ℕ) : K)) (hnK n)) : ℝ) :=
    tendsto_atTop.1 htendsto (N : ℝ)
  filter_upwards [hreal] with n hn
  exact_mod_cast hn

/-- The signed logarithm-series terms also tend to zero.  This is the form
matching the usual series for `log (1 + x)`. -/
theorem tendsto_zero_signed_log_term_ofWithZeroValuation_of_pos
    (v : _root_.Valuation K (WithZero (Multiplicative ℤ)))
    {p : ℕ} [Fact p.Prime] (x : Kˣ)
    (hnK : ∀ n : ℕ, (((n + 1 : ℕ) : K) ≠ 0))
    (hnval : ∀ n : ℕ,
      v (((n + 1 : ℕ) : K)) =
        WithZero.exp (-(padicValNat p (n + 1) : ℤ)))
    (hxpos : 0 < (ofWithZeroValuation v).val x) :
    letI : Valued K (WithZero (Multiplicative ℤ)) := Valued.mk' v
    Tendsto
      (fun n : ℕ =>
        (-1 : K) ^ n *
          ((x ^ (n + 1) /
            Units.mk0 (((n + 1 : ℕ) : K)) (hnK n) : Kˣ) : K))
      atTop (𝓝 (0 : K)) := by
  let : Valued K (WithZero (Multiplicative ℤ)) := Valued.mk' v
  rw [tendsto_iff_forall_eventually_mem]
  intro s hs
  rw [Valued.mem_nhds_zero] at hs
  rcases hs with ⟨γ, hγs⟩
  let γ' : (WithZero (Multiplicative ℤ))ˣ :=
    Units.map (MonoidWithZeroHom.ValueGroup₀.embedding
      (f := (.ofClass v))) γ
  rcases WithZero.exists_exp_neg_natCast_lt γ'.ne_zero with ⟨N, hNγ⟩
  have hterm :=
    eventually_le_ofWithZeroValuation_val_log_term_of_pos
      (v := v) (p := p) x hnK hnval hxpos (N : ℤ)
  filter_upwards [hterm] with n hn
  apply hγs
  let y : Kˣ :=
    x ^ (n + 1) /
      Units.mk0 (((n + 1 : ℕ) : K)) (hnK n)
  have hlog :
      WithZero.log (v (y : K)) ≤ -(N : ℤ) := by
    have hNlog : (N : ℤ) ≤ -WithZero.log (v (y : K)) := by
      simpa [y, ofWithZeroValuation_val] using hn
    linarith
  have hvle : v (y : K) ≤ WithZero.exp (-(N : ℤ)) :=
    WithZero.le_exp_of_log_le hlog
  have hsign : v ((-1 : K) ^ n) = 1 := by
    rw [v.map_pow]
    simp
  have hvsigned :
      v ((-1 : K) ^ n * (y : K)) ≤ WithZero.exp (-(N : ℤ)) := by
    rw [v.map_mul, hsign, one_mul]
    exact hvle
  change v.restrict ((-1 : K) ^ n * (y : K)) < γ.1
  rw [Valuation.restrict_lt_iff_lt_embedding]
  exact lt_of_le_of_lt hvsigned (by simpa [γ'] using hNγ)

/-- Ramified-denominator version of the logarithm-series valuation estimate:
if integer denominators have value `e * v_p(n)`, positive valuation of `x`
still forces `x^(n+1)/(n+1)` to tend to zero. -/
theorem ofWithZeroValuation_val_log_term_scaled_tendsto_atTop_of_pos
    (v : _root_.Valuation K (WithZero (Multiplicative ℤ)))
    {p : ℕ} [Fact p.Prime] (e : ℕ) (x : Kˣ)
    (hnK : ∀ n : ℕ, (((n + 1 : ℕ) : K) ≠ 0))
    (hnval : ∀ n : ℕ,
      v (((n + 1 : ℕ) : K)) =
        WithZero.exp (-((e : ℤ) * (padicValNat p (n + 1) : ℤ))))
    (hxpos : 0 < (ofWithZeroValuation v).val x) :
    Tendsto
      (fun n : ℕ =>
        ((ofWithZeroValuation v).val
          (x ^ (n + 1) /
            Units.mk0 (((n + 1 : ℕ) : K)) (hnK n)) : ℝ))
      atTop atTop := by
  have hxone : (1 : ℤ) ≤ (ofWithZeroValuation v).val x := by
    omega
  have hxoneReal : (1 : ℝ) ≤ ((ofWithZeroValuation v).val x : ℝ) := by
    exact_mod_cast hxone
  exact
    ofWithZeroValuation_val_pow_succ_div_natCast_scaled_tendsto_atTop
      (v := v) (p := p) e x hnK hnval
      (hcpos := by norm_num)
      (hc := hxoneReal)

/-- Eventually the ramified-denominator logarithm-series terms have valuation
at least any prescribed integer bound. -/
theorem eventually_le_ofWithZeroValuation_val_log_term_scaled_of_pos
    (v : _root_.Valuation K (WithZero (Multiplicative ℤ)))
    {p : ℕ} [Fact p.Prime] (e : ℕ) (x : Kˣ)
    (hnK : ∀ n : ℕ, (((n + 1 : ℕ) : K) ≠ 0))
    (hnval : ∀ n : ℕ,
      v (((n + 1 : ℕ) : K)) =
        WithZero.exp (-((e : ℤ) * (padicValNat p (n + 1) : ℤ))))
    (hxpos : 0 < (ofWithZeroValuation v).val x)
    (N : ℤ) :
    ∀ᶠ n : ℕ in atTop,
      N ≤
        (ofWithZeroValuation v).val
          (x ^ (n + 1) /
            Units.mk0 (((n + 1 : ℕ) : K)) (hnK n)) := by
  have htendsto :=
    ofWithZeroValuation_val_log_term_scaled_tendsto_atTop_of_pos
      (v := v) (p := p) e x hnK hnval hxpos
  have hreal :
      ∀ᶠ n : ℕ in atTop,
        (N : ℝ) ≤
          ((ofWithZeroValuation v).val
            (x ^ (n + 1) /
              Units.mk0 (((n + 1 : ℕ) : K)) (hnK n)) : ℝ) :=
    tendsto_atTop.1 htendsto (N : ℝ)
  filter_upwards [hreal] with n hn
  exact_mod_cast hn

/-- The signed logarithm-series terms tend to zero under the ramified
denominator valuation hypothesis. -/
theorem tendsto_zero_signed_log_term_ofWithZeroValuation_scaled_of_pos
    (v : _root_.Valuation K (WithZero (Multiplicative ℤ)))
    {p : ℕ} [Fact p.Prime] (e : ℕ) (x : Kˣ)
    (hnK : ∀ n : ℕ, (((n + 1 : ℕ) : K) ≠ 0))
    (hnval : ∀ n : ℕ,
      v (((n + 1 : ℕ) : K)) =
        WithZero.exp (-((e : ℤ) * (padicValNat p (n + 1) : ℤ))))
    (hxpos : 0 < (ofWithZeroValuation v).val x) :
    letI : Valued K (WithZero (Multiplicative ℤ)) := Valued.mk' v
    Tendsto
      (fun n : ℕ =>
        (-1 : K) ^ n *
          ((x ^ (n + 1) /
            Units.mk0 (((n + 1 : ℕ) : K)) (hnK n) : Kˣ) : K))
      atTop (𝓝 (0 : K)) := by
  let : Valued K (WithZero (Multiplicative ℤ)) := Valued.mk' v
  rw [tendsto_iff_forall_eventually_mem]
  intro s hs
  rw [Valued.mem_nhds_zero] at hs
  rcases hs with ⟨γ, hγs⟩
  let γ' : (WithZero (Multiplicative ℤ))ˣ :=
    Units.map (MonoidWithZeroHom.ValueGroup₀.embedding
      (f := (.ofClass v))) γ
  rcases WithZero.exists_exp_neg_natCast_lt γ'.ne_zero with ⟨N, hNγ⟩
  have hterm :=
    eventually_le_ofWithZeroValuation_val_log_term_scaled_of_pos
      (v := v) (p := p) e x hnK hnval hxpos (N : ℤ)
  filter_upwards [hterm] with n hn
  apply hγs
  let y : Kˣ :=
    x ^ (n + 1) /
      Units.mk0 (((n + 1 : ℕ) : K)) (hnK n)
  have hlog :
      WithZero.log (v (y : K)) ≤ -(N : ℤ) := by
    have hNlog : (N : ℤ) ≤ -WithZero.log (v (y : K)) := by
      simpa [y, ofWithZeroValuation_val] using hn
    linarith
  have hvle : v (y : K) ≤ WithZero.exp (-(N : ℤ)) :=
    WithZero.le_exp_of_log_le hlog
  have hsign : v ((-1 : K) ^ n) = 1 := by
    rw [v.map_pow]
    simp
  have hvsigned :
      v ((-1 : K) ^ n * (y : K)) ≤ WithZero.exp (-(N : ℤ)) := by
    rw [v.map_mul, hsign, one_mul]
    exact hvle
  change v.restrict ((-1 : K) ^ n * (y : K)) < γ.1
  rw [Valuation.restrict_lt_iff_lt_embedding]
  exact lt_of_le_of_lt hvsigned (by simpa [γ'] using hNγ)

end MultiplicativeIntegerValuation
end LocalFieldTheory.DiscreteValuationField

end
end

section
-- module Solutions.OAIQ244_DUKE.LocalField_Analytic_LogExpSeries_ExpConvergence
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.LubinTate.compatibleGroupFamiliesGroup _root_.OAI.PrimeDegreePackets.instNonemptyLeafTestSpace _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.OAI.PrimeDegreePackets.xT2Space _root_.RayClass.approximationCompletionTopologicalSpace _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.LocalClassFieldTheory.intrinsicAbsoluteGaloisT2 _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.LocalClassFieldTheory.normalizationIntegerRingIsIntegralClosure _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen
attribute [-simp] _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.IsDiscreteValuationRing.addVal_ringEquiv _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.LocalFieldTheory.IsNonarchimedeanLocalField.multiplicativeIntegerValuation_val _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.LocalFieldTheory.residueField_algebraMap_residue _root_.OAI.PrimeDegreePackets.ThetaConstruction.schwartzCM_apply _root_.infinitePlace_mult_smul
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false
/-!
Establishes convergence and summability of the exponential series on sufficiently deep
nonarchimedean ideals.
-/

open Filter
open Polynomial
open scoped Topology
open scoped PowerSeries.WithPiTopology
noncomputable section

attribute [local instance] Classical.propDecidable

universe u

open ValuationTheory.DiscreteValuationField
open LocalFieldTheory.DiscreteValuationField

namespace LocalFieldTheory.DiscreteValuationField
namespace MultiplicativeIntegerValuation

variable {K : Type u} [Field K]

/-- The field-unit logarithm theorem, exponential-series valuation estimate:
if `x` has integer valuation strictly bigger than one, then the valuations of
`x^n / n!` tend to `+∞`. -/
theorem ofWithZeroValuation_val_exp_term_tendsto_atTop_of_one_lt
    (v : _root_.Valuation K (WithZero (Multiplicative ℤ)))
    {p : ℕ} [Fact p.Prime] (x : Kˣ)
    (hnK : ∀ n : ℕ, (((n.factorial : ℕ) : K) ≠ 0))
    (hnval : ∀ n : ℕ,
      v (((n.factorial : ℕ) : K)) =
        WithZero.exp (-(padicValNat p n.factorial : ℤ)))
    (hxone : 1 < ((ofWithZeroValuation v).val x : ℝ)) :
    Tendsto
      (fun n : ℕ =>
        ((ofWithZeroValuation v).val
          (x ^ n /
            Units.mk0 (((n.factorial : ℕ) : K)) (hnK n)) : ℝ))
      atTop atTop :=
  ofWithZeroValuation_val_pow_div_natCast_factorial_tendsto_atTop
    (v := v) (p := p) x hnK hnval
    (c := ((ofWithZeroValuation v).val x : ℝ)) hxone le_rfl

/-- Eventually the exponential-series terms have valuation at least any
prescribed integer bound. -/
theorem eventually_le_ofWithZeroValuation_val_exp_term_of_one_lt
    (v : _root_.Valuation K (WithZero (Multiplicative ℤ)))
    {p : ℕ} [Fact p.Prime] (x : Kˣ)
    (hnK : ∀ n : ℕ, (((n.factorial : ℕ) : K) ≠ 0))
    (hnval : ∀ n : ℕ,
      v (((n.factorial : ℕ) : K)) =
        WithZero.exp (-(padicValNat p n.factorial : ℤ)))
    (hxone : 1 < ((ofWithZeroValuation v).val x : ℝ))
    (N : ℤ) :
    ∀ᶠ n : ℕ in atTop,
      N ≤
        (ofWithZeroValuation v).val
          (x ^ n /
            Units.mk0 (((n.factorial : ℕ) : K)) (hnK n)) := by
  have htendsto :=
    ofWithZeroValuation_val_exp_term_tendsto_atTop_of_one_lt
      (v := v) (p := p) x hnK hnval hxone
  have hreal :
      ∀ᶠ n : ℕ in atTop,
        (N : ℝ) ≤
          ((ofWithZeroValuation v).val
            (x ^ n /
              Units.mk0 (((n.factorial : ℕ) : K)) (hnK n)) : ℝ) :=
    tendsto_atTop.1 htendsto (N : ℝ)
  filter_upwards [hreal] with n hn
  exact_mod_cast hn

/-- The exponential-series terms tend to zero in the topology defined by the
given `ℤᵐ⁰`-valued valuation. -/
theorem tendsto_zero_exp_term_ofWithZeroValuation_of_one_lt
    (v : _root_.Valuation K (WithZero (Multiplicative ℤ)))
    {p : ℕ} [Fact p.Prime] (x : Kˣ)
    (hnK : ∀ n : ℕ, (((n.factorial : ℕ) : K) ≠ 0))
    (hnval : ∀ n : ℕ,
      v (((n.factorial : ℕ) : K)) =
        WithZero.exp (-(padicValNat p n.factorial : ℤ)))
    (hxone : 1 < ((ofWithZeroValuation v).val x : ℝ)) :
    letI : Valued K (WithZero (Multiplicative ℤ)) := Valued.mk' v
    Tendsto
      (fun n : ℕ =>
        ((x ^ n /
          Units.mk0 (((n.factorial : ℕ) : K)) (hnK n) : Kˣ) : K))
      atTop (𝓝 (0 : K)) := by
  let : Valued K (WithZero (Multiplicative ℤ)) := Valued.mk' v
  rw [tendsto_iff_forall_eventually_mem]
  intro s hs
  rw [Valued.mem_nhds_zero] at hs
  rcases hs with ⟨γ, hγs⟩
  let γ' : (WithZero (Multiplicative ℤ))ˣ :=
    Units.map (MonoidWithZeroHom.ValueGroup₀.embedding
      (f := (.ofClass v))) γ
  rcases WithZero.exists_exp_neg_natCast_lt γ'.ne_zero with ⟨N, hNγ⟩
  have hterm :=
    eventually_le_ofWithZeroValuation_val_exp_term_of_one_lt
      (v := v) (p := p) x hnK hnval hxone (N : ℤ)
  filter_upwards [hterm] with n hn
  apply hγs
  let y : Kˣ :=
    x ^ n /
      Units.mk0 (((n.factorial : ℕ) : K)) (hnK n)
  have hlog :
      WithZero.log (v (y : K)) ≤ -(N : ℤ) := by
    have hNlog : (N : ℤ) ≤ -WithZero.log (v (y : K)) := by
      simpa [y, ofWithZeroValuation_val] using hn
    linarith
  have hvle : v (y : K) ≤ WithZero.exp (-(N : ℤ)) :=
    WithZero.le_exp_of_log_le hlog
  change v.restrict (y : K) < γ.1
  rw [Valuation.restrict_lt_iff_lt_embedding]
  exact lt_of_le_of_lt hvle (by simpa [γ'] using hNγ)

/-- Sharp ramified version of the exponential-series valuation estimate:
if `x` has integer valuation strictly bigger than `e/(p-1)`, then the
valuations of `x^n / n!` tend to `+∞`. -/
theorem ofWithZeroValuation_val_exp_term_scaled_tendsto_atTop_of_threshold
    (v : _root_.Valuation K (WithZero (Multiplicative ℤ)))
    {p : ℕ} [Fact p.Prime] (e : ℕ) (x : Kˣ)
    (hnK : ∀ n : ℕ, (((n.factorial : ℕ) : K) ≠ 0))
    (hnval : ∀ n : ℕ,
      v (((n.factorial : ℕ) : K)) =
        WithZero.exp (-((e : ℤ) * (padicValNat p n.factorial : ℤ))))
    (hxthreshold :
      (e : ℝ) / ((p : ℝ) - 1) <
        ((ofWithZeroValuation v).val x : ℝ)) :
    Tendsto
      (fun n : ℕ =>
        ((ofWithZeroValuation v).val
          (x ^ n /
            Units.mk0 (((n.factorial : ℕ) : K)) (hnK n)) : ℝ))
      atTop atTop :=
  ofWithZeroValuation_val_pow_div_natCast_factorial_scaled_tendsto_atTop
    (v := v) (p := p) e x hnK hnval
    (c := ((ofWithZeroValuation v).val x : ℝ)) hxthreshold le_rfl

/-- Eventually the ramified exponential-series terms have valuation at least
any prescribed integer bound. -/
theorem eventually_le_ofWithZeroValuation_val_exp_term_scaled_of_threshold
    (v : _root_.Valuation K (WithZero (Multiplicative ℤ)))
    {p : ℕ} [Fact p.Prime] (e : ℕ) (x : Kˣ)
    (hnK : ∀ n : ℕ, (((n.factorial : ℕ) : K) ≠ 0))
    (hnval : ∀ n : ℕ,
      v (((n.factorial : ℕ) : K)) =
        WithZero.exp (-((e : ℤ) * (padicValNat p n.factorial : ℤ))))
    (hxthreshold :
      (e : ℝ) / ((p : ℝ) - 1) <
        ((ofWithZeroValuation v).val x : ℝ))
    (N : ℤ) :
    ∀ᶠ n : ℕ in atTop,
      N ≤
        (ofWithZeroValuation v).val
          (x ^ n /
            Units.mk0 (((n.factorial : ℕ) : K)) (hnK n)) := by
  have htendsto :=
    ofWithZeroValuation_val_exp_term_scaled_tendsto_atTop_of_threshold
      (v := v) (p := p) e x hnK hnval hxthreshold
  have hreal :
      ∀ᶠ n : ℕ in atTop,
        (N : ℝ) ≤
          ((ofWithZeroValuation v).val
            (x ^ n /
              Units.mk0 (((n.factorial : ℕ) : K)) (hnK n)) : ℝ) :=
    tendsto_atTop.1 htendsto (N : ℝ)
  filter_upwards [hreal] with n hn
  exact_mod_cast hn

/-- The exponential-series terms tend to zero under the sharp ramified
threshold. -/
theorem tendsto_zero_exp_term_ofWithZeroValuation_scaled_of_threshold
    (v : _root_.Valuation K (WithZero (Multiplicative ℤ)))
    {p : ℕ} [Fact p.Prime] (e : ℕ) (x : Kˣ)
    (hnK : ∀ n : ℕ, (((n.factorial : ℕ) : K) ≠ 0))
    (hnval : ∀ n : ℕ,
      v (((n.factorial : ℕ) : K)) =
        WithZero.exp (-((e : ℤ) * (padicValNat p n.factorial : ℤ))))
    (hxthreshold :
      (e : ℝ) / ((p : ℝ) - 1) <
        ((ofWithZeroValuation v).val x : ℝ)) :
    letI : Valued K (WithZero (Multiplicative ℤ)) := Valued.mk' v
    Tendsto
      (fun n : ℕ =>
        ((x ^ n /
          Units.mk0 (((n.factorial : ℕ) : K)) (hnK n) : Kˣ) : K))
      atTop (𝓝 (0 : K)) := by
  let : Valued K (WithZero (Multiplicative ℤ)) := Valued.mk' v
  rw [tendsto_iff_forall_eventually_mem]
  intro s hs
  rw [Valued.mem_nhds_zero] at hs
  rcases hs with ⟨γ, hγs⟩
  let γ' : (WithZero (Multiplicative ℤ))ˣ :=
    Units.map (MonoidWithZeroHom.ValueGroup₀.embedding
      (f := (.ofClass v))) γ
  rcases WithZero.exists_exp_neg_natCast_lt γ'.ne_zero with ⟨N, hNγ⟩
  have hterm :=
    eventually_le_ofWithZeroValuation_val_exp_term_scaled_of_threshold
      (v := v) (p := p) e x hnK hnval hxthreshold (N : ℤ)
  filter_upwards [hterm] with n hn
  apply hγs
  let y : Kˣ :=
    x ^ n /
      Units.mk0 (((n.factorial : ℕ) : K)) (hnK n)
  have hlog :
      WithZero.log (v (y : K)) ≤ -(N : ℤ) := by
    have hNlog : (N : ℤ) ≤ -WithZero.log (v (y : K)) := by
      simpa [y, ofWithZeroValuation_val] using hn
    linarith
  have hvle : v (y : K) ≤ WithZero.exp (-(N : ℤ)) :=
    WithZero.le_exp_of_log_le hlog
  change v.restrict (y : K) < γ.1
  rw [Valuation.restrict_lt_iff_lt_embedding]
  exact lt_of_le_of_lt hvle (by simpa [γ'] using hNγ)

/-- Field-element exponential-series terms tend to zero under the normalized
radius condition `v x < exp (-1)`.  This version also covers `x = 0`. -/
theorem tendsto_zero_expSeriesTermField_ofWithZeroValuation_of_lt_exp_neg_one
    (v : _root_.Valuation K (WithZero (Multiplicative ℤ)))
    {p : ℕ} [Fact p.Prime] (x : K)
    (hnK : ∀ n : ℕ, (((n.factorial : ℕ) : K) ≠ 0))
    (hnval : ∀ n : ℕ,
      v (((n.factorial : ℕ) : K)) =
        WithZero.exp (-(padicValNat p n.factorial : ℤ)))
    (hvx : v x < WithZero.exp (-1 : ℤ)) :
    letI : Valued K (WithZero (Multiplicative ℤ)) := Valued.mk' v
    Tendsto (fun n : ℕ => expSeriesTermField x hnK n) atTop
      (𝓝 (0 : K)) := by
  let : Valued K (WithZero (Multiplicative ℤ)) := Valued.mk' v
  by_cases hx : x = 0
  · have hconst :
        (fun n : ℕ => expSeriesTermField x hnK n) =ᶠ[atTop]
          fun _ : ℕ => (0 : K) := by
      filter_upwards [eventually_ge_atTop 1] with n hn
      have hnzero : n ≠ 0 := by omega
      exact expSeriesTermField_eq_zero_of_eq_zero_of_ne_zero hx hnK hnzero
    exact hconst.tendsto
  · have hxone :
        1 < ((ofWithZeroValuation v).val (Units.mk0 x hx) : ℝ) :=
      ofWithZeroValuation_val_mk0_one_lt_of_lt_exp_neg_one
        (v := v) hx hvx
    have hunit :=
      tendsto_zero_exp_term_ofWithZeroValuation_of_one_lt
        (v := v) (p := p) (Units.mk0 x hx) hnK hnval hxone
    simpa [expSeriesTermField, expSeriesTerm] using hunit

/-- In a complete nonarchimedean valuation topology, the field-element
exponential-series terms are summable under `v x < exp (-1)`. -/
theorem summable_expSeriesTermField_ofWithZeroValuation_of_lt_exp_neg_one
    (v : _root_.Valuation K (WithZero (Multiplicative ℤ)))
    {p : ℕ} [Fact p.Prime] (x : K)
    (hnK : ∀ n : ℕ, (((n.factorial : ℕ) : K) ≠ 0))
    (hnval : ∀ n : ℕ,
      v (((n.factorial : ℕ) : K)) =
        WithZero.exp (-(padicValNat p n.factorial : ℤ)))
    (hvx : v x < WithZero.exp (-1 : ℤ))
    (hcomplete :
      letI : Valued K (WithZero (Multiplicative ℤ)) := Valued.mk' v
      CompleteSpace K) :
    letI : Valued K (WithZero (Multiplicative ℤ)) := Valued.mk' v
    Summable (fun n : ℕ => expSeriesTermField x hnK n) := by
  let : Valued K (WithZero (Multiplicative ℤ)) := Valued.mk' v
  let : CompleteSpace K := hcomplete
  have : NonarchimedeanRing K := nonarchimedeanRing_ofWithZeroValuation v
  have hzero :
      Tendsto (fun n : ℕ => expSeriesTermField x hnK n) atTop
        (𝓝 (0 : K)) :=
    tendsto_zero_expSeriesTermField_ofWithZeroValuation_of_lt_exp_neg_one
      (v := v) (p := p) x hnK hnval hvx
  have hcofinite :
      Tendsto (fun n : ℕ => expSeriesTermField x hnK n) cofinite
        (𝓝 (0 : K)) := by
    simpa [Nat.cofinite_eq_atTop] using hzero
  rw [NonarchimedeanAddGroup.summable_iff_tendsto_cofinite_zero]
  exact hcofinite

/-- Field-element exponential series with value supplied by
`expSeriesFieldOfWithZeroValuation`. -/
theorem hasSum_expSeriesTermField_expSeriesField_ofWithZeroValuation_of_lt_exp_neg_one
    (v : _root_.Valuation K (WithZero (Multiplicative ℤ)))
    {p : ℕ} [Fact p.Prime] (x : K)
    (hnK : ∀ n : ℕ, (((n.factorial : ℕ) : K) ≠ 0))
    (hnval : ∀ n : ℕ,
      v (((n.factorial : ℕ) : K)) =
        WithZero.exp (-(padicValNat p n.factorial : ℤ)))
    (hvx : v x < WithZero.exp (-1 : ℤ))
    (hcomplete :
      letI : Valued K (WithZero (Multiplicative ℤ)) := Valued.mk' v
      CompleteSpace K) :
    letI : Valued K (WithZero (Multiplicative ℤ)) := Valued.mk' v
    HasSum (fun n : ℕ => expSeriesTermField x hnK n)
      (expSeriesFieldOfWithZeroValuation v x hnK) := by
  let : Valued K (WithZero (Multiplicative ℤ)) := Valued.mk' v
  have hs :
      Summable (fun n : ℕ => expSeriesTermField x hnK n) :=
    summable_expSeriesTermField_ofWithZeroValuation_of_lt_exp_neg_one
      (v := v) (p := p) x hnK hnval hvx hcomplete
  simpa [expSeriesFieldOfWithZeroValuation] using hs.hasSum

/-- Field-element exponential-series terms tend to zero under the sharp
ramified threshold.  This version also covers `x = 0`. -/
theorem tendsto_zero_expSeriesTermField_ofWithZeroValuation_scaled_of_threshold
    (v : _root_.Valuation K (WithZero (Multiplicative ℤ)))
    {p : ℕ} [Fact p.Prime] (e : ℕ) (x : K)
    (hnK : ∀ n : ℕ, (((n.factorial : ℕ) : K) ≠ 0))
    (hnval : ∀ n : ℕ,
      v (((n.factorial : ℕ) : K)) =
        WithZero.exp (-((e : ℤ) * (padicValNat p n.factorial : ℤ))))
    (hxthreshold : ∀ hx : x ≠ 0,
      (e : ℝ) / ((p : ℝ) - 1) <
        ((ofWithZeroValuation v).val (Units.mk0 x hx) : ℝ)) :
    letI : Valued K (WithZero (Multiplicative ℤ)) := Valued.mk' v
    Tendsto (fun n : ℕ => expSeriesTermField x hnK n) atTop
      (𝓝 (0 : K)) := by
  let : Valued K (WithZero (Multiplicative ℤ)) := Valued.mk' v
  by_cases hx : x = 0
  · have hconst :
        (fun n : ℕ => expSeriesTermField x hnK n) =ᶠ[atTop]
          fun _ : ℕ => (0 : K) := by
      filter_upwards [eventually_ge_atTop 1] with n hn
      have hnzero : n ≠ 0 := by omega
      exact expSeriesTermField_eq_zero_of_eq_zero_of_ne_zero hx hnK hnzero
    exact hconst.tendsto
  · have hunit :=
      tendsto_zero_exp_term_ofWithZeroValuation_scaled_of_threshold
        (v := v) (p := p) e (Units.mk0 x hx) hnK hnval (hxthreshold hx)
    simpa [expSeriesTermField, expSeriesTerm] using hunit

/-- Summability of the field-element exponential series under the sharp
ramified threshold. -/
theorem summable_expSeriesTermField_ofWithZeroValuation_scaled_of_threshold
    (v : _root_.Valuation K (WithZero (Multiplicative ℤ)))
    {p : ℕ} [Fact p.Prime] (e : ℕ) (x : K)
    (hnK : ∀ n : ℕ, (((n.factorial : ℕ) : K) ≠ 0))
    (hnval : ∀ n : ℕ,
      v (((n.factorial : ℕ) : K)) =
        WithZero.exp (-((e : ℤ) * (padicValNat p n.factorial : ℤ))))
    (hxthreshold : ∀ hx : x ≠ 0,
      (e : ℝ) / ((p : ℝ) - 1) <
        ((ofWithZeroValuation v).val (Units.mk0 x hx) : ℝ))
    (hcomplete :
      letI : Valued K (WithZero (Multiplicative ℤ)) := Valued.mk' v
      CompleteSpace K) :
    letI : Valued K (WithZero (Multiplicative ℤ)) := Valued.mk' v
    Summable (fun n : ℕ => expSeriesTermField x hnK n) := by
  let : Valued K (WithZero (Multiplicative ℤ)) := Valued.mk' v
  let : CompleteSpace K := hcomplete
  have : NonarchimedeanRing K := nonarchimedeanRing_ofWithZeroValuation v
  have hzero :
      Tendsto (fun n : ℕ => expSeriesTermField x hnK n) atTop
        (𝓝 (0 : K)) :=
    tendsto_zero_expSeriesTermField_ofWithZeroValuation_scaled_of_threshold
      (v := v) (p := p) e x hnK hnval hxthreshold
  have hcofinite :
      Tendsto (fun n : ℕ => expSeriesTermField x hnK n) cofinite
        (𝓝 (0 : K)) := by
    simpa [Nat.cofinite_eq_atTop] using hzero
  rw [NonarchimedeanAddGroup.summable_iff_tendsto_cofinite_zero]
  exact hcofinite

/-- Field-element exponential series with value supplied by
`expSeriesFieldOfWithZeroValuation`, under the sharp ramified threshold. -/
theorem hasSum_expSeriesTermField_expSeriesField_ofWithZeroValuation_scaled_of_threshold
    (v : _root_.Valuation K (WithZero (Multiplicative ℤ)))
    {p : ℕ} [Fact p.Prime] (e : ℕ) (x : K)
    (hnK : ∀ n : ℕ, (((n.factorial : ℕ) : K) ≠ 0))
    (hnval : ∀ n : ℕ,
      v (((n.factorial : ℕ) : K)) =
        WithZero.exp (-((e : ℤ) * (padicValNat p n.factorial : ℤ))))
    (hxthreshold : ∀ hx : x ≠ 0,
      (e : ℝ) / ((p : ℝ) - 1) <
        ((ofWithZeroValuation v).val (Units.mk0 x hx) : ℝ))
    (hcomplete :
      letI : Valued K (WithZero (Multiplicative ℤ)) := Valued.mk' v
      CompleteSpace K) :
    letI : Valued K (WithZero (Multiplicative ℤ)) := Valued.mk' v
    HasSum (fun n : ℕ => expSeriesTermField x hnK n)
      (expSeriesFieldOfWithZeroValuation v x hnK) := by
  let : Valued K (WithZero (Multiplicative ℤ)) := Valued.mk' v
  have hs :
      Summable (fun n : ℕ => expSeriesTermField x hnK n) :=
    summable_expSeriesTermField_ofWithZeroValuation_scaled_of_threshold
      (v := v) (p := p) e x hnK hnval hxthreshold hcomplete
  simpa [expSeriesFieldOfWithZeroValuation] using hs.hasSum

/-- Field-element exponential partial sums converge under the sharp ramified
threshold. -/
theorem tendsto_expSeriesPartialSumField_ofWithZeroValuation_scaled_of_threshold
    (v : _root_.Valuation K (WithZero (Multiplicative ℤ)))
    {p : ℕ} [Fact p.Prime] (e : ℕ) (x : K)
    (hnK : ∀ n : ℕ, (((n.factorial : ℕ) : K) ≠ 0))
    (hnval : ∀ n : ℕ,
      v (((n.factorial : ℕ) : K)) =
        WithZero.exp (-((e : ℤ) * (padicValNat p n.factorial : ℤ))))
    (hxthreshold : ∀ hx : x ≠ 0,
      (e : ℝ) / ((p : ℝ) - 1) <
        ((ofWithZeroValuation v).val (Units.mk0 x hx) : ℝ))
    (hcomplete :
      letI : Valued K (WithZero (Multiplicative ℤ)) := Valued.mk' v
      CompleteSpace K) :
    letI : Valued K (WithZero (Multiplicative ℤ)) := Valued.mk' v
    Tendsto (fun N : ℕ => expSeriesPartialSumField x hnK N) atTop
      (𝓝 (expSeriesFieldOfWithZeroValuation v x hnK)) := by
  let : Valued K (WithZero (Multiplicative ℤ)) := Valued.mk' v
  have hsum :=
    hasSum_expSeriesTermField_expSeriesField_ofWithZeroValuation_scaled_of_threshold
      (v := v) (p := p) e x hnK hnval hxthreshold hcomplete
  simpa [expSeriesPartialSumField] using hsum.tendsto_sum_nat

/-- The antidiagonal Cauchy product of two local exponential series sums to
the product of their values. -/
theorem hasSum_expSeriesTermField_cauchyProduct_expSeriesField_mul_ofWithZeroValuation_of_lt_exp_neg_one
    (v : _root_.Valuation K (WithZero (Multiplicative ℤ)))
    {p : ℕ} [Fact p.Prime] (x y : K)
    (hnK : ∀ n : ℕ, (((n.factorial : ℕ) : K) ≠ 0))
    (hnval : ∀ n : ℕ,
      v (((n.factorial : ℕ) : K)) =
        WithZero.exp (-(padicValNat p n.factorial : ℤ)))
    (hvx : v x < WithZero.exp (-1 : ℤ))
    (hvy : v y < WithZero.exp (-1 : ℤ))
    (hcomplete :
      letI : Valued K (WithZero (Multiplicative ℤ)) := Valued.mk' v
      CompleteSpace K) :
    letI : Valued K (WithZero (Multiplicative ℤ)) := Valued.mk' v
    HasSum
      (fun n : ℕ =>
        ∑ ij ∈ Finset.HasAntidiagonal.antidiagonal n,
          expSeriesTermField x hnK ij.1 *
            expSeriesTermField y hnK ij.2)
      (expSeriesFieldOfWithZeroValuation v x hnK *
        expSeriesFieldOfWithZeroValuation v y hnK) := by
  let : Valued K (WithZero (Multiplicative ℤ)) := Valued.mk' v
  have : NonarchimedeanRing K := nonarchimedeanRing_ofWithZeroValuation v
  have hxsum :
      Summable (fun n : ℕ => expSeriesTermField x hnK n) :=
    summable_expSeriesTermField_ofWithZeroValuation_of_lt_exp_neg_one
      (v := v) (p := p) x hnK hnval hvx hcomplete
  have hysum :
      Summable (fun n : ℕ => expSeriesTermField y hnK n) :=
    summable_expSeriesTermField_ofWithZeroValuation_of_lt_exp_neg_one
      (v := v) (p := p) y hnK hnval hvy hcomplete
  have hprod :
      Summable
        (fun ij : ℕ × ℕ =>
          expSeriesTermField x hnK ij.1 *
            expSeriesTermField y hnK ij.2) :=
    hxsum.mul_of_nonarchimedean hysum
  have hcauchy :
      Summable
        (fun n : ℕ =>
          ∑ ij ∈ Finset.HasAntidiagonal.antidiagonal n,
            expSeriesTermField x hnK ij.1 *
              expSeriesTermField y hnK ij.2) :=
    summable_sum_mul_antidiagonal_of_summable_mul hprod
  have htsum :
      expSeriesFieldOfWithZeroValuation v x hnK *
          expSeriesFieldOfWithZeroValuation v y hnK =
        ∑' n : ℕ,
          ∑ ij ∈ Finset.HasAntidiagonal.antidiagonal n,
            expSeriesTermField x hnK ij.1 *
              expSeriesTermField y hnK ij.2 := by
    simpa [expSeriesFieldOfWithZeroValuation] using
      hxsum.tsum_mul_tsum_eq_tsum_sum_antidiagonal hysum hprod
  exact htsum.symm ▸ hcauchy.hasSum

/-- Local exponential multiplicativity on the normalized convergence ball. -/
theorem expSeriesField_add_eq_mul_ofWithZeroValuation_of_lt_exp_neg_one
    [Algebra ℚ K]
    (v : _root_.Valuation K (WithZero (Multiplicative ℤ)))
    {p : ℕ} [Fact p.Prime] (x y : K)
    (hnK : ∀ n : ℕ, (((n.factorial : ℕ) : K) ≠ 0))
    (hnval : ∀ n : ℕ,
      v (((n.factorial : ℕ) : K)) =
        WithZero.exp (-(padicValNat p n.factorial : ℤ)))
    (hvx : v x < WithZero.exp (-1 : ℤ))
    (hvy : v y < WithZero.exp (-1 : ℤ))
    (hcomplete :
      letI : Valued K (WithZero (Multiplicative ℤ)) := Valued.mk' v
      CompleteSpace K) :
    expSeriesFieldOfWithZeroValuation v (x + y) hnK =
      expSeriesFieldOfWithZeroValuation v x hnK *
        expSeriesFieldOfWithZeroValuation v y hnK := by
  let : Valued K (WithZero (Multiplicative ℤ)) := Valued.mk' v
  have hxy :
      v (x + y) < WithZero.exp (-1 : ℤ) :=
    valuation_add_lt_exp_neg_one_of_lt_exp_neg_one v hvx hvy
  have hsumAdd :=
    hasSum_expSeriesTermField_expSeriesField_ofWithZeroValuation_of_lt_exp_neg_one
      (v := v) (p := p) (x + y) hnK hnval hxy hcomplete
  have hsumCauchyAdd :
      HasSum
        (fun n : ℕ =>
          ∑ ij ∈ Finset.HasAntidiagonal.antidiagonal n,
            expSeriesTermField x hnK ij.1 *
              expSeriesTermField y hnK ij.2)
        (expSeriesFieldOfWithZeroValuation v (x + y) hnK) :=
    hsumAdd.congr_fun fun n =>
      (expSeriesTermField_add_eq_sum_antidiagonal
        (K := K) x y hnK n).symm
  have hsumProduct :=
    hasSum_expSeriesTermField_cauchyProduct_expSeriesField_mul_ofWithZeroValuation_of_lt_exp_neg_one
      (v := v) (p := p) x y hnK hnval hvx hvy hcomplete
  exact hsumCauchyAdd.unique hsumProduct

/-- The antidiagonal Cauchy product of two local exponential series sums to
the product of their values under the sharp ramified threshold. -/
theorem hasSum_expSeriesTermField_cauchyProduct_expSeriesField_mul_ofWithZeroValuation_scaled_of_threshold
    (v : _root_.Valuation K (WithZero (Multiplicative ℤ)))
    {p : ℕ} [Fact p.Prime] (e : ℕ) (x y : K)
    (hnK : ∀ n : ℕ, (((n.factorial : ℕ) : K) ≠ 0))
    (hnval : ∀ n : ℕ,
      v (((n.factorial : ℕ) : K)) =
        WithZero.exp (-((e : ℤ) * (padicValNat p n.factorial : ℤ))))
    (hxthreshold : ∀ hx : x ≠ 0,
      (e : ℝ) / ((p : ℝ) - 1) <
        ((ofWithZeroValuation v).val (Units.mk0 x hx) : ℝ))
    (hythreshold : ∀ hy : y ≠ 0,
      (e : ℝ) / ((p : ℝ) - 1) <
        ((ofWithZeroValuation v).val (Units.mk0 y hy) : ℝ))
    (hcomplete :
      letI : Valued K (WithZero (Multiplicative ℤ)) := Valued.mk' v
      CompleteSpace K) :
    letI : Valued K (WithZero (Multiplicative ℤ)) := Valued.mk' v
    HasSum
      (fun n : ℕ =>
        ∑ ij ∈ Finset.HasAntidiagonal.antidiagonal n,
          expSeriesTermField x hnK ij.1 *
            expSeriesTermField y hnK ij.2)
      (expSeriesFieldOfWithZeroValuation v x hnK *
        expSeriesFieldOfWithZeroValuation v y hnK) := by
  let : Valued K (WithZero (Multiplicative ℤ)) := Valued.mk' v
  have : NonarchimedeanRing K := nonarchimedeanRing_ofWithZeroValuation v
  have hxsum :
      Summable (fun n : ℕ => expSeriesTermField x hnK n) :=
    summable_expSeriesTermField_ofWithZeroValuation_scaled_of_threshold
      (v := v) (p := p) e x hnK hnval hxthreshold hcomplete
  have hysum :
      Summable (fun n : ℕ => expSeriesTermField y hnK n) :=
    summable_expSeriesTermField_ofWithZeroValuation_scaled_of_threshold
      (v := v) (p := p) e y hnK hnval hythreshold hcomplete
  have hprod :
      Summable
        (fun ij : ℕ × ℕ =>
          expSeriesTermField x hnK ij.1 *
            expSeriesTermField y hnK ij.2) :=
    hxsum.mul_of_nonarchimedean hysum
  have hcauchy :
      Summable
        (fun n : ℕ =>
          ∑ ij ∈ Finset.HasAntidiagonal.antidiagonal n,
            expSeriesTermField x hnK ij.1 *
              expSeriesTermField y hnK ij.2) :=
    summable_sum_mul_antidiagonal_of_summable_mul hprod
  have htsum :
      expSeriesFieldOfWithZeroValuation v x hnK *
          expSeriesFieldOfWithZeroValuation v y hnK =
        ∑' n : ℕ,
          ∑ ij ∈ Finset.HasAntidiagonal.antidiagonal n,
            expSeriesTermField x hnK ij.1 *
              expSeriesTermField y hnK ij.2 := by
    simpa [expSeriesFieldOfWithZeroValuation] using
      hxsum.tsum_mul_tsum_eq_tsum_sum_antidiagonal hysum hprod
  exact htsum.symm ▸ hcauchy.hasSum

/-- Local exponential multiplicativity under the sharp ramified threshold. -/
theorem expSeriesField_add_eq_mul_ofWithZeroValuation_scaled_of_threshold
    [Algebra ℚ K]
    (v : _root_.Valuation K (WithZero (Multiplicative ℤ)))
    {p : ℕ} [Fact p.Prime] (e : ℕ) (x y : K)
    (hnK : ∀ n : ℕ, (((n.factorial : ℕ) : K) ≠ 0))
    (hnval : ∀ n : ℕ,
      v (((n.factorial : ℕ) : K)) =
        WithZero.exp (-((e : ℤ) * (padicValNat p n.factorial : ℤ))))
    (hxthreshold : ∀ hx : x ≠ 0,
      (e : ℝ) / ((p : ℝ) - 1) <
        ((ofWithZeroValuation v).val (Units.mk0 x hx) : ℝ))
    (hythreshold : ∀ hy : y ≠ 0,
      (e : ℝ) / ((p : ℝ) - 1) <
        ((ofWithZeroValuation v).val (Units.mk0 y hy) : ℝ))
    (hcomplete :
      letI : Valued K (WithZero (Multiplicative ℤ)) := Valued.mk' v
      CompleteSpace K) :
    expSeriesFieldOfWithZeroValuation v (x + y) hnK =
      expSeriesFieldOfWithZeroValuation v x hnK *
        expSeriesFieldOfWithZeroValuation v y hnK := by
  let : Valued K (WithZero (Multiplicative ℤ)) := Valued.mk' v
  have hxythreshold : ∀ hxy : x + y ≠ 0,
      (e : ℝ) / ((p : ℝ) - 1) <
        ((ofWithZeroValuation v).val (Units.mk0 (x + y) hxy) : ℝ) := by
    intro hxy
    by_cases hx : x = 0
    · have hy : y ≠ 0 := by
        intro hy
        exact hxy (by simp [hx, hy])
      simpa [hx] using hythreshold hy
    · by_cases hy : y = 0
      · simpa [hy] using hxthreshold hx
      · have hmin :
            min ((ofWithZeroValuation v).val (Units.mk0 x hx))
                ((ofWithZeroValuation v).val (Units.mk0 y hy)) ≤
              (ofWithZeroValuation v).val (Units.mk0 (x + y) hxy) :=
          ofWithZeroValuation_val_add_ge_min v hx hy hxy
        have hminR :
            ((min ((ofWithZeroValuation v).val (Units.mk0 x hx))
                ((ofWithZeroValuation v).val (Units.mk0 y hy)) : ℤ) : ℝ) ≤
              ((ofWithZeroValuation v).val (Units.mk0 (x + y) hxy) : ℝ) := by
          exact_mod_cast hmin
        have hthresholdMin :
            (e : ℝ) / ((p : ℝ) - 1) <
              ((min ((ofWithZeroValuation v).val (Units.mk0 x hx))
                  ((ofWithZeroValuation v).val (Units.mk0 y hy)) : ℤ) : ℝ) := by
          rw [Int.cast_min]
          exact lt_min (hxthreshold hx) (hythreshold hy)
        exact lt_of_lt_of_le hthresholdMin hminR
  have hsumAdd :=
    hasSum_expSeriesTermField_expSeriesField_ofWithZeroValuation_scaled_of_threshold
      (v := v) (p := p) e (x + y) hnK hnval hxythreshold hcomplete
  have hsumCauchyAdd :
      HasSum
        (fun n : ℕ =>
          ∑ ij ∈ Finset.HasAntidiagonal.antidiagonal n,
            expSeriesTermField x hnK ij.1 *
              expSeriesTermField y hnK ij.2)
        (expSeriesFieldOfWithZeroValuation v (x + y) hnK) :=
    hsumAdd.congr_fun fun n =>
      (expSeriesTermField_add_eq_sum_antidiagonal
        (K := K) x y hnK n).symm
  have hsumProduct :=
    hasSum_expSeriesTermField_cauchyProduct_expSeriesField_mul_ofWithZeroValuation_scaled_of_threshold
      (v := v) (p := p) e x y hnK hnval hxthreshold hythreshold
      hcomplete
  exact hsumCauchyAdd.unique hsumProduct

/-- Field-element exponential partial sums converge to the exponential-series
value under `v x < exp (-1)`. -/
theorem tendsto_expSeriesPartialSumField_ofWithZeroValuation_of_lt_exp_neg_one
    (v : _root_.Valuation K (WithZero (Multiplicative ℤ)))
    {p : ℕ} [Fact p.Prime] (x : K)
    (hnK : ∀ n : ℕ, (((n.factorial : ℕ) : K) ≠ 0))
    (hnval : ∀ n : ℕ,
      v (((n.factorial : ℕ) : K)) =
        WithZero.exp (-(padicValNat p n.factorial : ℤ)))
    (hvx : v x < WithZero.exp (-1 : ℤ))
    (hcomplete :
      letI : Valued K (WithZero (Multiplicative ℤ)) := Valued.mk' v
      CompleteSpace K) :
    letI : Valued K (WithZero (Multiplicative ℤ)) := Valued.mk' v
    Tendsto (fun N : ℕ => expSeriesPartialSumField x hnK N) atTop
      (𝓝 (expSeriesFieldOfWithZeroValuation v x hnK)) := by
  let : Valued K (WithZero (Multiplicative ℤ)) := Valued.mk' v
  have hsum :=
    hasSum_expSeriesTermField_expSeriesField_ofWithZeroValuation_of_lt_exp_neg_one
      (v := v) (p := p) x hnK hnval hvx hcomplete
  simpa [expSeriesPartialSumField] using hsum.tendsto_sum_nat

/-- Every positive-degree exponential-series term lies in the open unit ball
on the normalized exponential convergence radius. -/
theorem valuation_expSeriesTermField_lt_one_of_lt_exp_neg_one
    (v : _root_.Valuation K (WithZero (Multiplicative ℤ)))
    {p : ℕ} [Fact p.Prime] (x : K)
    (hnK : ∀ n : ℕ, (((n.factorial : ℕ) : K) ≠ 0))
    (hnval : ∀ n : ℕ,
      v (((n.factorial : ℕ) : K)) =
        WithZero.exp (-(padicValNat p n.factorial : ℤ)))
    (hvx : v x < WithZero.exp (-1 : ℤ))
    {n : ℕ} (hn : n ≠ 0) :
    v (expSeriesTermField x hnK n) <
      (1 : WithZero (Multiplicative ℤ)) := by
  by_cases hx : x = 0
  · have hterm :
        expSeriesTermField x hnK n = 0 :=
      expSeriesTermField_eq_zero_of_eq_zero_of_ne_zero hx hnK hn
    simp [hterm]
  · let y : Kˣ :=
      (Units.mk0 x hx) ^ n /
        Units.mk0 (((n.factorial : ℕ) : K)) (hnK n)
    have hxoneReal :
        1 < ((ofWithZeroValuation v).val (Units.mk0 x hx) : ℝ) :=
      ofWithZeroValuation_val_mk0_one_lt_of_lt_exp_neg_one
        (v := v) hx hvx
    have hxone : 1 < (ofWithZeroValuation v).val (Units.mk0 x hx) := by
      exact_mod_cast hxoneReal
    have hpos :
        0 < (ofWithZeroValuation v).val y :=
      ofWithZeroValuation_val_pow_div_natCast_factorial_pos_of_one_lt
        (v := v) (p := p) (n := n) (Units.mk0 x hx)
        (hnK n) (hnval n) hxone hn
    have hlt :
        v (y : K) < (1 : WithZero (Multiplicative ℤ)) :=
      valuation_lt_one_of_ofWithZeroValuation_val_pos v y hpos
    simpa [y, expSeriesTermField, expSeriesTerm] using hlt

/-- Every finite positive-degree tail of the exponential series lies in the
open unit ball on the normalized exponential convergence radius. -/
theorem valuation_expSeriesTailPartialSumField_lt_one_of_lt_exp_neg_one
    (v : _root_.Valuation K (WithZero (Multiplicative ℤ)))
    {p : ℕ} [Fact p.Prime] (x : K)
    (hnK : ∀ n : ℕ, (((n.factorial : ℕ) : K) ≠ 0))
    (hnval : ∀ n : ℕ,
      v (((n.factorial : ℕ) : K)) =
        WithZero.exp (-(padicValNat p n.factorial : ℤ)))
    (hvx : v x < WithZero.exp (-1 : ℤ)) (N : ℕ) :
    v (∑ n ∈ Finset.range N, expSeriesTermField x hnK (n + 1)) <
      (1 : WithZero (Multiplicative ℤ)) := by
  exact
    v.map_sum_lt' (show (0 : WithZero (Multiplicative ℤ)) < 1 from zero_lt_one)
      (fun n _hn =>
        valuation_expSeriesTermField_lt_one_of_lt_exp_neg_one
          (v := v) (p := p) x hnK hnval hvx (Nat.succ_ne_zero n))

end MultiplicativeIntegerValuation
end LocalFieldTheory.DiscreteValuationField

end
end

section
-- module Solutions.OAIQ244_DUKE.LocalField_Analytic_LogExpSeries_LogConvergence
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.LubinTate.compatibleGroupFamiliesGroup _root_.OAI.PrimeDegreePackets.instNonemptyLeafTestSpace _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.RayClass.approximationCompletionTopologicalSpace _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.LocalClassFieldTheory.normalizationIntegerRingIsIntegralClosure _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen
attribute [-simp] _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.IsDiscreteValuationRing.addVal_ringEquiv _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.LocalFieldTheory.IsNonarchimedeanLocalField.multiplicativeIntegerValuation_val _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.LocalFieldTheory.residueField_algebraMap_residue _root_.OAI.PrimeDegreePackets.ThetaConstruction.schwartzCM_apply _root_.infinitePlace_mult_smul
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false
/-!
Establishes convergence and summability of the logarithm series on the nonarchimedean open unit
ball.
-/

open Filter
open Polynomial
open scoped Topology
open scoped PowerSeries.WithPiTopology
noncomputable section

attribute [local instance] Classical.propDecidable

universe u

open ValuationTheory.DiscreteValuationField
open LocalFieldTheory.DiscreteValuationField

namespace LocalFieldTheory.DiscreteValuationField
namespace MultiplicativeIntegerValuation

variable {K : Type u} [Field K]

/-- Signed field-element logarithm-series terms tend to zero when `v x < 1`. -/
theorem tendsto_zero_signedLogSeriesTermField_ofWithZeroValuation_of_lt_one
    (v : _root_.Valuation K (WithZero (Multiplicative ℤ)))
    {p : ℕ} [Fact p.Prime] (x : K)
    (hnK : ∀ n : ℕ, (((n + 1 : ℕ) : K) ≠ 0))
    (hnval : ∀ n : ℕ,
      v (((n + 1 : ℕ) : K)) =
        WithZero.exp (-(padicValNat p (n + 1) : ℤ)))
    (hvx : v x < (1 : WithZero (Multiplicative ℤ))) :
    letI : Valued K (WithZero (Multiplicative ℤ)) := Valued.mk' v
    Tendsto (fun n : ℕ => signedLogSeriesTermField x hnK n) atTop
      (𝓝 (0 : K)) := by
  let : Valued K (WithZero (Multiplicative ℤ)) := Valued.mk' v
  by_cases hx : x = 0
  · have hconst :
        (fun n : ℕ => signedLogSeriesTermField x hnK n) =
          fun _ : ℕ => (0 : K) := by
      funext n
      exact signedLogSeriesTermField_eq_zero_of_eq_zero hx hnK n
    simp [hconst]
  · have hxpos :
        0 < (ofWithZeroValuation v).val (Units.mk0 x hx) :=
      ofWithZeroValuation_val_mk0_pos_of_lt_one (v := v) hx hvx
    have hunit :=
      tendsto_zero_signed_log_term_ofWithZeroValuation_of_pos
        (v := v) (p := p) (Units.mk0 x hx) hnK hnval hxpos
    simpa [signedLogSeriesTermField, logSeriesTermField] using hunit

/-- Summability of the signed field-element logarithm series under the
principal-unit condition `v x < 1`. -/
theorem summable_signedLogSeriesTermField_ofWithZeroValuation_of_lt_one
    (v : _root_.Valuation K (WithZero (Multiplicative ℤ)))
    {p : ℕ} [Fact p.Prime] (x : K)
    (hnK : ∀ n : ℕ, (((n + 1 : ℕ) : K) ≠ 0))
    (hnval : ∀ n : ℕ,
      v (((n + 1 : ℕ) : K)) =
        WithZero.exp (-(padicValNat p (n + 1) : ℤ)))
    (hvx : v x < (1 : WithZero (Multiplicative ℤ)))
    (hcomplete :
      letI : Valued K (WithZero (Multiplicative ℤ)) := Valued.mk' v
      CompleteSpace K) :
    letI : Valued K (WithZero (Multiplicative ℤ)) := Valued.mk' v
    Summable (fun n : ℕ => signedLogSeriesTermField x hnK n) := by
  let : Valued K (WithZero (Multiplicative ℤ)) := Valued.mk' v
  let : CompleteSpace K := hcomplete
  have : NonarchimedeanRing K := nonarchimedeanRing_ofWithZeroValuation v
  have hzero :
      Tendsto (fun n : ℕ => signedLogSeriesTermField x hnK n) atTop
        (𝓝 (0 : K)) :=
    tendsto_zero_signedLogSeriesTermField_ofWithZeroValuation_of_lt_one
      (v := v) (p := p) x hnK hnval hvx
  have hcofinite :
      Tendsto (fun n : ℕ => signedLogSeriesTermField x hnK n) cofinite
        (𝓝 (0 : K)) := by
    simpa [Nat.cofinite_eq_atTop] using hzero
  rw [NonarchimedeanAddGroup.summable_iff_tendsto_cofinite_zero]
  exact hcofinite

/-- Field-element principal-unit logarithm series: the signed series has the
value supplied by `logOnePlusSeriesFieldOfWithZeroValuation`. -/
theorem hasSum_signedLogSeriesTermField_logOnePlusSeriesField_ofWithZeroValuation_of_lt_one
    (v : _root_.Valuation K (WithZero (Multiplicative ℤ)))
    {p : ℕ} [Fact p.Prime] (x : K)
    (hnK : ∀ n : ℕ, (((n + 1 : ℕ) : K) ≠ 0))
    (hnval : ∀ n : ℕ,
      v (((n + 1 : ℕ) : K)) =
        WithZero.exp (-(padicValNat p (n + 1) : ℤ)))
    (hvx : v x < (1 : WithZero (Multiplicative ℤ)))
    (hcomplete :
      letI : Valued K (WithZero (Multiplicative ℤ)) := Valued.mk' v
      CompleteSpace K) :
    letI : Valued K (WithZero (Multiplicative ℤ)) := Valued.mk' v
    HasSum (fun n : ℕ => signedLogSeriesTermField x hnK n)
      (logOnePlusSeriesFieldOfWithZeroValuation v x hnK) := by
  let : Valued K (WithZero (Multiplicative ℤ)) := Valued.mk' v
  have hs :
      Summable (fun n : ℕ => signedLogSeriesTermField x hnK n) :=
    summable_signedLogSeriesTermField_ofWithZeroValuation_of_lt_one
      (v := v) (p := p) x hnK hnval hvx hcomplete
  simpa [logOnePlusSeriesFieldOfWithZeroValuation] using hs.hasSum

/-- The field-element finite logarithm polynomials converge to the
principal-unit logarithm-series value. -/
theorem tendsto_logOnePlusPartialSumField_ofWithZeroValuation_of_lt_one
    (v : _root_.Valuation K (WithZero (Multiplicative ℤ)))
    {p : ℕ} [Fact p.Prime] (x : K)
    (hnK : ∀ n : ℕ, (((n + 1 : ℕ) : K) ≠ 0))
    (hnval : ∀ n : ℕ,
      v (((n + 1 : ℕ) : K)) =
        WithZero.exp (-(padicValNat p (n + 1) : ℤ)))
    (hvx : v x < (1 : WithZero (Multiplicative ℤ)))
    (hcomplete :
      letI : Valued K (WithZero (Multiplicative ℤ)) := Valued.mk' v
      CompleteSpace K) :
    letI : Valued K (WithZero (Multiplicative ℤ)) := Valued.mk' v
    Tendsto (fun N : ℕ => logOnePlusPartialSumField x hnK N) atTop
      (𝓝 (logOnePlusSeriesFieldOfWithZeroValuation v x hnK)) := by
  let : Valued K (WithZero (Multiplicative ℤ)) := Valued.mk' v
  have hsum :=
    hasSum_signedLogSeriesTermField_logOnePlusSeriesField_ofWithZeroValuation_of_lt_one
      (v := v) (p := p) x hnK hnval hvx hcomplete
  simpa [logOnePlusPartialSumField] using hsum.tendsto_sum_nat

/-- Signed field-element logarithm-series terms tend to zero under a
ramified denominator valuation hypothesis. -/
theorem tendsto_zero_signedLogSeriesTermField_ofWithZeroValuation_scaled_of_lt_one
    (v : _root_.Valuation K (WithZero (Multiplicative ℤ)))
    {p : ℕ} [Fact p.Prime] (e : ℕ) (x : K)
    (hnK : ∀ n : ℕ, (((n + 1 : ℕ) : K) ≠ 0))
    (hnval : ∀ n : ℕ,
      v (((n + 1 : ℕ) : K)) =
        WithZero.exp (-((e : ℤ) * (padicValNat p (n + 1) : ℤ))))
    (hvx : v x < (1 : WithZero (Multiplicative ℤ))) :
    letI : Valued K (WithZero (Multiplicative ℤ)) := Valued.mk' v
    Tendsto (fun n : ℕ => signedLogSeriesTermField x hnK n) atTop
      (𝓝 (0 : K)) := by
  let : Valued K (WithZero (Multiplicative ℤ)) := Valued.mk' v
  by_cases hx : x = 0
  · have hconst :
        (fun n : ℕ => signedLogSeriesTermField x hnK n) =
          fun _ : ℕ => (0 : K) := by
      funext n
      exact signedLogSeriesTermField_eq_zero_of_eq_zero hx hnK n
    simp [hconst]
  · have hxpos :
        0 < (ofWithZeroValuation v).val (Units.mk0 x hx) :=
      ofWithZeroValuation_val_mk0_pos_of_lt_one (v := v) hx hvx
    have hunit :=
      tendsto_zero_signed_log_term_ofWithZeroValuation_scaled_of_pos
        (v := v) (p := p) e (Units.mk0 x hx) hnK hnval hxpos
    simpa [signedLogSeriesTermField, logSeriesTermField] using hunit

/-- Summability of the signed field-element logarithm series under a
ramified denominator valuation hypothesis. -/
theorem summable_signedLogSeriesTermField_ofWithZeroValuation_scaled_of_lt_one
    (v : _root_.Valuation K (WithZero (Multiplicative ℤ)))
    {p : ℕ} [Fact p.Prime] (e : ℕ) (x : K)
    (hnK : ∀ n : ℕ, (((n + 1 : ℕ) : K) ≠ 0))
    (hnval : ∀ n : ℕ,
      v (((n + 1 : ℕ) : K)) =
        WithZero.exp (-((e : ℤ) * (padicValNat p (n + 1) : ℤ))))
    (hvx : v x < (1 : WithZero (Multiplicative ℤ)))
    (hcomplete :
      letI : Valued K (WithZero (Multiplicative ℤ)) := Valued.mk' v
      CompleteSpace K) :
    letI : Valued K (WithZero (Multiplicative ℤ)) := Valued.mk' v
    Summable (fun n : ℕ => signedLogSeriesTermField x hnK n) := by
  let : Valued K (WithZero (Multiplicative ℤ)) := Valued.mk' v
  let : CompleteSpace K := hcomplete
  have : NonarchimedeanRing K := nonarchimedeanRing_ofWithZeroValuation v
  have hzero :
      Tendsto (fun n : ℕ => signedLogSeriesTermField x hnK n) atTop
        (𝓝 (0 : K)) :=
    tendsto_zero_signedLogSeriesTermField_ofWithZeroValuation_scaled_of_lt_one
      (v := v) (p := p) e x hnK hnval hvx
  have hcofinite :
      Tendsto (fun n : ℕ => signedLogSeriesTermField x hnK n) cofinite
        (𝓝 (0 : K)) := by
    simpa [Nat.cofinite_eq_atTop] using hzero
  rw [NonarchimedeanAddGroup.summable_iff_tendsto_cofinite_zero]
  exact hcofinite

/-- Field-element logarithm series has the same `tsum` value under a
ramified denominator valuation hypothesis. -/
theorem hasSum_signedLogSeriesTermField_logOnePlusSeriesField_ofWithZeroValuation_scaled_of_lt_one
    (v : _root_.Valuation K (WithZero (Multiplicative ℤ)))
    {p : ℕ} [Fact p.Prime] (e : ℕ) (x : K)
    (hnK : ∀ n : ℕ, (((n + 1 : ℕ) : K) ≠ 0))
    (hnval : ∀ n : ℕ,
      v (((n + 1 : ℕ) : K)) =
        WithZero.exp (-((e : ℤ) * (padicValNat p (n + 1) : ℤ))))
    (hvx : v x < (1 : WithZero (Multiplicative ℤ)))
    (hcomplete :
      letI : Valued K (WithZero (Multiplicative ℤ)) := Valued.mk' v
      CompleteSpace K) :
    letI : Valued K (WithZero (Multiplicative ℤ)) := Valued.mk' v
    HasSum (fun n : ℕ => signedLogSeriesTermField x hnK n)
      (logOnePlusSeriesFieldOfWithZeroValuation v x hnK) := by
  let : Valued K (WithZero (Multiplicative ℤ)) := Valued.mk' v
  have hs :
      Summable (fun n : ℕ => signedLogSeriesTermField x hnK n) :=
    summable_signedLogSeriesTermField_ofWithZeroValuation_scaled_of_lt_one
      (v := v) (p := p) e x hnK hnval hvx hcomplete
  simpa [logOnePlusSeriesFieldOfWithZeroValuation] using hs.hasSum

/-- Field-element finite logarithm polynomials converge to the logarithm
series under a ramified denominator valuation hypothesis. -/
theorem tendsto_logOnePlusPartialSumField_ofWithZeroValuation_scaled_of_lt_one
    (v : _root_.Valuation K (WithZero (Multiplicative ℤ)))
    {p : ℕ} [Fact p.Prime] (e : ℕ) (x : K)
    (hnK : ∀ n : ℕ, (((n + 1 : ℕ) : K) ≠ 0))
    (hnval : ∀ n : ℕ,
      v (((n + 1 : ℕ) : K)) =
        WithZero.exp (-((e : ℤ) * (padicValNat p (n + 1) : ℤ))))
    (hvx : v x < (1 : WithZero (Multiplicative ℤ)))
    (hcomplete :
      letI : Valued K (WithZero (Multiplicative ℤ)) := Valued.mk' v
      CompleteSpace K) :
    letI : Valued K (WithZero (Multiplicative ℤ)) := Valued.mk' v
    Tendsto (fun N : ℕ => logOnePlusPartialSumField x hnK N) atTop
      (𝓝 (logOnePlusSeriesFieldOfWithZeroValuation v x hnK)) := by
  let : Valued K (WithZero (Multiplicative ℤ)) := Valued.mk' v
  have hsum :=
    hasSum_signedLogSeriesTermField_logOnePlusSeriesField_ofWithZeroValuation_scaled_of_lt_one
      (v := v) (p := p) e x hnK hnval hvx hcomplete
  simpa [logOnePlusPartialSumField] using hsum.tendsto_sum_nat

/-- Above the ramified threshold `e/(p-1)`, each higher logarithm term has
strictly smaller `ℤᵐ⁰`-value than the linear term. -/
theorem valuation_logSeriesTermField_lt_self_of_scaled_inv_sub_one_lt
    (v : _root_.Valuation K (WithZero (Multiplicative ℤ)))
    {p : ℕ} [Fact p.Prime] (e : ℕ) {x : K} (hx : x ≠ 0)
    (hnK : ∀ n : ℕ, (((n + 1 : ℕ) : K) ≠ 0))
    (hnval : ∀ n : ℕ,
      v (((n + 1 : ℕ) : K)) =
        WithZero.exp (-((e : ℤ) * (padicValNat p (n + 1) : ℤ))))
    (hthreshold :
      (e : ℚ) / ((p : ℚ) - 1) <
        ((ofWithZeroValuation v).val (Units.mk0 x hx) : ℚ))
    {n : ℕ} (hn : n ≠ 0) :
    v (logSeriesTermField x hnK n) < v x := by
  let xu : Kˣ := Units.mk0 x hx
  let denom : Kˣ :=
    Units.mk0 (((n + 1 : ℕ) : K)) (hnK n)
  have hval :
      (ofWithZeroValuation v).val xu <
        (ofWithZeroValuation v).val (xu ^ (n + 1) / denom) := by
    change
      (ofWithZeroValuation v).val xu <
        (ofWithZeroValuation v).val
          (xu ^ (n + 1) /
            Units.mk0 (((n + 1 : ℕ) : K)) (hnK n))
    rw [ofWithZeroValuation_val_pow_div_natCast_scaled
      (v := v) (p := p) (e := e) (n := n + 1) xu (hnK n) (hnval n)]
    exact
      log_higher_term_integer_valuation_gt_scaled
        (p := p) (e := e) (n := n + 1) (by omega) hthreshold
  have hlt :=
    valuation_lt_of_ofWithZeroValuation_val_lt
      (v := v) (x := xu) (y := xu ^ (n + 1) / denom) hval
  simpa [xu, denom, logSeriesTermField] using hlt

/-- The signed higher logarithm terms have the same ramified valuation
estimate as the unsigned terms. -/
theorem valuation_signedLogSeriesTermField_lt_self_of_scaled_inv_sub_one_lt
    (v : _root_.Valuation K (WithZero (Multiplicative ℤ)))
    {p : ℕ} [Fact p.Prime] (e : ℕ) {x : K} (hx : x ≠ 0)
    (hnK : ∀ n : ℕ, (((n + 1 : ℕ) : K) ≠ 0))
    (hnval : ∀ n : ℕ,
      v (((n + 1 : ℕ) : K)) =
        WithZero.exp (-((e : ℤ) * (padicValNat p (n + 1) : ℤ))))
    (hthreshold :
      (e : ℚ) / ((p : ℚ) - 1) <
        ((ofWithZeroValuation v).val (Units.mk0 x hx) : ℚ))
    {n : ℕ} (hn : n ≠ 0) :
    v (signedLogSeriesTermField x hnK n) < v x := by
  have hlog :
      v (logSeriesTermField x hnK n) < v x :=
    valuation_logSeriesTermField_lt_self_of_scaled_inv_sub_one_lt
      (v := v) (p := p) e (x := x) hx hnK hnval hthreshold hn
  have hval :
      v (signedLogSeriesTermField x hnK n) =
        v (logSeriesTermField x hnK n) := by
    rw [signedLogSeriesTermField, v.map_mul]
    simp
  rw [hval]
  exact hlog

/-- Every finite higher-degree logarithm tail has valuation strictly smaller
than the linear term above the ramified `e/(p-1)` threshold. -/
theorem valuation_logHigherTailPartialSumField_lt_self_of_scaled_inv_sub_one_lt
    (v : _root_.Valuation K (WithZero (Multiplicative ℤ)))
    {p : ℕ} [Fact p.Prime] (e : ℕ) {x : K} (hx : x ≠ 0)
    (hnK : ∀ n : ℕ, (((n + 1 : ℕ) : K) ≠ 0))
    (hnval : ∀ n : ℕ,
      v (((n + 1 : ℕ) : K)) =
        WithZero.exp (-((e : ℤ) * (padicValNat p (n + 1) : ℤ))))
    (hthreshold :
      (e : ℚ) / ((p : ℚ) - 1) <
        ((ofWithZeroValuation v).val (Units.mk0 x hx) : ℚ))
    (N : ℕ) :
    v (∑ n ∈ Finset.range N, signedLogSeriesTermField x hnK (n + 1)) <
      v x := by
  exact
    v.map_sum_lt ((_root_.Valuation.ne_zero_iff v).2 hx)
      (fun n _hn =>
        valuation_signedLogSeriesTermField_lt_self_of_scaled_inv_sub_one_lt
          (v := v) (p := p) e (x := x) hx hnK hnval hthreshold
          (Nat.succ_ne_zero n))

/-- The higher-degree logarithm tail partial sums converge to
`log(1+x) - x` under a ramified denominator valuation hypothesis. -/
theorem tendsto_logHigherTailPartialSumField_ofWithZeroValuation_scaled_of_lt_one
    (v : _root_.Valuation K (WithZero (Multiplicative ℤ)))
    {p : ℕ} [Fact p.Prime] (e : ℕ) (x : K)
    (hnK : ∀ n : ℕ, (((n + 1 : ℕ) : K) ≠ 0))
    (hnval : ∀ n : ℕ,
      v (((n + 1 : ℕ) : K)) =
        WithZero.exp (-((e : ℤ) * (padicValNat p (n + 1) : ℤ))))
    (hvx : v x < (1 : WithZero (Multiplicative ℤ)))
    (hcomplete :
      letI : Valued K (WithZero (Multiplicative ℤ)) := Valued.mk' v
      CompleteSpace K) :
    letI : Valued K (WithZero (Multiplicative ℤ)) := Valued.mk' v
    Tendsto
      (fun N : ℕ =>
        ∑ n ∈ Finset.range N, signedLogSeriesTermField x hnK (n + 1))
      atTop
      (𝓝 (logOnePlusSeriesFieldOfWithZeroValuation v x hnK - x)) := by
  let : Valued K (WithZero (Multiplicative ℤ)) := Valued.mk' v
  have hfull :
      Tendsto
        (fun N : ℕ => logOnePlusPartialSumField x hnK (N + 1))
        atTop (𝓝 (logOnePlusSeriesFieldOfWithZeroValuation v x hnK)) := by
    exact
      (tendsto_logOnePlusPartialSumField_ofWithZeroValuation_scaled_of_lt_one
        (v := v) (p := p) e x hnK hnval hvx hcomplete).comp
          (tendsto_add_atTop_nat 1)
  have hsub :
      Tendsto
        (fun N : ℕ => logOnePlusPartialSumField x hnK (N + 1) - x)
        atTop
        (𝓝 (logOnePlusSeriesFieldOfWithZeroValuation v x hnK - x)) :=
    hfull.sub tendsto_const_nhds
  have htail :
      (fun N : ℕ => logOnePlusPartialSumField x hnK (N + 1) - x) =
      fun N : ℕ =>
        ∑ n ∈ Finset.range N, signedLogSeriesTermField x hnK (n + 1) := by
    funext N
    rw [logOnePlusPartialSumField, Finset.sum_range_succ']
    simp
  simpa [htail] using hsub

/-- The full higher-degree logarithm tail has valuation strictly smaller than
the linear term above the ramified `e/(p-1)` threshold. -/
theorem valuation_logHigherTailField_lt_self_of_scaled_inv_sub_one_lt
    (v : _root_.Valuation K (WithZero (Multiplicative ℤ)))
    {p : ℕ} [Fact p.Prime] (e : ℕ) {x : K} (hx : x ≠ 0)
    (hnK : ∀ n : ℕ, (((n + 1 : ℕ) : K) ≠ 0))
    (hnval : ∀ n : ℕ,
      v (((n + 1 : ℕ) : K)) =
        WithZero.exp (-((e : ℤ) * (padicValNat p (n + 1) : ℤ))))
    (hvx : v x < (1 : WithZero (Multiplicative ℤ)))
    (hthreshold :
      (e : ℚ) / ((p : ℚ) - 1) <
        ((ofWithZeroValuation v).val (Units.mk0 x hx) : ℚ))
    (hcomplete :
      letI : Valued K (WithZero (Multiplicative ℤ)) := Valued.mk' v
      CompleteSpace K) :
    v (logOnePlusSeriesFieldOfWithZeroValuation v x hnK - x) <
      v x := by
  exact
    valuation_limit_lt_of_tendsto_of_eventually_lt
      (v := v) (γ := v x) ((_root_.Valuation.ne_zero_iff v).2 hx)
      (tendsto_logHigherTailPartialSumField_ofWithZeroValuation_scaled_of_lt_one
        (v := v) (p := p) e x hnK hnval hvx hcomplete)
      (Eventually.of_forall fun N =>
        valuation_logHigherTailPartialSumField_lt_self_of_scaled_inv_sub_one_lt
          (v := v) (p := p) e (x := x) hx hnK hnval hthreshold N)

/-- Above the ramified `e/(p-1)` threshold, `log(1+x)` has the same valuation
as the linear term `x`. -/
theorem valuation_logOnePlusSeriesField_eq_self_of_scaled_inv_sub_one_lt
    (v : _root_.Valuation K (WithZero (Multiplicative ℤ)))
    {p : ℕ} [Fact p.Prime] (e : ℕ) {x : K} (hx : x ≠ 0)
    (hnK : ∀ n : ℕ, (((n + 1 : ℕ) : K) ≠ 0))
    (hnval : ∀ n : ℕ,
      v (((n + 1 : ℕ) : K)) =
        WithZero.exp (-((e : ℤ) * (padicValNat p (n + 1) : ℤ))))
    (hvx : v x < (1 : WithZero (Multiplicative ℤ)))
    (hthreshold :
      (e : ℚ) / ((p : ℚ) - 1) <
        ((ofWithZeroValuation v).val (Units.mk0 x hx) : ℚ))
    (hcomplete :
      letI : Valued K (WithZero (Multiplicative ℤ)) := Valued.mk' v
      CompleteSpace K) :
    v (logOnePlusSeriesFieldOfWithZeroValuation v x hnK) = v x := by
  have htail :
      v (logOnePlusSeriesFieldOfWithZeroValuation v x hnK - x) <
        v x :=
    valuation_logHigherTailField_lt_self_of_scaled_inv_sub_one_lt
      (v := v) (p := p) e (x := x) hx hnK hnval hvx hthreshold hcomplete
  have hsplit :
      logOnePlusSeriesFieldOfWithZeroValuation v x hnK =
        x + (logOnePlusSeriesFieldOfWithZeroValuation v x hnK - x) := by
    abel
  rw [hsplit]
  exact v.map_add_eq_of_lt_left htail

end MultiplicativeIntegerValuation
end LocalFieldTheory.DiscreteValuationField

end
end

section
-- module Solutions.OAIQ244_DUKE.LocalField_Analytic_LogExpSeries_InverseEstimates
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_isCompleteDiscrete _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.AdicPrincipalUnits.instAddCommGroup _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.AdicPrincipalUnits.instTopologicalSpace _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.DiscretePrincipalUnitQuotient.instAddCommGroup _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitInverseLimitCarrierPadicModule _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitQuotientCarrierPadicModule _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.PrincipalUnitProdiscreteLimit.instAddCommGroup _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.PrincipalUnitProdiscreteLimit.instTopologicalSpace _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitPadicModule _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitPadicSMul _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.residueFieldZModAlgebra _root_.LocalFieldTheory.DiscreteValuationField.Examples.Qp.padicDVRValuation_isRankOneDiscrete _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.LubinTate.Valuations.exponentialValuationSubringIsLocalRing _root_.LubinTate.compatibleGroupFamiliesGroup _root_.OAI.PrimeDegreePackets.instNonemptyLeafTestSpace _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.RamificationTheory.HilbertRamification.Higher.lowerRamificationGroup.instNormal _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionFixedSubring.instIsLocalRing _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionResidueField.instField _root_.RamificationTheory.HilbertRamification.ValuationSubring.selectedResidueField.instAlgebra _root_.RayClass.approximationCompletionTopologicalSpace _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.LocalClassFieldTheory.normalizationIntegerRingIsIntegralClosure _root_.RamificationTheory.HilbertRamification.CompleteDVF.decompositionGroupMulSemiringAction _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen _root_.relativeAdeleRingIntermediateAlgebra _root_.relativeAdeleRingTopIntermediateAlgebra
attribute [-simp] _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.IsDiscreteValuationRing.addVal_ringEquiv _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.EqualCharacteristicLaurent.coeffHom_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.EqualCharacteristicLaurent.powerSeriesEvalHom_C _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.EqualCharacteristicLaurent.powerSeriesEvalHom_X _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.EqualCharacteristicLaurent.powerSeriesEvalSubringHom_C _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.EqualCharacteristicLaurent.powerSeriesEvalSubringHom_X _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.AdicPrincipalUnits.addEquiv_map_smul _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.AdicPrincipalUnits.of_val _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.AdicPrincipalUnits.val_of _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.DiscretePrincipalUnitQuotient.addEquiv_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.DiscretePrincipalUnitQuotient.addEquiv_map_smul _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.DiscretePrincipalUnitQuotient.addEquiv_of _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.DiscretePrincipalUnitQuotient.addEquiv_symm_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.DiscretePrincipalUnitQuotient.of_val _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.DiscretePrincipalUnitQuotient.val_of _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.DiscretePrincipalUnitQuotient.val_transition _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.adicPrincipalUnitsHomeomorphUnderlying_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.iwasawaGlobalInverseLimitCarrier_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitAddEquivInverseLimitCarrier_map_smul _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitAddHomeomorphInverseLimitCarrier_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitInverseLimitCarrierEval_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitInverseLimitCarrierPadic_smul_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitMulEquivInverseLimitCarrier_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitPadic_smul_carrier_coordinate _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitProdiscreteLimitHomeomorphUnderlying_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitQuotientCarrierPadicScalar_eq_smul _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitQuotientCarrierToFull_mk _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitQuotientCarrierTransition_mk _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.uniformizerHigherUnitQuotientEquiv_mk _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.PrincipalUnitProdiscreteLimit.addEquiv_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.PrincipalUnitProdiscreteLimit.addEquiv_map_smul _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.PrincipalUnitProdiscreteLimit.addEquiv_symm_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.PrincipalUnitProdiscreteLimit.coordinate_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.PrincipalUnitProdiscreteLimit.of_val _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.PrincipalUnitProdiscreteLimit.val_of _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.adicPrincipalUnitsContinuousAddEquivUnderlyingOfWithZeroValuation_map_smul _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.adicPrincipalUnitsHomeomorphProdiscreteLimit_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.adicPrincipalUnitsHomeomorphProdiscreteLimit_to_addEquiv _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.iwasawaDegreeTerm_zero _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.iwasawaGn_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.iwasawaPartialProduct_zero_input _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.iwasawaSeedAtLevel_val _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.iwasawaSeedIdeal_val _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.iwasawaSeed_val _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitPadic_natCast_smul _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitPadic_nsmul_eq_pow _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitPadic_smul_def _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitSuccQuotAddEquivResidue_iwasawaSeed _root_.LocalFieldTheory.DiscreteValuationField.LocalField.laurentSeriesEquivLaurentImageSubfield_apply_coe _root_.LocalFieldTheory.IsNonarchimedeanLocalField.multiplicativeIntegerValuation_val _root_.LocalFieldTheory.localIntegerValuationSubringEquiv_apply_coe _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.LocalFieldTheory.residueField_algebraMap_residue _root_.LubinTate.LubinTateSeries.standardLubinTateSeries_toPowerSeries _root_.LubinTate.SameUniformizer.coeff_recursiveIntertwiner _root_.LubinTate.SameUniformizer.constantCoeff_inVariable _root_.LubinTate.SameUniformizer.intertwinerApproximation_zero _root_.LubinTate.SameUniformizer.standardLubinTateEndomorphism_coeff_one _root_.LubinTate.standardLubinTateBaseUniformizerUnit_coe _root_.LubinTate.standardLubinTateChangedUniformizerUnit_coe _root_.LubinTate.standardLubinTateLevelGenerator_coe _root_.LubinTate.standardLubinTatePolynomialIterateOverSeparableClosure_eval _root_.LubinTate.standardLubinTatePolynomialIterate_derivative_eval_zero _root_.LubinTate.standardLubinTatePolynomialIterate_eval_zero _root_.LubinTate.standardLubinTatePolynomialIterate_zero _root_.LubinTate.standardLubinTatePolynomial_derivative_eval_zero _root_.LubinTate.standardLubinTatePolynomial_eval _root_.LubinTate.standardLubinTatePolynomial_toPowerSeries _root_.LubinTate.standardLubinTatePolynomial_toPowerSeries_eq_series _root_.LubinTate.standardLubinTatePrimitivePointInteger_coe _root_.LubinTate.standardLubinTatePrimitivePolynomialOverField_coeff_zero _root_.LubinTate.standardLubinTatePrimitivePolynomial_coeff_zero _root_.LubinTate.standardLubinTateUnitFactorFieldUnit_coe _root_.OAI.PrimeDegreePackets.ThetaConstruction.schwartzCM_apply _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteResidueActionOfHenselianDVF_apply _root_.RamificationTheory.HilbertRamification.Higher.dvfValuationSubringUnitAut_apply _root_.RamificationTheory.HilbertRamification.Higher.lowerRamificationGroup_neg_one _root_.RamificationTheory.HilbertRamification.Higher.mem_dvfHigherPrincipalUnitGroup_iff _root_.RamificationTheory.HilbertRamification.Higher.mem_lowerRamificationGroup_iff _root_.RamificationTheory.HilbertRamification.Higher.mem_valuationSubringDisplacementSubalgebraOfUniqueExtension_iff _root_.RamificationTheory.HilbertRamification.Higher.realRamificationIdeal_nat _root_.RamificationTheory.HilbertRamification.Higher.realRamificationIdeal_neg_one _root_.RamificationTheory.HilbertRamification.Higher.valuationSubringAutOfUniqueExtension_apply_coe _root_.RamificationTheory.HilbertRamification.Higher.valuationSubringAutOfUniqueExtension_apply_inv_apply _root_.RamificationTheory.HilbertRamification.Higher.valuationSubringAutOfUniqueExtension_mul_apply _root_.RamificationTheory.HilbertRamification.Higher.valuationSubringAutOfUniqueExtension_one_apply _root_.infinitePlace_mult_smul
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false
/-!
Develops the valuation estimates showing that logarithm and exponential series are inverse on
their common principal-unit domain.
-/

open Filter
open Polynomial
open scoped Topology
open scoped PowerSeries.WithPiTopology
noncomputable section

attribute [local instance] Classical.propDecidable

universe u

open ValuationTheory.DiscreteValuationField
open LocalFieldTheory.DiscreteValuationField

namespace LocalFieldTheory.DiscreteValuationField
namespace MultiplicativeIntegerValuation

variable {K : Type u} [Field K]

/-- The positive-degree exponential tail partial sums converge to
`expSeries - 1`. -/
theorem tendsto_expSeriesTailPartialSumField_ofWithZeroValuation_of_lt_exp_neg_one
    (v : _root_.Valuation K (WithZero (Multiplicative ℤ)))
    {p : ℕ} [Fact p.Prime] (x : K)
    (hnK : ∀ n : ℕ, (((n.factorial : ℕ) : K) ≠ 0))
    (hnval : ∀ n : ℕ,
      v (((n.factorial : ℕ) : K)) =
        WithZero.exp (-(padicValNat p n.factorial : ℤ)))
    (hvx : v x < WithZero.exp (-1 : ℤ))
    (hcomplete :
      letI : Valued K (WithZero (Multiplicative ℤ)) := Valued.mk' v
      CompleteSpace K) :
    letI : Valued K (WithZero (Multiplicative ℤ)) := Valued.mk' v
    Tendsto
      (fun N : ℕ =>
        ∑ n ∈ Finset.range N, expSeriesTermField x hnK (n + 1))
      atTop
      (𝓝 (expSeriesFieldOfWithZeroValuation v x hnK - 1)) := by
  let : Valued K (WithZero (Multiplicative ℤ)) := Valued.mk' v
  have hfull :
      Tendsto
        (fun N : ℕ => expSeriesPartialSumField x hnK (N + 1))
        atTop (𝓝 (expSeriesFieldOfWithZeroValuation v x hnK)) := by
    exact
      (tendsto_expSeriesPartialSumField_ofWithZeroValuation_of_lt_exp_neg_one
        (v := v) (p := p) x hnK hnval hvx hcomplete).comp
          (tendsto_add_atTop_nat 1)
  have hsub :
      Tendsto
        (fun N : ℕ => expSeriesPartialSumField x hnK (N + 1) - 1)
        atTop (𝓝 (expSeriesFieldOfWithZeroValuation v x hnK - 1)) :=
    hfull.sub tendsto_const_nhds
  have htail :
      (fun N : ℕ => expSeriesPartialSumField x hnK (N + 1) - 1) =
        fun N : ℕ =>
          ∑ n ∈ Finset.range N, expSeriesTermField x hnK (n + 1) := by
    funext N
    rw [expSeriesPartialSumField_succ_eq_one_add_tail]
    abel
  simpa [htail] using hsub

/-- The positive-degree exponential tail partial sums converge to
`expSeries - 1` under the sharp ramified threshold. -/
theorem tendsto_expSeriesTailPartialSumField_ofWithZeroValuation_scaled_of_threshold
    (v : _root_.Valuation K (WithZero (Multiplicative ℤ)))
    {p : ℕ} [Fact p.Prime] (e : ℕ) (x : K)
    (hnK : ∀ n : ℕ, (((n.factorial : ℕ) : K) ≠ 0))
    (hnval : ∀ n : ℕ,
      v (((n.factorial : ℕ) : K)) =
        WithZero.exp (-((e : ℤ) * (padicValNat p n.factorial : ℤ))))
    (hxthreshold : ∀ hx : x ≠ 0,
      (e : ℚ) / ((p : ℚ) - 1) <
        ((ofWithZeroValuation v).val (Units.mk0 x hx) : ℚ))
    (hcomplete :
      letI : Valued K (WithZero (Multiplicative ℤ)) := Valued.mk' v
      CompleteSpace K) :
    letI : Valued K (WithZero (Multiplicative ℤ)) := Valued.mk' v
    Tendsto
      (fun N : ℕ =>
        ∑ n ∈ Finset.range N, expSeriesTermField x hnK (n + 1))
      atTop
      (𝓝 (expSeriesFieldOfWithZeroValuation v x hnK - 1)) := by
  let : Valued K (WithZero (Multiplicative ℤ)) := Valued.mk' v
  have hfull :
      Tendsto
        (fun N : ℕ => expSeriesPartialSumField x hnK (N + 1))
        atTop (𝓝 (expSeriesFieldOfWithZeroValuation v x hnK)) := by
    exact
      (tendsto_expSeriesPartialSumField_ofWithZeroValuation_scaled_of_threshold
        (v := v) (p := p) e x hnK hnval
        (fun hx => by exact_mod_cast hxthreshold hx) hcomplete).comp
          (tendsto_add_atTop_nat 1)
  have hsub :
      Tendsto
        (fun N : ℕ => expSeriesPartialSumField x hnK (N + 1) - 1)
        atTop (𝓝 (expSeriesFieldOfWithZeroValuation v x hnK - 1)) :=
    hfull.sub tendsto_const_nhds
  have htail :
      (fun N : ℕ => expSeriesPartialSumField x hnK (N + 1) - 1) =
        fun N : ℕ =>
          ∑ n ∈ Finset.range N, expSeriesTermField x hnK (n + 1) := by
    funext N
    rw [expSeriesPartialSumField_succ_eq_one_add_tail]
    abel
  simpa [htail] using hsub

/-- Above the sharp ramified `e/(p-1)` threshold, every exponential term of
degree at least two has strictly smaller `ℤᵐ⁰`-value than the linear term. -/
theorem valuation_expSeriesTermField_lt_self_of_scaled_inv_sub_one_lt
    (v : _root_.Valuation K (WithZero (Multiplicative ℤ)))
    {p : ℕ} [Fact p.Prime] (e : ℕ) {x : K} (hx : x ≠ 0)
    (hnK : ∀ n : ℕ, (((n.factorial : ℕ) : K) ≠ 0))
    (hnval : ∀ n : ℕ,
      v (((n.factorial : ℕ) : K)) =
        WithZero.exp (-((e : ℤ) * (padicValNat p n.factorial : ℤ))))
    (hthreshold :
      (e : ℚ) / ((p : ℚ) - 1) <
        ((ofWithZeroValuation v).val (Units.mk0 x hx) : ℚ))
    {n : ℕ} (hn : 2 ≤ n) :
    v (expSeriesTermField x hnK n) < v x := by
  let xu : Kˣ := Units.mk0 x hx
  let denom : Kˣ :=
    Units.mk0 (((n.factorial : ℕ) : K)) (hnK n)
  have hval :
      (ofWithZeroValuation v).val xu <
        (ofWithZeroValuation v).val (xu ^ n / denom) := by
    change
      (ofWithZeroValuation v).val xu <
        (ofWithZeroValuation v).val
          (xu ^ n /
            Units.mk0 (((n.factorial : ℕ) : K)) (hnK n))
    rw [ofWithZeroValuation_val_pow_div_natCast_factorial_scaled
      (v := v) (p := p) (e := e) (n := n) xu (hnK n) (hnval n)]
    exact
      exp_higher_term_integer_valuation_gt_scaled
        (p := p) (e := e) (n := n) hn hthreshold
  have hlt :=
    valuation_lt_of_ofWithZeroValuation_val_lt
      (v := v) (x := xu) (y := xu ^ n / denom) hval
  simpa [xu, denom, expSeriesTermField] using hlt

/-- Every finite higher-degree exponential tail has valuation strictly smaller
than the linear term above the sharp ramified `e/(p-1)` threshold. -/
theorem valuation_expSeriesHigherTailPartialSumField_lt_self_of_scaled_inv_sub_one_lt
    (v : _root_.Valuation K (WithZero (Multiplicative ℤ)))
    {p : ℕ} [Fact p.Prime] (e : ℕ) {x : K} (hx : x ≠ 0)
    (hnK : ∀ n : ℕ, (((n.factorial : ℕ) : K) ≠ 0))
    (hnval : ∀ n : ℕ,
      v (((n.factorial : ℕ) : K)) =
        WithZero.exp (-((e : ℤ) * (padicValNat p n.factorial : ℤ))))
    (hthreshold :
      (e : ℚ) / ((p : ℚ) - 1) <
        ((ofWithZeroValuation v).val (Units.mk0 x hx) : ℚ))
    (N : ℕ) :
    v (∑ n ∈ Finset.range N, expSeriesTermField x hnK (n + 2)) <
      v x := by
  exact
    v.map_sum_lt ((_root_.Valuation.ne_zero_iff v).2 hx)
      (fun n _hn =>
        valuation_expSeriesTermField_lt_self_of_scaled_inv_sub_one_lt
          (v := v) (p := p) e (x := x) hx hnK hnval hthreshold
          (by omega))

/-- The higher-degree exponential tail partial sums converge to
`expSeries - 1 - x` under the sharp ramified threshold. -/
theorem tendsto_expSeriesHigherTailPartialSumField_ofWithZeroValuation_scaled_of_threshold
    (v : _root_.Valuation K (WithZero (Multiplicative ℤ)))
    {p : ℕ} [Fact p.Prime] (e : ℕ) (x : K)
    (hnK : ∀ n : ℕ, (((n.factorial : ℕ) : K) ≠ 0))
    (hnval : ∀ n : ℕ,
      v (((n.factorial : ℕ) : K)) =
        WithZero.exp (-((e : ℤ) * (padicValNat p n.factorial : ℤ))))
    (hxthreshold : ∀ hx : x ≠ 0,
      (e : ℚ) / ((p : ℚ) - 1) <
        ((ofWithZeroValuation v).val (Units.mk0 x hx) : ℚ))
    (hcomplete :
      letI : Valued K (WithZero (Multiplicative ℤ)) := Valued.mk' v
      CompleteSpace K) :
    letI : Valued K (WithZero (Multiplicative ℤ)) := Valued.mk' v
    Tendsto
      (fun N : ℕ =>
        ∑ n ∈ Finset.range N, expSeriesTermField x hnK (n + 2))
      atTop
      (𝓝 (expSeriesFieldOfWithZeroValuation v x hnK - 1 - x)) := by
  let : Valued K (WithZero (Multiplicative ℤ)) := Valued.mk' v
  have hfull :
      Tendsto
        (fun N : ℕ =>
          ∑ n ∈ Finset.range (N + 1),
            expSeriesTermField x hnK (n + 1))
        atTop
        (𝓝 (expSeriesFieldOfWithZeroValuation v x hnK - 1)) := by
    exact
      (tendsto_expSeriesTailPartialSumField_ofWithZeroValuation_scaled_of_threshold
        (v := v) (p := p) e x hnK hnval hxthreshold hcomplete).comp
          (tendsto_add_atTop_nat 1)
  have hsub :
      Tendsto
        (fun N : ℕ =>
          (∑ n ∈ Finset.range (N + 1),
            expSeriesTermField x hnK (n + 1)) - x)
        atTop
        (𝓝 (expSeriesFieldOfWithZeroValuation v x hnK - 1 - x)) :=
    hfull.sub tendsto_const_nhds
  have htail :
      (fun N : ℕ =>
        (∑ n ∈ Finset.range (N + 1),
          expSeriesTermField x hnK (n + 1)) - x) =
      fun N : ℕ =>
        ∑ n ∈ Finset.range N, expSeriesTermField x hnK (n + 2) := by
    funext N
    rw [Finset.sum_range_succ']
    simp [expSeriesTermField]
  simpa [htail] using hsub

/-- The full higher-degree exponential tail has valuation strictly smaller
than the linear term above the sharp ramified `e/(p-1)` threshold. -/
theorem valuation_expSeriesHigherTailField_lt_self_of_scaled_inv_sub_one_lt
    (v : _root_.Valuation K (WithZero (Multiplicative ℤ)))
    {p : ℕ} [Fact p.Prime] (e : ℕ) {x : K} (hx : x ≠ 0)
    (hnK : ∀ n : ℕ, (((n.factorial : ℕ) : K) ≠ 0))
    (hnval : ∀ n : ℕ,
      v (((n.factorial : ℕ) : K)) =
        WithZero.exp (-((e : ℤ) * (padicValNat p n.factorial : ℤ))))
    (hthreshold :
      (e : ℚ) / ((p : ℚ) - 1) <
        ((ofWithZeroValuation v).val (Units.mk0 x hx) : ℚ))
    (hcomplete :
      letI : Valued K (WithZero (Multiplicative ℤ)) := Valued.mk' v
      CompleteSpace K) :
    v (expSeriesFieldOfWithZeroValuation v x hnK - 1 - x) <
      v x := by
  exact
    valuation_limit_lt_of_tendsto_of_eventually_lt
      (v := v) (γ := v x) ((_root_.Valuation.ne_zero_iff v).2 hx)
      (tendsto_expSeriesHigherTailPartialSumField_ofWithZeroValuation_scaled_of_threshold
        (v := v) (p := p) e x hnK hnval
        (fun hx' => by
          have hval_eq :
              (ofWithZeroValuation v).val (Units.mk0 x hx') =
                (ofWithZeroValuation v).val (Units.mk0 x hx) := by
            congr
          rw [hval_eq]
          exact hthreshold)
        hcomplete)
      (Eventually.of_forall fun N =>
        valuation_expSeriesHigherTailPartialSumField_lt_self_of_scaled_inv_sub_one_lt
          (v := v) (p := p) e (x := x) hx hnK hnval hthreshold N)

/-- The exponential-series value is a first principal unit on the normalized
convergence radius: after subtracting the constant term, it lies in the open
unit ball. -/
theorem valuation_expSeriesField_sub_one_lt_one_ofWithZeroValuation_of_lt_exp_neg_one
    (v : _root_.Valuation K (WithZero (Multiplicative ℤ)))
    {p : ℕ} [Fact p.Prime] (x : K)
    (hnK : ∀ n : ℕ, (((n.factorial : ℕ) : K) ≠ 0))
    (hnval : ∀ n : ℕ,
      v (((n.factorial : ℕ) : K)) =
        WithZero.exp (-(padicValNat p n.factorial : ℤ)))
    (hvx : v x < WithZero.exp (-1 : ℤ))
    (hcomplete :
      letI : Valued K (WithZero (Multiplicative ℤ)) := Valued.mk' v
      CompleteSpace K) :
    v (expSeriesFieldOfWithZeroValuation v x hnK - 1) <
      (1 : WithZero (Multiplicative ℤ)) := by
  let : Valued K (WithZero (Multiplicative ℤ)) := Valued.mk' v
  exact
    valuation_limit_lt_one_of_tendsto_of_eventually_lt_one
      (v := v)
      (u := fun N : ℕ =>
        ∑ n ∈ Finset.range N, expSeriesTermField x hnK (n + 1))
      (z := expSeriesFieldOfWithZeroValuation v x hnK - 1)
      (tendsto_expSeriesTailPartialSumField_ofWithZeroValuation_of_lt_exp_neg_one
        (v := v) (p := p) x hnK hnval hvx hcomplete)
      (Eventually.of_forall fun N =>
        valuation_expSeriesTailPartialSumField_lt_one_of_lt_exp_neg_one
          (v := v) (p := p) x hnK hnval hvx N)

/-- On the sharp ramified exponential convergence ball,
`exp(x) - 1` has the same valuation as the linear term `x`. -/
theorem valuation_expSeriesField_sub_one_eq_self_ofWithZeroValuation_scaled_of_threshold
    (v : _root_.Valuation K (WithZero (Multiplicative ℤ)))
    {p : ℕ} [Fact p.Prime] (e : ℕ) {x : K} (hx : x ≠ 0)
    (hnK : ∀ n : ℕ, (((n.factorial : ℕ) : K) ≠ 0))
    (hnval : ∀ n : ℕ,
      v (((n.factorial : ℕ) : K)) =
        WithZero.exp (-((e : ℤ) * (padicValNat p n.factorial : ℤ))))
    (hthreshold :
      (e : ℚ) / ((p : ℚ) - 1) <
        ((ofWithZeroValuation v).val (Units.mk0 x hx) : ℚ))
    (hcomplete :
      letI : Valued K (WithZero (Multiplicative ℤ)) := Valued.mk' v
      CompleteSpace K) :
    v (expSeriesFieldOfWithZeroValuation v x hnK - 1) = v x := by
  have htail :
      v (expSeriesFieldOfWithZeroValuation v x hnK - 1 - x) <
        v x :=
    valuation_expSeriesHigherTailField_lt_self_of_scaled_inv_sub_one_lt
      (v := v) (p := p) e (x := x) hx hnK hnval hthreshold hcomplete
  have hsplit :
      expSeriesFieldOfWithZeroValuation v x hnK - 1 =
        x + (expSeriesFieldOfWithZeroValuation v x hnK - 1 - x) := by
    abel
  rw [hsplit]
  exact v.map_add_eq_of_lt_left htail

/-- The complete-DVF package attached to a standard `ℤᵐ⁰`-valued complete
discrete valuation. -/
def completeDVFOfWithZeroValuation
    (v : _root_.Valuation K (WithZero (Multiplicative ℤ)))
    [ValuationTheory.DiscreteValuationField.Valuation.IsCompleteDiscrete v] :
    CompleteDVF.{u, 0} K where
  ValueGroup := WithZero (Multiplicative ℤ)
  valuation := v
  instCompleteDiscrete := inferInstance

/-- For a normalized `ℤᵐ⁰`-valued complete DVF, an integer-valuation lower
bound gives membership in the corresponding maximal-ideal power. -/
theorem mem_maximalIdeal_pow_ofWithZeroValuation_val_ge
    (v : _root_.Valuation K (WithZero (Multiplicative ℤ)))
    [ValuationTheory.DiscreteValuationField.Valuation.IsCompleteDiscrete v]
    {π : (completeDVFOfWithZeroValuation v).valuationSubring}
    (hπ : v.IsUniformizer (π : K))
    (hπval : v (π : K) = WithZero.exp (-1 : ℤ))
    (n : ℕ) (a : (completeDVFOfWithZeroValuation v).valuationSubring)
    (hval : ∀ ha : (a : K) ≠ 0,
      (n : ℤ) ≤
        (ofWithZeroValuation v).val (Units.mk0 (a : K) ha)) :
    a ∈ (completeDVFOfWithZeroValuation v).maximalIdeal ^ n := by
  by_cases ha0 : (a : K) = 0
  · have ha_zero : a = 0 := Subtype.ext ha0
    simp [ha_zero]
  · have hπpow :
        v (π : K) ^ n =
          WithZero.exp (-(n : ℤ)) := by
      rw [hπval, ← WithZero.exp_nsmul]
      simp
    have hlog :
        WithZero.log (v (a : K)) ≤ -(n : ℤ) := by
      have hNlog :
          (n : ℤ) ≤ -WithZero.log (v (a : K)) := by
        simpa [ofWithZeroValuation_val] using hval ha0
      linarith
    have hva :
        v (a : K) ≤ WithZero.exp (-(n : ℤ)) :=
      WithZero.le_exp_of_log_le hlog
    exact
      (ValuationTheory.DiscreteValuationField.Valuation.mem_maximalIdeal_pow_iff_valuation_le_uniformizer_pow
        (val := v) hπ n (x := a)).2 (by
          change v (a : K) ≤ v ((π : K) ^ n)
          rw [map_pow, hπpow]
          exact hva)

/-- Conversely, membership in `m^n` gives the expected lower bound for the
attached integer valuation. -/
theorem ofWithZeroValuation_val_ge_of_mem_maximalIdeal_pow
    (v : _root_.Valuation K (WithZero (Multiplicative ℤ)))
    [ValuationTheory.DiscreteValuationField.Valuation.IsCompleteDiscrete v]
    {π : (completeDVFOfWithZeroValuation v).valuationSubring}
    (hπ : v.IsUniformizer (π : K))
    (hπval : v (π : K) = WithZero.exp (-1 : ℤ))
    (n : ℕ) (a : (completeDVFOfWithZeroValuation v).valuationSubring)
    (ha : a ∈ (completeDVFOfWithZeroValuation v).maximalIdeal ^ n)
    (ha_ne : (a : K) ≠ 0) :
    (n : ℤ) ≤
      (ofWithZeroValuation v).val (Units.mk0 (a : K) ha_ne) := by
  have hπpow :
      v (π : K) ^ n =
        WithZero.exp (-(n : ℤ)) := by
    rw [hπval, ← WithZero.exp_nsmul]
    simp
  have hva :
      v (a : K) ≤ WithZero.exp (-(n : ℤ)) := by
    have h :=
      (ValuationTheory.DiscreteValuationField.Valuation.mem_maximalIdeal_pow_iff_valuation_le_uniformizer_pow
        (val := v) hπ n (x := a)).1 ha
    change v (a : K) ≤ v ((π : K) ^ n) at h
    rw [map_pow, hπpow] at h
    exact h
  have hv_ne : v (a : K) ≠ 0 :=
    (_root_.Valuation.ne_zero_iff v).2 ha_ne
  have hlog :
      WithZero.log (v (a : K)) ≤ -(n : ℤ) :=
    (WithZero.log_le_iff_le_exp hv_ne).2 hva
  have hneg :
      (n : ℤ) ≤ -WithZero.log (v (a : K)) := by
    simpa using (neg_le_neg hlog)
  simpa [ofWithZeroValuation_val] using hneg

end MultiplicativeIntegerValuation
end LocalFieldTheory.DiscreteValuationField

end
end

section
-- module Solutions.OAIQ244_DUKE.LocalField_Analytic_LogExpSeries_PrincipalUnitExp
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_isCompleteDiscrete _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.AdicPrincipalUnits.instAddCommGroup _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.AdicPrincipalUnits.instTopologicalSpace _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.DiscretePrincipalUnitQuotient.instAddCommGroup _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitInverseLimitCarrierPadicModule _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitQuotientCarrierPadicModule _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.PrincipalUnitProdiscreteLimit.instAddCommGroup _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.PrincipalUnitProdiscreteLimit.instTopologicalSpace _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitPadicModule _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitPadicSMul _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.residueFieldZModAlgebra _root_.LocalFieldTheory.DiscreteValuationField.Examples.Qp.padicDVRValuation_isRankOneDiscrete _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.LubinTate.compatibleGroupFamiliesGroup _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.RamificationTheory.HilbertRamification.Higher.lowerRamificationGroup.instNormal _root_.RamificationTheory.HilbertRamification.ValuationSubring.selectedResidueField.instAlgebra _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.LocalClassFieldTheory.normalizationIntegerRingIsIntegralClosure _root_.RamificationTheory.HilbertRamification.CompleteDVF.decompositionGroupMulSemiringAction _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen _root_.relativeAdeleRingIntermediateAlgebra _root_.relativeAdeleRingTopIntermediateAlgebra
attribute [-simp] _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.IsDiscreteValuationRing.addVal_ringEquiv _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.EqualCharacteristicLaurent.coeffHom_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.EqualCharacteristicLaurent.powerSeriesEvalHom_C _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.EqualCharacteristicLaurent.powerSeriesEvalHom_X _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.EqualCharacteristicLaurent.powerSeriesEvalSubringHom_C _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.EqualCharacteristicLaurent.powerSeriesEvalSubringHom_X _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.AdicPrincipalUnits.addEquiv_map_smul _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.AdicPrincipalUnits.of_val _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.AdicPrincipalUnits.val_of _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.DiscretePrincipalUnitQuotient.addEquiv_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.DiscretePrincipalUnitQuotient.addEquiv_map_smul _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.DiscretePrincipalUnitQuotient.addEquiv_of _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.DiscretePrincipalUnitQuotient.addEquiv_symm_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.DiscretePrincipalUnitQuotient.of_val _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.DiscretePrincipalUnitQuotient.val_of _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.DiscretePrincipalUnitQuotient.val_transition _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.adicPrincipalUnitsHomeomorphUnderlying_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.iwasawaGlobalInverseLimitCarrier_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitAddEquivInverseLimitCarrier_map_smul _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitAddHomeomorphInverseLimitCarrier_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitInverseLimitCarrierEval_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitInverseLimitCarrierPadic_smul_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitMulEquivInverseLimitCarrier_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitPadic_smul_carrier_coordinate _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitProdiscreteLimitHomeomorphUnderlying_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitQuotientCarrierPadicScalar_eq_smul _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitQuotientCarrierToFull_mk _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitQuotientCarrierTransition_mk _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.uniformizerHigherUnitQuotientEquiv_mk _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.PrincipalUnitProdiscreteLimit.addEquiv_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.PrincipalUnitProdiscreteLimit.addEquiv_map_smul _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.PrincipalUnitProdiscreteLimit.addEquiv_symm_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.PrincipalUnitProdiscreteLimit.coordinate_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.PrincipalUnitProdiscreteLimit.of_val _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.PrincipalUnitProdiscreteLimit.val_of _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.adicPrincipalUnitsContinuousAddEquivUnderlyingOfWithZeroValuation_map_smul _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.adicPrincipalUnitsHomeomorphProdiscreteLimit_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.adicPrincipalUnitsHomeomorphProdiscreteLimit_to_addEquiv _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.iwasawaDegreeTerm_zero _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.iwasawaGn_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.iwasawaPartialProduct_zero_input _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.iwasawaSeedAtLevel_val _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.iwasawaSeedIdeal_val _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.iwasawaSeed_val _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitPadic_natCast_smul _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitPadic_nsmul_eq_pow _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitPadic_smul_def _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitSuccQuotAddEquivResidue_iwasawaSeed _root_.LocalFieldTheory.DiscreteValuationField.LocalField.laurentSeriesEquivLaurentImageSubfield_apply_coe _root_.LocalFieldTheory.IsNonarchimedeanLocalField.multiplicativeIntegerValuation_val _root_.LocalFieldTheory.localIntegerValuationSubringEquiv_apply_coe _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.LocalFieldTheory.residueField_algebraMap_residue _root_.LubinTate.LubinTateSeries.standardLubinTateSeries_toPowerSeries _root_.LubinTate.SameUniformizer.coeff_recursiveIntertwiner _root_.LubinTate.SameUniformizer.constantCoeff_inVariable _root_.LubinTate.SameUniformizer.intertwinerApproximation_zero _root_.LubinTate.SameUniformizer.standardLubinTateEndomorphism_coeff_one _root_.LubinTate.standardLubinTateBaseUniformizerUnit_coe _root_.LubinTate.standardLubinTateChangedUniformizerUnit_coe _root_.LubinTate.standardLubinTateLevelGenerator_coe _root_.LubinTate.standardLubinTatePolynomialIterateOverSeparableClosure_eval _root_.LubinTate.standardLubinTatePolynomialIterate_derivative_eval_zero _root_.LubinTate.standardLubinTatePolynomialIterate_eval_zero _root_.LubinTate.standardLubinTatePolynomialIterate_zero _root_.LubinTate.standardLubinTatePolynomial_derivative_eval_zero _root_.LubinTate.standardLubinTatePolynomial_eval _root_.LubinTate.standardLubinTatePolynomial_toPowerSeries _root_.LubinTate.standardLubinTatePolynomial_toPowerSeries_eq_series _root_.LubinTate.standardLubinTatePrimitivePointInteger_coe _root_.LubinTate.standardLubinTatePrimitivePolynomialOverField_coeff_zero _root_.LubinTate.standardLubinTatePrimitivePolynomial_coeff_zero _root_.LubinTate.standardLubinTateUnitFactorFieldUnit_coe _root_.OAI.PrimeDegreePackets.ThetaConstruction.schwartzCM_apply _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteResidueActionOfHenselianDVF_apply _root_.RamificationTheory.HilbertRamification.Higher.dvfValuationSubringUnitAut_apply _root_.RamificationTheory.HilbertRamification.Higher.lowerRamificationGroup_neg_one _root_.RamificationTheory.HilbertRamification.Higher.mem_dvfHigherPrincipalUnitGroup_iff _root_.RamificationTheory.HilbertRamification.Higher.mem_lowerRamificationGroup_iff _root_.RamificationTheory.HilbertRamification.Higher.mem_valuationSubringDisplacementSubalgebraOfUniqueExtension_iff _root_.RamificationTheory.HilbertRamification.Higher.realRamificationIdeal_nat _root_.RamificationTheory.HilbertRamification.Higher.realRamificationIdeal_neg_one _root_.RamificationTheory.HilbertRamification.Higher.valuationSubringAutOfUniqueExtension_apply_coe _root_.RamificationTheory.HilbertRamification.Higher.valuationSubringAutOfUniqueExtension_apply_inv_apply _root_.RamificationTheory.HilbertRamification.Higher.valuationSubringAutOfUniqueExtension_mul_apply _root_.RamificationTheory.HilbertRamification.Higher.valuationSubringAutOfUniqueExtension_one_apply _root_.infinitePlace_mult_smul
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false
/-!
Restricts the exponential series to deep additive ideals and shows that its values lie in the
corresponding principal-unit subgroups.
-/

open Filter
open Polynomial
open scoped Topology
open scoped PowerSeries.WithPiTopology
noncomputable section

attribute [local instance] Classical.propDecidable

universe u

open ValuationTheory.DiscreteValuationField
open LocalFieldTheory.DiscreteValuationField

namespace LocalFieldTheory.DiscreteValuationField
namespace MultiplicativeIntegerValuation

variable {K : Type u} [Field K]

/-- The exponential-series value, viewed as a first principal unit. -/
noncomputable def principalUnitExpSeriesOfWithZeroValuation
    (v : _root_.Valuation K (WithZero (Multiplicative ℤ)))
    [ValuationTheory.DiscreteValuationField.Valuation.IsCompleteDiscrete v]
    {p : ℕ} [Fact p.Prime] (x : K)
    (hnK : ∀ n : ℕ, (((n.factorial : ℕ) : K) ≠ 0))
    (hnval : ∀ n : ℕ,
      v (((n.factorial : ℕ) : K)) =
        WithZero.exp (-(padicValNat p n.factorial : ℤ)))
    (hvx : v x < WithZero.exp (-1 : ℤ))
    (hcomplete :
      letI : Valued K (WithZero (Multiplicative ℤ)) := Valued.mk' v
      CompleteSpace K) :
    (LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup (completeDVFOfWithZeroValuation v)) 1 := by
  let F : CompleteDVF.{u, 0} K := completeDVFOfWithZeroValuation v
  have hlt :
      v (expSeriesFieldOfWithZeroValuation v x hnK - 1) <
        (1 : WithZero (Multiplicative ℤ)) :=
    valuation_expSeriesField_sub_one_lt_one_ofWithZeroValuation_of_lt_exp_neg_one
      (v := v) (p := p) x hnK hnval hvx hcomplete
  let a : F.valuationSubring :=
    ⟨expSeriesFieldOfWithZeroValuation v x hnK - 1,
      (CompleteDVF.mem_valuationSubring_iff F
        (expSeriesFieldOfWithZeroValuation v x hnK - 1)).2
        (by
          change v (expSeriesFieldOfWithZeroValuation v x hnK - 1) ≤ 1
          exact le_of_lt hlt)⟩
  have ha : a ∈ F.maximalIdeal ^ 1 := by
    have ha0 : a ∈ F.maximalIdeal := by
      rw [CompleteDVF.mem_maximalIdeal_iff]
      change v (expSeriesFieldOfWithZeroValuation v x hnK - 1) < 1
      exact hlt
    simpa [pow_one] using ha0
  exact
    LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitOneAddOfMemPowSubgroup
      F (n := 1) le_rfl a ha

/-- Sharp ramified endpoint form of the exponential: if `a ∈ m^n` and
`n > e/(p-1)`, then `Exp(a)` is a principal unit in `U^n`. -/
noncomputable def principalUnitExpSeriesOfMaximalIdealPowOfWithZeroValuationScaled
    (v : _root_.Valuation K (WithZero (Multiplicative ℤ)))
    [ValuationTheory.DiscreteValuationField.Valuation.IsCompleteDiscrete v]
    {p : ℕ} [Fact p.Prime] (e n : ℕ)
    {π : (completeDVFOfWithZeroValuation v).valuationSubring}
    (hπ : v.IsUniformizer (π : K))
    (hπval : v (π : K) = WithZero.exp (-1 : ℤ))
    (hn : 1 ≤ n)
    (hlevel : (e : ℚ) / ((p : ℚ) - 1) < (n : ℚ))
    (hnK : ∀ m : ℕ, (((m.factorial : ℕ) : K) ≠ 0))
    (hnval : ∀ m : ℕ,
      v (((m.factorial : ℕ) : K)) =
        WithZero.exp (-((e : ℤ) * (padicValNat p m.factorial : ℤ))))
    (hcomplete :
      letI : Valued K (WithZero (Multiplicative ℤ)) := Valued.mk' v
      CompleteSpace K)
    (a :
      ((completeDVFOfWithZeroValuation v).maximalIdeal ^ n :
        Ideal (completeDVFOfWithZeroValuation v).valuationSubring)) :
    (LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup (completeDVFOfWithZeroValuation v)) n := by
  let F : CompleteDVF.{u, 0} K := completeDVFOfWithZeroValuation v
  let x : K := ((a : F.valuationSubring) : K)
  have hxthreshold :
      ∀ hx : x ≠ 0,
        (e : ℚ) / ((p : ℚ) - 1) <
          ((ofWithZeroValuation v).val (Units.mk0 x hx) : ℚ) := by
    intro hx
    have hge :
        (n : ℤ) ≤
          (ofWithZeroValuation v).val (Units.mk0 x hx) := by
      simpa [F, x] using
        ofWithZeroValuation_val_ge_of_mem_maximalIdeal_pow
          (v := v) (π := π) hπ hπval n
          (a := (a : F.valuationSubring)) a.property hx
    exact lt_of_lt_of_le hlevel (by exact_mod_cast hge)
  have hbLe :
      v (expSeriesFieldOfWithZeroValuation v x hnK - 1) ≤
        (1 : WithZero (Multiplicative ℤ)) := by
    by_cases hx : x = 0
    · simp [x, hx]
    · have hv :
          v (expSeriesFieldOfWithZeroValuation v x hnK - 1) = v x :=
        valuation_expSeriesField_sub_one_eq_self_ofWithZeroValuation_scaled_of_threshold
          (v := v) (p := p) e (x := x) hx hnK hnval
          (hxthreshold hx) hcomplete
      have hxInt : v x ≤ (1 : WithZero (Multiplicative ℤ)) := by
        have hxMem : x ∈ F.valuation.valuationSubring := by
          change ((a : F.valuationSubring) : K) ∈ F.valuation.valuationSubring
          exact (a : F.valuationSubring).property
        have hxBound := (CompleteDVF.mem_valuationSubring_iff F x).1 hxMem
        change v x ≤ 1 at hxBound
        exact hxBound
      simpa [hv] using hxInt
  let b : F.valuationSubring :=
    ⟨expSeriesFieldOfWithZeroValuation v x hnK - 1,
      (CompleteDVF.mem_valuationSubring_iff F
        (expSeriesFieldOfWithZeroValuation v x hnK - 1)).2
        (by
          change v (expSeriesFieldOfWithZeroValuation v x hnK - 1) ≤ 1
          exact hbLe)⟩
  have hbmem : b ∈ F.maximalIdeal ^ n := by
    apply
      mem_maximalIdeal_pow_ofWithZeroValuation_val_ge
        (v := v) (π := π) hπ hπval n b
    intro hbne
    by_cases hx : x = 0
    · have hbzero : (b : K) = 0 := by
        simp [b, x, hx]
      exact False.elim (hbne hbzero)
    · have hv :
          v (b : K) = v x := by
        simpa [b] using
          valuation_expSeriesField_sub_one_eq_self_ofWithZeroValuation_scaled_of_threshold
            (v := v) (p := p) e (x := x) hx hnK hnval
            (hxthreshold hx) hcomplete
      have hge :
          (n : ℤ) ≤
            (ofWithZeroValuation v).val (Units.mk0 x hx) := by
        simpa [F, x] using
          ofWithZeroValuation_val_ge_of_mem_maximalIdeal_pow
            (v := v) (π := π) hπ hπval n
            (a := (a : F.valuationSubring)) a.property hx
      have hvaleq :
          (ofWithZeroValuation v).val (Units.mk0 (b : K) hbne) =
            (ofWithZeroValuation v).val (Units.mk0 x hx) := by
        simp [ofWithZeroValuation_val, hv]
      rw [hvaleq]
      exact hge
  exact
    LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitOneAddOfMemPowSubgroup
      F hn b hbmem

/--
The underlying field value of the scaled exponential-series principal unit is the corresponding
field exponential series.
-/
@[simp] theorem principalUnitExpSeries_maximalIdealPow_val_ofWithZeroValuationScaled
    (v : _root_.Valuation K (WithZero (Multiplicative ℤ)))
    [ValuationTheory.DiscreteValuationField.Valuation.IsCompleteDiscrete v]
    {p : ℕ} [Fact p.Prime] (e n : ℕ)
    {π : (completeDVFOfWithZeroValuation v).valuationSubring}
    (hπ : v.IsUniformizer (π : K))
    (hπval : v (π : K) = WithZero.exp (-1 : ℤ))
    (hn : 1 ≤ n)
    (hlevel : (e : ℚ) / ((p : ℚ) - 1) < (n : ℚ))
    (hnK : ∀ m : ℕ, (((m.factorial : ℕ) : K) ≠ 0))
    (hnval : ∀ m : ℕ,
      v (((m.factorial : ℕ) : K)) =
        WithZero.exp (-((e : ℤ) * (padicValNat p m.factorial : ℤ))))
    (hcomplete :
      letI : Valued K (WithZero (Multiplicative ℤ)) := Valued.mk' v
      CompleteSpace K)
    (a :
      ((completeDVFOfWithZeroValuation v).maximalIdeal ^ n :
        Ideal (completeDVFOfWithZeroValuation v).valuationSubring)) :
    let F : CompleteDVF.{u, 0} K := completeDVFOfWithZeroValuation v
    ((((principalUnitExpSeriesOfMaximalIdealPowOfWithZeroValuationScaled
        (v := v) (p := p) e n (π := π) hπ hπval hn hlevel
        hnK hnval hcomplete a : (LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup F) n) :
        F.valuationSubringˣ) : F.valuationSubring) : K) =
      expSeriesFieldOfWithZeroValuation v
        (((a : F.valuationSubring) : K)) hnK := by
  simp [principalUnitExpSeriesOfMaximalIdealPowOfWithZeroValuationScaled]

/-- Scaled principal-unit exponential additivity on the sharp convergence threshold:
`Exp(a+b)=Exp(a)Exp(b)` for `a,b ∈ m^n`. -/
theorem principalUnitExpSeries_maximalIdealPow_add_eq_mul_ofWithZeroValuationScaled
    [Algebra ℚ K]
    (v : _root_.Valuation K (WithZero (Multiplicative ℤ)))
    [ValuationTheory.DiscreteValuationField.Valuation.IsCompleteDiscrete v]
    {p : ℕ} [Fact p.Prime] (e n : ℕ)
    {π : (completeDVFOfWithZeroValuation v).valuationSubring}
    (hπ : v.IsUniformizer (π : K))
    (hπval : v (π : K) = WithZero.exp (-1 : ℤ))
    (hn : 1 ≤ n)
    (hlevel : (e : ℚ) / ((p : ℚ) - 1) < (n : ℚ))
    (hnK : ∀ m : ℕ, (((m.factorial : ℕ) : K) ≠ 0))
    (hnval : ∀ m : ℕ,
      v (((m.factorial : ℕ) : K)) =
        WithZero.exp (-((e : ℤ) * (padicValNat p m.factorial : ℤ))))
    (hcomplete :
      letI : Valued K (WithZero (Multiplicative ℤ)) := Valued.mk' v
      CompleteSpace K)
    (a b :
      ((completeDVFOfWithZeroValuation v).maximalIdeal ^ n :
        Ideal (completeDVFOfWithZeroValuation v).valuationSubring)) :
    principalUnitExpSeriesOfMaximalIdealPowOfWithZeroValuationScaled
        (v := v) (p := p) e n (π := π) hπ hπval hn hlevel
        hnK hnval hcomplete (a + b) =
      principalUnitExpSeriesOfMaximalIdealPowOfWithZeroValuationScaled
          (v := v) (p := p) e n (π := π) hπ hπval hn hlevel
          hnK hnval hcomplete a *
        principalUnitExpSeriesOfMaximalIdealPowOfWithZeroValuationScaled
          (v := v) (p := p) e n (π := π) hπ hπval hn hlevel
          hnK hnval hcomplete b := by
  let F : CompleteDVF.{u, 0} K := completeDVFOfWithZeroValuation v
  let x : K := ((a : F.valuationSubring) : K)
  let y : K := ((b : F.valuationSubring) : K)
  have hlevelR : (e : ℝ) / ((p : ℝ) - 1) < (n : ℝ) := by
    exact_mod_cast hlevel
  have hxthreshold : ∀ hx : x ≠ 0,
      (e : ℝ) / ((p : ℝ) - 1) <
        ((ofWithZeroValuation v).val (Units.mk0 x hx) : ℝ) := by
    intro hx
    have hge :
        (n : ℤ) ≤
          (ofWithZeroValuation v).val (Units.mk0 x hx) := by
      simpa [F, x] using
        ofWithZeroValuation_val_ge_of_mem_maximalIdeal_pow
          (v := v) (π := π) hπ hπval n
          (a := (a : F.valuationSubring)) a.property hx
    exact lt_of_lt_of_le hlevelR (by exact_mod_cast hge)
  have hythreshold : ∀ hy : y ≠ 0,
      (e : ℝ) / ((p : ℝ) - 1) <
        ((ofWithZeroValuation v).val (Units.mk0 y hy) : ℝ) := by
    intro hy
    have hge :
        (n : ℤ) ≤
          (ofWithZeroValuation v).val (Units.mk0 y hy) := by
      simpa [F, y] using
        ofWithZeroValuation_val_ge_of_mem_maximalIdeal_pow
          (v := v) (π := π) hπ hπval n
          (a := (b : F.valuationSubring)) b.property hy
    exact lt_of_lt_of_le hlevelR (by exact_mod_cast hge)
  have hfield :
      expSeriesFieldOfWithZeroValuation v (x + y) hnK =
        expSeriesFieldOfWithZeroValuation v x hnK *
          expSeriesFieldOfWithZeroValuation v y hnK :=
    expSeriesField_add_eq_mul_ofWithZeroValuation_scaled_of_threshold
      (v := v) (p := p) e x y hnK hnval hxthreshold hythreshold
      hcomplete
  apply Subtype.ext
  apply Units.ext
  apply Subtype.ext
  simpa [F, x, y] using hfield

/-- The additive parameter `x = u - 1` attached to a first principal unit. -/
noncomputable def principalUnitSubOneOfWithZeroValuation
    (v : _root_.Valuation K (WithZero (Multiplicative ℤ)))
    [ValuationTheory.DiscreteValuationField.Valuation.IsCompleteDiscrete v]
    (u : (LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup (completeDVFOfWithZeroValuation v)) 1) : K :=
  (((u : (completeDVFOfWithZeroValuation v).valuationSubringˣ) :
      (completeDVFOfWithZeroValuation v).valuationSubring) : K) - 1

/--
Establishes the identity `principalUnitSubOneOfWithZeroValuation v
(principalUnitExpSeriesOfWithZeroValuation (v := v) (p := p) x hnK hnval hvx hcomplete) =
expSeriesFieldOfWithZeroValuation v x hnK - 1`.
-/
@[simp] theorem principalUnitSubOne_expSeries_ofWithZeroValuation
    (v : _root_.Valuation K (WithZero (Multiplicative ℤ)))
    [ValuationTheory.DiscreteValuationField.Valuation.IsCompleteDiscrete v]
    {p : ℕ} [Fact p.Prime] (x : K)
    (hnK : ∀ n : ℕ, (((n.factorial : ℕ) : K) ≠ 0))
    (hnval : ∀ n : ℕ,
      v (((n.factorial : ℕ) : K)) =
        WithZero.exp (-(padicValNat p n.factorial : ℤ)))
    (hvx : v x < WithZero.exp (-1 : ℤ))
    (hcomplete :
      letI : Valued K (WithZero (Multiplicative ℤ)) := Valued.mk' v
      CompleteSpace K) :
    principalUnitSubOneOfWithZeroValuation v
      (principalUnitExpSeriesOfWithZeroValuation
        (v := v) (p := p) x hnK hnval hvx hcomplete) =
      expSeriesFieldOfWithZeroValuation v x hnK - 1 := by
  simp [principalUnitSubOneOfWithZeroValuation,
    principalUnitExpSeriesOfWithZeroValuation]

/--
The underlying field value of the exponential-series principal unit is the field exponential
series.
-/
@[simp] theorem principalUnitExpSeries_val_ofWithZeroValuation
    (v : _root_.Valuation K (WithZero (Multiplicative ℤ)))
    [ValuationTheory.DiscreteValuationField.Valuation.IsCompleteDiscrete v]
    {p : ℕ} [Fact p.Prime] (x : K)
    (hnK : ∀ n : ℕ, (((n.factorial : ℕ) : K) ≠ 0))
    (hnval : ∀ n : ℕ,
      v (((n.factorial : ℕ) : K)) =
        WithZero.exp (-(padicValNat p n.factorial : ℤ)))
    (hvx : v x < WithZero.exp (-1 : ℤ))
    (hcomplete :
      letI : Valued K (WithZero (Multiplicative ℤ)) := Valued.mk' v
      CompleteSpace K) :
    let F : CompleteDVF.{u, 0} K := completeDVFOfWithZeroValuation v
    ((((principalUnitExpSeriesOfWithZeroValuation
        (v := v) (p := p) x hnK hnval hvx hcomplete :
          (LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup F) 1) : F.valuationSubringˣ) :
          F.valuationSubring) : K) =
      expSeriesFieldOfWithZeroValuation v x hnK := by
  simp [principalUnitExpSeriesOfWithZeroValuation]

/-- The principal-unit exponential sends zero to the identity. -/
@[simp] theorem principalUnitExpSeries_zero_ofWithZeroValuation
    (v : _root_.Valuation K (WithZero (Multiplicative ℤ)))
    [ValuationTheory.DiscreteValuationField.Valuation.IsCompleteDiscrete v]
    {p : ℕ} [Fact p.Prime]
    (hnK : ∀ n : ℕ, (((n.factorial : ℕ) : K) ≠ 0))
    (hnval : ∀ n : ℕ,
      v (((n.factorial : ℕ) : K)) =
        WithZero.exp (-(padicValNat p n.factorial : ℤ)))
    (hcomplete :
      letI : Valued K (WithZero (Multiplicative ℤ)) := Valued.mk' v
      CompleteSpace K) :
    principalUnitExpSeriesOfWithZeroValuation
      (v := v) (p := p) (0 : K) hnK hnval
      (valuation_zero_lt_exp_neg_one (K := K) v) hcomplete =
      (1 : (LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup (completeDVFOfWithZeroValuation v)) 1) := by
  apply Subtype.ext
  apply Units.ext
  apply Subtype.ext
  simp

/--
The underlying field value of the product of two exponential-series principal units is the product
of their field exponential series.
-/
@[simp] theorem principalUnitExpSeries_mul_val_ofWithZeroValuation
    (v : _root_.Valuation K (WithZero (Multiplicative ℤ)))
    [ValuationTheory.DiscreteValuationField.Valuation.IsCompleteDiscrete v]
    {p : ℕ} [Fact p.Prime] (x y : K)
    (hnK : ∀ n : ℕ, (((n.factorial : ℕ) : K) ≠ 0))
    (hnval : ∀ n : ℕ,
      v (((n.factorial : ℕ) : K)) =
        WithZero.exp (-(padicValNat p n.factorial : ℤ)))
    (hvx : v x < WithZero.exp (-1 : ℤ))
    (hvy : v y < WithZero.exp (-1 : ℤ))
    (hcomplete :
      letI : Valued K (WithZero (Multiplicative ℤ)) := Valued.mk' v
      CompleteSpace K) :
    let F : CompleteDVF.{u, 0} K := completeDVFOfWithZeroValuation v
    (((((principalUnitExpSeriesOfWithZeroValuation
          (v := v) (p := p) x hnK hnval hvx hcomplete) *
        (principalUnitExpSeriesOfWithZeroValuation
          (v := v) (p := p) y hnK hnval hvy hcomplete) :
          (LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup F) 1) : F.valuationSubringˣ) :
          F.valuationSubring) : K) =
      expSeriesFieldOfWithZeroValuation v x hnK *
        expSeriesFieldOfWithZeroValuation v y hnK := by
  simp

/-- Principal-unit exponential multiplicativity on the normalized convergence
ball.  This is the principal-unit form of the field-side identity
`exp(x+y)=exp(x)exp(y)`. -/
theorem principalUnitExpSeries_add_eq_mul_ofWithZeroValuation
    [Algebra ℚ K]
    (v : _root_.Valuation K (WithZero (Multiplicative ℤ)))
    [ValuationTheory.DiscreteValuationField.Valuation.IsCompleteDiscrete v]
    {p : ℕ} [Fact p.Prime] (x y : K)
    (hnK : ∀ n : ℕ, (((n.factorial : ℕ) : K) ≠ 0))
    (hnval : ∀ n : ℕ,
      v (((n.factorial : ℕ) : K)) =
        WithZero.exp (-(padicValNat p n.factorial : ℤ)))
    (hvx : v x < WithZero.exp (-1 : ℤ))
    (hvy : v y < WithZero.exp (-1 : ℤ))
    (hcomplete :
      letI : Valued K (WithZero (Multiplicative ℤ)) := Valued.mk' v
      CompleteSpace K) :
    principalUnitExpSeriesOfWithZeroValuation
        (v := v) (p := p) (x + y) hnK hnval
        (valuation_add_lt_exp_neg_one_of_lt_exp_neg_one v hvx hvy)
        hcomplete =
      (principalUnitExpSeriesOfWithZeroValuation
          (v := v) (p := p) x hnK hnval hvx hcomplete) *
        (principalUnitExpSeriesOfWithZeroValuation
          (v := v) (p := p) y hnK hnval hvy hcomplete) := by
  apply Subtype.ext
  apply Units.ext
  apply Subtype.ext
  simpa [principalUnitExpSeriesOfWithZeroValuation] using
    expSeriesField_add_eq_mul_ofWithZeroValuation_of_lt_exp_neg_one
      (v := v) (p := p) x y hnK hnval hvx hvy hcomplete

/-- The principal-unit exponential as a homomorphism from the additive
convergence ball, written multiplicatively via `Multiplicative`. -/
noncomputable def principalUnitExpSeriesHomOfWithZeroValuation
    [Algebra ℚ K]
    (v : _root_.Valuation K (WithZero (Multiplicative ℤ)))
    [ValuationTheory.DiscreteValuationField.Valuation.IsCompleteDiscrete v]
    {p : ℕ} [Fact p.Prime]
    (hnK : ∀ n : ℕ, (((n.factorial : ℕ) : K) ≠ 0))
    (hnval : ∀ n : ℕ,
      v (((n.factorial : ℕ) : K)) =
        WithZero.exp (-(padicValNat p n.factorial : ℤ)))
    (hcomplete :
      letI : Valued K (WithZero (Multiplicative ℤ)) := Valued.mk' v
      CompleteSpace K) :
    Multiplicative (expConvergenceAddSubgroupOfWithZeroValuation v) →*
      (LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup (completeDVFOfWithZeroValuation v)) 1 where
  toFun x :=
    principalUnitExpSeriesOfWithZeroValuation
      (v := v) (p := p) (x.toAdd : K) hnK hnval x.toAdd.property
      hcomplete
  map_one' := by
    simp
  map_mul' := by
    intro x y
    simpa using
      principalUnitExpSeries_add_eq_mul_ofWithZeroValuation
        (v := v) (p := p) (x.toAdd : K) (y.toAdd : K)
        hnK hnval x.toAdd.property y.toAdd.property hcomplete

/--
Establishes the identity `principalUnitExpSeriesHomOfWithZeroValuation (v := v) (p := p) hnK hnval
hcomplete (Multiplicative.ofAdd x) = principalUnitExpSeriesOfWithZeroValuation (v := v) (p := p)
(x : K) hnK hnval x.property hcomplete`.
-/
@[simp] theorem principalUnitExpSeriesHom_apply_ofAdd
    [Algebra ℚ K]
    (v : _root_.Valuation K (WithZero (Multiplicative ℤ)))
    [ValuationTheory.DiscreteValuationField.Valuation.IsCompleteDiscrete v]
    {p : ℕ} [Fact p.Prime]
    (hnK : ∀ n : ℕ, (((n.factorial : ℕ) : K) ≠ 0))
    (hnval : ∀ n : ℕ,
      v (((n.factorial : ℕ) : K)) =
        WithZero.exp (-(padicValNat p n.factorial : ℤ)))
    (hcomplete :
      letI : Valued K (WithZero (Multiplicative ℤ)) := Valued.mk' v
      CompleteSpace K)
    (x : expConvergenceAddSubgroupOfWithZeroValuation v) :
    principalUnitExpSeriesHomOfWithZeroValuation
        (v := v) (p := p) hnK hnval hcomplete
        (Multiplicative.ofAdd x) =
      principalUnitExpSeriesOfWithZeroValuation
        (v := v) (p := p) (x : K) hnK hnval x.property hcomplete :=
  rfl

/-- A first principal unit has additive parameter of valuation strictly below
one, which is the convergence hypothesis for the logarithm series. -/
theorem principalUnitSubOne_val_lt_one_ofWithZeroValuation
    (v : _root_.Valuation K (WithZero (Multiplicative ℤ)))
    [ValuationTheory.DiscreteValuationField.Valuation.IsCompleteDiscrete v]
    (u : (LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup (completeDVFOfWithZeroValuation v)) 1) :
    v (principalUnitSubOneOfWithZeroValuation v u) <
      (1 : WithZero (Multiplicative ℤ)) := by
  let F : CompleteDVF.{u, 0} K := completeDVFOfWithZeroValuation v
  have hu :
      ((u : F.valuationSubringˣ) : F.valuationSubring) - 1 ∈
        F.maximalIdeal := by
    have hmemPow :
        ((u : F.valuationSubringˣ) : F.valuationSubring) - 1 ∈
          F.maximalIdeal ^ 1 :=
      (LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.mem_iff
        (F := F) 1 (u : F.valuationSubringˣ)).1 u.property
    have hpow : F.maximalIdeal ^ 1 = F.maximalIdeal := by
      change F.maximalIdeal ^ (Nat.succ 0) = F.maximalIdeal
      rw [pow_succ, pow_zero, one_mul]
    rwa [hpow] at hmemPow
  have hlt := (CompleteDVF.mem_maximalIdeal_iff F
    (((u : F.valuationSubringˣ) : F.valuationSubring) - 1)).1 hu
  change v ((((u : F.valuationSubringˣ) : F.valuationSubring) - 1 :
    F.valuationSubring) : K) < (1 : WithZero (Multiplicative ℤ)) at hlt
  simpa [principalUnitSubOneOfWithZeroValuation, F] using hlt

/--
Establishes the identity `principalUnitSubOneOfWithZeroValuation v (1 :
(CompleteDVF.higherPrincipalUnitGroup (completeDVFOfWithZeroValuation v)) 1) = 0`.
-/
@[simp] theorem principalUnitSubOne_one_ofWithZeroValuation
    (v : _root_.Valuation K (WithZero (Multiplicative ℤ)))
    [ValuationTheory.DiscreteValuationField.Valuation.IsCompleteDiscrete v] :
    principalUnitSubOneOfWithZeroValuation v
        (1 : (LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup (completeDVFOfWithZeroValuation v)) 1) =
      0 := by
  simp [principalUnitSubOneOfWithZeroValuation]

/-- The additive parameter of a product of first principal units is
`(u - 1) + (w - 1) + (u - 1)(w - 1)`.  This is the algebraic input for the
formal identity `log((1 + x)(1 + y)) = log(1 + x) + log(1 + y)`. -/
theorem principalUnitSubOne_mul_ofWithZeroValuation
    (v : _root_.Valuation K (WithZero (Multiplicative ℤ)))
    [ValuationTheory.DiscreteValuationField.Valuation.IsCompleteDiscrete v]
    (u w : (LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup (completeDVFOfWithZeroValuation v)) 1) :
    principalUnitSubOneOfWithZeroValuation v (u * w) =
      principalUnitSubOneOfWithZeroValuation v u +
        principalUnitSubOneOfWithZeroValuation v w +
          principalUnitSubOneOfWithZeroValuation v u *
            principalUnitSubOneOfWithZeroValuation v w := by
  simp [principalUnitSubOneOfWithZeroValuation]
  ring

end MultiplicativeIntegerValuation
end LocalFieldTheory.DiscreteValuationField

end
end

section
-- module Solutions.OAIQ244_DUKE.LocalField_Analytic_LogExpSeries_PrincipalUnitLog
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_isCompleteDiscrete _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitInverseLimitCarrierPadicModule _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitQuotientCarrierPadicModule _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitPadicModule _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitPadicSMul _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.residueFieldZModAlgebra _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.RamificationTheory.HilbertRamification.Higher.lowerRamificationGroup.instNormal _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.LocalClassFieldTheory.normalizationIntegerRingIsIntegralClosure _root_.RamificationTheory.HilbertRamification.CompleteDVF.decompositionGroupMulSemiringAction _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false
/-!
Restricts the logarithm series to principal units and places its values in the corresponding
additive ideal.
-/

open Filter
open Polynomial
open scoped Topology
open scoped PowerSeries.WithPiTopology
noncomputable section

attribute [local instance] Classical.propDecidable

universe u

open ValuationTheory.DiscreteValuationField
open LocalFieldTheory.DiscreteValuationField

namespace LocalFieldTheory.DiscreteValuationField
namespace MultiplicativeIntegerValuation

variable {K : Type u} [Field K]

/-- The logarithm-series value of a first principal unit `u`, defined as the
series for `log(1 + (u - 1))`. -/
noncomputable def principalUnitLogSeriesOfWithZeroValuation
    (v : _root_.Valuation K (WithZero (Multiplicative ℤ)))
    [ValuationTheory.DiscreteValuationField.Valuation.IsCompleteDiscrete v]
    (u : (LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup (completeDVFOfWithZeroValuation v)) 1)
    (hnK : ∀ n : ℕ, (((n + 1 : ℕ) : K) ≠ 0)) : K :=
  logOnePlusSeriesFieldOfWithZeroValuation v
    (principalUnitSubOneOfWithZeroValuation v u) hnK

end MultiplicativeIntegerValuation
end LocalFieldTheory.DiscreteValuationField

end
end

section
-- module Solutions.OAIQ244_DUKE.LocalField_Analytic_LogExpSeries_Homomorphisms
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_isCompleteDiscrete _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.AdicPrincipalUnits.instAddCommGroup _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.AdicPrincipalUnits.instTopologicalSpace _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.DiscretePrincipalUnitQuotient.instAddCommGroup _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitInverseLimitCarrierPadicModule _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitQuotientCarrierPadicModule _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.PrincipalUnitProdiscreteLimit.instAddCommGroup _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.PrincipalUnitProdiscreteLimit.instTopologicalSpace _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitPadicModule _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitPadicSMul _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.residueFieldZModAlgebra _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.LubinTate.compatibleGroupFamiliesGroup _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.OAI.PrimeDegreePackets.xT2Space _root_.RamificationTheory.HilbertRamification.Higher.lowerRamificationGroup.instNormal _root_.RayClass.approximationCompletionTopologicalSpace _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.LocalClassFieldTheory.intrinsicAbsoluteGaloisT2 _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.LocalClassFieldTheory.normalizationIntegerRingIsIntegralClosure _root_.RamificationTheory.HilbertRamification.CompleteDVF.decompositionGroupMulSemiringAction _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen
attribute [-simp] _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.IsDiscreteValuationRing.addVal_ringEquiv _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.EqualCharacteristicLaurent.coeffHom_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.EqualCharacteristicLaurent.powerSeriesEvalHom_C _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.EqualCharacteristicLaurent.powerSeriesEvalHom_X _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.EqualCharacteristicLaurent.powerSeriesEvalSubringHom_C _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.EqualCharacteristicLaurent.powerSeriesEvalSubringHom_X _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.AdicPrincipalUnits.addEquiv_map_smul _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.AdicPrincipalUnits.of_val _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.AdicPrincipalUnits.val_of _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.DiscretePrincipalUnitQuotient.addEquiv_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.DiscretePrincipalUnitQuotient.addEquiv_map_smul _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.DiscretePrincipalUnitQuotient.addEquiv_of _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.DiscretePrincipalUnitQuotient.addEquiv_symm_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.DiscretePrincipalUnitQuotient.of_val _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.DiscretePrincipalUnitQuotient.val_of _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.DiscretePrincipalUnitQuotient.val_transition _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.adicPrincipalUnitsHomeomorphUnderlying_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.iwasawaGlobalInverseLimitCarrier_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitAddEquivInverseLimitCarrier_map_smul _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitAddHomeomorphInverseLimitCarrier_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitInverseLimitCarrierEval_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitInverseLimitCarrierPadic_smul_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitMulEquivInverseLimitCarrier_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitPadic_smul_carrier_coordinate _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitProdiscreteLimitHomeomorphUnderlying_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitQuotientCarrierPadicScalar_eq_smul _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitQuotientCarrierToFull_mk _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitQuotientCarrierTransition_mk _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.uniformizerHigherUnitQuotientEquiv_mk _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.PrincipalUnitProdiscreteLimit.addEquiv_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.PrincipalUnitProdiscreteLimit.addEquiv_map_smul _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.PrincipalUnitProdiscreteLimit.addEquiv_symm_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.PrincipalUnitProdiscreteLimit.coordinate_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.PrincipalUnitProdiscreteLimit.of_val _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.PrincipalUnitProdiscreteLimit.val_of _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.adicPrincipalUnitsContinuousAddEquivUnderlyingOfWithZeroValuation_map_smul _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.adicPrincipalUnitsHomeomorphProdiscreteLimit_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.adicPrincipalUnitsHomeomorphProdiscreteLimit_to_addEquiv _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.iwasawaDegreeTerm_zero _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.iwasawaGn_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.iwasawaPartialProduct_zero_input _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.iwasawaSeedAtLevel_val _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.iwasawaSeedIdeal_val _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.iwasawaSeed_val _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitPadic_natCast_smul _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitPadic_nsmul_eq_pow _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitPadic_smul_def _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitSuccQuotAddEquivResidue_iwasawaSeed _root_.LocalFieldTheory.DiscreteValuationField.LocalField.laurentSeriesEquivLaurentImageSubfield_apply_coe _root_.LocalFieldTheory.localIntegerValuationSubringEquiv_apply_coe _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.LocalFieldTheory.residueField_algebraMap_residue _root_.LubinTate.LubinTateSeries.standardLubinTateSeries_toPowerSeries _root_.LubinTate.SameUniformizer.coeff_recursiveIntertwiner _root_.LubinTate.SameUniformizer.constantCoeff_inVariable _root_.LubinTate.SameUniformizer.intertwinerApproximation_zero _root_.LubinTate.SameUniformizer.standardLubinTateEndomorphism_coeff_one _root_.LubinTate.standardLubinTateBaseUniformizerUnit_coe _root_.LubinTate.standardLubinTateChangedUniformizerUnit_coe _root_.LubinTate.standardLubinTateLevelGenerator_coe _root_.LubinTate.standardLubinTatePolynomialIterateOverSeparableClosure_eval _root_.LubinTate.standardLubinTatePolynomialIterate_derivative_eval_zero _root_.LubinTate.standardLubinTatePolynomialIterate_eval_zero _root_.LubinTate.standardLubinTatePolynomialIterate_zero _root_.LubinTate.standardLubinTatePolynomial_derivative_eval_zero _root_.LubinTate.standardLubinTatePolynomial_eval _root_.LubinTate.standardLubinTatePolynomial_toPowerSeries _root_.LubinTate.standardLubinTatePolynomial_toPowerSeries_eq_series _root_.LubinTate.standardLubinTatePrimitivePointInteger_coe _root_.LubinTate.standardLubinTatePrimitivePolynomialOverField_coeff_zero _root_.LubinTate.standardLubinTatePrimitivePolynomial_coeff_zero _root_.LubinTate.standardLubinTateUnitFactorFieldUnit_coe _root_.OAI.PrimeDegreePackets.ThetaConstruction.schwartzCM_apply _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteResidueActionOfHenselianDVF_apply _root_.RamificationTheory.HilbertRamification.Higher.dvfValuationSubringUnitAut_apply _root_.RamificationTheory.HilbertRamification.Higher.lowerRamificationGroup_neg_one _root_.RamificationTheory.HilbertRamification.Higher.mem_dvfHigherPrincipalUnitGroup_iff _root_.RamificationTheory.HilbertRamification.Higher.mem_lowerRamificationGroup_iff _root_.RamificationTheory.HilbertRamification.Higher.mem_valuationSubringDisplacementSubalgebraOfUniqueExtension_iff _root_.RamificationTheory.HilbertRamification.Higher.realRamificationIdeal_nat _root_.RamificationTheory.HilbertRamification.Higher.realRamificationIdeal_neg_one _root_.RamificationTheory.HilbertRamification.Higher.valuationSubringAutOfUniqueExtension_apply_coe _root_.RamificationTheory.HilbertRamification.Higher.valuationSubringAutOfUniqueExtension_apply_inv_apply _root_.RamificationTheory.HilbertRamification.Higher.valuationSubringAutOfUniqueExtension_mul_apply _root_.RamificationTheory.HilbertRamification.Higher.valuationSubringAutOfUniqueExtension_one_apply _root_.infinitePlace_mult_smul
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false
/-!
Packages the convergent logarithm and exponential series as additive and multiplicative
homomorphisms on their natural nonarchimedean domains.
-/

open Filter
open Polynomial
open scoped Topology
open scoped PowerSeries.WithPiTopology
noncomputable section

attribute [local instance] Classical.propDecidable

universe u

open ValuationTheory.DiscreteValuationField
open LocalFieldTheory.DiscreteValuationField

namespace LocalFieldTheory.DiscreteValuationField
namespace MultiplicativeIntegerValuation

variable {K : Type u} [Field K]

/-- Finite logarithm polynomials of a first principal unit. -/
noncomputable def principalUnitLogPartialSumOfWithZeroValuation
    (v : _root_.Valuation K (WithZero (Multiplicative ℤ)))
    [ValuationTheory.DiscreteValuationField.Valuation.IsCompleteDiscrete v]
    (u : (LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup (completeDVFOfWithZeroValuation v)) 1)
    (hnK : ∀ n : ℕ, (((n + 1 : ℕ) : K) ≠ 0)) (N : ℕ) : K :=
  logOnePlusPartialSumField (principalUnitSubOneOfWithZeroValuation v u) hnK N

/-- Establishes the identity `principalUnitLogPartialSumOfWithZeroValuation v u hnK 0 = 0`. -/
@[simp] theorem principalUnitLogPartialSum_zero_ofWithZeroValuation
    (v : _root_.Valuation K (WithZero (Multiplicative ℤ)))
    [ValuationTheory.DiscreteValuationField.Valuation.IsCompleteDiscrete v]
    (u : (LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup (completeDVFOfWithZeroValuation v)) 1)
    (hnK : ∀ n : ℕ, (((n + 1 : ℕ) : K) ≠ 0)) :
    principalUnitLogPartialSumOfWithZeroValuation v u hnK 0 = 0 := by
  simp [principalUnitLogPartialSumOfWithZeroValuation]

/--
Establishes the identity `principalUnitLogPartialSumOfWithZeroValuation v u hnK 1 =
principalUnitSubOneOfWithZeroValuation v u`.
-/
@[simp] theorem principalUnitLogPartialSum_one_ofWithZeroValuation
    (v : _root_.Valuation K (WithZero (Multiplicative ℤ)))
    [ValuationTheory.DiscreteValuationField.Valuation.IsCompleteDiscrete v]
    (u : (LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup (completeDVFOfWithZeroValuation v)) 1)
    (hnK : ∀ n : ℕ, (((n + 1 : ℕ) : K) ≠ 0)) :
    principalUnitLogPartialSumOfWithZeroValuation v u hnK 1 =
      principalUnitSubOneOfWithZeroValuation v u := by
  simp [principalUnitLogPartialSumOfWithZeroValuation]

/--
Establishes the identity `principalUnitLogSeriesOfWithZeroValuation v (1 :
(CompleteDVF.higherPrincipalUnitGroup (completeDVFOfWithZeroValuation v)) 1) hnK = 0`.
-/
@[simp] theorem principalUnitLogSeries_one_ofWithZeroValuation
    (v : _root_.Valuation K (WithZero (Multiplicative ℤ)))
    [ValuationTheory.DiscreteValuationField.Valuation.IsCompleteDiscrete v]
    (hnK : ∀ n : ℕ, (((n + 1 : ℕ) : K) ≠ 0)) :
    principalUnitLogSeriesOfWithZeroValuation v
        (1 : (LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup (completeDVFOfWithZeroValuation v)) 1)
        hnK = 0 := by
  simp [principalUnitLogSeriesOfWithZeroValuation]

/-- Product of principal units, rewritten as the `log(1 + z)` argument for
`z = (u - 1) + (w - 1) + (u - 1)(w - 1)`. -/
theorem principalUnitLogSeries_mul_argument_ofWithZeroValuation
    (v : _root_.Valuation K (WithZero (Multiplicative ℤ)))
    [ValuationTheory.DiscreteValuationField.Valuation.IsCompleteDiscrete v]
    (u w : (LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup (completeDVFOfWithZeroValuation v)) 1)
    (hnK : ∀ n : ℕ, (((n + 1 : ℕ) : K) ≠ 0)) :
    principalUnitLogSeriesOfWithZeroValuation v (u * w) hnK =
      logOnePlusSeriesFieldOfWithZeroValuation v
        (principalUnitSubOneOfWithZeroValuation v u +
          principalUnitSubOneOfWithZeroValuation v w +
            principalUnitSubOneOfWithZeroValuation v u *
              principalUnitSubOneOfWithZeroValuation v w) hnK := by
  simp [principalUnitLogSeriesOfWithZeroValuation,
    principalUnitSubOne_mul_ofWithZeroValuation]

/-- Finite-logarithm-polynomial version of
`principalUnitLogSeries_mul_argument_ofWithZeroValuation`. -/
theorem principalUnitLogPartialSum_mul_argument_ofWithZeroValuation
    (v : _root_.Valuation K (WithZero (Multiplicative ℤ)))
    [ValuationTheory.DiscreteValuationField.Valuation.IsCompleteDiscrete v]
    (u w : (LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup (completeDVFOfWithZeroValuation v)) 1)
    (hnK : ∀ n : ℕ, (((n + 1 : ℕ) : K) ≠ 0)) (N : ℕ) :
    principalUnitLogPartialSumOfWithZeroValuation v (u * w) hnK N =
      logOnePlusPartialSumField
        (principalUnitSubOneOfWithZeroValuation v u +
          principalUnitSubOneOfWithZeroValuation v w +
            principalUnitSubOneOfWithZeroValuation v u *
              principalUnitSubOneOfWithZeroValuation v w) hnK N := by
  simp [principalUnitLogPartialSumOfWithZeroValuation,
    principalUnitSubOne_mul_ofWithZeroValuation]

/-- The finite logarithm polynomials of a first principal unit converge to the
principal-unit logarithm-series value. -/
theorem tendsto_principalUnitLogPartialSum_ofWithZeroValuation
    (v : _root_.Valuation K (WithZero (Multiplicative ℤ)))
    [ValuationTheory.DiscreteValuationField.Valuation.IsCompleteDiscrete v]
    {p : ℕ} [Fact p.Prime]
    (u : (LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup (completeDVFOfWithZeroValuation v)) 1)
    (hnK : ∀ n : ℕ, (((n + 1 : ℕ) : K) ≠ 0))
    (hnval : ∀ n : ℕ,
      v (((n + 1 : ℕ) : K)) =
        WithZero.exp (-(padicValNat p (n + 1) : ℤ)))
    (hcomplete :
      letI : Valued K (WithZero (Multiplicative ℤ)) := Valued.mk' v
      CompleteSpace K) :
    letI : Valued K (WithZero (Multiplicative ℤ)) := Valued.mk' v
    Tendsto
      (fun N : ℕ =>
        principalUnitLogPartialSumOfWithZeroValuation v u hnK N)
      atTop (𝓝 (principalUnitLogSeriesOfWithZeroValuation v u hnK)) := by
  let : Valued K (WithZero (Multiplicative ℤ)) := Valued.mk' v
  have hvx :
      v (principalUnitSubOneOfWithZeroValuation v u) <
        (1 : WithZero (Multiplicative ℤ)) :=
    principalUnitSubOne_val_lt_one_ofWithZeroValuation v u
  simpa [principalUnitLogPartialSumOfWithZeroValuation,
    principalUnitLogSeriesOfWithZeroValuation] using
    tendsto_logOnePlusPartialSumField_ofWithZeroValuation_of_lt_one
      (v := v) (p := p)
      (principalUnitSubOneOfWithZeroValuation v u) hnK hnval hvx hcomplete

/-- The sum of two finite principal-unit logarithm polynomials converges to
`Log(u) + Log(w)`. -/
theorem tendsto_principalUnitLogPartialSum_add_ofWithZeroValuation
    (v : _root_.Valuation K (WithZero (Multiplicative ℤ)))
    [ValuationTheory.DiscreteValuationField.Valuation.IsCompleteDiscrete v]
    {p : ℕ} [Fact p.Prime]
    (u w : (LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup (completeDVFOfWithZeroValuation v)) 1)
    (hnK : ∀ n : ℕ, (((n + 1 : ℕ) : K) ≠ 0))
    (hnval : ∀ n : ℕ,
      v (((n + 1 : ℕ) : K)) =
        WithZero.exp (-(padicValNat p (n + 1) : ℤ)))
    (hcomplete :
      letI : Valued K (WithZero (Multiplicative ℤ)) := Valued.mk' v
      CompleteSpace K) :
    letI : Valued K (WithZero (Multiplicative ℤ)) := Valued.mk' v
    Tendsto
      (fun N : ℕ =>
        principalUnitLogPartialSumOfWithZeroValuation v u hnK N +
          principalUnitLogPartialSumOfWithZeroValuation v w hnK N)
      atTop
      (𝓝 (principalUnitLogSeriesOfWithZeroValuation v u hnK +
        principalUnitLogSeriesOfWithZeroValuation v w hnK)) := by
  let : Valued K (WithZero (Multiplicative ℤ)) := Valued.mk' v
  have hu :=
    tendsto_principalUnitLogPartialSum_ofWithZeroValuation
      (v := v) (p := p) u hnK hnval hcomplete
  have hw :=
    tendsto_principalUnitLogPartialSum_ofWithZeroValuation
      (v := v) (p := p) w hnK hnval hcomplete
  exact hu.add hw

/-- The principal-unit logarithm product defect is the same as the field-level
defect for the two additive parameters `u - 1` and `w - 1`. -/
theorem principalUnitLogPartialSum_product_defect_eq_field_defect_ofWithZeroValuation
    (v : _root_.Valuation K (WithZero (Multiplicative ℤ)))
    [ValuationTheory.DiscreteValuationField.Valuation.IsCompleteDiscrete v]
    (u w : (LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup (completeDVFOfWithZeroValuation v)) 1)
    (hnK : ∀ n : ℕ, (((n + 1 : ℕ) : K) ≠ 0)) (N : ℕ) :
    principalUnitLogPartialSumOfWithZeroValuation v (u * w) hnK N -
        (principalUnitLogPartialSumOfWithZeroValuation v u hnK N +
          principalUnitLogPartialSumOfWithZeroValuation v w hnK N) =
      logOnePlusPartialSumField
          (principalUnitSubOneOfWithZeroValuation v u +
            principalUnitSubOneOfWithZeroValuation v w +
              principalUnitSubOneOfWithZeroValuation v u *
                principalUnitSubOneOfWithZeroValuation v w) hnK N -
        (logOnePlusPartialSumField
            (principalUnitSubOneOfWithZeroValuation v u) hnK N +
          logOnePlusPartialSumField
            (principalUnitSubOneOfWithZeroValuation v w) hnK N) := by
  rw [principalUnitLogPartialSum_mul_argument_ofWithZeroValuation]
  simp [principalUnitLogPartialSumOfWithZeroValuation]

/-- Principal-unit logarithm additivity reduced to the one remaining analytic
bridge: the difference between the product logarithm partial sums and the
sum of the two logarithm partial sums tends to zero.  The formal identity
proved above supplies the coefficient cancellation for this defect; this
lemma records the exact topological endpoint needed by the field-unit logarithm theorem. -/
theorem principalUnitLogSeries_mul_eq_add_of_tendsto_defect_ofWithZeroValuation
    (v : _root_.Valuation K (WithZero (Multiplicative ℤ)))
    [ValuationTheory.DiscreteValuationField.Valuation.IsCompleteDiscrete v]
    {p : ℕ} [Fact p.Prime]
    (u w : (LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup (completeDVFOfWithZeroValuation v)) 1)
    (hnK : ∀ n : ℕ, (((n + 1 : ℕ) : K) ≠ 0))
    (hnval : ∀ n : ℕ,
      v (((n + 1 : ℕ) : K)) =
        WithZero.exp (-(padicValNat p (n + 1) : ℤ)))
    (hcomplete :
      letI : Valued K (WithZero (Multiplicative ℤ)) := Valued.mk' v
      CompleteSpace K)
    (hdefect :
      letI : Valued K (WithZero (Multiplicative ℤ)) := Valued.mk' v
      Tendsto
        (fun N : ℕ =>
          principalUnitLogPartialSumOfWithZeroValuation v (u * w) hnK N -
            (principalUnitLogPartialSumOfWithZeroValuation v u hnK N +
              principalUnitLogPartialSumOfWithZeroValuation v w hnK N))
        atTop (𝓝 (0 : K))) :
    principalUnitLogSeriesOfWithZeroValuation v (u * w) hnK =
      principalUnitLogSeriesOfWithZeroValuation v u hnK +
        principalUnitLogSeriesOfWithZeroValuation v w hnK := by
  let : Valued K (WithZero (Multiplicative ℤ)) := Valued.mk' v
  have hprod :=
    tendsto_principalUnitLogPartialSum_ofWithZeroValuation
      (v := v) (p := p) (u * w) hnK hnval hcomplete
  have hadd :=
    tendsto_principalUnitLogPartialSum_add_ofWithZeroValuation
      (v := v) (p := p) u w hnK hnval hcomplete
  exact
    eq_of_tendsto_sub_zero
      (K := K) hprod hadd hdefect

/-- Field-level version of
`principalUnitLogSeries_mul_eq_add_of_tendsto_defect_ofWithZeroValuation`.
After this reduction, the remaining analytic work for the field-unit logarithm theorem is to
prove that the displayed field-level defect tends to zero from the formal
coefficient identity. -/
theorem principalUnitLogSeries_mul_eq_add_of_tendsto_field_defect_ofWithZeroValuation
    (v : _root_.Valuation K (WithZero (Multiplicative ℤ)))
    [ValuationTheory.DiscreteValuationField.Valuation.IsCompleteDiscrete v]
    {p : ℕ} [Fact p.Prime]
    (u w : (LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup (completeDVFOfWithZeroValuation v)) 1)
    (hnK : ∀ n : ℕ, (((n + 1 : ℕ) : K) ≠ 0))
    (hnval : ∀ n : ℕ,
      v (((n + 1 : ℕ) : K)) =
        WithZero.exp (-(padicValNat p (n + 1) : ℤ)))
    (hcomplete :
      letI : Valued K (WithZero (Multiplicative ℤ)) := Valued.mk' v
      CompleteSpace K)
    (hdefect :
      letI : Valued K (WithZero (Multiplicative ℤ)) := Valued.mk' v
      Tendsto
        (fun N : ℕ =>
          logOnePlusPartialSumField
              (principalUnitSubOneOfWithZeroValuation v u +
                principalUnitSubOneOfWithZeroValuation v w +
                  principalUnitSubOneOfWithZeroValuation v u *
                    principalUnitSubOneOfWithZeroValuation v w) hnK N -
            (logOnePlusPartialSumField
                (principalUnitSubOneOfWithZeroValuation v u) hnK N +
              logOnePlusPartialSumField
                (principalUnitSubOneOfWithZeroValuation v w) hnK N))
        atTop (𝓝 (0 : K))) :
    principalUnitLogSeriesOfWithZeroValuation v (u * w) hnK =
      principalUnitLogSeriesOfWithZeroValuation v u hnK +
        principalUnitLogSeriesOfWithZeroValuation v w hnK := by
  apply principalUnitLogSeries_mul_eq_add_of_tendsto_defect_ofWithZeroValuation
    (v := v) (p := p) u w hnK hnval hcomplete
  let : Valued K (WithZero (Multiplicative ℤ)) := Valued.mk' v
  simpa [principalUnitLogPartialSum_product_defect_eq_field_defect_ofWithZeroValuation
    (v := v) u w hnK] using hdefect

/-- Principal-unit logarithm as a multiplicative homomorphism, conditional only
on the remaining field-level defect convergence.  The codomain is written as
`Multiplicative K`, so multiplication there is addition in the local field. -/
noncomputable def principalUnitLogSeriesHomOfTendstoFieldDefect_ofWithZeroValuation
    (v : _root_.Valuation K (WithZero (Multiplicative ℤ)))
    [ValuationTheory.DiscreteValuationField.Valuation.IsCompleteDiscrete v]
    {p : ℕ} [Fact p.Prime]
    (hnK : ∀ n : ℕ, (((n + 1 : ℕ) : K) ≠ 0))
    (hnval : ∀ n : ℕ,
      v (((n + 1 : ℕ) : K)) =
        WithZero.exp (-(padicValNat p (n + 1) : ℤ)))
    (hcomplete :
      letI : Valued K (WithZero (Multiplicative ℤ)) := Valued.mk' v
      CompleteSpace K)
    (hdefect :
      ∀ u w : (LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup (completeDVFOfWithZeroValuation v)) 1,
        letI : Valued K (WithZero (Multiplicative ℤ)) := Valued.mk' v
        Tendsto
          (fun N : ℕ =>
            logOnePlusPartialSumField
                (principalUnitSubOneOfWithZeroValuation v u +
                  principalUnitSubOneOfWithZeroValuation v w +
                    principalUnitSubOneOfWithZeroValuation v u *
                      principalUnitSubOneOfWithZeroValuation v w) hnK N -
              (logOnePlusPartialSumField
                  (principalUnitSubOneOfWithZeroValuation v u) hnK N +
                logOnePlusPartialSumField
                  (principalUnitSubOneOfWithZeroValuation v w) hnK N))
          atTop (𝓝 (0 : K))) :
    (LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup (completeDVFOfWithZeroValuation v)) 1 →*
      Multiplicative K where
  toFun u := Multiplicative.ofAdd
    (principalUnitLogSeriesOfWithZeroValuation v u hnK)
  map_one' := by
    simp
  map_mul' u w := by
    change
      Multiplicative.ofAdd
          (principalUnitLogSeriesOfWithZeroValuation v (u * w) hnK) =
        Multiplicative.ofAdd
          (principalUnitLogSeriesOfWithZeroValuation v u hnK +
            principalUnitLogSeriesOfWithZeroValuation v w hnK)
    rw [principalUnitLogSeries_mul_eq_add_of_tendsto_field_defect_ofWithZeroValuation
      (v := v) (p := p) u w hnK hnval hcomplete (hdefect u w)]

/--
Establishes the identity `Multiplicative.toAdd
(principalUnitLogSeriesHomOfTendstoFieldDefect_ofWithZeroValuation (v := v) (p := p) hnK hnval
hcomplete hdefect u) = principalUnitLogSeriesOfWithZeroValuation v u hnK`.
-/
@[simp] theorem principalUnitLogSeriesHom_apply_toAdd_ofWithZeroValuation
    (v : _root_.Valuation K (WithZero (Multiplicative ℤ)))
    [ValuationTheory.DiscreteValuationField.Valuation.IsCompleteDiscrete v]
    {p : ℕ} [Fact p.Prime]
    (hnK : ∀ n : ℕ, (((n + 1 : ℕ) : K) ≠ 0))
    (hnval : ∀ n : ℕ,
      v (((n + 1 : ℕ) : K)) =
        WithZero.exp (-(padicValNat p (n + 1) : ℤ)))
    (hcomplete :
      letI : Valued K (WithZero (Multiplicative ℤ)) := Valued.mk' v
      CompleteSpace K)
    (hdefect :
      ∀ u w : (LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup (completeDVFOfWithZeroValuation v)) 1,
        letI : Valued K (WithZero (Multiplicative ℤ)) := Valued.mk' v
        Tendsto
          (fun N : ℕ =>
            logOnePlusPartialSumField
                (principalUnitSubOneOfWithZeroValuation v u +
                  principalUnitSubOneOfWithZeroValuation v w +
                    principalUnitSubOneOfWithZeroValuation v u *
                      principalUnitSubOneOfWithZeroValuation v w) hnK N -
              (logOnePlusPartialSumField
                  (principalUnitSubOneOfWithZeroValuation v u) hnK N +
                logOnePlusPartialSumField
                  (principalUnitSubOneOfWithZeroValuation v w) hnK N))
          atTop (𝓝 (0 : K)))
    (u : (LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup (completeDVFOfWithZeroValuation v)) 1) :
    Multiplicative.toAdd
        (principalUnitLogSeriesHomOfTendstoFieldDefect_ofWithZeroValuation
          (v := v) (p := p) hnK hnval hcomplete hdefect u) =
      principalUnitLogSeriesOfWithZeroValuation v u hnK := by
  rfl

/-- A homomorphism on first principal units extends to the three-factor
decomposition of `Kˣ` by killing the Teichmuller root factor and the
uniformizer factor.  This is the algebraic extension shape used in the field-unit logarithm theorem after the principal-unit logarithm has been proved additive. -/
noncomputable def fieldUnitDecompositionLogHomOfPrincipalUnitHom
    (F : CompleteDVF K) [Finite F.residueField]
    {A : Type*} [AddCommGroup A]
    (φ : (LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup F) 1 →* Multiplicative A) :
    LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.fieldUnitDecompositionFactors F →*
      Multiplicative A where
  toFun z := φ z.1.2
  map_one' := by
    simp
  map_mul' z w := by
    simp

/--
The defining evaluation formula for `fieldUnitDecompositionLogHomOfPrincipalUnitHom` is
`fieldUnitDecompositionLogHomOfPrincipalUnitHom (F := F) φ z = φ z.1.2`.
-/
@[simp] theorem fieldUnitDecompositionLogHomOfPrincipalUnitHom_apply
    (F : CompleteDVF K) [Finite F.residueField]
    {A : Type*} [AddCommGroup A]
    (φ : (LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup F) 1 →* Multiplicative A)
    (z : LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.fieldUnitDecompositionFactors F) :
    fieldUnitDecompositionLogHomOfPrincipalUnitHom (F := F) φ z = φ z.1.2 :=
  rfl

/--
Establishes the identity `fieldUnitDecompositionLogHomOfPrincipalUnitHom (F := F) φ ((ζ, 1), (1 :
Multiplicative ℤ)) = 1`.
-/
@[simp] theorem fieldUnitDecompositionLogHomOfPrincipalUnitHom_root
    (F : CompleteDVF K) [Finite F.residueField]
    {A : Type*} [AddCommGroup A]
    (φ : (LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup F) 1 →* Multiplicative A)
    (ζ : LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.residueRootsOfUnityGroup F) :
    fieldUnitDecompositionLogHomOfPrincipalUnitHom (F := F) φ
        ((ζ, 1), (1 : Multiplicative ℤ)) = 1 := by
  simp

/--
Establishes the identity `fieldUnitDecompositionLogHomOfPrincipalUnitHom (F := F) φ (((1 :
CompleteDVF.higherPrincipalUnitGroup.residueRootsOfUnityGroup F), u), (1 : Multiplicative ℤ)) = φ
u`.
-/
@[simp] theorem fieldUnitDecompositionLogHomOfPrincipalUnitHom_principal
    (F : CompleteDVF K) [Finite F.residueField]
    {A : Type*} [AddCommGroup A]
    (φ : (LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup F) 1 →* Multiplicative A)
    (u : (LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup F) 1) :
    fieldUnitDecompositionLogHomOfPrincipalUnitHom (F := F) φ
        (((1 : LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.residueRootsOfUnityGroup F), u),
          (1 : Multiplicative ℤ)) = φ u := by
  simp

/--
Establishes the identity `fieldUnitDecompositionLogHomOfPrincipalUnitHom (F := F) φ (((1 :
CompleteDVF.higherPrincipalUnitGroup.residueRootsOfUnityGroup F), (1 :
(CompleteDVF.higherPrincipalUnitGroup F) 1)), Multiplicative.ofAdd m) = 1`.
-/
@[simp] theorem fieldUnitDecompositionLogHomOfPrincipalUnitHom_uniformizer
    (F : CompleteDVF K) [Finite F.residueField]
    {A : Type*} [AddCommGroup A]
    (φ : (LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup F) 1 →* Multiplicative A)
    (m : ℤ) :
    fieldUnitDecompositionLogHomOfPrincipalUnitHom (F := F) φ
        (((1 : LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.residueRootsOfUnityGroup F),
            (1 : (LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup F) 1)),
          Multiplicative.ofAdd m) = 1 := by
  simp

/-- A field-unit logarithm homomorphism obtained from a chosen the uniformizer–residue–principal-unit decomposition
three-factor decomposition and a principal-unit logarithm homomorphism. -/
noncomputable def fieldUnitLogHomOfPrincipalUnitHom
    (F : CompleteDVF K) [Finite F.residueField]
    {A : Type*} [AddCommGroup A]
    (e : LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.fieldUnitDecompositionFactors F ≃* Kˣ)
    (φ : (LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup F) 1 →* Multiplicative A) :
    Kˣ →* Multiplicative A :=
  (fieldUnitDecompositionLogHomOfPrincipalUnitHom (F := F) φ).comp
    e.symm.toMonoidHom

/--
The defining evaluation formula for `fieldUnitLogHomOfPrincipalUnitHom` is
`fieldUnitLogHomOfPrincipalUnitHom (F := F) e φ x = φ ((e.symm x).1.2)`.
-/
@[simp] theorem fieldUnitLogHomOfPrincipalUnitHom_apply
    (F : CompleteDVF K) [Finite F.residueField]
    {A : Type*} [AddCommGroup A]
    (e : LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.fieldUnitDecompositionFactors F ≃* Kˣ)
    (φ : (LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup F) 1 →* Multiplicative A) (x : Kˣ) :
    fieldUnitLogHomOfPrincipalUnitHom (F := F) e φ x =
      φ ((e.symm x).1.2) :=
  rfl

end MultiplicativeIntegerValuation
end LocalFieldTheory.DiscreteValuationField

end
end

section
-- module Solutions.OAIQ244_DUKE.LocalField_Analytic_LogExpAdditivity
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_isCompleteDiscrete _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitInverseLimitCarrierPadicModule _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitQuotientCarrierPadicModule _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitPadicModule _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitPadicSMul _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.residueFieldZModAlgebra _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.LubinTate.compatibleGroupFamiliesGroup _root_.OAI.PrimeDegreePackets.instNonemptyLeafTestSpace _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.OAI.PrimeDegreePackets.xT2Space _root_.RamificationTheory.HilbertRamification.Higher.lowerRamificationGroup.instNormal _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionResidueField.instField _root_.RamificationTheory.HilbertRamification.ValuationSubring.selectedResidueField.instAlgebra _root_.RayClass.approximationCompletionTopologicalSpace _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.LocalClassFieldTheory.intrinsicAbsoluteGaloisT2 _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.LocalClassFieldTheory.normalizationIntegerRingIsIntegralClosure _root_.RamificationTheory.HilbertRamification.CompleteDVF.decompositionGroupMulSemiringAction _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen _root_.relativeAdeleRingIntermediateAlgebra _root_.relativeAdeleRingTopIntermediateAlgebra
attribute [-simp] _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.IsDiscreteValuationRing.addVal_ringEquiv _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.EqualCharacteristicLaurent.coeffHom_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.EqualCharacteristicLaurent.powerSeriesEvalHom_C _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.EqualCharacteristicLaurent.powerSeriesEvalHom_X _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.EqualCharacteristicLaurent.powerSeriesEvalSubringHom_C _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.EqualCharacteristicLaurent.powerSeriesEvalSubringHom_X _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.AdicPrincipalUnits.addEquiv_map_smul _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.AdicPrincipalUnits.val_of _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.DiscretePrincipalUnitQuotient.addEquiv_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.DiscretePrincipalUnitQuotient.addEquiv_map_smul _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.DiscretePrincipalUnitQuotient.addEquiv_of _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.DiscretePrincipalUnitQuotient.addEquiv_symm_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.DiscretePrincipalUnitQuotient.val_transition _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.adicPrincipalUnitsHomeomorphUnderlying_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.iwasawaGlobalInverseLimitCarrier_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitAddEquivInverseLimitCarrier_map_smul _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitAddHomeomorphInverseLimitCarrier_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitInverseLimitCarrierEval_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitInverseLimitCarrierPadic_smul_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitMulEquivInverseLimitCarrier_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitPadic_smul_carrier_coordinate _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitProdiscreteLimitHomeomorphUnderlying_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitQuotientCarrierPadicScalar_eq_smul _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitQuotientCarrierToFull_mk _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitQuotientCarrierTransition_mk _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.uniformizerHigherUnitQuotientEquiv_mk _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.PrincipalUnitProdiscreteLimit.addEquiv_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.PrincipalUnitProdiscreteLimit.addEquiv_map_smul _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.PrincipalUnitProdiscreteLimit.addEquiv_symm_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.PrincipalUnitProdiscreteLimit.coordinate_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.adicPrincipalUnitsContinuousAddEquivUnderlyingOfWithZeroValuation_map_smul _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.adicPrincipalUnitsHomeomorphProdiscreteLimit_to_addEquiv _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.iwasawaDegreeTerm_zero _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.iwasawaGn_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.iwasawaPartialProduct_zero_input _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.iwasawaSeedAtLevel_val _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.iwasawaSeedIdeal_val _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.iwasawaSeed_val _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitPadic_natCast_smul _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitPadic_nsmul_eq_pow _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitPadic_smul_def _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitSuccQuotAddEquivResidue_iwasawaSeed _root_.LocalFieldTheory.DiscreteValuationField.LocalField.laurentSeriesEquivLaurentImageSubfield_apply_coe _root_.LocalFieldTheory.localIntegerValuationSubringEquiv_apply_coe _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.LocalFieldTheory.residueField_algebraMap_residue _root_.LubinTate.LubinTateSeries.standardLubinTateSeries_toPowerSeries _root_.LubinTate.SameUniformizer.coeff_recursiveIntertwiner _root_.LubinTate.SameUniformizer.constantCoeff_inVariable _root_.LubinTate.SameUniformizer.intertwinerApproximation_zero _root_.LubinTate.SameUniformizer.standardLubinTateEndomorphism_coeff_one _root_.LubinTate.standardLubinTateBaseUniformizerUnit_coe _root_.LubinTate.standardLubinTateChangedUniformizerUnit_coe _root_.LubinTate.standardLubinTateLevelGenerator_coe _root_.LubinTate.standardLubinTatePolynomialIterateOverSeparableClosure_eval _root_.LubinTate.standardLubinTatePolynomialIterate_derivative_eval_zero _root_.LubinTate.standardLubinTatePolynomialIterate_eval_zero _root_.LubinTate.standardLubinTatePolynomialIterate_zero _root_.LubinTate.standardLubinTatePolynomial_derivative_eval_zero _root_.LubinTate.standardLubinTatePolynomial_eval _root_.LubinTate.standardLubinTatePolynomial_toPowerSeries _root_.LubinTate.standardLubinTatePolynomial_toPowerSeries_eq_series _root_.LubinTate.standardLubinTatePrimitivePointInteger_coe _root_.LubinTate.standardLubinTatePrimitivePolynomialOverField_coeff_zero _root_.LubinTate.standardLubinTatePrimitivePolynomial_coeff_zero _root_.LubinTate.standardLubinTateUnitFactorFieldUnit_coe _root_.OAI.PrimeDegreePackets.ThetaConstruction.schwartzCM_apply _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteResidueActionOfHenselianDVF_apply _root_.RamificationTheory.HilbertRamification.Higher.dvfValuationSubringUnitAut_apply _root_.RamificationTheory.HilbertRamification.Higher.lowerRamificationGroup_neg_one _root_.RamificationTheory.HilbertRamification.Higher.mem_dvfHigherPrincipalUnitGroup_iff _root_.RamificationTheory.HilbertRamification.Higher.mem_lowerRamificationGroup_iff _root_.RamificationTheory.HilbertRamification.Higher.mem_valuationSubringDisplacementSubalgebraOfUniqueExtension_iff _root_.RamificationTheory.HilbertRamification.Higher.realRamificationIdeal_nat _root_.RamificationTheory.HilbertRamification.Higher.realRamificationIdeal_neg_one _root_.RamificationTheory.HilbertRamification.Higher.valuationSubringAutOfUniqueExtension_apply_coe _root_.RamificationTheory.HilbertRamification.Higher.valuationSubringAutOfUniqueExtension_apply_inv_apply _root_.RamificationTheory.HilbertRamification.Higher.valuationSubringAutOfUniqueExtension_mul_apply _root_.RamificationTheory.HilbertRamification.Higher.valuationSubringAutOfUniqueExtension_one_apply _root_.infinitePlace_mult_smul
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

open Filter
open Polynomial
open scoped Topology
open scoped PowerSeries.WithPiTopology

/-!
# Scaled logarithm additivity for local fields

This file supplies the unconditional summability and regrouping step needed to
evaluate the formal identity
`log ((1 + X) * (1 + Y)) = log (1 + X) + log (1 + Y)` in a complete discretely
valued field whose normalized valuation restricts to `e * v_p` on the natural
numbers.
-/

noncomputable section

attribute [local instance] Classical.propDecidable

universe u

open ValuationTheory.DiscreteValuationField
open LocalFieldTheory.DiscreteValuationField

namespace LocalFieldTheory.DiscreteValuationField
namespace MultiplicativeIntegerValuation

variable {K : Type u} [Field K]

/-- The scaled field logarithm series, written as evaluation of the positive
coefficients of the formal series `log (1 + X)`. -/
theorem hasSum_powerSeries_log_eval_logOnePlusSeriesField_ofWithZeroValuation_scaled
    [Algebra ℚ K]
    (v : _root_.Valuation K (WithZero (Multiplicative ℤ)))
    {p : ℕ} [Fact p.Prime] (e : ℕ) (x : K)
    (hnK : ∀ n : ℕ, (((n + 1 : ℕ) : K) ≠ 0))
    (hnval : ∀ n : ℕ,
      v (((n + 1 : ℕ) : K)) =
        WithZero.exp (-((e : ℤ) * (padicValNat p (n + 1) : ℤ))))
    (hvx : v x < (1 : WithZero (Multiplicative ℤ)))
    (hcomplete :
      letI : Valued K (WithZero (Multiplicative ℤ)) := Valued.mk' v
      CompleteSpace K) :
    letI : Valued K (WithZero (Multiplicative ℤ)) := Valued.mk' v
    HasSum
      (fun n : ℕ =>
        PowerSeries.coeff (n + 1) (PowerSeries.log K) *
          x ^ (n + 1))
      (logOnePlusSeriesFieldOfWithZeroValuation v x hnK) := by
  let : Valued K (WithZero (Multiplicative ℤ)) := Valued.mk' v
  have hsum :=
    hasSum_signedLogSeriesTermField_logOnePlusSeriesField_ofWithZeroValuation_scaled_of_lt_one
      (v := v) (p := p) e x hnK hnval hvx hcomplete
  exact hsum.congr_fun fun n =>
    powerSeries_log_coeff_mul_pow_eq_signedLogSeriesTermField
      (K := K) x hnK n

/-- The scaled one-variable formal logarithm evaluation, including its zero
constant coefficient. -/
theorem hasSum_powerSeries_log_eval_nat_logOnePlusSeriesField_ofWithZeroValuation_scaled
    [Algebra ℚ K]
    (v : _root_.Valuation K (WithZero (Multiplicative ℤ)))
    {p : ℕ} [Fact p.Prime] (e : ℕ) (x : K)
    (hnK : ∀ n : ℕ, (((n + 1 : ℕ) : K) ≠ 0))
    (hnval : ∀ n : ℕ,
      v (((n + 1 : ℕ) : K)) =
        WithZero.exp (-((e : ℤ) * (padicValNat p (n + 1) : ℤ))))
    (hvx : v x < (1 : WithZero (Multiplicative ℤ)))
    (hcomplete :
      letI : Valued K (WithZero (Multiplicative ℤ)) := Valued.mk' v
      CompleteSpace K) :
    letI : Valued K (WithZero (Multiplicative ℤ)) := Valued.mk' v
    HasSum
      (fun n : ℕ =>
        PowerSeries.coeff n (PowerSeries.log K) * x ^ n)
      (logOnePlusSeriesFieldOfWithZeroValuation v x hnK) := by
  let : Valued K (WithZero (Multiplicative ℤ)) := Valued.mk' v
  let f : ℕ → K := fun n =>
    PowerSeries.coeff n (PowerSeries.log K) * x ^ n
  have htail :
      HasSum (fun n : ℕ => f (n + 1))
        (logOnePlusSeriesFieldOfWithZeroValuation v x hnK) := by
    simpa only [f] using
      hasSum_powerSeries_log_eval_logOnePlusSeriesField_ofWithZeroValuation_scaled
        (v := v) (p := p) e x hnK hnval hvx hcomplete
  have hfull :=
    (hasSum_nat_add_iff
      (f := f)
      (g := logOnePlusSeriesFieldOfWithZeroValuation v x hnK) 1).1 htail
  simpa [f, PowerSeries.coeff_log] using hfull

/-- Scaled evaluation of the left-axis series in the two-variable formal
product formula. -/
theorem hasSum_formalLogOnePlusLeftVariableLogSubst_monomialValue_pair_ofWithZeroValuation_scaled
    [Algebra ℚ K]
    (v : _root_.Valuation K (WithZero (Multiplicative ℤ)))
    {p : ℕ} [Fact p.Prime] (e : ℕ) (x y : K)
    (hnK : ∀ n : ℕ, (((n + 1 : ℕ) : K) ≠ 0))
    (hnval : ∀ n : ℕ,
      v (((n + 1 : ℕ) : K)) =
        WithZero.exp (-((e : ℤ) * (padicValNat p (n + 1) : ℤ))))
    (hvx : v x < (1 : WithZero (Multiplicative ℤ)))
    (hcomplete :
      letI : Valued K (WithZero (Multiplicative ℤ)) := Valued.mk' v
      CompleteSpace K) :
    letI : Valued K (WithZero (Multiplicative ℤ)) := Valued.mk' v
    HasSum
      (fun d : Fin 2 →₀ ℕ =>
        MvPowerSeries.coeff d (formalLogOnePlusLeftVariableLogSubst K) *
          mvPowerSeriesMonomialValue
            (fun i : Fin 2 => if i = 0 then x else y) d)
      (logOnePlusSeriesFieldOfWithZeroValuation v x hnK) := by
  let : Valued K (WithZero (Multiplicative ℤ)) := Valued.mk' v
  let term : (Fin 2 →₀ ℕ) → K := fun d =>
    MvPowerSeries.coeff d (formalLogOnePlusLeftVariableLogSubst K) *
      mvPowerSeriesMonomialValue
        (fun i : Fin 2 => if i = 0 then x else y) d
  let axis : ℕ → (Fin 2 →₀ ℕ) := fun n => Finsupp.single (0 : Fin 2) n
  have haxis_inj : Function.Injective axis := by
    intro m n h
    have hcoord := congrArg (fun d : Fin 2 →₀ ℕ => d (0 : Fin 2)) h
    simpa [axis] using hcoord
  have haxis :
      HasSum (term ∘ axis)
        (logOnePlusSeriesFieldOfWithZeroValuation v x hnK) := by
    refine
      (hasSum_powerSeries_log_eval_nat_logOnePlusSeriesField_ofWithZeroValuation_scaled
        (v := v) (p := p) e x hnK hnval hvx hcomplete).congr_fun ?_
    intro n
    simp [term, axis, formalLogOnePlusLeftVariableLogSubst_coeff_single,
      mvPowerSeriesMonomialValue]
  have hout : ∀ d, d ∉ Set.range axis → term d = 0 := by
    intro d hd
    have hne : ∀ n : ℕ, d ≠ Finsupp.single (0 : Fin 2) n := by
      intro n h
      exact hd ⟨n, by simpa [axis] using h.symm⟩
    simp [term, formalLogOnePlusLeftVariableLogSubst_coeff_of_ne_axis K d hne]
  exact (haxis_inj.hasSum_iff (f := term) hout).1 haxis

/-- Scaled evaluation of the right-axis series in the two-variable formal
product formula. -/
theorem hasSum_formalLogOnePlusRightVariableLogSubst_monomialValue_pair_ofWithZeroValuation_scaled
    [Algebra ℚ K]
    (v : _root_.Valuation K (WithZero (Multiplicative ℤ)))
    {p : ℕ} [Fact p.Prime] (e : ℕ) (x y : K)
    (hnK : ∀ n : ℕ, (((n + 1 : ℕ) : K) ≠ 0))
    (hnval : ∀ n : ℕ,
      v (((n + 1 : ℕ) : K)) =
        WithZero.exp (-((e : ℤ) * (padicValNat p (n + 1) : ℤ))))
    (hvy : v y < (1 : WithZero (Multiplicative ℤ)))
    (hcomplete :
      letI : Valued K (WithZero (Multiplicative ℤ)) := Valued.mk' v
      CompleteSpace K) :
    letI : Valued K (WithZero (Multiplicative ℤ)) := Valued.mk' v
    HasSum
      (fun d : Fin 2 →₀ ℕ =>
        MvPowerSeries.coeff d (formalLogOnePlusRightVariableLogSubst K) *
          mvPowerSeriesMonomialValue
            (fun i : Fin 2 => if i = 0 then x else y) d)
      (logOnePlusSeriesFieldOfWithZeroValuation v y hnK) := by
  let : Valued K (WithZero (Multiplicative ℤ)) := Valued.mk' v
  let term : (Fin 2 →₀ ℕ) → K := fun d =>
    MvPowerSeries.coeff d (formalLogOnePlusRightVariableLogSubst K) *
      mvPowerSeriesMonomialValue
        (fun i : Fin 2 => if i = 0 then x else y) d
  let axis : ℕ → (Fin 2 →₀ ℕ) := fun n => Finsupp.single (1 : Fin 2) n
  have haxis_inj : Function.Injective axis := by
    intro m n h
    have hcoord := congrArg (fun d : Fin 2 →₀ ℕ => d (1 : Fin 2)) h
    simpa [axis] using hcoord
  have haxis :
      HasSum (term ∘ axis)
        (logOnePlusSeriesFieldOfWithZeroValuation v y hnK) := by
    refine
      (hasSum_powerSeries_log_eval_nat_logOnePlusSeriesField_ofWithZeroValuation_scaled
        (v := v) (p := p) e y hnK hnval hvy hcomplete).congr_fun ?_
    intro n
    simp [term, axis, formalLogOnePlusRightVariableLogSubst_coeff_single,
      mvPowerSeriesMonomialValue]
  have hout : ∀ d, d ∉ Set.range axis → term d = 0 := by
    intro d hd
    have hne : ∀ n : ℕ, d ≠ Finsupp.single (1 : Fin 2) n := by
      intro n h
      exact hd ⟨n, by simpa [axis] using h.symm⟩
    simp [term, formalLogOnePlusRightVariableLogSubst_coeff_of_ne_axis K d hne]
  exact (haxis_inj.hasSum_iff (f := term) hout).1 haxis

/-- Scaled evaluation of the formal product formula's right-hand side. -/
theorem hasSum_formalLogOnePlusProductRightSide_monomialValue_pair_ofWithZeroValuation_scaled
    [Algebra ℚ K]
    (v : _root_.Valuation K (WithZero (Multiplicative ℤ)))
    {p : ℕ} [Fact p.Prime] (e : ℕ) (x y : K)
    (hnK : ∀ n : ℕ, (((n + 1 : ℕ) : K) ≠ 0))
    (hnval : ∀ n : ℕ,
      v (((n + 1 : ℕ) : K)) =
        WithZero.exp (-((e : ℤ) * (padicValNat p (n + 1) : ℤ))))
    (hvx : v x < (1 : WithZero (Multiplicative ℤ)))
    (hvy : v y < (1 : WithZero (Multiplicative ℤ)))
    (hcomplete :
      letI : Valued K (WithZero (Multiplicative ℤ)) := Valued.mk' v
      CompleteSpace K) :
    letI : Valued K (WithZero (Multiplicative ℤ)) := Valued.mk' v
    HasSum
      (fun d : Fin 2 →₀ ℕ =>
        MvPowerSeries.coeff d (formalLogOnePlusProductRightSide K) *
          mvPowerSeriesMonomialValue
            (fun i : Fin 2 => if i = 0 then x else y) d)
      (logOnePlusSeriesFieldOfWithZeroValuation v x hnK +
        logOnePlusSeriesFieldOfWithZeroValuation v y hnK) := by
  let : Valued K (WithZero (Multiplicative ℤ)) := Valued.mk' v
  have hleft :=
    hasSum_formalLogOnePlusLeftVariableLogSubst_monomialValue_pair_ofWithZeroValuation_scaled
      (v := v) (p := p) e x y hnK hnval hvx hcomplete
  have hright :=
    hasSum_formalLogOnePlusRightVariableLogSubst_monomialValue_pair_ofWithZeroValuation_scaled
      (v := v) (p := p) e x y hnK hnval hvy hcomplete
  refine (hleft.add hright).congr_fun ?_
  intro d
  rw [formalLogOnePlusProductRightSide_coeff]
  ring

/-- The full Sigma-family obtained by expanding every power of
`X + Y + XY` in the scaled logarithm substitution is unconditionally
summable.  No rearrangement hypothesis is exposed: nonzero terms in each
fixed outer degree have finite polynomial support, while their values are
bounded by the convergent one-variable logarithm terms. -/
theorem summable_formalLogOnePlusProductArgument_logDegree_monomialValue_pair_ofWithZeroValuation_scaled
    [Algebra ℚ K]
    (v : _root_.Valuation K (WithZero (Multiplicative ℤ)))
    {p : ℕ} [Fact p.Prime] (e : ℕ) (x y : K)
    (hnK : ∀ n : ℕ, (((n + 1 : ℕ) : K) ≠ 0))
    (hnval : ∀ n : ℕ,
      v (((n + 1 : ℕ) : K)) =
        WithZero.exp (-((e : ℤ) * (padicValNat p (n + 1) : ℤ))))
    (hvx : v x < (1 : WithZero (Multiplicative ℤ)))
    (hvy : v y < (1 : WithZero (Multiplicative ℤ)))
    (hcomplete :
      letI : Valued K (WithZero (Multiplicative ℤ)) := Valued.mk' v
      CompleteSpace K) :
    letI : Valued K (WithZero (Multiplicative ℤ)) := Valued.mk' v
    Summable
      (fun qd : Sigma fun _ : ℕ => Fin 2 →₀ ℕ =>
        PowerSeries.coeff qd.1 (PowerSeries.log K) *
          MvPowerSeries.coeff qd.2
            ((formalLogOnePlusProductArgument K) ^ qd.1) *
          mvPowerSeriesMonomialValue
            (fun i : Fin 2 => if i = 0 then x else y) qd.2) := by
  let : Valued K (WithZero (Multiplicative ℤ)) := Valued.mk' v
  let : CompleteSpace K := hcomplete
  have : NonarchimedeanRing K := nonarchimedeanRing_ofWithZeroValuation v
  let term : (Sigma fun _ : ℕ => Fin 2 →₀ ℕ) → K := fun qd =>
    PowerSeries.coeff qd.1 (PowerSeries.log K) *
      MvPowerSeries.coeff qd.2
        ((formalLogOnePlusProductArgument K) ^ qd.1) *
      mvPowerSeriesMonomialValue
        (fun i : Fin 2 => if i = 0 then x else y) qd.2
  change Summable term
  rw [NonarchimedeanAddGroup.summable_iff_tendsto_cofinite_zero]
  rw [tendsto_def]
  intro s hs
  have hrepr := Valued.mem_nhds_zero.mp hs
  let γ := Classical.choose hrepr
  have hγ := Classical.choose_spec hrepr
  have hball :
      {z : K |
        v z < MonoidWithZeroHom.ValueGroup₀.embedding γ.1} ∈ nhds (0 : K) := by
    apply Valued.mem_nhds_zero.mpr
    exact ⟨γ, by
      intro z hz
      change Valued.v.restrict z < γ.1 at hz
      rw [Valuation.restrict_lt_iff_lt_embedding] at hz
      exact hz⟩
  have hxsum :=
    hasSum_powerSeries_log_eval_nat_logOnePlusSeriesField_ofWithZeroValuation_scaled
      (v := v) (p := p) e x hnK hnval hvx hcomplete
  have hysum :=
    hasSum_powerSeries_log_eval_nat_logOnePlusSeriesField_ofWithZeroValuation_scaled
      (v := v) (p := p) e y hnK hnval hvy hcomplete
  have hxzero :
      Tendsto
        (fun q : ℕ =>
          PowerSeries.coeff q (PowerSeries.log K) * x ^ q)
        atTop (nhds (0 : K)) := by
    have h := hxsum.summable.tendsto_cofinite_zero
    simpa [Nat.cofinite_eq_atTop] using h
  have hyzero :
      Tendsto
        (fun q : ℕ =>
          PowerSeries.coeff q (PowerSeries.log K) * y ^ q)
        atTop (nhds (0 : K)) := by
    have h := hysum.summable.tendsto_cofinite_zero
    simpa [Nat.cofinite_eq_atTop] using h
  have hevent : ∀ᶠ q : ℕ in atTop,
      v (PowerSeries.coeff q (PowerSeries.log K) * x ^ q) <
          MonoidWithZeroHom.ValueGroup₀.embedding γ.1 ∧
      v (PowerSeries.coeff q (PowerSeries.log K) * y ^ q) <
          MonoidWithZeroHom.ValueGroup₀.embedding γ.1 :=
    (hxzero.eventually hball).and (hyzero.eventually hball)
  have hexN := Filter.eventually_atTop.mp hevent
  let N := Classical.choose hexN
  have hN := Classical.choose_spec hexN
  let P : MvPolynomial (Fin 2) K :=
    formalLogOnePlusProductArgumentPolynomial K
  let E : Finset (Sigma fun _ : ℕ => Fin 2 →₀ ℕ) :=
    (Finset.range N).sigma fun q => (P ^ q).support
  apply Filter.mem_cofinite.mpr
  apply E.finite_toSet.subset
  intro qd hbad
  by_contra hnotE
  have hgood : term qd ∈ s := by
    by_cases hqsmall : qd.1 < N
    · have hdnot : qd.2 ∉ (P ^ qd.1).support := by
        intro hd
        apply hnotE
        exact Finset.mem_sigma.mpr ⟨Finset.mem_range.mpr hqsmall, hd⟩
      have hpoly : (P ^ qd.1).coeff qd.2 = 0 := by
        by_contra hp
        exact hdnot (MvPolynomial.mem_support_iff.mpr hp)
      have hcoeff :
          MvPowerSeries.coeff qd.2
              ((formalLogOnePlusProductArgument K) ^ qd.1) = 0 := by
        rw [formalLogOnePlusProductArgument_eq_coe_polynomial,
          ← MvPolynomial.coe_pow, MvPolynomial.coeff_coe]
        exact hpoly
      have htermzero : term qd = 0 := by simp [term, hcoeff]
      rw [htermzero]
      exact mem_of_mem_nhds hs
    · have hqN : N ≤ qd.1 := Nat.le_of_not_gt hqsmall
      have hcomp := hN qd.1 hqN
      apply hγ
      change Valued.v.restrict (term qd) < γ.1
      rw [Valuation.restrict_lt_iff_lt_embedding]
      have hbound :=
        valuation_formalLogOnePlusProductArgument_sigmaTerm_le_max
          (v := v) (p := p) e hnval hvx hvy qd.1 qd.2
      exact lt_of_le_of_lt hbound (max_lt hcomp.1 hcomp.2)
  exact hbad hgood

/-- The expanded product-argument Sigma-family has sum equal to the scaled
logarithm of `x + y + xy`. -/
theorem hasSum_formalLogOnePlusProductArgument_logDegree_monomialValue_pair_sigma_ofWithZeroValuation_scaled
    [Algebra ℚ K]
    (v : _root_.Valuation K (WithZero (Multiplicative ℤ)))
    {p : ℕ} [Fact p.Prime] (e : ℕ) (x y : K)
    (hnK : ∀ n : ℕ, (((n + 1 : ℕ) : K) ≠ 0))
    (hnval : ∀ n : ℕ,
      v (((n + 1 : ℕ) : K)) =
        WithZero.exp (-((e : ℤ) * (padicValNat p (n + 1) : ℤ))))
    (hvx : v x < (1 : WithZero (Multiplicative ℤ)))
    (hvy : v y < (1 : WithZero (Multiplicative ℤ)))
    (hcomplete :
      letI : Valued K (WithZero (Multiplicative ℤ)) := Valued.mk' v
      CompleteSpace K) :
    letI : Valued K (WithZero (Multiplicative ℤ)) := Valued.mk' v
    HasSum
      (fun qd : Sigma fun _ : ℕ => Fin 2 →₀ ℕ =>
        PowerSeries.coeff qd.1 (PowerSeries.log K) *
          MvPowerSeries.coeff qd.2
            ((formalLogOnePlusProductArgument K) ^ qd.1) *
          mvPowerSeriesMonomialValue
            (fun i : Fin 2 => if i = 0 then x else y) qd.2)
      (logOnePlusSeriesFieldOfWithZeroValuation v (x + y + x * y) hnK) := by
  let : Valued K (WithZero (Multiplicative ℤ)) := Valued.mk' v
  have harg :
      v (x + y + x * y) < (1 : WithZero (Multiplicative ℤ)) :=
    valuation_log_mul_argument_lt_one_of_lt_one v hvx hvy
  have houter :
      HasSum
        (fun q : ℕ =>
          PowerSeries.coeff q (PowerSeries.log K) *
            (x + y + x * y) ^ q)
        (logOnePlusSeriesFieldOfWithZeroValuation v
          (x + y + x * y) hnK) :=
    hasSum_powerSeries_log_eval_nat_logOnePlusSeriesField_ofWithZeroValuation_scaled
      (v := v) (p := p) e (x + y + x * y) hnK hnval harg hcomplete
  have hinner :
      ∀ q : ℕ,
        HasSum
          (fun d : Fin 2 →₀ ℕ =>
            PowerSeries.coeff q (PowerSeries.log K) *
              MvPowerSeries.coeff d
                ((formalLogOnePlusProductArgument K) ^ q) *
              mvPowerSeriesMonomialValue
                (fun i : Fin 2 => if i = 0 then x else y) d)
          (PowerSeries.coeff q (PowerSeries.log K) *
            (x + y + x * y) ^ q) := by
    intro q
    exact
      hasSum_formalLogOnePlusProductArgument_pow_monomialValue_pair_mul_left
        K (PowerSeries.coeff q (PowerSeries.log K)) x y q
  have hsigma :=
    summable_formalLogOnePlusProductArgument_logDegree_monomialValue_pair_ofWithZeroValuation_scaled
      (v := v) (p := p) e x y hnK hnval hvx hvy hcomplete
  exact HasSum.sigma_of_hasSum houter hinner hsigma

/-- Regrouping the scaled Sigma-family by monomial exponent evaluates the
substituted formal logarithm itself.  The inner sum is finite for every fixed
monomial, by the degree bound in power-series substitution. -/
theorem hasSum_formalLogOnePlusProductArgument_logSubst_monomialValue_pair_ofWithZeroValuation_scaled
    [Algebra ℚ K]
    (v : _root_.Valuation K (WithZero (Multiplicative ℤ)))
    {p : ℕ} [Fact p.Prime] (e : ℕ) (x y : K)
    (hnK : ∀ n : ℕ, (((n + 1 : ℕ) : K) ≠ 0))
    (hnval : ∀ n : ℕ,
      v (((n + 1 : ℕ) : K)) =
        WithZero.exp (-((e : ℤ) * (padicValNat p (n + 1) : ℤ))))
    (hvx : v x < (1 : WithZero (Multiplicative ℤ)))
    (hvy : v y < (1 : WithZero (Multiplicative ℤ)))
    (hcomplete :
      letI : Valued K (WithZero (Multiplicative ℤ)) := Valued.mk' v
      CompleteSpace K) :
    letI : Valued K (WithZero (Multiplicative ℤ)) := Valued.mk' v
    HasSum
      (fun d : Fin 2 →₀ ℕ =>
        MvPowerSeries.coeff d
            (PowerSeries.subst (formalLogOnePlusProductArgument K) (PowerSeries.log K)) *
          mvPowerSeriesMonomialValue
            (fun i : Fin 2 => if i = 0 then x else y) d)
      (logOnePlusSeriesFieldOfWithZeroValuation v (x + y + x * y) hnK) := by
  let : Valued K (WithZero (Multiplicative ℤ)) := Valued.mk' v
  let sigmaTerm : (Sigma fun _ : ℕ => Fin 2 →₀ ℕ) → K := fun qd =>
    PowerSeries.coeff qd.1 (PowerSeries.log K) *
      MvPowerSeries.coeff qd.2
        ((formalLogOnePlusProductArgument K) ^ qd.1) *
      mvPowerSeriesMonomialValue
        (fun i : Fin 2 => if i = 0 then x else y) qd.2
  have hsigma :
      HasSum sigmaTerm
        (logOnePlusSeriesFieldOfWithZeroValuation v
          (x + y + x * y) hnK) := by
    simpa [sigmaTerm] using
      hasSum_formalLogOnePlusProductArgument_logDegree_monomialValue_pair_sigma_ofWithZeroValuation_scaled
        (v := v) (p := p) e x y hnK hnval hvx hvy hcomplete
  let swap :
      (Sigma fun _ : (Fin 2 →₀ ℕ) => ℕ) ≃
        (Sigma fun _ : ℕ => Fin 2 →₀ ℕ) :=
    { toFun := fun dq => ⟨dq.2, dq.1⟩
      invFun := fun qd => ⟨qd.2, qd.1⟩
      left_inv := by intro dq; cases dq; rfl
      right_inv := by intro qd; cases qd; rfl }
  have hswapped :
      HasSum (sigmaTerm ∘ swap)
        (logOnePlusSeriesFieldOfWithZeroValuation v
          (x + y + x * y) hnK) :=
    (swap.hasSum_iff).2 hsigma
  have hfiber :
      ∀ d : Fin 2 →₀ ℕ,
        HasSum
          (fun q : ℕ => (sigmaTerm ∘ swap) ⟨d, q⟩)
          (MvPowerSeries.coeff d
              (PowerSeries.subst (formalLogOnePlusProductArgument K) (PowerSeries.log K)) *
            mvPowerSeriesMonomialValue
              (fun i : Fin 2 => if i = 0 then x else y) d) := by
    intro d
    let monomial :=
      mvPowerSeriesMonomialValue
        (fun i : Fin 2 => if i = 0 then x else y) d
    let fiberTerm : ℕ → K := fun q =>
      PowerSeries.coeff q (PowerSeries.log K) *
        MvPowerSeries.coeff d
          ((formalLogOnePlusProductArgument K) ^ q) * monomial
    have hfinite :
        HasSum fiberTerm
          (∑ q ∈ Finset.range (Finsupp.degree d + 1), fiberTerm q) := by
      apply hasSum_sum_of_ne_finset_zero
      intro q hq
      have hqge : Finsupp.degree d + 1 ≤ q := by
        simpa only [Finset.mem_range, not_lt] using hq
      have hdegree : Finsupp.degree d < q := Nat.lt_of_succ_le hqge
      have hzero :=
        formalLogOnePlusProductArgument_pow_coeff_eq_zero_of_degree_lt
          K q d hdegree
      simp [fiberTerm, hzero]
    have hsum :
        (∑ q ∈ Finset.range (Finsupp.degree d + 1), fiberTerm q) =
          MvPowerSeries.coeff d
              (PowerSeries.subst (formalLogOnePlusProductArgument K)
                (PowerSeries.log K)) *
            monomial := by
      rw [formalLogOnePlusProductArgument_logSubst_coeff_eq_sum_range_degree_succ]
      simp only [smul_eq_mul, fiberTerm]
      rw [Finset.sum_mul]
    rw [hsum] at hfinite
    simpa [fiberTerm, monomial, sigmaTerm, swap, Function.comp_def] using hfinite
  exact hswapped.sigma hfiber

/-- Scaled field-level logarithm additivity on the open unit ball, obtained by
evaluating the formal product identity after the unconditional regrouping
above. -/
theorem logOnePlusSeriesField_mul_argument_eq_add_ofWithZeroValuation_scaled
    [Algebra ℚ K]
    (v : _root_.Valuation K (WithZero (Multiplicative ℤ)))
    {p : ℕ} [Fact p.Prime] (e : ℕ) (x y : K)
    (hnK : ∀ n : ℕ, (((n + 1 : ℕ) : K) ≠ 0))
    (hnval : ∀ n : ℕ,
      v (((n + 1 : ℕ) : K)) =
        WithZero.exp (-((e : ℤ) * (padicValNat p (n + 1) : ℤ))))
    (hvx : v x < (1 : WithZero (Multiplicative ℤ)))
    (hvy : v y < (1 : WithZero (Multiplicative ℤ)))
    (hcomplete :
      letI : Valued K (WithZero (Multiplicative ℤ)) := Valued.mk' v
      CompleteSpace K) :
    letI : Valued K (WithZero (Multiplicative ℤ)) := Valued.mk' v
    logOnePlusSeriesFieldOfWithZeroValuation v (x + y + x * y) hnK =
      logOnePlusSeriesFieldOfWithZeroValuation v x hnK +
        logOnePlusSeriesFieldOfWithZeroValuation v y hnK := by
  let : Valued K (WithZero (Multiplicative ℤ)) := Valued.mk' v
  have hleft :=
    hasSum_formalLogOnePlusProductArgument_logSubst_monomialValue_pair_ofWithZeroValuation_scaled
      (v := v) (p := p) e x y hnK hnval hvx hvy hcomplete
  have hright :=
    hasSum_formalLogOnePlusProductRightSide_monomialValue_pair_ofWithZeroValuation_scaled
      (v := v) (p := p) e x y hnK hnval hvx hvy hcomplete
  exact formalLogOnePlusProductFormula_hasSum_monomialValue_eq
    (A := K) hleft hright

/-- Scaled logarithm-series additivity on first principal units.  Unlike the
earlier endpoint reduction, this theorem has no defect-convergence hypothesis. -/
theorem principalUnitLogSeries_mul_eq_add_ofWithZeroValuation_scaled
    [Algebra ℚ K]
    (v : _root_.Valuation K (WithZero (Multiplicative ℤ)))
    [ValuationTheory.DiscreteValuationField.Valuation.IsCompleteDiscrete v]
    {p : ℕ} [Fact p.Prime] (e : ℕ)
    (u w : (LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup (completeDVFOfWithZeroValuation v)) 1)
    (hnK : ∀ n : ℕ, (((n + 1 : ℕ) : K) ≠ 0))
    (hnval : ∀ n : ℕ,
      v (((n + 1 : ℕ) : K)) =
        WithZero.exp (-((e : ℤ) * (padicValNat p (n + 1) : ℤ))))
    (hcomplete :
      letI : Valued K (WithZero (Multiplicative ℤ)) := Valued.mk' v
      CompleteSpace K) :
    principalUnitLogSeriesOfWithZeroValuation v (u * w) hnK =
      principalUnitLogSeriesOfWithZeroValuation v u hnK +
        principalUnitLogSeriesOfWithZeroValuation v w hnK := by
  let x := principalUnitSubOneOfWithZeroValuation v u
  let y := principalUnitSubOneOfWithZeroValuation v w
  have hvx : v x < (1 : WithZero (Multiplicative ℤ)) := by
    simpa [x] using principalUnitSubOne_val_lt_one_ofWithZeroValuation v u
  have hvy : v y < (1 : WithZero (Multiplicative ℤ)) := by
    simpa [y] using principalUnitSubOne_val_lt_one_ofWithZeroValuation v w
  have hadd :=
    logOnePlusSeriesField_mul_argument_eq_add_ofWithZeroValuation_scaled
      (v := v) (p := p) e x y hnK hnval hvx hvy hcomplete
  rw [principalUnitLogSeries_mul_argument_ofWithZeroValuation]
  simpa [principalUnitLogSeriesOfWithZeroValuation, x, y] using hadd

/-- The scaled logarithm series as a genuine homomorphism on first principal
units, with no supplied additivity or defect theorem. -/
noncomputable def principalUnitLogSeriesHomOfWithZeroValuationScaled
    [Algebra ℚ K]
    (v : _root_.Valuation K (WithZero (Multiplicative ℤ)))
    [ValuationTheory.DiscreteValuationField.Valuation.IsCompleteDiscrete v]
    {p : ℕ} [Fact p.Prime] (e : ℕ)
    (hnK : ∀ n : ℕ, (((n + 1 : ℕ) : K) ≠ 0))
    (hnval : ∀ n : ℕ,
      v (((n + 1 : ℕ) : K)) =
        WithZero.exp (-((e : ℤ) * (padicValNat p (n + 1) : ℤ))))
    (hcomplete :
      letI : Valued K (WithZero (Multiplicative ℤ)) := Valued.mk' v
      CompleteSpace K) :
    (LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup (completeDVFOfWithZeroValuation v)) 1 →*
      Multiplicative K where
  toFun u := Multiplicative.ofAdd
    (principalUnitLogSeriesOfWithZeroValuation v u hnK)
  map_one' := by simp
  map_mul' u w := by
    change
      Multiplicative.ofAdd
          (principalUnitLogSeriesOfWithZeroValuation v (u * w) hnK) =
        Multiplicative.ofAdd
          (principalUnitLogSeriesOfWithZeroValuation v u hnK +
            principalUnitLogSeriesOfWithZeroValuation v w hnK)
    rw [principalUnitLogSeries_mul_eq_add_ofWithZeroValuation_scaled
      (v := v) (p := p) e u w hnK hnval hcomplete]

/--
Establishes the identity `Multiplicative.toAdd (principalUnitLogSeriesHomOfWithZeroValuationScaled
(v := v) (p := p) e hnK hnval hcomplete u) = principalUnitLogSeriesOfWithZeroValuation v u hnK`.
-/
@[simp] theorem principalUnitLogSeriesHomOfWithZeroValuationScaled_apply_toAdd
    [Algebra ℚ K]
    (v : _root_.Valuation K (WithZero (Multiplicative ℤ)))
    [ValuationTheory.DiscreteValuationField.Valuation.IsCompleteDiscrete v]
    {p : ℕ} [Fact p.Prime] (e : ℕ)
    (hnK : ∀ n : ℕ, (((n + 1 : ℕ) : K) ≠ 0))
    (hnval : ∀ n : ℕ,
      v (((n + 1 : ℕ) : K)) =
        WithZero.exp (-((e : ℤ) * (padicValNat p (n + 1) : ℤ))))
    (hcomplete :
      letI : Valued K (WithZero (Multiplicative ℤ)) := Valued.mk' v
      CompleteSpace K)
    (u : (LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup (completeDVFOfWithZeroValuation v)) 1) :
    Multiplicative.toAdd
        (principalUnitLogSeriesHomOfWithZeroValuationScaled
          (v := v) (p := p) e hnK hnval hcomplete u) =
      principalUnitLogSeriesOfWithZeroValuation v u hnK := by
  rfl

end MultiplicativeIntegerValuation
end LocalFieldTheory.DiscreteValuationField

end
end

section
-- module Solutions.OAIQ244_DUKE.LocalField_Analytic_LogExpComposition
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.residueFieldZModAlgebra _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.PrimeDegreePackets.instNonemptyLeafTestSpace _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.OAI.PrimeDegreePackets.xT2Space _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionResidueField.instField _root_.RamificationTheory.HilbertRamification.ValuationSubring.selectedResidueField.instAlgebra _root_.RayClass.approximationCompletionTopologicalSpace _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.LocalClassFieldTheory.intrinsicAbsoluteGaloisT2 _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.LocalClassFieldTheory.normalizationIntegerRingIsIntegralClosure _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen _root_.relativeAdeleRingIntermediateAlgebra _root_.relativeAdeleRingTopIntermediateAlgebra
attribute [-simp] _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.IsDiscreteValuationRing.addVal_ringEquiv _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.LocalFieldTheory.IsNonarchimedeanLocalField.multiplicativeIntegerValuation_val _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.LocalFieldTheory.residueField_algebraMap_residue _root_.OAI.PrimeDegreePackets.ThetaConstruction.schwartzCM_apply _root_.infinitePlace_mult_smul
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

open Filter
open Polynomial
open scoped Topology
open scoped PowerSeries.WithPiTopology

/-!
# Exact logarithm--exponential compositions

This file evaluates the two formal composition identities used in
the deep exponential–logarithm equivalence, on the sharp ramified
convergence ball.  The source lemmas below justify the Cauchy products and
the unconditional regrouping involved in power-series substitution.
-/

noncomputable section

attribute [local instance] Classical.propDecidable

universe u

namespace LocalFieldTheory.DiscreteValuationField
namespace MultiplicativeIntegerValuation

variable {K : Type u} [Field K]

/-! ## Scaled logarithm and exponential input estimates -/

/-- Scaled evaluation of the formal exponential series. -/
theorem hasSum_formalExpPowerSeries_eval_expSeriesField_ofWithZeroValuation_scaled
    [Algebra ℚ K]
    (v : _root_.Valuation K (WithZero (Multiplicative ℤ)))
    {p : ℕ} [Fact p.Prime] (e : ℕ) (x : K)
    (hnK : ∀ n : ℕ, (((n.factorial : ℕ) : K) ≠ 0))
    (hnval : ∀ n : ℕ,
      v (((n.factorial : ℕ) : K)) =
        WithZero.exp (-((e : ℤ) * (padicValNat p n.factorial : ℤ))))
    (hthreshold : ∀ hx : x ≠ 0,
      (e : ℝ) / ((p : ℝ) - 1) <
        ((ofWithZeroValuation v).val (Units.mk0 x hx) : ℝ))
    (hcomplete :
      letI : Valued K (WithZero (Multiplicative ℤ)) := Valued.mk' v
      CompleteSpace K) :
    letI : Valued K (WithZero (Multiplicative ℤ)) := Valued.mk' v
    HasSum
      (fun n : ℕ =>
        PowerSeries.coeff n (PowerSeries.exp K) * x ^ n)
      (expSeriesFieldOfWithZeroValuation v x hnK) := by
  let : Valued K (WithZero (Multiplicative ℤ)) := Valued.mk' v
  have hsum :=
    hasSum_expSeriesTermField_expSeriesField_ofWithZeroValuation_scaled_of_threshold
      (v := v) (p := p) e x hnK hnval hthreshold hcomplete
  exact hsum.congr_fun fun n =>
    formalExpPowerSeries_coeff_mul_pow_eq_expSeriesTermField
      (K := K) x hnK n

/-- The scaled threshold implies that the argument lies in the open unit
ball, including the zero argument. -/
theorem valuation_lt_one_ofWithZeroValuation_scaled_threshold_real
    (v : _root_.Valuation K (WithZero (Multiplicative ℤ)))
    {p : ℕ} [Fact p.Prime] (e : ℕ) {x : K}
    (hthreshold : ∀ hx : x ≠ 0,
      (e : ℝ) / ((p : ℝ) - 1) <
        ((ofWithZeroValuation v).val (Units.mk0 x hx) : ℝ)) :
    v x < (1 : WithZero (Multiplicative ℤ)) := by
  by_cases hx : x = 0
  · simp [hx]
  · have hp_two : (2 : ℕ) ≤ p := (Fact.out : Nat.Prime p).two_le
    have hp_two_real : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp_two
    have hp_sub_pos : 0 < ((p : ℝ) - 1) := by linarith
    have hnonneg : 0 ≤ (e : ℝ) / ((p : ℝ) - 1) :=
      div_nonneg (Nat.cast_nonneg e) hp_sub_pos.le
    have hxval_pos_real :
        (0 : ℝ) <
          ((ofWithZeroValuation v).val (Units.mk0 x hx) : ℝ) :=
      lt_of_le_of_lt hnonneg (hthreshold hx)
    have hxval_pos :
        0 < (ofWithZeroValuation v).val (Units.mk0 x hx) := by
      exact_mod_cast hxval_pos_real
    exact valuation_lt_one_of_ofWithZeroValuation_val_pos
      v (Units.mk0 x hx) hxval_pos

/-- On the sharp scaled threshold, every evaluated coefficient of the formal
logarithm is bounded by the linear term. -/
theorem valuation_powerSeries_log_coeff_mul_pow_le_self_scaled
    [Algebra ℚ K]
    (v : _root_.Valuation K (WithZero (Multiplicative ℤ)))
    {p : ℕ} [Fact p.Prime] (e : ℕ) {x : K}
    (hnK : ∀ n : ℕ, (((n + 1 : ℕ) : K) ≠ 0))
    (hnval : ∀ n : ℕ,
      v (((n + 1 : ℕ) : K)) =
        WithZero.exp (-((e : ℤ) * (padicValNat p (n + 1) : ℤ))))
    (hthreshold : ∀ hx : x ≠ 0,
      (e : ℝ) / ((p : ℝ) - 1) <
        ((ofWithZeroValuation v).val (Units.mk0 x hx) : ℝ))
    (d : ℕ) :
    v (PowerSeries.coeff d (PowerSeries.log K) * x ^ d) ≤
      v x := by
  by_cases hx : x = 0
  · subst x
    by_cases hd : d = 0
    · subst d
      simp [PowerSeries.coeff_log]
    · simp [hd]
  · have hthresholdRat :
        (e : ℚ) / ((p : ℚ) - 1) <
          ((ofWithZeroValuation v).val (Units.mk0 x hx) : ℚ) := by
      exact_mod_cast hthreshold hx
    cases d with
    | zero => simp [PowerSeries.coeff_log]
    | succ n =>
        cases n with
        | zero =>
            rw [powerSeries_log_coeff_mul_pow_eq_signedLogSeriesTermField
              (K := K) x hnK 0]
            simp
        | succ n =>
            rw [powerSeries_log_coeff_mul_pow_eq_signedLogSeriesTermField
              (K := K) x hnK (n + 1)]
            exact le_of_lt
              (valuation_signedLogSeriesTermField_lt_self_of_scaled_inv_sub_one_lt
                (v := v) (p := p) e (x := x) hx hnK hnval hthresholdRat
                (by omega : n + 1 ≠ 0))

/-- On the sharp scaled threshold, every evaluated coefficient of
`exp(X)-1` is bounded by its linear term. -/
theorem valuation_formalExp_sub_one_coeff_mul_pow_le_self_scaled
    [Algebra ℚ K]
    (v : _root_.Valuation K (WithZero (Multiplicative ℤ)))
    {p : ℕ} [Fact p.Prime] (e : ℕ) {x : K}
    (hnK : ∀ n : ℕ, (((n.factorial : ℕ) : K) ≠ 0))
    (hnval : ∀ n : ℕ,
      v (((n.factorial : ℕ) : K)) =
        WithZero.exp (-((e : ℤ) * (padicValNat p n.factorial : ℤ))))
    (hthreshold : ∀ hx : x ≠ 0,
      (e : ℝ) / ((p : ℝ) - 1) <
        ((ofWithZeroValuation v).val (Units.mk0 x hx) : ℝ))
    (d : ℕ) :
    v (PowerSeries.coeff d ((PowerSeries.exp K) - 1) * x ^ d) ≤ v x := by
  by_cases hx : x = 0
  · subst x
    by_cases hd : d = 0
    · subst d
      simp
    · simp [hd]
  · have hthresholdRat :
        (e : ℚ) / ((p : ℚ) - 1) <
          ((ofWithZeroValuation v).val (Units.mk0 x hx) : ℚ) := by
      exact_mod_cast hthreshold hx
    cases d with
    | zero => simp
    | succ n =>
        cases n with
        | zero => simp [PowerSeries.coeff_exp]
        | succ n =>
            have hcoeff :
                PowerSeries.coeff (n + 2) ((PowerSeries.exp K) - 1) * x ^ (n + 2) =
                  expSeriesTermField x hnK (n + 2) := by
              rw [map_sub]
              have hone :
                  PowerSeries.coeff (n + 2) (1 : PowerSeries K) = 0 := by
                simp [PowerSeries.coeff_one]
              rw [hone, sub_zero]
              exact
                formalExpPowerSeries_coeff_mul_pow_eq_expSeriesTermField
                  (K := K) x hnK (n + 2)
            rw [hcoeff]
            exact le_of_lt
              (valuation_expSeriesTermField_lt_self_of_scaled_inv_sub_one_lt
                (v := v) (p := p) e (x := x) hx hnK hnval hthresholdRat
                (by omega : 2 ≤ n + 2))

/-! ## Evaluation of the two formal identities -/

/-- The deep exponential–logarithm equivalence, exact principal-unit composite:
on the sharp scaled threshold, evaluating the formal identity
`exp(log(1+X)) = 1+X` gives `exp(log(1+x)) = 1+x`. -/
theorem expSeries_logOnePlusSeries_eq_one_add_ofWithZeroValuation_scaled_of_threshold
    [Algebra ℚ K]
    (v : _root_.Valuation K (WithZero (Multiplicative ℤ)))
    {p : ℕ} [Fact p.Prime] (e : ℕ) (x : K)
    (hnKlog : ∀ n : ℕ, (((n + 1 : ℕ) : K) ≠ 0))
    (hnvalLog : ∀ n : ℕ,
      v (((n + 1 : ℕ) : K)) =
        WithZero.exp (-((e : ℤ) * (padicValNat p (n + 1) : ℤ))))
    (hnKexp : ∀ n : ℕ, (((n.factorial : ℕ) : K) ≠ 0))
    (hnvalExp : ∀ n : ℕ,
      v (((n.factorial : ℕ) : K)) =
        WithZero.exp (-((e : ℤ) * (padicValNat p n.factorial : ℤ))))
    (hthreshold : ∀ hx : x ≠ 0,
      (e : ℝ) / ((p : ℝ) - 1) <
        ((ofWithZeroValuation v).val (Units.mk0 x hx) : ℝ))
    (hcomplete :
      letI : Valued K (WithZero (Multiplicative ℤ)) := Valued.mk' v
      CompleteSpace K) :
    expSeriesFieldOfWithZeroValuation v
        (logOnePlusSeriesFieldOfWithZeroValuation v x hnKlog) hnKexp =
      1 + x := by
  let : Valued K (WithZero (Multiplicative ℤ)) := Valued.mk' v
  let : CompleteSpace K := hcomplete
  have : NonarchimedeanRing K := nonarchimedeanRing_ofWithZeroValuation v
  let : IsAddTorsionFree K := IsAddTorsionFree.of_module_rat K
  by_cases hx : x = 0
  · subst x
    simp
  · let y : K := logOnePlusSeriesFieldOfWithZeroValuation v x hnKlog
    have hvx_lt_one : v x < (1 : WithZero (Multiplicative ℤ)) :=
      valuation_lt_one_ofWithZeroValuation_scaled_threshold_real
        (v := v) (p := p) e hthreshold
    have hthresholdRat :
        (e : ℚ) / ((p : ℚ) - 1) <
          ((ofWithZeroValuation v).val (Units.mk0 x hx) : ℚ) := by
      exact_mod_cast hthreshold hx
    have hvy_eq : v y = v x := by
      simpa [y] using
        valuation_logOnePlusSeriesField_eq_self_of_scaled_inv_sub_one_lt
          (v := v) (p := p) e (x := x) hx hnKlog hnvalLog hvx_lt_one
          hthresholdRat hcomplete
    have hy : y ≠ 0 := by
      intro hy0
      have hzero : v y = 0 := by simp [hy0]
      have hxzero : v x = 0 := by simpa [hvy_eq] using hzero
      exact ((_root_.Valuation.ne_zero_iff v).2 hx) hxzero
    have hyval_eq :
        (ofWithZeroValuation v).val (Units.mk0 y hy) =
          (ofWithZeroValuation v).val (Units.mk0 x hx) :=
      ofWithZeroValuation_val_eq_of_valuation_eq v hvy_eq
    have hythreshold : ∀ hy' : y ≠ 0,
        (e : ℝ) / ((p : ℝ) - 1) <
          ((ofWithZeroValuation v).val (Units.mk0 y hy') : ℝ) := by
      intro hy'
      have hyproof : Units.mk0 y hy' = Units.mk0 y hy := by
        ext
        rfl
      rw [hyproof, hyval_eq]
      exact hthreshold hx
    have hinner :
        HasSum
          (fun d : ℕ =>
            PowerSeries.coeff d (PowerSeries.log K) * x ^ d)
          y := by
      simpa [y] using
        hasSum_powerSeries_log_eval_nat_logOnePlusSeriesField_ofWithZeroValuation_scaled
          (v := v) (p := p) e x hnKlog hnvalLog hvx_lt_one hcomplete
    have houterX :
        HasSum
          (fun q : ℕ => PowerSeries.coeff q (PowerSeries.exp K) * x ^ q)
          (expSeriesFieldOfWithZeroValuation v x hnKexp) :=
      hasSum_formalExpPowerSeries_eval_expSeriesField_ofWithZeroValuation_scaled
        (v := v) (p := p) e x hnKexp hnvalExp hthreshold hcomplete
    have houterY :
        HasSum
          (fun q : ℕ => PowerSeries.coeff q (PowerSeries.exp K) * y ^ q)
          (expSeriesFieldOfWithZeroValuation v y hnKexp) :=
      hasSum_formalExpPowerSeries_eval_expSeriesField_ofWithZeroValuation_scaled
        (v := v) (p := p) e y hnKexp hnvalExp hythreshold hcomplete
    have hcoeff : ∀ d : ℕ,
        v (PowerSeries.coeff d (PowerSeries.log K) * x ^ d) ≤ v x :=
      valuation_powerSeries_log_coeff_mul_pow_le_self_scaled
        (v := v) (p := p) e hnKlog hnvalLog hthreshold
    have hcomp :
        HasSum
          (fun d : ℕ =>
            PowerSeries.coeff d
                (PowerSeries.subst (PowerSeries.log K)
                  (PowerSeries.exp K)) * x ^ d)
          (expSeriesFieldOfWithZeroValuation v y hnKexp) :=
      hasSum_powerSeries_subst_coeff_mul_pow
        (PowerSeries.exp K) (PowerSeries.log K) x y
          (expSeriesFieldOfWithZeroValuation v y hnKexp)
          PowerSeries.constantCoeff_log hinner
          houterX.summable houterY hcoeff
    rw [PowerSeries.exp_subst_log_eq_one_add_X K] at hcomp
    exact hcomp.unique (hasSum_powerSeries_one_add_X_coeff_mul_pow (K := K) x)

/-- The deep exponential–logarithm equivalence, exact maximal-ideal composite:
on the sharp scaled threshold, evaluating the formal identity
`log(exp(X)) = X` gives `log(exp(x)) = x`. -/
theorem logOnePlusSeries_expSeries_sub_one_eq_self_ofWithZeroValuation_scaled_of_threshold
    [Algebra ℚ K]
    (v : _root_.Valuation K (WithZero (Multiplicative ℤ)))
    {p : ℕ} [Fact p.Prime] (e : ℕ) (x : K)
    (hnKexp : ∀ n : ℕ, (((n.factorial : ℕ) : K) ≠ 0))
    (hnvalExp : ∀ n : ℕ,
      v (((n.factorial : ℕ) : K)) =
        WithZero.exp (-((e : ℤ) * (padicValNat p n.factorial : ℤ))))
    (hnKlog : ∀ n : ℕ, (((n + 1 : ℕ) : K) ≠ 0))
    (hnvalLog : ∀ n : ℕ,
      v (((n + 1 : ℕ) : K)) =
        WithZero.exp (-((e : ℤ) * (padicValNat p (n + 1) : ℤ))))
    (hthreshold : ∀ hx : x ≠ 0,
      (e : ℝ) / ((p : ℝ) - 1) <
        ((ofWithZeroValuation v).val (Units.mk0 x hx) : ℝ))
    (hcomplete :
      letI : Valued K (WithZero (Multiplicative ℤ)) := Valued.mk' v
      CompleteSpace K) :
    logOnePlusSeriesFieldOfWithZeroValuation v
        (expSeriesFieldOfWithZeroValuation v x hnKexp - 1) hnKlog =
      x := by
  let : Valued K (WithZero (Multiplicative ℤ)) := Valued.mk' v
  let : CompleteSpace K := hcomplete
  have : NonarchimedeanRing K := nonarchimedeanRing_ofWithZeroValuation v
  let : IsAddTorsionFree K := IsAddTorsionFree.of_module_rat K
  by_cases hx : x = 0
  · subst x
    simp
  · let y : K := expSeriesFieldOfWithZeroValuation v x hnKexp - 1
    have hvx_lt_one : v x < (1 : WithZero (Multiplicative ℤ)) :=
      valuation_lt_one_ofWithZeroValuation_scaled_threshold_real
        (v := v) (p := p) e hthreshold
    have hthresholdRat :
        (e : ℚ) / ((p : ℚ) - 1) <
          ((ofWithZeroValuation v).val (Units.mk0 x hx) : ℚ) := by
      exact_mod_cast hthreshold hx
    have hvy_eq : v y = v x := by
      simpa [y] using
        valuation_expSeriesField_sub_one_eq_self_ofWithZeroValuation_scaled_of_threshold
          (v := v) (p := p) e (x := x) hx hnKexp hnvalExp
          hthresholdRat hcomplete
    have hvy_lt_one : v y < (1 : WithZero (Multiplicative ℤ)) := by
      simpa [hvy_eq] using hvx_lt_one
    have hexp :
        HasSum
          (fun d : ℕ => PowerSeries.coeff d (PowerSeries.exp K) * x ^ d)
          (expSeriesFieldOfWithZeroValuation v x hnKexp) :=
      hasSum_formalExpPowerSeries_eval_expSeriesField_ofWithZeroValuation_scaled
        (v := v) (p := p) e x hnKexp hnvalExp hthreshold hcomplete
    have hinner :
        HasSum
          (fun d : ℕ =>
            PowerSeries.coeff d ((PowerSeries.exp K) - 1) * x ^ d)
          y := by
      simpa [y] using
        hasSum_powerSeries_sub_one_coeff_mul_pow
          (PowerSeries.exp K) x
            (expSeriesFieldOfWithZeroValuation v x hnKexp) hexp
    have houterX :
        HasSum
          (fun q : ℕ =>
            PowerSeries.coeff q (PowerSeries.log K) * x ^ q)
          (logOnePlusSeriesFieldOfWithZeroValuation v x hnKlog) :=
      hasSum_powerSeries_log_eval_nat_logOnePlusSeriesField_ofWithZeroValuation_scaled
        (v := v) (p := p) e x hnKlog hnvalLog hvx_lt_one hcomplete
    have houterY :
        HasSum
          (fun q : ℕ =>
            PowerSeries.coeff q (PowerSeries.log K) * y ^ q)
          (logOnePlusSeriesFieldOfWithZeroValuation v y hnKlog) :=
      hasSum_powerSeries_log_eval_nat_logOnePlusSeriesField_ofWithZeroValuation_scaled
        (v := v) (p := p) e y hnKlog hnvalLog hvy_lt_one hcomplete
    have hcoeff : ∀ d : ℕ,
        v (PowerSeries.coeff d ((PowerSeries.exp K) - 1) * x ^ d) ≤ v x :=
      valuation_formalExp_sub_one_coeff_mul_pow_le_self_scaled
        (v := v) (p := p) e hnKexp hnvalExp hthreshold
    have hg0 :
        PowerSeries.constantCoeff ((PowerSeries.exp K) - 1) = 0 := by
      simp
    have hcomp :
        HasSum
          (fun d : ℕ =>
            PowerSeries.coeff d
                (PowerSeries.subst ((PowerSeries.exp K) - 1)
                  (PowerSeries.log K)) * x ^ d)
          (logOnePlusSeriesFieldOfWithZeroValuation v y hnKlog) :=
      hasSum_powerSeries_subst_coeff_mul_pow
        (PowerSeries.log K) ((PowerSeries.exp K) - 1) x y
          (logOnePlusSeriesFieldOfWithZeroValuation v y hnKlog)
          hg0 hinner houterX.summable houterY hcoeff
    rw [PowerSeries.log_subst_exp_sub_one_eq_X K] at hcomp
    exact hcomp.unique (hasSum_powerSeries_X_coeff_mul_pow (K := K) x)

end MultiplicativeIntegerValuation
end LocalFieldTheory.DiscreteValuationField
end
end

section
-- module Solutions.OAIQ244_DUKE.LocalField_Analytic_FieldUnitLogExtension
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.AdicPrincipalUnits.instAddCommGroup _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.AdicPrincipalUnits.instTopologicalSpace _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.DiscretePrincipalUnitQuotient.instAddCommGroup _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitInverseLimitCarrierPadicModule _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitQuotientCarrierPadicModule _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.PrincipalUnitProdiscreteLimit.instAddCommGroup _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.PrincipalUnitProdiscreteLimit.instTopologicalSpace _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitPadicModule _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitPadicSMul _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.residueFieldZModAlgebra _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.LubinTate.compatibleGroupFamiliesGroup _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.RamificationTheory.HilbertRamification.Higher.lowerRamificationGroup.instNormal _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.LocalClassFieldTheory.normalizationIntegerRingIsIntegralClosure _root_.RamificationTheory.HilbertRamification.CompleteDVF.decompositionGroupMulSemiringAction _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen
attribute [-simp] _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.IsDiscreteValuationRing.addVal_ringEquiv _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.EqualCharacteristicLaurent.coeffHom_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.EqualCharacteristicLaurent.powerSeriesEvalHom_C _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.EqualCharacteristicLaurent.powerSeriesEvalHom_X _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.EqualCharacteristicLaurent.powerSeriesEvalSubringHom_C _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.EqualCharacteristicLaurent.powerSeriesEvalSubringHom_X _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.AdicPrincipalUnits.addEquiv_map_smul _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.AdicPrincipalUnits.of_val _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.AdicPrincipalUnits.val_of _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.DiscretePrincipalUnitQuotient.addEquiv_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.DiscretePrincipalUnitQuotient.addEquiv_map_smul _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.DiscretePrincipalUnitQuotient.addEquiv_of _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.DiscretePrincipalUnitQuotient.addEquiv_symm_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.DiscretePrincipalUnitQuotient.of_val _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.DiscretePrincipalUnitQuotient.val_of _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.DiscretePrincipalUnitQuotient.val_transition _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.adicPrincipalUnitsHomeomorphUnderlying_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.iwasawaGlobalInverseLimitCarrier_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitAddEquivInverseLimitCarrier_map_smul _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitAddHomeomorphInverseLimitCarrier_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitInverseLimitCarrierEval_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitInverseLimitCarrierPadic_smul_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitMulEquivInverseLimitCarrier_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitPadic_smul_carrier_coordinate _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitProdiscreteLimitHomeomorphUnderlying_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitQuotientCarrierPadicScalar_eq_smul _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitQuotientCarrierToFull_mk _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitQuotientCarrierTransition_mk _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.uniformizerHigherUnitQuotientEquiv_mk _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.PrincipalUnitProdiscreteLimit.addEquiv_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.PrincipalUnitProdiscreteLimit.addEquiv_map_smul _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.PrincipalUnitProdiscreteLimit.addEquiv_symm_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.PrincipalUnitProdiscreteLimit.coordinate_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.PrincipalUnitProdiscreteLimit.of_val _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.PrincipalUnitProdiscreteLimit.val_of _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.adicPrincipalUnitsContinuousAddEquivUnderlyingOfWithZeroValuation_map_smul _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.adicPrincipalUnitsHomeomorphProdiscreteLimit_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.adicPrincipalUnitsHomeomorphProdiscreteLimit_to_addEquiv _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.iwasawaDegreeTerm_zero _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.iwasawaGn_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.iwasawaPartialProduct_zero_input _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.iwasawaSeedAtLevel_val _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.iwasawaSeedIdeal_val _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.iwasawaSeed_val _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitPadic_natCast_smul _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitPadic_nsmul_eq_pow _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitPadic_smul_def _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitSuccQuotAddEquivResidue_iwasawaSeed _root_.LocalFieldTheory.DiscreteValuationField.LocalField.laurentSeriesEquivLaurentImageSubfield_apply_coe _root_.LocalFieldTheory.DiscreteValuationField.MultiplicativeIntegerValuation.principalUnitLogSeriesHomOfWithZeroValuationScaled_apply_toAdd _root_.LocalFieldTheory.localIntegerValuationSubringEquiv_apply_coe _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.LocalFieldTheory.residueField_algebraMap_residue _root_.LubinTate.LubinTateSeries.standardLubinTateSeries_toPowerSeries _root_.LubinTate.SameUniformizer.coeff_recursiveIntertwiner _root_.LubinTate.SameUniformizer.constantCoeff_inVariable _root_.LubinTate.SameUniformizer.intertwinerApproximation_zero _root_.LubinTate.SameUniformizer.standardLubinTateEndomorphism_coeff_one _root_.LubinTate.standardLubinTateBaseUniformizerUnit_coe _root_.LubinTate.standardLubinTateChangedUniformizerUnit_coe _root_.LubinTate.standardLubinTateLevelGenerator_coe _root_.LubinTate.standardLubinTatePolynomialIterateOverSeparableClosure_eval _root_.LubinTate.standardLubinTatePolynomialIterate_derivative_eval_zero _root_.LubinTate.standardLubinTatePolynomialIterate_eval_zero _root_.LubinTate.standardLubinTatePolynomialIterate_zero _root_.LubinTate.standardLubinTatePolynomial_derivative_eval_zero _root_.LubinTate.standardLubinTatePolynomial_eval _root_.LubinTate.standardLubinTatePolynomial_toPowerSeries _root_.LubinTate.standardLubinTatePolynomial_toPowerSeries_eq_series _root_.LubinTate.standardLubinTatePrimitivePointInteger_coe _root_.LubinTate.standardLubinTatePrimitivePolynomialOverField_coeff_zero _root_.LubinTate.standardLubinTatePrimitivePolynomial_coeff_zero _root_.LubinTate.standardLubinTateUnitFactorFieldUnit_coe _root_.OAI.PrimeDegreePackets.ThetaConstruction.schwartzCM_apply _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteResidueActionOfHenselianDVF_apply _root_.RamificationTheory.HilbertRamification.Higher.dvfValuationSubringUnitAut_apply _root_.RamificationTheory.HilbertRamification.Higher.lowerRamificationGroup_neg_one _root_.RamificationTheory.HilbertRamification.Higher.mem_dvfHigherPrincipalUnitGroup_iff _root_.RamificationTheory.HilbertRamification.Higher.mem_lowerRamificationGroup_iff _root_.RamificationTheory.HilbertRamification.Higher.mem_valuationSubringDisplacementSubalgebraOfUniqueExtension_iff _root_.RamificationTheory.HilbertRamification.Higher.realRamificationIdeal_nat _root_.RamificationTheory.HilbertRamification.Higher.realRamificationIdeal_neg_one _root_.RamificationTheory.HilbertRamification.Higher.valuationSubringAutOfUniqueExtension_apply_coe _root_.RamificationTheory.HilbertRamification.Higher.valuationSubringAutOfUniqueExtension_apply_inv_apply _root_.RamificationTheory.HilbertRamification.Higher.valuationSubringAutOfUniqueExtension_mul_apply _root_.RamificationTheory.HilbertRamification.Higher.valuationSubringAutOfUniqueExtension_one_apply _root_.infinitePlace_mult_smul
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

/-!
# Extending the logarithm to the field-unit group

The logarithm on first principal units does not extend by killing a chosen
uniformizer.  Its uniformizer value must instead be chosen so that the
distinguished rational prime has logarithm zero.  This file isolates that
algebraic construction.
-/

noncomputable section

universe u

open ValuationTheory.DiscreteValuationField
open LocalFieldTheory.DiscreteValuationField

namespace LocalFieldTheory.DiscreteValuationField
namespace MultiplicativeIntegerValuation

variable {K : Type u} [Field K]

/-- Extend a homomorphism on first principal units to the three factors in
the uniformizer–residue–principal-unit decomposition, killing the residue-root factor and assigning the additive
value `c` to one power of the chosen uniformizer. -/
noncomputable def fieldUnitDecompositionLogHomWithUniformizerValue
    (F : CompleteDVF K) [Finite F.residueField]
    {A : Type*} [AddCommGroup A]
    (φ : (LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup F) 1 →* Multiplicative A) (c : A) :
    CompleteDVF.higherPrincipalUnitGroup.fieldUnitDecompositionFactors F →*
      Multiplicative A where
  toFun z :=
    φ z.1.2 * Multiplicative.ofAdd (Multiplicative.toAdd z.2 • c)
  map_one' := by simp
  map_mul' z w := by
    apply Multiplicative.toAdd.injective
    change
      Multiplicative.toAdd (φ (z.1.2 * w.1.2)) +
          (Multiplicative.toAdd z.2 + Multiplicative.toAdd w.2) • c =
        (Multiplicative.toAdd (φ z.1.2) + Multiplicative.toAdd z.2 • c) +
          (Multiplicative.toAdd (φ w.1.2) + Multiplicative.toAdd w.2 • c)
    rw [φ.map_mul]
    simp only [toAdd_mul, add_zsmul]
    abel

/--
The defining evaluation formula for `fieldUnitDecompositionLogHomWithUniformizerValue` is
`fieldUnitDecompositionLogHomWithUniformizerValue F φ c z = φ z.1.2 * Multiplicative.ofAdd
(Multiplicative.toAdd z.2 • c)`.
-/
@[simp] theorem fieldUnitDecompositionLogHomWithUniformizerValue_apply
    (F : CompleteDVF K) [Finite F.residueField]
    {A : Type*} [AddCommGroup A]
    (φ : (LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup F) 1 →* Multiplicative A) (c : A)
    (z : CompleteDVF.higherPrincipalUnitGroup.fieldUnitDecompositionFactors F) :
    fieldUnitDecompositionLogHomWithUniformizerValue F φ c z =
      φ z.1.2 * Multiplicative.ofAdd (Multiplicative.toAdd z.2 • c) :=
  rfl

/--
Establishes the identity `fieldUnitDecompositionLogHomWithUniformizerValue F φ c ((ζ, 1), (1 :
Multiplicative ℤ)) = 1`.
-/
@[simp] theorem fieldUnitDecompositionLogHomWithUniformizerValue_root
    (F : CompleteDVF K) [Finite F.residueField]
    {A : Type*} [AddCommGroup A]
    (φ : (LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup F) 1 →* Multiplicative A) (c : A)
    (ζ : CompleteDVF.higherPrincipalUnitGroup.residueRootsOfUnityGroup F) :
    fieldUnitDecompositionLogHomWithUniformizerValue F φ c
        ((ζ, 1), (1 : Multiplicative ℤ)) = 1 := by
  simp

/--
Establishes the identity `fieldUnitDecompositionLogHomWithUniformizerValue F φ c (((1 :
CompleteDVF.higherPrincipalUnitGroup.residueRootsOfUnityGroup F), u), (1 : Multiplicative ℤ)) = φ
u`.
-/
@[simp] theorem fieldUnitDecompositionLogHomWithUniformizerValue_principal
    (F : CompleteDVF K) [Finite F.residueField]
    {A : Type*} [AddCommGroup A]
    (φ : (LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup F) 1 →* Multiplicative A) (c : A)
    (u : (LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup F) 1) :
    fieldUnitDecompositionLogHomWithUniformizerValue F φ c
        (((1 : CompleteDVF.higherPrincipalUnitGroup.residueRootsOfUnityGroup F), u),
          (1 : Multiplicative ℤ)) = φ u := by
  simp

/--
Establishes the identity `fieldUnitDecompositionLogHomWithUniformizerValue F φ c (((1 :
CompleteDVF.higherPrincipalUnitGroup.residueRootsOfUnityGroup F), (1 :
(CompleteDVF.higherPrincipalUnitGroup F) 1)), Multiplicative.ofAdd m) = Multiplicative.ofAdd (m •
c)`.
-/
@[simp] theorem fieldUnitDecompositionLogHomWithUniformizerValue_uniformizer
    (F : CompleteDVF K) [Finite F.residueField]
    {A : Type*} [AddCommGroup A]
    (φ : (LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup F) 1 →* Multiplicative A) (c : A)
    (m : ℤ) :
    fieldUnitDecompositionLogHomWithUniformizerValue F φ c
        (((1 : CompleteDVF.higherPrincipalUnitGroup.residueRootsOfUnityGroup F),
            (1 : (LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup F) 1)),
          Multiplicative.ofAdd m) = Multiplicative.ofAdd (m • c) := by
  simp

/-- Transport the corrected factor logarithm across a chosen the uniformizer–residue–principal-unit decomposition
decomposition of the field-unit group. -/
noncomputable def fieldUnitLogHomWithUniformizerValue
    (F : CompleteDVF K) [Finite F.residueField]
    {A : Type*} [AddCommGroup A]
    (d : CompleteDVF.higherPrincipalUnitGroup.fieldUnitDecompositionFactors F ≃* Kˣ)
    (φ : (LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup F) 1 →* Multiplicative A) (c : A) :
    Kˣ →* Multiplicative A :=
  (fieldUnitDecompositionLogHomWithUniformizerValue F φ c).comp
    d.symm.toMonoidHom

/--
The defining evaluation formula for `fieldUnitLogHomWithUniformizerValue` is
`fieldUnitLogHomWithUniformizerValue F d φ c x = φ (d.symm x).1.2 * Multiplicative.ofAdd
(Multiplicative.toAdd (d.symm x).2 • c)`.
-/
@[simp] theorem fieldUnitLogHomWithUniformizerValue_apply
    (F : CompleteDVF K) [Finite F.residueField]
    {A : Type*} [AddCommGroup A]
    (d : CompleteDVF.higherPrincipalUnitGroup.fieldUnitDecompositionFactors F ≃* Kˣ)
    (φ : (LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup F) 1 →* Multiplicative A) (c : A) (x : Kˣ) :
    fieldUnitLogHomWithUniformizerValue F d φ c x =
      φ (d.symm x).1.2 *
        Multiplicative.ofAdd (Multiplicative.toAdd (d.symm x).2 • c) :=
  rfl

end MultiplicativeIntegerValuation
end LocalFieldTheory.DiscreteValuationField
end
end

section
-- module Solutions.OAIQ244_DUKE.LocalField_Analytic_LogExpContinuity
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_isCompleteDiscrete _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.DiscreteNthRootsSubgroup.instTopologicalSpaceSubtypeUnitsMemSubgroup _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.AdicPrincipalUnits.instAddCommGroup _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.AdicPrincipalUnits.instTopologicalSpace _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.DiscretePrincipalUnitQuotient.instAddCommGroup _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitInverseLimitCarrierPadicModule _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitQuotientCarrierPadicModule _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.PrincipalUnitProdiscreteLimit.instAddCommGroup _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.PrincipalUnitProdiscreteLimit.instTopologicalSpace _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitPadicModule _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitPadicSMul _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.residueFieldZModAlgebra _root_.LocalFieldTheory.DiscreteValuationField.Examples.Qp.padicDVRValuation_isRankOneDiscrete _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.LubinTate.compatibleGroupFamiliesGroup _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.RamificationTheory.HilbertRamification.Higher.lowerRamificationGroup.instNormal _root_.RamificationTheory.HilbertRamification.ValuationSubring.selectedResidueField.instAlgebra _root_.RayClass.approximationCompletionTopologicalSpace _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.LocalClassFieldTheory.normalizationIntegerRingIsIntegralClosure _root_.RamificationTheory.HilbertRamification.CompleteDVF.decompositionGroupMulSemiringAction _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen _root_.relativeAdeleRingIntermediateAlgebra _root_.relativeAdeleRingTopIntermediateAlgebra
attribute [-simp] _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.IsDiscreteValuationRing.addVal_ringEquiv _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.EqualCharacteristicLaurent.coeffHom_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.EqualCharacteristicLaurent.powerSeriesEvalHom_C _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.EqualCharacteristicLaurent.powerSeriesEvalHom_X _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.EqualCharacteristicLaurent.powerSeriesEvalSubringHom_C _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.EqualCharacteristicLaurent.powerSeriesEvalSubringHom_X _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.AdicPrincipalUnits.addEquiv_map_smul _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.AdicPrincipalUnits.of_val _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.AdicPrincipalUnits.val_of _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.DiscretePrincipalUnitQuotient.addEquiv_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.DiscretePrincipalUnitQuotient.addEquiv_map_smul _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.DiscretePrincipalUnitQuotient.addEquiv_of _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.DiscretePrincipalUnitQuotient.addEquiv_symm_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.DiscretePrincipalUnitQuotient.of_val _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.DiscretePrincipalUnitQuotient.val_of _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.DiscretePrincipalUnitQuotient.val_transition _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.adicPrincipalUnitsHomeomorphUnderlying_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.iwasawaGlobalInverseLimitCarrier_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitAddEquivInverseLimitCarrier_map_smul _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitAddHomeomorphInverseLimitCarrier_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitInverseLimitCarrierEval_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitInverseLimitCarrierPadic_smul_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitMulEquivInverseLimitCarrier_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitPadic_smul_carrier_coordinate _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitProdiscreteLimitHomeomorphUnderlying_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitQuotientCarrierPadicScalar_eq_smul _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitQuotientCarrierToFull_mk _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitQuotientCarrierTransition_mk _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.uniformizerHigherUnitQuotientEquiv_mk _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.PrincipalUnitProdiscreteLimit.addEquiv_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.PrincipalUnitProdiscreteLimit.addEquiv_map_smul _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.PrincipalUnitProdiscreteLimit.addEquiv_symm_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.PrincipalUnitProdiscreteLimit.coordinate_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.PrincipalUnitProdiscreteLimit.of_val _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.PrincipalUnitProdiscreteLimit.val_of _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.adicPrincipalUnitsContinuousAddEquivUnderlyingOfWithZeroValuation_map_smul _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.adicPrincipalUnitsHomeomorphProdiscreteLimit_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.adicPrincipalUnitsHomeomorphProdiscreteLimit_to_addEquiv _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.iwasawaDegreeTerm_zero _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.iwasawaGn_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.iwasawaPartialProduct_zero_input _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.iwasawaSeedAtLevel_val _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.iwasawaSeedIdeal_val _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.iwasawaSeed_val _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitPadic_natCast_smul _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitPadic_nsmul_eq_pow _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitPadic_smul_def _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitSuccQuotAddEquivResidue_iwasawaSeed _root_.LocalFieldTheory.DiscreteValuationField.LocalField.laurentSeriesEquivLaurentImageSubfield_apply_coe _root_.LocalFieldTheory.IsNonarchimedeanLocalField.multiplicativeIntegerValuation_val _root_.LocalFieldTheory.localIntegerValuationSubringEquiv_apply_coe _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.LocalFieldTheory.residueField_algebraMap_residue _root_.LubinTate.LubinTateSeries.standardLubinTateSeries_toPowerSeries _root_.LubinTate.SameUniformizer.coeff_recursiveIntertwiner _root_.LubinTate.SameUniformizer.constantCoeff_inVariable _root_.LubinTate.SameUniformizer.intertwinerApproximation_zero _root_.LubinTate.SameUniformizer.standardLubinTateEndomorphism_coeff_one _root_.LubinTate.standardLubinTateBaseUniformizerUnit_coe _root_.LubinTate.standardLubinTateChangedUniformizerUnit_coe _root_.LubinTate.standardLubinTateLevelGenerator_coe _root_.LubinTate.standardLubinTatePolynomialIterateOverSeparableClosure_eval _root_.LubinTate.standardLubinTatePolynomialIterate_derivative_eval_zero _root_.LubinTate.standardLubinTatePolynomialIterate_eval_zero _root_.LubinTate.standardLubinTatePolynomialIterate_zero _root_.LubinTate.standardLubinTatePolynomial_derivative_eval_zero _root_.LubinTate.standardLubinTatePolynomial_eval _root_.LubinTate.standardLubinTatePolynomial_toPowerSeries _root_.LubinTate.standardLubinTatePolynomial_toPowerSeries_eq_series _root_.LubinTate.standardLubinTatePrimitivePointInteger_coe _root_.LubinTate.standardLubinTatePrimitivePolynomialOverField_coeff_zero _root_.LubinTate.standardLubinTatePrimitivePolynomial_coeff_zero _root_.LubinTate.standardLubinTateUnitFactorFieldUnit_coe _root_.OAI.PrimeDegreePackets.ThetaConstruction.schwartzCM_apply _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteResidueActionOfHenselianDVF_apply _root_.RamificationTheory.HilbertRamification.Higher.dvfValuationSubringUnitAut_apply _root_.RamificationTheory.HilbertRamification.Higher.lowerRamificationGroup_neg_one _root_.RamificationTheory.HilbertRamification.Higher.mem_dvfHigherPrincipalUnitGroup_iff _root_.RamificationTheory.HilbertRamification.Higher.mem_lowerRamificationGroup_iff _root_.RamificationTheory.HilbertRamification.Higher.mem_valuationSubringDisplacementSubalgebraOfUniqueExtension_iff _root_.RamificationTheory.HilbertRamification.Higher.realRamificationIdeal_nat _root_.RamificationTheory.HilbertRamification.Higher.realRamificationIdeal_neg_one _root_.RamificationTheory.HilbertRamification.Higher.valuationSubringAutOfUniqueExtension_apply_coe _root_.RamificationTheory.HilbertRamification.Higher.valuationSubringAutOfUniqueExtension_apply_inv_apply _root_.RamificationTheory.HilbertRamification.Higher.valuationSubringAutOfUniqueExtension_mul_apply _root_.RamificationTheory.HilbertRamification.Higher.valuationSubringAutOfUniqueExtension_one_apply _root_.infinitePlace_mult_smul
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

/-!
# Topology of exponential and logarithm

This file supplies the topological part of the deep exponential–logarithm equivalence at the sharp
ramified endpoint `n > e / (p - 1)`.  The algebraic construction of the maps is supplied by the preceding modules;
here we prove that the endpoint
exponential and logarithm maps are continuous for the valuation topology.
-/

noncomputable section

universe u

namespace LocalFieldTheory.DiscreteValuationField
namespace MultiplicativeIntegerValuation

open Filter
open WithZeroValuation
open scoped Topology

variable {K : Type u} [Field K]

/-- The endpoint exponential of the deep exponential–logarithm equivalence, as a homomorphism from the
additive ideal (written multiplicatively) to the higher principal units. -/
noncomputable def principalUnitExpSeriesHomOfMaximalIdealPowOfWithZeroValuationScaled
    [Algebra ℚ K]
    (v : _root_.Valuation K (WithZero (Multiplicative ℤ)))
    [ValuationTheory.DiscreteValuationField.Valuation.IsCompleteDiscrete v]
    {p : ℕ} [Fact p.Prime] (e n : ℕ)
    {π : (completeDVFOfWithZeroValuation v).valuationSubring}
    (hπval : v (π : K) = WithZero.exp (-1 : ℤ))
    (hn : 1 ≤ n)
    (hlevel : (e : ℚ) / ((p : ℚ) - 1) < (n : ℚ))
    (hnK : ∀ m : ℕ, (((m.factorial : ℕ) : K) ≠ 0))
    (hnval : ∀ m : ℕ,
      v (((m.factorial : ℕ) : K)) =
        WithZero.exp (-((e : ℤ) * (padicValNat p m.factorial : ℤ))))
    (hcomplete :
      letI : Valued K (WithZero (Multiplicative ℤ)) := Valued.mk' v
      CompleteSpace K) :
    Multiplicative
      ((completeDVFOfWithZeroValuation v).maximalIdeal ^ n :
        Ideal (completeDVFOfWithZeroValuation v).valuationSubring) →*
      LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup (completeDVFOfWithZeroValuation v) n := by
  let hπ : v.IsUniformizer (π : K) :=
    isUniformizer_of_valuation_eq_exp_neg_one v (π : K) hπval
  exact
    { toFun := fun a =>
        principalUnitExpSeriesOfMaximalIdealPowOfWithZeroValuationScaled
          (v := v) (p := p) e n (π := π) hπ hπval hn hlevel
          hnK hnval hcomplete a.toAdd
      map_one' := by
        apply Subtype.ext
        apply Units.ext
        apply Subtype.ext
        simp [principalUnitExpSeriesOfMaximalIdealPowOfWithZeroValuationScaled]
      map_mul' := by
        intro a b
        simpa using
          principalUnitExpSeries_maximalIdealPow_add_eq_mul_ofWithZeroValuationScaled
            (v := v) (p := p) e n (π := π) hπ hπval hn hlevel
            hnK hnval hcomplete a.toAdd b.toAdd }

/--
The defining evaluation formula for `principalUnitExpSeriesHomOfMaximalIdealPow` is
`principalUnitExpSeriesHomOfMaximalIdealPowOfWithZeroValuationScaled (v := v) (p := p) e n (π :=
π) hπval hn hlevel hnK hnval hcomplete a =
principalUnitExpSeriesOfMaximalIdealPowOfWithZeroValuationScaled (v := v) (p := p) e n (π := π)
(isUniformizer_of_valuation_eq_exp_neg_one v (π : K) hπval) hπval hn hlevel hnK hnval hcomplete
a.toAdd`.
-/
@[simp] theorem principalUnitExpSeriesHomOfMaximalIdealPow_apply
    [Algebra ℚ K]
    (v : _root_.Valuation K (WithZero (Multiplicative ℤ)))
    [ValuationTheory.DiscreteValuationField.Valuation.IsCompleteDiscrete v]
    {p : ℕ} [Fact p.Prime] (e n : ℕ)
    {π : (completeDVFOfWithZeroValuation v).valuationSubring}
    (hπval : v (π : K) = WithZero.exp (-1 : ℤ))
    (hn : 1 ≤ n)
    (hlevel : (e : ℚ) / ((p : ℚ) - 1) < (n : ℚ))
    (hnK : ∀ m : ℕ, (((m.factorial : ℕ) : K) ≠ 0))
    (hnval : ∀ m : ℕ,
      v (((m.factorial : ℕ) : K)) =
        WithZero.exp (-((e : ℤ) * (padicValNat p m.factorial : ℤ))))
    (hcomplete :
      letI : Valued K (WithZero (Multiplicative ℤ)) := Valued.mk' v
      CompleteSpace K)
    (a : Multiplicative
      ((completeDVFOfWithZeroValuation v).maximalIdeal ^ n :
        Ideal (completeDVFOfWithZeroValuation v).valuationSubring)) :
    principalUnitExpSeriesHomOfMaximalIdealPowOfWithZeroValuationScaled
        (v := v) (p := p) e n (π := π) hπval hn hlevel
        hnK hnval hcomplete a =
      principalUnitExpSeriesOfMaximalIdealPowOfWithZeroValuationScaled
        (v := v) (p := p) e n (π := π)
        (isUniformizer_of_valuation_eq_exp_neg_one v (π : K) hπval)
        hπval hn hlevel
        hnK hnval hcomplete a.toAdd :=
  rfl

/-- The field value of the endpoint exponential is continuous at the origin.
The proof is the valuation estimate `v(Exp(a) - 1) = v(a)`: membership in `m^n`
puts every nonzero `a` above the ramified convergence threshold. -/
theorem continuousAt_zero_principalUnitExpSeries_maximalIdealPow_fieldVal_ofWithZeroValuationScaled
    [Algebra ℚ K]
    (v : _root_.Valuation K (WithZero (Multiplicative ℤ)))
    [ValuationTheory.DiscreteValuationField.Valuation.IsCompleteDiscrete v]
    {p : ℕ} [Fact p.Prime] (e n : ℕ)
    {π : (completeDVFOfWithZeroValuation v).valuationSubring}
    (hπval : v (π : K) = WithZero.exp (-1 : ℤ))
    (hn : 1 ≤ n)
    (hlevel : (e : ℚ) / ((p : ℚ) - 1) < (n : ℚ))
    (hnK : ∀ m : ℕ, (((m.factorial : ℕ) : K) ≠ 0))
    (hnval : ∀ m : ℕ,
      v (((m.factorial : ℕ) : K)) =
        WithZero.exp (-((e : ℤ) * (padicValNat p m.factorial : ℤ))))
    (hcomplete :
      letI : Valued K (WithZero (Multiplicative ℤ)) := Valued.mk' v
      CompleteSpace K) :
    letI : Valued K (WithZero (Multiplicative ℤ)) := Valued.mk' v
    ContinuousAt
      (fun a :
          ((completeDVFOfWithZeroValuation v).maximalIdeal ^ n :
            Ideal (completeDVFOfWithZeroValuation v).valuationSubring) =>
        ((((principalUnitExpSeriesOfMaximalIdealPowOfWithZeroValuationScaled
            (v := v) (p := p) e n (π := π)
            (isUniformizer_of_valuation_eq_exp_neg_one v (π : K) hπval)
            hπval hn hlevel
            hnK hnval hcomplete a :
          LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup (completeDVFOfWithZeroValuation v) n) :
          (completeDVFOfWithZeroValuation v).valuationSubringˣ) :
          (completeDVFOfWithZeroValuation v).valuationSubring) : K))
      0 := by
  let : Valued K (WithZero (Multiplicative ℤ)) := Valued.mk' v
  let hπ : v.IsUniformizer (π : K) :=
    isUniformizer_of_valuation_eq_exp_neg_one v (π : K) hπval
  let F : ValuationTheory.DiscreteValuationField.CompleteDVF.{u, 0} K := completeDVFOfWithZeroValuation v
  let E :=
    principalUnitExpSeriesOfMaximalIdealPowOfWithZeroValuationScaled
      (v := v) (p := p) e n (π := π) hπ hπval hn hlevel
      hnK hnval hcomplete
  have hcoe : Continuous
      (fun a : (F.maximalIdeal ^ n : Ideal F.valuationSubring) =>
        ((a : F.valuationSubring) : K)) :=
    continuous_subtype_val.comp continuous_subtype_val
  have hEzero : ((((E 0 : LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup F n) :
      F.valuationSubringˣ) : F.valuationSubring) : K) = 1 := by
    simp [E, principalUnitExpSeriesOfMaximalIdealPowOfWithZeroValuationScaled]
  rw [ContinuousAt, Filter.tendsto_def]
  intro s hs
  rw [hEzero, Valued.mem_nhds] at hs
  obtain ⟨γ, hγ⟩ := hs
  have hball : {x : K |
      v x < MonoidWithZeroHom.ValueGroup₀.embedding γ.1} ∈
      𝓝 (0 : K) := by
    apply Valued.mem_nhds_zero.mpr
    exact ⟨γ, by
      intro x hx
      change v.restrict x < γ.1 at hx
      rw [Valuation.restrict_lt_iff_lt_embedding] at hx
      exact hx⟩
  have hpre :
      {a : (F.maximalIdeal ^ n : Ideal F.valuationSubring) |
        v (((a : F.valuationSubring) : K)) <
          MonoidWithZeroHom.ValueGroup₀.embedding γ.1} ∈ 𝓝 0 := by
    have ht := (hcoe.tendsto
      (0 : (F.maximalIdeal ^ n : Ideal F.valuationSubring))) hball
    simpa using ht
  refine Filter.mem_of_superset hpre ?_
  intro a ha
  change v (((a : F.valuationSubring) : K)) <
    MonoidWithZeroHom.ValueGroup₀.embedding γ.1 at ha
  apply hγ
  change v.restrict
    (((((E a : LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup F n) :
      F.valuationSubringˣ) : F.valuationSubring) : K) - 1) < γ.1
  rw [Valuation.restrict_lt_iff_lt_embedding]
  let x : K := ((a : F.valuationSubring) : K)
  by_cases hx : x = 0
  · simpa [E, principalUnitExpSeriesOfMaximalIdealPowOfWithZeroValuationScaled,
      x, hx] using
        (MonoidWithZeroHom.ValueGroup₀.embedding_unit_pos γ)
  · have hge :
        (n : ℤ) ≤ (ofWithZeroValuation v).val (Units.mk0 x hx) := by
      simpa [F, x] using
        ofWithZeroValuation_val_ge_of_mem_maximalIdeal_pow
          (v := v) (π := π) hπ hπval n
          (a := (a : F.valuationSubring)) a.property hx
    have hthreshold :
        (e : ℚ) / ((p : ℚ) - 1) <
          ((ofWithZeroValuation v).val (Units.mk0 x hx) : ℚ) :=
      lt_of_lt_of_le hlevel (by exact_mod_cast hge)
    have hv :=
      valuation_expSeriesField_sub_one_eq_self_ofWithZeroValuation_scaled_of_threshold
        (v := v) (p := p) e (x := x) hx hnK hnval hthreshold hcomplete
    rw [principalUnitExpSeries_maximalIdealPow_val_ofWithZeroValuationScaled,
      hv]
    simpa [x] using ha

/-- The field value of the endpoint exponential is continuous everywhere.
Translation in `m^n`, exponential additivity, and continuity of multiplication
reduce this to the preceding continuity statement at zero. -/
theorem continuous_principalUnitExpSeries_maximalIdealPow_fieldVal_ofWithZeroValuationScaled
    [Algebra ℚ K]
    (v : _root_.Valuation K (WithZero (Multiplicative ℤ)))
    [ValuationTheory.DiscreteValuationField.Valuation.IsCompleteDiscrete v]
    {p : ℕ} [Fact p.Prime] (e n : ℕ)
    {π : (completeDVFOfWithZeroValuation v).valuationSubring}
    (hπval : v (π : K) = WithZero.exp (-1 : ℤ))
    (hn : 1 ≤ n)
    (hlevel : (e : ℚ) / ((p : ℚ) - 1) < (n : ℚ))
    (hnK : ∀ m : ℕ, (((m.factorial : ℕ) : K) ≠ 0))
    (hnval : ∀ m : ℕ,
      v (((m.factorial : ℕ) : K)) =
        WithZero.exp (-((e : ℤ) * (padicValNat p m.factorial : ℤ))))
    (hcomplete :
      letI : Valued K (WithZero (Multiplicative ℤ)) := Valued.mk' v
      CompleteSpace K) :
    letI : Valued K (WithZero (Multiplicative ℤ)) := Valued.mk' v
    Continuous
      (fun a :
          ((completeDVFOfWithZeroValuation v).maximalIdeal ^ n :
            Ideal (completeDVFOfWithZeroValuation v).valuationSubring) =>
        ((((principalUnitExpSeriesOfMaximalIdealPowOfWithZeroValuationScaled
            (v := v) (p := p) e n (π := π)
            (isUniformizer_of_valuation_eq_exp_neg_one v (π : K) hπval)
            hπval hn hlevel
            hnK hnval hcomplete a :
          LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup (completeDVFOfWithZeroValuation v) n) :
          (completeDVFOfWithZeroValuation v).valuationSubringˣ) :
          (completeDVFOfWithZeroValuation v).valuationSubring) : K)) := by
  let : Valued K (WithZero (Multiplicative ℤ)) := Valued.mk' v
  let hπ : v.IsUniformizer (π : K) :=
    isUniformizer_of_valuation_eq_exp_neg_one v (π : K) hπval
  let F : ValuationTheory.DiscreteValuationField.CompleteDVF.{u, 0} K := completeDVFOfWithZeroValuation v
  let E :=
    principalUnitExpSeriesOfMaximalIdealPowOfWithZeroValuationScaled
      (v := v) (p := p) e n (π := π) hπ hπval hn hlevel
      hnK hnval hcomplete
  let f : (F.maximalIdeal ^ n : Ideal F.valuationSubring) → K :=
    fun a => ((((E a : LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup F n) :
      F.valuationSubringˣ) : F.valuationSubring) : K)
  have hzero : ContinuousAt f 0 := by
    simpa [F, E, f] using
      continuousAt_zero_principalUnitExpSeries_maximalIdealPow_fieldVal_ofWithZeroValuationScaled
        (v := v) (p := p) e n (π := π) hπval hn hlevel
        hnK hnval hcomplete
  rw [continuous_iff_continuousAt]
  intro a
  have hshiftContinuous : Continuous
      (fun b : (F.maximalIdeal ^ n : Ideal F.valuationSubring) => b - a) := by
    apply Continuous.subtype_mk
    apply Continuous.subtype_mk
    exact
      (continuous_subtype_val.comp continuous_subtype_val).sub
        continuous_const
  have hshift : ContinuousAt
      (fun b : (F.maximalIdeal ^ n : Ideal F.valuationSubring) => b - a) a :=
    hshiftContinuous.continuousAt
  have hshiftExp : ContinuousAt (fun b => f (b - a)) a :=
    hzero.comp_of_eq hshift (sub_self a)
  have htranslated : ContinuousAt (fun b => f a * f (b - a)) a :=
    continuousAt_const.mul hshiftExp
  convert htranslated using 1
  all_goals try with_reducible_and_instances rfl
  funext b
  have hadd :=
    principalUnitExpSeries_maximalIdealPow_add_eq_mul_ofWithZeroValuationScaled
      (v := v) (p := p) e n (π := π) hπ hπval hn hlevel
      hnK hnval hcomplete a (b - a)
  have hfield := congrArg
    (fun u : LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup F n =>
      ((((u : F.valuationSubringˣ) : F.valuationSubring) : K))) hadd
  simpa [f, E, add_sub_cancel_right] using hfield

end MultiplicativeIntegerValuation
end LocalFieldTheory.DiscreteValuationField
end
end

section
-- module Solutions.OAIQ244_DUKE.LocalField_DiscreteValuationField_PadicField
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_isCompleteDiscrete _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.AdicPrincipalUnits.instAddCommGroup _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.AdicPrincipalUnits.instTopologicalSpace _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.DiscretePrincipalUnitQuotient.instAddCommGroup _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitInverseLimitCarrierPadicModule _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitQuotientCarrierPadicModule _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.PrincipalUnitProdiscreteLimit.instAddCommGroup _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.PrincipalUnitProdiscreteLimit.instTopologicalSpace _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitPadicModule _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitPadicSMul _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.LubinTate.Valuations.exponentialValuationSubringIsLocalRing _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionFixedSubring.instIsLocalRing _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionResidueField.instField _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.LocalClassFieldTheory.normalizationIntegerRingIsIntegralClosure _root_.RamificationTheory.HilbertRamification.CompleteDVF.decompositionGroupMulSemiringAction _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen
attribute [-simp] _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.IsDiscreteValuationRing.addVal_ringEquiv _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.EqualCharacteristicLaurent.coeffHom_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.EqualCharacteristicLaurent.powerSeriesEvalHom_C _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.EqualCharacteristicLaurent.powerSeriesEvalHom_X _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.EqualCharacteristicLaurent.powerSeriesEvalSubringHom_C _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.EqualCharacteristicLaurent.powerSeriesEvalSubringHom_X _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.AdicPrincipalUnits.addEquiv_map_smul _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.AdicPrincipalUnits.val_of _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.DiscretePrincipalUnitQuotient.addEquiv_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.DiscretePrincipalUnitQuotient.addEquiv_map_smul _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.DiscretePrincipalUnitQuotient.addEquiv_of _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.DiscretePrincipalUnitQuotient.addEquiv_symm_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.DiscretePrincipalUnitQuotient.val_transition _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.adicPrincipalUnitsHomeomorphUnderlying_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.iwasawaGlobalInverseLimitCarrier_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitAddEquivInverseLimitCarrier_map_smul _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitAddHomeomorphInverseLimitCarrier_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitInverseLimitCarrierEval_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitInverseLimitCarrierPadic_smul_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitMulEquivInverseLimitCarrier_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitPadic_smul_carrier_coordinate _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitProdiscreteLimitHomeomorphUnderlying_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitQuotientCarrierPadicScalar_eq_smul _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitQuotientCarrierToFull_mk _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitQuotientCarrierTransition_mk _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.uniformizerHigherUnitQuotientEquiv_mk _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.PrincipalUnitProdiscreteLimit.addEquiv_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.PrincipalUnitProdiscreteLimit.addEquiv_map_smul _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.PrincipalUnitProdiscreteLimit.addEquiv_symm_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.PrincipalUnitProdiscreteLimit.coordinate_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.adicPrincipalUnitsContinuousAddEquivUnderlyingOfWithZeroValuation_map_smul _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.adicPrincipalUnitsHomeomorphProdiscreteLimit_to_addEquiv _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.iwasawaDegreeTerm_zero _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.iwasawaGn_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.iwasawaPartialProduct_zero_input _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.iwasawaSeedAtLevel_val _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.iwasawaSeedIdeal_val _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.iwasawaSeed_val _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitPadic_natCast_smul _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitPadic_nsmul_eq_pow _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitPadic_smul_def _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitSuccQuotAddEquivResidue_iwasawaSeed _root_.LocalFieldTheory.DiscreteValuationField.LocalField.laurentSeriesEquivLaurentImageSubfield_apply_coe _root_.LocalFieldTheory.DiscreteValuationField.MultiplicativeIntegerValuation.fieldUnitDecompositionLogHomWithUniformizerValue_apply _root_.LocalFieldTheory.DiscreteValuationField.MultiplicativeIntegerValuation.fieldUnitDecompositionLogHomWithUniformizerValue_principal _root_.LocalFieldTheory.DiscreteValuationField.MultiplicativeIntegerValuation.fieldUnitDecompositionLogHomWithUniformizerValue_root _root_.LocalFieldTheory.DiscreteValuationField.MultiplicativeIntegerValuation.fieldUnitDecompositionLogHomWithUniformizerValue_uniformizer _root_.LocalFieldTheory.DiscreteValuationField.MultiplicativeIntegerValuation.fieldUnitLogHomWithUniformizerValue_apply _root_.LocalFieldTheory.DiscreteValuationField.MultiplicativeIntegerValuation.principalUnitExpSeriesHomOfMaximalIdealPow_apply _root_.LocalFieldTheory.DiscreteValuationField.MultiplicativeIntegerValuation.principalUnitLogSeriesHomOfWithZeroValuationScaled_apply_toAdd _root_.LocalFieldTheory.localIntegerValuationSubringEquiv_apply_coe _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.LocalFieldTheory.residueField_algebraMap_residue _root_.OAI.PrimeDegreePackets.ThetaConstruction.schwartzCM_apply _root_.infinitePlace_mult_smul
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

/-!
# The concrete p-adic field `ℚ_[p]`

This file is the first concrete example leaf for the DVF navigation library.
It deliberately uses mathlib's public p-adic objects directly in theorem
statements instead of introducing public aliases for `ℚ_[p]` or its unit group.
-/

noncomputable section

namespace LocalFieldTheory.DiscreteValuationField
namespace Examples
namespace Qp

open Filter
open scoped Topology
open scoped WithZero

open ValuationTheory.DiscreteValuationField
open LocalFieldTheory.DiscreteValuationField

/-- The standard `p`-adic valuation is complete as a discrete valuation. -/
instance padicDVRValuation_isCompleteDiscrete
    (p : ℕ) [Fact p.Prime] :
    Valuation.IsCompleteDiscrete (padicDVRValuation p) where
  isAdicComplete := padicDVRValuation_isAdicComplete p

/-- The concrete complete-DVF package for the `p`-adic field `ℚ_[p]`. -/
noncomputable def padicCompleteDVF
    (p : ℕ) [Fact p.Prime] :
    CompleteDVF ℚ_[p] where
  ValueGroup := ℤᵐ⁰
  valuation := padicDVRValuation p
  instCompleteDiscrete := inferInstance

/-- The residue field of the complete-DVF package on `ℚ_[p]` is finite. -/
theorem padicCompleteDVF_residueField_finite
    (p : ℕ) [Fact p.Prime] :
    Finite (padicCompleteDVF p).residueField := by
  let e : ℤ_[p] ≃+* (padicDVRValuation p).valuationSubring :=
    padicIntEquivValuationSubring p
  let : Finite (IsLocalRing.ResidueField ℤ_[p]) :=
    padicInt_residueField_finite p
  have hfiniteVal :
      Finite (IsLocalRing.ResidueField
        (padicDVRValuation p).valuationSubring) :=
    Finite.of_equiv (IsLocalRing.ResidueField ℤ_[p])
      (IsLocalRing.ResidueField.mapEquiv e)
  simpa [padicCompleteDVF, CompleteDVF.residueField,
    CompleteDVF.valuationSubring, CompleteDVF.toDVF] using hfiniteVal

/-- The residue field of the concrete complete-DVF package on `ℚ_[p]` has
cardinality exactly `p`. -/
theorem padicCompleteDVF_residueField_card
    (p : ℕ) [Fact p.Prime] :
    Nat.card (padicCompleteDVF p).residueField = p := by
  let eO : ℤ_[p] ≃+* (padicDVRValuation p).valuationSubring :=
    padicIntEquivValuationSubring p
  let eRes :
      IsLocalRing.ResidueField (padicDVRValuation p).valuationSubring ≃+*
        ZMod p :=
    (IsLocalRing.ResidueField.mapEquiv eO).symm.trans
      (padicIntResidueFieldEquivZMod p)
  change
    Nat.card
        (IsLocalRing.ResidueField
          (padicDVRValuation p).valuationSubring) =
      p
  calc
    Nat.card
        (IsLocalRing.ResidueField
          (padicDVRValuation p).valuationSubring) =
        Nat.card (ZMod p) :=
      Nat.card_congr eRes.toEquiv
    _ = p := Nat.card_zmod p

end Qp
end Examples
end LocalFieldTheory.DiscreteValuationField

end
end

section
-- module Solutions.OAIQ244_DUKE.LocalField_DiscreteValuationField_MixedCharacteristicStructure_IntegralLattice
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.DiscreteNthRootsSubgroup.instCommGroupSubtypeUnitsMemSubgroup _root_.KummerTheory.DiscreteNthRootsSubgroup.instTopologicalSpaceSubtypeUnitsMemSubgroup _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.residueFieldZModAlgebra _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.PrimeDegreePackets.diagonalLogAction _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.RamificationTheory.HilbertRamification.Higher.lowerRamificationGroup.instNormal _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionResidueField.instField _root_.RamificationTheory.HilbertRamification.ValuationSubring.selectedResidueField.instAlgebra _root_.RayClass.approximationCompletionTopologicalSpace _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.RelativeIdeleGroup.relativeIdeleMulAction _root_.CyclicCohomology.binaryCoefficientFamilyCommGroup _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.LocalClassFieldTheory.normalizationIntegerRingIsIntegralClosure _root_.RamificationTheory.HilbertRamification.CompleteDVF.decompositionGroupMulSemiringAction _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen _root_.relativeAdeleRingIntermediateAlgebra _root_.relativeAdeleRingTopIntermediateAlgebra
attribute [-simp] _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.IsDiscreteValuationRing.addVal_ringEquiv _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.EqualCharacteristicLaurent.coeffHom_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.EqualCharacteristicLaurent.powerSeriesEvalHom_C _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.EqualCharacteristicLaurent.powerSeriesEvalHom_X _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.EqualCharacteristicLaurent.powerSeriesEvalSubringHom_C _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.EqualCharacteristicLaurent.powerSeriesEvalSubringHom_X _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.iwasawaGlobalInverseLimitCarrier_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.iwasawaDegreeTerm_zero _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.iwasawaGn_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.iwasawaPartialProduct_zero_input _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.iwasawaSeedAtLevel_val _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.iwasawaSeedIdeal_val _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.iwasawaSeed_val _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitSuccQuotAddEquivResidue_iwasawaSeed _root_.LocalFieldTheory.DiscreteValuationField.LocalField.laurentSeriesEquivLaurentImageSubfield_apply_coe _root_.LocalFieldTheory.localIntegerValuationSubringEquiv_apply_coe _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.LocalFieldTheory.residueField_algebraMap_residue _root_.LubinTate.LubinTateSeries.standardLubinTateSeries_toPowerSeries _root_.LubinTate.SameUniformizer.coeff_recursiveIntertwiner _root_.LubinTate.SameUniformizer.constantCoeff_inVariable _root_.LubinTate.SameUniformizer.intertwinerApproximation_zero _root_.LubinTate.SameUniformizer.standardLubinTateEndomorphism_coeff_one _root_.LubinTate.standardLubinTateBaseUniformizerUnit_coe _root_.LubinTate.standardLubinTateChangedUniformizerUnit_coe _root_.LubinTate.standardLubinTateLevelGenerator_coe _root_.LubinTate.standardLubinTatePolynomialIterateOverSeparableClosure_eval _root_.LubinTate.standardLubinTatePolynomialIterate_derivative_eval_zero _root_.LubinTate.standardLubinTatePolynomialIterate_eval_zero _root_.LubinTate.standardLubinTatePolynomialIterate_zero _root_.LubinTate.standardLubinTatePolynomial_derivative_eval_zero _root_.LubinTate.standardLubinTatePolynomial_eval _root_.LubinTate.standardLubinTatePolynomial_toPowerSeries _root_.LubinTate.standardLubinTatePolynomial_toPowerSeries_eq_series _root_.LubinTate.standardLubinTatePrimitivePointInteger_coe _root_.LubinTate.standardLubinTatePrimitivePolynomialOverField_coeff_zero _root_.LubinTate.standardLubinTatePrimitivePolynomial_coeff_zero _root_.LubinTate.standardLubinTateUnitFactorFieldUnit_coe _root_.OAI.PrimeDegreePackets.ThetaConstruction.schwartzCM_apply _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteResidueActionOfHenselianDVF_apply _root_.RamificationTheory.HilbertRamification.Higher.dvfValuationSubringUnitAut_apply _root_.RamificationTheory.HilbertRamification.Higher.lowerRamificationGroup_neg_one _root_.RamificationTheory.HilbertRamification.Higher.mem_dvfHigherPrincipalUnitGroup_iff _root_.RamificationTheory.HilbertRamification.Higher.mem_lowerRamificationGroup_iff _root_.RamificationTheory.HilbertRamification.Higher.mem_valuationSubringDisplacementSubalgebraOfUniqueExtension_iff _root_.RamificationTheory.HilbertRamification.Higher.realRamificationIdeal_nat _root_.RamificationTheory.HilbertRamification.Higher.realRamificationIdeal_neg_one _root_.RamificationTheory.HilbertRamification.Higher.valuationSubringAutOfUniqueExtension_apply_coe _root_.RamificationTheory.HilbertRamification.Higher.valuationSubringAutOfUniqueExtension_apply_inv_apply _root_.RamificationTheory.HilbertRamification.Higher.valuationSubringAutOfUniqueExtension_mul_apply _root_.RamificationTheory.HilbertRamification.Higher.valuationSubringAutOfUniqueExtension_one_apply _root_.infinitePlace_mult_smul
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

/-- The canonical embedding `Q_p → K` takes `Z_p` into the valuation
subring.  This is proved by density of the ordinary natural numbers and
closedness of the valuation subring. -/
theorem qpadicInt_algebraMap_mem_valuationSubring
    (F : LocalField.{u, v} K) [CharZero K]
    (z : ℤ_[F.residueCharacteristic]) :
    letI : MixedQPadicContext F := mixedQPadicContext F
    algebraMap ℚ_[F.residueCharacteristic] K (z : ℚ_[F.residueCharacteristic]) ∈
      F.toCompleteDVF.valuation.valuationSubring := by
  let p : ℕ := F.residueCharacteristic
  let : MixedQPadicContext F := mixedQPadicContext F
  let : Fact p.Prime := ⟨F.residueCharacteristic_prime⟩
  let : Valued K F.mrangeValueGroup :=
    _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.mrangeRestrictValued F.toCompleteDVF
  let : NontriviallyNormedField K :=
    _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.mrangeRestrict_nontriviallyNormedField F.toCompleteDVF
  have hcontinuous : Continuous (algebraMap ℚ_[p] K) := by
    change Continuous
      (fun x : ℚ_[p] =>
        ((F.qpadicNumbersEquivQpadicClosureSubfield x :
          F.qpadicClosureSubfield) : K))
    exact continuous_subtype_val.comp
      F.qpadicNumbersToQpadicClosureSubfield_isUniformInducing.uniformContinuous.continuous
  have hclosed : IsClosed
      {x : ℤ_[p] |
        _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.mrangeRestrict F.toCompleteDVF
            (algebraMap ℚ_[p] K (x : ℚ_[p])) ≤ 1} := by
    have hvclosed : IsClosed
        {x : K | _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.mrangeRestrict F.toCompleteDVF x ≤ 1} := by
      have hset :
          {x : K |
              _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.mrangeRestrict
                F.toCompleteDVF x ≤ 1} =
            ((Valued.v : Valuation K
              (MonoidHom.mrange
                F.toCompleteDVF.valuation.toMonoidWithZeroHom)).valuationSubring :
              Set K) := by
        ext x
        change
          _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.mrangeRestrict
                F.toCompleteDVF x ≤ 1 ↔
            (Valued.v : Valuation K
              (MonoidHom.mrange
                F.toCompleteDVF.valuation.toMonoidWithZeroHom)) x ≤ 1
        rfl
      rw [hset]
      exact Valued.isClosed_valuationSubring K
    exact hvclosed.preimage
      (hcontinuous.comp continuous_subtype_val)
  have hz' :
      _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.mrangeRestrict F.toCompleteDVF
          (algebraMap ℚ_[p] K (z : ℚ_[p])) ≤ 1 := by
    refine PadicInt.denseRange_natCast.induction_on z hclosed ?_
    intro n
    change _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.mrangeRestrict F.toCompleteDVF
        (algebraMap ℚ_[p] K ((n : ℤ_[p]) : ℚ_[p])) ≤ 1
    rw [← Subtype.coe_le_coe]
    simpa [_root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.mrangeRestrict_apply] using
      F.valuation_natCast_le_one n
  rw [← Subtype.coe_le_coe] at hz'
  simpa [_root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.mrangeRestrict_apply, p] using hz'

/-- Pulling the valuation ring of `K` back along the canonical `Q_p` map
recovers precisely `Z_p`.  The reverse implication uses the DVR identity
`m_(Z_p) = p Z_p` and the strict inequality `v_K(p) < 1`. -/
theorem qpadicNumbersAlgebra_mem_valuationSubring_iff
    (F : LocalField.{u, v} K) [CharZero K]
    (x : ℚ_[F.residueCharacteristic]) :
    letI : MixedQPadicContext F := mixedQPadicContext F
    algebraMap ℚ_[F.residueCharacteristic] K x ∈
        F.toCompleteDVF.valuation.valuationSubring ↔
      ‖x‖ ≤ 1 := by
  let p : ℕ := F.residueCharacteristic
  let : MixedQPadicContext F := mixedQPadicContext F
  let : Fact p.Prime := ⟨F.residueCharacteristic_prime⟩
  constructor
  · intro hx
    by_contra hxnorm
    have hnorm : 1 < ‖x‖ := lt_of_not_ge hxnorm
    have hx0 : x ≠ 0 := by
      intro hzero
      have : ¬ (1 : ℝ) < 0 := not_lt_of_ge zero_le_one
      exact this (by simpa [hzero] using hnorm)
    have hinvnorm : ‖x⁻¹‖ < 1 := by
      rw [norm_inv]
      exact inv_lt_one_of_one_lt₀ hnorm
    let y : ℤ_[p] := ⟨x⁻¹, hinvnorm.le⟩
    have hymax : y ∈ IsLocalRing.maximalIdeal ℤ_[p] := by
      rw [IsLocalRing.mem_maximalIdeal, PadicInt.mem_nonunits]
      exact hinvnorm
    rw [PadicInt.maximalIdeal_eq_span_p,
      Ideal.mem_span_singleton] at hymax
    obtain ⟨c, hc⟩ := hymax
    have hcmem :
        algebraMap ℚ_[p] K (c : ℚ_[p]) ∈
          F.toCompleteDVF.valuation.valuationSubring := by
      simpa [p] using
        F.qpadicInt_algebraMap_mem_valuationSubring c
    have hcval :
        F.toCompleteDVF.valuation
            (algebraMap ℚ_[p] K (c : ℚ_[p])) ≤ 1 :=
      (F.toCompleteDVF.mem_valuationSubring_iff _).1 hcmem
    have hpval :
        F.toCompleteDVF.valuation
            (algebraMap ℚ_[p] K (p : ℚ_[p])) < 1 := by
      simpa [p] using
        F.valuation_natCast_residueCharacteristic_lt_one
    have hyfield : (y : ℚ_[p]) = (p : ℚ_[p]) * (c : ℚ_[p]) := by
      simpa [mul_comm] using congrArg (fun z : ℤ_[p] => (z : ℚ_[p])) hc
    have hyval :
        F.toCompleteDVF.valuation
            (algebraMap ℚ_[p] K (y : ℚ_[p])) < 1 := by
      rw [hyfield, map_mul, F.toCompleteDVF.valuation.map_mul]
      exact mul_lt_one_of_lt_of_le hpval hcval
    have hprod :
        F.toCompleteDVF.valuation (algebraMap ℚ_[p] K x) *
            F.toCompleteDVF.valuation
              (algebraMap ℚ_[p] K (x⁻¹)) < 1 := by
      apply Right.mul_lt_one_of_le_of_lt
      · exact (F.toCompleteDVF.mem_valuationSubring_iff _).1 hx
      · simpa [y] using hyval
    have hone_lt :
        F.toCompleteDVF.valuation
            (algebraMap ℚ_[p] K (x * x⁻¹)) < 1 := by
      simpa only [map_mul, F.toCompleteDVF.valuation.map_mul] using hprod
    rw [mul_inv_cancel₀ hx0, map_one,
      F.toCompleteDVF.valuation.map_one] at hone_lt
    exact (lt_irrefl (1 : F.toCompleteDVF.ValueGroup)) hone_lt
  · intro hx
    let z : ℤ_[p] := ⟨x, hx⟩
    simpa [z, p] using
      F.qpadicInt_algebraMap_mem_valuationSubring z

/-- The actual valuation of a mixed-characteristic local field extends the
DVR valuation on the canonical `Q_p` subfield. -/
theorem qpadicDVRValuation_hasExtension
    (F : LocalField.{u, v} K) [CharZero K] :
    letI : MixedQPadicContext F := mixedQPadicContext F
    (Examples.Qp.padicDVRValuation F.residueCharacteristic).HasExtension
      F.toCompleteDVF.valuation := by
  let p : ℕ := F.residueCharacteristic
  let : MixedQPadicContext F := mixedQPadicContext F
  refine ⟨(_root_.Valuation.isEquiv_iff_val_le_one).2 ?_⟩
  intro x
  have htarget :
      F.toCompleteDVF.valuation (algebraMap ℚ_[p] K x) ≤ 1 ↔
        ‖x‖ ≤ 1 :=
    (F.toCompleteDVF.mem_valuationSubring_iff _).symm.trans
      (by simpa [p] using
        F.qpadicNumbersAlgebra_mem_valuationSubring_iff x)
  exact
    (padicDVRValuation_le_one_iff_norm_le_one p x).trans
      htarget.symm

/-- The `p`-adic valuation extends to the valuation on the mixed-characteristic local field. -/
noncomputable instance mixedQPadicContextValuationExtension
    (F : LocalField.{u, v} K) [CharZero K] [MixedQPadicContext F] :
    (Examples.Qp.padicCompleteDVF F.residueCharacteristic).valuation.HasExtension
      F.toCompleteDVF.valuation :=
  F.qpadicDVRValuation_hasExtension

/-! ### the canonical `Z_p` integral basis -/

/-- The canonical ring map `Z_p → O_K`, obtained by restricting the
canonical `Q_p → K` map proved above. -/
noncomputable def padicIntToValuationSubring
    (F : LocalField.{u, v} K) [CharZero K] :
    ℤ_[F.residueCharacteristic] →+* F.toCompleteDVF.valuationSubring := by
  let p : ℕ := F.residueCharacteristic
  letI : MixedQPadicContext F := mixedQPadicContext F
  exact
    ((algebraMap ℚ_[p] K).comp PadicInt.Coe.ringHom).codRestrict
      F.toCompleteDVF.valuation.valuationSubring
      (fun z => by
        exact F.qpadicInt_algebraMap_mem_valuationSubring z)

/--
The embedding of `ℤ_p` into the valuation ring has underlying field value given by the `ℚ_p`
algebra map.
-/
@[simp]
theorem padicIntToValuationSubring_coe
    (F : LocalField.{u, v} K) [CharZero K]
    (z : ℤ_[F.residueCharacteristic]) :
    letI : MixedQPadicContext F := mixedQPadicContext F
    ((F.padicIntToValuationSubring z : F.toCompleteDVF.valuationSubring) : K) =
      algebraMap ℚ_[F.residueCharacteristic] K
        (z : ℚ_[F.residueCharacteristic]) := by
  rfl

/-- The corresponding `Z_p`-algebra structure on `O_K`. -/
@[implicit_reducible]
noncomputable def padicIntValuationSubringAlgebra
    (F : LocalField.{u, v} K) [CharZero K] :
    Algebra ℤ_[F.residueCharacteristic]
      F.toCompleteDVF.valuationSubring :=
  RingHom.toAlgebra F.padicIntToValuationSubring

/-- The corresponding `Z_p`-algebra structure on `K`. -/
@[implicit_reducible]
noncomputable def padicIntFieldAlgebra
    (F : LocalField.{u, v} K) [CharZero K] :
    Algebra ℤ_[F.residueCharacteristic] K := by
  let p : ℕ := F.residueCharacteristic
  letI : MixedQPadicContext F := mixedQPadicContext F
  exact RingHom.toAlgebra
    ((algebraMap ℚ_[p] K).comp PadicInt.Coe.ringHom)

/-- The coherent canonical `Z_p → O_K → K` algebra model.  The bundle
retains its canonical `Q_p` context and installs both integral algebra
structures and their scalar towers. -/
class MixedIntegralAlgebraContext (F : LocalField.{u, v} K) : Prop where
  /-- The canonical `Q_p` scalar context underlying the integral algebra structure. -/
  qpadic : MixedQPadicContext F

/-- The canonical integral algebra context attached to `F`. -/
theorem mixedIntegralAlgebraContext (F : LocalField.{u, v} K) :
    MixedIntegralAlgebraContext F :=
  ⟨mixedQPadicContext F⟩

/--
Equips the target with its canonical `MixedQPadicContext` structure, namely `MixedQPadicContext
F`.
-/
instance mixedIntegralAlgebraContextQPadic
    (F : LocalField.{u, v} K) [ctx : MixedIntegralAlgebraContext F] :
    MixedQPadicContext F :=
  ctx.qpadic

/--
Equips the target with its canonical `Algebra` structure, namely `Algebra
ℤ_[F.residueCharacteristic] F.toCompleteDVF.valuationSubring`.
-/
noncomputable instance mixedIntegralAlgebraContextValuationSubringAlgebra
    (F : LocalField.{u, v} K) [CharZero K]
    [MixedIntegralAlgebraContext F] :
    Algebra ℤ_[F.residueCharacteristic]
      F.toCompleteDVF.valuationSubring :=
  F.padicIntValuationSubringAlgebra

/-- The finite free canonical `Z_p` lattice model of `O_K`.  It retains the
integral algebra context and installs the finite and free module instances. -/
class MixedIntegralLatticeContext (F : LocalField.{u, v} K) : Prop where
  /-- The canonical `Z_p → O_K → K` algebra context underlying the lattice. -/
  integralAlgebra : MixedIntegralAlgebraContext F

/-- The canonical finite free integral-lattice context attached to `F`. -/
theorem mixedIntegralLatticeContext (F : LocalField.{u, v} K) :
    MixedIntegralLatticeContext F :=
  ⟨mixedIntegralAlgebraContext F⟩

/-- The valued field carries the integral algebra context `MixedIntegralAlgebraContext F`. -/
instance mixedIntegralLatticeContextAlgebra
    (F : LocalField.{u, v} K) [ctx : MixedIntegralLatticeContext F] :
    MixedIntegralAlgebraContext F :=
  ctx.integralAlgebra

/-! ### The canonical `Z_p` action on `U^r` -/

/-- Inclusion of a higher principal-unit group into `U^1`. -/
def higherPrincipalUnitToFirst
    (F : LocalField.{u, v} K) {r : ℕ} (hr : 1 ≤ r) :
    LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup (F.toCompleteDVF) r →*
      LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup (F.toCompleteDVF) 1 where
  toFun x := ⟨(x : F.toCompleteDVF.valuationSubringˣ),
    LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.antitone F.toCompleteDVF hr x.property⟩
  map_one' := rfl
  map_mul' _ _ := rfl

/-- The specified map is injective: `Function.Injective (F.higherPrincipalUnitToFirst hr)`. -/
theorem higherPrincipalUnitToFirst_injective
    (F : LocalField.{u, v} K) {r : ℕ} (hr : 1 ≤ r) :
    Function.Injective (F.higherPrincipalUnitToFirst hr) := by
  intro x y hxy
  apply Subtype.ext
  exact congrArg
    (fun z : LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup (F.toCompleteDVF) 1 =>
      (z : F.toCompleteDVF.valuationSubringˣ)) hxy

/-- Additive form of the inclusion `U^r → U^1`. -/
def higherPrincipalUnitAddToFirst
    (F : LocalField.{u, v} K) {r : ℕ} (hr : 1 ≤ r) :
    Additive (LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup (F.toCompleteDVF) r) →+
      Additive (LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup (F.toCompleteDVF) 1) :=
  MonoidHom.toAdditive (F.higherPrincipalUnitToFirst hr)

/-- The specified map is injective: `Function.Injective (F.higherPrincipalUnitAddToFirst hr)`. -/
theorem higherPrincipalUnitAddToFirst_injective
    (F : LocalField.{u, v} K) {r : ℕ} (hr : 1 ≤ r) :
    Function.Injective (F.higherPrincipalUnitAddToFirst hr) := by
  intro x y hxy
  apply Additive.toMul.injective
  exact F.higherPrincipalUnitToFirst_injective hr
    (congrArg Additive.toMul hxy)

/-- Restrict the canonical p-adic scalar action on `U^1` to the stable
subgroup `U^r`. -/
@[reducible]
noncomputable def higherPrincipalUnitPadicSMul
    (F : LocalField.{u, v} K) {r : ℕ} (hr : 1 ≤ r) :
    SMul ℤ_[F.residueCharacteristic]
      (Additive (LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup (F.toCompleteDVF) r)) where
  smul a x := by
    let x1 : LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup (F.toCompleteDVF) 1 :=
      F.higherPrincipalUnitToFirst hr (Additive.toMul x)
    let y1 : LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup (F.toCompleteDVF) 1 :=
      Additive.toMul (a • Additive.ofMul x1)
    exact Additive.ofMul ⟨(y1 : F.toCompleteDVF.valuationSubringˣ),
      CompleteDVF.higherPrincipalUnitGroup.principalUnitPadic_smul_mem_higher
        F hr a x1 (by simp [x1, higherPrincipalUnitToFirst])⟩

/-- The additive inclusion `U^r → U^1` commutes with the canonical `ℤ_p`-scalar action. -/
@[simp]
theorem higherPrincipalUnitAddToFirst_smul
    (F : LocalField.{u, v} K) {r : ℕ} (hr : 1 ≤ r)
    (a : ℤ_[F.residueCharacteristic])
    (x : Additive (LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup (F.toCompleteDVF) r)) :
    letI : SMul ℤ_[F.residueCharacteristic]
        (Additive (LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup (F.toCompleteDVF) r)) :=
      F.higherPrincipalUnitPadicSMul hr
    F.higherPrincipalUnitAddToFirst hr (a • x) =
      a • F.higherPrincipalUnitAddToFirst hr x := by
  rfl

/-- The stable subgroup `U^r` with its canonical `Z_p`-module structure. -/
@[reducible]
noncomputable def higherPrincipalUnitPadicModule
    (F : LocalField.{u, v} K) {r : ℕ} (hr : 1 ≤ r) :
    Module ℤ_[F.residueCharacteristic]
      (Additive (LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup (F.toCompleteDVF) r)) := by
  letI : SMul ℤ_[F.residueCharacteristic]
      (Additive (LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup (F.toCompleteDVF) r)) :=
    F.higherPrincipalUnitPadicSMul hr
  exact Module.ofMinimalAxioms
    (fun a x y => by
      apply F.higherPrincipalUnitAddToFirst_injective hr
      simp only [map_add, F.higherPrincipalUnitAddToFirst_smul]
      exact smul_add a
        (F.higherPrincipalUnitAddToFirst hr x :
          Additive (LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup (F.toCompleteDVF) 1))
        (F.higherPrincipalUnitAddToFirst hr y :
          Additive (LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup (F.toCompleteDVF) 1)))
    (fun a b x => by
      apply F.higherPrincipalUnitAddToFirst_injective hr
      simp only [map_add, F.higherPrincipalUnitAddToFirst_smul]
      exact add_smul a b
        (F.higherPrincipalUnitAddToFirst hr x :
          Additive (LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup (F.toCompleteDVF) 1)))
    (fun a b x => by
      apply F.higherPrincipalUnitAddToFirst_injective hr
      simp only [F.higherPrincipalUnitAddToFirst_smul, mul_smul])
    (fun x => by
      apply F.higherPrincipalUnitAddToFirst_injective hr
      simp only [F.higherPrincipalUnitAddToFirst_smul, one_smul])

/-- The deep principal units, regarded as a `Z_p`-submodule of `U^1`. -/
noncomputable def higherPrincipalUnitPadicSubmodule
    (F : LocalField.{u, v} K) {r : ℕ} (hr : 1 ≤ r) :
    Submodule ℤ_[F.residueCharacteristic]
      (Additive (LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup (F.toCompleteDVF) 1)) where
  carrier := {x | ((Additive.toMul x :
      LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup (F.toCompleteDVF) 1) :
        F.toCompleteDVF.valuationSubringˣ) ∈
      LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup (F.toCompleteDVF) r}
  zero_mem' := by
    change (1 : F.toCompleteDVF.valuationSubringˣ) ∈
      LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup (F.toCompleteDVF) r
    exact Subgroup.one_mem _
  add_mem' {x y} hx hy := by
    change (((Additive.toMul x :
        LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup (F.toCompleteDVF) 1) :
          F.toCompleteDVF.valuationSubringˣ) *
      ((Additive.toMul y :
        LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup (F.toCompleteDVF) 1) :
          F.toCompleteDVF.valuationSubringˣ)) ∈
        LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup (F.toCompleteDVF) r
    exact Subgroup.mul_mem _ hx hy
  smul_mem' a x hx :=
    CompleteDVF.higherPrincipalUnitGroup.principalUnitPadic_smul_mem_higher
      F hr a (Additive.toMul x) hx

/-- A higher principal-unit group is linearly equivalent to its image in
`U^1`.  This is the submodule used in the finite-index argument in the
proof of the mixed-characteristic field-unit structure theorem. -/
noncomputable def higherPrincipalUnitLinearEquivPadicSubmodule
    (F : LocalField.{u, v} K) {r : ℕ} (hr : 1 ≤ r) :
    letI : Module ℤ_[F.residueCharacteristic]
        (Additive (LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup (F.toCompleteDVF) r)) :=
      F.higherPrincipalUnitPadicModule hr
    Additive (LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup (F.toCompleteDVF) r) ≃ₗ[
        ℤ_[F.residueCharacteristic]] F.higherPrincipalUnitPadicSubmodule hr := by
  letI : Module ℤ_[F.residueCharacteristic]
      (Additive (LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup (F.toCompleteDVF) r)) :=
    F.higherPrincipalUnitPadicModule hr
  exact
    { toFun := fun x => ⟨F.higherPrincipalUnitAddToFirst hr x,
        (Additive.toMul x).property⟩
      invFun := fun x => Additive.ofMul
        ⟨((Additive.toMul x.1 :
          LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup (F.toCompleteDVF) 1) :
            F.toCompleteDVF.valuationSubringˣ), x.2⟩
      left_inv := fun x => by
        apply Additive.toMul.injective
        apply Subtype.ext
        rfl
      right_inv := fun x => by
        apply Subtype.ext
        apply Additive.toMul.injective
        apply Subtype.ext
        rfl
      map_add' := fun x y => by
        apply Subtype.ext
        exact map_add (F.higherPrincipalUnitAddToFirst hr) x y
      map_smul' := fun a x => by
        apply Subtype.ext
        exact F.higherPrincipalUnitAddToFirst_smul hr a x }

/-- Every wrapped local-field coordinate `U^1/U^(n+1)` is a torsion
`Z_p`-module. -/
theorem discretePrincipalUnitQuotient_moduleIsTorsion
    (F : LocalField.{u, v} K) (n : ℕ) :
    Module.IsTorsion ℤ_[F.residueCharacteristic]
      (CompleteDVF.higherPrincipalUnitGroup.DiscretePrincipalUnitQuotient
        F.toCompleteDVF n) := by
  let exponent : ℕ := F.residueCharacteristic ^
    ((CompleteDVF.higherPrincipalUnitGroup.principalUnitResidueDegree F : ℕ) * n)
  have hexponent : exponent ≠ 0 := by
    exact pow_ne_zero _ F.residueCharacteristic_prime.ne_zero
  let a : (ℤ_[F.residueCharacteristic])⁰ :=
    ⟨(exponent : ℤ_[F.residueCharacteristic]), by
      rw [mem_nonZeroDivisors_iff_ne_zero]
      exact_mod_cast hexponent⟩
  intro x
  refine ⟨a, ?_⟩
  change (exponent : ℤ_[F.residueCharacteristic]) • x = 0
  rw [Nat.cast_smul_eq_nsmul]
  exact
    CompleteDVF.higherPrincipalUnitGroup.discretePrincipalUnitQuotient_nsmul_residueCharacteristic_pow_eq_zero
      F n x

/-- The same finite coordinate is a `p`-group, with its exact cardinality
coming from the principal-unit filtration. -/
theorem discretePrincipalUnitQuotient_isPGroup
    (F : LocalField.{u, v} K) (n : ℕ) :
    IsPGroup F.residueCharacteristic
      (Multiplicative
        (CompleteDVF.higherPrincipalUnitGroup.DiscretePrincipalUnitQuotient
          F.toCompleteDVF n)) := by
  apply IsPGroup.of_card
    (n := (CompleteDVF.higherPrincipalUnitGroup.principalUnitResidueDegree F : ℕ) * n)
  calc
    Nat.card
        (Multiplicative
          (CompleteDVF.higherPrincipalUnitGroup.DiscretePrincipalUnitQuotient
            F.toCompleteDVF n)) =
        Nat.card
          (CompleteDVF.higherPrincipalUnitGroup.DiscretePrincipalUnitQuotient
            F.toCompleteDVF n) :=
      Nat.card_congr Multiplicative.toAdd
    _ = F.residueCharacteristic ^
          ((CompleteDVF.higherPrincipalUnitGroup.principalUnitResidueDegree F : ℕ) * n) :=
      CompleteDVF.higherPrincipalUnitGroup.card_discretePrincipalUnitQuotient_eq_residueCharacteristic_pow
        F n

/-- Finite generation passes from a higher principal-unit group to its
image as a submodule of `U^1`. -/
theorem higherPrincipalUnitPadicSubmodule_moduleFinite
    (F : LocalField.{u, v} K) {r : ℕ} (hr : 1 ≤ r)
    (hfinite : @Module.Finite ℤ_[F.residueCharacteristic]
      (Additive (LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup (F.toCompleteDVF) r)) _ _
      (F.higherPrincipalUnitPadicModule hr)) :
    Module.Finite ℤ_[F.residueCharacteristic]
      (F.higherPrincipalUnitPadicSubmodule hr) := by
  let : Module ℤ_[F.residueCharacteristic]
      (Additive (LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup (F.toCompleteDVF) r)) :=
    F.higherPrincipalUnitPadicModule hr
  let : Module.Finite ℤ_[F.residueCharacteristic]
      (Additive (LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup (F.toCompleteDVF) r)) := hfinite
  exact Module.Finite.equiv
    (F.higherPrincipalUnitLinearEquivPadicSubmodule hr)

end LocalField
end LocalFieldTheory.DiscreteValuationField
end
end

section
-- module Solutions.OAIQ244_DUKE.LocalField_DiscreteValuationField_MixedCharacteristicStructure_DeepPrincipalUnits
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_isCompleteDiscrete _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.DiscreteNthRootsSubgroup.instCommGroupSubtypeUnitsMemSubgroup _root_.KummerTheory.DiscreteNthRootsSubgroup.instTopologicalSpaceSubtypeUnitsMemSubgroup _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.residueFieldZModAlgebra _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.RamificationTheory.HilbertRamification.Higher.lowerRamificationGroup.instNormal _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionFixedSubring.instIsLocalRing _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionResidueField.instField _root_.RamificationTheory.HilbertRamification.ValuationSubring.selectedResidueField.instAlgebra _root_.RayClass.approximationCompletionTopologicalSpace _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.CyclicCohomology.binaryCoefficientFamilyCommGroup _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.LocalClassFieldTheory.normalizationIntegerRingIsIntegralClosure _root_.RamificationTheory.HilbertRamification.CompleteDVF.decompositionGroupMulSemiringAction _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen _root_.relativeAdeleRingIntermediateAlgebra _root_.relativeAdeleRingTopIntermediateAlgebra
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

/-!
# Deep principal units in mixed characteristic

This module equips the canonical `Z_p` lattice with the normalized valuation
topology and transports integral-basis coordinates through the deep
exponential--logarithm equivalence.
-/

noncomputable section

universe u v

namespace LocalFieldTheory.DiscreteValuationField
namespace LocalField

open scoped WithZero nonZeroDivisors
open Module

variable {K : Type u} [Field K]

/-! ### The canonical normalized-valuation model -/

/-- The canonical mixed-characteristic algebra and topology attached to a
normalized `ℤᵐ⁰`-valued local field.  The bundle retains both the integral
algebra context and the direct valued-field structure; installing it exposes
the coherent `Q_p`/`Z_p` scalar towers and valuation topology. -/
class MixedWithZeroValuationContext
    (v : _root_.Valuation K (WithZero (Multiplicative ℤ)))
    [ValuationTheory.DiscreteValuationField.Valuation.IsCompleteDiscrete v]
    [Finite (IsLocalRing.ResidueField v.valuationSubring)] where
  /-- The integral-algebra context for the local-field model obtained by
  restricting the normalized valuation to its nonzero value group. -/
  integralAlgebra :
    MixedIntegralAlgebraContext (ofWithZeroValuation v)
  /-- The valued-field structure on `K` whose valuation is the original
  normalized `WithZero (Multiplicative ℤ)`-valued valuation. -/
  valued : Valued K (WithZero (Multiplicative ℤ))

/-- The canonical normalized-valuation context. -/
@[implicit_reducible]
def mixedWithZeroValuationContext
    (v : _root_.Valuation K (WithZero (Multiplicative ℤ)))
    [ValuationTheory.DiscreteValuationField.Valuation.IsCompleteDiscrete v]
    [Finite (IsLocalRing.ResidueField v.valuationSubring)] :
    MixedWithZeroValuationContext v :=
  { integralAlgebra :=
      mixedIntegralAlgebraContext (ofWithZeroValuation v)
    valued := Valued.mk' v }

/--
The valued field carries the integral algebra context `MixedIntegralAlgebraContext
(ofWithZeroValuation v)`.
-/
instance mixedWithZeroValuationContextIntegralAlgebra
    (v : _root_.Valuation K (WithZero (Multiplicative ℤ)))
    [ValuationTheory.DiscreteValuationField.Valuation.IsCompleteDiscrete v]
    [Finite (IsLocalRing.ResidueField v.valuationSubring)]
    [ctx : MixedWithZeroValuationContext v] :
    MixedIntegralAlgebraContext (ofWithZeroValuation v) :=
  ctx.integralAlgebra

/-! ### Continuity for the normalized valuation used by the deep exponential–logarithm equivalence -/

/-- For a normalized `ℤᵐ⁰`-valued local field, the canonical embedding
`Q_p → K` is continuous for the direct topology induced by `v`. -/
theorem continuous_qpadicNumbersAlgebra_ofWithZeroValuation
    (v : _root_.Valuation K (WithZero (Multiplicative ℤ)))
    [ValuationTheory.DiscreteValuationField.Valuation.IsCompleteDiscrete v]
    [Finite (IsLocalRing.ResidueField v.valuationSubring)] [CharZero K] :
    let F : LocalField.{u, 0} K := ofWithZeroValuation v
    letI : MixedWithZeroValuationContext v :=
      mixedWithZeroValuationContext v
    letI : Valued K (WithZero (Multiplicative ℤ)) := Valued.mk' v
    Continuous (algebraMap ℚ_[F.residueCharacteristic] K) := by
  let F : LocalField.{u, 0} K := ofWithZeroValuation v
  let : MixedWithZeroValuationContext v :=
    mixedWithZeroValuationContext v
  let : Valued K (WithZero (Multiplicative ℤ)) := Valued.mk' v
  let p : ℕ := F.residueCharacteristic
  let direct : Valued K (WithZero (Multiplicative ℤ)) := Valued.mk' v
  let restricted : Valued K F.mrangeValueGroup :=
    _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.mrangeRestrictValued F.toCompleteDVF
  have hrestricted :
      @Continuous ℚ_[p] K inferInstance restricted.toTopologicalSpace
        (algebraMap ℚ_[p] K) := by
    let : Valued K F.mrangeValueGroup := restricted
    let : NontriviallyNormedField K :=
      _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.mrangeRestrict_nontriviallyNormedField F.toCompleteDVF
    change Continuous
      (fun x : ℚ_[p] =>
        ((F.qpadicNumbersEquivQpadicClosureSubfield x :
          F.qpadicClosureSubfield) : K))
    exact continuous_subtype_val.comp
      F.qpadicNumbersToQpadicClosureSubfield_isUniformInducing.uniformContinuous.continuous
  have huniform :
      (Valued.mk' v).toUniformSpace =
        (_root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.mrangeRestrictValued
          F.toCompleteDVF).toUniformSpace := by
    change (Valued.mk' v).toUniformSpace =
      (_root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.mrangeRestrictValued
        (WithZeroValuationTopology.completeDVF v)).toUniformSpace
    exact WithZeroValuationTopology.valuedMk_uniformSpace_eq_mrangeRestrict v
  let : Valued K (WithZero (Multiplicative ℤ)) := direct
  rw [show direct.toTopologicalSpace = restricted.toTopologicalSpace by
    exact congrArg (fun U : UniformSpace K => U.toTopologicalSpace) huniform]
  exact hrestricted

/-- The restricted map `Z_p → O_K` is continuous in the direct valuation
topology. -/
theorem continuous_padicIntToValuationSubring_ofWithZeroValuation
    (v : _root_.Valuation K (WithZero (Multiplicative ℤ)))
    [ValuationTheory.DiscreteValuationField.Valuation.IsCompleteDiscrete v]
    [Finite (IsLocalRing.ResidueField v.valuationSubring)] [CharZero K] :
    let F : LocalField.{u, 0} K := ofWithZeroValuation v
    letI : MixedWithZeroValuationContext v :=
      mixedWithZeroValuationContext v
    letI : Valued K (WithZero (Multiplicative ℤ)) := Valued.mk' v
    Continuous F.padicIntToValuationSubring := by
  let F : LocalField.{u, 0} K := ofWithZeroValuation v
  let : MixedWithZeroValuationContext v :=
    mixedWithZeroValuationContext v
  let : Valued K (WithZero (Multiplicative ℤ)) := Valued.mk' v
  apply Continuous.subtype_mk
  exact (continuous_qpadicNumbersAlgebra_ofWithZeroValuation v).comp
    continuous_subtype_val

/-- The natural scalar multiplication of `Z_p` on `O_K` is continuous. -/
theorem continuousSMul_padicInt_valuationSubring_ofWithZeroValuation
    (v : _root_.Valuation K (WithZero (Multiplicative ℤ)))
    [ValuationTheory.DiscreteValuationField.Valuation.IsCompleteDiscrete v]
    [Finite (IsLocalRing.ResidueField v.valuationSubring)] [CharZero K] :
    let F : LocalField.{u, 0} K := ofWithZeroValuation v
    letI : MixedWithZeroValuationContext v :=
      mixedWithZeroValuationContext v
    letI : Valued K (WithZero (Multiplicative ℤ)) := Valued.mk' v
    ContinuousSMul ℤ_[F.residueCharacteristic]
      F.toCompleteDVF.valuationSubring := by
  let F : LocalField.{u, 0} K := ofWithZeroValuation v
  let : MixedWithZeroValuationContext v :=
    mixedWithZeroValuationContext v
  let : Valued K (WithZero (Multiplicative ℤ)) := Valued.mk' v
  refine ⟨?_⟩
  apply Continuous.subtype_mk
  change Continuous
    (fun z : ℤ_[F.residueCharacteristic] ×
        F.toCompleteDVF.valuationSubring =>
      ((F.padicIntToValuationSubring z.1 :
        F.toCompleteDVF.valuationSubring) : K) * (z.2 : K))
  exact
    (continuous_subtype_val.comp
      ((continuous_padicIntToValuationSubring_ofWithZeroValuation v).comp
        continuous_fst)).mul
      (continuous_subtype_val.comp continuous_snd)

/-- The induced action on every maximal-ideal power is continuous. -/
theorem continuousSMul_padicInt_maximalIdealPow_ofWithZeroValuation
    (v : _root_.Valuation K (WithZero (Multiplicative ℤ)))
    [ValuationTheory.DiscreteValuationField.Valuation.IsCompleteDiscrete v]
    [Finite (IsLocalRing.ResidueField v.valuationSubring)] [CharZero K]
    (n : ℕ) :
    let F : LocalField.{u, 0} K := ofWithZeroValuation v
    letI : MixedWithZeroValuationContext v :=
      mixedWithZeroValuationContext v
    letI : Valued K (WithZero (Multiplicative ℤ)) := Valued.mk' v
    ContinuousSMul ℤ_[F.residueCharacteristic]
      ((F.toCompleteDVF.maximalIdeal ^ n :
        Ideal F.toCompleteDVF.valuationSubring)) := by
  let F : LocalField.{u, 0} K := ofWithZeroValuation v
  let : MixedWithZeroValuationContext v :=
    mixedWithZeroValuationContext v
  let : Valued K (WithZero (Multiplicative ℤ)) := Valued.mk' v
  let : ContinuousSMul ℤ_[F.residueCharacteristic]
      F.toCompleteDVF.valuationSubring :=
    continuousSMul_padicInt_valuationSubring_ofWithZeroValuation v
  refine ⟨?_⟩
  apply Continuous.subtype_mk
  change Continuous
    (fun z : ℤ_[F.residueCharacteristic] ×
        ((F.toCompleteDVF.maximalIdeal ^ n :
          Ideal F.toCompleteDVF.valuationSubring)) =>
      z.1 • (z.2 : F.toCompleteDVF.valuationSubring))
  exact continuous_fst.smul (continuous_subtype_val.comp continuous_snd)

/-- The canonical p-adic action on `U^1` is jointly continuous for the
direct normalized valuation topology. -/
theorem continuousSMul_padicInt_firstPrincipalUnit_ofWithZeroValuation
    (v : _root_.Valuation K (WithZero (Multiplicative ℤ)))
    [ValuationTheory.DiscreteValuationField.Valuation.IsCompleteDiscrete v]
    [Finite (IsLocalRing.ResidueField v.valuationSubring)] [CharZero K] :
    let F : LocalField.{u, 0} K := ofWithZeroValuation v
    letI : MixedWithZeroValuationContext v :=
      mixedWithZeroValuationContext v
    letI : Valued K (WithZero (Multiplicative ℤ)) := Valued.mk' v
    ContinuousSMul ℤ_[F.residueCharacteristic]
      (Additive (LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup (F.toCompleteDVF) 1)) := by
  let F : LocalField.{u, 0} K := ofWithZeroValuation v
  let : MixedWithZeroValuationContext v :=
    mixedWithZeroValuationContext v
  let : Valued K (WithZero (Multiplicative ℤ)) := Valued.mk' v
  exact
    CompleteDVF.higherPrincipalUnitGroup.principalUnitPadicContinuousSMulOfWithZeroValuation
      v

/-- Every stable higher principal-unit subgroup inherits the joint
continuous p-adic action from `U^1`. -/
theorem continuousSMul_padicInt_higherPrincipalUnit_ofWithZeroValuation
    (v : _root_.Valuation K (WithZero (Multiplicative ℤ)))
    [ValuationTheory.DiscreteValuationField.Valuation.IsCompleteDiscrete v]
    [Finite (IsLocalRing.ResidueField v.valuationSubring)] [CharZero K]
    {r : ℕ} (hr : 1 ≤ r) :
    let F : LocalField.{u, 0} K := ofWithZeroValuation v
    letI : MixedWithZeroValuationContext v :=
      mixedWithZeroValuationContext v
    letI : Valued K (WithZero (Multiplicative ℤ)) := Valued.mk' v
    letI : Module ℤ_[F.residueCharacteristic]
        (Additive (LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup (F.toCompleteDVF) r)) :=
      F.higherPrincipalUnitPadicModule hr
    ContinuousSMul ℤ_[F.residueCharacteristic]
      (Additive (LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup (F.toCompleteDVF) r)) := by
  let F : LocalField.{u, 0} K := ofWithZeroValuation v
  let : MixedWithZeroValuationContext v :=
    mixedWithZeroValuationContext v
  let : Valued K (WithZero (Multiplicative ℤ)) := Valued.mk' v
  let : Module ℤ_[F.residueCharacteristic]
      (Additive (LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup (F.toCompleteDVF) r)) :=
    F.higherPrincipalUnitPadicModule hr
  let : ContinuousSMul ℤ_[F.residueCharacteristic]
      (Additive (LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup (F.toCompleteDVF) 1)) :=
    continuousSMul_padicInt_firstPrincipalUnit_ofWithZeroValuation v
  have hinc : Continuous (F.higherPrincipalUnitAddToFirst hr) := by
    apply Continuous.subtype_mk
    exact continuous_subtype_val
  have hsmulFirst : Continuous
      (fun z : ℤ_[F.residueCharacteristic] ×
          Additive (LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup
            F.toCompleteDVF r) =>
        z.1 • F.higherPrincipalUnitAddToFirst hr z.2) :=
    continuous_fst.smul (hinc.comp continuous_snd)
  refine ⟨?_⟩
  apply Continuous.subtype_mk
  apply (continuous_subtype_val.comp hsmulFirst).congr
  intro z
  exact congrArg
    (fun y :
        Additive (LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup
          F.toCompleteDVF 1) =>
      ((Additive.toMul y :
        LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup
          F.toCompleteDVF 1) : F.toCompleteDVF.valuationSubringˣ))
    (F.higherPrincipalUnitAddToFirst_smul hr z.1 z.2).symm

/-! ### the deep exponential–logarithm equivalence connected to the integral basis -/

end LocalField
end LocalFieldTheory.DiscreteValuationField
end
end

section
-- module Solutions.OAIQ244_DUKE.LocalField_Padic_PrincipalUnits
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitInverseLimitCarrierPadicModule _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitQuotientCarrierPadicModule _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitPadicModule _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitPadicSMul _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.residueFieldZModAlgebra _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedIntegralAlgebraContextValuationSubringAlgebra _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedQPadicContextValuationExtension _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.RamificationTheory.HilbertRamification.Higher.lowerRamificationGroup.instNormal _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionResidueField.instField _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.LocalClassFieldTheory.normalizationIntegerRingIsIntegralClosure _root_.RamificationTheory.HilbertRamification.CompleteDVF.decompositionGroupMulSemiringAction _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.chosenFinitePlaceBaseValuativeRel _root_.finiteLocalUnitsOpen
attribute [-simp] _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.IsDiscreteValuationRing.addVal_ringEquiv _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.EqualCharacteristicLaurent.coeffHom_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.EqualCharacteristicLaurent.powerSeriesEvalHom_C _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.EqualCharacteristicLaurent.powerSeriesEvalHom_X _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.EqualCharacteristicLaurent.powerSeriesEvalSubringHom_C _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.EqualCharacteristicLaurent.powerSeriesEvalSubringHom_X _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.AdicPrincipalUnits.addEquiv_map_smul _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.AdicPrincipalUnits.val_of _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.DiscretePrincipalUnitQuotient.addEquiv_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.DiscretePrincipalUnitQuotient.addEquiv_map_smul _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.DiscretePrincipalUnitQuotient.addEquiv_of _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.DiscretePrincipalUnitQuotient.addEquiv_symm_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.DiscretePrincipalUnitQuotient.val_transition _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.adicPrincipalUnitsHomeomorphUnderlying_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.iwasawaGlobalInverseLimitCarrier_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitAddEquivInverseLimitCarrier_map_smul _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitAddHomeomorphInverseLimitCarrier_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitInverseLimitCarrierEval_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitInverseLimitCarrierPadic_smul_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitMulEquivInverseLimitCarrier_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitPadic_smul_carrier_coordinate _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitProdiscreteLimitHomeomorphUnderlying_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitQuotientCarrierPadicScalar_eq_smul _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitQuotientCarrierToFull_mk _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitQuotientCarrierTransition_mk _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.uniformizerHigherUnitQuotientEquiv_mk _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.PrincipalUnitProdiscreteLimit.addEquiv_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.PrincipalUnitProdiscreteLimit.addEquiv_map_smul _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.PrincipalUnitProdiscreteLimit.addEquiv_symm_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.PrincipalUnitProdiscreteLimit.coordinate_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.adicPrincipalUnitsContinuousAddEquivUnderlyingOfWithZeroValuation_map_smul _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.adicPrincipalUnitsHomeomorphProdiscreteLimit_to_addEquiv _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.iwasawaDegreeTerm_zero _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.iwasawaGn_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.iwasawaPartialProduct_zero_input _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.iwasawaSeedAtLevel_val _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.iwasawaSeedIdeal_val _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.iwasawaSeed_val _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitPadic_natCast_smul _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitPadic_nsmul_eq_pow _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitPadic_smul_def _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitSuccQuotAddEquivResidue_iwasawaSeed _root_.LocalFieldTheory.DiscreteValuationField.LocalField.higherPrincipalUnitAddToFirst_smul _root_.LocalFieldTheory.DiscreteValuationField.LocalField.laurentSeriesEquivLaurentImageSubfield_apply_coe _root_.LocalFieldTheory.DiscreteValuationField.LocalField.padicIntToValuationSubring_coe _root_.LocalFieldTheory.localIntegerValuationSubringEquiv_apply_coe _root_.LocalFieldTheory.residueField_algebraMap_residue _root_.LubinTate.LubinTateSeries.standardLubinTateSeries_toPowerSeries _root_.LubinTate.SameUniformizer.coeff_recursiveIntertwiner _root_.LubinTate.SameUniformizer.constantCoeff_inVariable _root_.LubinTate.SameUniformizer.intertwinerApproximation_zero _root_.LubinTate.SameUniformizer.standardLubinTateEndomorphism_coeff_one _root_.LubinTate.standardLubinTateBaseUniformizerUnit_coe _root_.LubinTate.standardLubinTateChangedUniformizerUnit_coe _root_.LubinTate.standardLubinTateLevelGenerator_coe _root_.LubinTate.standardLubinTatePolynomialIterateOverSeparableClosure_eval _root_.LubinTate.standardLubinTatePolynomialIterate_derivative_eval_zero _root_.LubinTate.standardLubinTatePolynomialIterate_eval_zero _root_.LubinTate.standardLubinTatePolynomialIterate_zero _root_.LubinTate.standardLubinTatePolynomial_derivative_eval_zero _root_.LubinTate.standardLubinTatePolynomial_eval _root_.LubinTate.standardLubinTatePolynomial_toPowerSeries _root_.LubinTate.standardLubinTatePolynomial_toPowerSeries_eq_series _root_.LubinTate.standardLubinTatePrimitivePointInteger_coe _root_.LubinTate.standardLubinTatePrimitivePolynomialOverField_coeff_zero _root_.LubinTate.standardLubinTatePrimitivePolynomial_coeff_zero _root_.LubinTate.standardLubinTateUnitFactorFieldUnit_coe _root_.OAI.PrimeDegreePackets.ThetaConstruction.schwartzCM_apply _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteResidueActionOfHenselianDVF_apply _root_.RamificationTheory.HilbertRamification.Higher.dvfValuationSubringUnitAut_apply _root_.RamificationTheory.HilbertRamification.Higher.lowerRamificationGroup_neg_one _root_.RamificationTheory.HilbertRamification.Higher.mem_dvfHigherPrincipalUnitGroup_iff _root_.RamificationTheory.HilbertRamification.Higher.mem_lowerRamificationGroup_iff _root_.RamificationTheory.HilbertRamification.Higher.mem_valuationSubringDisplacementSubalgebraOfUniqueExtension_iff _root_.RamificationTheory.HilbertRamification.Higher.realRamificationIdeal_nat _root_.RamificationTheory.HilbertRamification.Higher.realRamificationIdeal_neg_one _root_.RamificationTheory.HilbertRamification.Higher.valuationSubringAutOfUniqueExtension_apply_coe _root_.RamificationTheory.HilbertRamification.Higher.valuationSubringAutOfUniqueExtension_apply_inv_apply _root_.RamificationTheory.HilbertRamification.Higher.valuationSubringAutOfUniqueExtension_mul_apply _root_.RamificationTheory.HilbertRamification.Higher.valuationSubringAutOfUniqueExtension_one_apply _root_.infinitePlace_mult_smul
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

/-- The valuative integer ring of `ℚ_p` is canonically equivalent to the
valuation subring of the bundled p-adic complete discrete valuation field. -/
noncomputable def integerRingEquivPadicDVRValuationSubring :
    𝒪[ℚ_[p]] ≃+*
      (LocalFieldTheory.DiscreteValuationField.Examples.Qp.padicCompleteDVF p).valuationSubring :=
  (integerRingEquivPadicInt p).trans
    (LocalFieldTheory.DiscreteValuationField.Examples.Qp.padicIntEquivValuationSubring p)

/-- The equivalence with the bundled p-adic valuation subring preserves the
underlying field element. -/
@[simp] theorem integerRingEquivPadicDVRValuationSubring_coe
    (x : 𝒪[ℚ_[p]]) :
    ((integerRingEquivPadicDVRValuationSubring p x :
        (LocalFieldTheory.DiscreteValuationField.Examples.Qp.padicCompleteDVF p).valuationSubring) :
      ℚ_[p]) = (x : ℚ_[p]) := by
  rfl

/-- Coercing the p-adic prime integer back to `ℚ_p` gives `p`. -/
@[simp] theorem padicPrimeInteger_coe :
    ((padicPrimeInteger p : 𝒪[ℚ_[p]]) : ℚ_[p]) = (p : ℚ_[p]) := rfl

end LocalFieldTheory.Padic

end
end

section
-- module Solutions.OAIQ244_DUKE.GlobalClassFieldTheory_ClassFieldAxiom_IdeleClassPowerLocalUnitQuotient_LocalResidueArithmetic
attribute [-instance] _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.OAI.PrimeDegreePackets.boundedRealFields_finite _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_finite_residue _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.RamificationTheory.HilbertRamification.Higher.lowerRamificationGroup.instNormal _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionFixedSubring.instIsLocalRing _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionResidueField.instField _root_.RamificationTheory.HilbertRamification.ValuationSubring.selectedResidueField.instAlgebra _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.LocalClassFieldTheory.normalizationIntegerRingIsIntegralClosure _root_.RamificationTheory.HilbertRamification.CompleteDVF.decompositionGroupMulSemiringAction _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.chosenFinitePlaceBaseValued _root_.relativeAdeleRingIntermediateAlgebra _root_.relativeAdeleRingTopIntermediateAlgebra _root_.scaledRelativeIntegerLatticeQuotientFinite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

/-!
# Residue arithmetic for finite-place power indices

This file relates global ideal norms to the residue fields and ramification
invariants of the corresponding finite completions.
-/

open scoped NumberField Classical NNReal ValuativeRel
open NumberField IsDedekindDomain
open LocalFieldTheory

noncomputable section

namespace GlobalClassFieldTheory.ClassFieldAxiom

variable {K : Type} [Field K] [NumberField K]


/-- The cardinality of a mixed-characteristic local residue field is
`p` to the residue degree. -/
theorem card_localField_residueField_eq_pow_residueDegree
    {E : Type*} [Field E]
    (ν : Valuation E (WithZero (Multiplicative ℤ)))
    [ValuationTheory.DiscreteValuationField.Valuation.IsCompleteDiscrete ν]
    [Finite
      (IsLocalRing.ResidueField ν.valuationSubring)]
    [CharZero E] :
    let F :=
      LocalFieldTheory.DiscreteValuationField.LocalField.ofWithZeroValuation
        ν
    letI :
        LocalFieldTheory.DiscreteValuationField.LocalField.MixedQPadicContext
          F :=
      LocalFieldTheory.DiscreteValuationField.LocalField.mixedQPadicContext
        F
    Nat.card F.residueField =
      F.residueCharacteristic ^
        ValuationTheory.DiscreteValuationField.ValuedExtension.residueDegree
          (LocalFieldTheory.DiscreteValuationField.Examples.Qp.padicCompleteDVF
            F.residueCharacteristic).toDVF
          F.toCompleteDVF.toDVF := by
  let F :=
    LocalFieldTheory.DiscreteValuationField.LocalField.ofWithZeroValuation
      ν
  let p := F.residueCharacteristic
  let :
      LocalFieldTheory.DiscreteValuationField.LocalField.MixedQPadicContext
        F :=
    LocalFieldTheory.DiscreteValuationField.LocalField.mixedQPadicContext
      F
  let base :=
    LocalFieldTheory.DiscreteValuationField.Examples.Qp.padicCompleteDVF p
  let target := F.toCompleteDVF
  let : Finite base.residueField :=
    LocalFieldTheory.DiscreteValuationField.Examples.Qp.padicCompleteDVF_residueField_finite p
  change
    Nat.card target.residueField =
      p ^
        ValuationTheory.DiscreteValuationField.ValuedExtension.residueDegree
          base.toDVF target.toDVF
  have hfinrank :
      Module.finrank base.residueField target.residueField =
        ValuationTheory.DiscreteValuationField.ValuedExtension.residueDegree
          base.toDVF target.toDVF := by
    rw [
      ValuationTheory.DiscreteValuationField.ValuedExtension.residueDegree_eq_finrank_quotient
        base target]
    rfl
  calc
    Nat.card target.residueField =
        Nat.card base.residueField ^
          Module.finrank base.residueField target.residueField :=
      Module.natCard_eq_pow_finrank
    _ = p ^
        ValuationTheory.DiscreteValuationField.ValuedExtension.residueDegree
          base.toDVF target.toDVF := by
      rw [hfinrank,
        LocalFieldTheory.DiscreteValuationField.Examples.Qp.padicCompleteDVF_residueField_card]

/-- The absolute norm of `v` is `p^f`, with `p` the residue
characteristic and `f` the local residue degree. -/
theorem absNorm_eq_residueCharacteristic_pow_residueDegree
    (v : HeightOneSpectrum (𝓞 K)) :
    let ν :
        Valuation
          (v.adicCompletion K)
          (WithZero (Multiplicative ℤ)) :=
      Valued.v
    let F :=
      LocalFieldTheory.DiscreteValuationField.LocalField.ofWithZeroValuation
        ν
    letI :
        LocalFieldTheory.DiscreteValuationField.LocalField.MixedQPadicContext
          F :=
      LocalFieldTheory.DiscreteValuationField.LocalField.mixedQPadicContext
        F
    Ideal.absNorm v.asIdeal =
      F.residueCharacteristic ^
        ValuationTheory.DiscreteValuationField.ValuedExtension.residueDegree
          (LocalFieldTheory.DiscreteValuationField.Examples.Qp.padicCompleteDVF
            F.residueCharacteristic).toDVF
          F.toCompleteDVF.toDVF := by
  let ν :
      Valuation
        (v.adicCompletion K)
        (WithZero (Multiplicative ℤ)) :=
    Valued.v
  let F :=
    LocalFieldTheory.DiscreteValuationField.LocalField.ofWithZeroValuation
      ν
  let :
      LocalFieldTheory.DiscreteValuationField.LocalField.MixedQPadicContext
        F :=
    LocalFieldTheory.DiscreteValuationField.LocalField.mixedQPadicContext
      F
  rw [absNorm_eq_card_adicResidueField]
  change
    Nat.card F.residueField =
      F.residueCharacteristic ^
        ValuationTheory.DiscreteValuationField.ValuedExtension.residueDegree
          (LocalFieldTheory.DiscreteValuationField.Examples.Qp.padicCompleteDVF
            F.residueCharacteristic).toDVF
          F.toCompleteDVF.toDVF
  exact card_localField_residueField_eq_pow_residueDegree ν


end GlobalClassFieldTheory.ClassFieldAxiom
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

theorem linearForm_basis (i : σ) :
    linearForm (R := R)
        (fun j : σ => if j = i then (1 : R) else 0) =
      (MvPowerSeries.X i : MvPowerSeries σ R) := by
  classical
  simp [linearForm]

end LinearTerms

end SameUniformizer
end LubinTate

end
end


