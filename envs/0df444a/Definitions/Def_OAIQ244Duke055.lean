-- Prove2me | Definitions.Def_OAIQ244Duke055
-- name    : OAIQ244Duke055
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-13T07:04:48.451197+00:00
-- url     : https://prove2.me/theorems/ba8d81a6-6395-4dc6-9568-9440bc5e5cc6
-- title:
--   Definitions bundle OAIQ244Duke055 of the split of OpenAI, Equidistribution of Prime-Degree Torus Packets with Arbitrary Local Type
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.DukePrimeDegree.prime_degree_packet_measure_equidistribution_unconditional` and `OAI.DukePrimeDegree.prime_degree_packet_measures_tendsto_haar_unconditional`, carved from OpenAI's openai/math development (OpenAI, *Equidistribution of Prime-Degree Torus Packets with Arbitrary Local Type*, OpenAI Math Release, September 24, 2026, result family 15, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 102 declarations of OpenAI's Lean: 28 definitions, 1 inductive type or structure, 8 instances and 65 theorems. The definitions and types are `GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceNthPowerDefect`, `GlobalClassFieldTheory.ClassFieldAxiom.sUnitKummerAvoidedBasePlaces`, `GlobalClassFieldTheory.ClassFieldAxiom.sUnitKummerPrimeCount`, `KummerTheory.enlargedSUnitKummerAlgebra`, `KummerTheory.enlargedSUnitKummerCyclicFixedField`, `KummerTheory.enlargedSUnitKummerRestrictionHom`, `LocalClassFieldTheory.A`, `LocalClassFieldTheory.abstractExtensionFixedRepresentationIsoUnitsRes`, `LocalClassFieldTheory.abstractExtensionFixedRepresentationUnitsEquiv`, `LocalClassFieldTheory.abstractExtensionQuotientEquivGaloisGroup`, `LocalClassFieldTheory.abstractFixedFieldUnitsEquivGaloisFixed`, `LocalClassFieldTheory.abstractRelativeFixedFieldUnitsEquivGaloisFixed`, `LocalClassFieldTheory.baseFieldUnitsEquiv`, `LocalClassFieldTheory.baseFixingCosetEquivAlgHom`, `LocalClassFieldTheory.baseFixingCosetToAlgHom`, `LocalClassFieldTheory.finiteNormQuotientEquivEmbeddedNormQuotient`, `LocalClassFieldTheory.finiteNormQuotientEquivNormQuotient`, `LocalClassFieldTheory.localBaseValuation`, `LocalClassFieldTheory.localHenselianValuation`, `LocalClassFieldTheory.localValueGroupReduction`, `LocalFieldTheory.DiscreteValuationField.LocalField.MixedMaximalIdealPowContext`, `LocalFieldTheory.DiscreteValuationField.LocalField.mixed_deepLogContinuousAddEquiv`, `LocalFieldTheory.DiscreteValuationField.LocalField.mixed_deepLogLinearEquiv`, `LocalFieldTheory.DiscreteValuationField.LocalField.principalUnitQuotientProjectionLinear`, `LocalFieldTheory.DiscreteValuationField.LocalField.principalUnitSuccPadicSubmodule`, `LocalFieldTheory.DiscreteValuationField.MultiplicativeIntegerValuation.chosenExpLogContinuousMulEquiv`, `LocalFieldTheory.DiscreteValuationField.MultiplicativeIntegerValuation.principalUnitExpLogContinuousMulEquivOfExact_ofWithZeroValuationScaled`, `LocalFieldTheory.DiscreteValuationField.MultiplicativeIntegerValuation.principalUnitExpLogMulEquivOfExact_ofWithZeroValuationScaled`, `LocalFieldTheory.DiscreteValuationField.MultiplicativeIntegerValuation.principalUnitLogSeriesOfHigherPrincipalUnitGroupOfWithZeroValuationScaled`.
--
--   **Sources.** They come from these modules of lean/OAI/NumberTheory, in whole or in part: `AlgebraicNumberTheory_Ramification_Splitting_FinitePlaceIdeal`, `AlgebraicNumberTheory_RayClass_Approximation`, `GlobalClassFieldTheory_ClassFieldAxiom_IdeleClassPowerLocalUnitQuotient_FinitePlacePowerIndex`, `GlobalClassFieldTheory_ClassFieldAxiom_IdeleClassPowerLocalUnitQuotient_LocalResidueArithmetic`, `GlobalClassFieldTheory_ClassFieldAxiom_IdeleClassPowerLocalUnitQuotient_SupportedIdeleIndex`, `GlobalClassFieldTheory_ClassFieldAxiom_SUnitKummerPrimeSelection_BasePlaceSelection`, `GlobalClassFieldTheory_ClassFieldAxiom_SUnitKummerPrimeSelection_RestrictionKernel`, `KummerTheory_Concrete_SUnitPreparation_EnlargedSUnitRestriction`, `KummerTheory_Concrete_SUnitPreparation_FiniteRadicalSupport`, `LocalClassFieldTheory_Finite_LocalReciprocity_AbstractFixedFieldNorm`, `LocalClassFieldTheory_Finite_LocalReciprocity_AbstractFixedFieldUnits`, `LocalClassFieldTheory_Finite_LocalReciprocity_FiniteAbstractFixedField`, `LocalClassFieldTheory_Finite_LocalReciprocity_HenselianValuationBase`, `LocalClassFieldTheory_Finite_LocalReciprocity_LocalClassFieldAxiom`, `LocalClassFieldTheory_Finite_LocalReciprocity_LocalHenselianValuation`, `LocalClassFieldTheory_Finite_LocalReciprocity_SeparableFixedFieldNorm`, `LocalClassFieldTheory_Finite_LocalReciprocity_SeparableUnitsNorm`, `LocalField_Analytic_ContinuousFieldUnitLog`, `LocalField_Analytic_LogExpContinuity`, `LocalField_Analytic_LogExpSeries_PrincipalUnitLog`, `LocalField_Analytic_PrincipalUnitExpLogEquiv`, `LocalField_DiscreteValuationField_MixedCharacteristicStructure_DeepPrincipalUnits`, `LocalField_DiscreteValuationField_MixedCharacteristicStructure_IntegralLattice`, `LocalField_DiscreteValuationField_PadicPowerIndex`, `LocalField_DiscreteValuationField_PowerIndex`, `LocalField_Padic_PrincipalUnits`.
--
--   **Imports.** It imports the bundles `OAIQ244Duke046`, `OAIQ244Duke047` and `OAIQ244Duke048` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ244Duke062`, `OAIQ244Duke063`, `OAIQ244Duke064`, `OAIQ244Duke065`, `OAIQ244Duke066`, `OAIQ244Duke067` and `OAIQ244Duke068`.
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
import Mathlib.Algebra.Group.Equiv.Basic
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
import Mathlib.NumberTheory.Padics.ValuativeRel
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
import Definitions.Def_OAIQ244Duke046
import Definitions.Def_OAIQ244Duke047
import Definitions.Def_OAIQ244Duke048

section
-- module Solutions.OAIQ244_DUKE.AlgebraicNumberTheory_RayClass_Approximation
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.LocalClassFieldTheory.normalizationIntegerRingIsIntegralClosure _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic
attribute [-simp] _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.IsDiscreteValuationRing.addVal_ringEquiv _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.OAI.PrimeDegreePackets.ThetaConstruction.schwartzCM_apply _root_.infinitePlace_mult_smul
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

/-!
# Multiplicative weak approximation for ideles

This file extracts the simultaneous approximation statement needed for ray
class groups. At finitely many
finite places one may prescribe an arbitrary open multiplicative coset and
move a given idele into all of those cosets by a single principal idele.
-/

open scoped NumberField Classical
open NumberField IsDedekindDomain

noncomputable section


variable {K : Type*} [Field K] [NumberField K]

namespace IdeleGroup

@[simp]
theorem modulusOfFinset_support
    (S : Finset (HeightOneSpectrum (𝓞 K))) :
    (modulusOfFinset S).finitePart.support = S := by
  classical
  ext v
  simp [modulusOfFinset, RayClass.Modulus.ofFinite]

end IdeleGroup
end
end

section
-- module Solutions.OAIQ244_DUKE.LocalClassFieldTheory_Finite_LocalReciprocity_SeparableUnitsNorm
attribute [-instance] _root_.ClassFormation.DegreeData.FiniteAmbientFrobeniusFixedFieldTower.ambientRepresentedQuotientFinite _root_.ClassFormation.DegreeData.FrobeniusFixedFieldTower.baseAbsoluteFiniteInstance _root_.ClassFormation.DegreeData.FrobeniusFixedFieldTower.extensionFinite _root_.ClassFormation.DegreeData.FrobeniusFixedFieldTower.extensionNormal _root_.ClassFormation.DegreeData.FrobeniusFixedFieldTower.fieldAbsoluteFiniteInstance _root_.ClassFormation.DegreeData.FrobeniusPowerFixedFieldTower.baseRepresentedAbsoluteFinite _root_.ClassFormation.DegreeData.FrobeniusPowerFixedFieldTower.fieldRepresentedAbsoluteFinite _root_.ClassFormation.DegreeData.FrobeniusPowerFixedFieldTower.relativeRepresentedQuotientFinite _root_.ClassFormation.DegreeData.frobeniusClosure_isTopologicalGroup _root_.ClassFormation.DegreeData.frobeniusElementsMul _root_.ClassFormation.DegreeData.frobeniusElementsSemigroup _root_.ClassFormation.FiniteAbstractField.toFiniteResidueAbstractField_extensionFinite _root_.ClassFormation.FiniteAbstractField.toFiniteResidueAbstractField_extensionNormal _root_.ClassFormation.FiniteCyclicSubextension.instFiniteQuotientSubtypeMemSubgroupFieldExtensionSubgroupField _root_.ClassFormation.FiniteCyclicSubextension.instFintypeQuotientSubtypeMemSubgroupFieldExtensionSubgroupField _root_.ClassFormation.FiniteCyclicSubextension.instNormalSubtypeMemSubgroupFieldExtensionSubgroupField _root_.ClassFormation.FiniteGaloisSubextension.extensionSubgroup_normalInstance _root_.ClassFormation.FiniteGaloisSubextension.extensionSubgroup_over_intermediate_normalInstance _root_.ClassFormation.FiniteGaloisSubextension.intermediateField_normalInstance _root_.ClassFormation.FiniteIntermediateField.galoisRefinement_normal _root_.ClassFormation.FiniteUnramifiedCyclicExtension.instFiniteQuotientSubtypeMemSubgroupBaseFieldExtensionSubgroupField _root_.ClassFormation.FiniteUnramifiedCyclicExtension.instFiniteQuotientSubtypeMemSubgroupFieldExtensionSubgroupField _root_.ClassFormation.FiniteUnramifiedCyclicExtension.instFintypeQuotientSubtypeMemSubgroupFieldExtensionSubgroupField _root_.ClassFormation.FiniteUnramifiedCyclicExtension.instNormalSubtypeMemSubgroupFieldExtensionSubgroupField _root_.ClassFormation.conjugateExtension_normal _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.KummerTheory.finite_finsupp_nsmulQuotient _root_.KummerTheory.finite_sUnit_nthPowerQuotient _root_.KummerTheory.primeCyclotomicBaseFiniteDimensional _root_.KummerTheory.primeCyclotomicBaseIsGalois _root_.LocalClassFieldTheory.finiteGaloisExtensionSubgroupOfEmbedding_normal _root_.LocalClassFieldTheory.finiteGaloisFieldRangeOfEmbedding_finiteDimensional _root_.LocalClassFieldTheory.finiteGaloisFieldRangeOfEmbedding_isGalois _root_.LocalClassFieldTheory.localDecompositionResidueFinite _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitQuotientCarrier_finite _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.residueFieldZModAlgebra _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedIntegralAlgebraContextValuationSubringAlgebra _root_.LocalFieldTheory.DiscreteValuationField.finite_padicInt_finPi_nsmulQuotient _root_.LocalFieldTheory.DiscreteValuationField.finite_padicInt_pi_nsmulQuotient_of_coprime _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_multiplicative_nthPowerQuotient _root_.LocalFieldTheory.finite_nsmulAddQuotient_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.PrimeDegreePackets.boundedRealFields_finite _root_.OAI.PrimeDegreePackets.diagonalLogAction _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionResidueField.instField _root_.RamificationTheory.HilbertRamification.ValuationSubring.inertiaGroup_normal _root_.RamificationTheory.HilbertRamification.ValuationSubring.ramificationGroupInInertiaAut_normal _root_.RamificationTheory.HilbertRamification.ValuationSubring.selectedResidueField.instAlgebra _root_.RayClass.approximationCompletionTopologicalSpace _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.RelativeIdeleGroup.relativeIdeleMulAction _root_.ValuationTheory.DiscreteValuationField.DVF.maximalIdealPowSuccQuotModule _root_.ValuationTheory.DiscreteValuationField.DVF.residueField.field _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.CyclicCohomology.binaryCoefficientFamilyCommGroup _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.LocalClassFieldTheory.normalizationIntegerRingIsIntegralClosure _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.chosenFinitePlaceCompletionAlgebra _root_.chosenFinitePlaceCompletionFiniteDimensional _root_.chosenFinitePlaceLocalizedFiniteDimensional _root_.chosenFinitePlaceLocalizedIsGalois _root_.cyclicPrimeDegreeIntermediate_isGalois _root_.cyclicPrimeSubextension_isGalois _root_.finiteLocalUnitsOpen _root_.finiteNormalClosure_isGalois _root_.relativeAdeleRingIntermediateAlgebra _root_.relativeAdeleRingTopIntermediateAlgebra
attribute [-simp] _root_.ClassFormation.DegreeData.finiteReciprocityCandidate_apply _root_.ClassFormation.DegreeData.finiteReciprocityCandidate_zero _root_.ClassFormation.DegreeData.frobeniusFixedFieldAction_coe _root_.ClassFormation.DegreeData.frobeniusPowerSum_coe _root_.ClassFormation.DegreeData.frobeniusQuotientAction_mk _root_.ClassFormation.DegreeData.frobeniusQuotientRepresentation_apply _root_.ClassFormation.FiniteGaloisSubextension.classFieldCandidate_field _root_.ClassFormation.ValuationData.canonicalUnramifiedNormQuotientValuation_finiteNormClass _root_.ClassFormation.ValuationData.mem_infiniteUnitAddSubgroup_iff _root_.ClassFormation.ValuationData.mem_infiniteUnitNormSubgroup_iff _root_.ClassFormation.ValuationData.unitRepresentation_quotient_mk_apply _root_.ClassFormation.ValuationData.unramifiedNormQuotientValuation_finiteNormClass _root_.ClassFormation.ValuationData.unramifiedReciprocity_equiv_of_generator_apply _root_.ClassFormation.ValuationData.valuationAt_chosenPrimeElement _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.ClassFormation.conjugateStableAction_coe _root_.ClassFormation.cyclicNormClassHom_apply _root_.ClassFormation.extensionFixedRepresentationEquiv_apply_coe _root_.ClassFormation.extensionFixedRepresentationEquiv_symm_apply_coe _root_.ClassFormation.mem_normFilterBasis_iff _root_.IsDiscreteValuationRing.addVal_ringEquiv _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.LocalClassFieldTheory.finiteGaloisUnitsEquivAbstractFixedOfEmbedding_coe _root_.LocalClassFieldTheory.finiteGaloisUnitsEquivAbstractFixed_coe _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.LocalFieldTheory.residueField_algebraMap_residue _root_.OAI.PrimeDegreePackets.ThetaConstruction.schwartzCM_apply _root_.infinitePlace_mult_smul
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

namespace LocalClassFieldTheory
open RamificationTheory KummerTheory

open LocalFieldTheory

open ClassFormation CyclicCohomology

/-!
# Finite local reciprocity: the abstract norm on separable-closure units

The coefficient module in local class field theory is the unit group of a
separable closure.  This file compares the norm defined in the abstract class-formation framework by a
sum over abstract Galois cosets with the ordinary field norm.  The comparison
is proved first for an arbitrary (possibly infinite) Galois ambient field, so
it does not require the ground field to be perfect.
-/

noncomputable section

open scoped BigOperators

variable (K : Type) (Ω : Type) [Field K] [Field Ω] [Algebra K Ω]
  [IsGalois K Ω]

section FiniteGaloisIntermediate

variable (E : IntermediateField K Ω) [FiniteDimensional K E] [IsGalois K E]

/-- The abstract finite norm quotient is the actual multiplicative field
norm quotient, written additively for the abstract class-formation API. -/
def finiteNormQuotientEquivNormQuotient :
    FiniteNormQuotient (galoisAmbientUnitsRep K Ω)
        (closedFixingSubgroup K Ω (⊥ : IntermediateField K Ω))
        (closedFixingSubgroup K Ω E) (fixingSubgroupLeBase K Ω E) ≃+
      Additive (NormQuotient K E) := by
  let S := finiteNormSubgroup (galoisAmbientUnitsRep K Ω)
    (closedFixingSubgroup K Ω (⊥ : IntermediateField K Ω))
    (closedFixingSubgroup K Ω E) (fixingSubgroupLeBase K Ω E)
  let normAdd : Additive Kˣ →+ Additive (NormQuotient K E) :=
    MonoidHom.toAdditive (normClass K E)
  let T := normAdd.ker
  let e := baseUnitsEquivGaloisAmbientFixed K Ω
  have hmap : S.map e.symm.toAddMonoidHom = T := by
    simpa [S, T, normAdd, e] using
      (map_finiteNormSubgroup_eq_additiveNormSubgroup K Ω E).trans
        (additiveNormSubgroup_eq_ker_quotient_map K E)
  have hforward : S ≤ AddSubgroup.comap e.symm.toAddMonoidHom T := by
    intro x hx
    change e.symm x ∈ T
    rw [← hmap]
    exact ⟨x, hx, rfl⟩
  have hinverse : T ≤ AddSubgroup.comap e.toAddMonoidHom S := by
    intro y hy
    change e y ∈ S
    have hy' : y ∈ S.map e.symm.toAddMonoidHom := by
      rw [hmap]
      exact hy
    rcases hy' with ⟨x, hx, hxy⟩
    have heq : e y = x := by
      apply e.symm.injective
      simpa using hxy.symm
    rw [heq]
    exact hx
  let f : (ambientFixedAddSubgroup (galoisAmbientUnitsRep K Ω)
      (closedFixingSubgroup K Ω (⊥ : IntermediateField K Ω)) ⧸ S) →+
      (Additive Kˣ ⧸ T) :=
    QuotientAddGroup.map S T e.symm.toAddMonoidHom hforward
  let g : (Additive Kˣ ⧸ T) →+
      (ambientFixedAddSubgroup (galoisAmbientUnitsRep K Ω)
        (closedFixingSubgroup K Ω (⊥ : IntermediateField K Ω)) ⧸ S) :=
    QuotientAddGroup.map T S e.toAddMonoidHom hinverse
  let modelEquiv :
      (ambientFixedAddSubgroup (galoisAmbientUnitsRep K Ω)
          (closedFixingSubgroup K Ω (⊥ : IntermediateField K Ω)) ⧸ S) ≃+
        (Additive Kˣ ⧸ T) :=
    { toFun := f
      invFun := g
      left_inv := by
        intro q
        refine QuotientAddGroup.induction_on q ?_
        intro x
        change ↑(e (e.symm x)) = (↑x :
          ambientFixedAddSubgroup (galoisAmbientUnitsRep K Ω)
            (closedFixingSubgroup K Ω (⊥ : IntermediateField K Ω)) ⧸ S)
        rw [e.apply_symm_apply]
      right_inv := by
        intro q
        refine QuotientAddGroup.induction_on q ?_
        intro x
        change ↑(e.symm (e x)) = (↑x : Additive Kˣ ⧸ T)
        rw [e.symm_apply_apply]
      map_add' := f.map_add }
  let firstIso : (Additive Kˣ ⧸ T) ≃+ Additive (NormQuotient K E) :=
    QuotientAddGroup.quotientKerEquivOfSurjective normAdd
      (QuotientGroup.mk'_surjective (localNormSubgroup K E))
  exact (finiteNormQuotientConcreteEquiv (galoisAmbientUnitsRep K Ω)
    (closedFixingSubgroup K Ω (⊥ : IntermediateField K Ω))
    (closedFixingSubgroup K Ω E) (fixingSubgroupLeBase K Ω E)).trans
      (modelEquiv.trans firstIso)

/-- The fixed-unit comparison carries the canonical finite norm class to the
canonical field norm class.  The concrete quotient representation remains
private to the proof of this boundary theorem. -/
@[simp]
theorem finiteNormQuotientEquivNormQuotient_finiteNormClass
    (a : ambientFixedAddSubgroup (galoisAmbientUnitsRep K Ω)
      (closedFixingSubgroup K Ω (⊥ : IntermediateField K Ω))) :
    finiteNormQuotientEquivNormQuotient K Ω E
        (finiteNormClass (galoisAmbientUnitsRep K Ω)
          (closedFixingSubgroup K Ω (⊥ : IntermediateField K Ω))
          (closedFixingSubgroup K Ω E) (fixingSubgroupLeBase K Ω E) a) =
      (MonoidHom.toAdditive (normClass K E))
        ((baseUnitsEquivGaloisAmbientFixed K Ω).symm a) := by
  let S := finiteNormSubgroup (galoisAmbientUnitsRep K Ω)
    (closedFixingSubgroup K Ω (⊥ : IntermediateField K Ω))
    (closedFixingSubgroup K Ω E) (fixingSubgroupLeBase K Ω E)
  let normAdd : Additive Kˣ →+ Additive (NormQuotient K E) :=
    MonoidHom.toAdditive (normClass K E)
  let T := normAdd.ker
  let e := baseUnitsEquivGaloisAmbientFixed K Ω
  have hmap : S.map e.symm.toAddMonoidHom = T := by
    simpa [S, T, normAdd, e] using
      (map_finiteNormSubgroup_eq_additiveNormSubgroup K Ω E).trans
        (additiveNormSubgroup_eq_ker_quotient_map K E)
  have hforward : S ≤ AddSubgroup.comap e.symm.toAddMonoidHom T := by
    intro x hx
    change e.symm x ∈ T
    rw [← hmap]
    exact ⟨x, hx, rfl⟩
  simp only [finiteNormQuotientEquivNormQuotient,
    finiteNormQuotientConcreteEquiv_finiteNormClass,
    AddEquiv.trans_apply,
    QuotientAddGroup.quotientKerEquivOfSurjective,
    QuotientAddGroup.quotientKerEquivOfRightInverse]
  change QuotientAddGroup.kerLift normAdd
      (QuotientAddGroup.map S T e.symm.toAddMonoidHom hforward
        (QuotientAddGroup.mk' S a)) = normAdd (e.symm a)
  rw [QuotientAddGroup.map_mk', QuotientAddGroup.kerLift_mk]
  rfl

end FiniteGaloisIntermediate

section EmbeddedFiniteGaloisExtension

variable (L : Type) [Field L] [Algebra K L]
  [FiniteDimensional K L] [IsGalois K L]
  (i : L →ₐ[K] Ω)

attribute [local instance] LocalClassFieldTheory.embeddedFieldRangeFiniteDimensional
attribute [local instance] LocalClassFieldTheory.embeddedFieldRangeIsGalois
/-- For an embedded finite Galois extension `L/K`, the finite norm quotient
in the abstract class formation is the actual quotient `Kˣ/N_{L/K}Lˣ`. -/
def finiteNormQuotientEquivEmbeddedNormQuotient :
    FiniteNormQuotient (galoisAmbientUnitsRep K Ω)
        (closedFixingSubgroup K Ω (⊥ : IntermediateField K Ω))
        (closedFixingSubgroup K Ω (AlgHom.fieldRange i))
        (fixingSubgroupLeBase K Ω (AlgHom.fieldRange i)) ≃+
      Additive (NormQuotient K L) :=
  (finiteNormQuotientEquivNormQuotient K Ω (AlgHom.fieldRange i)).trans
    (MulEquiv.toAdditive
      (normQuotientEquivOfNormSubgroupEq K (AlgHom.fieldRange i) L
        (localNormSubgroup_fieldRange_eq K Ω L i)))

/-- The embedded-extension comparison carries a canonical finite norm class
to the corresponding field norm class, followed by the canonical transport
from the embedded field range to `L`. -/
@[simp]
theorem finiteNormQuotientEquivEmbeddedNormQuotient_finiteNormClass
    (a : ambientFixedAddSubgroup (galoisAmbientUnitsRep K Ω)
      (closedFixingSubgroup K Ω (⊥ : IntermediateField K Ω))) :
    finiteNormQuotientEquivEmbeddedNormQuotient K Ω L i
        (finiteNormClass (galoisAmbientUnitsRep K Ω)
          (closedFixingSubgroup K Ω (⊥ : IntermediateField K Ω))
          (closedFixingSubgroup K Ω (AlgHom.fieldRange i))
          (fixingSubgroupLeBase K Ω (AlgHom.fieldRange i)) a) =
      (MulEquiv.toAdditive
        (normQuotientEquivOfNormSubgroupEq K (AlgHom.fieldRange i) L
          (localNormSubgroup_fieldRange_eq K Ω L i)))
        ((MonoidHom.toAdditive (normClass K (AlgHom.fieldRange i)))
          ((baseUnitsEquivGaloisAmbientFixed K Ω).symm a)) := by
  change (MulEquiv.toAdditive
      (normQuotientEquivOfNormSubgroupEq K (AlgHom.fieldRange i) L
        (localNormSubgroup_fieldRange_eq K Ω L i)))
      (finiteNormQuotientEquivNormQuotient K Ω (AlgHom.fieldRange i)
        (finiteNormClass (galoisAmbientUnitsRep K Ω)
          (closedFixingSubgroup K Ω (⊥ : IntermediateField K Ω))
          (closedFixingSubgroup K Ω (AlgHom.fieldRange i))
          (fixingSubgroupLeBase K Ω (AlgHom.fieldRange i)) a)) = _
  rw [finiteNormQuotientEquivNormQuotient_finiteNormClass]

end EmbeddedFiniteGaloisExtension

end
end LocalClassFieldTheory
end

section
-- module Solutions.OAIQ244_DUKE.LocalClassFieldTheory_Finite_LocalReciprocity_FiniteAbstractFixedField
attribute [-instance] _root_.ClassFormation.DegreeData.FiniteAmbientFrobeniusFixedFieldTower.ambientRepresentedQuotientFinite _root_.ClassFormation.DegreeData.FrobeniusFixedFieldTower.baseAbsoluteFiniteInstance _root_.ClassFormation.DegreeData.FrobeniusFixedFieldTower.extensionFinite _root_.ClassFormation.DegreeData.FrobeniusFixedFieldTower.extensionNormal _root_.ClassFormation.DegreeData.FrobeniusFixedFieldTower.fieldAbsoluteFiniteInstance _root_.ClassFormation.DegreeData.FrobeniusPowerFixedFieldTower.baseRepresentedAbsoluteFinite _root_.ClassFormation.DegreeData.FrobeniusPowerFixedFieldTower.fieldRepresentedAbsoluteFinite _root_.ClassFormation.DegreeData.FrobeniusPowerFixedFieldTower.relativeRepresentedQuotientFinite _root_.ClassFormation.DegreeData.frobeniusClosure_isTopologicalGroup _root_.ClassFormation.DegreeData.frobeniusElementsMul _root_.ClassFormation.DegreeData.frobeniusElementsSemigroup _root_.ClassFormation.FiniteAbstractField.toFiniteResidueAbstractField_extensionFinite _root_.ClassFormation.FiniteAbstractField.toFiniteResidueAbstractField_extensionNormal _root_.ClassFormation.FiniteGaloisSubextension.extensionSubgroup_over_intermediate_normalInstance _root_.ClassFormation.FiniteGaloisSubextension.intermediateField_normalInstance _root_.ClassFormation.FiniteIntermediateField.galoisRefinement_normal _root_.ClassFormation.conjugateExtension_normal _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.KummerTheory.primeCyclotomicBaseIsGalois _root_.LocalClassFieldTheory.finiteGaloisExtensionSubgroupOfEmbedding_normal _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.residueFieldZModAlgebra _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedIntegralAlgebraContextValuationSubringAlgebra _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.LubinTate.compatibleGroupFamiliesGroup _root_.OAI.PrimeDegreePackets.diagonalLogAction _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionResidueField.instField _root_.RamificationTheory.HilbertRamification.ValuationSubring.selectedResidueField.instAlgebra _root_.RayClass.approximationCompletionTopologicalSpace _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.RelativeIdeleGroup.relativeIdeleMulAction _root_.ValuationTheory.DiscreteValuationField.DVF.maximalIdealPowSuccQuotModule _root_.ValuationTheory.DiscreteValuationField.DVF.residueField.field _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.LocalClassFieldTheory.normalizationIntegerRingIsIntegralClosure _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.chosenFinitePlaceCompletionAlgebra _root_.chosenFinitePlaceLocalizedIntegerAlgebra _root_.chosenFinitePlaceLocalizedIsGalois _root_.cyclicPrimeDegreeIntermediate_top_isGalois _root_.finiteLocalUnitsOpen _root_.primeOrderFixedField_isGalois _root_.relativeAdeleRingIntermediateAlgebra _root_.relativeAdeleRingTopIntermediateAlgebra
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

namespace LocalClassFieldTheory
open RamificationTheory KummerTheory CyclicCohomology

open ClassFormation

/-!
# Finite local reciprocity: finite abstract fields inside a separable closure

The abstract fields to which the class field axiom is applied are the open
closed subgroups of the absolute Galois group.  This file turns the explicit
finite-index witness from the abstract class-formation data into the corresponding finite fixed
field.  It is the field-theoretic input needed before the local class-field-axiom theorem can be
applied.
-/

noncomputable section

variable (k Ω : Type) [Field k] [Field Ω] [Algebra k Ω] [IsGalois k Ω]

/-- Passing from an abstract field to its concrete fixed field
and back recovers the original closed subgroup. -/
theorem closedFixingSubgroup_abstractFixedField_eq
    (H : ClosedSubgroup (Gal(Ω / k))) :
    closedFixingSubgroup k Ω (abstractFixedField k Ω H) = H := by
  ext σ
  change σ ∈ (abstractFixedField k Ω H).fixingSubgroup ↔ σ ∈ H
  rw [InfiniteGalois.fixingSubgroup_fixedField H]
  rfl

/-- The quotient group appearing in the abstract class-field-axiom predicate is
canonically the actual Galois group of the two concrete fixed fields. -/
def abstractExtensionQuotientEquivGaloisGroup
    (K L : ClosedSubgroup (Gal(Ω / k)))
    (hLK : L.toSubgroup ≤ K.toSubgroup)
    (hnormal : (extensionSubgroup K L hLK).Normal) :
    letI := hnormal
    K.toSubgroup ⧸ extensionSubgroup K L hLK ≃*
      Gal(abstractRelativeFixedField k Ω hLK / abstractFixedField k Ω K) := by
  letI := hnormal
  letI : (abstractRelativeFixedField k Ω hLK).fixingSubgroup.Normal :=
    abstractRelativeFixingSubgroup_normal k Ω K L hLK hnormal
  let H : ClosedSubgroup (Gal(Ω / abstractFixedField k Ω K)) :=
    closedFixingSubgroup (abstractFixedField k Ω K) Ω
      (abstractRelativeFixedField k Ω hLK)
  letI : H.toSubgroup.Normal := by
    exact abstractRelativeFixingSubgroup_normal k Ω K L hLK hnormal
  exact (abstractExtensionQuotientEquivAmbient
      k Ω K L hLK hnormal).trans
    ((InfiniteGalois.normalAutEquivQuotient H).trans
      (AlgEquiv.autCongr
        (IntermediateField.equivOfEq
          (InfiniteGalois.fixedField_fixingSubgroup
            (abstractRelativeFixedField k Ω hLK)))))

/-- The abstract extension degree is the ordinary degree of the concrete
finite Galois extension represented by the same pair of fixed fields. -/
theorem finiteAbstractExtension_degree_eq_finrank
    (K L : ClosedSubgroup (Gal(Ω / k)))
    (hLK : L.toSubgroup ≤ K.toSubgroup)
    (hnormal : (extensionSubgroup K L hLK).Normal)
    (hKfinite : Finite ((baseField (Gal(Ω / k))).toSubgroup ⧸
      extensionSubgroup (baseField (Gal(Ω / k))) K (le_baseField K)))
    (hLKfinite : Finite
      (K.toSubgroup ⧸ extensionSubgroup K L hLK)) :
    ((DegreeData.FiniteAbstractExtension.ofInclusion L K hLK).degree : ℕ) =
      Module.finrank (abstractFixedField k Ω K)
        (abstractRelativeFixedField k Ω hLK) := by
  let := hnormal
  let : Finite
      (K.toSubgroup ⧸ extensionSubgroup K L hLK) := hLKfinite
  let : FiniteDimensional (abstractFixedField k Ω K)
      (abstractRelativeFixedField k Ω hLK) :=
    abstractRelativeFixedField_finiteDimensional
      k Ω K L hLK hKfinite hLKfinite
  let : IsGalois (abstractFixedField k Ω K)
      (abstractRelativeFixedField k Ω hLK) :=
    abstractRelativeFixedField_isGalois k Ω K L hLK hnormal
  calc
    ((DegreeData.FiniteAbstractExtension.ofInclusion L K hLK).degree : ℕ) =
        (extensionSubgroup K L hLK).index :=
      (DegreeData.FiniteAbstractExtension.ofInclusion L K hLK).extensionSubgroup_index_eq_degree.symm
    _ = Nat.card
        (K.toSubgroup ⧸ extensionSubgroup K L hLK) :=
      Subgroup.index_eq_card (extensionSubgroup K L hLK)
    _ = Nat.card (Gal(abstractRelativeFixedField k Ω hLK / abstractFixedField k Ω K)) :=
      Nat.card_congr
        (abstractExtensionQuotientEquivGaloisGroup
          k Ω K L hLK hnormal).toEquiv
    _ = Module.finrank (abstractFixedField k Ω K)
        (abstractRelativeFixedField k Ω hLK) :=
      IsGalois.card_aut_eq_finrank
        (abstractFixedField k Ω K)
        (abstractRelativeFixedField k Ω hLK)

end
end LocalClassFieldTheory
end

section
-- module Solutions.OAIQ244_DUKE.LocalClassFieldTheory_Finite_LocalReciprocity_AbstractFixedFieldUnits
attribute [-instance] _root_.ClassFormation.DegreeData.FiniteAmbientFrobeniusFixedFieldTower.ambientRepresentedQuotientFinite _root_.ClassFormation.DegreeData.FrobeniusFixedFieldTower.baseAbsoluteFiniteInstance _root_.ClassFormation.DegreeData.FrobeniusFixedFieldTower.extensionFinite _root_.ClassFormation.DegreeData.FrobeniusFixedFieldTower.extensionNormal _root_.ClassFormation.DegreeData.FrobeniusFixedFieldTower.fieldAbsoluteFiniteInstance _root_.ClassFormation.DegreeData.FrobeniusPowerFixedFieldTower.baseRepresentedAbsoluteFinite _root_.ClassFormation.DegreeData.FrobeniusPowerFixedFieldTower.fieldRepresentedAbsoluteFinite _root_.ClassFormation.DegreeData.FrobeniusPowerFixedFieldTower.relativeRepresentedQuotientFinite _root_.ClassFormation.DegreeData.frobeniusClosure_isTopologicalGroup _root_.ClassFormation.DegreeData.frobeniusElementsMul _root_.ClassFormation.DegreeData.frobeniusElementsSemigroup _root_.ClassFormation.FiniteAbstractField.toFiniteResidueAbstractField_extensionFinite _root_.ClassFormation.FiniteAbstractField.toFiniteResidueAbstractField_extensionNormal _root_.ClassFormation.FiniteGaloisSubextension.extensionSubgroup_over_intermediate_normalInstance _root_.ClassFormation.FiniteGaloisSubextension.intermediateField_normalInstance _root_.ClassFormation.FiniteIntermediateField.galoisRefinement_normal _root_.ClassFormation.conjugateExtension_normal _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.KummerTheory.primeCyclotomicBaseIsGalois _root_.LocalClassFieldTheory.finiteGaloisExtensionSubgroupOfEmbedding_normal _root_.LocalClassFieldTheory.finiteGaloisFieldRangeOfEmbedding_isGalois _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.residueFieldZModAlgebra _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedIntegralAlgebraContextValuationSubringAlgebra _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.LubinTate.compatibleGroupFamiliesGroup _root_.OAI.PrimeDegreePackets.diagonalLogAction _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionResidueExtension_normal _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionResidueField.instField _root_.RamificationTheory.HilbertRamification.ValuationSubring.selectedResidueField.instAlgebra _root_.RayClass.approximationCompletionTopologicalSpace _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.RelativeIdeleGroup.relativeIdeleMulAction _root_.ValuationTheory.DiscreteValuationField.DVF.maximalIdealPowSuccQuotModule _root_.ValuationTheory.DiscreteValuationField.DVF.residueField.field _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.isDomain _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.isLocalRing _root_.CyclicCohomology.binaryCoefficientFamilyCommGroup _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.LocalClassFieldTheory.normalizationIntegerRingIsIntegralClosure _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.chosenFinitePlaceCompletionAlgebra _root_.chosenFinitePlaceLocalizedIntegerAlgebra _root_.chosenFinitePlaceLocalizedIsGalois _root_.cyclicPrimeDegreeIntermediate_isGalois _root_.cyclicPrimeDegreeIntermediate_top_isGalois _root_.cyclicPrimeSubextension_isGalois _root_.finiteLocalUnitsOpen _root_.finiteNormalClosure_isGalois _root_.primeOrderFixedField_isGalois _root_.relativeAdeleRingIntermediateAlgebra _root_.relativeAdeleRingTopIntermediateAlgebra
attribute [-simp] _root_.ClassFormation.DegreeData.chosenUnramifiedFrobeniusLift_exponent _root_.ClassFormation.DegreeData.extensionNormalizedDegreeContinuous_apply _root_.ClassFormation.DegreeData.extensionNormalizedDegreeContinuous_toMonoidHom _root_.ClassFormation.DegreeData.extensionNormalizedDegree_frobenius_mul _root_.ClassFormation.DegreeData.finiteReciprocityCandidate_apply _root_.ClassFormation.DegreeData.finiteReciprocityCandidate_zero _root_.ClassFormation.DegreeData.fixedFieldNormalizedDegree_generator _root_.ClassFormation.DegreeData.frobeniusActionConjugate_coe _root_.ClassFormation.DegreeData.frobeniusClosureDegreeInMulNatRange_coe _root_.ClassFormation.DegreeData.frobeniusClosureDegree_generator _root_.ClassFormation.DegreeData.frobeniusExponent_actionConjugate _root_.ClassFormation.DegreeData.frobeniusExponent_chosenDegreeOneFrobeniusElement _root_.ClassFormation.DegreeData.frobeniusExponent_mul _root_.ClassFormation.DegreeData.frobeniusExponent_powerOfDegreeOne _root_.ClassFormation.DegreeData.frobeniusFixedFieldAction_coe _root_.ClassFormation.DegreeData.frobeniusFixedFieldQuotientEquiv_mk _root_.ClassFormation.DegreeData.frobeniusFixedFieldToClosure_apply _root_.ClassFormation.DegreeData.frobeniusFixedField_normalizedDegreeEquiv_apply _root_.ClassFormation.DegreeData.frobeniusLiftDifference_coe _root_.ClassFormation.DegreeData.frobeniusMul_coe _root_.ClassFormation.DegreeData.frobeniusPowerOfDegreeOne_coe _root_.ClassFormation.DegreeData.frobeniusPowerSum_coe _root_.ClassFormation.DegreeData.frobeniusQuotientAction_mk _root_.ClassFormation.DegreeData.frobeniusQuotientRepresentation_apply _root_.ClassFormation.DegreeData.frobeniusRestriction_chosenFiniteReciprocityFrobeniusLift _root_.ClassFormation.DegreeData.frobeniusRestriction_mul _root_.ClassFormation.DegreeData.mem_frobeniusFixedField_iff _root_.ClassFormation.DegreeData.mem_frobeniusFixedSubgroupWithin_iff _root_.ClassFormation.FiniteAbelianSubextension.extensionQuotientMk_apply _root_.ClassFormation.FiniteGaloisSubextension.classFieldCandidate_field _root_.ClassFormation.ValuationData.canonicalUnramifiedNormQuotientValuation_finiteNormClass _root_.ClassFormation.ValuationData.mem_infiniteUnitAddSubgroup_iff _root_.ClassFormation.ValuationData.mem_infiniteUnitNormSubgroup_iff _root_.ClassFormation.ValuationData.unramifiedNormQuotientValuation_finiteNormClass _root_.ClassFormation.ValuationData.unramifiedReciprocity_equiv_of_generator_apply _root_.ClassFormation.ValuationData.valuationAt_chosenPrimeElement _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.ClassFormation.conjugateStableAction_coe _root_.ClassFormation.cyclicNormClassHom_apply _root_.ClassFormation.finiteReciprocityNaturalityConjugation_mk _root_.ClassFormation.mem_normFilterBasis_iff _root_.ClassFormation.relativeConjugateCosetEquiv_mk _root_.IsDiscreteValuationRing.addVal_ringEquiv _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.LocalClassFieldTheory.finiteGaloisUnitsEquivAbstractFixedOfEmbedding_coe _root_.LocalClassFieldTheory.finiteGaloisUnitsEquivAbstractFixed_coe _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.LocalFieldTheory.residueField_algebraMap_residue _root_.OAI.PrimeDegreePackets.ThetaConstruction.schwartzCM_apply _root_.ClassFormation.DegreeData.inertiaConjugationCosetEquiv_mk _root_.infinitePlace_mult_smul
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

namespace LocalClassFieldTheory
open RamificationTheory CyclicCohomology KummerTheory

open LocalFieldTheory

open ClassFormation

/-!
# The local class-field-axiom theorem: units in an abstract finite fixed-field tower

For a finite abstract tower represented by closed subgroups `L ≤ K`, this
file identifies the descended coefficient representation on `A_L` with the
ordinary representation of `Gal(L/K)` on the units of the concrete upper
fixed field.  Both the carrier and the action are compared; the latter is
essential for transporting the actual Tate groups rather than only their
underlying norm quotients.
-/

noncomputable section

open CategoryTheory

variable (k Ω : Type) [Field k] [Field Ω] [Algebra k Ω] [IsGalois k Ω]

/-- Units of the concrete fixed field represented by an arbitrary closed
subgroup, identified directly with the corresponding fixed coefficients. -/
def abstractFixedFieldUnitsEquivGaloisFixed
    (H : ClosedSubgroup (Gal(Ω / k))) :
    Additive (abstractFixedField k Ω H)ˣ ≃+
      ambientFixedAddSubgroup (galoisAmbientUnitsRep k Ω) H where
  toFun x := ⟨intermediateFieldUnitsToGaloisAmbient k Ω
      (abstractFixedField k Ω H) x, by
    intro σ
    apply Additive.ext
    apply Units.ext
    exact (IntermediateField.mem_fixedField_iff H.toSubgroup
      ((Additive.toMul x : (abstractFixedField k Ω H)ˣ) : Ω)).1
        (Additive.toMul x : (abstractFixedField k Ω H)ˣ).1.property σ.1 σ.2⟩
  invFun a := by
    have ha : ((Additive.toMul a.1 : Ωˣ) : Ω) ∈
        abstractFixedField k Ω H := by
      rw [IntermediateField.mem_fixedField_iff]
      intro σ hσ
      have hfixed := a.2 ⟨σ, hσ⟩
      exact congrArg
        (fun z : Additive Ωˣ => ((Additive.toMul z : Ωˣ) : Ω)) hfixed
    let y₀ : abstractFixedField k Ω H :=
      ⟨((Additive.toMul a.1 : Ωˣ) : Ω), ha⟩
    have hy₀ : y₀ ≠ 0 := by
      intro h
      have h' : ((Additive.toMul a.1 : Ωˣ) : Ω) = 0 :=
        congrArg (abstractFixedField k Ω H).val h
      exact (Additive.toMul a.1 : Ωˣ).ne_zero h'
    exact Additive.ofMul (Units.mk0 y₀ hy₀)
  left_inv x := by
    apply Additive.ext
    apply Units.ext
    rfl
  right_inv a := by
    apply Subtype.ext
    apply Additive.ext
    apply Units.ext
    rfl
  map_add' _ _ := by
    apply Subtype.ext
    rfl

omit [IsGalois k Ω] in
/-- States the theorem `abstractFixedFieldUnitsEquivGaloisFixed_coe`. -/
@[simp]
theorem abstractFixedFieldUnitsEquivGaloisFixed_coe
    (H : ClosedSubgroup (Gal(Ω / k)))
    (x : Additive (abstractFixedField k Ω H)ˣ) :
    ((abstractFixedFieldUnitsEquivGaloisFixed k Ω H x).1 :
        Additive Ωˣ) =
      intermediateFieldUnitsToGaloisAmbient k Ω
        (abstractFixedField k Ω H) x :=
  rfl

/-- Scalar extension from the lower fixed field does not change the
underlying upper field or its unit group. -/
def abstractRelativeFixedFieldUnitsEquivGaloisFixed
    (K L : ClosedSubgroup (Gal(Ω / k)))
    (hLK : L.toSubgroup ≤ K.toSubgroup) :
    Additive (abstractRelativeFixedField k Ω hLK)ˣ ≃+
      ambientFixedAddSubgroup (galoisAmbientUnitsRep k Ω) L := by
  change Additive (abstractFixedField k Ω L)ˣ ≃+ _
  exact abstractFixedFieldUnitsEquivGaloisFixed k Ω L

omit [IsGalois k Ω] in
/-- States the theorem `abstractRelativeFixedFieldUnitsEquivGaloisFixed_coe`. -/
@[simp]
theorem abstractRelativeFixedFieldUnitsEquivGaloisFixed_coe
    (K L : ClosedSubgroup (Gal(Ω / k)))
    (hLK : L.toSubgroup ≤ K.toSubgroup)
    (x : Additive (abstractRelativeFixedField k Ω hLK)ˣ) :
    ((abstractRelativeFixedFieldUnitsEquivGaloisFixed
        k Ω K L hLK x).1 : Additive Ωˣ) =
      intermediateFieldUnitsToGaloisAmbient k Ω
        (abstractFixedField k Ω L) x :=
  rfl

/-- Carrier comparison between the descended class-formation representation and
the actual unit group of the upper concrete fixed field. -/
def abstractExtensionFixedRepresentationUnitsEquiv
    (K L : ClosedSubgroup (Gal(Ω / k)))
    (hLK : L.toSubgroup ≤ K.toSubgroup)
    (hnormal : (extensionSubgroup K L hLK).Normal) :
    (extensionFixedRepresentation (galoisAmbientUnitsRep k Ω)
        K L hLK hnormal).V ≃+
      Additive (abstractRelativeFixedField k Ω hLK)ˣ :=
  (extensionFixedRepresentationEquiv (galoisAmbientUnitsRep k Ω)
      K L hLK hnormal).trans
    (abstractRelativeFixedFieldUnitsEquivGaloisFixed
      k Ω K L hLK).symm

omit [IsGalois k Ω] in
/-- States the theorem `abstractRelativeUnitsEquiv_extensionUnitsEquiv`. -/
@[simp]
theorem abstractRelativeUnitsEquiv_extensionUnitsEquiv
    (K L : ClosedSubgroup (Gal(Ω / k)))
    (hLK : L.toSubgroup ≤ K.toSubgroup)
    (hnormal : (extensionSubgroup K L hLK).Normal)
    (x : (extensionFixedRepresentation (galoisAmbientUnitsRep k Ω)
      K L hLK hnormal).V) :
    abstractRelativeFixedFieldUnitsEquivGaloisFixed k Ω K L hLK
        (abstractExtensionFixedRepresentationUnitsEquiv
          k Ω K L hLK hnormal x) =
      extensionFixedRepresentationEquiv
        (galoisAmbientUnitsRep k Ω) K L hLK hnormal x := by
  exact (abstractRelativeFixedFieldUnitsEquivGaloisFixed
    k Ω K L hLK).apply_symm_apply
      (extensionFixedRepresentationEquiv
        (galoisAmbientUnitsRep k Ω) K L hLK hnormal x)

/-- On a quotient representative, the concrete relative Galois
automorphism is restriction of the same ambient automorphism. -/
theorem abstractExtensionQuotientEquivGaloisGroup_mk_apply_val
    (K L : ClosedSubgroup (Gal(Ω / k)))
    (hLK : L.toSubgroup ≤ K.toSubgroup)
    (hnormal : (extensionSubgroup K L hLK).Normal)
    (σ : K.toSubgroup)
    (x : abstractRelativeFixedField k Ω hLK) :
    letI := hnormal
    σ.1 (x : Ω) =
      (((abstractExtensionQuotientEquivGaloisGroup
          k Ω K L hLK hnormal
          (QuotientGroup.mk' (extensionSubgroup K L hLK) σ)) x :
        abstractRelativeFixedField k Ω hLK) : Ω) := by
  let := hnormal
  let : (abstractRelativeFixedField k Ω hLK).fixingSubgroup.Normal :=
    abstractRelativeFixingSubgroup_normal k Ω K L hLK hnormal
  let H : ClosedSubgroup (Gal(Ω / abstractFixedField k Ω K)) :=
    closedFixingSubgroup (abstractFixedField k Ω K) Ω
      (abstractRelativeFixedField k Ω hLK)
  let : H.toSubgroup.Normal :=
    abstractRelativeFixingSubgroup_normal k Ω K L hLK hnormal
  have hq :
      abstractExtensionQuotientEquivAmbient k Ω K L hLK hnormal
          (QuotientGroup.mk' (extensionSubgroup K L hLK) σ) =
        QuotientGroup.mk'
          (abstractRelativeFixedField k Ω hLK).fixingSubgroup
          (abstractSubgroupEquivGaloisGroup k Ω K σ) := by
    rfl
  rw [abstractExtensionQuotientEquivGaloisGroup, MulEquiv.trans_apply, hq,
    MulEquiv.trans_apply]
  change σ.1 (x : Ω) =
    ((((IntermediateField.equivOfEq
      (InfiniteGalois.fixedField_fixingSubgroup
        (abstractRelativeFixedField k Ω hLK))).autCongr
      (InfiniteGalois.normalAutEquivQuotient
        (closedFixingSubgroup (abstractFixedField k Ω K) Ω
          (abstractRelativeFixedField k Ω hLK))
        ((abstractSubgroupEquivGaloisGroup k Ω K σ :
            Gal(Ω / abstractFixedField k Ω K)) :
          Gal(Ω / abstractFixedField k Ω K) ⧸
            (abstractRelativeFixedField k Ω hLK).fixingSubgroup))) x :
      abstractRelativeFixedField k Ω hLK) : Ω)
  rw [InfiniteGalois.normalAutEquivQuotient_apply,
    AlgEquiv.autCongr_apply]
  simp only [AlgEquiv.trans_apply, IntermediateField.equivOfEq_symm,
    IntermediateField.equivOfEq_apply]
  change σ.1 (x : Ω) =
    (((AlgEquiv.restrictNormalHom
      (IntermediateField.fixedField H.toSubgroup)
      (abstractSubgroupEquivGaloisGroup k Ω K σ))
      ⟨(x : Ω), _⟩ : IntermediateField.fixedField H.toSubgroup) : Ω)
  rw [AlgEquiv.restrictNormalHom_apply]
  rfl

/-- The abstract coset action on an upper fixed-field unit is the ordinary
action of the corresponding concrete relative Galois automorphism. -/
theorem relativeCosetAction_abstractRelativeFixedFieldUnit_val
    (K L : ClosedSubgroup (Gal(Ω / k)))
    (hLK : L.toSubgroup ≤ K.toSubgroup)
    (hnormal : (extensionSubgroup K L hLK).Normal)
    (x : Additive (abstractRelativeFixedField k Ω hLK)ˣ)
    (q : K.toSubgroup ⧸ extensionSubgroup K L hLK) :
    letI := hnormal
    ((Additive.toMul
      (relativeCosetAction (galoisAmbientUnitsRep k Ω)
        K L hLK
        (abstractRelativeFixedFieldUnitsEquivGaloisFixed
          k Ω K L hLK x) q) : Ωˣ) : Ω) =
      (((Additive.toMul
        ((Rep.ofAlgebraAutOnUnits (abstractFixedField k Ω K)
          (abstractRelativeFixedField k Ω hLK)).ρ
            (abstractExtensionQuotientEquivGaloisGroup
              k Ω K L hLK hnormal q) x) :
          (abstractRelativeFixedField k Ω hLK)ˣ) :
        abstractRelativeFixedField k Ω hLK) : Ω) := by
  let := hnormal
  refine Quotient.inductionOn' q ?_
  intro σ
  rw [relativeCosetAction_mk]
  change σ.1 ((Additive.toMul x :
      (abstractRelativeFixedField k Ω hLK)ˣ) : Ω) = _
  exact abstractExtensionQuotientEquivGaloisGroup_mk_apply_val
    k Ω K L hLK hnormal σ
      (Additive.toMul x : (abstractRelativeFixedField k Ω hLK)ˣ)

/-- The carrier comparison intertwines the descended quotient action with
the actual relative Galois action. -/
theorem abstractExtensionFixedRepresentationUnitsEquiv_action
    (K L : ClosedSubgroup (Gal(Ω / k)))
    (hLK : L.toSubgroup ≤ K.toSubgroup)
    (hnormal : (extensionSubgroup K L hLK).Normal)
    (q : K.toSubgroup ⧸ extensionSubgroup K L hLK)
    (x : (extensionFixedRepresentation (galoisAmbientUnitsRep k Ω)
      K L hLK hnormal).V) :
    letI := hnormal
    abstractExtensionFixedRepresentationUnitsEquiv k Ω K L hLK hnormal
        ((extensionFixedRepresentation (galoisAmbientUnitsRep k Ω)
          K L hLK hnormal).ρ q x) =
      (Rep.ofAlgebraAutOnUnits (abstractFixedField k Ω K)
        (abstractRelativeFixedField k Ω hLK)).ρ
          (abstractExtensionQuotientEquivGaloisGroup
            k Ω K L hLK hnormal q)
          (abstractExtensionFixedRepresentationUnitsEquiv
            k Ω K L hLK hnormal x) := by
  let := hnormal
  let eFixed := abstractRelativeFixedFieldUnitsEquivGaloisFixed
    k Ω K L hLK
  apply eFixed.injective
  rw [abstractRelativeUnitsEquiv_extensionUnitsEquiv]
  apply Subtype.ext
  apply Additive.ext
  apply Units.ext
  have haction := extensionFixedRepresentation_action_coe
    (galoisAmbientUnitsRep k Ω) K L hLK hnormal q x
  change
    ((Additive.toMul
      ((extensionFixedRepresentation (galoisAmbientUnitsRep k Ω)
        K L hLK hnormal).ρ q x).1 : Ωˣ) : Ω) = _
  rw [haction]
  rw [← abstractRelativeUnitsEquiv_extensionUnitsEquiv
    k Ω K L hLK hnormal x]
  exact relativeCosetAction_abstractRelativeFixedFieldUnit_val
    k Ω K L hLK hnormal
      (abstractExtensionFixedRepresentationUnitsEquiv
        k Ω K L hLK hnormal x) q

/-- Representation-level form of the fixed-field unit comparison.  The
concrete unit representation is reindexed along the canonical isomorphism
from the abstract class-formation quotient to the actual relative Galois group. -/
def abstractExtensionFixedRepresentationIsoUnitsRes
    (K L : ClosedSubgroup (Gal(Ω / k)))
    (hLK : L.toSubgroup ≤ K.toSubgroup)
    (hnormal : (extensionSubgroup K L hLK).Normal) :
    letI := hnormal
    extensionFixedRepresentation (galoisAmbientUnitsRep k Ω)
        K L hLK hnormal ≅
      Rep.res
        (abstractExtensionQuotientEquivGaloisGroup
          k Ω K L hLK hnormal).toMonoidHom
        (Rep.ofAlgebraAutOnUnits (abstractFixedField k Ω K)
          (abstractRelativeFixedField k Ω hLK)) := by
  letI := hnormal
  let e := abstractExtensionFixedRepresentationUnitsEquiv
    k Ω K L hLK hnormal
  refine Rep.mkIso (Representation.Equiv.mk e.toIntLinearEquiv ?_)
  intro q
  apply LinearMap.ext
  intro x
  exact abstractExtensionFixedRepresentationUnitsEquiv_action
    k Ω K L hLK hnormal q x

end
end LocalClassFieldTheory
end

section
-- module Solutions.OAIQ244_DUKE.LocalClassFieldTheory_Finite_LocalReciprocity_LocalClassFieldAxiom
attribute [-instance] _root_.ClassFormation.DegreeData.FiniteAmbientFrobeniusFixedFieldTower.ambientRepresentedQuotientFinite _root_.ClassFormation.DegreeData.FrobeniusFixedFieldTower.baseAbsoluteFiniteInstance _root_.ClassFormation.DegreeData.FrobeniusFixedFieldTower.extensionFinite _root_.ClassFormation.DegreeData.FrobeniusFixedFieldTower.extensionNormal _root_.ClassFormation.DegreeData.FrobeniusFixedFieldTower.fieldAbsoluteFiniteInstance _root_.ClassFormation.DegreeData.FrobeniusPowerFixedFieldTower.baseRepresentedAbsoluteFinite _root_.ClassFormation.DegreeData.FrobeniusPowerFixedFieldTower.fieldRepresentedAbsoluteFinite _root_.ClassFormation.DegreeData.FrobeniusPowerFixedFieldTower.relativeRepresentedQuotientFinite _root_.ClassFormation.DegreeData.frobeniusClosure_isTopologicalGroup _root_.ClassFormation.DegreeData.frobeniusElementsMul _root_.ClassFormation.DegreeData.frobeniusElementsSemigroup _root_.ClassFormation.FiniteAbstractField.toFiniteResidueAbstractField_extensionFinite _root_.ClassFormation.FiniteAbstractField.toFiniteResidueAbstractField_extensionNormal _root_.ClassFormation.FiniteGaloisSubextension.extensionSubgroup_over_intermediate_normalInstance _root_.ClassFormation.FiniteGaloisSubextension.intermediateField_normalInstance _root_.ClassFormation.FiniteIntermediateField.galoisRefinement_normal _root_.ClassFormation.conjugateExtension_normal _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.KummerTheory.primeCyclotomicBaseIsGalois _root_.LocalClassFieldTheory.finiteGaloisExtensionSubgroupOfEmbedding_normal _root_.LocalClassFieldTheory.finiteGaloisFieldRangeOfEmbedding_isGalois _root_.LocalClassFieldTheory.localDecompositionResidueFintype _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.residueFieldZModAlgebra _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedIntegralAlgebraContextValuationSubringAlgebra _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.LubinTate.compatibleGroupFamiliesGroup _root_.OAI.PrimeDegreePackets.diagonalLogAction _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionResidueExtension_normal _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionResidueField.instField _root_.RamificationTheory.HilbertRamification.ValuationSubring.inertiaGroup_normal _root_.RamificationTheory.HilbertRamification.ValuationSubring.ramificationGroupInInertiaAut_normal _root_.RamificationTheory.HilbertRamification.ValuationSubring.selectedResidueField.instAlgebra _root_.RayClass.approximationCompletionTopologicalSpace _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.RelativeIdeleGroup.relativeIdeleMulAction _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.LocalClassFieldTheory.normalizationIntegerRingIsIntegralClosure _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.chosenFinitePlaceCompletionAlgebra _root_.chosenFinitePlaceLocalizedIntegerAlgebra _root_.chosenFinitePlaceLocalizedIsGalois _root_.cyclicPrimeDegreeIntermediate_isGalois _root_.cyclicPrimeSubextension_isGalois _root_.finiteLocalUnitsOpen _root_.finiteNormalClosure_isGalois _root_.relativeAdeleRingIntermediateAlgebra _root_.relativeAdeleRingTopIntermediateAlgebra
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

namespace LocalClassFieldTheory
open CyclicCohomology ClassFormation

open LocalFieldTheory

/-!
# The local multiplicative group satisfies the class-field axiom

For a finite cyclic abstract tower `L / K / k`, the closed subgroups are
replaced by their concrete fixed fields.  The lower fixed field is finite
over the local ground field and the upper fixed field is finite Galois over
it.  The finite-tower form of the local class-field-axiom theorem therefore
applies.  The fixed unit representation and cyclic Tate-complex comparisons
then transport its two cardinality statements back to the abstract
class-field-axiom predicate.
-/

noncomputable section

open CategoryTheory

/-- **The local class-field-axiom theorem, abstract class-field-axiom form.**

For any Galois ambient field over a nonarchimedean local field, its ambient
unit representation satisfies the abstract class-field-axiom predicate.
The predicate ranges only over towers whose lower field is finite over the
distinguished base, in the fixed-separable-closure model. -/
theorem galoisAmbientUnits_satisfiesClassFieldAxiom
    (k Ω : Type) [Field k] [Field Ω] [Algebra k Ω] [IsGalois k Ω]
    [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] :
    SatisfiesClassFieldAxiom (galoisAmbientUnitsRep k Ω) := by
  rintro ⟨K, hKfinite⟩
  rintro ⟨L, hLK, hnormal, hfinite, g, hg⟩
  let := hKfinite
  let := hnormal
  let := hfinite
  let Q := K.toSubgroup ⧸ extensionSubgroup K L hLK
  let : Fintype Q := Fintype.ofFinite Q
  let F := abstractFixedField k Ω K
  let E := abstractRelativeFixedField k Ω hLK
  let : FiniteDimensional k F :=
    abstractFixedField_finiteDimensional k Ω K hKfinite
  let : FiniteDimensional F E :=
    abstractRelativeFixedField_finiteDimensional
      k Ω K L hLK hKfinite hfinite
  let : IsGalois F E :=
    abstractRelativeFixedField_isGalois k Ω K L hLK hnormal
  let eQ : Q ≃* Gal(E / F) :=
    abstractExtensionQuotientEquivGaloisGroup k Ω K L hLK hnormal
  let g' : Gal(E / F) := eQ g
  have hg' : ∀ σ : Gal(E / F), σ ∈ Subgroup.zpowers g' :=
    map_cyclicGenerator eQ g hg
  have hUnitsTateCard := finiteTowerUnits_tate_card_of_generator k F E g' hg'

  let : IsCyclic Q := CyclicCohomology.isCyclic_of_generator g hg
  let : CommGroup Q := IsCyclic.commGroup
  let : IsCyclic (Gal(E / F)) :=
    CyclicCohomology.isCyclic_of_generator g' hg'
  let : CommGroup (Gal(E / F)) := IsCyclic.commGroup
  let M := extensionFixedRepresentation
    (galoisAmbientUnitsRep k Ω) K L hLK hnormal
  let U := Rep.ofAlgebraAutOnUnits F E
  let eM : M ≅
      Rep.res eQ.toMonoidHom U :=
    abstractExtensionFixedRepresentationIsoUnitsRes
      k Ω K L hLK hnormal
  let eH0 :
      (Rep.FiniteCyclicGroup.normHomCompSub M g).homology ≅
        (Rep.FiniteCyclicGroup.normHomCompSub U g').homology :=
    (normHomCompSubHomologyIsoOfRepIso eM g) ≪≫
      normHomCompSubHomologyResEquivIso eQ U g
  let eHm1 :
      (Rep.FiniteCyclicGroup.subCompNormHom M g).homology ≅
        (Rep.FiniteCyclicGroup.subCompNormHom U g').homology :=
    (subCompNormHomHomologyIsoOfRepIso eM g) ≪≫
      subCompNormHomHomologyResEquivIso eQ U g
  let eTateH0 :
      tateCohomology M 0 ≅ tateCohomology U 0 :=
    TateCohomology.isoFiniteCyclicZero M g hg ≪≫ eH0 ≪≫
      (TateCohomology.isoFiniteCyclicZero U g' hg').symm
  let eTateHm1 :
      tateCohomology M (-1) ≅ tateCohomology U (-1) :=
    TateCohomology.isoFiniteCyclicNegOne M g hg ≪≫ eHm1 ≪≫
      (TateCohomology.isoFiniteCyclicNegOne U g' hg').symm
  let : Finite (tateCohomology U 0) :=
    hUnitsTateCard.finiteH0
  have hUTateMinusOneZero :
      Limits.IsZero (tateCohomology U (-1)) :=
    hilbert90_unitsTateHminusOne_isZero F E g' hg'
  let : Subsingleton (tateCohomology U (-1)) :=
    ModuleCat.subsingleton_of_isZero hUTateMinusOneZero
  let : Finite (tateCohomology U (-1)) := by infer_instance
  let : Finite (tateCohomology M 0) :=
    Finite.of_equiv (tateCohomology U 0) eTateH0.symm.toLinearEquiv.toEquiv
  let : Finite (tateCohomology M (-1)) :=
    Finite.of_equiv (tateCohomology U (-1)) eTateHm1.symm.toLinearEquiv.toEquiv
  have hH0actual :
      Nat.card (tateCohomology U 0) =
        Module.finrank F E :=
    hUnitsTateCard.cardH0
  have hHm1actual :
      Nat.card (tateCohomology U (-1)) = 1 :=
    hUnitsTateCard.cardHminusOne
  refine
    { finiteTateHZero := by
        change Finite (tateCohomology M 0)
        infer_instance
      finiteTateHMinusOne := by
        change Finite (tateCohomology M (-1))
        infer_instance
      tateHZero_card := ?_
      tateHMinusOne_card := ?_ }
  · change Nat.card
      (tateCohomology M 0) =
        ((DegreeData.FiniteAbstractExtension.ofInclusion L K hLK).degree : ℕ)
    calc
      Nat.card (tateCohomology M 0) =
          Nat.card (tateCohomology U 0) :=
        Nat.card_congr eTateH0.toLinearEquiv.toEquiv
      _ = Module.finrank F E := hH0actual
      _ = ((DegreeData.FiniteAbstractExtension.ofInclusion L K hLK).degree : ℕ) :=
        (finiteAbstractExtension_degree_eq_finrank
          k Ω K L hLK hnormal hKfinite hfinite).symm
  · change Nat.card
      (tateCohomology M (-1)) = 1
    calc
      Nat.card (tateCohomology M (-1)) =
          Nat.card (tateCohomology U (-1)) :=
        Nat.card_congr eTateHm1.toLinearEquiv.toEquiv
      _ = 1 := hHm1actual

/-- The coefficient module A = (kˢᵉᵖ)ˣ satisfies the abstract
class-field axiom.  This is the separable-closure specialization used for local
reciprocity. -/
theorem separableClosureUnits_isClassFormation
    (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] :
    SatisfiesClassFieldAxiom
      (galoisAmbientUnitsRep k (SeparableClosure k)) :=
  galoisAmbientUnits_satisfiesClassFieldAxiom k (SeparableClosure k)

end
end LocalClassFieldTheory
end

section
-- module Solutions.OAIQ244_DUKE.LocalClassFieldTheory_Finite_LocalReciprocity_HenselianValuationBase
attribute [-instance] _root_.ClassFormation.DegreeData.FrobeniusFixedFieldTower.baseAbsoluteFiniteInstance _root_.ClassFormation.DegreeData.FrobeniusFixedFieldTower.fieldAbsoluteFiniteInstance _root_.ClassFormation.DegreeData.FrobeniusPowerFixedFieldTower.baseRepresentedAbsoluteFinite _root_.ClassFormation.DegreeData.FrobeniusPowerFixedFieldTower.fieldRepresentedAbsoluteFinite _root_.ClassFormation.FiniteUnramifiedCyclicExtension.instFiniteQuotientSubtypeMemSubgroupBaseFieldExtensionSubgroupField _root_.ClassFormation.instIsAddTorsionFreeZHat _root_.ClassFormation.instIsMulTorsionFreeMultiplicativeZHat _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.KummerTheory.primeCyclotomicBaseIsGalois _root_.LocalClassFieldTheory.finiteGaloisExtensionSubgroupOfEmbedding_normal _root_.LocalClassFieldTheory.finiteGaloisFieldRangeOfEmbedding_isGalois _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.residueFieldZModAlgebra _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedIntegralAlgebraContextValuationSubringAlgebra _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionResidueExtension_normal _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionResidueField.instField _root_.RamificationTheory.HilbertRamification.ValuationSubring.selectedResidueField.instAlgebra _root_.RayClass.approximationCompletionTopologicalSpace _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.residueField.field _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.LocalClassFieldTheory.normalizationIntegerRingIsIntegralClosure _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.chosenFinitePlaceCompletionAlgebra _root_.chosenFinitePlaceLocalizedIsGalois _root_.cyclicPrimeDegreeIntermediate_isGalois _root_.cyclicPrimeSubextension_isGalois _root_.finiteLocalUnitsOpen _root_.finiteNormalClosure_isGalois _root_.relativeAdeleRingIntermediateAlgebra _root_.relativeAdeleRingTopIntermediateAlgebra
attribute [-simp] _root_.ClassFormation.DegreeData.extensionNormalizedDegreeContinuous_apply _root_.ClassFormation.DegreeData.extensionNormalizedDegreeContinuous_toMonoidHom _root_.ClassFormation.DegreeData.extensionNormalizedDegree_frobenius_mul _root_.ClassFormation.DegreeData.fixedFieldNormalizedDegree_generator _root_.ClassFormation.DegreeData.frobeniusActionConjugate_coe _root_.ClassFormation.DegreeData.frobeniusClosureDegreeInMulNatRange_coe _root_.ClassFormation.DegreeData.frobeniusClosureDegree_generator _root_.ClassFormation.DegreeData.frobeniusFixedFieldAction_coe _root_.ClassFormation.DegreeData.frobeniusFixedField_normalizedDegreeEquiv_apply _root_.ClassFormation.DegreeData.frobeniusLiftDifference_coe _root_.ClassFormation.DegreeData.frobeniusMul_coe _root_.ClassFormation.DegreeData.frobeniusPowerOfDegreeOne_coe _root_.ClassFormation.DegreeData.frobeniusPowerSum_coe _root_.ClassFormation.DegreeData.frobeniusQuotientAction_mk _root_.ClassFormation.DegreeData.frobeniusQuotientRepresentation_apply _root_.ClassFormation.FiniteGaloisSubextension.classFieldCandidate_field _root_.ClassFormation.ValuationData.canonicalUnramifiedNormQuotientValuation_finiteNormClass _root_.ClassFormation.ValuationData.canonicalValueQuotientHom_mk _root_.ClassFormation.ValuationData.canonicalValueReduction_one _root_.ClassFormation.ValuationData.mem_infiniteUnitAddSubgroup_iff _root_.ClassFormation.ValuationData.mem_infiniteUnitNormSubgroup_iff _root_.ClassFormation.ValuationData.unitRepresentation_quotient_mk_apply _root_.ClassFormation.ValuationData.unramifiedNormQuotientValuation_finiteNormClass _root_.ClassFormation.ValuationData.valuationAt_chosenPrimeElement _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.ClassFormation.conjugateStableAction_coe _root_.ClassFormation.cyclicNormClassHom_apply _root_.ClassFormation.extensionFixedRepresentationEquiv_apply_coe _root_.ClassFormation.extensionFixedRepresentationEquiv_symm_apply_coe _root_.ClassFormation.mem_normFilterBasis_iff _root_.ClassFormation.toZModPow_zHatToPadicInt _root_.ClassFormation.zHatPowNat_apply_toAdd _root_.ClassFormation.zHatPowNat_one _root_.ClassFormation.zHatReductionMul_apply_toAdd _root_.ClassFormation.zHatReductionRingHom_apply _root_.ClassFormation.zHatRingEquivProfiniteIntegerPrimeProduct_apply _root_.ClassFormation.zHatToPadicInt_intCast _root_.ClassFormation.zHatToProfiniteIntegerPrimeProduct_apply _root_.ClassFormation.zHatToProfiniteIntegerPrimeProduct_intCast _root_.ClassFormation.zHatUnitsContinuousMulEquivPrimeProduct_coe_apply _root_.IsDiscreteValuationRing.addVal_ringEquiv _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.KummerTheory.torsionQuotientEquivOfZHatMulDecomposition_mk _root_.KummerTheory.zHatUnitsContinuousMulEquivPrimeProduct_rationalCyclotomicCharacter _root_.LocalClassFieldTheory.abstractFixedFieldUnitsEquivGaloisFixed_coe _root_.LocalClassFieldTheory.abstractRelativeFixedFieldUnitsEquivGaloisFixed_coe _root_.LocalClassFieldTheory.abstractRelativeUnitsEquiv_extensionUnitsEquiv _root_.LocalClassFieldTheory.finiteGaloisUnitsEquivAbstractFixedOfEmbedding_coe _root_.LocalClassFieldTheory.finiteGaloisUnitsEquivAbstractFixed_coe _root_.LocalClassFieldTheory.finiteResidueFrobeniusFromZHat_apply _root_.LocalClassFieldTheory.finiteResidueFrobeniusFromZHat_one _root_.LocalClassFieldTheory.residueAbsoluteDegreeIn_frobenius _root_.LocalClassFieldTheory.residueAbsoluteFrobenius_one _root_.LocalClassFieldTheory.residueFrobeniusToLimit_apply_component _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.OAI.PrimeDegreePackets.ThetaConstruction.schwartzCM_apply _root_.infinitePlace_mult_smul
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

namespace LocalClassFieldTheory
open RamificationTheory KummerTheory

open LocalFieldTheory

open ClassFormation

/-!
# Finite local reciprocity: the value group of the local henselian valuation

The normalized valuation of the base local field is transported to the
actual fixed coefficient group in the separable closure and then embedded
in `ℤ̂`.  Its range is proved to be exactly the ordinary integers inside
`ℤ̂`, and the quotients by `nℤ` are identified with `ZMod n`.  These are the
source-producing parts of the Henselian valuation condition.
-/

noncomputable section

variable (K : Type) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]

abbrev A_p1 : Rep ℤ (G_p2 K) :=
  galoisAmbientUnitsRep K (SeparableClosure K)

/-- `Kˣ` is the coefficient group fixed by the distinguished base subgroup
of the absolute separable Galois group. -/
def baseFieldUnitsEquiv :
    Additive Kˣ ≃+ ambientFixedAddSubgroup (A_p1 K) (baseField (G_p2 K)) :=
  (baseUnitsEquivGaloisAmbientFixed K (SeparableClosure K)).trans
    (AddEquiv.addSubgroupCongr
      (congrArg (ambientFixedAddSubgroup (A_p1 K))
        (closedFixingSubgroup_bot_eq_baseField K (SeparableClosure K))))

omit [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K] in
/-- States the theorem `baseFieldUnitsEquiv_val`. -/
@[simp]
theorem baseFieldUnitsEquiv_val (x : Kˣ) :
    ((Additive.toMul
      ((baseFieldUnitsEquiv K (Additive.ofMul x)).1 :
        Additive (SeparableClosure K)ˣ) : (SeparableClosure K)ˣ) :
      SeparableClosure K) = algebraMap K (SeparableClosure K) (x : K) := by
  change
    ((Additive.toMul
      ((baseUnitsEquivGaloisAmbientFixed K (SeparableClosure K)
          (Additive.ofMul x)).1 :
        Additive (SeparableClosure K)ˣ) : (SeparableClosure K)ˣ) :
      SeparableClosure K) = algebraMap K (SeparableClosure K) (x : K)
  exact baseUnitsEquivGaloisAmbientFixed_val K (SeparableClosure K) x

/-- The normalized valuation `v_K : Kˣ → ℤ`, embedded in `ℤ̂` and written on
the actual fixed coefficient group. -/
def localBaseValuation :
    ambientFixedAddSubgroup (A_p1 K) (baseField (G_p2 K)) →+ ZHat :=
  (Int.castRingHom ZHat).toAddMonoidHom.comp
    ((LocalFieldTheory.IsNonarchimedeanLocalField.valuationMap K).comp
      (baseFieldUnitsEquiv K).symm.toAddMonoidHom)

/-- States the theorem `localBaseValuation_baseFieldUnitsEquiv`. -/
@[simp]
theorem localBaseValuation_baseFieldUnitsEquiv (x : Additive Kˣ) :
    localBaseValuation K (baseFieldUnitsEquiv K x) =
      Int.castRingHom ZHat
        (LocalFieldTheory.IsNonarchimedeanLocalField.valuationMap K x) := by
  simp [localBaseValuation]

/-- The value group is exactly the image of the ordinary integers in the
profinite integers. -/
theorem localBaseValuation_range :
    (localBaseValuation K).range =
      (Int.castRingHom ZHat).toAddMonoidHom.range := by
  apply le_antisymm
  · rintro z ⟨x, rfl⟩
    exact ⟨IsNonarchimedeanLocalField.valuationMap K
      ((baseFieldUnitsEquiv K).symm x), rfl⟩
  · rintro z ⟨m, rfl⟩
    obtain ⟨x, hx⟩ :=
      LocalFieldTheory.IsNonarchimedeanLocalField.valuationMap_surjective K m
    refine ⟨baseFieldUnitsEquiv K x, ?_⟩
    rw [localBaseValuation_baseFieldUnitsEquiv, hx]
    rfl

/-- Every ordinary integer occurs as a value, as required in the Henselian valuation condition. -/
theorem intToProCInteger_mem_localBaseValuation_range (m : ℤ) :
    Int.castRingHom ZHat m ∈
      (localBaseValuation K).range := by
  rw [localBaseValuation_range]
  exact ⟨m, rfl⟩

/-- Reduction modulo `n` on the actual value group. -/
def localValueGroupReduction (n : ℕ) (hn : 0 < n) :
    (localBaseValuation K).range →+ ZMod n :=
  (zHatReduction n hn).toAddMonoidHom.comp
    (localBaseValuation K).range.subtype

/-- States the theorem `localValueGroupReduction_surjective`. -/
theorem localValueGroupReduction_surjective (n : ℕ) (hn : 0 < n) :
    Function.Surjective (localValueGroupReduction K n hn) := by
  intro a
  obtain ⟨m, rfl⟩ := ZMod.intCast_surjective a
  let z : (localBaseValuation K).range :=
    ⟨Int.castRingHom ZHat m,
      intToProCInteger_mem_localBaseValuation_range K m⟩
  refine ⟨z, ?_⟩
  exact zHatReduction_int n hn m

/-- The kernel of reduction on the value group is precisely `nZ`. -/
theorem localValueGroupReduction_ker (n : ℕ) (hn : 0 < n) :
    (localValueGroupReduction K n hn).ker =
      nsmulWithin (localBaseValuation K).range n := by
  apply le_antisymm
  · intro z hz
    have hzInt : (z : ZHat) ∈
        (Int.castRingHom ZHat).toAddMonoidHom.range := by
      rw [← localBaseValuation_range K]
      exact z.property
    obtain ⟨m, hm⟩ := hzInt
    change Int.castRingHom ZHat m = (z : ZHat) at hm
    have hmod : (m : ZMod n) = 0 := by
      have hz0 : localValueGroupReduction K n hn z = 0 := hz
      change zHatReduction n hn (z : ZHat) = 0 at hz0
      rw [← hm, zHatReduction_int] at hz0
      exact hz0
    have hdiv : (n : ℤ) ∣ m := by
      rwa [ZMod.intCast_zmod_eq_zero_iff_dvd] at hmod
    obtain ⟨k, hk⟩ := hdiv
    let w : (localBaseValuation K).range :=
      ⟨Int.castRingHom ZHat k,
        intToProCInteger_mem_localBaseValuation_range K k⟩
    refine ⟨w, ?_⟩
    apply Subtype.ext
    change n • Int.castRingHom ZHat k = (z : ZHat)
    rw [← map_nsmul]
    have hnk : n • k = m := by
      simpa [nsmul_eq_mul] using hk.symm
    rw [hnk, hm]
  · rintro z ⟨w, rfl⟩
    change zHatReduction n hn (n • (w : ZHat)) = 0
    rw [map_nsmul]
    simp [nsmul_eq_mul]

/-- The inclusion-and-reduction quotient map of the Henselian valuation condition is
bijective for the actual local value group. -/
theorem localCanonicalValueQuotientMap_bijective (n : ℕ) (hn : 0 < n) :
    Function.Bijective
      (canonicalValueQuotientMap (localBaseValuation K).range n hn) := by
  constructor
  · intro q₁ q₂
    refine Quotient.inductionOn' q₁ ?_
    intro z₁
    refine Quotient.inductionOn' q₂ ?_
    intro z₂ h
    apply QuotientAddGroup.eq_iff_sub_mem.mpr
    rw [← localValueGroupReduction_ker K n hn]
    change localValueGroupReduction K n hn (z₁ - z₂) = 0
    rw [map_sub]
    change localValueGroupReduction K n hn z₁ =
      localValueGroupReduction K n hn z₂ at h
    rw [h, sub_self]
  · intro a
    obtain ⟨z, hz⟩ := localValueGroupReduction_surjective K n hn a
    refine ⟨QuotientAddGroup.mk'
      (nsmulWithin (localBaseValuation K).range n) z, ?_⟩
    exact hz

end
end LocalClassFieldTheory
end

section
-- module Solutions.OAIQ244_DUKE.LocalClassFieldTheory_Finite_LocalReciprocity_SeparableFixedFieldNorm
attribute [-instance] _root_.ClassFormation.DegreeData.FiniteAmbientFrobeniusFixedFieldTower.ambientRepresentedQuotientFinite _root_.ClassFormation.DegreeData.FrobeniusFixedFieldTower.baseAbsoluteFiniteInstance _root_.ClassFormation.DegreeData.FrobeniusFixedFieldTower.extensionFinite _root_.ClassFormation.DegreeData.FrobeniusFixedFieldTower.extensionNormal _root_.ClassFormation.DegreeData.FrobeniusFixedFieldTower.fieldAbsoluteFiniteInstance _root_.ClassFormation.DegreeData.FrobeniusPowerFixedFieldTower.baseRepresentedAbsoluteFinite _root_.ClassFormation.DegreeData.FrobeniusPowerFixedFieldTower.fieldRepresentedAbsoluteFinite _root_.ClassFormation.DegreeData.FrobeniusPowerFixedFieldTower.relativeRepresentedQuotientFinite _root_.ClassFormation.DegreeData.frobeniusClosure_isTopologicalGroup _root_.ClassFormation.DegreeData.frobeniusElementsMul _root_.ClassFormation.DegreeData.frobeniusElementsSemigroup _root_.ClassFormation.FiniteAbstractField.toFiniteResidueAbstractField_extensionFinite _root_.ClassFormation.FiniteAbstractField.toFiniteResidueAbstractField_extensionNormal _root_.ClassFormation.FiniteCyclicSubextension.instFiniteQuotientSubtypeMemSubgroupFieldExtensionSubgroupField _root_.ClassFormation.FiniteCyclicSubextension.instFintypeQuotientSubtypeMemSubgroupFieldExtensionSubgroupField _root_.ClassFormation.FiniteCyclicSubextension.instNormalSubtypeMemSubgroupFieldExtensionSubgroupField _root_.ClassFormation.FiniteGaloisSubextension.extensionSubgroup_normalInstance _root_.ClassFormation.FiniteGaloisSubextension.extensionSubgroup_over_intermediate_normalInstance _root_.ClassFormation.FiniteGaloisSubextension.intermediateField_normalInstance _root_.ClassFormation.FiniteIntermediateField.galoisRefinement_normal _root_.ClassFormation.FiniteUnramifiedCyclicExtension.instFiniteQuotientSubtypeMemSubgroupBaseFieldExtensionSubgroupField _root_.ClassFormation.FiniteUnramifiedCyclicExtension.instFiniteQuotientSubtypeMemSubgroupFieldExtensionSubgroupField _root_.ClassFormation.FiniteUnramifiedCyclicExtension.instFintypeQuotientSubtypeMemSubgroupFieldExtensionSubgroupField _root_.ClassFormation.FiniteUnramifiedCyclicExtension.instNormalSubtypeMemSubgroupFieldExtensionSubgroupField _root_.ClassFormation.conjugateExtension_normal _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.KummerTheory.finite_finsupp_nsmulQuotient _root_.KummerTheory.finite_sUnit_nthPowerQuotient _root_.LocalClassFieldTheory.finiteGaloisExtensionSubgroupOfEmbedding_normal _root_.LocalClassFieldTheory.localDecompositionResidueFinite _root_.LocalClassFieldTheory.localDecompositionResidueFintype _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitQuotientCarrier_finite _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.residueFieldZModAlgebra _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedIntegralAlgebraContextValuationSubringAlgebra _root_.LocalFieldTheory.DiscreteValuationField.finite_padicInt_finPi_nsmulQuotient _root_.LocalFieldTheory.DiscreteValuationField.finite_padicInt_pi_nsmulQuotient_of_coprime _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_multiplicative_nthPowerQuotient _root_.LocalFieldTheory.finite_nsmulAddQuotient_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.LubinTate.compatibleGroupFamiliesGroup _root_.OAI.PrimeDegreePackets.boundedRealFields_finite _root_.OAI.PrimeDegreePackets.diagonalLogAction _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionResidueExtension_normal _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionResidueField.instField _root_.RamificationTheory.HilbertRamification.ValuationSubring.selectedResidueField.instAlgebra _root_.RayClass.approximationCompletionTopologicalSpace _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.RelativeIdeleGroup.relativeIdeleMulAction _root_.ValuationTheory.DiscreteValuationField.DVF.maximalIdealPowSuccQuotModule _root_.ValuationTheory.DiscreteValuationField.DVF.residueField.field _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.isDomain _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.isLocalRing _root_.CyclicCohomology.binaryCoefficientFamilyCommGroup _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.LocalClassFieldTheory.normalizationIntegerRingIsIntegralClosure _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.chosenFinitePlaceCompletionAlgebra _root_.chosenFinitePlaceLocalizedIntegerAlgebra _root_.finiteLocalUnitsOpen _root_.relativeAdeleRingIntermediateAlgebra _root_.relativeAdeleRingTopIntermediateAlgebra
attribute [-simp] _root_.ClassFormation.DegreeData.chosenUnramifiedFrobeniusLift_exponent _root_.ClassFormation.DegreeData.extensionNormalizedDegreeContinuous_apply _root_.ClassFormation.DegreeData.extensionNormalizedDegreeContinuous_toMonoidHom _root_.ClassFormation.DegreeData.extensionNormalizedDegree_frobenius_mul _root_.ClassFormation.DegreeData.finiteReciprocityCandidate_apply _root_.ClassFormation.DegreeData.finiteReciprocityCandidate_zero _root_.ClassFormation.DegreeData.fixedFieldNormalizedDegree_generator _root_.ClassFormation.DegreeData.frobeniusActionConjugate_coe _root_.ClassFormation.DegreeData.frobeniusClosureDegreeInMulNatRange_coe _root_.ClassFormation.DegreeData.frobeniusClosureDegree_generator _root_.ClassFormation.DegreeData.frobeniusExponent_actionConjugate _root_.ClassFormation.DegreeData.frobeniusExponent_chosenDegreeOneFrobeniusElement _root_.ClassFormation.DegreeData.frobeniusExponent_mul _root_.ClassFormation.DegreeData.frobeniusExponent_powerOfDegreeOne _root_.ClassFormation.DegreeData.frobeniusFixedFieldAction_coe _root_.ClassFormation.DegreeData.frobeniusFixedFieldQuotientEquiv_mk _root_.ClassFormation.DegreeData.frobeniusFixedFieldToClosure_apply _root_.ClassFormation.DegreeData.frobeniusFixedField_normalizedDegreeEquiv_apply _root_.ClassFormation.DegreeData.frobeniusLiftDifference_coe _root_.ClassFormation.DegreeData.frobeniusMul_coe _root_.ClassFormation.DegreeData.frobeniusPowerOfDegreeOne_coe _root_.ClassFormation.DegreeData.frobeniusPowerSum_coe _root_.ClassFormation.DegreeData.frobeniusQuotientAction_mk _root_.ClassFormation.DegreeData.frobeniusQuotientRepresentation_apply _root_.ClassFormation.DegreeData.frobeniusRestriction_chosenFiniteReciprocityFrobeniusLift _root_.ClassFormation.DegreeData.frobeniusRestriction_mul _root_.ClassFormation.DegreeData.mem_frobeniusFixedField_iff _root_.ClassFormation.DegreeData.mem_frobeniusFixedSubgroupWithin_iff _root_.ClassFormation.FiniteAbelianSubextension.extensionQuotientMk_apply _root_.ClassFormation.FiniteGaloisSubextension.extensionQuotientMk_apply _root_.ClassFormation.FiniteGaloisSubextension.extensionQuotientMk_eq_one_iff _root_.ClassFormation.ValuationData.unitRepresentation_quotient_mk_apply _root_.ClassFormation.ValuationData.unramifiedNormQuotientValuation_finiteNormClass _root_.ClassFormation.ValuationData.unramifiedReciprocity_equiv_of_generator_apply _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.ClassFormation.cyclicNormClassHom_apply _root_.ClassFormation.extensionFixedRepresentationEquiv_apply_coe _root_.ClassFormation.extensionFixedRepresentationEquiv_symm_apply_coe _root_.ClassFormation.finiteReciprocityNaturalityConjugation_mk _root_.ClassFormation.relativeConjugateCosetEquiv_mk _root_.IsDiscreteValuationRing.addVal_ringEquiv _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.LocalClassFieldTheory.abstractRelativeUnitsEquiv_extensionUnitsEquiv _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.LocalFieldTheory.residueField_algebraMap_residue _root_.OAI.PrimeDegreePackets.ThetaConstruction.schwartzCM_apply _root_.ClassFormation.DegreeData.inertiaConjugationCosetEquiv_mk _root_.infinitePlace_mult_smul
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

namespace LocalClassFieldTheory
open RamificationTheory KummerTheory

open LocalFieldTheory

open ClassFormation CyclicCohomology

/-!
# Finite local reciprocity: norms from arbitrary finite separable fixed fields

The henselian condition in the abstract class-formation framework quantifies over every finite abstract
field, not only over normal ones.  For an intermediate finite separable field
`E` in a separably closed Galois ambient field, the left cosets of
`Gal(Ω / E)` are canonically the `K`-embeddings `E → Ω`.  This file uses that
identification to compare the abstract class-formation coset norm with the ordinary field
norm, without a normality assumption on `E / K`.
-/

noncomputable section

open scoped BigOperators

variable (K Ω : Type) [Field K] [Field Ω] [Algebra K Ω]
  [IsGalois K Ω] [IsSepClosed Ω]

section CosetsAndEmbeddings

variable (E : IntermediateField K Ω)

/-- Restriction to `E` sends a left coset of `Gal(Ω/E)` to the corresponding
`K`-embedding of `E` into `Ω`. -/
def baseFixingCosetToAlgHom :
    ((closedFixingSubgroup K Ω (⊥ : IntermediateField K Ω)).toSubgroup ⧸
      extensionSubgroup
        (closedFixingSubgroup K Ω (⊥ : IntermediateField K Ω))
        (closedFixingSubgroup K Ω E) (fixingSubgroupLeBase K Ω E)) →
      (E →ₐ[K] Ω) := fun q =>
  Quotient.liftOn' q
    (fun σ => σ.1.toAlgHom.comp E.val)
    (by
      intro σ τ hστ
      have hmem : σ⁻¹ * τ ∈
          extensionSubgroup
            (closedFixingSubgroup K Ω (⊥ : IntermediateField K Ω))
            (closedFixingSubgroup K Ω E) (fixingSubgroupLeBase K Ω E) :=
        QuotientGroup.leftRel_apply.mp hστ
      let η : (closedFixingSubgroup K Ω E).toSubgroup :=
        ⟨(σ⁻¹ * τ).1, hmem⟩
      have hτ : τ = σ * Subgroup.inclusion
          (fixingSubgroupLeBase K Ω E) η := by
        apply Subtype.ext
        change τ.1 = σ.1 * η.1
        simp [η]
      apply AlgHom.ext
      intro x
      have hηfix :=
        (IntermediateField.mem_fixingSubgroup_iff E η.1).mp η.2
      have hηx : η.1 (x : Ω) = (x : Ω) := hηfix x x.2
      have hτ' := congrArg Subtype.val hτ
      change τ.1 = σ.1 * η.1 at hτ'
      change σ.1 (x : Ω) = τ.1 (x : Ω)
      calc
        σ.1 (x : Ω) = σ.1 (η.1 (x : Ω)) :=
          congrArg σ.1 hηx.symm
        _ = (σ.1 * η.1) (x : Ω) := rfl
        _ = τ.1 (x : Ω) := by rw [hτ'])

omit [IsSepClosed Ω] in
/-- States the theorem `baseFixingCosetToAlgHom_mk`. -/
@[simp]
theorem baseFixingCosetToAlgHom_mk
    (σ : (closedFixingSubgroup K Ω
      (⊥ : IntermediateField K Ω)).toSubgroup) :
    baseFixingCosetToAlgHom K Ω E (QuotientGroup.mk σ) =
      σ.1.toAlgHom.comp E.val :=
  rfl

theorem baseFixingCosetToAlgHom_surjective
    [FiniteDimensional K E] [Algebra.IsSeparable K E] :
    Function.Surjective (baseFixingCosetToAlgHom K Ω E) := by
  intro f
  let : Algebra.IsSeparable E Ω :=
    Algebra.isSeparable_tower_top_of_isSeparable K E Ω
  obtain ⟨φ, hφ⟩ :=
    (IsSepClosed.surjective_domRestrict_of_isSeparable
      (K := K) (L := E) (M := Ω) (E := Ω)) f
  let σ : Ω ≃ₐ[K] Ω :=
    AlgEquiv.ofBijective φ
      (Normal.toIsAlgebraic.algHom_bijective₂
        φ (AlgHom.id K Ω)).1
  have hσ : σ ∈ (closedFixingSubgroup K Ω
      (⊥ : IntermediateField K Ω)).toSubgroup := by
    change σ ∈ (⊥ : IntermediateField K Ω).fixingSubgroup
    rw [IntermediateField.fixingSubgroup_bot]
    exact Subgroup.mem_top σ
  let σbase : (closedFixingSubgroup K Ω
      (⊥ : IntermediateField K Ω)).toSubgroup := ⟨σ, hσ⟩
  refine ⟨QuotientGroup.mk σbase, ?_⟩
  apply AlgHom.ext
  intro x
  have hx := congrArg (fun ψ : E →ₐ[K] Ω => ψ x) hφ
  change φ (x : Ω) = f x
  change φ (x : Ω) = f x at hx
  exact hx

omit [IsSepClosed Ω] in
theorem baseFixingCosetToAlgHom_injective :
    Function.Injective (baseFixingCosetToAlgHom K Ω E) := by
  intro q r hqr
  rw [← Quotient.out_eq q, ← Quotient.out_eq r] at hqr ⊢
  apply Quotient.sound'
  apply QuotientGroup.leftRel_apply.mpr
  apply (mem_extensionSubgroup_iff
    (closedFixingSubgroup K Ω (⊥ : IntermediateField K Ω))
    (closedFixingSubgroup K Ω E) (fixingSubgroupLeBase K Ω E)
    ((Quotient.out q)⁻¹ * Quotient.out r)).2
  change (Quotient.out q).1⁻¹ * (Quotient.out r).1 ∈ E.fixingSubgroup
  rw [IntermediateField.mem_fixingSubgroup_iff]
  intro x hx
  let y : E := ⟨x, hx⟩
  have hy := congrArg (fun ψ : E →ₐ[K] Ω => ψ y) hqr
  change (Quotient.out q).1 (y : Ω) =
    (Quotient.out r).1 (y : Ω) at hy
  change (Quotient.out q).1⁻¹ ((Quotient.out r).1 x) = x
  rw [← hy]
  simp [y]

/-- Left cosets of the absolute subgroup fixing `E` are the actual
`K`-embeddings of `E` into the separably closed ambient field. -/
def baseFixingCosetEquivAlgHom
    [FiniteDimensional K E] [Algebra.IsSeparable K E] :
    ((closedFixingSubgroup K Ω (⊥ : IntermediateField K Ω)).toSubgroup ⧸
      extensionSubgroup
        (closedFixingSubgroup K Ω (⊥ : IntermediateField K Ω))
        (closedFixingSubgroup K Ω E) (fixingSubgroupLeBase K Ω E)) ≃
      (E →ₐ[K] Ω) :=
  Equiv.ofBijective (baseFixingCosetToAlgHom K Ω E)
    ⟨baseFixingCosetToAlgHom_injective K Ω E,
      baseFixingCosetToAlgHom_surjective K Ω E⟩

/-- Provides the instance `baseFixingExtensionQuotient_finite_of_isSeparable`. -/
noncomputable instance baseFixingExtensionQuotient_finite_of_isSeparable
    [FiniteDimensional K E] [Algebra.IsSeparable K E] :
    Finite
      ((closedFixingSubgroup K Ω (⊥ : IntermediateField K Ω)).toSubgroup ⧸
        extensionSubgroup
          (closedFixingSubgroup K Ω (⊥ : IntermediateField K Ω))
          (closedFixingSubgroup K Ω E) (fixingSubgroupLeBase K Ω E)) :=
  (baseFixingCosetEquivAlgHom K Ω E).finite_iff.mpr inferInstance

end CosetsAndEmbeddings

section NormAsProduct

variable (E : IntermediateField K Ω)
  [FiniteDimensional K E] [Algebra.IsSeparable K E]

omit [IsSepClosed Ω] [FiniteDimensional K E] [Algebra.IsSeparable K E] in

/-- The abstract coset action on an `E`-unit is evaluation under the
corresponding actual `K`-embedding of `E`. -/
theorem relativeCosetAction_intermediateFieldUnit_val_of_isSeparable
    (x : Eˣ)
    (q : (closedFixingSubgroup K Ω
        (⊥ : IntermediateField K Ω)).toSubgroup ⧸
      extensionSubgroup
        (closedFixingSubgroup K Ω (⊥ : IntermediateField K Ω))
        (closedFixingSubgroup K Ω E) (fixingSubgroupLeBase K Ω E)) :
    ((Additive.toMul
      (relativeCosetAction (galoisAmbientUnitsRep K Ω)
        (closedFixingSubgroup K Ω (⊥ : IntermediateField K Ω))
        (closedFixingSubgroup K Ω E) (fixingSubgroupLeBase K Ω E)
        (intermediateFieldUnitsEquivGaloisFixed K Ω E
          (Additive.ofMul x)) q) : Ωˣ) : Ω) =
      baseFixingCosetToAlgHom K Ω E q (x : E) := by
  refine Quotient.inductionOn' q ?_
  intro σ
  rfl

attribute [local instance] LocalClassFieldTheory.finiteSeparableAlgHomFintype
/-- For every finite separable intermediate field, including a nonnormal
one, the abstract class-formation left-coset norm is the ordinary field norm. -/
theorem relativeNorm_intermediateFieldUnit_val_of_isSeparable (x : Eˣ) :
    ((Additive.toMul
      ((relativeNorm (galoisAmbientUnitsRep K Ω)
        (closedFixingSubgroup K Ω (⊥ : IntermediateField K Ω))
        (closedFixingSubgroup K Ω E) (fixingSubgroupLeBase K Ω E)
        (intermediateFieldUnitsEquivGaloisFixed K Ω E
          (Additive.ofMul x))).1 : Additive Ωˣ) : Ωˣ) : Ω) =
      algebraMap K Ω (Algebra.norm K (x : E)) := by
  let Q := (closedFixingSubgroup K Ω
      (⊥ : IntermediateField K Ω)).toSubgroup ⧸
    extensionSubgroup
      (closedFixingSubgroup K Ω (⊥ : IntermediateField K Ω))
      (closedFixingSubgroup K Ω E) (fixingSubgroupLeBase K Ω E)
  let := Fintype.ofFinite Q
  change
    ((Additive.toMul
      (relativeNormValue (galoisAmbientUnitsRep K Ω)
        (closedFixingSubgroup K Ω (⊥ : IntermediateField K Ω))
        (closedFixingSubgroup K Ω E) (fixingSubgroupLeBase K Ω E)
        (intermediateFieldUnitsEquivGaloisFixed K Ω E
          (Additive.ofMul x))) : Ωˣ) : Ω) = _
  rw [relativeNormValue]
  change
    (↑(Additive.toMul (∑ q : Q,
      relativeCosetAction (galoisAmbientUnitsRep K Ω)
        (closedFixingSubgroup K Ω (⊥ : IntermediateField K Ω))
        (closedFixingSubgroup K Ω E) (fixingSubgroupLeBase K Ω E)
        (intermediateFieldUnitsEquivGaloisFixed K Ω E
          (Additive.ofMul x)) q) : Ωˣ) : Ω) = _

  change (Units.coeHom Ω) (∏ q : Q,
    Additive.toMul
      (relativeCosetAction (galoisAmbientUnitsRep K Ω)
        (closedFixingSubgroup K Ω (⊥ : IntermediateField K Ω))
        (closedFixingSubgroup K Ω E) (fixingSubgroupLeBase K Ω E)
        (intermediateFieldUnitsEquivGaloisFixed K Ω E
          (Additive.ofMul x)) q)) = _
  rw [map_prod]
  change
    (∏ q : Q,
      ((Additive.toMul
        (relativeCosetAction (galoisAmbientUnitsRep K Ω)
          (closedFixingSubgroup K Ω (⊥ : IntermediateField K Ω))
          (closedFixingSubgroup K Ω E) (fixingSubgroupLeBase K Ω E)
          (intermediateFieldUnitsEquivGaloisFixed K Ω E
            (Additive.ofMul x)) q) : Ωˣ) : Ω)) = _
  calc
    _ = ∏ σ : E →ₐ[K] Ω, σ (x : E) := by
      exact Fintype.prod_equiv
        (baseFixingCosetEquivAlgHom K Ω E)
        (fun q : Q =>
          ((Additive.toMul
            (relativeCosetAction (galoisAmbientUnitsRep K Ω)
              (closedFixingSubgroup K Ω (⊥ : IntermediateField K Ω))
              (closedFixingSubgroup K Ω E) (fixingSubgroupLeBase K Ω E)
              (intermediateFieldUnitsEquivGaloisFixed K Ω E
                (Additive.ofMul x)) q) : Ωˣ) : Ω))
        (fun σ : E →ₐ[K] Ω => σ (x : E))
        (relativeCosetAction_intermediateFieldUnit_val_of_isSeparable
          K Ω E x)
    _ = algebraMap K Ω (Algebra.norm K (x : E)) :=
      (algebraMap_norm_eq_prod_embeddings_of_isSepClosed
        K Ω E (x : E)).symm

end NormAsProduct

end
end LocalClassFieldTheory
end

section
-- module Solutions.OAIQ244_DUKE.LocalClassFieldTheory_Finite_LocalReciprocity_AbstractFixedFieldNorm
attribute [-instance] _root_.ClassFormation.DegreeData.FiniteAmbientFrobeniusFixedFieldTower.ambientRepresentedQuotientFinite _root_.ClassFormation.DegreeData.FrobeniusFixedFieldTower.baseAbsoluteFiniteInstance _root_.ClassFormation.DegreeData.FrobeniusFixedFieldTower.extensionFinite _root_.ClassFormation.DegreeData.FrobeniusFixedFieldTower.extensionNormal _root_.ClassFormation.DegreeData.FrobeniusFixedFieldTower.fieldAbsoluteFiniteInstance _root_.ClassFormation.DegreeData.FrobeniusPowerFixedFieldTower.baseRepresentedAbsoluteFinite _root_.ClassFormation.DegreeData.FrobeniusPowerFixedFieldTower.fieldRepresentedAbsoluteFinite _root_.ClassFormation.DegreeData.FrobeniusPowerFixedFieldTower.relativeRepresentedQuotientFinite _root_.ClassFormation.DegreeData.frobeniusClosure_isTopologicalGroup _root_.ClassFormation.DegreeData.frobeniusElementsMul _root_.ClassFormation.DegreeData.frobeniusElementsSemigroup _root_.ClassFormation.FiniteAbstractField.toFiniteResidueAbstractField_extensionFinite _root_.ClassFormation.FiniteAbstractField.toFiniteResidueAbstractField_extensionNormal _root_.ClassFormation.FiniteGaloisSubextension.extensionSubgroup_over_intermediate_normalInstance _root_.ClassFormation.FiniteGaloisSubextension.intermediateField_normalInstance _root_.ClassFormation.FiniteIntermediateField.galoisRefinement_normal _root_.ClassFormation.conjugateExtension_normal _root_.ClassFormation.instIsAddTorsionFreeZHat _root_.ClassFormation.instIsMulTorsionFreeMultiplicativeZHat _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.KummerTheory.finite_finsupp_nsmulQuotient _root_.KummerTheory.finite_sUnit_nthPowerQuotient _root_.KummerTheory.primeCyclotomicBaseIsGalois _root_.LocalClassFieldTheory.finiteGaloisExtensionSubgroupOfEmbedding_normal _root_.LocalClassFieldTheory.finiteGaloisFieldRangeOfEmbedding_isGalois _root_.LocalClassFieldTheory.localDecompositionResidueFinite _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitQuotientCarrier_finite _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.residueFieldZModAlgebra _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedIntegralAlgebraContextValuationSubringAlgebra _root_.LocalFieldTheory.DiscreteValuationField.finite_padicInt_finPi_nsmulQuotient _root_.LocalFieldTheory.DiscreteValuationField.finite_padicInt_pi_nsmulQuotient_of_coprime _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_multiplicative_nthPowerQuotient _root_.LocalFieldTheory.finite_nsmulAddQuotient_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.LubinTate.Valuations.exponentialValuationSubringIsLocalRing _root_.LubinTate.compatibleGroupFamiliesGroup _root_.OAI.PrimeDegreePackets.boundedRealFields_finite _root_.OAI.PrimeDegreePackets.diagonalLogAction _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_finite_residue _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionFixedSubring.instIsLocalRing _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionResidueExtension_normal _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionResidueField.instField _root_.RamificationTheory.HilbertRamification.ValuationSubring.selectedResidueField.instAlgebra _root_.RayClass.approximationCompletionTopologicalSpace _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.RelativeIdeleGroup.relativeIdeleMulAction _root_.ValuationTheory.DiscreteValuationField.DVF.maximalIdealPowSuccQuotModule _root_.ValuationTheory.DiscreteValuationField.DVF.residueField.field _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.isDomain _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.isLocalRing _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.LocalClassFieldTheory.normalizationIntegerRingIsIntegralClosure _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.chosenFinitePlaceCompletionAlgebra _root_.chosenFinitePlaceLocalizedIntegerModuleFinite _root_.chosenFinitePlaceLocalizedIsGalois _root_.cyclicPrimeDegreeIntermediate_isGalois _root_.cyclicPrimeSubextension_isGalois _root_.finiteLocalUnitsOpen _root_.finiteNormalClosure_isGalois _root_.relativeAdeleRingIntermediateAlgebra _root_.relativeAdeleRingTopIntermediateAlgebra _root_.scaledRelativeIntegerLatticeQuotientFinite
set_option maxHeartbeats 800000
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

namespace LocalClassFieldTheory

open RamificationTheory CyclicCohomology KummerTheory ClassFormation

open LocalFieldTheory

/-!
# Finite local reciprocity: the norm of an arbitrary finite abstract field

The abstract class-formation framework indexes finite fields by closed subgroups, whereas the local norm
calculation is stated for their concrete fixed intermediate fields.  This file
identifies the two presentations.  In particular, it does not assume that the
finite fixed field is normal over the local ground field.
-/

noncomputable section

open scoped ValuativeRel
variable (K Ω : Type) [Field K] [Field Ω] [Algebra K Ω]
  [IsGalois K Ω] [IsSepClosed Ω]

/-- The underlying value of a relative norm is unchanged when its two
closed-subgroup indices and its fixed coefficient are transported along
equalities.  Keeping this congruence explicit avoids dependent rewriting
through the inclusion proof carried by `relativeNorm`. -/
theorem relativeNorm_coe_eq_of_closedSubgroup_eq
    {G : Type} [Group G] [TopologicalSpace G]
    (A : Rep ℤ G)
    (B B' C C' : ClosedSubgroup G)
    (hCB : C.toSubgroup ≤ B.toSubgroup)
    (hC'B' : C'.toSubgroup ≤ B'.toSubgroup)
    [hfinite : Finite
      (B.toSubgroup ⧸ extensionSubgroup B C hCB)]
    [hfinite' : Finite
      (B'.toSubgroup ⧸ extensionSubgroup B' C' hC'B')]
    (hB : B = B') (hC : C = C')
    (x : ambientFixedAddSubgroup A C)
    (x' : ambientFixedAddSubgroup A C')
    (hx : x.1 = x'.1) :
    ((relativeNorm A B C hCB x : ambientFixedAddSubgroup A B) : A.V) =
      ((relativeNorm A B' C' hC'B' x' :
        ambientFixedAddSubgroup A B') : A.V) := by
  subst B'
  subst C'
  have hle : hCB = hC'B' := Subsingleton.elim _ _
  subst hC'B'
  have hfin : hfinite = hfinite' := Subsingleton.elim _ _
  subst hfinite'
  have hxx' : x = x' := Subtype.ext hx
  subst x'
  rfl

/-- For an arbitrary finite separable abstract field, the abstract class-formation norm on
fixed coefficients has the same underlying field element as the ordinary
field norm from its concrete fixed field. -/
theorem normToBase_abstractFixedFieldUnit_val_of_isSeparable
    (H : ClosedSubgroup (Gal(Ω / K)))
    [Finite ((baseField (Gal(Ω / K))).toSubgroup ⧸
      extensionSubgroup (baseField (Gal(Ω / K))) H (le_baseField H))]
    [FiniteDimensional K (abstractFixedField K Ω H)]
    [Algebra.IsSeparable K (abstractFixedField K Ω H)]
    (x : (abstractFixedField K Ω H)ˣ) :
    ((Additive.toMul
      ((normToBase (galoisAmbientUnitsRep K Ω) H
        (abstractFixedFieldUnitsEquivGaloisFixed K Ω H
          (Additive.ofMul x))).1 : Additive Ωˣ) : Ωˣ) : Ω) =
      algebraMap K Ω (Algebra.norm K
        (x : abstractFixedField K Ω H)) := by
  let E := abstractFixedField K Ω H
  let y : ambientFixedAddSubgroup (galoisAmbientUnitsRep K Ω) H :=
    abstractFixedFieldUnitsEquivGaloisFixed K Ω H (Additive.ofMul x)
  let yE := intermediateFieldUnitsEquivGaloisFixed K Ω E (Additive.ofMul x)
  have hy : yE.1 = y.1 := by
    rw [intermediateFieldUnitsEquivGaloisFixed_coe]
    exact (abstractFixedFieldUnitsEquivGaloisFixed_coe
      K Ω H (Additive.ofMul x)).symm
  have hnorm :=
    relativeNorm_intermediateFieldUnit_val_of_isSeparable K Ω E x
  have htransport := relativeNorm_coe_eq_of_closedSubgroup_eq
    (galoisAmbientUnitsRep K Ω)
    (closedFixingSubgroup K Ω (⊥ : IntermediateField K Ω))
    (baseField (Gal(Ω / K)))
    (closedFixingSubgroup K Ω E) H
    (fixingSubgroupLeBase K Ω E) (le_baseField H)
    (closedFixingSubgroup_bot_eq_baseField K Ω)
    (closedFixingSubgroup_abstractFixedField_eq K Ω H)
    yE y hy
  have htransport' := congrArg
    (fun z : Additive Ωˣ => ((Additive.toMul z : Ωˣ) : Ω)) htransport
  change
    ((Additive.toMul
      ((normToBase (galoisAmbientUnitsRep K Ω) H y).1 :
        Additive Ωˣ) : Ωˣ) : Ω) = _
  exact htransport'.symm.trans hnorm

/-- The base normalized valuation of the abstract norm is the ordinary
normalized valuation of the concrete field norm. -/
theorem localBaseValuation_normToBase_abstractFixedFieldUnit
    (K : Type) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    (H : ClosedSubgroup (Gal(SeparableClosure K / K)))
    [Finite ((baseField (Gal(SeparableClosure K / K))).toSubgroup ⧸
      extensionSubgroup (baseField (Gal(SeparableClosure K / K))) H
        (le_baseField H))]
    [FiniteDimensional K
      (abstractFixedField K (SeparableClosure K) H)]
    (x : (abstractFixedField K (SeparableClosure K) H)ˣ) :
    localBaseValuation K
        (normToBase
          (galoisAmbientUnitsRep K (SeparableClosure K)) H
          (abstractFixedFieldUnitsEquivGaloisFixed
            K (SeparableClosure K) H (Additive.ofMul x))) =
      Int.castRingHom ZHat
        (LocalFieldTheory.IsNonarchimedeanLocalField.valuationMap K
          (Additive.ofMul
            (normUnits K (abstractFixedField K (SeparableClosure K) H) x))) := by
  let E := abstractFixedField K (SeparableClosure K) H
  let a := normToBase
    (galoisAmbientUnitsRep K (SeparableClosure K)) H
    (abstractFixedFieldUnitsEquivGaloisFixed
      K (SeparableClosure K) H (Additive.ofMul x))
  have ha : (baseFieldUnitsEquiv K).symm a =
      Additive.ofMul (normUnits K E x) := by
    apply (baseFieldUnitsEquiv K).injective
    rw [(baseFieldUnitsEquiv K).apply_symm_apply]
    apply Subtype.ext
    apply Additive.ext
    apply Units.ext
    calc
      ((Additive.toMul
          ((normToBase
            (galoisAmbientUnitsRep K (SeparableClosure K)) H
            (abstractFixedFieldUnitsEquivGaloisFixed
              K (SeparableClosure K) H (Additive.ofMul x))).1 :
              Additive (SeparableClosure K)ˣ) :
            (SeparableClosure K)ˣ) : SeparableClosure K) =
          algebraMap K (SeparableClosure K)
            (Algebra.norm K (x : E)) :=
        normToBase_abstractFixedFieldUnit_val_of_isSeparable
          K (SeparableClosure K) H x
      _ = algebraMap K (SeparableClosure K)
          ((normUnits K E x : Kˣ) : K) := by
        rw [LocalFieldTheory.normUnits_apply_coe]
      _ =
          ((Additive.toMul
            ((baseFieldUnitsEquiv K
              (Additive.ofMul (normUnits K E x))).1 :
                Additive (SeparableClosure K)ˣ) :
              (SeparableClosure K)ˣ) : SeparableClosure K) :=
        (baseFieldUnitsEquiv_val K (normUnits K E x)).symm
  rw [show normToBase
      (galoisAmbientUnitsRep K (SeparableClosure K)) H
      (abstractFixedFieldUnitsEquivGaloisFixed
        K (SeparableClosure K) H (Additive.ofMul x)) = a from rfl]
  change Int.castRingHom ZHat
      (LocalFieldTheory.IsNonarchimedeanLocalField.valuationMap K
        ((baseFieldUnitsEquiv K).symm a)) = _
  rw [ha]

/-- For an arbitrary finite separable abstract field, the image of the
base valuation after the abstract class-formation norm is exactly the actual residue-degree
multiple of the base value group. -/
theorem localBaseValuation_comp_normToBase_range_eq_residueFinrank
    (K : Type) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    (H : ClosedSubgroup (Gal(SeparableClosure K / K)))
    [Finite ((baseField (Gal(SeparableClosure K / K))).toSubgroup ⧸
      extensionSubgroup (baseField (Gal(SeparableClosure K / K))) H
        (le_baseField H))]
    [FiniteDimensional K
      (abstractFixedField K (SeparableClosure K) H)]
    [ValuativeRel (abstractFixedField K (SeparableClosure K) H)]
    [TopologicalSpace (abstractFixedField K (SeparableClosure K) H)]
    [IsNonarchimedeanLocalField
      (abstractFixedField K (SeparableClosure K) H)]
    [Valuation.HasExtension (ValuativeRel.valuation K)
      (ValuativeRel.valuation
        (abstractFixedField K (SeparableClosure K) H))]
    [hIntegralClosure : IsIntegralClosure
      𝒪[abstractFixedField K (SeparableClosure K) H] 𝒪[K]
      (abstractFixedField K (SeparableClosure K) H)] :
    ((localBaseValuation K).comp
      (normToBase
        (galoisAmbientUnitsRep K (SeparableClosure K)) H)).range =
      nsmulImage (localBaseValuation K).range
        (Module.finrank 𝓀[K]
          𝓀[abstractFixedField K (SeparableClosure K) H]) := by
  let f := Module.finrank 𝓀[K]
    𝓀[abstractFixedField K (SeparableClosure K) H]
  ext z
  constructor
  · rintro ⟨a, rfl⟩
    let x : Additive
        (abstractFixedField K (SeparableClosure K) H)ˣ :=
      (abstractFixedFieldUnitsEquivGaloisFixed
        K (SeparableClosure K) H).symm a
    have hxa : abstractFixedFieldUnitsEquivGaloisFixed
        K (SeparableClosure K) H x = a :=
      (abstractFixedFieldUnitsEquivGaloisFixed
        K (SeparableClosure K) H).apply_symm_apply a
    rw [← hxa]
    change localBaseValuation K
      (normToBase (galoisAmbientUnitsRep K (SeparableClosure K)) H
        (abstractFixedFieldUnitsEquivGaloisFixed
          K (SeparableClosure K) H
            (Additive.ofMul (Additive.toMul x)))) ∈ _
    rw [localBaseValuation_normToBase_abstractFixedFieldUnit]
    have hnorm :=
      @v_normUnits_eq_residue_finrank_mul_of_isSeparable
        K (abstractFixedField K (SeparableClosure K) H)
          _ _ _ _ _ _ _ _ _ _ _ _ hIntegralClosure (Additive.toMul x)
    have hnorm' :
        LocalFieldTheory.IsNonarchimedeanLocalField.valuationMap K
            (Additive.ofMul
              (normUnits K
                (abstractFixedField K (SeparableClosure K) H)
                (Additive.toMul x))) =
          (f : Int) *
            LocalFieldTheory.IsNonarchimedeanLocalField.valuationMap
              (abstractFixedField K (SeparableClosure K) H) x := by
      convert hnorm using 3
      all_goals try rfl
      all_goals (simp only [f]; congr!)
      all_goals first
        | exact residueAlgebra_eq
        | exact residueModule_eq
        | (rw [residueAlgebra_eq]; exact residueModule_eq)
        | (simp only [residueAlgebra_eq]; exact residueModule_eq)
        | (convert residueModule_eq using 2; exact residueAlgebra_eq)
    rw [hnorm', mem_nsmulImage_iff]
    refine ⟨Int.castRingHom ZHat
        (LocalFieldTheory.IsNonarchimedeanLocalField.valuationMap
          (abstractFixedField K (SeparableClosure K) H) x),
      intToProCInteger_mem_localBaseValuation_range K _, ?_⟩
    rw [← map_nsmul]
    congr 1
  · rw [mem_nsmulImage_iff]
    rintro ⟨w, hw, hwz⟩
    rw [localBaseValuation_range K] at hw
    obtain ⟨m, rfl⟩ := hw
    obtain ⟨x, hx⟩ :=
      LocalFieldTheory.IsNonarchimedeanLocalField.valuationMap_surjective
        (abstractFixedField K (SeparableClosure K) H) m
    refine ⟨abstractFixedFieldUnitsEquivGaloisFixed
      K (SeparableClosure K) H x, ?_⟩
    change localBaseValuation K
      (normToBase (galoisAmbientUnitsRep K (SeparableClosure K)) H
        (abstractFixedFieldUnitsEquivGaloisFixed
          K (SeparableClosure K) H
            (Additive.ofMul (Additive.toMul x)))) = z
    rw [localBaseValuation_normToBase_abstractFixedFieldUnit]
    have hnorm :=
      @v_normUnits_eq_residue_finrank_mul_of_isSeparable
        K (abstractFixedField K (SeparableClosure K) H)
          _ _ _ _ _ _ _ _ _ _ _ _ hIntegralClosure (Additive.toMul x)
    have hnorm' :
        LocalFieldTheory.IsNonarchimedeanLocalField.valuationMap K
            (Additive.ofMul
              (normUnits K
                (abstractFixedField K (SeparableClosure K) H)
                (Additive.toMul x))) =
          (f : Int) *
            LocalFieldTheory.IsNonarchimedeanLocalField.valuationMap
              (abstractFixedField K (SeparableClosure K) H) x := by
      convert hnorm using 3
      all_goals try rfl
      all_goals (simp only [f]; congr!)
      all_goals first
        | exact residueAlgebra_eq
        | exact residueModule_eq
        | (rw [residueAlgebra_eq]; exact residueModule_eq)
        | (simp only [residueAlgebra_eq]; exact residueModule_eq)
        | (convert residueModule_eq using 2; exact residueAlgebra_eq)
    rw [hnorm', hx]
    calc
      Int.castRingHom ZHat
          ((f : Int) * m) =
          f • Int.castRingHom ZHat m := by
        rw [← map_nsmul]
        congr 1
      _ = z := hwz

end
end LocalClassFieldTheory
end

section
-- module Solutions.OAIQ244_DUKE.LocalClassFieldTheory_Finite_LocalReciprocity_LocalHenselianValuation
attribute [-instance] _root_.ClassFormation.DegreeData.FiniteAmbientFrobeniusFixedFieldTower.ambientRepresentedQuotientFinite _root_.ClassFormation.DegreeData.FrobeniusFixedFieldTower.baseAbsoluteFiniteInstance _root_.ClassFormation.DegreeData.FrobeniusFixedFieldTower.extensionFinite _root_.ClassFormation.DegreeData.FrobeniusFixedFieldTower.extensionNormal _root_.ClassFormation.DegreeData.FrobeniusFixedFieldTower.fieldAbsoluteFiniteInstance _root_.ClassFormation.DegreeData.FrobeniusPowerFixedFieldTower.baseRepresentedAbsoluteFinite _root_.ClassFormation.DegreeData.FrobeniusPowerFixedFieldTower.fieldRepresentedAbsoluteFinite _root_.ClassFormation.DegreeData.FrobeniusPowerFixedFieldTower.relativeRepresentedQuotientFinite _root_.ClassFormation.DegreeData.frobeniusClosure_isTopologicalGroup _root_.ClassFormation.DegreeData.frobeniusElementsMul _root_.ClassFormation.DegreeData.frobeniusElementsSemigroup _root_.ClassFormation.FiniteAbstractField.toFiniteResidueAbstractField_extensionFinite _root_.ClassFormation.FiniteAbstractField.toFiniteResidueAbstractField_extensionNormal _root_.ClassFormation.FiniteGaloisSubextension.extensionSubgroup_over_intermediate_normalInstance _root_.ClassFormation.FiniteGaloisSubextension.intermediateField_normalInstance _root_.ClassFormation.FiniteIntermediateField.galoisRefinement_normal _root_.ClassFormation.conjugateExtension_normal _root_.ClassFormation.instIsAddTorsionFreeZHat _root_.ClassFormation.instIsMulTorsionFreeMultiplicativeZHat _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.DiscreteNthRootsSubgroup.instTopologicalSpaceSubtypeUnitsMemSubgroup _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.KummerTheory.finite_finsupp_nsmulQuotient _root_.KummerTheory.finite_sUnit_nthPowerQuotient _root_.KummerTheory.primeCyclotomicBaseIsGalois _root_.LocalClassFieldTheory.finiteGaloisExtensionSubgroupOfEmbedding_normal _root_.LocalClassFieldTheory.finiteGaloisFieldRangeOfEmbedding_isGalois _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitQuotientCarrier_finite _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.residueFieldZModAlgebra _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedIntegralAlgebraContextValuationSubringAlgebra _root_.LocalFieldTheory.DiscreteValuationField.finite_padicInt_finPi_nsmulQuotient _root_.LocalFieldTheory.DiscreteValuationField.finite_padicInt_pi_nsmulQuotient_of_coprime _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_multiplicative_nthPowerQuotient _root_.LocalFieldTheory.finite_nsmulAddQuotient_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.LubinTate.compatibleGroupFamiliesGroup _root_.OAI.PrimeDegreePackets.boundedRealFields_finite _root_.OAI.PrimeDegreePackets.diagonalLogAction _root_.OAI.PrimeDegreePackets.gLocallyCompact _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_finite_residue _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.RayClass.approximationCompletionTopologicalSpace _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.RelativeIdeleGroup.relativeIdeleMulAction _root_.LocalClassFieldTheory.normalizationIntegerRingIsIntegralClosure _root_.adicCompletionProperSpace _root_.chosenFinitePlaceBaseIsUltrametricDist _root_.chosenFinitePlaceBaseIsValuativeTopology _root_.chosenFinitePlaceBaseLocallyCompactSpace _root_.chosenFinitePlaceBaseValuationCompatible _root_.chosenFinitePlaceBaseValuationIsNontrivial _root_.chosenFinitePlaceBaseValuativeRelIsNontrivial _root_.chosenFinitePlaceBaseValued _root_.chosenFinitePlaceCompletionAlgebra _root_.chosenFinitePlaceCompletionContinuousSMul _root_.chosenFinitePlaceLocalizedIntegerAlgebra _root_.chosenFinitePlaceLocalizedIntegerModuleFinite _root_.chosenFinitePlaceLocalizedIsGalois _root_.cyclicPrimeDegreeIntermediate_isGalois _root_.cyclicPrimeSubextension_isGalois _root_.finiteLocalUnitsOpen _root_.finiteNormalClosure_isGalois _root_.relativeAdeleRingIntermediateAlgebra _root_.relativeAdeleRingTopIntermediateAlgebra _root_.scaledRelativeIntegerLatticeQuotientFinite
attribute [-simp] _root_.ClassFormation.DegreeData.chosenUnramifiedFrobeniusLift_exponent _root_.ClassFormation.DegreeData.extensionNormalizedDegreeContinuous_apply _root_.ClassFormation.DegreeData.extensionNormalizedDegreeContinuous_toMonoidHom _root_.ClassFormation.DegreeData.extensionNormalizedDegree_frobenius_mul _root_.ClassFormation.DegreeData.finiteReciprocityCandidate_apply _root_.ClassFormation.DegreeData.finiteReciprocityCandidate_zero _root_.ClassFormation.DegreeData.fixedFieldNormalizedDegree_generator _root_.ClassFormation.DegreeData.frobeniusActionConjugate_coe _root_.ClassFormation.DegreeData.frobeniusClosureDegreeInMulNatRange_coe _root_.ClassFormation.DegreeData.frobeniusClosureDegree_generator _root_.ClassFormation.DegreeData.frobeniusExponent_actionConjugate _root_.ClassFormation.DegreeData.frobeniusExponent_chosenDegreeOneFrobeniusElement _root_.ClassFormation.DegreeData.frobeniusExponent_mul _root_.ClassFormation.DegreeData.frobeniusExponent_powerOfDegreeOne _root_.ClassFormation.DegreeData.frobeniusFixedFieldAction_coe _root_.ClassFormation.DegreeData.frobeniusFixedFieldQuotientEquiv_mk _root_.ClassFormation.DegreeData.frobeniusFixedFieldToClosure_apply _root_.ClassFormation.DegreeData.frobeniusFixedField_normalizedDegreeEquiv_apply _root_.ClassFormation.DegreeData.frobeniusLiftDifference_coe _root_.ClassFormation.DegreeData.frobeniusMul_coe _root_.ClassFormation.DegreeData.frobeniusPowerOfDegreeOne_coe _root_.ClassFormation.DegreeData.frobeniusPowerSum_coe _root_.ClassFormation.DegreeData.frobeniusQuotientAction_mk _root_.ClassFormation.DegreeData.frobeniusQuotientRepresentation_apply _root_.ClassFormation.DegreeData.frobeniusRestriction_chosenFiniteReciprocityFrobeniusLift _root_.ClassFormation.DegreeData.frobeniusRestriction_mul _root_.ClassFormation.DegreeData.mem_frobeniusFixedField_iff _root_.ClassFormation.DegreeData.mem_frobeniusFixedSubgroupWithin_iff _root_.ClassFormation.FiniteAbelianSubextension.extensionQuotientMk_apply _root_.ClassFormation.FiniteGaloisSubextension.classFieldCandidate_field _root_.ClassFormation.ValuationData.canonicalUnramifiedNormQuotientValuation_finiteNormClass _root_.ClassFormation.ValuationData.canonicalValueQuotientHom_mk _root_.ClassFormation.ValuationData.canonicalValueReduction_one _root_.ClassFormation.ValuationData.mem_infiniteUnitAddSubgroup_iff _root_.ClassFormation.ValuationData.mem_infiniteUnitNormSubgroup_iff _root_.ClassFormation.ValuationData.unramifiedNormQuotientValuation_finiteNormClass _root_.ClassFormation.ValuationData.unramifiedReciprocity_equiv_of_generator_apply _root_.ClassFormation.ValuationData.valuationAt_chosenPrimeElement _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.ClassFormation.conjugateStableAction_coe _root_.ClassFormation.cyclicNormClassHom_apply _root_.ClassFormation.finiteReciprocityNaturalityConjugation_mk _root_.ClassFormation.mem_normFilterBasis_iff _root_.ClassFormation.relativeConjugateCosetEquiv_mk _root_.ClassFormation.toZModPow_zHatToPadicInt _root_.ClassFormation.zHatPowNat_apply_toAdd _root_.ClassFormation.zHatPowNat_one _root_.ClassFormation.zHatReductionMul_apply_toAdd _root_.ClassFormation.zHatReductionRingHom_apply _root_.ClassFormation.zHatRingEquivProfiniteIntegerPrimeProduct_apply _root_.ClassFormation.zHatToPadicInt_intCast _root_.ClassFormation.zHatToProfiniteIntegerPrimeProduct_apply _root_.ClassFormation.zHatToProfiniteIntegerPrimeProduct_intCast _root_.ClassFormation.zHatUnitsContinuousMulEquivPrimeProduct_coe_apply _root_.IsDiscreteValuationRing.addVal_ringEquiv _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.KummerTheory.torsionQuotientEquivOfZHatMulDecomposition_mk _root_.KummerTheory.zHatUnitsContinuousMulEquivPrimeProduct_rationalCyclotomicCharacter _root_.LocalClassFieldTheory.finiteGaloisUnitsEquivAbstractFixedOfEmbedding_coe _root_.LocalClassFieldTheory.finiteGaloisUnitsEquivAbstractFixed_coe _root_.LocalClassFieldTheory.intrinsicFiniteAbstractBase_eq_base _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.OAI.PrimeDegreePackets.ThetaConstruction.schwartzCM_apply _root_.ClassFormation.DegreeData.inertiaConjugationCosetEquiv_mk _root_.infinitePlace_mult_smul
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

namespace LocalClassFieldTheory

open ClassFormation LocalFieldTheory

/-!
# Finite local reciprocity: the normalized local valuation is Henselian

For a nonarchimedean local field, the normalized discrete valuation on the
base unit group satisfies the Henselian valuation condition.  The value group is the copy of
the ordinary integers in the profinite integers.  For every finite abstract
field, including a non-normal one, the image after the abstract norm is the
ordinary residue-degree multiple of that value group.
-/

noncomputable section

open scoped NNReal ValuativeRel
/-- **Finite local reciprocity.**  The normalized valuation of a nonarchimedean local
field, on the actual fixed coefficient group in its separable closure, is a
Henselian valuation relative to the residue Frobenius degree datum. -/
noncomputable def localHenselianValuation
    (K : Type) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] :
    ValuationData (localResidueDatum K)
      (galoisAmbientUnitsRep K (SeparableClosure K)) := by
  refine
    { toAddMonoidHom := localBaseValuation K
      integers_mem := intToProCInteger_mem_localBaseValuation_range K
      canonical_value_quotient_bijective :=
        localCanonicalValueQuotientMap_bijective K
      norm_range := ?_ }
  intro F
  let H := F.field
  let := F.finite
  let E := abstractFixedField K (SeparableClosure K) H
  let : FiniteDimensional K E :=
    abstractFixedField_finiteDimensional K (SeparableClosure K) H F.finite

  let : UniformSpace K := IsTopologicalAddGroup.rightUniformSpace K
  let : IsUniformAddGroup K := isUniformAddGroup_of_addCommGroup
  let : (Valued.v : Valuation K
      (ValuativeRel.ValueGroupWithZero K)).RankOne :=
    { hom' := ValuativeRel.IsRankLeOne.nonempty.some.emb (R := K) |>.comp
        MonoidWithZeroHom.ValueGroup₀.embedding
      strictMono' := ValuativeRel.IsRankLeOne.nonempty.some.strictMono.comp
        MonoidWithZeroHom.ValueGroup₀.embedding_strictMono }
  let : NontriviallyNormedField K :=
    Valued.toNontriviallyNormedField
      (L := K) (Γ₀ := ValuativeRel.ValueGroupWithZero K)

  let : NontriviallyNormedField E :=
    spectralNorm.nontriviallyNormedField K E
  let : NormedSpace K E := spectralNorm.normedSpace K E
  let : CompleteSpace E := spectralNorm.completeSpace K E
  let : LocallyCompactSpace E :=
    LocallyCompactSpace.of_finiteDimensional_of_complete K E
  let : IsUltrametricDist E :=
    ⟨fun x y z => by
      change ‖x - z‖ ≤ max ‖x - y‖ ‖y - z‖
      rw [← sub_add_sub_cancel x y z]
      exact isNonarchimedean_spectralNorm
        (K := K) (L := E) (x - y) (y - z)⟩
  let : Valued E ℝ≥0 := NormedField.toValued
  let vE : Valuation E ℝ≥0 := Valued.v
  let : vE.IsNontrivial :=
    (inferInstance : (NormedField.valuation (K := E)).IsNontrivial)
  let : ValuativeRel E := ValuativeRel.ofValuation vE
  let : vE.Compatible := Valuation.Compatible.ofValuation vE
  let : ValuativeRel.IsNontrivial E :=
    (ValuativeRel.isNontrivial_iff_isNontrivial vE).2 inferInstance
  let : IsValuativeTopology E :=
    isValuativeTopology_of_valued_ofValuation E ℝ≥0
  let : IsNonarchimedeanLocalField E :=
    { toIsValuativeTopology := inferInstance
      toLocallyCompactSpace := inferInstance
      toIsNontrivial := inferInstance }

  let : (ValuativeRel.valuation K).HasExtension
      (ValuativeRel.valuation E) := by
    apply Valuation.HasExtension.ofComapInteger
    ext x
    change ValuativeRel.valuation E (algebraMap K E x) ≤ 1 ↔
      ValuativeRel.valuation K x ≤ 1
    rw [← (ValuativeRel.valuation E).vle_one_iff, vE.vle_one_iff]
    change spectralNorm K E (algebraMap K E x) ≤ 1 ↔
      ValuativeRel.valuation K x ≤ 1
    rw [spectralNorm_extends]
    exact Valued.toNormedField.norm_le_one_iff

  let : Algebra.IsIntegral 𝒪[K] 𝒪[E] := ⟨by
    intro y
    have hyv : vE (y : E) ≤ 1 := by
      apply (vE.vle_one_iff).1
      apply ((ValuativeRel.valuation E).vle_one_iff).2
      exact y.property
    have hynorm : ‖(y : E)‖ ≤ 1 := by
      have hynnnorm : ‖(y : E)‖₊ ≤ 1 := by
        simpa [vE, NormedField.valuation_apply] using hyv
      exact_mod_cast hynnnorm
    change spectralNorm K E (y : E) ≤ 1 at hynorm
    have hcoeffNorm :
        ∀ n : ℕ, ‖(minpoly K (y : E)).coeff n‖ ≤ 1 :=
      (spectralValue_le_one_iff
        (minpoly.monic (Algebra.IsIntegral.isIntegral (y : E)))).1
        (by simpa [spectralNorm] using hynorm)
    have hcoeff :
        (↑(minpoly K (y : E)).coeffs : Set K) ⊆
          (ValuativeRel.valuation K).integer := by
      intro c hc
      obtain ⟨n, _hn, rfl⟩ := Polynomial.mem_coeffs_iff.mp hc
      exact ((ValuativeRel.valuation K).mem_integer_iff _).2
        (Valued.toNormedField.norm_le_one_iff.mp (hcoeffNorm n))
    let p : Polynomial 𝒪[K] :=
      (minpoly K (y : E)).toSubring
        (ValuativeRel.valuation K).integer hcoeff
    refine ⟨p, ?_, ?_⟩
    · exact (Polynomial.monic_toSubring
        (minpoly K (y : E)) (ValuativeRel.valuation K).integer hcoeff).2
          (minpoly.monic (Algebra.IsIntegral.isIntegral (y : E)))
    · apply Subtype.ext
      have hmaproot :
          Polynomial.aeval (y : E)
            (p.map (algebraMap 𝒪[K] K)) = 0 := by
        dsimp only [p]
        rw [show algebraMap 𝒪[K] K =
          (ValuativeRel.valuation K).integer.subtype from rfl,
          Polynomial.map_toSubring]
        exact minpoly.aeval K (y : E)
      change (ValuativeRel.valuation E).integer.subtype
        (Polynomial.eval₂ (algebraMap 𝒪[K] 𝒪[E]) y p) = (0 : E)
      rw [Polynomial.hom_eval₂]
      change Polynomial.aeval (y : E) p = 0
      rwa [Polynomial.aeval_map_algebraMap K (y : E) p] at hmaproot⟩

  let : Algebra.IsIntegral
      (ValuativeRel.valuation K).valuationSubring
      (ValuativeRel.valuation E).valuationSubring := by
    change Algebra.IsIntegral 𝒪[K] 𝒪[E]
    infer_instance
  let hIntegralClosure : IsIntegralClosure
      (ValuativeRel.valuation E).valuationSubring
      (ValuativeRel.valuation K).valuationSubring E :=
    ValuationTheory.DiscreteValuationField.Valuation.valuationSubring_isIntegralClosure_of_isIntegral
      (ValuativeRel.valuation K) (ValuativeRel.valuation E)
  let : IsIntegralClosure 𝒪[E] 𝒪[K] E := by
    change IsIntegralClosure
      (ValuativeRel.valuation E).valuationSubring
      (ValuativeRel.valuation K).valuationSubring E
    exact hIntegralClosure

  rw [localResidueDatum_residueDegree_eq_residueFinrank K F]
  convert localBaseValuation_comp_normToBase_range_eq_residueFinrank K H using 3
  all_goals first | exact residueAlgebra_eq | exact residueModule_eq | exact residueAlgebra_eq.symm | exact residueModule_eq.symm | (rw [residueAlgebra_eq]; exact residueModule_eq.symm) | (simp only [residueAlgebra_eq]; exact residueModule_eq.symm) | (symm; rw [residueAlgebra_eq]; exact residueModule_eq) | rfl

end
end LocalClassFieldTheory
end

section
-- module Solutions.OAIQ244_DUKE.AlgebraicNumberTheory_Ramification_Splitting_FinitePlaceIdeal
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.residueFieldZModAlgebra _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedIntegralAlgebraContextValuationSubringAlgebra _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.LocalClassFieldTheory.normalizationIntegerRingIsIntegralClosure _root_.chosenFinitePlaceCompletionAlgebra
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
/-- There are finitely many finite places of `L` above a fixed finite
place of `K`. -/
theorem finite_finitePlaceBelow_fibre
    (v : HeightOneSpectrum (𝓞 K)) :
    Set.Finite
      {W : HeightOneSpectrum (𝓞 L) |
        finitePlaceBelow (K := K) W = v} := by
  apply Set.Finite.of_finite_image
  · apply
      (Algebra.QuasiFinite.finite_primesOver
        (R := 𝓞 K) (S := 𝓞 L) v.asIdeal).subset
    rintro I ⟨W, hW, rfl⟩
    exact
      ⟨W.isPrime, ⟨(congrArg HeightOneSpectrum.asIdeal hW).symm⟩⟩
  · intro W₁ _ W₂ _ h
    apply HeightOneSpectrum.ext
    exact h

omit [FiniteDimensional K L] [IsGalois K L] in
/-- The inverse image of a finite set of base finite places under
contraction is finite. -/
theorem Set.Finite.preimage_finitePlaceBelow
    {S : Set (HeightOneSpectrum (𝓞 K))}
    (hS : S.Finite) :
    {W : HeightOneSpectrum (𝓞 L) |
      finitePlaceBelow (K := K) W ∈ S}.Finite := by
  show
    ((finitePlaceBelow (K := K)) ⁻¹' S).Finite
  exact hS.preimage'
    (fun v _ => finite_finitePlaceBelow_fibre
      (K := K) (L := L) v)
end
end

section
-- module Solutions.OAIQ244_DUKE.LocalField_Analytic_LogExpSeries_PrincipalUnitLog
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_isCompleteDiscrete _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalClassFieldTheory.localSeparableValuationHasExtension _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.AdicPrincipalUnits.instAddCommGroup _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.AdicPrincipalUnits.instTopologicalSpace _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.DiscretePrincipalUnitQuotient.instAddCommGroup _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitInverseLimitCarrierPadicModule _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitQuotientCarrierPadicModule _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.PrincipalUnitProdiscreteLimit.instAddCommGroup _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.PrincipalUnitProdiscreteLimit.instTopologicalSpace _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitPadicModule _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitPadicSMul _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.residueFieldZModAlgebra _root_.LocalFieldTheory.DiscreteValuationField.Examples.Qp.padicDVRValuation_isCompleteDiscrete _root_.LocalFieldTheory.DiscreteValuationField.Examples.Qp.padicDVRValuation_isRankOneDiscrete _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedIntegralAlgebraContextValuationSubringAlgebra _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedQPadicContextValuationExtension _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedWithZeroValuationContextIntegralAlgebra _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.RamificationTheory.HilbertRamification.Higher.lowerRamificationGroup.instNormal _root_.RamificationTheory.HilbertRamification.ValuationSubring.selectedResidueField.instAlgebra _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.LocalClassFieldTheory.normalizationIntegerRingIsIntegralClosure _root_.RamificationTheory.HilbertRamification.CompleteDVF.decompositionGroupMulSemiringAction _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.chosenFinitePlaceCompletionAlgebra _root_.finiteLocalUnitsOpen _root_.relativeAdeleRingIntermediateAlgebra _root_.relativeAdeleRingTopIntermediateAlgebra
attribute [-simp] _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.IsDiscreteValuationRing.addVal_ringEquiv _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.EqualCharacteristicLaurent.coeffHom_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.EqualCharacteristicLaurent.powerSeriesEvalHom_C _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.EqualCharacteristicLaurent.powerSeriesEvalHom_X _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.EqualCharacteristicLaurent.powerSeriesEvalSubringHom_C _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.EqualCharacteristicLaurent.powerSeriesEvalSubringHom_X _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.AdicPrincipalUnits.addEquiv_map_smul _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.AdicPrincipalUnits.of_val _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.AdicPrincipalUnits.val_of _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.DiscretePrincipalUnitQuotient.addEquiv_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.DiscretePrincipalUnitQuotient.addEquiv_map_smul _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.DiscretePrincipalUnitQuotient.addEquiv_of _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.DiscretePrincipalUnitQuotient.addEquiv_symm_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.DiscretePrincipalUnitQuotient.of_val _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.DiscretePrincipalUnitQuotient.val_of _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.DiscretePrincipalUnitQuotient.val_transition _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.adicPrincipalUnitsHomeomorphUnderlying_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.iwasawaGlobalInverseLimitCarrier_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitAddEquivInverseLimitCarrier_map_smul _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitAddHomeomorphInverseLimitCarrier_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitInverseLimitCarrierEval_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitInverseLimitCarrierPadic_smul_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitMulEquivInverseLimitCarrier_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitPadic_smul_carrier_coordinate _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitProdiscreteLimitHomeomorphUnderlying_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitQuotientCarrierPadicScalar_eq_smul _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitQuotientCarrierToFull_mk _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitQuotientCarrierTransition_mk _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.uniformizerHigherUnitQuotientEquiv_mk _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.PrincipalUnitProdiscreteLimit.addEquiv_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.PrincipalUnitProdiscreteLimit.addEquiv_map_smul _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.PrincipalUnitProdiscreteLimit.addEquiv_symm_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.PrincipalUnitProdiscreteLimit.coordinate_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.PrincipalUnitProdiscreteLimit.of_val _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.PrincipalUnitProdiscreteLimit.val_of _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.adicPrincipalUnitsContinuousAddEquivUnderlyingOfWithZeroValuation_map_smul _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.adicPrincipalUnitsHomeomorphProdiscreteLimit_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.adicPrincipalUnitsHomeomorphProdiscreteLimit_to_addEquiv _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.iwasawaDegreeTerm_zero _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.iwasawaGn_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.iwasawaPartialProduct_zero_input _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.iwasawaSeedAtLevel_val _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.iwasawaSeedIdeal_val _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.iwasawaSeed_val _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitPadic_natCast_smul _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitPadic_nsmul_eq_pow _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitPadic_smul_def _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitSuccQuotAddEquivResidue_iwasawaSeed _root_.LocalFieldTheory.DiscreteValuationField.LocalField.higherPrincipalUnitAddToFirst_smul _root_.LocalFieldTheory.DiscreteValuationField.LocalField.laurentSeriesEquivLaurentImageSubfield_apply_coe _root_.LocalFieldTheory.DiscreteValuationField.LocalField.padicIntToValuationSubring_coe _root_.LocalFieldTheory.DiscreteValuationField.MultiplicativeIntegerValuation.fieldUnitDecompositionLogHomOfPrincipalUnitHom_apply _root_.LocalFieldTheory.DiscreteValuationField.MultiplicativeIntegerValuation.fieldUnitDecompositionLogHomOfPrincipalUnitHom_principal _root_.LocalFieldTheory.DiscreteValuationField.MultiplicativeIntegerValuation.fieldUnitDecompositionLogHomOfPrincipalUnitHom_root _root_.LocalFieldTheory.DiscreteValuationField.MultiplicativeIntegerValuation.fieldUnitDecompositionLogHomOfPrincipalUnitHom_uniformizer _root_.LocalFieldTheory.DiscreteValuationField.MultiplicativeIntegerValuation.fieldUnitDecompositionLogHomWithUniformizerValue_apply _root_.LocalFieldTheory.DiscreteValuationField.MultiplicativeIntegerValuation.fieldUnitDecompositionLogHomWithUniformizerValue_principal _root_.LocalFieldTheory.DiscreteValuationField.MultiplicativeIntegerValuation.fieldUnitDecompositionLogHomWithUniformizerValue_root _root_.LocalFieldTheory.DiscreteValuationField.MultiplicativeIntegerValuation.fieldUnitDecompositionLogHomWithUniformizerValue_uniformizer _root_.LocalFieldTheory.DiscreteValuationField.MultiplicativeIntegerValuation.fieldUnitLogHomOfPrincipalUnitHom_apply _root_.LocalFieldTheory.DiscreteValuationField.MultiplicativeIntegerValuation.fieldUnitLogHomWithUniformizerValue_apply _root_.LocalFieldTheory.DiscreteValuationField.MultiplicativeIntegerValuation.principalUnitExpSeriesHomOfMaximalIdealPow_apply _root_.LocalFieldTheory.DiscreteValuationField.MultiplicativeIntegerValuation.principalUnitLogPartialSum_one_ofWithZeroValuation _root_.LocalFieldTheory.DiscreteValuationField.MultiplicativeIntegerValuation.principalUnitLogPartialSum_zero_ofWithZeroValuation _root_.LocalFieldTheory.DiscreteValuationField.MultiplicativeIntegerValuation.principalUnitLogSeriesHomOfWithZeroValuationScaled_apply_toAdd _root_.LocalFieldTheory.DiscreteValuationField.MultiplicativeIntegerValuation.principalUnitLogSeriesHom_apply_toAdd_ofWithZeroValuation _root_.LocalFieldTheory.DiscreteValuationField.MultiplicativeIntegerValuation.principalUnitLogSeries_one_ofWithZeroValuation _root_.LocalFieldTheory.IsNonarchimedeanLocalField.multiplicativeIntegerValuation_val _root_.LocalFieldTheory.Padic.integerRingEquivPadicDVRValuationSubring_coe _root_.LocalFieldTheory.localIntegerValuationSubringEquiv_apply_coe _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.LocalFieldTheory.residueField_algebraMap_residue _root_.LubinTate.LubinTateSeries.standardLubinTateSeries_toPowerSeries _root_.LubinTate.SameUniformizer.coeff_recursiveIntertwiner _root_.LubinTate.SameUniformizer.constantCoeff_inVariable _root_.LubinTate.SameUniformizer.intertwinerApproximation_zero _root_.LubinTate.SameUniformizer.standardLubinTateEndomorphism_coeff_one _root_.LubinTate.standardLubinTateBaseUniformizerUnit_coe _root_.LubinTate.standardLubinTateChangedUniformizerUnit_coe _root_.LubinTate.standardLubinTateLevelGenerator_coe _root_.LubinTate.standardLubinTatePolynomialIterateOverSeparableClosure_eval _root_.LubinTate.standardLubinTatePolynomialIterate_derivative_eval_zero _root_.LubinTate.standardLubinTatePolynomialIterate_eval_zero _root_.LubinTate.standardLubinTatePolynomialIterate_zero _root_.LubinTate.standardLubinTatePolynomial_derivative_eval_zero _root_.LubinTate.standardLubinTatePolynomial_eval _root_.LubinTate.standardLubinTatePolynomial_toPowerSeries _root_.LubinTate.standardLubinTatePolynomial_toPowerSeries_eq_series _root_.LubinTate.standardLubinTatePrimitivePointInteger_coe _root_.LubinTate.standardLubinTatePrimitivePolynomialOverField_coeff_zero _root_.LubinTate.standardLubinTatePrimitivePolynomial_coeff_zero _root_.LubinTate.standardLubinTateUnitFactorFieldUnit_coe _root_.OAI.PrimeDegreePackets.ThetaConstruction.schwartzCM_apply _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteResidueActionOfHenselianDVF_apply _root_.RamificationTheory.HilbertRamification.Higher.dvfValuationSubringUnitAut_apply _root_.RamificationTheory.HilbertRamification.Higher.lowerRamificationGroup_neg_one _root_.RamificationTheory.HilbertRamification.Higher.mem_dvfHigherPrincipalUnitGroup_iff _root_.RamificationTheory.HilbertRamification.Higher.mem_lowerRamificationGroup_iff _root_.RamificationTheory.HilbertRamification.Higher.mem_valuationSubringDisplacementSubalgebraOfUniqueExtension_iff _root_.RamificationTheory.HilbertRamification.Higher.realRamificationIdeal_nat _root_.RamificationTheory.HilbertRamification.Higher.realRamificationIdeal_neg_one _root_.RamificationTheory.HilbertRamification.Higher.valuationSubringAutOfUniqueExtension_apply_coe _root_.RamificationTheory.HilbertRamification.Higher.valuationSubringAutOfUniqueExtension_apply_inv_apply _root_.RamificationTheory.HilbertRamification.Higher.valuationSubringAutOfUniqueExtension_mul_apply _root_.RamificationTheory.HilbertRamification.Higher.valuationSubringAutOfUniqueExtension_one_apply _root_.infinitePlace_mult_smul
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

/-- Sharp ramified endpoint form of the logarithm: if `u ∈ U^n` and
`n > e/(p-1)`, then `Log(u)` lies in `m^n`. -/
noncomputable def principalUnitLogSeriesOfHigherPrincipalUnitGroupOfWithZeroValuationScaled
    (v : _root_.Valuation K (WithZero (Multiplicative ℤ)))
    [ValuationTheory.DiscreteValuationField.Valuation.IsCompleteDiscrete v]
    {p : ℕ} [Fact p.Prime] (e n : ℕ)
    {π : (completeDVFOfWithZeroValuation v).valuationSubring}
    (hπ : v.IsUniformizer (π : K))
    (hπval : v (π : K) = WithZero.exp (-1 : ℤ))
    (hn : 1 ≤ n)
    (hlevel : (e : ℚ) / ((p : ℚ) - 1) < (n : ℚ))
    (hnK : ∀ m : ℕ, (((m + 1 : ℕ) : K) ≠ 0))
    (hnval : ∀ m : ℕ,
      v (((m + 1 : ℕ) : K)) =
        WithZero.exp (-((e : ℤ) * (padicValNat p (m + 1) : ℤ))))
    (hcomplete :
      letI : Valued K (WithZero (Multiplicative ℤ)) := Valued.mk' v
      CompleteSpace K)
    (u : (LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup (completeDVFOfWithZeroValuation v)) n) :
    ((completeDVFOfWithZeroValuation v).maximalIdeal ^ n :
      Ideal (completeDVFOfWithZeroValuation v).valuationSubring) := by
  let F : CompleteDVF.{u, 0} K := completeDVFOfWithZeroValuation v
  let aSub : F.valuationSubring :=
    ((u : F.valuationSubringˣ) : F.valuationSubring) - 1
  let x : K := (aSub : K)
  have haMem : aSub ∈ F.maximalIdeal ^ n := by
    simpa [aSub] using
      (LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.mem_iff
        (F := F) n (u : F.valuationSubringˣ)).1 u.property
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
          (v := v) (π := π) hπ hπval n aSub haMem hx
    exact lt_of_lt_of_le hlevel (by exact_mod_cast hge)
  have haMemOne : aSub ∈ F.maximalIdeal := by
    have hle : F.maximalIdeal ^ n ≤ F.maximalIdeal ^ 1 :=
      Ideal.pow_le_pow_right hn
    simpa [pow_one] using hle haMem
  have hxlt : v x < (1 : WithZero (Multiplicative ℤ)) := by
    have hbound := (CompleteDVF.mem_maximalIdeal_iff F aSub).1 haMemOne
    change v (aSub : K) < 1 at hbound
    exact hbound
  have hbLe :
      v (logOnePlusSeriesFieldOfWithZeroValuation v x hnK) ≤
        (1 : WithZero (Multiplicative ℤ)) := by
    by_cases hx : x = 0
    · simp [x, hx]
    · have hv :
          v (logOnePlusSeriesFieldOfWithZeroValuation v x hnK) = v x :=
        valuation_logOnePlusSeriesField_eq_self_of_scaled_inv_sub_one_lt
          (v := v) (p := p) e (x := x) hx hnK hnval
          hxlt (hxthreshold hx) hcomplete
      have hxInt : v x ≤ (1 : WithZero (Multiplicative ℤ)) :=
        le_of_lt hxlt
      simpa [hv] using hxInt
  let b : F.valuationSubring :=
    ⟨logOnePlusSeriesFieldOfWithZeroValuation v x hnK,
      (CompleteDVF.mem_valuationSubring_iff F
        (logOnePlusSeriesFieldOfWithZeroValuation v x hnK)).2
        (by
          change v (logOnePlusSeriesFieldOfWithZeroValuation v x hnK) ≤ 1
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
          valuation_logOnePlusSeriesField_eq_self_of_scaled_inv_sub_one_lt
            (v := v) (p := p) e (x := x) hx hnK hnval
            hxlt (hxthreshold hx) hcomplete
      have hge :
          (n : ℤ) ≤
            (ofWithZeroValuation v).val (Units.mk0 x hx) := by
        simpa [F, x] using
          ofWithZeroValuation_val_ge_of_mem_maximalIdeal_pow
            (v := v) (π := π) hπ hπval n aSub haMem hx
      have hvaleq :
          (ofWithZeroValuation v).val (Units.mk0 (b : K) hbne) =
            (ofWithZeroValuation v).val (Units.mk0 x hx) := by
        simp [ofWithZeroValuation_val, hv]
      rw [hvaleq]
      exact hge
  exact ⟨b, hbmem⟩

/-- Endpoint package for the deep exponential–logarithm equivalence as the actual group isomorphism:
if the evaluated composites are identities, then the source and target groups are
multiplicatively isomorphic after wrapping the additive ideal by
`Multiplicative`.  The multiplicativity of the forward map is supplied by the
scaled exponential additivity proved above. -/
noncomputable def principalUnitExpLogMulEquivOfExact_ofWithZeroValuationScaled
    (v : _root_.Valuation K (WithZero (Multiplicative ℤ)))
    [ValuationTheory.DiscreteValuationField.Valuation.IsCompleteDiscrete v]
    [Algebra ℚ K]
    {p : ℕ} [Fact p.Prime] (e n : ℕ)
    {π : (completeDVFOfWithZeroValuation v).valuationSubring}
    (hπ : v.IsUniformizer (π : K))
    (hπval : v (π : K) = WithZero.exp (-1 : ℤ))
    (hn : 1 ≤ n)
    (hlevel : (e : ℚ) / ((p : ℚ) - 1) < (n : ℚ))
    (hnKexp : ∀ m : ℕ, (((m.factorial : ℕ) : K) ≠ 0))
    (hnvalExp : ∀ m : ℕ,
      v (((m.factorial : ℕ) : K)) =
        WithZero.exp (-((e : ℤ) * (padicValNat p m.factorial : ℤ))))
    (hnKlog : ∀ m : ℕ, (((m + 1 : ℕ) : K) ≠ 0))
    (hnvalLog : ∀ m : ℕ,
      v (((m + 1 : ℕ) : K)) =
        WithZero.exp (-((e : ℤ) * (padicValNat p (m + 1) : ℤ))))
    (hcomplete :
      letI : Valued K (WithZero (Multiplicative ℤ)) := Valued.mk' v
      CompleteSpace K)
    (hlog_exp :
      ∀ a :
        ((completeDVFOfWithZeroValuation v).maximalIdeal ^ n :
          Ideal (completeDVFOfWithZeroValuation v).valuationSubring),
        principalUnitLogSeriesOfHigherPrincipalUnitGroupOfWithZeroValuationScaled
          (v := v) (p := p) e n (π := π) hπ hπval hn hlevel
          hnKlog hnvalLog hcomplete
          (principalUnitExpSeriesOfMaximalIdealPowOfWithZeroValuationScaled
            (v := v) (p := p) e n (π := π) hπ hπval hn hlevel
            hnKexp hnvalExp hcomplete a) =
        a)
    (hexp_log :
      ∀ u : (LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup (completeDVFOfWithZeroValuation v)) n,
        principalUnitExpSeriesOfMaximalIdealPowOfWithZeroValuationScaled
          (v := v) (p := p) e n (π := π) hπ hπval hn hlevel
          hnKexp hnvalExp hcomplete
          (principalUnitLogSeriesOfHigherPrincipalUnitGroupOfWithZeroValuationScaled
            (v := v) (p := p) e n (π := π) hπ hπval hn hlevel
            hnKlog hnvalLog hcomplete u) =
        u) :
    Multiplicative
      ((completeDVFOfWithZeroValuation v).maximalIdeal ^ n :
        Ideal (completeDVFOfWithZeroValuation v).valuationSubring) ≃*
      (LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup (completeDVFOfWithZeroValuation v)) n where
  toFun a :=
    principalUnitExpSeriesOfMaximalIdealPowOfWithZeroValuationScaled
      (v := v) (p := p) e n (π := π) hπ hπval hn hlevel
      hnKexp hnvalExp hcomplete a.toAdd
  invFun u :=
    Multiplicative.ofAdd
      (principalUnitLogSeriesOfHigherPrincipalUnitGroupOfWithZeroValuationScaled
        (v := v) (p := p) e n (π := π) hπ hπval hn hlevel
        hnKlog hnvalLog hcomplete u)
  left_inv a := by
    apply Multiplicative.ext
    simpa using hlog_exp a.toAdd
  right_inv u := by
    simpa using hexp_log u
  map_mul' a b := by
    simpa using
      principalUnitExpSeries_maximalIdealPow_add_eq_mul_ofWithZeroValuationScaled
        (v := v) (p := p) e n (π := π) hπ hπval hn hlevel
        hnKexp hnvalExp hcomplete a.toAdd b.toAdd

end MultiplicativeIntegerValuation
end LocalFieldTheory.DiscreteValuationField

end
end

section
-- module Solutions.OAIQ244_DUKE.LocalField_Analytic_ContinuousFieldUnitLog
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_isCompleteDiscrete _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.DiscreteNthRootsSubgroup.instTopologicalSpaceSubtypeUnitsMemSubgroup _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalClassFieldTheory.localSeparableValuationHasExtension _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.AdicPrincipalUnits.instAddCommGroup _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.AdicPrincipalUnits.instTopologicalSpace _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.DiscretePrincipalUnitQuotient.instAddCommGroup _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitInverseLimitCarrierPadicModule _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitQuotientCarrierPadicModule _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.PrincipalUnitProdiscreteLimit.instAddCommGroup _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.PrincipalUnitProdiscreteLimit.instTopologicalSpace _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitPadicModule _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitPadicSMul _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.residueFieldZModAlgebra _root_.LocalFieldTheory.DiscreteValuationField.Examples.Qp.padicDVRValuation_isCompleteDiscrete _root_.LocalFieldTheory.DiscreteValuationField.Examples.Qp.padicDVRValuation_isRankOneDiscrete _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedIntegralAlgebraContextValuationSubringAlgebra _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedQPadicContextValuationExtension _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedWithZeroValuationContextIntegralAlgebra _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.LubinTate.compatibleGroupFamiliesGroup _root_.OAI.PrimeDegreePackets.instNonemptyLeafTestSpace _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.RamificationTheory.HilbertRamification.Higher.lowerRamificationGroup.instNormal _root_.RayClass.approximationCompletionTopologicalSpace _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.LocalClassFieldTheory.normalizationIntegerRingIsIntegralClosure _root_.RamificationTheory.HilbertRamification.CompleteDVF.decompositionGroupMulSemiringAction _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.chosenFinitePlaceBaseValuationIsNontrivial _root_.finiteLocalUnitsOpen
attribute [-simp] _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.IsDiscreteValuationRing.addVal_ringEquiv _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.EqualCharacteristicLaurent.coeffHom_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.EqualCharacteristicLaurent.powerSeriesEvalHom_C _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.EqualCharacteristicLaurent.powerSeriesEvalHom_X _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.EqualCharacteristicLaurent.powerSeriesEvalSubringHom_C _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.EqualCharacteristicLaurent.powerSeriesEvalSubringHom_X _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.AdicPrincipalUnits.addEquiv_map_smul _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.AdicPrincipalUnits.of_val _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.AdicPrincipalUnits.val_of _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.DiscretePrincipalUnitQuotient.addEquiv_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.DiscretePrincipalUnitQuotient.addEquiv_map_smul _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.DiscretePrincipalUnitQuotient.addEquiv_of _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.DiscretePrincipalUnitQuotient.addEquiv_symm_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.DiscretePrincipalUnitQuotient.of_val _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.DiscretePrincipalUnitQuotient.val_of _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.DiscretePrincipalUnitQuotient.val_transition _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.adicPrincipalUnitsHomeomorphUnderlying_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.iwasawaGlobalInverseLimitCarrier_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitAddEquivInverseLimitCarrier_map_smul _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitAddHomeomorphInverseLimitCarrier_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitInverseLimitCarrierEval_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitInverseLimitCarrierPadic_smul_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitMulEquivInverseLimitCarrier_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitPadic_smul_carrier_coordinate _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitProdiscreteLimitHomeomorphUnderlying_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitQuotientCarrierPadicScalar_eq_smul _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitQuotientCarrierToFull_mk _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitQuotientCarrierTransition_mk _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.uniformizerHigherUnitQuotientEquiv_mk _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.PrincipalUnitProdiscreteLimit.addEquiv_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.PrincipalUnitProdiscreteLimit.addEquiv_map_smul _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.PrincipalUnitProdiscreteLimit.addEquiv_symm_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.PrincipalUnitProdiscreteLimit.coordinate_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.PrincipalUnitProdiscreteLimit.of_val _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.PrincipalUnitProdiscreteLimit.val_of _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.adicPrincipalUnitsContinuousAddEquivUnderlyingOfWithZeroValuation_map_smul _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.adicPrincipalUnitsHomeomorphProdiscreteLimit_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.adicPrincipalUnitsHomeomorphProdiscreteLimit_to_addEquiv _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.iwasawaDegreeTerm_zero _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.iwasawaGn_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.iwasawaPartialProduct_zero_input _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.iwasawaSeedAtLevel_val _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.iwasawaSeedIdeal_val _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.iwasawaSeed_val _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitPadic_natCast_smul _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitPadic_nsmul_eq_pow _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitPadic_smul_def _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitSuccQuotAddEquivResidue_iwasawaSeed _root_.LocalFieldTheory.DiscreteValuationField.LocalField.higherPrincipalUnitAddToFirst_smul _root_.LocalFieldTheory.DiscreteValuationField.LocalField.laurentSeriesEquivLaurentImageSubfield_apply_coe _root_.LocalFieldTheory.DiscreteValuationField.LocalField.padicIntToValuationSubring_coe _root_.LocalFieldTheory.DiscreteValuationField.MultiplicativeIntegerValuation.principalUnitExpSeriesHomOfMaximalIdealPow_apply _root_.LocalFieldTheory.IsNonarchimedeanLocalField.multiplicativeIntegerValuation_val _root_.LocalFieldTheory.Padic.integerRingEquivPadicDVRValuationSubring_coe _root_.LocalFieldTheory.localIntegerValuationSubringEquiv_apply_coe _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.LocalFieldTheory.residueField_algebraMap_residue _root_.LubinTate.LubinTateSeries.standardLubinTateSeries_toPowerSeries _root_.LubinTate.SameUniformizer.coeff_recursiveIntertwiner _root_.LubinTate.SameUniformizer.constantCoeff_inVariable _root_.LubinTate.SameUniformizer.intertwinerApproximation_zero _root_.LubinTate.SameUniformizer.standardLubinTateEndomorphism_coeff_one _root_.LubinTate.standardLubinTateBaseUniformizerUnit_coe _root_.LubinTate.standardLubinTateChangedUniformizerUnit_coe _root_.LubinTate.standardLubinTateLevelGenerator_coe _root_.LubinTate.standardLubinTatePolynomialIterateOverSeparableClosure_eval _root_.LubinTate.standardLubinTatePolynomialIterate_derivative_eval_zero _root_.LubinTate.standardLubinTatePolynomialIterate_eval_zero _root_.LubinTate.standardLubinTatePolynomialIterate_zero _root_.LubinTate.standardLubinTatePolynomial_derivative_eval_zero _root_.LubinTate.standardLubinTatePolynomial_eval _root_.LubinTate.standardLubinTatePolynomial_toPowerSeries _root_.LubinTate.standardLubinTatePolynomial_toPowerSeries_eq_series _root_.LubinTate.standardLubinTatePrimitivePointInteger_coe _root_.LubinTate.standardLubinTatePrimitivePolynomialOverField_coeff_zero _root_.LubinTate.standardLubinTatePrimitivePolynomial_coeff_zero _root_.LubinTate.standardLubinTateUnitFactorFieldUnit_coe _root_.OAI.PrimeDegreePackets.ThetaConstruction.schwartzCM_apply _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteResidueActionOfHenselianDVF_apply _root_.RamificationTheory.HilbertRamification.Higher.dvfValuationSubringUnitAut_apply _root_.RamificationTheory.HilbertRamification.Higher.lowerRamificationGroup_neg_one _root_.RamificationTheory.HilbertRamification.Higher.mem_dvfHigherPrincipalUnitGroup_iff _root_.RamificationTheory.HilbertRamification.Higher.mem_lowerRamificationGroup_iff _root_.RamificationTheory.HilbertRamification.Higher.mem_valuationSubringDisplacementSubalgebraOfUniqueExtension_iff _root_.RamificationTheory.HilbertRamification.Higher.realRamificationIdeal_nat _root_.RamificationTheory.HilbertRamification.Higher.realRamificationIdeal_neg_one _root_.RamificationTheory.HilbertRamification.Higher.valuationSubringAutOfUniqueExtension_apply_coe _root_.RamificationTheory.HilbertRamification.Higher.valuationSubringAutOfUniqueExtension_apply_inv_apply _root_.RamificationTheory.HilbertRamification.Higher.valuationSubringAutOfUniqueExtension_mul_apply _root_.RamificationTheory.HilbertRamification.Higher.valuationSubringAutOfUniqueExtension_one_apply _root_.infinitePlace_mult_smul
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

/-!
# The local-field logarithm

This file packages the ramification-scaled principal-unit logarithm as a
continuous homomorphism and extends it to field units with the unique
uniformizer value forced by `log p = 0`.
-/

noncomputable section

universe u

namespace LocalFieldTheory.DiscreteValuationField
namespace MultiplicativeIntegerValuation

open Filter
open scoped Topology

variable {K : Type u} [Field K]

/-- The ramification-scaled logarithm homomorphism on first principal units is
continuous.  Near the identity its valuation agrees with that of `u - 1`,
because one may restrict to an arbitrarily deep ball above `e/(p-1)`. -/
theorem continuous_principalUnitLogSeriesHomOfWithZeroValuationScaled
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
    letI : Valued K (WithZero (Multiplicative ℤ)) := Valued.mk' v
    Continuous
      (principalUnitLogSeriesHomOfWithZeroValuationScaled
        (v := v) (p := p) e hnK hnval hcomplete) := by
  let : Valued K (WithZero (Multiplicative ℤ)) := Valued.mk' v
  let F : ValuationTheory.DiscreteValuationField.CompleteDVF.{u, 0} K := completeDVFOfWithZeroValuation v
  have hMulSubring :
      Continuous (fun z : F.valuationSubring × F.valuationSubring =>
        z.1 * z.2) := by
    apply Continuous.subtype_mk
    exact
      (continuous_subtype_val.comp continuous_fst).mul
        (continuous_subtype_val.comp continuous_snd)
  let : ContinuousMul F.valuationSubring := ⟨hMulSubring⟩
  have hInv :
      Continuous (fun u : F.valuationSubringˣ => u⁻¹) := by
    rw [Units.continuous_iff]
    constructor
    · change Continuous (fun u : F.valuationSubringˣ =>
        ((u⁻¹ : F.valuationSubringˣ) : F.valuationSubring))
      exact Units.continuous_coe_inv
    · simpa using (Units.continuous_val :
        Continuous (fun u : F.valuationSubringˣ =>
          (u : F.valuationSubring)))
  have hMul :
      Continuous (fun z : F.valuationSubringˣ × F.valuationSubringˣ =>
        z.1 * z.2) := by
    rw [Units.continuous_iff]
    constructor
    · exact
        (Units.continuous_val.comp continuous_fst).mul
          (Units.continuous_val.comp continuous_snd)
    · change Continuous (fun z : F.valuationSubringˣ × F.valuationSubringˣ =>
        (((z.1 * z.2)⁻¹ : F.valuationSubringˣ) : F.valuationSubring))
      have hc : Continuous
          (fun z : F.valuationSubringˣ × F.valuationSubringˣ =>
            ((z.1⁻¹ : F.valuationSubringˣ) : F.valuationSubring) *
              ((z.2⁻¹ : F.valuationSubringˣ) : F.valuationSubring)) :=
        (Units.continuous_coe_inv.comp continuous_fst).mul
          (Units.continuous_coe_inv.comp continuous_snd)
      simpa [Units.val_inv_eq_inv_val, mul_comm] using hc
  let : ContinuousMul F.valuationSubringˣ := ⟨hMul⟩
  let : ContinuousInv F.valuationSubringˣ := ⟨hInv⟩
  have : IsTopologicalGroup F.valuationSubringˣ := by infer_instance
  have : IsTopologicalGroup ((LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup F) 1) := by
    infer_instance
  let φ :=
    principalUnitLogSeriesHomOfWithZeroValuationScaled
      (v := v) (p := p) e hnK hnval hcomplete
  apply continuous_of_continuousAt_one φ
  dsimp [φ, principalUnitLogSeriesHomOfWithZeroValuationScaled]
  rw [ContinuousAt]
  suffices hlog :
    Tendsto
      (fun u : (LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup (completeDVFOfWithZeroValuation v)) 1 =>
        principalUnitLogSeriesOfWithZeroValuation v u hnK)
      (𝓝 1) (𝓝 0) by
    rw [principalUnitLogSeries_one_ofWithZeroValuation v hnK]
    change Tendsto
      (fun u => Multiplicative.ofAdd
        (principalUnitLogSeriesOfWithZeroValuation v u hnK))
      (𝓝 1) (𝓝 (Multiplicative.ofAdd (0 : K)))
    exact (continuous_ofAdd.tendsto (0 : K)).comp hlog
  rw [(Valued.hasBasis_nhds_zero K
    (WithZero (Multiplicative ℤ))).tendsto_right_iff]
  intro γ _
  let γ' : (WithZero (Multiplicative ℤ))ˣ :=
    Units.map (MonoidWithZeroHom.ValueGroup₀.embedding
      (f := (.ofClass v))) γ
  obtain ⟨N₀, hN₀γ⟩ :=
    WithZero.exists_exp_neg_natCast_lt γ'.ne_zero
  obtain ⟨N₁, hN₁⟩ : ∃ N₁ : ℕ,
      (e : ℚ) / ((p : ℚ) - 1) < (N₁ : ℚ) :=
    exists_nat_gt ((e : ℚ) / ((p : ℚ) - 1))
  let N := max N₀ N₁
  have hNγ : WithZero.exp (-(N : ℤ)) <
      (γ' : WithZero (Multiplicative ℤ)) := by
    exact lt_of_le_of_lt
      (by
        apply WithZero.exp_le_exp.mpr
        simp only [neg_le_neg_iff]
        exact_mod_cast Nat.le_max_left N₀ N₁)
      hN₀γ
  have hNth :
      (e : ℚ) / ((p : ℚ) - 1) < (N : ℚ) :=
    lt_of_lt_of_le hN₁ (by exact_mod_cast Nat.le_max_right N₀ N₁)
  have hsubContinuous :
      Continuous
        (fun u : (LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup (completeDVFOfWithZeroValuation v)) 1 =>
          principalUnitSubOneOfWithZeroValuation v u) := by
    unfold principalUnitSubOneOfWithZeroValuation
    fun_prop
  have hball :
      {x : K | v x < WithZero.exp (-(N : ℤ))} ∈ 𝓝 (0 : K) := by
    let g : (WithZero (Multiplicative ℤ))ˣ :=
      Valuation.IsRankOneDiscrete.generator v
    have hg : (g : WithZero (Multiplicative ℤ)) < 1 := by
      exact Valuation.IsRankOneDiscrete.generator_lt_one v
    let a : ℤ := WithZero.log (g : WithZero (Multiplicative ℤ))
    have ha : a ≤ -1 := by
      have ha0 : a < 0 := by
        have hlog := (WithZero.log_lt_log (Units.ne_zero g)
          (one_ne_zero : (1 : WithZero (Multiplicative ℤ)) ≠ 0)).2 hg
        simpa [a] using hlog
      omega
    let m := N + 1
    have hm :
        (g : WithZero (Multiplicative ℤ)) ^ m <
          WithZero.exp (-(N : ℤ)) := by
      rw [show m = N + 1 by rfl, ← WithZero.exp_log (Units.ne_zero g),
        ← WithZero.exp_nsmul, WithZero.exp_lt_exp]
      change ((N + 1 : ℕ) : ℤ) * a < -(N : ℤ)
      calc
        ((N + 1 : ℕ) : ℤ) * a ≤ ((N + 1 : ℕ) : ℤ) * (-1) :=
          mul_le_mul_of_nonneg_left ha (by omega)
        _ < -(N : ℤ) := by omega
    rcases Valuation.IsRankOneDiscrete.generator_mem_range K v with ⟨z, hz⟩
    have hz0 : z ≠ 0 := (Valuation.ne_zero_iff v).mp (by
      rw [hz]
      exact Units.ne_zero g)
    have hzm0 : z ^ m ≠ 0 := pow_ne_zero m hz0
    rw [Valued.mem_nhds_zero]
    refine ⟨Units.mk0 (v.restrict (z ^ m))
      ((Valuation.ne_zero_iff v.restrict).2 hzm0), ?_⟩
    intro x hx
    change v.restrict x < v.restrict (z ^ m) at hx
    have hx' : v x < v (z ^ m) := v.restrict_lt_iff.mp hx
    exact hx'.trans (by simpa [v.map_pow, hz] using hm)
  have hpre :
      {u : (LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup (completeDVFOfWithZeroValuation v)) 1 |
        v (principalUnitSubOneOfWithZeroValuation v u) <
          WithZero.exp (-(N : ℤ))} ∈ 𝓝 1 := by
    have hballOne :
        {x : K | v x < WithZero.exp (-(N : ℤ))} ∈
          𝓝 (principalUnitSubOneOfWithZeroValuation v
            (1 : (LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup (completeDVFOfWithZeroValuation v)) 1)) := by
      simpa using hball
    have ht := (hsubContinuous.tendsto
      (1 : (LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup (completeDVFOfWithZeroValuation v)) 1)) hballOne
    exact ht
  refine Filter.mem_of_superset hpre ?_
  intro u hu
  change
    v.restrict (principalUnitLogSeriesOfWithZeroValuation v u hnK) < γ.1
  rw [Valuation.restrict_lt_iff_lt_embedding]
  let x := principalUnitSubOneOfWithZeroValuation v u
  by_cases hx : x = 0
  · have hlog : principalUnitLogSeriesOfWithZeroValuation v u hnK = 0 := by
      simp [principalUnitLogSeriesOfWithZeroValuation, x, hx]
    rw [hlog, v.map_zero]
    exact zero_lt_iff.mpr
      (MonoidWithZeroHom.ValueGroup₀.embedding_unit_ne_zero γ)
  · have hxv_ne : v x ≠ 0 := (_root_.Valuation.ne_zero_iff v).2 hx
    have hloglt : WithZero.log (v x) < -(N : ℤ) := by
      exact
        (WithZero.log_lt_log hxv_ne
          (WithZero.exp_ne_zero (a := -(N : ℤ)))).2 (by simpa [x] using hu)
    have hvalN :
        (N : ℤ) < (ofWithZeroValuation v).val (Units.mk0 x hx) := by
      change (N : ℤ) < -WithZero.log (v x)
      linarith
    have hthreshold :
        (e : ℚ) / ((p : ℚ) - 1) <
          ((ofWithZeroValuation v).val (Units.mk0 x hx) : ℚ) :=
      lt_of_lt_of_le hNth (by exact_mod_cast hvalN.le)
    have hvx : v x < (1 : WithZero (Multiplicative ℤ)) :=
      principalUnitSubOne_val_lt_one_ofWithZeroValuation v u
    have hval :=
      valuation_logOnePlusSeriesField_eq_self_of_scaled_inv_sub_one_lt
        (v := v) (p := p) e (x := x) hx hnK hnval hvx hthreshold hcomplete
    rw [principalUnitLogSeriesOfWithZeroValuation, hval]
    exact lt_trans (by simpa [x] using hu) (by simpa [γ'] using hNγ)

end MultiplicativeIntegerValuation
end LocalFieldTheory.DiscreteValuationField
end
end

section
-- module Solutions.OAIQ244_DUKE.LocalField_Analytic_LogExpContinuity
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_isCompleteDiscrete _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.DiscreteNthRootsSubgroup.instTopologicalSpaceSubtypeUnitsMemSubgroup _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalClassFieldTheory.localSeparableValuationHasExtension _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.AdicPrincipalUnits.instAddCommGroup _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.AdicPrincipalUnits.instTopologicalSpace _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.DiscretePrincipalUnitQuotient.instAddCommGroup _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitInverseLimitCarrierPadicModule _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitQuotientCarrierPadicModule _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.PrincipalUnitProdiscreteLimit.instAddCommGroup _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.PrincipalUnitProdiscreteLimit.instTopologicalSpace _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitPadicModule _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitPadicSMul _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.residueFieldZModAlgebra _root_.LocalFieldTheory.DiscreteValuationField.Examples.Qp.padicDVRValuation_isCompleteDiscrete _root_.LocalFieldTheory.DiscreteValuationField.Examples.Qp.padicDVRValuation_isRankOneDiscrete _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedIntegralAlgebraContextValuationSubringAlgebra _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedQPadicContextValuationExtension _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedWithZeroValuationContextIntegralAlgebra _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.LubinTate.compatibleGroupFamiliesGroup _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.RamificationTheory.HilbertRamification.Higher.lowerRamificationGroup.instNormal _root_.RamificationTheory.HilbertRamification.ValuationSubring.selectedResidueField.instAlgebra _root_.RayClass.approximationCompletionTopologicalSpace _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.LocalClassFieldTheory.normalizationIntegerRingIsIntegralClosure _root_.RamificationTheory.HilbertRamification.CompleteDVF.decompositionGroupMulSemiringAction _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.chosenFinitePlaceCompletionAlgebra _root_.finiteLocalUnitsOpen _root_.relativeAdeleRingIntermediateAlgebra _root_.relativeAdeleRingTopIntermediateAlgebra
attribute [-simp] _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.IsDiscreteValuationRing.addVal_ringEquiv _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.EqualCharacteristicLaurent.coeffHom_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.EqualCharacteristicLaurent.powerSeriesEvalHom_C _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.EqualCharacteristicLaurent.powerSeriesEvalHom_X _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.EqualCharacteristicLaurent.powerSeriesEvalSubringHom_C _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.EqualCharacteristicLaurent.powerSeriesEvalSubringHom_X _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.AdicPrincipalUnits.addEquiv_map_smul _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.AdicPrincipalUnits.of_val _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.AdicPrincipalUnits.val_of _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.DiscretePrincipalUnitQuotient.addEquiv_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.DiscretePrincipalUnitQuotient.addEquiv_map_smul _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.DiscretePrincipalUnitQuotient.addEquiv_of _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.DiscretePrincipalUnitQuotient.addEquiv_symm_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.DiscretePrincipalUnitQuotient.of_val _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.DiscretePrincipalUnitQuotient.val_of _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.DiscretePrincipalUnitQuotient.val_transition _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.adicPrincipalUnitsHomeomorphUnderlying_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.iwasawaGlobalInverseLimitCarrier_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitAddEquivInverseLimitCarrier_map_smul _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitAddHomeomorphInverseLimitCarrier_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitInverseLimitCarrierEval_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitInverseLimitCarrierPadic_smul_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitMulEquivInverseLimitCarrier_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitPadic_smul_carrier_coordinate _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitProdiscreteLimitHomeomorphUnderlying_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitQuotientCarrierPadicScalar_eq_smul _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitQuotientCarrierToFull_mk _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitQuotientCarrierTransition_mk _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.uniformizerHigherUnitQuotientEquiv_mk _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.PrincipalUnitProdiscreteLimit.addEquiv_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.PrincipalUnitProdiscreteLimit.addEquiv_map_smul _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.PrincipalUnitProdiscreteLimit.addEquiv_symm_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.PrincipalUnitProdiscreteLimit.coordinate_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.PrincipalUnitProdiscreteLimit.of_val _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.PrincipalUnitProdiscreteLimit.val_of _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.adicPrincipalUnitsContinuousAddEquivUnderlyingOfWithZeroValuation_map_smul _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.adicPrincipalUnitsHomeomorphProdiscreteLimit_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.adicPrincipalUnitsHomeomorphProdiscreteLimit_to_addEquiv _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.iwasawaDegreeTerm_zero _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.iwasawaGn_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.iwasawaPartialProduct_zero_input _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.iwasawaSeedAtLevel_val _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.iwasawaSeedIdeal_val _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.iwasawaSeed_val _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitPadic_natCast_smul _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitPadic_nsmul_eq_pow _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitPadic_smul_def _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitSuccQuotAddEquivResidue_iwasawaSeed _root_.LocalFieldTheory.DiscreteValuationField.LocalField.higherPrincipalUnitAddToFirst_smul _root_.LocalFieldTheory.DiscreteValuationField.LocalField.laurentSeriesEquivLaurentImageSubfield_apply_coe _root_.LocalFieldTheory.DiscreteValuationField.LocalField.padicIntToValuationSubring_coe _root_.LocalFieldTheory.IsNonarchimedeanLocalField.multiplicativeIntegerValuation_val _root_.LocalFieldTheory.Padic.integerRingEquivPadicDVRValuationSubring_coe _root_.LocalFieldTheory.localIntegerValuationSubringEquiv_apply_coe _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.LocalFieldTheory.residueField_algebraMap_residue _root_.LubinTate.LubinTateSeries.standardLubinTateSeries_toPowerSeries _root_.LubinTate.SameUniformizer.coeff_recursiveIntertwiner _root_.LubinTate.SameUniformizer.constantCoeff_inVariable _root_.LubinTate.SameUniformizer.intertwinerApproximation_zero _root_.LubinTate.SameUniformizer.standardLubinTateEndomorphism_coeff_one _root_.LubinTate.standardLubinTateBaseUniformizerUnit_coe _root_.LubinTate.standardLubinTateChangedUniformizerUnit_coe _root_.LubinTate.standardLubinTateLevelGenerator_coe _root_.LubinTate.standardLubinTatePolynomialIterateOverSeparableClosure_eval _root_.LubinTate.standardLubinTatePolynomialIterate_derivative_eval_zero _root_.LubinTate.standardLubinTatePolynomialIterate_eval_zero _root_.LubinTate.standardLubinTatePolynomialIterate_zero _root_.LubinTate.standardLubinTatePolynomial_derivative_eval_zero _root_.LubinTate.standardLubinTatePolynomial_eval _root_.LubinTate.standardLubinTatePolynomial_toPowerSeries _root_.LubinTate.standardLubinTatePolynomial_toPowerSeries_eq_series _root_.LubinTate.standardLubinTatePrimitivePointInteger_coe _root_.LubinTate.standardLubinTatePrimitivePolynomialOverField_coeff_zero _root_.LubinTate.standardLubinTatePrimitivePolynomial_coeff_zero _root_.LubinTate.standardLubinTateUnitFactorFieldUnit_coe _root_.OAI.PrimeDegreePackets.ThetaConstruction.schwartzCM_apply _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteResidueActionOfHenselianDVF_apply _root_.RamificationTheory.HilbertRamification.Higher.dvfValuationSubringUnitAut_apply _root_.RamificationTheory.HilbertRamification.Higher.lowerRamificationGroup_neg_one _root_.RamificationTheory.HilbertRamification.Higher.mem_dvfHigherPrincipalUnitGroup_iff _root_.RamificationTheory.HilbertRamification.Higher.mem_lowerRamificationGroup_iff _root_.RamificationTheory.HilbertRamification.Higher.mem_valuationSubringDisplacementSubalgebraOfUniqueExtension_iff _root_.RamificationTheory.HilbertRamification.Higher.realRamificationIdeal_nat _root_.RamificationTheory.HilbertRamification.Higher.realRamificationIdeal_neg_one _root_.RamificationTheory.HilbertRamification.Higher.valuationSubringAutOfUniqueExtension_apply_coe _root_.RamificationTheory.HilbertRamification.Higher.valuationSubringAutOfUniqueExtension_apply_inv_apply _root_.RamificationTheory.HilbertRamification.Higher.valuationSubringAutOfUniqueExtension_mul_apply _root_.RamificationTheory.HilbertRamification.Higher.valuationSubringAutOfUniqueExtension_one_apply _root_.infinitePlace_mult_smul
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

/-- The exponential endpoint `m^n → U^n` of the deep exponential–logarithm equivalence is continuous.
The unit topology records both a unit and its inverse; the inverse component is
the same continuous exponential evaluated at `-a`. -/
theorem continuous_principalUnitExpSeriesHomOfMaximalIdealPowOfWithZeroValuationScaled
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
      (principalUnitExpSeriesHomOfMaximalIdealPowOfWithZeroValuationScaled
        (v := v) (p := p) e n (π := π) hπval hn hlevel
        hnK hnval hcomplete) := by
  let : Valued K (WithZero (Multiplicative ℤ)) := Valued.mk' v
  let F : ValuationTheory.DiscreteValuationField.CompleteDVF.{u, 0} K := completeDVFOfWithZeroValuation v
  let I : Type u := (F.maximalIdeal ^ n : Ideal F.valuationSubring)
  let H : Multiplicative I →* LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup F n :=
    principalUnitExpSeriesHomOfMaximalIdealPowOfWithZeroValuationScaled
      (v := v) (p := p) e n (π := π) hπval hn hlevel
      hnK hnval hcomplete
  have hFieldAdd : Continuous
      (fun a : I => ((((H (Multiplicative.ofAdd a) :
        LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup F n) : F.valuationSubringˣ) :
        F.valuationSubring) : K)) := by
    simpa [F, I, H] using
      continuous_principalUnitExpSeries_maximalIdealPow_fieldVal_ofWithZeroValuationScaled
        (v := v) (p := p) e n (π := π) hπval hn hlevel
        hnK hnval hcomplete
  have hField : Continuous
      (fun a : Multiplicative I => ((((H a : LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup F n) :
        F.valuationSubringˣ) : F.valuationSubring) : K)) := by
    convert hFieldAdd.comp continuous_toAdd using 1
    all_goals try with_reducible_and_instances rfl
    rfl
  have hVal : Continuous
      (fun a : Multiplicative I =>
        (((H a : LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup F n) : F.valuationSubringˣ) :
          F.valuationSubring)) := by
    apply Continuous.subtype_mk
    exact hField
  have hNegI : Continuous (fun a : I => -a) := by
    apply Continuous.subtype_mk
    apply Continuous.subtype_mk
    exact (continuous_subtype_val.comp continuous_subtype_val).neg
  have hNeg : Continuous (fun a : Multiplicative I => -(a.toAdd)) :=
    hNegI.comp continuous_toAdd
  let Hinv : Multiplicative I → F.valuationSubringˣ :=
    fun a => ((H a : F.valuationSubringˣ)⁻¹)
  have hFieldInv : Continuous
      (fun a : Multiplicative I => ((Hinv a : F.valuationSubring) : K)) := by
    have hnegexp := hFieldAdd.comp hNeg
    convert hnegexp using 1
    all_goals try with_reducible_and_instances rfl
    funext a
    simp [Hinv]
  have hInvVal : Continuous
      (fun a : Multiplicative I => (Hinv a : F.valuationSubring)) := by
    apply Continuous.subtype_mk
    exact hFieldInv
  have hUnits : Continuous
      (fun a : Multiplicative I =>
        ((H a : LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup F n) : F.valuationSubringˣ)) := by
    rw [Units.continuous_iff]
    exact ⟨hVal, by simpa [Hinv] using hInvVal⟩
  change Continuous H
  apply Continuous.subtype_mk
  exact hUnits

/-- The logarithm endpoint `U^n → m^n` of the deep exponential–logarithm equivalence is continuous.
It is the restriction of the continuous logarithm on `U^1`; the two subtype
lifts merely record the already-proved fact that its value lies in `m^n`. -/
theorem continuous_principalUnitLogSeriesOfHigherPrincipalUnitGroupOfWithZeroValuationScaled
    [Algebra ℚ K]
    (v : _root_.Valuation K (WithZero (Multiplicative ℤ)))
    [ValuationTheory.DiscreteValuationField.Valuation.IsCompleteDiscrete v]
    {p : ℕ} [Fact p.Prime] (e n : ℕ)
    {π : (completeDVFOfWithZeroValuation v).valuationSubring}
    (hπval : v (π : K) = WithZero.exp (-1 : ℤ))
    (hn : 1 ≤ n)
    (hlevel : (e : ℚ) / ((p : ℚ) - 1) < (n : ℚ))
    (hnK : ∀ m : ℕ, (((m + 1 : ℕ) : K) ≠ 0))
    (hnval : ∀ m : ℕ,
      v (((m + 1 : ℕ) : K)) =
        WithZero.exp (-((e : ℤ) * (padicValNat p (m + 1) : ℤ))))
    (hcomplete :
      letI : Valued K (WithZero (Multiplicative ℤ)) := Valued.mk' v
      CompleteSpace K) :
    letI : Valued K (WithZero (Multiplicative ℤ)) := Valued.mk' v
    Continuous
      (principalUnitLogSeriesOfHigherPrincipalUnitGroupOfWithZeroValuationScaled
        (v := v) (p := p) e n (π := π)
        (isUniformizer_of_valuation_eq_exp_neg_one v (π : K) hπval)
        hπval hn hlevel
        hnK hnval hcomplete) := by
  let : Valued K (WithZero (Multiplicative ℤ)) := Valued.mk' v
  let hπ : v.IsUniformizer (π : K) :=
    isUniformizer_of_valuation_eq_exp_neg_one v (π : K) hπval
  let F : ValuationTheory.DiscreteValuationField.CompleteDVF.{u, 0} K := completeDVFOfWithZeroValuation v
  let ι : LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup F n → LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup F 1 :=
    fun u => ⟨(u : F.valuationSubringˣ),
      LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.antitone F hn u.property⟩
  have hι : Continuous ι := by
    apply Continuous.subtype_mk
    exact continuous_subtype_val
  let L : LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup F 1 →* Multiplicative K :=
    principalUnitLogSeriesHomOfWithZeroValuationScaled
      (v := v) (p := p) e hnK hnval hcomplete
  have hL : Continuous L := by
    simpa [F, L] using
      continuous_principalUnitLogSeriesHomOfWithZeroValuationScaled
        (v := v) (p := p) e hnK hnval hcomplete
  have hfield : Continuous
      (fun u : LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup F n => (L (ι u)).toAdd) :=
    continuous_toAdd.comp (hL.comp hι)
  have hfieldEndpoint : Continuous
      (fun u : LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup F n =>
        (((principalUnitLogSeriesOfHigherPrincipalUnitGroupOfWithZeroValuationScaled
          (v := v) (p := p) e n (π := π) hπ hπval hn hlevel
          hnK hnval hcomplete u :
            (F.maximalIdeal ^ n : Ideal F.valuationSubring)) :
          F.valuationSubring) : K)) := by
    convert hfield using 1
    all_goals try with_reducible_and_instances rfl
    funext u
    change principalUnitLogSeriesOfWithZeroValuation v (ι u) hnK =
      Multiplicative.toAdd (L (ι u))
    exact
      (principalUnitLogSeriesHomOfWithZeroValuationScaled_apply_toAdd
        (v := v) (p := p) e hnK hnval hcomplete (ι u)).symm
  have hValEndpoint : Continuous
      (fun u : LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup F n =>
        ((principalUnitLogSeriesOfHigherPrincipalUnitGroupOfWithZeroValuationScaled
          (v := v) (p := p) e n (π := π) hπ hπval hn hlevel
          hnK hnval hcomplete u :
            (F.maximalIdeal ^ n : Ideal F.valuationSubring)) :
          F.valuationSubring)) := by
    apply Continuous.subtype_mk
    exact hfieldEndpoint
  apply Continuous.subtype_mk
  exact hValEndpoint

/-- The deep exponential–logarithm equivalence as a topological group isomorphism, once the two exact
series-composition identities have been supplied.  Continuity of both maps is
not an assumption: it is furnished by the endpoint theorems above. -/
noncomputable def principalUnitExpLogContinuousMulEquivOfExact_ofWithZeroValuationScaled
    [Algebra ℚ K]
    (v : _root_.Valuation K (WithZero (Multiplicative ℤ)))
    [ValuationTheory.DiscreteValuationField.Valuation.IsCompleteDiscrete v]
    {p : ℕ} [Fact p.Prime] (e n : ℕ)
    {π : (completeDVFOfWithZeroValuation v).valuationSubring}
    (hπval : v (π : K) = WithZero.exp (-1 : ℤ))
    (hn : 1 ≤ n)
    (hlevel : (e : ℚ) / ((p : ℚ) - 1) < (n : ℚ))
    (hnKexp : ∀ m : ℕ, (((m.factorial : ℕ) : K) ≠ 0))
    (hnvalExp : ∀ m : ℕ,
      v (((m.factorial : ℕ) : K)) =
        WithZero.exp (-((e : ℤ) * (padicValNat p m.factorial : ℤ))))
    (hnKlog : ∀ m : ℕ, (((m + 1 : ℕ) : K) ≠ 0))
    (hnvalLog : ∀ m : ℕ,
      v (((m + 1 : ℕ) : K)) =
        WithZero.exp (-((e : ℤ) * (padicValNat p (m + 1) : ℤ))))
    (hcomplete :
      letI : Valued K (WithZero (Multiplicative ℤ)) := Valued.mk' v
      CompleteSpace K)
    (hlog_exp :
      ∀ a :
        ((completeDVFOfWithZeroValuation v).maximalIdeal ^ n :
          Ideal (completeDVFOfWithZeroValuation v).valuationSubring),
        principalUnitLogSeriesOfHigherPrincipalUnitGroupOfWithZeroValuationScaled
          (v := v) (p := p) e n (π := π)
          (isUniformizer_of_valuation_eq_exp_neg_one v (π : K) hπval)
          hπval hn hlevel
          hnKlog hnvalLog hcomplete
          (principalUnitExpSeriesOfMaximalIdealPowOfWithZeroValuationScaled
            (v := v) (p := p) e n (π := π)
            (isUniformizer_of_valuation_eq_exp_neg_one v (π : K) hπval)
            hπval hn hlevel
            hnKexp hnvalExp hcomplete a) = a)
    (hexp_log :
      ∀ u : LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup (completeDVFOfWithZeroValuation v) n,
        principalUnitExpSeriesOfMaximalIdealPowOfWithZeroValuationScaled
          (v := v) (p := p) e n (π := π)
          (isUniformizer_of_valuation_eq_exp_neg_one v (π : K) hπval)
          hπval hn hlevel
          hnKexp hnvalExp hcomplete
          (principalUnitLogSeriesOfHigherPrincipalUnitGroupOfWithZeroValuationScaled
            (v := v) (p := p) e n (π := π)
            (isUniformizer_of_valuation_eq_exp_neg_one v (π : K) hπval)
            hπval hn hlevel
            hnKlog hnvalLog hcomplete u) = u) :
    letI : Valued K (WithZero (Multiplicative ℤ)) := Valued.mk' v
    Multiplicative
      ((completeDVFOfWithZeroValuation v).maximalIdeal ^ n :
        Ideal (completeDVFOfWithZeroValuation v).valuationSubring) ≃ₜ*
      LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup (completeDVFOfWithZeroValuation v) n := by
  letI : Valued K (WithZero (Multiplicative ℤ)) := Valued.mk' v
  let hπ : v.IsUniformizer (π : K) :=
    isUniformizer_of_valuation_eq_exp_neg_one v (π : K) hπval
  exact
    { __ :=
        principalUnitExpLogMulEquivOfExact_ofWithZeroValuationScaled
          (v := v) (p := p) e n (π := π) hπ hπval hn hlevel
          hnKexp hnvalExp hnKlog hnvalLog hcomplete hlog_exp hexp_log
      continuous_toFun :=
        continuous_principalUnitExpSeriesHomOfMaximalIdealPowOfWithZeroValuationScaled
          (v := v) (p := p) e n (π := π) hπval hn hlevel
          hnKexp hnvalExp hcomplete
      continuous_invFun :=
        continuous_ofAdd.comp
          (continuous_principalUnitLogSeriesOfHigherPrincipalUnitGroupOfWithZeroValuationScaled
            (v := v) (p := p) e n (π := π) hπval hn hlevel
            hnKlog hnvalLog hcomplete) }

end MultiplicativeIntegerValuation
end LocalFieldTheory.DiscreteValuationField
end
end

section
-- module Solutions.OAIQ244_DUKE.LocalField_Analytic_PrincipalUnitExpLogEquiv
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_isCompleteDiscrete _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.DiscreteNthRootsSubgroup.instTopologicalSpaceSubtypeUnitsMemSubgroup _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalClassFieldTheory.localSeparableValuationHasExtension _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.AdicPrincipalUnits.instAddCommGroup _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.AdicPrincipalUnits.instTopologicalSpace _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.DiscretePrincipalUnitQuotient.instAddCommGroup _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitInverseLimitCarrierPadicModule _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitInverseLimitCarrierPadicSMul _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitQuotientCarrierPadicModule _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitQuotientCarrier_finite _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.PrincipalUnitProdiscreteLimit.instAddCommGroup _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.PrincipalUnitProdiscreteLimit.instTopologicalSpace _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.adicPrincipalUnitsContinuousAdd _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.adicPrincipalUnitsContinuousSMul _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.adicPrincipalUnitsPadicModule _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.discretePrincipalUnitQuotientFinite _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.discretePrincipalUnitQuotientPadicModule _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitPadicModule _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitPadicSMul _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitProdiscreteLimitContinuousAdd _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitProdiscreteLimitContinuousSMul _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitProdiscreteLimitPadicModule _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.residueFieldZModAlgebra _root_.LocalFieldTheory.DiscreteValuationField.Examples.Qp.padicDVRValuation_isCompleteDiscrete _root_.LocalFieldTheory.DiscreteValuationField.Examples.Qp.padicDVRValuation_isRankOneDiscrete _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedIntegralAlgebraContextQPadic _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedIntegralAlgebraContextValuationSubringAlgebra _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedIntegralLatticeContextAlgebra _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedQPadicContextAlgebra _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedQPadicContextFact _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedQPadicContextFiniteDimensional _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedQPadicContextValuationExtension _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedWithZeroValuationContextIntegralAlgebra _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.LubinTate.Valuations.exponentialValuationSubringIsLocalRing _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.RamificationTheory.HilbertRamification.Higher.lowerRamificationGroup.instNormal _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionFixedSubring.instIsLocalRing _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionResidueField.instField _root_.RamificationTheory.HilbertRamification.ValuationSubring.selectedResidueField.instAlgebra _root_.RayClass.approximationCompletionTopologicalSpace _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.LocalClassFieldTheory.normalizationIntegerRingIsIntegralClosure _root_.RamificationTheory.HilbertRamification.CompleteDVF.decompositionGroupMulSemiringAction _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.chosenFinitePlaceCompletionAlgebra _root_.finiteLocalUnitsOpen _root_.relativeAdeleRingIntermediateAlgebra _root_.relativeAdeleRingTopIntermediateAlgebra
attribute [-simp] _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.IsDiscreteValuationRing.addVal_ringEquiv _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.EqualCharacteristicLaurent.coeffHom_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.EqualCharacteristicLaurent.powerSeriesEvalHom_C _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.EqualCharacteristicLaurent.powerSeriesEvalHom_X _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.EqualCharacteristicLaurent.powerSeriesEvalSubringHom_C _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.EqualCharacteristicLaurent.powerSeriesEvalSubringHom_X _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.AdicPrincipalUnits.addEquiv_map_smul _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.AdicPrincipalUnits.of_val _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.AdicPrincipalUnits.val_of _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.DiscretePrincipalUnitQuotient.addEquiv_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.DiscretePrincipalUnitQuotient.addEquiv_map_smul _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.DiscretePrincipalUnitQuotient.addEquiv_of _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.DiscretePrincipalUnitQuotient.addEquiv_symm_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.DiscretePrincipalUnitQuotient.of_val _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.DiscretePrincipalUnitQuotient.val_of _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.DiscretePrincipalUnitQuotient.val_transition _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.adicPrincipalUnitsHomeomorphUnderlying_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.iwasawaGlobalInverseLimitCarrier_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitAddEquivInverseLimitCarrier_map_smul _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitAddHomeomorphInverseLimitCarrier_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitInverseLimitCarrierEval_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitInverseLimitCarrierPadic_smul_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitMulEquivInverseLimitCarrier_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitPadic_smul_carrier_coordinate _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitProdiscreteLimitHomeomorphUnderlying_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitQuotientCarrierPadicScalar_eq_smul _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitQuotientCarrierToFull_mk _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitQuotientCarrierTransition_mk _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.uniformizerHigherUnitQuotientEquiv_mk _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.PrincipalUnitProdiscreteLimit.addEquiv_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.PrincipalUnitProdiscreteLimit.addEquiv_map_smul _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.PrincipalUnitProdiscreteLimit.addEquiv_symm_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.PrincipalUnitProdiscreteLimit.coordinate_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.PrincipalUnitProdiscreteLimit.coordinate_smul _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.PrincipalUnitProdiscreteLimit.of_val _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.PrincipalUnitProdiscreteLimit.val_of _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.adicPrincipalUnitsAddEquivProdiscreteLimit_map_smul _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.adicPrincipalUnitsContinuousAddEquivUnderlyingOfWithZeroValuation_map_smul _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.adicPrincipalUnitsHomeomorphProdiscreteLimit_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.adicPrincipalUnitsHomeomorphProdiscreteLimit_to_addEquiv _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.iwasawaDegreeTerm_zero _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.iwasawaGn_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.iwasawaPartialProduct_zero_input _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.iwasawaSeedAtLevel_val _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.iwasawaSeedIdeal_val _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.iwasawaSeed_val _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitPadic_natCast_smul _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitPadic_nsmul_eq_pow _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitPadic_smul_def _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitSuccQuotAddEquivResidue_iwasawaSeed _root_.LocalFieldTheory.DiscreteValuationField.LocalField.higherPrincipalUnitAddToFirst_smul _root_.LocalFieldTheory.DiscreteValuationField.LocalField.laurentSeriesEquivLaurentImageSubfield_apply_coe _root_.LocalFieldTheory.DiscreteValuationField.LocalField.padicIntToValuationSubring_coe _root_.LocalFieldTheory.DiscreteValuationField.LocalField.ratCastToQpadicClosureSubfield_apply _root_.LocalFieldTheory.DiscreteValuationField.LocalField.ratCastWithValToQpadicClosureSubfield_apply _root_.LocalFieldTheory.IsNonarchimedeanLocalField.multiplicativeIntegerValuation_val _root_.LocalFieldTheory.Padic.integerRingEquivPadicDVRValuationSubring_coe _root_.LocalFieldTheory.localIntegerValuationSubringEquiv_apply_coe _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.LocalFieldTheory.residueField_algebraMap_residue _root_.LubinTate.LubinTateSeries.standardLubinTateSeries_toPowerSeries _root_.LubinTate.SameUniformizer.coeff_recursiveIntertwiner _root_.LubinTate.SameUniformizer.constantCoeff_inVariable _root_.LubinTate.SameUniformizer.intertwinerApproximation_zero _root_.LubinTate.SameUniformizer.standardLubinTateEndomorphism_coeff_one _root_.LubinTate.standardLubinTateBaseUniformizerUnit_coe _root_.LubinTate.standardLubinTateChangedUniformizerUnit_coe _root_.LubinTate.standardLubinTateLevelGenerator_coe _root_.LubinTate.standardLubinTatePolynomialIterateOverSeparableClosure_eval _root_.LubinTate.standardLubinTatePolynomialIterate_derivative_eval_zero _root_.LubinTate.standardLubinTatePolynomialIterate_eval_zero _root_.LubinTate.standardLubinTatePolynomialIterate_zero _root_.LubinTate.standardLubinTatePolynomial_derivative_eval_zero _root_.LubinTate.standardLubinTatePolynomial_eval _root_.LubinTate.standardLubinTatePolynomial_toPowerSeries _root_.LubinTate.standardLubinTatePolynomial_toPowerSeries_eq_series _root_.LubinTate.standardLubinTatePrimitivePointInteger_coe _root_.LubinTate.standardLubinTatePrimitivePolynomialOverField_coeff_zero _root_.LubinTate.standardLubinTatePrimitivePolynomial_coeff_zero _root_.LubinTate.standardLubinTateUnitFactorFieldUnit_coe _root_.OAI.PrimeDegreePackets.ThetaConstruction.schwartzCM_apply _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteResidueActionOfHenselianDVF_apply _root_.RamificationTheory.HilbertRamification.Higher.dvfValuationSubringUnitAut_apply _root_.RamificationTheory.HilbertRamification.Higher.lowerRamificationGroup_neg_one _root_.RamificationTheory.HilbertRamification.Higher.mem_dvfHigherPrincipalUnitGroup_iff _root_.RamificationTheory.HilbertRamification.Higher.mem_lowerRamificationGroup_iff _root_.RamificationTheory.HilbertRamification.Higher.mem_valuationSubringDisplacementSubalgebraOfUniqueExtension_iff _root_.RamificationTheory.HilbertRamification.Higher.realRamificationIdeal_nat _root_.RamificationTheory.HilbertRamification.Higher.realRamificationIdeal_neg_one _root_.RamificationTheory.HilbertRamification.Higher.valuationSubringAutOfUniqueExtension_apply_coe _root_.RamificationTheory.HilbertRamification.Higher.valuationSubringAutOfUniqueExtension_apply_inv_apply _root_.RamificationTheory.HilbertRamification.Higher.valuationSubringAutOfUniqueExtension_mul_apply _root_.RamificationTheory.HilbertRamification.Higher.valuationSubringAutOfUniqueExtension_one_apply _root_.infinitePlace_mult_smul
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

/-!
# Exponential and logarithm on deep principal units

This file combines the two evaluated formal composition identities with the
valuation-theoretic endpoint maps and their continuity.  No finite-quotient
or defect-membership hypothesis remains in the public result.
-/

noncomputable section

universe u

namespace LocalFieldTheory.DiscreteValuationField
namespace MultiplicativeIntegerValuation

variable {K : Type u} [Field K]

/-- The local-field structure theory, the deep exponential–logarithm equivalence.  If the normalized valuation has
ramification index `e`, then for every `n > e/(p-1)` the exponential and
logarithm series give mutually inverse topological group isomorphisms
`m^n ≃ U^n` (with the additive source written multiplicatively).
Surjectivity onto the standard value group `ℤᵐ⁰` is the formal normalization
condition; a normalized uniformizer is chosen internally. -/
noncomputable def chosenExpLogContinuousMulEquiv
    (v : _root_.Valuation K (WithZero (Multiplicative ℤ)))
    [ValuationTheory.DiscreteValuationField.Valuation.IsCompleteDiscrete v]
    [Finite (IsLocalRing.ResidueField v.valuationSubring)] [CharZero K]
    (hv : Function.Surjective v)
    (n : ℕ)
    (hlevel :
      (LocalField.ramificationIndexOfWithZeroValuation v : ℚ) /
          (((LocalField.ofWithZeroValuation v).residueCharacteristic : ℚ) - 1) <
        (n : ℚ)) :
    letI : Valued K (WithZero (Multiplicative ℤ)) := Valued.mk' v
    Multiplicative
      ((completeDVFOfWithZeroValuation v).maximalIdeal ^ n :
        Ideal (completeDVFOfWithZeroValuation v).valuationSubring) ≃ₜ*
      LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup (completeDVFOfWithZeroValuation v) n := by
  let F : ValuationTheory.DiscreteValuationField.CompleteDVF.{u, 0} K := completeDVFOfWithZeroValuation v
  let LF : LocalField.{u, 0} K := LocalField.ofWithZeroValuation v
  let hnormalized :=
    WithZeroValuation.exists_valuationSubring_valuation_eq_exp_neg_one_of_surjective
      v hv
  let π : (completeDVFOfWithZeroValuation v).valuationSubring :=
    Classical.choose hnormalized
  have hπval : v (π : K) = WithZero.exp (-1 : ℤ) :=
    Classical.choose_spec hnormalized
  let hπ : v.IsUniformizer (π : K) :=
    WithZeroValuation.isUniformizer_of_valuation_eq_exp_neg_one
      v (π : K) hπval
  let p : ℕ := LF.residueCharacteristic
  let e : ℕ := LocalField.ramificationIndexOfWithZeroValuation v
  haveI : Finite F.residueField := by
    change Finite (IsLocalRing.ResidueField v.valuationSubring)
    infer_instance
  letI : Fact p.Prime := by
    dsimp [p, LF]
    infer_instance
  have hlevel' : (e : ℚ) / ((p : ℚ) - 1) < (n : ℚ) := by
    simpa [e, p, LF] using hlevel
  have hpden : (0 : ℚ) < (p : ℚ) - 1 := by
    have hp : 1 < p := (Fact.out : Nat.Prime p).one_lt
    exact sub_pos.mpr (by exact_mod_cast hp)
  have hepos : (0 : ℚ) < (e : ℚ) := by
    exact_mod_cast LocalField.ramificationIndexOfWithZeroValuation_pos v
  have hnpos : 0 < n := by
    have hnq : (0 : ℚ) < (n : ℚ) :=
      lt_trans (div_pos hepos hpden) hlevel'
    exact_mod_cast hnq
  have hn : 1 ≤ n := hnpos
  let hnKexp : ∀ m : ℕ, (((m.factorial : ℕ) : K) ≠ 0) :=
    fun m => Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero m)
  let hnKlog : ∀ m : ℕ, (((m + 1 : ℕ) : K) ≠ 0) :=
    fun m => Nat.cast_ne_zero.mpr (Nat.succ_ne_zero m)
  let hnvalExp : ∀ m : ℕ,
      v (((m.factorial : ℕ) : K)) =
        WithZero.exp (-((e : ℤ) * (padicValNat p m.factorial : ℤ))) := by
    intro m
    simpa [e, p, LF] using
      LocalField.valuation_natCast_factorial_eq_exp_neg_ramificationIndex_mul_padicValNat
        v m
  let hnvalLog : ∀ m : ℕ,
      v (((m + 1 : ℕ) : K)) =
        WithZero.exp (-((e : ℤ) * (padicValNat p (m + 1) : ℤ))) := by
    intro m
    simpa [e, p, LF] using
      LocalField.valuation_natCast_succ_eq_exp_neg_ramificationIndex_mul_padicValNat
        v m
  have hcomplete :
      letI : Valued K (WithZero (Multiplicative ℤ)) := Valued.mk' v
      CompleteSpace K :=
    WithZeroValuationTopology.completeSpace_ofWithZeroValuation v
  have hlevelR : (e : ℝ) / ((p : ℝ) - 1) < (n : ℝ) := by
    exact_mod_cast hlevel'
  have hthreshold_of_mem :
      ∀ (a : F.valuationSubring), a ∈ F.maximalIdeal ^ n →
        ∀ hx : (a : K) ≠ 0,
          (e : ℝ) / ((p : ℝ) - 1) <
            ((ofWithZeroValuation v).val (Units.mk0 (a : K) hx) : ℝ) := by
    intro a ha hx
    have hge :
        (n : ℤ) ≤
          (ofWithZeroValuation v).val (Units.mk0 (a : K) hx) := by
      simpa [F] using
        ofWithZeroValuation_val_ge_of_mem_maximalIdeal_pow
          (v := v) (π := π) hπ hπval n a ha hx
    exact lt_of_lt_of_le hlevelR (by exact_mod_cast hge)
  have hlog_exp :
      ∀ a : (F.maximalIdeal ^ n : Ideal F.valuationSubring),
        principalUnitLogSeriesOfHigherPrincipalUnitGroupOfWithZeroValuationScaled
          (v := v) (p := p) e n (π := π) hπ hπval hn hlevel'
          hnKlog hnvalLog hcomplete
          (principalUnitExpSeriesOfMaximalIdealPowOfWithZeroValuationScaled
            (v := v) (p := p) e n (π := π) hπ hπval hn hlevel'
            hnKexp hnvalExp hcomplete a) = a := by
    intro a
    apply Subtype.ext
    apply Subtype.ext
    simpa [principalUnitLogSeriesOfHigherPrincipalUnitGroupOfWithZeroValuationScaled,
      principalUnitExpSeriesOfMaximalIdealPowOfWithZeroValuationScaled, F] using
      logOnePlusSeries_expSeries_sub_one_eq_self_ofWithZeroValuation_scaled_of_threshold
        (v := v) (p := p) e (((a : F.valuationSubring) : K))
        hnKexp hnvalExp hnKlog hnvalLog
        (hthreshold_of_mem (a : F.valuationSubring) a.property) hcomplete
  have hexp_log :
      ∀ u : LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup F n,
        principalUnitExpSeriesOfMaximalIdealPowOfWithZeroValuationScaled
          (v := v) (p := p) e n (π := π) hπ hπval hn hlevel'
          hnKexp hnvalExp hcomplete
          (principalUnitLogSeriesOfHigherPrincipalUnitGroupOfWithZeroValuationScaled
            (v := v) (p := p) e n (π := π) hπ hπval hn hlevel'
            hnKlog hnvalLog hcomplete u) = u := by
    intro u
    let a : F.valuationSubring :=
      ((u : F.valuationSubringˣ) : F.valuationSubring) - 1
    have ha : a ∈ F.maximalIdeal ^ n := by
      simpa [a] using
        (LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.mem_iff
          (F := F) n (u : F.valuationSubringˣ)).1 u.property
    have hexact :=
      expSeries_logOnePlusSeries_eq_one_add_ofWithZeroValuation_scaled_of_threshold
        (v := v) (p := p) e (a : K) hnKlog hnvalLog hnKexp hnvalExp
        (hthreshold_of_mem a ha) hcomplete
    apply Subtype.ext
    apply Units.ext
    apply Subtype.ext
    simpa [a,
      principalUnitLogSeriesOfHigherPrincipalUnitGroupOfWithZeroValuationScaled,
      principalUnitExpSeriesOfMaximalIdealPowOfWithZeroValuationScaled, F] using hexact
  exact
    principalUnitExpLogContinuousMulEquivOfExact_ofWithZeroValuationScaled
      (v := v) (p := p) e n (π := π) hπval hn hlevel'
      hnKexp hnvalExp hnKlog hnvalLog hcomplete hlog_exp hexp_log

end MultiplicativeIntegerValuation
end LocalFieldTheory.DiscreteValuationField
end
end

section
-- module Solutions.OAIQ244_DUKE.LocalField_DiscreteValuationField_MixedCharacteristicStructure_IntegralLattice
attribute [-instance] _root_.ClassFormation.DegreeData.FrobeniusFixedFieldTower.extensionNormal _root_.ClassFormation.DegreeData.GaloisSubextension.extensionSubgroup_normalInstance _root_.ClassFormation.FiniteAbstractField.toFiniteResidueAbstractField_extensionNormal _root_.ClassFormation.FiniteCyclicSubextension.instNormalSubtypeMemSubgroupFieldExtensionSubgroupField _root_.ClassFormation.FiniteGaloisSubextension.extensionSubgroup_normalInstance _root_.ClassFormation.FiniteGaloisSubextension.extensionSubgroup_over_intermediate_normalInstance _root_.ClassFormation.FiniteGaloisSubextension.intermediateField_normalInstance _root_.ClassFormation.FiniteIntermediateField.galoisRefinement_normal _root_.ClassFormation.FiniteUnramifiedCyclicExtension.instNormalSubtypeMemSubgroupFieldExtensionSubgroupField _root_.ClassFormation.conjugateExtension_normal _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.HilbertRamification.Dedekind.inertiaSubgroupOfDecomposition_normal _root_.KummerTheory.DiscreteNthRootsSubgroup.instCommGroupSubtypeUnitsMemSubgroup _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalClassFieldTheory.extensionSubgroupBase_normal _root_.LocalClassFieldTheory.finiteGaloisExtensionSubgroupOfEmbedding_normal _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.residueFieldZModAlgebra _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.RamificationTheory.HilbertRamification.Higher.lowerRamificationGroup.instNormal _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionResidueField.instField _root_.RamificationTheory.HilbertRamification.ValuationSubring.inertiaGroup_normal _root_.RamificationTheory.HilbertRamification.ValuationSubring.ramificationGroupInInertiaAut_normal _root_.RamificationTheory.HilbertRamification.ValuationSubring.selectedResidueField.instAlgebra _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.CyclicCohomology.binaryCoefficientFamilyCommGroup _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.LocalClassFieldTheory.normalizationIntegerRingIsIntegralClosure _root_.RamificationTheory.HilbertRamification.CompleteDVF.decompositionGroupMulSemiringAction _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.chosenFinitePlaceCompletionAlgebra _root_.chosenFinitePlaceLocalizedIntegerAlgebra _root_.chosenFinitePlaceLocalizedValuationHasExtension _root_.finiteLocalUnitsOpen _root_.relativeAdeleRingIntermediateAlgebra _root_.relativeAdeleRingTopIntermediateAlgebra
attribute [-simp] _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.IsDiscreteValuationRing.addVal_ringEquiv _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.EqualCharacteristicLaurent.coeffHom_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.EqualCharacteristicLaurent.powerSeriesEvalHom_C _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.EqualCharacteristicLaurent.powerSeriesEvalHom_X _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.EqualCharacteristicLaurent.powerSeriesEvalSubringHom_C _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.EqualCharacteristicLaurent.powerSeriesEvalSubringHom_X _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.iwasawaGlobalInverseLimitCarrier_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.iwasawaDegreeTerm_zero _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.iwasawaGn_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.iwasawaPartialProduct_zero_input _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.iwasawaSeedAtLevel_val _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.iwasawaSeedIdeal_val _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.iwasawaSeed_val _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitSuccQuotAddEquivResidue_iwasawaSeed _root_.LocalFieldTheory.DiscreteValuationField.LocalField.laurentSeriesEquivLaurentImageSubfield_apply_coe _root_.LocalFieldTheory.Padic.integerRingEquivPadicDVRValuationSubring_coe _root_.LocalFieldTheory.localIntegerValuationSubringEquiv_apply_coe _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.LocalFieldTheory.residueField_algebraMap_residue _root_.LubinTate.LubinTateSeries.standardLubinTateSeries_toPowerSeries _root_.LubinTate.SameUniformizer.coeff_recursiveIntertwiner _root_.LubinTate.SameUniformizer.constantCoeff_inVariable _root_.LubinTate.SameUniformizer.intertwinerApproximation_zero _root_.LubinTate.SameUniformizer.standardLubinTateEndomorphism_coeff_one _root_.LubinTate.standardLubinTateBaseUniformizerUnit_coe _root_.LubinTate.standardLubinTateChangedUniformizerUnit_coe _root_.LubinTate.standardLubinTateLevelGenerator_coe _root_.LubinTate.standardLubinTatePolynomialIterateOverSeparableClosure_eval _root_.LubinTate.standardLubinTatePolynomialIterate_derivative_eval_zero _root_.LubinTate.standardLubinTatePolynomialIterate_eval_zero _root_.LubinTate.standardLubinTatePolynomialIterate_zero _root_.LubinTate.standardLubinTatePolynomial_derivative_eval_zero _root_.LubinTate.standardLubinTatePolynomial_eval _root_.LubinTate.standardLubinTatePolynomial_toPowerSeries _root_.LubinTate.standardLubinTatePolynomial_toPowerSeries_eq_series _root_.LubinTate.standardLubinTatePrimitivePointInteger_coe _root_.LubinTate.standardLubinTatePrimitivePolynomialOverField_coeff_zero _root_.LubinTate.standardLubinTatePrimitivePolynomial_coeff_zero _root_.LubinTate.standardLubinTateUnitFactorFieldUnit_coe _root_.OAI.PrimeDegreePackets.ThetaConstruction.schwartzCM_apply _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteResidueActionOfHenselianDVF_apply _root_.RamificationTheory.HilbertRamification.Higher.dvfValuationSubringUnitAut_apply _root_.RamificationTheory.HilbertRamification.Higher.lowerRamificationGroup_neg_one _root_.RamificationTheory.HilbertRamification.Higher.mem_dvfHigherPrincipalUnitGroup_iff _root_.RamificationTheory.HilbertRamification.Higher.mem_lowerRamificationGroup_iff _root_.RamificationTheory.HilbertRamification.Higher.mem_valuationSubringDisplacementSubalgebraOfUniqueExtension_iff _root_.RamificationTheory.HilbertRamification.Higher.realRamificationIdeal_nat _root_.RamificationTheory.HilbertRamification.Higher.realRamificationIdeal_neg_one _root_.RamificationTheory.HilbertRamification.Higher.valuationSubringAutOfUniqueExtension_apply_coe _root_.RamificationTheory.HilbertRamification.Higher.valuationSubringAutOfUniqueExtension_apply_inv_apply _root_.RamificationTheory.HilbertRamification.Higher.valuationSubringAutOfUniqueExtension_mul_apply _root_.RamificationTheory.HilbertRamification.Higher.valuationSubringAutOfUniqueExtension_one_apply _root_.infinitePlace_mult_smul
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

/--
Equips the target with its canonical `IsScalarTower` structure, namely `IsScalarTower
(Examples.Qp.padicCompleteDVF F.residueCharacteristic).valuationSubring
F.toCompleteDVF.valuationSubring K`.
-/
instance mixedQPadicContextValuationSubringTower
    (F : LocalField.{u, v} K) [CharZero K] [MixedQPadicContext F] :
    IsScalarTower
      (Examples.Qp.padicCompleteDVF F.residueCharacteristic).valuationSubring
      F.toCompleteDVF.valuationSubring K :=
  IsScalarTower.of_algebraMap_eq (by intro a; rfl)

/-! ### the canonical `Z_p` integral basis -/

/-- The restricted algebra structures form the expected tower
`Z_p → O_K → K`. -/
theorem padicIntValuationSubring_isScalarTower
    (F : LocalField.{u, v} K) [CharZero K] :
    letI : Algebra ℤ_[F.residueCharacteristic]
        F.toCompleteDVF.valuationSubring :=
      F.padicIntValuationSubringAlgebra
    letI : Algebra ℤ_[F.residueCharacteristic] K :=
      F.padicIntFieldAlgebra
    IsScalarTower ℤ_[F.residueCharacteristic]
      F.toCompleteDVF.valuationSubring K := by
  let : Algebra ℤ_[F.residueCharacteristic]
      F.toCompleteDVF.valuationSubring :=
    F.padicIntValuationSubringAlgebra
  let : Algebra ℤ_[F.residueCharacteristic] K :=
    F.padicIntFieldAlgebra
  exact IsScalarTower.of_algebraMap_eq (by intro z; rfl)

/-- The finite free `Z_p` model of one maximal-ideal power.  The ambient
integral-lattice context is an explicit dependency, while the indexed bundle
owns the finite and free witnesses for the selected power. -/
class MixedMaximalIdealPowContext
    (F : LocalField.{u, v} K) [CharZero K] (n : ℕ)
    [MixedIntegralLatticeContext F] : Prop where
  /-- The `n`th maximal-ideal power is finitely generated over `Z_p`. -/
  moduleFinite : Module.Finite ℤ_[F.residueCharacteristic]
    ((F.toCompleteDVF.maximalIdeal ^ n :
      Ideal F.toCompleteDVF.valuationSubring))
  /-- The `n`th maximal-ideal power is free over `Z_p`. -/
  moduleFree : Module.Free ℤ_[F.residueCharacteristic]
    ((F.toCompleteDVF.maximalIdeal ^ n :
      Ideal F.toCompleteDVF.valuationSubring))

/--
Equips the target with its canonical `Module.Finite` structure, namely `Module.Finite
ℤ_[F.residueCharacteristic] ((F.toCompleteDVF.maximalIdeal ^ n : Ideal
F.toCompleteDVF.valuationSubring))`.
-/
noncomputable instance mixedMaximalIdealPowContextModuleFinite
    (F : LocalField.{u, v} K) [CharZero K] (n : ℕ)
    [MixedIntegralLatticeContext F]
    [ctx : MixedMaximalIdealPowContext F n] :
    Module.Finite ℤ_[F.residueCharacteristic]
      ((F.toCompleteDVF.maximalIdeal ^ n :
        Ideal F.toCompleteDVF.valuationSubring)) :=
  ctx.moduleFinite

/--
Equips the target with its canonical `Module.Free` structure, namely `Module.Free
ℤ_[F.residueCharacteristic] ((F.toCompleteDVF.maximalIdeal ^ n : Ideal
F.toCompleteDVF.valuationSubring))`.
-/
noncomputable instance mixedMaximalIdealPowContextModuleFree
    (F : LocalField.{u, v} K) [CharZero K] (n : ℕ)
    [MixedIntegralLatticeContext F]
    [ctx : MixedMaximalIdealPowContext F n] :
    Module.Free ℤ_[F.residueCharacteristic]
      ((F.toCompleteDVF.maximalIdeal ^ n :
        Ideal F.toCompleteDVF.valuationSubring)) :=
  ctx.moduleFree

/-! ### The canonical `Z_p` action on `U^r` -/

/-- Projection of `U^1` to the wrapped quotient `U^1/U^(n+1)`, as a
`Z_p`-linear map. -/
noncomputable def principalUnitQuotientProjectionLinear
    (F : LocalField.{u, v} K) (n : ℕ) :
    Additive (LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup (F.toCompleteDVF) 1) →ₗ[
        ℤ_[F.residueCharacteristic]]
      CompleteDVF.higherPrincipalUnitGroup.DiscretePrincipalUnitQuotient
        F.toCompleteDVF n :=
  (CompleteDVF.higherPrincipalUnitGroup.adicPrincipalUnitsCoordinateLinear
    F n).comp
    (CompleteDVF.higherPrincipalUnitGroup.AdicPrincipalUnits.linearEquivUnderlying
      F).symm.toLinearMap

/-- The canonically indexed image of `U^(n+1)` inside `U^1`. -/
noncomputable def principalUnitSuccPadicSubmodule
    (F : LocalField.{u, v} K) (n : ℕ) :
    Submodule ℤ_[F.residueCharacteristic]
      (Additive (LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup (F.toCompleteDVF) 1)) :=
  F.higherPrincipalUnitPadicSubmodule
    (Nat.succ_le_succ (Nat.zero_le n))

/-- The kernel of the finite projection is exactly the image of
`U^(n+1) \hookrightarrow U^1`. -/
theorem principalUnitQuotientProjectionLinear_ker
    (F : LocalField.{u, v} K) (n : ℕ) :
    LinearMap.ker (F.principalUnitQuotientProjectionLinear n) =
      F.principalUnitSuccPadicSubmodule n := by
  let hn : 1 ≤ n + 1 := Nat.succ_le_succ (Nat.zero_le n)
  change LinearMap.ker (F.principalUnitQuotientProjectionLinear n) =
    F.higherPrincipalUnitPadicSubmodule hn
  ext x
  rw [LinearMap.mem_ker]
  change (F.principalUnitQuotientProjectionLinear n) x = 0 ↔
    ((Additive.toMul x : LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup (F.toCompleteDVF) 1) :
      F.toCompleteDVF.valuationSubringˣ) ∈
        LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup (F.toCompleteDVF) (n + 1)
  constructor
  · intro hx
    have hxq :
        (QuotientGroup.mk (Additive.toMul x) :
          CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitQuotientCarrier
            F.toCompleteDVF n) = 1 := by
      have hx' := congrArg
        (CompleteDVF.higherPrincipalUnitGroup.DiscretePrincipalUnitQuotient.addEquiv
          F.toCompleteDVF n) hx
      have hxadd : Additive.ofMul
          (QuotientGroup.mk (Additive.toMul x) :
            CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitQuotientCarrier
              F.toCompleteDVF n) = 0 := by
        rw [map_zero] at hx'
        change Additive.ofMul
          (QuotientGroup.mk (Additive.toMul x) :
            CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitQuotientCarrier
              F.toCompleteDVF n) = 0 at hx'
        exact hx'
      have hxtomul := congrArg Additive.toMul hxadd
      simpa using hxtomul
    have hxmem : ((Additive.toMul x :
        LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup (F.toCompleteDVF) 1) :
          F.toCompleteDVF.valuationSubringˣ) ∈
        LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup (F.toCompleteDVF) (n + 1) := by
      exact (QuotientGroup.eq_one_iff
        (N := (CompleteDVF.higherPrincipalUnitGroup F.toCompleteDVF (n + 1)).subgroupOf
          (CompleteDVF.higherPrincipalUnitGroup F.toCompleteDVF 1))
        (Additive.toMul x)).mp hxq
    exact hxmem
  · intro hx
    apply (CompleteDVF.higherPrincipalUnitGroup.DiscretePrincipalUnitQuotient.addEquiv
      F.toCompleteDVF n).injective
    apply Additive.ofMul.injective
    apply (QuotientGroup.eq_one_iff
      (N := (CompleteDVF.higherPrincipalUnitGroup F.toCompleteDVF (n + 1)).subgroupOf
        (CompleteDVF.higherPrincipalUnitGroup F.toCompleteDVF 1))
      (Additive.toMul x)).mpr
    exact hx

end LocalField
end LocalFieldTheory.DiscreteValuationField
end
end

section
-- module Solutions.OAIQ244_DUKE.LocalField_DiscreteValuationField_MixedCharacteristicStructure_DeepPrincipalUnits
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_isCompleteDiscrete _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.DiscreteNthRootsSubgroup.instCommGroupSubtypeUnitsMemSubgroup _root_.KummerTheory.DiscreteNthRootsSubgroup.instTopologicalSpaceSubtypeUnitsMemSubgroup _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.residueFieldZModAlgebra _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.OAI.PrimeDegreePackets.xT2Space _root_.RamificationTheory.HilbertRamification.Higher.lowerRamificationGroup.instNormal _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionFixedSubring.instIsLocalRing _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionResidueField.instField _root_.RamificationTheory.HilbertRamification.ValuationSubring.selectedResidueField.instAlgebra _root_.RayClass.approximationCompletionTopologicalSpace _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.CyclicCohomology.binaryCoefficientFamilyCommGroup _root_.LocalClassFieldTheory.intrinsicAbsoluteGaloisT2 _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.LocalClassFieldTheory.normalizationIntegerRingIsIntegralClosure _root_.RamificationTheory.HilbertRamification.CompleteDVF.decompositionGroupMulSemiringAction _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.chosenFinitePlaceCompletionAlgebra _root_.finiteLocalUnitsOpen _root_.relativeAdeleRingIntermediateAlgebra _root_.relativeAdeleRingTopIntermediateAlgebra
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

/-! ### Continuity for the normalized valuation used by the deep exponential–logarithm equivalence -/

/-! ### the deep exponential–logarithm equivalence connected to the integral basis -/

/-- The logarithmic depth inequality forces a positive filtration level. -/
theorem mixed_one_le_of_log_level
    (v : _root_.Valuation K (WithZero (Multiplicative ℤ)))
    [ValuationTheory.DiscreteValuationField.Valuation.IsCompleteDiscrete v]
    [Finite (IsLocalRing.ResidueField v.valuationSubring)] [CharZero K]
    (n : ℕ)
    (hlevel :
      (ramificationIndexOfWithZeroValuation v : ℚ) /
          (((ofWithZeroValuation v).residueCharacteristic : ℚ) - 1) <
        (n : ℚ)) :
    1 ≤ n := by
  let F : LocalField.{u, 0} K := ofWithZeroValuation v
  have hpden : (0 : ℚ) < (F.residueCharacteristic : ℚ) - 1 := by
    have hpq : (1 : ℚ) < F.residueCharacteristic := by
      exact_mod_cast F.residueCharacteristic_prime.one_lt
    linarith
  have hepos : (0 : ℚ) <
      (ramificationIndexOfWithZeroValuation v : ℚ) := by
    exact_mod_cast ramificationIndexOfWithZeroValuation_pos v
  have hnq : (0 : ℚ) < (n : ℚ) :=
    lt_trans (div_pos hepos hpden) hlevel
  exact_mod_cast hnq

/-- The logarithm direction of the deep exponential–logarithm equivalence, written as a topological
additive equivalence `U^n ≃ₜ+ m^n`. -/
noncomputable def mixed_deepLogContinuousAddEquiv
    (v : _root_.Valuation K (WithZero (Multiplicative ℤ)))
    [ValuationTheory.DiscreteValuationField.Valuation.IsCompleteDiscrete v]
    [Finite (IsLocalRing.ResidueField v.valuationSubring)] [CharZero K]
    (hv : Function.Surjective v)
    (n : ℕ)
    (hlevel :
      (ramificationIndexOfWithZeroValuation v : ℚ) /
          (((ofWithZeroValuation v).residueCharacteristic : ℚ) - 1) <
        (n : ℚ)) :
    let F : LocalField.{u, 0} K := ofWithZeroValuation v
    letI : MixedWithZeroValuationContext v :=
      mixedWithZeroValuationContext v
    letI : Valued K (WithZero (Multiplicative ℤ)) := Valued.mk' v
    Additive (LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup (F.toCompleteDVF) n) ≃ₜ+
      ((F.toCompleteDVF.maximalIdeal ^ n :
        Ideal F.toCompleteDVF.valuationSubring)) := by
  let F : LocalField.{u, 0} K := ofWithZeroValuation v
  letI : MixedWithZeroValuationContext v :=
    mixedWithZeroValuationContext v
  letI : Valued K (WithZero (Multiplicative ℤ)) := Valued.mk' v
  exact continuousAddEquivOfMultiplicativeSource
    (MultiplicativeIntegerValuation.chosenExpLogContinuousMulEquiv
      v hv n hlevel)

/-- At a depth allowed by the deep exponential–logarithm equivalence, logarithm is a `Z_p`-linear
equivalence from `U^n` to the additive ideal `m^n`. -/
noncomputable def mixed_deepLogLinearEquiv
    (v : _root_.Valuation K (WithZero (Multiplicative ℤ)))
    [ValuationTheory.DiscreteValuationField.Valuation.IsCompleteDiscrete v]
    [Finite (IsLocalRing.ResidueField v.valuationSubring)] [CharZero K]
    (hv : Function.Surjective v)
    (n : ℕ)
    (hlevel :
      (ramificationIndexOfWithZeroValuation v : ℚ) /
          (((ofWithZeroValuation v).residueCharacteristic : ℚ) - 1) <
        (n : ℚ)) :
    let F : LocalField.{u, 0} K := ofWithZeroValuation v
    let hn : 1 ≤ n := mixed_one_le_of_log_level v n hlevel
    letI : MixedWithZeroValuationContext v :=
      mixedWithZeroValuationContext v
    letI : Valued K (WithZero (Multiplicative ℤ)) := Valued.mk' v
    letI : Module ℤ_[F.residueCharacteristic]
        (Additive (LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup (F.toCompleteDVF) n)) :=
      F.higherPrincipalUnitPadicModule hn
    Additive (LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup (F.toCompleteDVF) n) ≃ₗ[
        ℤ_[F.residueCharacteristic]]
      ((F.toCompleteDVF.maximalIdeal ^ n :
        Ideal F.toCompleteDVF.valuationSubring)) := by
  let F : LocalField.{u, 0} K := ofWithZeroValuation v
  let hn : 1 ≤ n := mixed_one_le_of_log_level v n hlevel
  letI : MixedWithZeroValuationContext v :=
    mixedWithZeroValuationContext v
  letI : Valued K (WithZero (Multiplicative ℤ)) := Valued.mk' v
  letI : Module ℤ_[F.residueCharacteristic]
      (Additive (LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup (F.toCompleteDVF) n)) :=
    F.higherPrincipalUnitPadicModule hn
  letI : ContinuousSMul ℤ_[F.residueCharacteristic]
      (Additive (LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup (F.toCompleteDVF) n)) :=
    continuousSMul_padicInt_higherPrincipalUnit_ofWithZeroValuation v hn
  letI : ContinuousSMul ℤ_[F.residueCharacteristic]
      ((F.toCompleteDVF.maximalIdeal ^ n :
        Ideal F.toCompleteDVF.valuationSubring)) :=
    continuousSMul_padicInt_maximalIdealPow_ofWithZeroValuation v n
  let e := mixed_deepLogContinuousAddEquiv
    v hv n hlevel
  exact padicLinearEquivOfContinuousAddEquiv e.toAddEquiv e.continuous

end LocalField
end LocalFieldTheory.DiscreteValuationField
end
end

section
-- module Solutions.OAIQ244_DUKE.LocalField_DiscreteValuationField_PowerIndex
attribute [-instance] _root_.ClassFormation.DegreeData.FiniteAbstractExtension.ramificationQuotientFinite _root_.ClassFormation.DegreeData.FiniteAbstractExtension.representedQuotientFinite _root_.ClassFormation.DegreeData.FiniteAbstractExtension.residueQuotientFinite _root_.ClassFormation.DegreeData.FiniteAmbientFrobeniusFixedFieldTower.ambientRepresentedQuotientFinite _root_.ClassFormation.DegreeData.FiniteResidueAbstractExtension.instFiniteQuotientSubtypeMemSubgroupFieldBaseExtensionSubgroupField _root_.ClassFormation.DegreeData.FiniteTower.baseQuotientFinite _root_.ClassFormation.DegreeData.FiniteTower.topQuotientFinite _root_.ClassFormation.DegreeData.FiniteTower.totalQuotientFinite _root_.ClassFormation.DegreeData.FrobeniusFixedFieldTower.baseAbsoluteFiniteInstance _root_.ClassFormation.DegreeData.FrobeniusFixedFieldTower.extensionFinite _root_.ClassFormation.DegreeData.FrobeniusFixedFieldTower.fieldAbsoluteFiniteInstance _root_.ClassFormation.DegreeData.FrobeniusPowerFixedFieldTower.baseRepresentedAbsoluteFinite _root_.ClassFormation.DegreeData.FrobeniusPowerFixedFieldTower.fieldRepresentedAbsoluteFinite _root_.ClassFormation.DegreeData.FrobeniusPowerFixedFieldTower.relativeRepresentedQuotientFinite _root_.ClassFormation.FiniteAbstractField.instFiniteQuotientSubtypeMemSubgroupBaseFieldExtensionSubgroupField _root_.ClassFormation.FiniteAbstractField.toFiniteResidueAbstractField_extensionFinite _root_.ClassFormation.FiniteAbstractFieldExtension.instFiniteQuotientSubtypeMemSubgroupFieldBaseExtensionSubgroupField _root_.ClassFormation.FiniteCyclicSubextension.instFiniteQuotientSubtypeMemSubgroupFieldExtensionSubgroupField _root_.ClassFormation.FiniteUnramifiedCyclicExtension.instFiniteQuotientSubtypeMemSubgroupBaseFieldExtensionSubgroupField _root_.ClassFormation.FiniteUnramifiedCyclicExtension.instFiniteQuotientSubtypeMemSubgroupFieldExtensionSubgroupField _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_isCompleteDiscrete _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.DiscreteNthRootsSubgroup.instCommGroupSubtypeUnitsMemSubgroup _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.KummerTheory.finite_finsupp_nsmulQuotient _root_.KummerTheory.finite_sUnit_nthPowerQuotient _root_.LocalClassFieldTheory.baseFixingExtensionQuotient_finite _root_.LocalClassFieldTheory.baseFixingExtensionQuotient_finite_of_isSeparable _root_.LocalClassFieldTheory.localDecompositionResidueFinite _root_.LocalClassFieldTheory.localSeparableValuationHasExtension _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.AdicPrincipalUnits.instAddCommGroup _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.AdicPrincipalUnits.instTopologicalSpace _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.DiscretePrincipalUnitQuotient.instAddCommGroup _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitInverseLimitCarrierPadicModule _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitQuotientCarrierPadicModule _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitQuotientCarrier_finite _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.PrincipalUnitProdiscreteLimit.instAddCommGroup _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.PrincipalUnitProdiscreteLimit.instTopologicalSpace _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitPadicModule _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitPadicSMul _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.residueFieldZModAlgebra _root_.LocalFieldTheory.DiscreteValuationField.Examples.Qp.padicDVRValuation_isCompleteDiscrete _root_.LocalFieldTheory.DiscreteValuationField.Examples.Qp.padicDVRValuation_isRankOneDiscrete _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedIntegralAlgebraContextValuationSubringAlgebra _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedMaximalIdealPowContextModuleFinite _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedMaximalIdealPowContextModuleFree _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedQPadicContextValuationExtension _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedQPadicContextValuationSubringTower _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedWithZeroValuationContextIntegralAlgebra _root_.LocalFieldTheory.DiscreteValuationField.finite_nsmulAddKernel_padicInt_pi _root_.LocalFieldTheory.DiscreteValuationField.finite_padicInt_finPi_nsmulQuotient _root_.LocalFieldTheory.DiscreteValuationField.finite_padicInt_pi_nsmulQuotient_of_coprime _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LubinTate.compatibleGroupFamiliesCommGroup _root_.LubinTate.compatibleGroupFamiliesGroup _root_.OAI.PrimeDegreePackets.boundedRealFields_finite _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.RamificationTheory.HilbertRamification.Higher.lowerRamificationGroup.instNormal _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionResidueField.instField _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.CyclicCohomology.binaryCoefficientFamilyCommGroup _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.LocalClassFieldTheory.normalizationIntegerRingIsIntegralClosure _root_.RamificationTheory.HilbertRamification.CompleteDVF.decompositionGroupMulSemiringAction _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen
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

/-- The Teichmüller root factor is finite because it is equivalent to the
unit group of the finite residue field. -/
noncomputable instance finite_residueRootsOfUnityGroup
    (F : CompleteDVF.{u, v} K) [Finite F.residueField] :
    Finite
      (LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.residueRootsOfUnityGroup F) :=
  Finite.of_equiv F.residueFieldˣ
    (LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.residueRootsOfUnityEquivResidueFieldUnits
      F).symm.toEquiv

/-- A nonzero power has only finitely many roots in the valuation-ring unit
group, by injectivity of `O_Kˣ → Kˣ`. -/
noncomputable instance finite_valuationSubringUnits_nthPowerKernel
    (F : CompleteDVF.{u, v} K) (n : ℕ) [NeZero n] :
    Finite ((powMonoidHom n : F.valuationSubringˣ →* F.valuationSubringˣ).ker) := by
  apply LocalFieldTheory.finite_nthPowerKernel_of_injective F.valuationSubringˣ Kˣ n
    (LocalFieldTheory.DiscreteValuationField.CompleteDVF.valuationSubringUnitsToFieldUnits F)
  intro a b hab
  apply Units.ext
  apply Subtype.ext
  simpa only [CompleteDVF.coe_valuationSubringUnitsToFieldUnits_apply] using
    congrArg (fun z : Kˣ => (z : K)) hab

/-- A nonzero power has finite kernel on the first principal-unit subgroup. -/
noncomputable instance finite_principalUnits_nthPowerKernel
    (F : CompleteDVF.{u, v} K) (n : ℕ) [NeZero n] :
    Finite
      ((powMonoidHom n : ((LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup F) 1) →* ((LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup F) 1)).ker) := by
  apply LocalFieldTheory.finite_nthPowerKernel_of_injective
    ((LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup F) 1)
    F.valuationSubringˣ n
    ((LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup F) 1).subtype
  exact Subtype.val_injective

/-- Finiteness of the principal-unit power quotient implies finiteness of
the full valuation-ring unit quotient through the root/principal product
decomposition. -/
noncomputable instance finite_valuationSubringUnits_nthPowerQuotient
    (F : CompleteDVF.{u, v} K) [Finite F.residueField] (n : ℕ)
    [Finite
      ((LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup F) 1 ⧸
        (powMonoidHom n : ((LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup F) 1) →* ((LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup F) 1)).range)] :
    Finite (F.valuationSubringˣ ⧸ (powMonoidHom n : F.valuationSubringˣ →* F.valuationSubringˣ).range) := by
  let e :
      F.valuationSubringˣ ≃*
        LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.residueRootsOfUnityGroup F ×
          (LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup F) 1 :=
    (LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.valuationSubringUnitsEquivRootsTimesPrincipalUnits
      F).symm
  exact LocalFieldTheory.finite_nthPowerQuotient_of_mulEquiv
    F.valuationSubringˣ
    (LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.residueRootsOfUnityGroup F ×
      (LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup F) 1)
    n e

/-- Finiteness of the principal-unit power quotient, together with a chosen
uniformizer, explicitly yields finiteness of the full field-unit quotient.
This remains a constructor rather than a global instance so the analytic
finite boundary stays visible to callers. -/
theorem finite_fieldUnits_nthPowerQuotient_of_finite_principalUnits
    (F : CompleteDVF.{u, v} K) [Finite F.residueField]
    {π : F.valuationSubring} (hπ : F.valuation.IsUniformizer (π : K))
    (n : ℕ) [NeZero n]
    [Finite
      ((LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup F) 1 ⧸
        (powMonoidHom n : ((LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup F) 1) →* ((LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup F) 1)).range)] :
    Finite (Kˣ ⧸ (powMonoidHom n : Kˣ →* Kˣ).range) := by
  let eField :
      LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.fieldUnitDecompositionFactors F ≃*
        Kˣ :=
    _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.fieldUnitsEquivRootsPrincipalUnitsUniformizer_of_completeDVF
      F hπ
  let eUnits :
      LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.residueRootsOfUnityGroup F ×
          (LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup F) 1 ≃*
        F.valuationSubringˣ :=
    LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.valuationSubringUnitsEquivRootsTimesPrincipalUnits
      F
  let e :
      Kˣ ≃* F.valuationSubringˣ × Multiplicative ℤ :=
    eField.symm.trans
      (MulEquiv.prodCongr eUnits (MulEquiv.refl (Multiplicative ℤ)))
  exact LocalFieldTheory.finite_nthPowerQuotient_of_mulEquiv_units_prod_int
    Kˣ F.valuationSubringˣ e

/-- The local-field power-index formula, first equality: after choosing a
uniformizer, the field-unit `n`-th-power quotient has the unit quotient as a
factor and the uniformizer direction contributes exactly `n`. -/
theorem card_fieldUnits_nthPowerQuotient_eq_mul_unit_nthPowerQuotient
    (F : CompleteDVF.{u, v} K) [Finite F.residueField]
    {π : F.valuationSubring} (hπ : F.valuation.IsUniformizer (π : K))
    (n : ℕ) [NeZero n]
    [Finite (Kˣ ⧸ (powMonoidHom n : Kˣ →* Kˣ).range)]
    [Finite (F.valuationSubringˣ ⧸ (powMonoidHom n : F.valuationSubringˣ →* F.valuationSubringˣ).range)] :
    Nat.card (Kˣ ⧸ (powMonoidHom n : Kˣ →* Kˣ).range) =
      n * Nat.card (F.valuationSubringˣ ⧸
        (powMonoidHom n : F.valuationSubringˣ →* F.valuationSubringˣ).range) := by
  let eField :
      LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.fieldUnitDecompositionFactors F ≃*
        Kˣ :=
    _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.fieldUnitsEquivRootsPrincipalUnitsUniformizer_of_completeDVF
      F hπ
  let eUnits :
      LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.residueRootsOfUnityGroup F ×
          (LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup F) 1 ≃*
        F.valuationSubringˣ :=
    LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.valuationSubringUnitsEquivRootsTimesPrincipalUnits
      F
  let e :
      Kˣ ≃* F.valuationSubringˣ × Multiplicative ℤ :=
    eField.symm.trans
      (MulEquiv.prodCongr eUnits (MulEquiv.refl (Multiplicative ℤ)))
  exact
    LocalFieldTheory.card_nthPowerQuotient_eq_mul_of_mulEquiv_units_prod_int
      Kˣ F.valuationSubringˣ (NeZero.ne n) e

/-- The local-field power-index formula, unit-decomposition reduction: the unit
`n`-th-power quotient splits into the residue root-of-unity factor and the
first principal-unit factor. -/
theorem card_unit_nthPowerQuotient_eq_mul_roots_principalUnit_nthPowerQuotient
    (F : CompleteDVF.{u, v} K) [Finite F.residueField] (n : ℕ)
    [Finite
      ((LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup F) 1 ⧸
        (powMonoidHom n : ((LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup F) 1) →* ((LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup F) 1)).range)] :
    Nat.card (F.valuationSubringˣ ⧸
        (powMonoidHom n : F.valuationSubringˣ →* F.valuationSubringˣ).range) =
      Nat.card
          (LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.residueRootsOfUnityGroup F ⧸
            (powMonoidHom n : (LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.residueRootsOfUnityGroup F) →* (LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.residueRootsOfUnityGroup F)).range) *
        Nat.card
          ((LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup F) 1 ⧸
            (powMonoidHom n : ((LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup F) 1) →* ((LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup F) 1)).range) := by
  let e :
      F.valuationSubringˣ ≃*
        LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.residueRootsOfUnityGroup F ×
          (LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup F) 1 :=
    (LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.valuationSubringUnitsEquivRootsTimesPrincipalUnits
      F).symm
  exact
    LocalFieldTheory.card_nthPowerQuotient_eq_mul_of_mulEquiv_prod
      F.valuationSubringˣ
      (LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.residueRootsOfUnityGroup F)
      ((LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup F) 1) n e

/-- On the finite Teichmuller root factor, the `n`-th-power quotient has the
same size as the subgroup killed by `n`. -/
theorem card_residueRoots_nthPowerQuotient_eq_nthPowerKernel
    (F : CompleteDVF.{u, v} K) [Finite F.residueField] (n : ℕ) :
    Nat.card
        (LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.residueRootsOfUnityGroup F ⧸
          (powMonoidHom n : (LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.residueRootsOfUnityGroup F) →* (LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.residueRootsOfUnityGroup F)).range) =
      Nat.card
        ((powMonoidHom n : (LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.residueRootsOfUnityGroup F) →* (LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.residueRootsOfUnityGroup F)).ker) := by
  classical
  let e :
      LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.residueRootsOfUnityGroup F ≃*
        F.residueFieldˣ :=
    LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.residueRootsOfUnityEquivResidueFieldUnits
      F
  have :
      Finite (LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.residueRootsOfUnityGroup F) :=
    Finite.of_equiv F.residueFieldˣ e.symm.toEquiv
  exact
    LocalFieldTheory.card_nthPowerQuotient_eq_nthPowerKernel
      (LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.residueRootsOfUnityGroup F) n

/-- The `n`-torsion kernel of the full unit group splits into the finite
Teichmuller root factor and the first principal-unit factor. -/
theorem card_unit_nthPowerKernel_eq_mul_roots_principalUnit_nthPowerKernel
    (F : CompleteDVF.{u, v} K) [Finite F.residueField] (n : ℕ) [NeZero n] :
    Nat.card
        ((powMonoidHom n : F.valuationSubringˣ →* F.valuationSubringˣ).ker) =
      Nat.card
          ((powMonoidHom n : (LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.residueRootsOfUnityGroup F) →* (LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.residueRootsOfUnityGroup F)).ker) *
        Nat.card
          ((powMonoidHom n : ((LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup F) 1) →* ((LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup F) 1)).ker) := by
  let e :
      F.valuationSubringˣ ≃*
        LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.residueRootsOfUnityGroup F ×
          (LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup F) 1 :=
    (LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.valuationSubringUnitsEquivRootsTimesPrincipalUnits
      F).symm
  exact
    LocalFieldTheory.card_nthPowerKernel_eq_mul_of_mulEquiv_prod
      F.valuationSubringˣ
      (LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.residueRootsOfUnityGroup F)
      ((LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup F) 1) n e

/-- For nonzero `n`, the field-unit `n`-torsion kernel is the unit
`n`-torsion kernel; the uniformizer direction has no nontrivial finite
`n`-torsion. -/
theorem card_fieldUnits_nthPowerKernel_eq_unit_nthPowerKernel
    (F : CompleteDVF.{u, v} K) [Finite F.residueField]
    {π : F.valuationSubring} (hπ : F.valuation.IsUniformizer (π : K))
    (n : ℕ) [NeZero n] :
    Nat.card ((powMonoidHom n : Kˣ →* Kˣ).ker) =
      Nat.card ((powMonoidHom n : F.valuationSubringˣ →* F.valuationSubringˣ).ker) := by
  let eField :
      LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.fieldUnitDecompositionFactors F ≃*
        Kˣ :=
    _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.fieldUnitsEquivRootsPrincipalUnitsUniformizer_of_completeDVF
      F hπ
  let eUnits :
      LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.residueRootsOfUnityGroup F ×
          (LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup F) 1 ≃*
        F.valuationSubringˣ :=
    LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.valuationSubringUnitsEquivRootsTimesPrincipalUnits
      F
  let e :
      Kˣ ≃* F.valuationSubringˣ × Multiplicative ℤ :=
    eField.symm.trans
      (MulEquiv.prodCongr eUnits (MulEquiv.refl (Multiplicative ℤ)))
  exact
    LocalFieldTheory.card_nthPowerKernel_eq_of_mulEquiv_units_prod_int
      Kˣ F.valuationSubringˣ (NeZero.ne n) e

/-- For nonzero `n`, the field-unit `n`-torsion kernel is the product of the
Teichmuller `n`-torsion kernel and the first principal-unit `n`-torsion
kernel.  This is the group-theoretic `μ_n(K)` decomposition behind
the local-field power-index formula. -/
theorem card_fieldUnits_nthPowerKernel_eq_mul_roots_principalUnit_nthPowerKernel
    (F : CompleteDVF.{u, v} K) [Finite F.residueField]
    {π : F.valuationSubring} (hπ : F.valuation.IsUniformizer (π : K))
    (n : ℕ) [NeZero n] :
    Nat.card ((powMonoidHom n : Kˣ →* Kˣ).ker) =
      Nat.card
          ((powMonoidHom n : (LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.residueRootsOfUnityGroup F) →* (LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.residueRootsOfUnityGroup F)).ker) *
        Nat.card
          ((powMonoidHom n : ((LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup F) 1) →* ((LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup F) 1)).ker) := by
  rw [card_fieldUnits_nthPowerKernel_eq_unit_nthPowerKernel
    (F := F) hπ n]
  rw [card_unit_nthPowerKernel_eq_mul_roots_principalUnit_nthPowerKernel
    (F := F) n]

/-- The local-field power-index formula, unit-index reduction after identifying the finite
root-of-unity quotient with its `n`-torsion kernel.  The remaining analytic
input is the principal-unit factor, supplied by the field-unit structure theorem. -/
theorem card_unit_nthPowerQuotient_eq_mul_rootsKernel_principalUnit_nthPowerQuotient
    (F : CompleteDVF.{u, v} K) [Finite F.residueField] (n : ℕ)
    [Finite
      ((LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup F) 1 ⧸
        (powMonoidHom n : ((LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup F) 1) →* ((LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup F) 1)).range)] :
    Nat.card (F.valuationSubringˣ ⧸
        (powMonoidHom n : F.valuationSubringˣ →* F.valuationSubringˣ).range) =
      Nat.card
          ((powMonoidHom n : (LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.residueRootsOfUnityGroup F) →* (LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.residueRootsOfUnityGroup F)).ker) *
        Nat.card
          ((LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup F) 1 ⧸
            (powMonoidHom n : ((LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup F) 1) →* ((LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup F) 1)).range) := by
  rw [card_unit_nthPowerQuotient_eq_mul_roots_principalUnit_nthPowerQuotient,
    card_residueRoots_nthPowerQuotient_eq_nthPowerKernel]

/-- The local-field power-index formula, field-unit index reduced to the finite root factor and the
principal-unit factor.  The uniformizer contributes `n`; the finite
root-of-unity factor is already expressed as its `n`-torsion kernel. -/
theorem card_fieldUnits_nthPowerQuotient_eq_mul_rootsKernel_principalUnit_nthPowerQuotient
    (F : CompleteDVF.{u, v} K) [Finite F.residueField]
    {π : F.valuationSubring} (hπ : F.valuation.IsUniformizer (π : K))
    (n : ℕ) [NeZero n]
    [Finite (Kˣ ⧸ (powMonoidHom n : Kˣ →* Kˣ).range)]
    [Finite
      ((LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup F) 1 ⧸
        (powMonoidHom n : ((LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup F) 1) →* ((LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup F) 1)).range)] :
    Nat.card (Kˣ ⧸ (powMonoidHom n : Kˣ →* Kˣ).range) =
      n *
        (Nat.card
            ((powMonoidHom n : (LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.residueRootsOfUnityGroup F) →* (LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.residueRootsOfUnityGroup F)).ker) *
          Nat.card
            ((LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup F) 1 ⧸
              (powMonoidHom n : ((LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup F) 1) →* ((LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup F) 1)).range)) := by
  rw [card_fieldUnits_nthPowerQuotient_eq_mul_unit_nthPowerQuotient
    (F := F) hπ n]
  rw [card_unit_nthPowerQuotient_eq_mul_rootsKernel_principalUnit_nthPowerQuotient
    (F := F) n]

/-- The field-unit structure theorem logarithmic transport, principal-unit form: any
multiplicative logarithm equivalence from `U¹` to an additive group identifies
the principal-unit `n`-th-power quotient with the additive quotient by
`n`-fold multiples. -/
theorem card_principalUnit_nthPowerQuotient_eq_additive_nsmulQuotient_of_logEquiv
    (F : CompleteDVF.{u, v} K)
    (A : Type*) [AddCommGroup A]
    (n : ℕ)
    [Finite
      ((LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup F) 1 ⧸
        (powMonoidHom n : ((LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup F) 1) →* ((LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup F) 1)).range)]
    [Finite (A ⧸ LocalFieldTheory.nsmulAddSubgroup A n)]
    (e : (LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup F) 1 ≃* Multiplicative A) :
    Nat.card
        ((LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup F) 1 ⧸
          (powMonoidHom n : ((LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup F) 1) →* ((LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup F) 1)).range) =
      Nat.card (A ⧸ LocalFieldTheory.nsmulAddSubgroup A n) :=
  LocalFieldTheory.card_nthPowerQuotient_eq_additive_nsmulQuotient_of_mulEquiv
    (A := A) (G := (LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup F) 1) n e

/-- The field-unit structure theorem logarithmic transport, kernel form: under the same
principal-unit logarithm equivalence, the principal-unit `n`-torsion kernel
has the same cardinality as the additive kernel of `x ↦ n • x`. -/
theorem card_principalUnit_nthPowerKernel_eq_additive_nsmulKernel_of_logEquiv
    (F : CompleteDVF.{u, v} K)
    (A : Type*) [AddCommGroup A]
    (n : ℕ) [NeZero n]
    [Finite (LocalFieldTheory.nsmulAddKernel A n)]
    (e : (LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup F) 1 ≃* Multiplicative A) :
    Nat.card ((powMonoidHom n : ((LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup F) 1) →* ((LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup F) 1)).ker) =
      Nat.card (LocalFieldTheory.nsmulAddKernel A n) :=
  LocalFieldTheory.card_nthPowerKernel_eq_additive_nsmulKernel_of_mulEquiv
    (A := A) (G := (LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup F) 1) n e

/-- The field-unit structure theorem logarithmic transport in kernel-factor form: after a
principal-unit logarithm equivalence, a finite additive kernel/cokernel
calculation immediately supplies the kernel times defect factor used by
the local-field power-index formula. -/
theorem card_principalUnit_nthPowerQuotient_eq_mul_kernel_of_logEquiv
    (F : CompleteDVF.{u, v} K)
    (A : Type*) [AddCommGroup A]
    (n c : ℕ) [NeZero n]
    [Finite
      ((LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup F) 1 ⧸
        (powMonoidHom n : ((LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup F) 1) →* ((LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup F) 1)).range)]
    [Finite (A ⧸ LocalFieldTheory.nsmulAddSubgroup A n)]
    [Finite (LocalFieldTheory.nsmulAddKernel A n)]
    (e : (LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup F) 1 ≃* Multiplicative A)
    (hadd :
      Nat.card (A ⧸ LocalFieldTheory.nsmulAddSubgroup A n) =
        Nat.card (LocalFieldTheory.nsmulAddKernel A n) * c) :
    Nat.card
        ((LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup F) 1 ⧸
          (powMonoidHom n : ((LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup F) 1) →* ((LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup F) 1)).range) =
      Nat.card ((powMonoidHom n : ((LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup F) 1) →* ((LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup F) 1)).ker) * c := by
  rw [card_principalUnit_nthPowerQuotient_eq_additive_nsmulQuotient_of_logEquiv
    (F := F) (A := A) n e]
  rw [hadd]
  rw [card_principalUnit_nthPowerKernel_eq_additive_nsmulKernel_of_logEquiv
    (F := F) (A := A) n e]

/-- The local-field power-index formula reduced to the analytic principal-unit index statement.
If the field-unit structure theorem supplies the principal-unit quotient as its `n`-torsion
kernel times a defect factor `c`, then the field-unit quotient is `n` times
the field-unit `n`-torsion kernel times the same defect. -/
theorem card_fieldUnits_nthPowerQuotient_eq_mul_fieldKernel_of_principalUnit_index
    (F : CompleteDVF.{u, v} K) [Finite F.residueField]
    {π : F.valuationSubring} (hπ : F.valuation.IsUniformizer (π : K))
    {n c : ℕ} [NeZero n]
    [Finite (Kˣ ⧸ (powMonoidHom n : Kˣ →* Kˣ).range)]
    [Finite
      ((LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup F) 1 ⧸
        (powMonoidHom n : ((LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup F) 1) →* ((LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup F) 1)).range)]
    (hprincipal :
      Nat.card
          ((LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup F) 1 ⧸
            (powMonoidHom n : ((LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup F) 1) →* ((LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup F) 1)).range) =
        Nat.card
          ((powMonoidHom n : ((LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup F) 1) →* ((LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup F) 1)).ker) * c) :
    Nat.card (Kˣ ⧸ (powMonoidHom n : Kˣ →* Kˣ).range) =
      n * (Nat.card ((powMonoidHom n : Kˣ →* Kˣ).ker) * c) := by
  rw [card_fieldUnits_nthPowerQuotient_eq_mul_rootsKernel_principalUnit_nthPowerQuotient
    (F := F) hπ n]
  rw [hprincipal]
  rw [card_fieldUnits_nthPowerKernel_eq_mul_roots_principalUnit_nthPowerKernel
    (F := F) hπ n]
  ring

/-- The local-field power-index formula, field-index form fed directly by a principal-unit logarithm
equivalence and an additive kernel/cokernel calculation. -/
theorem card_fieldUnits_nthPowerQuotient_eq_mul_fieldKernel_of_logEquiv
    (F : CompleteDVF.{u, v} K) [Finite F.residueField]
    {π : F.valuationSubring} (hπ : F.valuation.IsUniformizer (π : K))
    (A : Type*) [AddCommGroup A]
    {n c : ℕ} [NeZero n]
    [Finite (Kˣ ⧸ (powMonoidHom n : Kˣ →* Kˣ).range)]
    [Finite
      ((LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup F) 1 ⧸
        (powMonoidHom n : ((LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup F) 1) →* ((LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup F) 1)).range)]
    [Finite (A ⧸ LocalFieldTheory.nsmulAddSubgroup A n)]
    [Finite (LocalFieldTheory.nsmulAddKernel A n)]
    (e : (LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup F) 1 ≃* Multiplicative A)
    (hadd :
      Nat.card (A ⧸ LocalFieldTheory.nsmulAddSubgroup A n) =
        Nat.card (LocalFieldTheory.nsmulAddKernel A n) * c) :
    Nat.card (Kˣ ⧸ (powMonoidHom n : Kˣ →* Kˣ).range) =
      n * (Nat.card ((powMonoidHom n : Kˣ →* Kˣ).ker) * c) :=
  card_fieldUnits_nthPowerQuotient_eq_mul_fieldKernel_of_principalUnit_index
    (F := F) hπ
    (hprincipal :=
      card_principalUnit_nthPowerQuotient_eq_mul_kernel_of_logEquiv
        (F := F) (A := A) n c e hadd)

end CompleteDVF

end LocalFieldTheory.DiscreteValuationField

end
end

section
-- module Solutions.OAIQ244_DUKE.LocalField_DiscreteValuationField_PadicPowerIndex
attribute [-instance] _root_.ClassFormation.DegreeData.FiniteAbstractExtension.ramificationQuotientFinite _root_.ClassFormation.DegreeData.FiniteAbstractExtension.representedQuotientFinite _root_.ClassFormation.DegreeData.FiniteAbstractExtension.residueQuotientFinite _root_.ClassFormation.DegreeData.FiniteAmbientFrobeniusFixedFieldTower.ambientRepresentedQuotientFinite _root_.ClassFormation.DegreeData.FiniteResidueAbstractExtension.instFiniteQuotientSubtypeMemSubgroupFieldBaseExtensionSubgroupField _root_.ClassFormation.DegreeData.FiniteTower.baseQuotientFinite _root_.ClassFormation.DegreeData.FiniteTower.topQuotientFinite _root_.ClassFormation.DegreeData.FiniteTower.totalQuotientFinite _root_.ClassFormation.DegreeData.FrobeniusFixedFieldTower.baseAbsoluteFiniteInstance _root_.ClassFormation.DegreeData.FrobeniusFixedFieldTower.extensionFinite _root_.ClassFormation.DegreeData.FrobeniusFixedFieldTower.fieldAbsoluteFiniteInstance _root_.ClassFormation.DegreeData.FrobeniusPowerFixedFieldTower.baseRepresentedAbsoluteFinite _root_.ClassFormation.DegreeData.FrobeniusPowerFixedFieldTower.fieldRepresentedAbsoluteFinite _root_.ClassFormation.DegreeData.FrobeniusPowerFixedFieldTower.relativeRepresentedQuotientFinite _root_.ClassFormation.FiniteAbstractField.instFiniteQuotientSubtypeMemSubgroupBaseFieldExtensionSubgroupField _root_.ClassFormation.FiniteAbstractField.toFiniteResidueAbstractField_extensionFinite _root_.ClassFormation.FiniteAbstractFieldExtension.instFiniteQuotientSubtypeMemSubgroupFieldBaseExtensionSubgroupField _root_.ClassFormation.FiniteCyclicSubextension.instFiniteQuotientSubtypeMemSubgroupFieldExtensionSubgroupField _root_.ClassFormation.FiniteUnramifiedCyclicExtension.instFiniteQuotientSubtypeMemSubgroupBaseFieldExtensionSubgroupField _root_.ClassFormation.FiniteUnramifiedCyclicExtension.instFiniteQuotientSubtypeMemSubgroupFieldExtensionSubgroupField _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_isCompleteDiscrete _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.DiscreteNthRootsSubgroup.instCommGroupSubtypeUnitsMemSubgroup _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.KummerTheory.finite_finsupp_nsmulQuotient _root_.KummerTheory.finite_sUnit_nthPowerQuotient _root_.LocalClassFieldTheory.baseFixingExtensionQuotient_finite _root_.LocalClassFieldTheory.baseFixingExtensionQuotient_finite_of_isSeparable _root_.LocalClassFieldTheory.localDecompositionResidueFinite _root_.LocalClassFieldTheory.localSeparableValuationHasExtension _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.AdicPrincipalUnits.instAddCommGroup _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.AdicPrincipalUnits.instTopologicalSpace _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.DiscretePrincipalUnitQuotient.instAddCommGroup _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitInverseLimitCarrierPadicModule _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitQuotientCarrierPadicModule _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitQuotientCarrier_finite _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.PrincipalUnitProdiscreteLimit.instAddCommGroup _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.PrincipalUnitProdiscreteLimit.instTopologicalSpace _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitPadicModule _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitPadicSMul _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.residueFieldZModAlgebra _root_.LocalFieldTheory.DiscreteValuationField.Examples.Qp.padicDVRValuation_isCompleteDiscrete _root_.LocalFieldTheory.DiscreteValuationField.Examples.Qp.padicDVRValuation_isRankOneDiscrete _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedIntegralAlgebraContextValuationSubringAlgebra _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedMaximalIdealPowContextModuleFinite _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedMaximalIdealPowContextModuleFree _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedQPadicContextValuationExtension _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedQPadicContextValuationSubringTower _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedWithZeroValuationContextIntegralAlgebra _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LubinTate.compatibleGroupFamiliesCommGroup _root_.LubinTate.compatibleGroupFamiliesGroup _root_.OAI.PrimeDegreePackets.boundedRealFields_finite _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.RamificationTheory.HilbertRamification.Higher.lowerRamificationGroup.instNormal _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.CyclicCohomology.binaryCoefficientFamilyCommGroup _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.LocalClassFieldTheory.normalizationIntegerRingIsIntegralClosure _root_.RamificationTheory.HilbertRamification.CompleteDVF.decompositionGroupMulSemiringAction _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen
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

/-- The local-field power-index formula, mixed-characteristic field-index formula supplied directly
by a principal-unit structure theorem. -/
theorem card_fieldUnits_nthPowerQuotient_of_mixedPrincipalUnitStructure
    (F : CompleteDVF.{u, 0} K) [Finite F.residueField]
    {π : F.valuationSubring} (hπ : F.valuation.IsUniformizer (π : K))
    (T : Type*) [AddCommGroup T] [Finite T]
    (d : ℕ) {n : ℕ} [NeZero n]
    [Finite (Kˣ ⧸ (powMonoidHom n : Kˣ →* Kˣ).range)]
    [Finite
      ((LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup F) 1 ⧸
        (powMonoidHom n : ((LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup F) 1) →* ((LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup F) 1)).range)]
    (e : (LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup F) 1 ≃*
      Multiplicative (T × (Fin d → ℤ_[p]))) :
    Nat.card (Kˣ ⧸ (powMonoidHom n : Kˣ →* Kˣ).range) =
      n * (Nat.card ((powMonoidHom n : Kˣ →* Kˣ).ker) *
        p ^ (d * padicValNat p n)) := by
  exact card_fieldUnits_nthPowerQuotient_eq_mul_fieldKernel_of_logEquiv
    (F := F) hπ (A := T × (Fin d → ℤ_[p])) e
      (card_finite_prod_padicInt_finPi_nsmulQuotient_eq_kernel_mul
        (p := p) T d n)

/-! The exact equal-characteristic specialization, with no artificial finite
factor in the principal-unit product. -/

end LocalFieldIndex

end LocalFieldTheory.DiscreteValuationField
end
end

section
-- module Solutions.OAIQ244_DUKE.LocalField_Padic_PrincipalUnits
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.residueFieldZModAlgebra _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedIntegralAlgebraContextValuationSubringAlgebra _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionResidueField.instField _root_.RamificationTheory.HilbertRamification.ValuationSubring.selectedResidueField.instAlgebra _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.LocalClassFieldTheory.normalizationIntegerRingIsIntegralClosure _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.chosenFinitePlaceCompletionAlgebra _root_.finiteLocalUnitsOpen _root_.relativeAdeleRingIntermediateAlgebra _root_.relativeAdeleRingTopIntermediateAlgebra
attribute [-simp] _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.IsDiscreteValuationRing.addVal_ringEquiv _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.LocalFieldTheory.residueField_algebraMap_residue _root_.OAI.PrimeDegreePackets.ThetaConstruction.schwartzCM_apply _root_.infinitePlace_mult_smul
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

/-- The canonical multiplicative discrete valuation sends `p` to
`exp (-1)`. -/
theorem padicDVR_valuation_p :
    LocalFieldTheory.DiscreteValuationField.Examples.Qp.padicDVRValuation p (p : ℚ_[p]) =
      WithZero.exp (-1 : ℤ) := by
  change (IsDiscreteValuationRing.maximalIdeal ℤ_[p]).valuation ℚ_[p]
      (((p : ℤ_[p]) : ℚ_[p])) = WithZero.exp (-1 : ℤ)
  calc
    (IsDiscreteValuationRing.maximalIdeal ℤ_[p]).valuation ℚ_[p]
        (((p : ℤ_[p]) : ℚ_[p])) =
        (IsDiscreteValuationRing.maximalIdeal ℤ_[p]).intValuation (p : ℤ_[p]) := by
      simpa using
        (IsDiscreteValuationRing.maximalIdeal ℤ_[p]).valuation_of_algebraMap
          (K := ℚ_[p]) (p : ℤ_[p])
    _ = WithZero.exp (-1 : ℤ) :=
      IsDedekindDomain.HeightOneSpectrum.intValuation_singleton
        (IsDiscreteValuationRing.maximalIdeal ℤ_[p])
        (by exact_mod_cast (Fact.out : Nat.Prime p).ne_zero)
        PadicInt.maximalIdeal_eq_span_p

end LocalFieldTheory.Padic

end
end

section
-- module Solutions.OAIQ244_DUKE.GlobalClassFieldTheory_ClassFieldAxiom_IdeleClassPowerLocalUnitQuotient_LocalResidueArithmetic
attribute [-instance] _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.KummerTheory.primeCyclotomicBaseFiniteDimensional _root_.LocalClassFieldTheory.localSeparableValuationHasExtension _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.RamificationTheory.HilbertRamification.Higher.lowerRamificationGroup.instNormal _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionFixedSubring.instIsLocalRing _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionResidueField.instField _root_.RamificationTheory.HilbertRamification.ValuationSubring.selectedResidueField.instAlgebra _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.LocalClassFieldTheory.normalizationIntegerRingIsIntegralClosure _root_.RamificationTheory.HilbertRamification.CompleteDVF.decompositionGroupMulSemiringAction _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.chosenFinitePlaceCompletionAlgebra _root_.chosenFinitePlaceCompletionFiniteDimensional _root_.chosenFinitePlaceLocalizedFiniteDimensional _root_.chosenFinitePlaceLocalizedIntegerAlgebra _root_.chosenFinitePlaceLocalizedValuationHasExtension _root_.relativeAdeleRingIntermediateAlgebra _root_.relativeAdeleRingTopIntermediateAlgebra
attribute [-simp] _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.IsDiscreteValuationRing.addVal_ringEquiv _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.LocalFieldTheory.localIntegerValuationSubringEquiv_apply_coe _root_.LocalFieldTheory.residueField_algebraMap_residue _root_.LubinTate.LubinTateSeries.standardLubinTateSeries_toPowerSeries _root_.LubinTate.SameUniformizer.coeff_recursiveIntertwiner _root_.LubinTate.SameUniformizer.constantCoeff_inVariable _root_.LubinTate.SameUniformizer.intertwinerApproximation_zero _root_.LubinTate.SameUniformizer.standardLubinTateEndomorphism_coeff_one _root_.LubinTate.standardLubinTateBaseUniformizerUnit_coe _root_.LubinTate.standardLubinTateChangedUniformizerUnit_coe _root_.LubinTate.standardLubinTateLevelGenerator_coe _root_.LubinTate.standardLubinTatePolynomialIterateOverSeparableClosure_eval _root_.LubinTate.standardLubinTatePolynomialIterate_derivative_eval_zero _root_.LubinTate.standardLubinTatePolynomialIterate_eval_zero _root_.LubinTate.standardLubinTatePolynomialIterate_zero _root_.LubinTate.standardLubinTatePolynomial_derivative_eval_zero _root_.LubinTate.standardLubinTatePolynomial_eval _root_.LubinTate.standardLubinTatePolynomial_toPowerSeries _root_.LubinTate.standardLubinTatePolynomial_toPowerSeries_eq_series _root_.LubinTate.standardLubinTatePrimitivePointInteger_coe _root_.LubinTate.standardLubinTatePrimitivePolynomialOverField_coeff_zero _root_.LubinTate.standardLubinTatePrimitivePolynomial_coeff_zero _root_.LubinTate.standardLubinTateUnitFactorFieldUnit_coe _root_.OAI.PrimeDegreePackets.ThetaConstruction.schwartzCM_apply _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteResidueActionOfHenselianDVF_apply _root_.RamificationTheory.HilbertRamification.Higher.dvfValuationSubringUnitAut_apply _root_.RamificationTheory.HilbertRamification.Higher.lowerRamificationGroup_neg_one _root_.RamificationTheory.HilbertRamification.Higher.mem_dvfHigherPrincipalUnitGroup_iff _root_.RamificationTheory.HilbertRamification.Higher.mem_lowerRamificationGroup_iff _root_.RamificationTheory.HilbertRamification.Higher.mem_valuationSubringDisplacementSubalgebraOfUniqueExtension_iff _root_.RamificationTheory.HilbertRamification.Higher.realRamificationIdeal_nat _root_.RamificationTheory.HilbertRamification.Higher.realRamificationIdeal_neg_one _root_.RamificationTheory.HilbertRamification.Higher.valuationSubringAutOfUniqueExtension_apply_coe _root_.RamificationTheory.HilbertRamification.Higher.valuationSubringAutOfUniqueExtension_apply_inv_apply _root_.RamificationTheory.HilbertRamification.Higher.valuationSubringAutOfUniqueExtension_mul_apply _root_.RamificationTheory.HilbertRamification.Higher.valuationSubringAutOfUniqueExtension_one_apply _root_.infinitePlace_mult_smul
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


/-- The valuation-theoretic ramification index used by the local field
formula agrees with the extension ramification index. -/
theorem ramificationIndexOfWithZeroValuation_eq_extensionRamificationIndex
    {E : Type*} [Field E]
    (ν : Valuation E (WithZero (Multiplicative ℤ)))
    [ValuationTheory.DiscreteValuationField.Valuation.IsCompleteDiscrete ν]
    [Finite
      (IsLocalRing.ResidueField ν.valuationSubring)]
    [CharZero E]
    (hν : Function.Surjective ν) :
    let F :=
      LocalFieldTheory.DiscreteValuationField.LocalField.ofWithZeroValuation
        ν
    letI :
        LocalFieldTheory.DiscreteValuationField.LocalField.MixedQPadicContext
          F :=
      LocalFieldTheory.DiscreteValuationField.LocalField.mixedQPadicContext
        F
    LocalFieldTheory.DiscreteValuationField.LocalField.ramificationIndexOfWithZeroValuation
        ν =
      ValuationTheory.DiscreteValuationField.ValuedExtension.ramificationIndex
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
  let : Fact p.Prime :=
    ⟨F.residueCharacteristic_prime⟩
  let base :=
    LocalFieldTheory.DiscreteValuationField.Examples.Qp.padicCompleteDVF p
  let target := F.toCompleteDVF
  let :
      (LocalFieldTheory.DiscreteValuationField.Examples.Qp.padicDVRValuation p).IsRankOneDiscrete :=
    (LocalFieldTheory.DiscreteValuationField.Examples.Qp.padicCompleteDVF p).instCompleteDiscrete.isRankOneDiscrete
  let ϖ : base.valuationSubring :=
    LocalFieldTheory.DiscreteValuationField.Examples.Qp.padicIntEquivValuationSubring
      p (p : ℤ_[p])
  have hϖval :
      base.valuation (ϖ : ℚ_[p]) =
        WithZero.exp (-1 : ℤ) := by
    dsimp [base, ϖ]
    exact LocalFieldTheory.Padic.padicDVR_valuation_p p
  have hϖ :
      base.valuation.IsUniformizer
        (ϖ : ℚ_[p]) := by
    dsimp [base, ϖ] at hϖval ⊢
    exact
      LocalFieldTheory.DiscreteValuationField.WithZeroValuation.isUniformizer_of_valuation_eq_exp_neg_one
        (LocalFieldTheory.DiscreteValuationField.Examples.Qp.padicDVRValuation p)
        ((LocalFieldTheory.DiscreteValuationField.Examples.Qp.padicIntEquivValuationSubring
          p (p : ℤ_[p]) :
            (LocalFieldTheory.DiscreteValuationField.Examples.Qp.padicCompleteDVF
              p).valuationSubring) : ℚ_[p])
        hϖval
  obtain ⟨π, hπval⟩ :=
    LocalFieldTheory.DiscreteValuationField.WithZeroValuation.exists_valuationSubring_valuation_eq_exp_neg_one_of_surjective
      ν hν
  have hπ :
      target.valuation.IsUniformizer (π : E) :=
    LocalFieldTheory.DiscreteValuationField.WithZeroValuation.isUniformizer_of_valuation_eq_exp_neg_one
      ν (π : E) hπval
  obtain ⟨u, hu⟩ :=
    LocalFieldTheory.DiscreteValuationField.ValuedExtension.exists_unit_mul_target_uniformizer_pow_eq_base_uniformizer_image
      base target hϖ hπ
  have huval :
      ν ((u : target.valuationSubring) : E) = 1 := by
    change
      ν (algebraMap target.valuationSubring E
        (u : target.valuationSubring)) = 1
    exact
      (Valuation.Integers.isUnit_iff_valuation_eq_one
        (Valuation.integer.integers ν)
        (x := (u : target.valuationSubring))).mp
        u.isUnit
  have hfield :
      ((ValuationTheory.DiscreteValuationField.ValuedExtension.integerMap
          base.toDVF target.toDVF ϖ :
            target.valuationSubring) : E) =
        ((u : target.valuationSubring) : E) *
          (π : E) ^
            ValuationTheory.DiscreteValuationField.ValuedExtension.ramificationIndex
              base.toDVF target.toDVF :=
    congrArg Subtype.val hu
  have hval := congrArg ν hfield
  have hpval :
      ν (p : E) =
        WithZero.exp
          (-(ValuationTheory.DiscreteValuationField.ValuedExtension.ramificationIndex
            base.toDVF target.toDVF : ℤ)) := by
    rw [ν.map_mul, ν.map_pow, huval, hπval,
      one_mul] at hval
    calc
      ν (p : E) =
          WithZero.exp (-1 : ℤ) ^
            ValuationTheory.DiscreteValuationField.ValuedExtension.ramificationIndex
              base.toDVF target.toDVF := by
        have himage :
            ((ValuationTheory.DiscreteValuationField.ValuedExtension.integerMap
                base.toDVF target.toDVF ϖ : target.valuationSubring) : E) =
              (p : E) := by
          change algebraMap ℚ_[p] E (p : ℚ_[p]) = (p : E)
          exact map_natCast _ _
        exact (congrArg ν himage).symm.trans hval
      _ =
          WithZero.exp
            (ValuationTheory.DiscreteValuationField.ValuedExtension.ramificationIndex
              base.toDVF target.toDVF •
                (-1 : ℤ)) :=
        (WithZero.exp_nsmul _ _).symm
      _ =
          WithZero.exp
            (-(ValuationTheory.DiscreteValuationField.ValuedExtension.ramificationIndex
              base.toDVF target.toDVF : ℤ)) := by
        congr 1
        simp
  have hcustom :=
    LocalFieldTheory.DiscreteValuationField.LocalField.valuation_residueCharacteristic_eq_exp_neg_ramificationIndex
      ν
  have hexp :
      WithZero.exp
          (-(LocalFieldTheory.DiscreteValuationField.LocalField.ramificationIndexOfWithZeroValuation
            ν : ℤ)) =
        WithZero.exp
          (-(ValuationTheory.DiscreteValuationField.ValuedExtension.ramificationIndex
            base.toDVF target.toDVF : ℤ)) :=
    hcustom.symm.trans
      (by
        simpa [F, p] using hpval)
  have hint :
      -(LocalFieldTheory.DiscreteValuationField.LocalField.ramificationIndexOfWithZeroValuation
          ν : ℤ) =
        -(ValuationTheory.DiscreteValuationField.ValuedExtension.ramificationIndex
          base.toDVF target.toDVF : ℤ) :=
    WithZero.exp_injective hexp
  exact_mod_cast neg_injective hint

/-- Degree over `ℚ_p` is ramification index times residue degree. -/
theorem finrank_qp_eq_ramificationIndex_mul_residueDegree
    {E : Type*} [Field E]
    (ν : Valuation E (WithZero (Multiplicative ℤ)))
    [ValuationTheory.DiscreteValuationField.Valuation.IsCompleteDiscrete ν]
    [Finite
      (IsLocalRing.ResidueField ν.valuationSubring)]
    [CharZero E]
    (hν : Function.Surjective ν) :
    let F :=
      LocalFieldTheory.DiscreteValuationField.LocalField.ofWithZeroValuation
        ν
    letI :
        LocalFieldTheory.DiscreteValuationField.LocalField.MixedQPadicContext
          F :=
      LocalFieldTheory.DiscreteValuationField.LocalField.mixedQPadicContext
        F
    Module.finrank ℚ_[F.residueCharacteristic] E =
      LocalFieldTheory.DiscreteValuationField.LocalField.ramificationIndexOfWithZeroValuation
          ν *
        ValuationTheory.DiscreteValuationField.ValuedExtension.residueDegree
          (LocalFieldTheory.DiscreteValuationField.Examples.Qp.padicCompleteDVF
            F.residueCharacteristic).toDVF
          F.toCompleteDVF.toDVF := by
  let F :=
    LocalFieldTheory.DiscreteValuationField.LocalField.ofWithZeroValuation
      ν
  let :
      LocalFieldTheory.DiscreteValuationField.LocalField.MixedQPadicContext
        F :=
    LocalFieldTheory.DiscreteValuationField.LocalField.mixedQPadicContext
      F
  let base :=
    LocalFieldTheory.DiscreteValuationField.Examples.Qp.padicCompleteDVF
      F.residueCharacteristic
  let target := F.toCompleteDVF
  rw [
    ramificationIndexOfWithZeroValuation_eq_extensionRamificationIndex
      ν hν]
  exact
    LocalFieldTheory.DiscreteValuationField.ValuedExtension.degree_eq_ramificationIndex_mul_residueDegree_of_finite_separable
      base target


end GlobalClassFieldTheory.ClassFieldAxiom
end
end

section
-- module Solutions.OAIQ244_DUKE.GlobalClassFieldTheory_ClassFieldAxiom_IdeleClassPowerLocalUnitQuotient_FinitePlacePowerIndex
attribute [-instance] _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalClassFieldTheory.localDecompositionResidueFinite _root_.OAI.PrimeDegreePackets.boundedRealFields_finite _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_finite_residue _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionResidueField.instField _root_.RamificationTheory.HilbertRamification.ValuationSubring.selectedResidueField.instAlgebra _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.LocalClassFieldTheory.normalizationIntegerRingIsIntegralClosure _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.chosenFinitePlaceBaseValued _root_.chosenFinitePlaceCompletionAlgebra _root_.chosenFinitePlaceLocalizedValuationHasExtension _root_.relativeAdeleRingIntermediateAlgebra _root_.relativeAdeleRingTopIntermediateAlgebra
attribute [-simp] _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.IsDiscreteValuationRing.addVal_ringEquiv _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.LocalFieldTheory.residueField_algebraMap_residue _root_.LubinTate.LubinTateSeries.standardLubinTateSeries_toPowerSeries _root_.LubinTate.SameUniformizer.coeff_recursiveIntertwiner _root_.LubinTate.SameUniformizer.constantCoeff_inVariable _root_.LubinTate.SameUniformizer.intertwinerApproximation_zero _root_.LubinTate.SameUniformizer.standardLubinTateEndomorphism_coeff_one _root_.LubinTate.standardLubinTateBaseUniformizerUnit_coe _root_.LubinTate.standardLubinTateChangedUniformizerUnit_coe _root_.LubinTate.standardLubinTateLevelGenerator_coe _root_.LubinTate.standardLubinTatePolynomialIterateOverSeparableClosure_eval _root_.LubinTate.standardLubinTatePolynomialIterate_derivative_eval_zero _root_.LubinTate.standardLubinTatePolynomialIterate_eval_zero _root_.LubinTate.standardLubinTatePolynomialIterate_zero _root_.LubinTate.standardLubinTatePolynomial_derivative_eval_zero _root_.LubinTate.standardLubinTatePolynomial_eval _root_.LubinTate.standardLubinTatePolynomial_toPowerSeries _root_.LubinTate.standardLubinTatePolynomial_toPowerSeries_eq_series _root_.LubinTate.standardLubinTatePrimitivePointInteger_coe _root_.LubinTate.standardLubinTatePrimitivePolynomialOverField_coeff_zero _root_.LubinTate.standardLubinTatePrimitivePolynomial_coeff_zero _root_.LubinTate.standardLubinTateUnitFactorFieldUnit_coe _root_.OAI.PrimeDegreePackets.ThetaConstruction.schwartzCM_apply _root_.infinitePlace_mult_smul
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

/-!
# Finite-place power indices

This file supplies the completion instances and local cardinality formulas used
to evaluate finite-place factors in idele power quotients.
-/

open scoped NumberField Classical NNReal ValuativeRel TensorProduct
open NumberField IsDedekindDomain

noncomputable section

namespace GlobalClassFieldTheory.ClassFieldAxiom

variable {K : Type} [Field K] [NumberField K]

/-- The residue-characteristic contribution in the finite local
power-index formula.  Keeping this contribution as a named natural
number makes the subsequent product-formula calculation visible. -/
noncomputable def finitePlaceNthPowerDefect
    (n : ℕ+)
    (v₀ : HeightOneSpectrum (𝓞 K)) : ℕ :=
  let ν :
      Valuation (v₀.adicCompletion K)
        (WithZero (Multiplicative ℤ)) :=
    Valued.v
  let F :=
    LocalFieldTheory.DiscreteValuationField.LocalField.ofWithZeroValuation ν
  letI :
      LocalFieldTheory.DiscreteValuationField.LocalField.MixedWithZeroValuationContext
        ν :=
    LocalFieldTheory.DiscreteValuationField.LocalField.mixedWithZeroValuationContext ν
  letI :
      Valued (v₀.adicCompletion K)
        (WithZero (Multiplicative ℤ)) :=
    Valued.mk' ν
  let d :=
    Module.finrank ℚ_[F.residueCharacteristic]
      (v₀.adicCompletion K)
  F.residueCharacteristic ^
    (d * padicValNat F.residueCharacteristic (n : ℕ))

/-- The local defect is the norm of the exact prime-power factor of
the principal ideal `(n)` at `v`. -/
theorem finitePlaceNthPowerDefect_eq_absNorm_maxPowDividing
    (n : ℕ+)
    (v : HeightOneSpectrum (𝓞 K)) :
    finitePlaceNthPowerDefect (K := K) n v =
      Ideal.absNorm
        (v.maxPowDividing
          (Ideal.span {((n : ℕ) : 𝓞 K)})) := by
  let ν :
      Valuation
        (v.adicCompletion K)
        (WithZero (Multiplicative ℤ)) :=
    Valued.v
  let F :=
    LocalFieldTheory.DiscreteValuationField.LocalField.ofWithZeroValuation
      ν
  let :
      LocalFieldTheory.DiscreteValuationField.LocalField.MixedWithZeroValuationContext
        ν :=
    LocalFieldTheory.DiscreteValuationField.LocalField.mixedWithZeroValuationContext
      ν
  let :
      Valued
        (v.adicCompletion K)
        (WithZero (Multiplicative ℤ)) :=
    Valued.mk' ν
  let p := F.residueCharacteristic
  let d :=
    Module.finrank ℚ_[p] (v.adicCompletion K)
  let e :=
    LocalFieldTheory.DiscreteValuationField.LocalField.ramificationIndexOfWithZeroValuation
      ν
  let f :=
    ValuationTheory.DiscreteValuationField.ValuedExtension.residueDegree
      (LocalFieldTheory.DiscreteValuationField.Examples.Qp.padicCompleteDVF p).toDVF
      F.toCompleteDVF.toDVF
  let k := padicValNat p (n : ℕ)
  let x : 𝓞 K := ((n : ℕ) : 𝓞 K)
  have hx : x ≠ 0 := by
    exact Nat.cast_ne_zero.mpr n.ne_zero
  have hI :
      Ideal.span {x} ≠ 0 :=
    Submodule.span_singleton_eq_bot.mp.mt hx
  have hd : d = e * f := by
    simpa [F, p, d, e, f] using
      finrank_qp_eq_ramificationIndex_mul_residueDegree
        ν (v.valuedAdicCompletion_surjective K)
  have hq : Ideal.absNorm v.asIdeal = p ^ f := by
    simpa [ν, F, p, f] using
      absNorm_eq_residueCharacteristic_pow_residueDegree
        (K := K) v
  have hcomp :
      ν ((n : ℕ) : v.adicCompletion K) =
        WithZero.exp
          (-((e : ℤ) * (k : ℤ))) := by
    simpa [F, e, k] using
      LocalFieldTheory.DiscreteValuationField.LocalField.valuation_natCast_eq_exp_neg_ramificationIndex_mul_padicValNat
        ν (n : ℕ) n.ne_zero
  have hval :
      v.intValuation x =
        WithZero.exp
          (-((e : ℤ) * (k : ℤ))) := by
    calc
      v.intValuation x =
          v.valuation K x :=
        (v.valuation_of_algebraMap
          (K := K) x).symm
      _ =
          Valued.v
            (x : v.adicCompletion K) :=
        (HeightOneSpectrum.valuedAdicCompletion_eq_valuation
          (v := v) x).symm
      _ =
          ν ((n : ℕ) : v.adicCompletion K) := by
        apply congrArg ν
        change
          algebraMap K (v.adicCompletion K) (x : K) =
            ((n : ℕ) : v.adicCompletion K)
        simp [x]
      _ = _ := hcomp
  have hexp :
      WithZero.exp
          (-(multiplicity v.asIdeal
            (Ideal.span {x}) : ℤ)) =
        WithZero.exp
          (-((e : ℤ) * (k : ℤ))) := by
    rw [← v.intValuation_eq_exp_neg_multiplicity hx]
    exact hval
  have hmult :
      multiplicity v.asIdeal
          (Ideal.span {x}) =
        e * k := by
    exact_mod_cast
      neg_injective
        (WithZero.exp_injective hexp)
  change
    p ^ (d * k) =
      Ideal.absNorm
        (v.maxPowDividing
          (Ideal.span {x}))
  calc
    p ^ (d * k) =
        p ^ ((e * f) * k) := by
      rw [hd]
    _ = p ^ (f * (e * k)) := by
      congr 1
      ac_rfl
    _ = (p ^ f) ^ (e * k) := by
      rw [pow_mul]
    _ =
        Ideal.absNorm v.asIdeal ^ (e * k) := by
      rw [hq]
    _ =
        Ideal.absNorm
          (v.asIdeal ^ (e * k)) := by
      rw [map_pow]
    _ =
        Ideal.absNorm
          (v.maxPowDividing
            (Ideal.span {x})) := by
      rw [
        HeightOneSpectrum.maxPowDividing_eq_pow_multiplicity
          hI,
        hmult]


end GlobalClassFieldTheory.ClassFieldAxiom
end
end

section
-- module Solutions.OAIQ244_DUKE.GlobalClassFieldTheory_ClassFieldAxiom_IdeleClassPowerLocalUnitQuotient_SupportedIdeleIndex
attribute [-instance] _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.LocalClassFieldTheory.normalizationIntegerRingIsIntegralClosure _root_.chosenFinitePlaceCompletionAlgebra
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

/-!
# Supported idele power quotient

This file expresses the supported idele quotient as the product of its local
archimedean and finite-place power indices and evaluates its cardinality.
-/

open scoped NumberField Classical NNReal ValuativeRel TensorProduct
open NumberField IsDedekindDomain
open AlgebraicNumberTheory.Valuations
open KummerTheory
open LocalFieldTheory
open LocalFieldTheory.IsNonarchimedeanLocalField

noncomputable section

namespace GlobalClassFieldTheory.ClassFieldAxiom

variable {K : Type} [Field K] [NumberField K]

/-- Product of the actual finite-place power defects. -/
theorem prod_finitePlaceNthPowerDefect
    (n : ℕ+)
    (S : Finset (HeightOneSpectrum (𝓞 K)))
    (hS :
      ∀ v : HeightOneSpectrum (𝓞 K),
        v.asIdeal ∣
            Ideal.span {((n : ℕ) : 𝓞 K)} →
          v ∈ S) :
    (∏ v : ↥S,
        finitePlaceNthPowerDefect
          (K := K) n v.1) =
      (n : ℕ) ^ Module.finrank ℚ K := by
  calc
    (∏ v : ↥S,
        finitePlaceNthPowerDefect
          (K := K) n v.1) =
        ∏ v : ↥S,
          Ideal.absNorm
            (v.1.maxPowDividing
              (Ideal.span
                {((n : ℕ) : 𝓞 K)})) := by
      apply Finset.prod_congr rfl
      intro v _
      exact
        finitePlaceNthPowerDefect_eq_absNorm_maxPowDividing
          (K := K) n v.1
    _ = _ :=
      prod_absNorm_maxPowDividing_natCast
        (K := K) n S hS


end GlobalClassFieldTheory.ClassFieldAxiom
end
end

section
-- module Solutions.OAIQ244_DUKE.KummerTheory_Concrete_SUnitPreparation_FiniteRadicalSupport
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.residueFieldZModAlgebra _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedIntegralAlgebraContextValuationSubringAlgebra _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedQPadicContextValuationSubringTower _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LubinTate.compatibleGroupFamiliesGroup _root_.OAI.PrimeDegreePackets.diagonalLogAction _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionResidueField.instField _root_.RamificationTheory.HilbertRamification.ValuationSubring.selectedResidueField.instAlgebra _root_.ValuationTheory.DiscreteValuationField.DVF.maximalIdealPowSuccQuotModule _root_.ValuationTheory.DiscreteValuationField.DVF.residueField.field _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.isDomain _root_.CyclicCohomology.binaryCoefficientFamilyCommGroup _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.LocalClassFieldTheory.normalizationIntegerRingIsIntegralClosure _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.chosenFinitePlaceBaseValued _root_.chosenFinitePlaceCompletionAlgebra
attribute [-simp] _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.IsDiscreteValuationRing.addVal_ringEquiv _root_.OAI.PrimeDegreePackets.ThetaConstruction.schwartzCM_apply _root_.finiteIdeleOfSPlaceFactors_apply_mem _root_.finiteIdeleOfSPlaceFactors_apply_notMem _root_.ideleSupportedAtEquivSPlaceFactors_infinite _root_.ideleSupportedAtEquivSPlaceFactors_inside _root_.ideleSupportedAtEquivSPlaceFactors_outside_coe _root_.infinitePlace_mult_smul _root_.principalLocalNormQuotientMap_apply _root_.sUnit_smul_coe
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

/-- A global unit is an `S`-unit for its chosen finite support. -/
theorem mem_sUnitGroup_chosenUnitFiniteSupport (x : Kˣ) :
    x ∈ SUnitGroup (K := K) (chosenUnitFiniteSupport (K := K) x) := by
  rw [mem_SUnitGroup_iff]
  intro v hv
  have hsupported :=
    Classical.choose_spec
      (IdeleGroup.exists_finset_supportedAt
        (IdeleGroup.principalIdele K x))
  have hunit :=
    (IdeleGroup.mem_supportedAt_iff
      (K := K)
      (chosenUnitFiniteSupport (K := K) x : Set _)
      (IdeleGroup.principalIdele K x)).mp hsupported v
      (by simpa using hv)
  rw [
    HeightOneSpectrum.adicCompletionIntegers.mem_units_iff_valued_eq_one]
      at hunit
  change
    Valued.v
        (((IdeleGroup.finiteComponent v
          (IdeleGroup.principalIdele K x) :
            (v.adicCompletion K)ˣ) :
          v.adicCompletion K)) = 1 at hunit
  rw [IdeleGroup.finiteComponent_principalIdele,
    HeightOneSpectrum.valuedAdicCompletion_eq_valuation'] at hunit
  exact hunit

/-- Each chosen radical representative is an `S`-unit after the chosen
finite enlargement. -/
theorem chosenFiniteKummerRadicalRepresentative_mem_enlargedSUnitGroup
    {L : Type*} [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    (n : ℕ+)
    (hmu : (primitiveRoots (n : ℕ) K).Nonempty)
    (S : Finset (HeightOneSpectrum (𝓞 K)))
    (q :
      (KummerTheory.chosenFiniteKummerRadicalDatum
        (K := K) (L := L) n).RadicalQuotient) :
    (chosenFiniteKummerRadicalRepresentative
        (K := K) (L := L) n q).1 ∈
      SUnitGroup (K := K)
        (enlargeByFiniteKummerRadicalSupport
          (K := K) (L := L) n hmu S) := by
  apply sUnitGroup_mono
    (K := K)
    (S := chosenUnitFiniteSupport (K := K)
      (chosenFiniteKummerRadicalRepresentative
        (K := K) (L := L) n q).1)
    (T := enlargeByFiniteKummerRadicalSupport
      (K := K) (L := L) n hmu S)
  · intro v hv
    apply Finset.mem_union_right
    let D :=
      KummerTheory.chosenFiniteKummerRadicalDatum
        (K := K) (L := L) n
    let : Finite D.RadicalQuotient :=
      finite_chosenFiniteKummerRadicalQuotient
        (K := K) (L := L) n hmu
    let : Fintype D.RadicalQuotient :=
      Fintype.ofFinite D.RadicalQuotient
    exact Finset.mem_biUnion.mpr
      ⟨q, Finset.mem_univ q, hv⟩
  · exact mem_sUnitGroup_chosenUnitFiniteSupport
      (K := K)
      (chosenFiniteKummerRadicalRepresentative
        (K := K) (L := L) n q).1

/-- After the chosen finite enlargement, the actual radical of `L/K`
is generated by its `S`-unit part and the ambient `n`-th powers. -/
theorem finiteKummerRadicalSubgroup_le_enlargedSUnitKummerSubgroup
    {L : Type*} [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    (n : ℕ+)
    (hmu : (primitiveRoots (n : ℕ) K).Nonempty)
    (S : Finset (HeightOneSpectrum (𝓞 K))) :
    KummerTheory.finiteKummerRadicalSubgroup
        (K := K) (L := L) n ≤
      (sUnitKummerSubgroup
        (K := K) (L := L) n
        (enlargeByFiniteKummerRadicalSupport
          (K := K) (L := L) n hmu S)).1 := by
  intro a ha
  let D :=
    KummerTheory.chosenFiniteKummerRadicalDatum
      (K := K) (L := L) n
  let aD : D.carrier := ⟨a, ha⟩
  let q : D.RadicalQuotient := D.radicalQuotientMk aD
  let bD : D.carrier :=
    chosenFiniteKummerRadicalRepresentative
      (K := K) (L := L) n q
  have hbclass : D.radicalQuotientMk bD =
      D.radicalQuotientMk aD := by
    exact chosenFiniteKummerRadicalRepresentative_spec
      (K := K) (L := L) n q
  have habpower : aD / bD ∈ D.ambientNthPowersSubgroup := by
    exact (D.radicalQuotientMk_eq_iff aD bD).1 hbclass.symm
  obtain ⟨z, hz⟩ :=
    (D.mem_ambientNthPowersSubgroup_iff).1 habpower
  apply Subgroup.mem_sup.mpr
  refine
    ⟨bD.1,
      ⟨chosenFiniteKummerRadicalRepresentative_mem_enlargedSUnitGroup
          (K := K) (L := L) n hmu S q,
        bD.2⟩,
      z ^ (n : ℕ),
      (KummerTheory.mem_unitNthPowersSubgroup_iff n).2
        ⟨z, rfl⟩,
      ?_⟩
  change bD.1 * z ^ (n : ℕ) = aD.1
  rw [hz]
  change bD.1 * (aD.1 / bD.1) = aD.1
  simp [div_eq_mul_inv, mul_comm, mul_left_comm]

/-- Exact radical identification after the chosen finite enlargement. -/
theorem enlargedSUnitKummerSubgroup_eq_finiteKummerRadicalSubgroup
    {L : Type*} [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    (n : ℕ+)
    (hmu : (primitiveRoots (n : ℕ) K).Nonempty)
    (S : Finset (HeightOneSpectrum (𝓞 K))) :
    (sUnitKummerSubgroup
        (K := K) (L := L) n
        (enlargeByFiniteKummerRadicalSupport
          (K := K) (L := L) n hmu S)).1 =
      KummerTheory.finiteKummerRadicalSubgroup
        (K := K) (L := L) n :=
  le_antisymm
    (sUnitKummerSubgroup_le_finiteKummerRadicalSubgroup
      (K := K) (L := L) n
      (enlargeByFiniteKummerRadicalSupport
        (K := K) (L := L) n hmu S))
    (finiteKummerRadicalSubgroup_le_enlargedSUnitKummerSubgroup
      (K := K) (L := L) n hmu S)

/-- Kummer generation of an abelian exponent-`n` extension from the
`S`-unit radical supplied by the chosen finite enlargement. -/
theorem kummerRadicalExtension_enlargedSUnitKummerSubgroup_eq
    {Omega : Type*} [Field Omega] [Algebra K Omega]
    [IsSepClosure K Omega]
    (E : IntermediateField K Omega)
    [FiniteDimensional K E] [IsGalois K E]
    [IsMulCommutative Gal(E/K)]
    (n : ℕ+)
    (hmu : (primitiveRoots (n : ℕ) K).Nonempty)
    (hexponent : ∀ sigma : Gal(E/K), sigma ^ (n : ℕ) = 1)
    (S : Finset (HeightOneSpectrum (𝓞 K))) :
    KummerTheory.kummerRadicalExtension
        (K := K) (Omega := Omega) n
        (sUnitKummerSubgroup
          (K := K) (L := E) n
          (enlargeByFiniteKummerRadicalSupport
            (K := K) (L := E) n hmu S)).1 =
      E := by
  rw [
    enlargedSUnitKummerSubgroup_eq_finiteKummerRadicalSubgroup
      (K := K) (L := E) n hmu S]
  exact
    KummerTheory.kummerRadicalExtension_finiteKummerRadicalSubgroup_eq
      E n hmu hexponent

end KummerTheory
end
end

section
-- module Solutions.OAIQ244_DUKE.KummerTheory_Concrete_SUnitPreparation_EnlargedSUnitRestriction
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.KummerTheory.primeCyclotomicBaseIsGalois _root_.LocalClassFieldTheory.localDecompositionResidueFinite _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitQuotientCarrier_finite _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.residueFieldZModAlgebra _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedIntegralAlgebraContextValuationSubringAlgebra _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedQPadicContextValuationSubringTower _root_.LocalFieldTheory.DiscreteValuationField.finite_nsmulAddKernel_padicInt_pi _root_.LocalFieldTheory.DiscreteValuationField.finite_principalUnits_nthPowerKernel _root_.LocalFieldTheory.DiscreteValuationField.finite_residueRootsOfUnityGroup _root_.LocalFieldTheory.DiscreteValuationField.finite_valuationSubringUnits_nthPowerKernel _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LubinTate.compatibleGroupFamiliesGroup _root_.OAI.PrimeDegreePackets.boundedRealFields_finite _root_.OAI.PrimeDegreePackets.diagonalLogAction _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionResidueExtension_normal _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionResidueField.instField _root_.RamificationTheory.HilbertRamification.ValuationSubring.selectedResidueField.instAlgebra _root_.ValuationTheory.DiscreteValuationField.DVF.maximalIdealPowSuccQuotModule _root_.ValuationTheory.DiscreteValuationField.DVF.residueField.field _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.isDomain _root_.CyclicCohomology.binaryCoefficientFamilyCommGroup _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.LocalClassFieldTheory.normalizationIntegerRingIsIntegralClosure _root_.RamificationTheory.HilbertRamification.CompleteDVF.decompositionGroupMulSemiringAction _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.chosenFinitePlaceCompletionAlgebra _root_.chosenFinitePlaceLocalizedIntegerAlgebra _root_.chosenFinitePlaceLocalizedIsGalois
attribute [-simp] _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.IsDiscreteValuationRing.addVal_ringEquiv _root_.OAI.PrimeDegreePackets.ThetaConstruction.schwartzCM_apply _root_.infinitePlace_mult_smul
set_option synthInstance.maxHeartbeats 400000
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

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

/-- The actual field containment `L ≤ N` for finite S-unit preparation, after producing
the required finite enlargement of `S`. -/
theorem le_fullSUnitKummerExtension_of_enlargedS
    {Omega : Type*} [Field Omega] [Algebra K Omega]
    [IsSepClosure K Omega]
    (E : IntermediateField K Omega)
    [FiniteDimensional K E] [IsGalois K E]
    [IsMulCommutative Gal(E/K)]
    (n : ℕ+)
    (hmu : (primitiveRoots (n : ℕ) K).Nonempty)
    (hexponent : ∀ sigma : Gal(E/K), sigma ^ (n : ℕ) = 1)
    (S : Finset (HeightOneSpectrum (𝓞 K))) :
    E ≤
      fullSUnitKummerExtension
        (K := K) (Omega := Omega) n
        (enlargeByFiniteKummerRadicalSupport
          (K := K) (L := E) n hmu S) := by
  have hgenerate :=
    kummerRadicalExtension_enlargedSUnitKummerSubgroup_eq
      (K := K) (Omega := Omega) E n hmu hexponent S
  have hmono := kummerRadicalExtension_mono
    (K := K) (Omega := Omega) n
    (sUnitKummerSubgroup_le_fullSUnitKummerSubgroup
      (K := K) (L := E) n
      (enlargeByFiniteKummerRadicalSupport
        (K := K) (L := E) n hmu S))
  intro x hx
  apply hmono
  rw [hgenerate]
  exact hx

/-- The actual inclusion algebra `E → N` supplied by the source-produced
containment above. -/
@[reducible]
noncomputable def enlargedSUnitKummerAlgebra
    {Omega : Type*} [Field Omega] [Algebra K Omega]
    [IsSepClosure K Omega]
    (E : IntermediateField K Omega)
    [FiniteDimensional K E] [IsGalois K E]
    [IsMulCommutative Gal(E/K)]
    (n : ℕ+)
    (hmu : (primitiveRoots (n : ℕ) K).Nonempty)
    (hexponent : ∀ sigma : Gal(E/K), sigma ^ (n : ℕ) = 1)
    (S : Finset (HeightOneSpectrum (𝓞 K))) :
    Algebra E
      (fullSUnitKummerExtension
        (K := K) (Omega := Omega) n
        (enlargeByFiniteKummerRadicalSupport
          (K := K) (L := E) n hmu S)) :=
  (IntermediateField.inclusion
    (le_fullSUnitKummerExtension_of_enlargedS
      (K := K) (Omega := Omega) E n hmu hexponent S)).toAlgebra

/-- Restriction from the full `S`-unit Kummer extension `N` to the actual
extension `E ≤ N` produced above. -/
noncomputable def enlargedSUnitKummerRestrictionHom
    {Omega : Type*} [Field Omega] [Algebra K Omega]
    [IsSepClosure K Omega]
    (E : IntermediateField K Omega)
    [FiniteDimensional K E] [IsGalois K E]
    [IsMulCommutative Gal(E/K)]
    (n : ℕ+)
    (hmu : (primitiveRoots (n : ℕ) K).Nonempty)
    (hexponent : ∀ sigma : Gal(E/K), sigma ^ (n : ℕ) = 1)
    (S : Finset (HeightOneSpectrum (𝓞 K))) :
    Gal(fullSUnitKummerExtension
          (K := K) (Omega := Omega) n
          (enlargeByFiniteKummerRadicalSupport
            (K := K) (L := E) n hmu S)/K) →*
      Gal(E/K) := by
  let N :=
    fullSUnitKummerExtension
      (K := K) (Omega := Omega) n
      (enlargeByFiniteKummerRadicalSupport
        (K := K) (L := E) n hmu S)
  let : Algebra E N :=
    enlargedSUnitKummerAlgebra
      (K := K) (Omega := Omega) E n hmu hexponent S
  letI : IsScalarTower K E N := by infer_instance
  exact
    AlgEquiv.restrictNormalHom
      (F := K) (K₁ := N) (E := E)

/-- The restriction map `Gal(N/K) → Gal(E/K)` is onto. -/
theorem enlargedSUnitKummerRestrictionHom_surjective
    {Omega : Type*} [Field Omega] [Algebra K Omega]
    [IsSepClosure K Omega]
    (E : IntermediateField K Omega)
    [FiniteDimensional K E] [IsGalois K E]
    [IsMulCommutative Gal(E/K)]
    (n : ℕ+)
    (hmu : (primitiveRoots (n : ℕ) K).Nonempty)
    (hexponent : ∀ sigma : Gal(E/K), sigma ^ (n : ℕ) = 1)
    (S : Finset (HeightOneSpectrum (𝓞 K))) :
    Function.Surjective
      (enlargedSUnitKummerRestrictionHom
        (K := K) (Omega := Omega) E n hmu hexponent S) := by
  let N :=
    fullSUnitKummerExtension
      (K := K) (Omega := Omega) n
      (enlargeByFiniteKummerRadicalSupport
        (K := K) (L := E) n hmu S)
  let _ : Algebra E N :=
    enlargedSUnitKummerAlgebra
      (K := K) (Omega := Omega) E n hmu hexponent S
  let : IsScalarTower K E N := by infer_instance
  let : IsGalois K N :=
    fullSUnitKummerExtension_isGalois
      (K := K) (Omega := Omega) n
      (enlargeByFiniteKummerRadicalSupport
        (K := K) (L := E) n hmu S)
  simpa [enlargedSUnitKummerRestrictionHom, N] using
    (AlgEquiv.restrictNormalHom_surjective
      (F := K) (K₁ := E) (E := N))

/-- For an element `sigma` of the relative Galois subgroup
`Gal(N/E)`, this is the actual cyclic fixed field
`N_sigma = N ^ ⟨sigma⟩` used in the prime construction of the finite S-unit preparation argument. -/
noncomputable def enlargedSUnitKummerCyclicFixedField
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
    IntermediateField K
      (fullSUnitKummerExtension
        (K := K) (Omega := Omega) n
        (enlargeByFiniteKummerRadicalSupport
          (K := K) (L := E) n hmu S)) :=
  IntermediateField.fixedField
    (Subgroup.zpowers
      (sigma :
        Gal(fullSUnitKummerExtension
          (K := K) (Omega := Omega) n
          (enlargeByFiniteKummerRadicalSupport
            (K := K) (L := E) n hmu S)/K)))

/-- The top Kummer field is Galois over each cyclic fixed field. -/
theorem enlargedSUnitKummerCyclicFixedField_isGalois
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
    IsGalois
      (enlargedSUnitKummerCyclicFixedField
        (K := K) (Omega := Omega) E n hmu
        hexponent S sigma)
      (fullSUnitKummerExtension
        (K := K) (Omega := Omega) n
        (enlargeByFiniteKummerRadicalSupport
          (K := K) (L := E) n hmu S)) := by
  let S' :=
    enlargeByFiniteKummerRadicalSupport
      (K := K) (L := E) n hmu S
  let N :=
    fullSUnitKummerExtension
      (K := K) (Omega := Omega) n S'
  have hnK : ((n : ℕ) : K) ≠ 0 := by
    exact_mod_cast n.ne_zero
  let : IsGalois K N :=
    fullSUnitKummerExtension_isGalois
      (K := K) (Omega := Omega) n S'
  let : Finite Gal(N/K) :=
    finite_fullSUnitKummerExtension_galois
      (K := K) (Omega := Omega) n hnK hmu S'
  change
    IsGalois
      (IntermediateField.fixedField
        (Subgroup.zpowers (sigma : Gal(N/K)))) N
  exact IsGalois.of_fixed_field N _

end KummerTheory
end
end

section
-- module Solutions.OAIQ244_DUKE.GlobalClassFieldTheory_ClassFieldAxiom_SUnitKummerPrimeSelection_RestrictionKernel
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.residueFieldZModAlgebra _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedIntegralAlgebraContextValuationSubringAlgebra _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedQPadicContextValuationSubringTower _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.OAI.PrimeDegreePackets.diagonalLogAction _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionResidueField.instField _root_.RamificationTheory.HilbertRamification.ValuationSubring.selectedResidueField.instAlgebra _root_.ValuationTheory.DiscreteValuationField.DVF.maximalIdealPowSuccQuotModule _root_.ValuationTheory.DiscreteValuationField.DVF.residueField.field _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.isDomain _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.LocalClassFieldTheory.normalizationIntegerRingIsIntegralClosure _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.chosenFinitePlaceCompletionAlgebra
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

/-!
# Restriction kernels of S-unit Kummer extensions

This file specializes the chosen restriction-kernel coordinates of an
enlarged S-unit Kummer extension to coordinate generators, their required
number, and their cyclic fixed fields.
-/

open scoped NumberField Classical IsMulCommutative
open NumberField IsDedekindDomain
open KummerTheory

noncomputable section

namespace GlobalClassFieldTheory.ClassFieldAxiom

section GeneralKummer

variable {K : Type*} [Field K]
    [NumberField K]

/-- The number `s-r` of finite places required to detect the restriction
kernel for the chosen source-produced enlargement of `S`. -/
def sUnitKummerPrimeCount
    {Omega : Type*} [Field Omega] [Algebra K Omega]
    (E : IntermediateField K Omega)
    [FiniteDimensional K E] [IsGalois K E]
    (n : ℕ+)
    (hmu : (primitiveRoots (n : ℕ) K).Nonempty)
    (r : ℕ)
    (S : Finset (HeightOneSpectrum (𝓞 K))) : ℕ :=
  totalPlaceCard (K := K)
      (enlargeByFiniteKummerRadicalSupport
        (K := K) (L := E) n hmu S) - r

end GeneralKummer

end GlobalClassFieldTheory.ClassFieldAxiom
end
end

section
-- module Solutions.OAIQ244_DUKE.GlobalClassFieldTheory_ClassFieldAxiom_SUnitKummerPrimeSelection_BasePlaceSelection
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.residueFieldZModAlgebra _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedIntegralAlgebraContextValuationSubringAlgebra _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedQPadicContextValuationSubringTower _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.OAI.PrimeDegreePackets.diagonalLogAction _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.LocalClassFieldTheory.normalizationIntegerRingIsIntegralClosure
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

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

/-- The finite set avoided in the prime choice: the enlarged support,
all base primes ramified in the full Kummer extension, and the support of
the exponent `n`. -/
noncomputable def sUnitKummerAvoidedBasePlaces
    {Omega : Type} [Field Omega] [Algebra K Omega]
    [IsSepClosure K Omega]
    (E : IntermediateField K Omega)
    [FiniteDimensional K E] [IsGalois K E]
    (n : ℕ+)
    (hmu : (primitiveRoots (n : ℕ) K).Nonempty)
    (S : Finset (HeightOneSpectrum (𝓞 K))) :
    Finset (HeightOneSpectrum (𝓞 K)) := by
  let S' :=
    enlargeByFiniteKummerRadicalSupport
      (K := K) (L := E) n hmu S
  let N :=
    fullSUnitKummerExtension
      (K := K) (Omega := Omega) n S'
  have hnK : ((n : ℕ) : K) ≠ 0 := by
    exact_mod_cast n.ne_zero
  letI : FiniteDimensional K N :=
    fullSUnitKummerExtension_finiteDimensional
      (K := K) (Omega := Omega) n hnK hmu S'
  letI : IsGalois K N :=
    fullSUnitKummerExtension_isGalois
      (K := K) (Omega := Omega) n S'
  letI : NumberField N :=
    NumberField.of_module_finite K N
  exact
    (S' ∪
      _root_.ramifiedBaseFinitePlaces
        (K := K) (L := N)) ∪
      chosenUnitFiniteSupport (K := K)
        (Units.mk0 ((n : ℕ) : K) hnK)

end FinitePlaces

end GlobalClassFieldTheory.ClassFieldAxiom
end
end


