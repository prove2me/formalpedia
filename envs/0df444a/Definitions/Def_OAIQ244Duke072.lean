-- Prove2me | Definitions.Def_OAIQ244Duke072
-- name    : OAIQ244Duke072
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-13T22:52:25.625125+00:00
-- url     : https://prove2.me/theorems/2f5260ca-d147-4899-86a0-132664552ef1
-- title:
--   Definitions bundle OAIQ244Duke072 of the split of OpenAI, Equidistribution of Prime-Degree Torus Packets with Arbitrary Local Type
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.DukePrimeDegree.prime_degree_packet_measure_equidistribution_unconditional` and `OAI.DukePrimeDegree.prime_degree_packet_measures_tendsto_haar_unconditional`, carved from OpenAI's openai/math development (OpenAI, *Equidistribution of Prime-Degree Torus Packets with Arbitrary Local Type*, OpenAI Math Release, September 24, 2026, result family 15, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 78 declarations of OpenAI's Lean: 18 definitions, 11 instances and 49 theorems. The definitions and types are `GlobalClassFieldTheory.Reciprocity.rationalAbsoluteGaloisIdeleClassAction`, `GlobalClassFieldTheory.Reciprocity.rationalIdeleClassDirectLimit`, `GlobalClassFieldTheory.Reciprocity.rationalIdeleClassRepresentation`, `GlobalClassFieldTheory.Reciprocity.rationalIntermediateIdeleClassEquivGaloisFixed`, `GlobalClassFieldTheory.Reciprocity.rationalIntermediateIdeleClassToDirectLimit`, `GlobalClassFieldTheory.Reciprocity.rationalIntermediateIdeleClassToNormalClosure`, `GlobalClassFieldTheory.Reciprocity.rationalNormalClosure`, `GlobalClassFieldTheory.Reciprocity.rationalRelativeIdeleClassToDirectLimit`, `GlobalClassFieldTheory.Reciprocity.rationalRelativeIdeleClassTowerBaseChangeEquiv`, `GlobalClassFieldTheory.Reciprocity.rationalRelativeIdeleClassTransition`, `IdeleClassGroup.normOneNorm`, `IdeleGroup.finitePrimeIdele`, `LocalClassFieldTheory.galoisGroupEquivAbelianizationOfUnramifiedValuation`, `LocalClassFieldTheory.normQuotientToUnramifiedNormQuotient`, `LocalClassFieldTheory.normQuotientUnramifiedValuationEquivZModOfIsIntegralClosure`, `LocalClassFieldTheory.unramifiedLocalArtinMap`, `LocalClassFieldTheory.unramifiedLocalReciprocityIso`, `LocalClassFieldTheory.unramifiedLocalReciprocityIsoToGaloisGroup`.
--
--   **Sources.** They come from these modules of lean/OAI/NumberTheory, in whole or in part: `AlgebraicNumberTheory_Idele_FinitePrime`, `AlgebraicNumberTheory_Idele_NormTopology_ArchimedeanNorm`, `AlgebraicNumberTheory_Idele_NormTopology_FiniteNormArithmetic`, `AlgebraicNumberTheory_Idele_NormTopology_IdeleClassNorm`, `GlobalClassFieldTheory_Reciprocity_IdeleClassDirectLimitAbstractFixedField`, `GlobalClassFieldTheory_Reciprocity_IdeleClassDirectLimitCore`, `GlobalClassFieldTheory_Reciprocity_IdeleClassDirectLimitExtension`, `GlobalClassFieldTheory_Reciprocity_IdeleClassDirectLimitFiniteLevel`, `GlobalClassFieldTheory_Reciprocity_IdeleClassDirectLimitFiniteLevelCore`, `GlobalClassFieldTheory_Reciprocity_IdeleClassDirectLimitFixedPointDescentCore`, `GlobalClassFieldTheory_Reciprocity_IdeleClassDirectLimitFixedPoints`, `GlobalClassFieldTheory_Reciprocity_OnePlaceNormKernel`, `GlobalClassFieldTheory_Reciprocity_RationalCyclotomicFinitePlace`, `LocalClassFieldTheory_Finite_LocalReciprocity_UnramifiedComparison`, `LocalClassFieldTheory_Finite_LocalReciprocity_UnramifiedNormComparison`, `LocalClassFieldTheory_Finite_LocalReciprocity_UnramifiedReciprocity`.
--
--   **Imports.** It imports the bundles `OAIQ244Duke062`, `OAIQ244Duke064`, `OAIQ244Duke065`, `OAIQ244Duke066`, `OAIQ244Duke067` and `OAIQ244Duke068` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ244Duke076`, `OAIQ244Duke078` and `OAIQ244Duke079`.
-- source:
--   OpenAI, Equidistribution of Prime-Degree Torus Packets with Arbitrary Local Type, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 15; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Equidistribution-of-Prime-Degree-Torus-Packets-with-Arbitrary-Local-Type-September-24-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/NumberTheory at commit 7ef5c0c

import Mathlib
import Mathlib.Algebra.Algebra.Basic
import Mathlib.Algebra.Algebra.Pi
import Mathlib.Algebra.Algebra.Tower
import Mathlib.Algebra.BigOperators.Finprod
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Category.ModuleCat.Basic
import Mathlib.Algebra.CharP.Algebra
import Mathlib.Algebra.CharP.Lemmas
import Mathlib.Algebra.CharP.Subring
import Mathlib.Algebra.Colimit.DirectLimit
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
import Mathlib.Data.Nat.GCD.BigOperators
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Rat.Cast.CharZero
import Mathlib.Data.Rat.Lemmas
import Mathlib.Data.Set.Finite.Range
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.ZMod.QuotientGroup
import Mathlib.Data.ZMod.Units
import Mathlib.Dynamics.BirkhoffSum.Basic
import Mathlib.FieldTheory.AbsoluteGaloisGroup
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.FieldTheory.Finite.Extension
import Mathlib.FieldTheory.Finite.GaloisField
import Mathlib.FieldTheory.Galois.Basic
import Mathlib.FieldTheory.Galois.Infinite
import Mathlib.FieldTheory.Galois.IsGaloisGroup
import Mathlib.FieldTheory.Galois.NormalBasis
import Mathlib.FieldTheory.Galois.Notation
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
import Mathlib.GroupTheory.QuotientGroup.Defs
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
import Mathlib.NumberTheory.Cyclotomic.Basic
import Mathlib.NumberTheory.LocalField.Basic
import Mathlib.NumberTheory.NumberField.AdeleRing
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.NumberTheory.NumberField.ClassNumber
import Mathlib.NumberTheory.NumberField.Completion.FinitePlace
import Mathlib.NumberTheory.NumberField.Completion.InfinitePlace
import Mathlib.NumberTheory.NumberField.Completion.LiesOverInstances
import Mathlib.NumberTheory.NumberField.Completion.Ramification
import Mathlib.NumberTheory.NumberField.Cyclotomic.Ideal
import Mathlib.NumberTheory.NumberField.InfinitePlace.Ramification
import Mathlib.NumberTheory.NumberField.ProductFormula
import Mathlib.NumberTheory.NumberField.Units.Basic
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
import Mathlib.RingTheory.RamificationInertia.Inertia
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
import Definitions.Def_OAIQ244Duke062
import Definitions.Def_OAIQ244Duke064
import Definitions.Def_OAIQ244Duke065
import Definitions.Def_OAIQ244Duke066
import Definitions.Def_OAIQ244Duke067
import Definitions.Def_OAIQ244Duke068

section
-- module Solutions.OAIQ244_DUKE.AlgebraicNumberTheory_Idele_FinitePrime
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 400000
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.GlobalClassFields.ConductorialSubgroup.finiteIndex _root_.GlobalClassFieldTheory.GlobalClassFields.bigHilbertClassFieldNormSubgroup_normal _root_.GlobalClassFieldTheory.GlobalClassFields.smallHilbertClassFieldNormSubgroupFiniteIndex _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalClassFieldTheory.finiteGaloisLocalField_integerRing_moduleFinite _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.residueFieldZModAlgebra _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedIntegralAlgebraContextValuationSubringAlgebra _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.LocalClassFieldTheory.comparisonIntegerRingIsIntegralClosure _root_.LocalClassFieldTheory.normalizationIntegerRingIsIntegralClosure _root_.chosenFinitePlaceCompletionAlgebra
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

/-!
# Normalized finite-prime ideles

This file defines the idele supported at one finite place with normalized
local order one, and computes its associated fractional ideal and ideal
class. These constructions are independent of class field theory.
-/

open scoped NumberField

noncomputable section

namespace IdeleGroup

open NumberField IsDedekindDomain

variable {K : Type*} [Field K] [NumberField K]

/-- The idele supported at `v` whose normalized local order is one. -/
def finitePrimeIdele
    (v : HeightOneSpectrum (𝓞 K)) :
    IdeleGroup K :=
  finitePlaceIdele v (FiniteIdeleGroup.chosenLocalOrderSection v 1)

end IdeleGroup
end
end

section
-- module Solutions.OAIQ244_DUKE.AlgebraicNumberTheory_Idele_NormTopology_FiniteNormArithmetic
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.GlobalClassFields.ConductorialSubgroup.finiteIndex _root_.GlobalClassFieldTheory.GlobalClassFields.bigHilbertClassFieldNormSubgroup_normal _root_.GlobalClassFieldTheory.GlobalClassFields.smallHilbertClassFieldNormSubgroupFiniteIndex _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalClassFieldTheory.finiteGaloisLocalField_integerRing_moduleFinite _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.residueFieldZModAlgebra _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedIntegralAlgebraContextValuationSubringAlgebra _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedIntegralLatticeContextModuleFinite _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedIntegralLatticeContextModuleFree _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.LubinTate.standardLubinTateLevelValuationSubring_moduleFinite _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.CyclicCohomology.binaryCoefficientFamilyCommGroup _root_.LocalClassFieldTheory.comparisonIntegerRingIsIntegralClosure _root_.LocalClassFieldTheory.normalizationIntegerRingIsIntegralClosure _root_.relativeUnrestrictedSPlaceFactorCommGroup
attribute [-simp] _root_.GlobalClassFieldTheory.ClassFieldAxiom.actualPushoutNormQuotientMap_mk _root_.GlobalClassFieldTheory.ClassFieldAxiom.sUnitEquivSupportedPrincipalIdeleSubgroup_coe _root_.GlobalClassFieldTheory.GlobalClassFields.bigHilbertClassFieldQuotientEquivNarrowClassGroup_mk _root_.GlobalClassFieldTheory.GlobalClassFields.bigHilbertClassFieldQuotientToSmallHilbertClassFieldQuotient_mk _root_.GlobalClassFieldTheory.GlobalClassFields.realSignToBigHilbertClassFieldQuotient_apply _root_.GlobalClassFieldTheory.GlobalClassFields.realSignToNarrowClassKernel_apply _root_.GlobalClassFieldTheory.GlobalClassFields.smallHilbertClassFieldQuotientEquivClassGroup_mk _root_.GlobalClassFieldTheory.IdealClassFieldTheory.smallHilbertClassFieldIdeleExtensionMap_mk' _root_.GlobalClassFieldTheory.Reciprocity.globalNormClassFromIdele_principalIdele _root_.GlobalClassFieldTheory.Reciprocity.infinitePlaceGlobalArtinMonoidHom_finitePlaceIdele _root_.IdeleGroup.count_fractionalIdeal _root_.IdeleGroup.finitePlaceIdele_finiteComponent_of_ne _root_.IdeleGroup.finitePlaceIdele_finiteComponent_same _root_.IdeleGroup.finitePlaceIdele_infiniteComponent _root_.IdeleGroup.ideleNormContinuousMonoidHom_apply _root_.IdeleGroup.infinitePlaceIdeleContinuous_apply _root_.IdeleGroup.infinitePlaceIdele_finiteComponent _root_.IdeleGroup.infinitePlaceIdele_infiniteComponent_of_ne _root_.IdeleGroup.infinitePlaceIdele_infiniteComponent_same _root_.IsDiscreteValuationRing.addVal_ringEquiv _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.OAI.PrimeDegreePackets.ThetaConstruction.schwartzCM_apply _root_.RayClass.idealNormExponentMap_apply _root_.RayClass.idealNormLiftedModulusExponent_eq_zero_of_not_mem _root_.RayClass.mem_idealNormLiftedModulus_support_iff _root_.RayClass.primesEquiv_val_eq_natGenerator _root_.RayClass.signToNarrow_mk _root_.IdeleGroup.idealClass_classRepresentative _root_.doubleCosetExtension_mk _root_.extendAbsoluteValueExtensionFromIntermediate_apply _root_.ideleClassCongr_ideleClassNorm _root_.ideleClassCongr_mk _root_.ideleClassCongr_refl _root_.ideleCongr_finiteComponent _root_.ideleCongr_principalIdele _root_.intermediateClassNormQuotientBaseChangeMulEquiv_mk _root_.ordinaryIdeleClassNormQuotientCongrOfAlgEquiv_mk _root_.ordinaryIdeleClassNorm_relativeIdeleClassBaseChange _root_.relativeIdeleClassBaseChangeMulEquiv_classInclusion _root_.relativeIdeleClassBaseChangeMulEquiv_congrOfAlgEquiv _root_.relativeIdeleClassBaseChangeMulEquiv_mk _root_.relativeIdeleClassCongrOfAlgEquiv_ideleClassNorm _root_.relativeIdeleClassCongr_ideleClassNorm _root_.relativeIdeleCongr_norm _root_.restrictAbsoluteValueExtensionToIntermediate_apply _root_.towerRelativeIdeleViaOrdinaryMulEquiv_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

/-!
# Finite-place arithmetic of idele norms

This file relates the finite components of the ordinary idele norm to local
orders and positive prime norms. It also proves the degree formula for the
finite positive norm under scalar extension.
-/

open scoped BigOperators NNReal NumberField NumberField.LiesOver
open NumberField IsDedekindDomain

noncomputable section

namespace IdeleGroup

open AlgebraicNumberTheory.Valuations
open Function

universe u v

variable
    (K : Type u) (L : Type v)
    [Field K] [NumberField K]
    [Field L] [NumberField L]
    [Algebra K L] [FiniteDimensional K L]

/-- The order of a finite component of the ordinary idele norm is the sum
of the upstairs orders weighted by their inertia degrees. -/
theorem finiteComponentOrder_norm
    (v₀ : HeightOneSpectrum (𝓞 K))
    (a : IdeleGroup L) :
    let vK := HeightOneSpectrum.adicAbv K v₀
    let hvK : vK.IsNontrivial :=
      RayClass.adicAbv_isNontrivial v₀
    letI :=
      completionTensorDecomposition_extensionFintype
        (K := K) (L := L) vK hvK
    let eAbove :=
      finitePlaceExtensionEquivAbove
        (K := K) (L := L) v₀
    letI : Fintype {W : HeightOneSpectrum (𝓞 L) //
        _root_.finitePlaceBelow (K := K) W = v₀} :=
      Fintype.ofEquiv (AbsoluteValueExtension vK L) eAbove
    letI : ∀ W : {W : HeightOneSpectrum (𝓞 L) //
        _root_.finitePlaceBelow (K := K) W = v₀},
        Algebra (v₀.adicCompletion K) (W.1.adicCompletion L) :=
      fun W =>
        (finitePlaceAdicCompletionMap
          K L v₀ W).toAlgebra
    (FiniteIdeleGroup.localOrder v₀
      (finiteComponent v₀ (norm K L a))).toAdd =
      ∑ W : {W : HeightOneSpectrum (𝓞 L) //
          _root_.finitePlaceBelow (K := K) W = v₀},
        (W.1.asIdeal.inertiaDeg (𝓞 K) : ℤ) *
          (FiniteIdeleGroup.localOrder W.1
            (finiteComponent W.1 a)).toAdd := by
  classical
  dsimp only
  let vK := HeightOneSpectrum.adicAbv K v₀
  let hvK : vK.IsNontrivial :=
    RayClass.adicAbv_isNontrivial v₀
  let :=
    completionTensorDecomposition_extensionFintype
      (K := K) (L := L) vK hvK
  let eAbove :=
    finitePlaceExtensionEquivAbove
      (K := K) (L := L) v₀
  let : Fintype {W : HeightOneSpectrum (𝓞 L) //
      _root_.finitePlaceBelow (K := K) W = v₀} :=
    Fintype.ofEquiv (AbsoluteValueExtension vK L) eAbove
  let : ∀ W : {W : HeightOneSpectrum (𝓞 L) //
      _root_.finitePlaceBelow (K := K) W = v₀},
      Algebra (v₀.adicCompletion K) (W.1.adicCompletion L) :=
    fun W =>
      (finitePlaceAdicCompletionMap
        K L v₀ W).toAlgebra
  have hcomponent :
      finiteComponent v₀ (norm K L a) =
        ∏ W : {W : HeightOneSpectrum (𝓞 L) //
            _root_.finitePlaceBelow (K := K) W = v₀},
          LocalFieldTheory.normUnits
            (v₀.adicCompletion K) (W.1.adicCompletion L)
            (finiteComponent W.1 a) := by
    simpa only using
      finiteComponent_norm_eq_prod (K := K) (L := L) v₀ a
  rw [hcomponent]
  rw [map_prod]
  change
    (∑ W : {W : HeightOneSpectrum (𝓞 L) //
        _root_.finitePlaceBelow (K := K) W = v₀},
      (FiniteIdeleGroup.localOrder v₀
        (LocalFieldTheory.normUnits
          (v₀.adicCompletion K) (W.1.adicCompletion L)
          (finiteComponent W.1 a))).toAdd) =
      ∑ W : {W : HeightOneSpectrum (𝓞 L) //
          _root_.finitePlaceBelow (K := K) W = v₀},
        (W.1.asIdeal.inertiaDeg (𝓞 K) : ℤ) *
          (FiniteIdeleGroup.localOrder W.1
            (finiteComponent W.1 a)).toAdd
  apply Finset.sum_congr rfl
  intro W _
  exact
    FiniteIdeleGroup.localOrder_normUnits
      K L v₀ W (finiteComponent W.1 a)

/-- The finite positive idele norm is preserved by the ordinary idele
norm. -/
theorem finiteAbsoluteNorm_norm
    (a : IdeleGroup L) :
    FiniteIdeleGroup.absoluteNorm (norm K L a).2 =
      FiniteIdeleGroup.absoluteNorm a.2 := by
  classical
  rw [finiteAbsoluteNorm_eq_finprod
      (K := K) ((norm K L a).2),
    finiteAbsoluteNorm_eq_finprod
      (K := L) a.2]
  have hfinite :
      HasFiniteMulSupport
        (fun W : HeightOneSpectrum (𝓞 L) =>
          FiniteIdeleGroup.primeNorm W ^
            (FiniteIdeleGroup.localOrder W
              (finiteComponent W a)).toAdd) := by
    refine
      ((FiniteIdeleGroup.valuationVector a.2).toAdd.support.finite_toSet).subset
        ?_
    intro W hW
    by_contra hmem
    have hzero :
      (FiniteIdeleGroup.localOrder W
          (finiteComponent W a)).toAdd = 0 := by
      change (FiniteIdeleGroup.valuationVector a.2).toAdd W = 0
      exact Finsupp.notMem_support_iff.mp hmem
    apply hW
    change FiniteIdeleGroup.primeNorm W ^
      (FiniteIdeleGroup.localOrder W (finiteComponent W a)).toAdd = 1
    rw [hzero, zpow_zero]
  calc
    (∏ᶠ v₀ : HeightOneSpectrum (𝓞 K),
        FiniteIdeleGroup.primeNorm v₀ ^
          (FiniteIdeleGroup.localOrder v₀
            (finiteComponent v₀ (norm K L a))).toAdd) =
        ∏ᶠ v₀ : HeightOneSpectrum (𝓞 K),
          ∏ᶠ W : {W : HeightOneSpectrum (𝓞 L) //
              _root_.finitePlaceBelow (K := K) W = v₀},
            FiniteIdeleGroup.primeNorm W.1 ^
              (FiniteIdeleGroup.localOrder W.1
                (finiteComponent W.1 a)).toAdd := by
      apply finprod_congr
      intro v₀
      let vK := HeightOneSpectrum.adicAbv K v₀
      let hvK : vK.IsNontrivial :=
        RayClass.adicAbv_isNontrivial v₀
      let :=
        completionTensorDecomposition_extensionFintype
          (K := K) (L := L) vK hvK
      let eAbove :=
        finitePlaceExtensionEquivAbove
          (K := K) (L := L) v₀
      let : Fintype {W : HeightOneSpectrum (𝓞 L) //
          _root_.finitePlaceBelow (K := K) W = v₀} :=
        Fintype.ofEquiv (AbsoluteValueExtension vK L) eAbove
      let : ∀ W : {W : HeightOneSpectrum (𝓞 L) //
          _root_.finitePlaceBelow (K := K) W = v₀},
          Algebra (v₀.adicCompletion K) (W.1.adicCompletion L) :=
        fun W =>
          (finitePlaceAdicCompletionMap
            K L v₀ W).toAlgebra
      calc
        FiniteIdeleGroup.primeNorm v₀ ^
              (FiniteIdeleGroup.localOrder v₀
                (finiteComponent v₀ (norm K L a))).toAdd =
            FiniteIdeleGroup.primeNorm v₀ ^
              (∑ W : {W : HeightOneSpectrum (𝓞 L) //
                    _root_.finitePlaceBelow (K := K) W = v₀},
                (W.1.asIdeal.inertiaDeg (𝓞 K) : ℤ) *
                  (FiniteIdeleGroup.localOrder W.1
                    (finiteComponent W.1 a)).toAdd) := by
          rw [finiteComponentOrder_norm K L v₀ a]
        _ =
            ∏ W : {W : HeightOneSpectrum (𝓞 L) //
                _root_.finitePlaceBelow (K := K) W = v₀},
              FiniteIdeleGroup.primeNorm v₀ ^
                ((W.1.asIdeal.inertiaDeg (𝓞 K) : ℤ) *
                  (FiniteIdeleGroup.localOrder W.1
                    (finiteComponent W.1 a)).toAdd) := by
          simpa using
            zpow_finset_sum
              (FiniteIdeleGroup.primeNorm v₀)
              Finset.univ
              (fun W : {W : HeightOneSpectrum (𝓞 L) //
                  _root_.finitePlaceBelow (K := K) W = v₀} =>
                (W.1.asIdeal.inertiaDeg (𝓞 K) : ℤ) *
                  (FiniteIdeleGroup.localOrder W.1
                    (finiteComponent W.1 a)).toAdd)
        _ =
            ∏ W : {W : HeightOneSpectrum (𝓞 L) //
                _root_.finitePlaceBelow (K := K) W = v₀},
              FiniteIdeleGroup.primeNorm W.1 ^
                (FiniteIdeleGroup.localOrder W.1
                  (finiteComponent W.1 a)).toAdd := by
          apply Finset.prod_congr rfl
          intro W _
          rw [zpow_mul, zpow_natCast,
            ← primeNorm_above (K := K) (L := L) v₀ W]
        _ =
            ∏ᶠ W : {W : HeightOneSpectrum (𝓞 L) //
                _root_.finitePlaceBelow (K := K) W = v₀},
              FiniteIdeleGroup.primeNorm W.1 ^
                (FiniteIdeleGroup.localOrder W.1
                  (finiteComponent W.1 a)).toAdd :=
          (finprod_eq_prod_of_fintype _).symm
    _ =
        ∏ᶠ W : HeightOneSpectrum (𝓞 L),
          FiniteIdeleGroup.primeNorm W ^
            (FiniteIdeleGroup.localOrder W
              (finiteComponent W a)).toAdd :=
      finprod_over_fibers
        (_root_.finitePlaceBelow (K := K))
        (fun W : HeightOneSpectrum (𝓞 L) =>
          FiniteIdeleGroup.primeNorm W ^
            (FiniteIdeleGroup.localOrder W
              (finiteComponent W a)).toAdd)
        hfinite

end IdeleGroup

end
end

section
-- module Solutions.OAIQ244_DUKE.AlgebraicNumberTheory_Idele_NormTopology_ArchimedeanNorm
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.GlobalClassFields.ConductorialSubgroup.finiteIndex _root_.GlobalClassFieldTheory.GlobalClassFields.bigHilbertClassFieldNormSubgroup_normal _root_.GlobalClassFieldTheory.GlobalClassFields.smallHilbertClassFieldNormSubgroupFiniteIndex _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.KummerTheory.nthRootsSubgroupFintype _root_.LocalClassFieldTheory.finiteGaloisLocalField_integerRing_moduleFinite _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.residueFieldZModAlgebra _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedIntegralAlgebraContextValuationSubringAlgebra _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.CyclicCohomology.binaryCoefficientFamilyCommGroup _root_.LocalClassFieldTheory.comparisonIntegerRingIsIntegralClosure _root_.LocalClassFieldTheory.normalizationIntegerRingIsIntegralClosure _root_.relativeUnrestrictedSPlaceFactorCommGroup
attribute [-simp] _root_.GlobalClassFieldTheory.ClassFieldAxiom.actualPushoutNormQuotientMap_mk _root_.GlobalClassFieldTheory.ClassFieldAxiom.sUnitEquivSupportedPrincipalIdeleSubgroup_coe _root_.GlobalClassFieldTheory.GlobalClassFields.bigHilbertClassFieldQuotientEquivNarrowClassGroup_mk _root_.GlobalClassFieldTheory.GlobalClassFields.bigHilbertClassFieldQuotientToSmallHilbertClassFieldQuotient_mk _root_.GlobalClassFieldTheory.GlobalClassFields.realSignToBigHilbertClassFieldQuotient_apply _root_.GlobalClassFieldTheory.GlobalClassFields.realSignToNarrowClassKernel_apply _root_.GlobalClassFieldTheory.GlobalClassFields.smallHilbertClassFieldQuotientEquivClassGroup_mk _root_.GlobalClassFieldTheory.IdealClassFieldTheory.smallHilbertClassFieldIdeleExtensionMap_mk' _root_.GlobalClassFieldTheory.Reciprocity.globalNormClassFromIdele_principalIdele _root_.GlobalClassFieldTheory.Reciprocity.infinitePlaceGlobalArtinMonoidHom_finitePlaceIdele _root_.IdeleGroup.count_fractionalIdeal _root_.IdeleGroup.finitePlaceIdele_finiteComponent_of_ne _root_.IdeleGroup.finitePlaceIdele_finiteComponent_same _root_.IdeleGroup.finitePlaceIdele_infiniteComponent _root_.IdeleGroup.ideleNormContinuousMonoidHom_apply _root_.IdeleGroup.infinitePlaceBaseUnitExtension_neg_one _root_.IdeleGroup.infinitePlaceIdeleContinuous_apply _root_.IdeleGroup.infinitePlaceIdele_finiteComponent _root_.IdeleGroup.infinitePlaceIdele_infiniteComponent_of_ne _root_.IdeleGroup.infinitePlaceIdele_infiniteComponent_same _root_.IsDiscreteValuationRing.addVal_ringEquiv _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.OAI.PrimeDegreePackets.ThetaConstruction.schwartzCM_apply _root_.RayClass.primesEquiv_val_eq_natGenerator _root_.RayClass.signToNarrow_mk _root_.IdeleGroup.idealClass_classRepresentative _root_.doubleCosetExtension_mk _root_.extendAbsoluteValueExtensionFromIntermediate_apply _root_.ideleClassCongr_ideleClassNorm _root_.ideleClassCongr_mk _root_.ideleClassCongr_refl _root_.ideleCongr_finiteComponent _root_.ideleCongr_principalIdele _root_.intermediateClassNormQuotientBaseChangeMulEquiv_mk _root_.ordinaryIdeleClassNormQuotientCongrOfAlgEquiv_mk _root_.ordinaryIdeleClassNorm_relativeIdeleClassBaseChange _root_.relativeIdeleClassBaseChangeMulEquiv_classInclusion _root_.relativeIdeleClassBaseChangeMulEquiv_congrOfAlgEquiv _root_.relativeIdeleClassBaseChangeMulEquiv_mk _root_.relativeIdeleClassCongrOfAlgEquiv_ideleClassNorm _root_.relativeIdeleClassCongr_ideleClassNorm _root_.relativeIdeleCongr_norm _root_.restrictAbsoluteValueExtensionToIntermediate_apply _root_.towerRelativeIdeleViaOrdinaryMulEquiv_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

/-!
# Archimedean behavior of idele norms

The positive archimedean norm, and consequently the absolute idele norm, is
preserved by the ordinary norm in a finite number-field extension.
-/

open scoped BigOperators NumberField NumberField.LiesOver
open NumberField IsDedekindDomain

noncomputable section

namespace IdeleGroup

universe u v

variable
    (K : Type u) (L : Type v)
    [Field K] [NumberField K]
    [Field L] [NumberField L]
    [Algebra K L] [FiniteDimensional K L]

/-- The archimedean positive norm is preserved by the ordinary idele norm. -/
theorem archimedeanNorm_norm
    (a : IdeleGroup L) :
    InfiniteIdeleGroup.archimedeanNorm
        (norm K L a).1 =
      InfiniteIdeleGroup.archimedeanNorm a.1 := by
  classical
  let : ∀ (v₀ : InfinitePlace K)
      (W : {W : InfinitePlace L //
        _root_.infinitePlaceBelow (K := K) W = v₀}),
      W.1.1.LiesOver v₀.1 :=
    fun v₀ W =>
      ⟨congrArg (fun q : InfinitePlace K => q.1) W.2⟩
  let : ∀ (v₀ : InfinitePlace K)
      (W : {W : InfinitePlace L //
        _root_.infinitePlaceBelow (K := K) W = v₀}),
      Algebra v₀.Completion W.1.Completion :=
    fun v₀ W =>
      (NumberField.LiesOver.completionMap
        (v := v₀) (w := W.1)).toAlgebra
  rw [InfiniteIdeleGroup.archimedeanNorm_apply,
    InfiniteIdeleGroup.archimedeanNorm_apply]
  change
    (∏ v₀ : InfinitePlace K,
        nnnormUnitHom v₀.Completion
          (infiniteComponent v₀ (norm K L a)) ^ v₀.mult) =
      ∏ W : InfinitePlace L,
        nnnormUnitHom W.Completion
          (infiniteComponent W a) ^ W.mult
  calc
    (∏ v₀ : InfinitePlace K,
        nnnormUnitHom v₀.Completion
          (infiniteComponent v₀ (norm K L a)) ^ v₀.mult) =
        ∏ v₀ : InfinitePlace K,
          ∏ W : {W : InfinitePlace L //
              _root_.infinitePlaceBelow (K := K) W = v₀},
            nnnormUnitHom v₀.Completion
                (LocalFieldTheory.normUnits
                  v₀.Completion W.1.Completion
                  (infiniteComponent W.1 a)) ^ v₀.mult := by
      apply Finset.prod_congr rfl
      intro v₀ _
      rw [infiniteComponent_norm_eq_prod]
      let vK := v₀.1
      let hvK : vK.IsNontrivial := v₀.isNontrivial
      let :=
        AlgebraicNumberTheory.Valuations.completionTensorDecomposition_extensionFintype
          (K := K) (L := L) vK hvK
      let eAbove :=
        infinitePlaceAboveEquivExtension (K := K) (L := L) v₀
      have hUniv :
          @Finset.univ
              {W : InfinitePlace L //
                _root_.infinitePlaceBelow (K := K) W = v₀}
              (Fintype.ofEquiv
                (AlgebraicNumberTheory.Valuations.AbsoluteValueExtension vK L)
                eAbove.symm) =
            @Finset.univ
              {W : InfinitePlace L //
                _root_.infinitePlaceBelow (K := K) W = v₀}
              (Subtype.fintype fun W =>
                _root_.infinitePlaceBelow (K := K) W = v₀) := by
        ext W
        simp
      rw [hUniv]
      rw [map_prod, Finset.prod_pow]
    _ =
        ∏ v₀ : InfinitePlace K,
          ∏ W : {W : InfinitePlace L //
              _root_.infinitePlaceBelow (K := K) W = v₀},
            nnnormUnitHom W.1.Completion
                (infiniteComponent W.1 a) ^ W.1.mult := by
      apply Finset.prod_congr rfl
      intro v₀ _
      apply Finset.prod_congr rfl
      intro W _
      exact
        nnnormUnitHom_normUnits_infinitePlace
          (K := K) (L := L) v₀ W.1
          ⟨congrArg (fun q : InfinitePlace K => q.1) W.2⟩
          (infiniteComponent W.1 a)
    _ =
        ∏ W : InfinitePlace L,
          nnnormUnitHom W.Completion
            (infiniteComponent W a) ^ W.mult := by
      exact
        Fintype.prod_fiberwise
          (_root_.infinitePlaceBelow (K := K))
          (fun W : InfinitePlace L =>
            nnnormUnitHom W.Completion
              (infiniteComponent W a) ^ W.mult)

/-- The absolute idele norm is preserved by the ordinary idele norm. -/
theorem absoluteNorm_norm
    (a : IdeleGroup L) :
    absoluteNorm (norm K L a) =
      absoluteNorm a := by
  rw [absoluteNorm_apply, absoluteNorm_apply,
    finiteAbsoluteNorm_norm, archimedeanNorm_norm]


end IdeleGroup

end
end

section
-- module Solutions.OAIQ244_DUKE.AlgebraicNumberTheory_Idele_NormTopology_IdeleClassNorm
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 400000
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.GlobalClassFields.ConductorialSubgroup.finiteIndex _root_.GlobalClassFieldTheory.GlobalClassFields.bigHilbertClassFieldNormSubgroup_normal _root_.GlobalClassFieldTheory.GlobalClassFields.smallHilbertClassFieldNormSubgroupFiniteIndex _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalClassFieldTheory.finiteGaloisLocalField_integerRing_moduleFinite _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.residueFieldZModAlgebra _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedIntegralAlgebraContextValuationSubringAlgebra _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.LubinTate.compatibleGroupFamiliesGroup _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.CyclicCohomology.binaryCoefficientFamilyCommGroup _root_.LocalClassFieldTheory.comparisonIntegerRingIsIntegralClosure _root_.LocalClassFieldTheory.normalizationIntegerRingIsIntegralClosure _root_.relativeUnrestrictedSPlaceFactorCommGroup
attribute [-simp] _root_.GlobalClassFieldTheory.ClassFieldAxiom.actualPushoutNormQuotientMap_mk _root_.GlobalClassFieldTheory.ClassFieldAxiom.sUnitEquivSupportedPrincipalIdeleSubgroup_coe _root_.GlobalClassFieldTheory.GlobalClassFields.bigHilbertClassFieldQuotientEquivNarrowClassGroup_mk _root_.GlobalClassFieldTheory.GlobalClassFields.bigHilbertClassFieldQuotientToSmallHilbertClassFieldQuotient_mk _root_.GlobalClassFieldTheory.GlobalClassFields.realSignToBigHilbertClassFieldQuotient_apply _root_.GlobalClassFieldTheory.GlobalClassFields.realSignToNarrowClassKernel_apply _root_.GlobalClassFieldTheory.GlobalClassFields.smallHilbertClassFieldQuotientEquivClassGroup_mk _root_.GlobalClassFieldTheory.IdealClassFieldTheory.smallHilbertClassFieldIdeleExtensionMap_mk' _root_.GlobalClassFieldTheory.Reciprocity.globalNormClassFromIdele_principalIdele _root_.GlobalClassFieldTheory.Reciprocity.infinitePlaceGlobalArtinMonoidHom_finitePlaceIdele _root_.IdeleGroup.count_fractionalIdeal _root_.IdeleGroup.finitePlaceIdele_finiteComponent_of_ne _root_.IdeleGroup.finitePlaceIdele_finiteComponent_same _root_.IdeleGroup.finitePlaceIdele_infiniteComponent _root_.IdeleGroup.ideleNormContinuousMonoidHom_apply _root_.IdeleGroup.infinitePlaceIdeleContinuous_apply _root_.IdeleGroup.infinitePlaceIdele_finiteComponent _root_.IdeleGroup.infinitePlaceIdele_infiniteComponent_of_ne _root_.IdeleGroup.infinitePlaceIdele_infiniteComponent_same _root_.IsDiscreteValuationRing.addVal_ringEquiv _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.OAI.PrimeDegreePackets.ThetaConstruction.schwartzCM_apply _root_.RayClass.primesEquiv_val_eq_natGenerator _root_.RayClass.signToNarrow_mk _root_.IdeleGroup.idealClass_classRepresentative _root_.ideleClassCongr_ideleClassNorm _root_.ideleClassCongr_mk _root_.ideleClassCongr_refl _root_.ideleCongr_finiteComponent _root_.ideleCongr_principalIdele _root_.intermediateClassNormQuotientBaseChangeMulEquiv_mk _root_.ordinaryIdeleClassNormQuotientCongrOfAlgEquiv_mk _root_.ordinaryIdeleClassNorm_relativeIdeleClassBaseChange _root_.relativeIdeleClassBaseChangeMulEquiv_classInclusion _root_.relativeIdeleClassBaseChangeMulEquiv_congrOfAlgEquiv _root_.relativeIdeleClassBaseChangeMulEquiv_mk _root_.relativeIdeleClassCongrOfAlgEquiv_ideleClassNorm _root_.relativeIdeleClassCongr_ideleClassNorm _root_.relativeIdeleCongr_norm _root_.towerRelativeIdeleViaOrdinaryMulEquiv_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

/-!
# The ordinary norm on idele classes

The ordinary idele-class norm preserves the absolute norm and restricts to
the norm-one idele-class subgroups.
-/

open scoped NumberField
open NumberField

noncomputable section

namespace IdeleClassGroup

universe u v

variable
    (K : Type u) (L : Type v)
    [Field K] [NumberField K]
    [Field L] [NumberField L]
    [Algebra K L] [FiniteDimensional K L]

/-- The ordinary idèle-class norm preserves the absolute idèle norm. -/
theorem absoluteNorm_ideleClassNorm
    (c : IdeleClassGroup L) :
    absoluteNorm (_root_.ideleClassNorm K L c) =
      absoluteNorm c := by
  refine QuotientGroup.induction_on c ?_
  intro a
  change
    absoluteNorm
        (_root_.ideleClassNorm K L
          (QuotientGroup.mk'
            (IdeleGroup.principalSubgroup L) a)) =
      absoluteNorm
        (QuotientGroup.mk'
          (IdeleGroup.principalSubgroup L) a)
  rw [_root_.ideleClassNorm_mk,
    absoluteNorm_mk, absoluteNorm_mk,
    IdeleGroup.absoluteNorm_norm]

/-- The ordinary idele-class norm carries norm-one idele classes to
norm-one idele classes. -/
theorem ideleClassNorm_mem_normOneSubgroup
    (c : IdeleClassGroup L)
    (hc : c ∈ normOneSubgroup (K := L)) :
    _root_.ideleClassNorm K L c ∈
      normOneSubgroup (K := K) := by
  change
    absoluteNorm (_root_.ideleClassNorm K L c) = 1
  change absoluteNorm c = 1 at hc
  rw [absoluteNorm_ideleClassNorm]
  exact hc

/-- The ordinary idele-class norm restricted to the norm-one idele-class
groups. -/
noncomputable def normOneNorm :
    normOneSubgroup (K := L) →*
      normOneSubgroup (K := K) :=
  ((_root_.ideleClassNorm K L).comp
      (normOneSubgroup (K := L)).subtype).codRestrict
    (normOneSubgroup (K := K))
    (fun c =>
      ideleClassNorm_mem_normOneSubgroup
        K L c.1 c.2)

/-- Coercing the restricted norm-one map recovers the ordinary idèle-class norm. -/
@[simp]
theorem normOneNorm_apply
    (c : normOneSubgroup (K := L)) :
    (normOneNorm K L c : IdeleClassGroup K) =
      _root_.ideleClassNorm K L c.1 :=
  rfl


end IdeleClassGroup

end
end

section
-- module Solutions.OAIQ244_DUKE.GlobalClassFieldTheory_Reciprocity_IdeleClassDirectLimitCore
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.GlobalClassFields.ConductorialSubgroup.finiteIndex _root_.GlobalClassFieldTheory.GlobalClassFields.bigHilbertClassFieldNormSubgroup_normal _root_.GlobalClassFieldTheory.GlobalClassFields.smallHilbertClassFieldNormSubgroupFiniteIndex _root_.GlobalClassFieldTheory.Reciprocity.complexFourthRootField_numberField _root_.GlobalClassFieldTheory.Reciprocity.infinitePlaceComplexificationOverfield_algebra _root_.GlobalClassFieldTheory.Reciprocity.infinitePlaceComplexificationOverfield_baseAlgebra _root_.GlobalClassFieldTheory.Reciprocity.infinitePlaceComplexificationOverfield_numberField _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.KummerTheory.primeCyclotomicBaseFiniteDimensional _root_.KummerTheory.primeCyclotomicBaseIsGalois _root_.KummerTheory.primeCyclotomicBaseNumberField _root_.KummerTheory.rationalCyclotomicLevel_numberField _root_.LocalClassFieldTheory.finiteGaloisLocalField_integerRing_moduleFinite _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.residueFieldZModAlgebra _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedIntegralAlgebraContextValuationSubringAlgebra _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedIntegralAlgebraContextValuationSubringTower _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedQPadicContextValuationSubringTower _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.boundedRealFields_numberField _root_.OAI.PrimeDegreePackets.diagonalLogAction _root_.OAI.PrimeDegreePackets.instNonemptyLeafTestSpace _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.CyclicCohomology.binaryCoefficientFamilyCommGroup _root_.CyclicCohomology.instMulDistribMulActionBinaryCoefficientFamily _root_.LocalClassFieldTheory.comparisonIntegerRingIsIntegralClosure _root_.LocalClassFieldTheory.normalizationIntegerRingIsIntegralClosure _root_.chosenFinitePlaceCompletionAlgebra _root_.chosenFinitePlaceCompletionFiniteDimensional _root_.chosenFinitePlaceLocalizedFiniteDimensional _root_.chosenFinitePlaceLocalizedIntegerAlgebra _root_.chosenFinitePlaceLocalizedIsGalois _root_.cyclicPrimeDegreeIntermediate_isGalois _root_.cyclicPrimeSubextension_isGalois _root_.relativeUnrestrictedSPlaceFactorCommGroup
attribute [-simp] _root_.GlobalClassFieldTheory.ClassFieldAxiom.actualPushoutNormQuotientMap_mk _root_.IsDiscreteValuationRing.addVal_ringEquiv _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.OAI.PrimeDegreePackets.ThetaConstruction.schwartzCM_apply _root_.RayClass.primesEquiv_val_eq_natGenerator _root_.RelativeIdeleGroup.relativeFinitePlaceIdele_finiteComponent_of_ne _root_.RelativeIdeleGroup.relativeFinitePlaceIdele_finiteComponent_same _root_.RelativeIdeleGroup.relativeFinitePlaceIdele_infiniteComponent _root_.RelativeIdeleGroup.relativeInfinitePlaceIdele_finiteComponent _root_.RelativeIdeleGroup.relativeInfinitePlaceIdele_infiniteComponent_of_ne _root_.RelativeIdeleGroup.relativeInfinitePlaceIdele_infiniteComponent_same _root_.intermediateClassNormQuotientBaseChangeMulEquiv_mk _root_.relativeIdeleClassBaseChangeMulEquiv_congrOfAlgEquiv _root_.towerActualRelativeAdeleRingEquiv_tmul _root_.towerRelativeIdeleBaseChangeMulEquiv_principalIdele _root_.towerRelativeIdeleClassBaseChangeMulEquiv_mk _root_.towerRelativeIdeleViaOrdinaryMulEquiv_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

/-!
# The rational absolute idele-class direct limit

Finite Galois relative idele class groups over `ℚ`, their scalar-extension
maps, and the induced absolute Galois representation.
-/

open scoped NumberField TensorProduct
open NumberField

noncomputable section

namespace GlobalClassFieldTheory
namespace Reciprocity

open CyclicCohomology

universe u

/-- Extending the diagonal rational idele class through two nested
intermediate fields is the diagonal class at the larger field. -/
theorem rationalRelativeIdeleClassEmbedding_classInclusion
    {E F : IntermediateField ℚ (SeparableClosure ℚ)}
    [NumberField E] [NumberField F]
    (h : E ≤ F)
    (c : IdeleClassGroup ℚ) :
    RelativeIdeleGroup.classEmbedding (IntermediateField.inclusion h)
        (RelativeIdeleGroup.classInclusion ℚ E c) =
      RelativeIdeleGroup.classInclusion ℚ F c := by
  refine QuotientGroup.induction_on c ?_
  intro a
  rfl

/-- The action of the rational absolute Galois group on one finite
relative idele class group, obtained by restricting automorphisms. -/
@[reducible]
noncomputable def rationalAbsoluteGaloisIdeleClassAction
    (E : FiniteGaloisIntermediateField ℚ (SeparableClosure ℚ)) :
    MulDistribMulAction
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ)
      (RelativeIdeleGroup.ClassGroup ℚ E) := by
  letI :
      MulDistribMulAction (E ≃ₐ[ℚ] E)
        (RelativeIdeleGroup.ClassGroup ℚ E) :=
    RelativeIdeleGroup.Cohomology.ideleClassMulDistribMulAction ℚ E
  exact
    MulDistribMulAction.compHom
      (RelativeIdeleGroup.ClassGroup ℚ E)
      (AlgEquiv.restrictNormalHom E)

instance instMonoidClassGroupRatSubtypeSeparableClosureMemIntermediateField
    (E : FiniteGaloisIntermediateField ℚ (SeparableClosure ℚ)) :
    Monoid (RelativeIdeleGroup.ClassGroup ℚ E) :=
  inferInstance

noncomputable instance instMulDistribMulActionAlgEquivRatSeparableClosureClassGroupSubtypeMemIntermediateField :
    ∀ E : FiniteGaloisIntermediateField ℚ (SeparableClosure ℚ),
      MulDistribMulAction
        (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ)
        (RelativeIdeleGroup.ClassGroup ℚ E) :=
  fun E => rationalAbsoluteGaloisIdeleClassAction E

noncomputable instance instSMulAlgEquivRatSeparableClosureClassGroupSubtypeMemIntermediateField :
    ∀ E : FiniteGaloisIntermediateField ℚ (SeparableClosure ℚ),
      SMul
        (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ)
        (RelativeIdeleGroup.ClassGroup ℚ E) :=
  fun E => (rationalAbsoluteGaloisIdeleClassAction E).toSMul

@[simp]
theorem rationalAbsoluteGaloisIdeleClass_smul_mk
    (E : FiniteGaloisIntermediateField ℚ (SeparableClosure ℚ))
    (σ : SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ)
    (a : RelativeIdeleGroup ℚ E) :
    σ • QuotientGroup.mk'
          (RelativeIdeleGroup.principalSubgroup ℚ E) a =
      QuotientGroup.mk'
        (RelativeIdeleGroup.principalSubgroup ℚ E)
        ((AlgEquiv.restrictNormalHom E σ) • a) :=
  rfl

/-- Relative-adele scalar extension intertwines conjugation with the
restriction of an absolute Galois automorphism. -/
theorem rationalRelativeAdeleEmbedding_conjugation_of_restrict
    {E : IntermediateField ℚ (SeparableClosure ℚ)}
    [FiniteDimensional ℚ E]
    {F : FiniteGaloisIntermediateField ℚ (SeparableClosure ℚ)}
    (h : E ≤ (F : IntermediateField ℚ (SeparableClosure ℚ)))
    (σ : SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ)
    (τ : E ≃ₐ[ℚ] E)
    (hστ : ∀ x : E,
      ((τ x : E) : SeparableClosure ℚ) =
        σ (x : SeparableClosure ℚ))
    (z : RelativeAdeleRing ℚ E) :
    RelativeIdeleGroup.adeleEmbedding (IntermediateField.inclusion h)
        (RelativeIdeleGroup.conjugation ℚ E τ z) =
      RelativeIdeleGroup.conjugation ℚ F
        (AlgEquiv.restrictNormalHom F σ)
        (RelativeIdeleGroup.adeleEmbedding (IntermediateField.inclusion h) z) := by
  induction z using OAI.tensorInductionOn with
  | tmul a x =>
      simp only [RelativeIdeleGroup.conjugation_tmul,
        RelativeIdeleGroup.adeleEmbedding,
        RelativeIdeleGroup.scalarEmbedding_tmul]
      congr 1
      apply Subtype.ext
      calc
        ((IntermediateField.inclusion h (τ x) : F) :
            SeparableClosure ℚ) =
            ((τ x : E) : SeparableClosure ℚ) := rfl
        _ = σ (x : SeparableClosure ℚ) := hστ x
        _ = σ ((IntermediateField.inclusion h x : F) :
            SeparableClosure ℚ) := rfl
        _ = (((AlgEquiv.restrictNormalHom F σ)
              (IntermediateField.inclusion h x) : F) :
            SeparableClosure ℚ) :=
          (AlgEquiv.restrictNormal_commutes σ F
            (IntermediateField.inclusion h x)).symm
  | add x y hx hy =>
      simp only [map_add, hx, hy]

/-- Relative-idele scalar extension intertwines conjugation with the
restriction of an absolute Galois automorphism. -/
theorem rationalRelativeIdeleEmbedding_conjugation_of_restrict
    {E : IntermediateField ℚ (SeparableClosure ℚ)}
    [FiniteDimensional ℚ E]
    {F : FiniteGaloisIntermediateField ℚ (SeparableClosure ℚ)}
    (h : E ≤ (F : IntermediateField ℚ (SeparableClosure ℚ)))
    (σ : SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ)
    (τ : E ≃ₐ[ℚ] E)
    (hστ : ∀ x : E,
      ((τ x : E) : SeparableClosure ℚ) =
        σ (x : SeparableClosure ℚ))
    (a : RelativeIdeleGroup ℚ E) :
    RelativeIdeleGroup.ideleEmbedding (IntermediateField.inclusion h)
        (τ • a) =
      (AlgEquiv.restrictNormalHom F σ) •
        RelativeIdeleGroup.ideleEmbedding (IntermediateField.inclusion h) a := by
  apply Units.ext
  exact
    rationalRelativeAdeleEmbedding_conjugation_of_restrict
      h σ τ hστ
      (a : RelativeAdeleRing ℚ E)

/-- Relative idele-class scalar extension intertwines conjugation with
the restriction of an absolute Galois automorphism. -/
theorem
    rationalRelativeIdeleClassEmbedding_conjugation_of_restrict
    {E : IntermediateField ℚ (SeparableClosure ℚ)}
    [FiniteDimensional ℚ E]
    {F : FiniteGaloisIntermediateField ℚ (SeparableClosure ℚ)}
    (h : E ≤ (F : IntermediateField ℚ (SeparableClosure ℚ)))
    (σ : SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ)
    (τ : E ≃ₐ[ℚ] E)
    (hστ : ∀ x : E,
      ((τ x : E) : SeparableClosure ℚ) =
        σ (x : SeparableClosure ℚ))
    (c : RelativeIdeleGroup.ClassGroup ℚ E) :
    RelativeIdeleGroup.classEmbedding (IntermediateField.inclusion h) (τ • c) =
      σ • RelativeIdeleGroup.classEmbedding (IntermediateField.inclusion h) c := by
  refine QuotientGroup.induction_on c ?_
  intro a
  exact congrArg
    (QuotientGroup.mk'
      (RelativeIdeleGroup.principalSubgroup ℚ F))
    (rationalRelativeIdeleEmbedding_conjugation_of_restrict
      h σ τ hστ a)

/-- The transition map between finite Galois relative idele class groups
is equivariant for the rational absolute Galois action. -/
theorem rationalRelativeIdeleClassEmbedding_smul
    {E F : FiniteGaloisIntermediateField ℚ (SeparableClosure ℚ)}
    (h : E ≤ F)
    (σ : SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ)
    (c : RelativeIdeleGroup.ClassGroup ℚ E) :
    RelativeIdeleGroup.classEmbedding (IntermediateField.inclusion h) (σ • c) =
      σ • RelativeIdeleGroup.classEmbedding (IntermediateField.inclusion h) c := by
  apply rationalRelativeIdeleClassEmbedding_conjugation_of_restrict
    h σ (AlgEquiv.restrictNormalHom E σ)
  intro x
  simp only [AlgEquiv.restrictNormalHom_apply]

/-- Acting after scalar extension agrees with the class embedding induced
by the resulting restricted field embedding. -/
theorem
    rationalRelativeIdeleClassEmbedding_smul_eq_classEmbedding
    {E : IntermediateField ℚ (SeparableClosure ℚ)}
    [FiniteDimensional ℚ E]
    {F : FiniteGaloisIntermediateField ℚ (SeparableClosure ℚ)}
    (h : E ≤ F)
    (σ : SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ)
    (c : RelativeIdeleGroup.ClassGroup ℚ E) :
    (AlgEquiv.restrictNormalHom F σ) •
        RelativeIdeleGroup.classEmbedding (IntermediateField.inclusion h) c =
      RelativeIdeleGroup.classEmbedding
        ((AlgEquiv.restrictNormalHom F σ).toAlgHom.comp
          (IntermediateField.inclusion h)) c := by
  refine QuotientGroup.induction_on c ?_
  intro a
  apply congrArg
    (QuotientGroup.mk'
      (RelativeIdeleGroup.principalSubgroup ℚ F))
  apply Units.ext
  change
    RelativeIdeleGroup.conjugation ℚ F
        (AlgEquiv.restrictNormalHom F σ)
        (RelativeIdeleGroup.adeleEmbedding (IntermediateField.inclusion h)
          (a : RelativeAdeleRing ℚ E)) =
      RelativeIdeleGroup.adeleEmbedding
        ((AlgEquiv.restrictNormalHom F σ).toAlgHom.comp
          (IntermediateField.inclusion h))
        (a : RelativeAdeleRing ℚ E)
  induction (a : RelativeAdeleRing ℚ E) using
      OAI.tensorInductionOn with
  | tmul y x =>
      simp only [RelativeIdeleGroup.adeleEmbedding,
        RelativeIdeleGroup.scalarEmbedding_tmul,
        RelativeIdeleGroup.conjugation_tmul]
      congr 1
  | add x y hx hy =>
      simp only [map_add, hx, hy]

/-- The equivariant scalar-extension transition map in the
finite-Galois idele-class system. -/
noncomputable def rationalRelativeIdeleClassTransition
    {E F : FiniteGaloisIntermediateField ℚ (SeparableClosure ℚ)}
    (h : E ≤ F) :
    MulDistribMulActionHom
      (MonoidHom.id
        (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
      (RelativeIdeleGroup.ClassGroup ℚ E)
      (RelativeIdeleGroup.ClassGroup ℚ F) where
  toMonoidHom :=
    RelativeIdeleGroup.classEmbedding (IntermediateField.inclusion h)
  map_smul' σ c := by
    simpa using rationalRelativeIdeleClassEmbedding_smul h σ c

/-- Scalar extension of relative adeles along the identity inclusion is
the identity. -/
theorem rationalRelativeAdeleEmbedding_self
    (E : IntermediateField ℚ (SeparableClosure ℚ))
    [NumberField E]
    (z : RelativeAdeleRing ℚ E) :
    RelativeIdeleGroup.adeleEmbedding
      (IntermediateField.inclusion (show E ≤ E from le_rfl)) z = z := by
  induction z using OAI.tensorInductionOn with
  | tmul a x =>
      simp only [RelativeIdeleGroup.adeleEmbedding,
        RelativeIdeleGroup.scalarEmbedding_tmul]
      congr 1
  | add x y hx hy =>
      simp only [map_add, hx, hy]

/-- Scalar extension of relative adeles is transitive in a tower of
intermediate fields. -/
theorem rationalRelativeAdeleEmbedding_comp
    {E F H : IntermediateField ℚ (SeparableClosure ℚ)}
    [NumberField E] [NumberField F] [NumberField H]
    (hEF : E ≤ F) (hFH : F ≤ H)
    (z : RelativeAdeleRing ℚ E) :
    RelativeIdeleGroup.adeleEmbedding (IntermediateField.inclusion hFH)
        (RelativeIdeleGroup.adeleEmbedding (IntermediateField.inclusion hEF) z) =
      RelativeIdeleGroup.adeleEmbedding
        (IntermediateField.inclusion (hEF.trans hFH)) z := by
  induction z using OAI.tensorInductionOn with
  | tmul a x =>
      simp only [RelativeIdeleGroup.adeleEmbedding,
        RelativeIdeleGroup.scalarEmbedding_tmul]
      congr 1
  | add x y hx hy =>
      simp only [map_add, hx, hy]

/-- Scalar extension of relative idele classes along the identity
inclusion is the identity. -/
theorem rationalRelativeIdeleClassEmbedding_self
    (E : IntermediateField ℚ (SeparableClosure ℚ))
    [NumberField E]
    (c : RelativeIdeleGroup.ClassGroup ℚ E) :
    RelativeIdeleGroup.classEmbedding
      (IntermediateField.inclusion (show E ≤ E from le_rfl)) c = c := by
  refine QuotientGroup.induction_on c ?_
  intro a
  exact congrArg
    (QuotientGroup.mk'
      (RelativeIdeleGroup.principalSubgroup ℚ E))
    (Units.ext
      (rationalRelativeAdeleEmbedding_self E
        (a : RelativeAdeleRing ℚ E)))

/-- Scalar extension of relative idele classes is transitive in a tower
of intermediate fields. -/
theorem rationalRelativeIdeleClassEmbedding_comp
    {E F H : IntermediateField ℚ (SeparableClosure ℚ)}
    [NumberField E] [NumberField F] [NumberField H]
    (hEF : E ≤ F) (hFH : F ≤ H)
    (c : RelativeIdeleGroup.ClassGroup ℚ E) :
    RelativeIdeleGroup.classEmbedding (IntermediateField.inclusion hFH)
        (RelativeIdeleGroup.classEmbedding (IntermediateField.inclusion hEF) c) =
      RelativeIdeleGroup.classEmbedding
        (IntermediateField.inclusion (hEF.trans hFH)) c := by
  refine QuotientGroup.induction_on c ?_
  intro a
  exact congrArg
    (QuotientGroup.mk'
      (RelativeIdeleGroup.principalSubgroup ℚ H))
    (Units.ext
      (rationalRelativeAdeleEmbedding_comp hEF hFH
        (a : RelativeAdeleRing ℚ E)))

noncomputable instance instDirectedSystemFiniteGaloisIntermediateFieldRatSeparableClosureClassGroupSubtypeMemIntermediateFieldCoeMulDistribMulActionHomAlgEquivIdRationalRelativeIdeleClassTransition :
    DirectedSystem
      (fun E : FiniteGaloisIntermediateField ℚ (SeparableClosure ℚ) =>
        RelativeIdeleGroup.ClassGroup ℚ E)
      (fun _ _ h => rationalRelativeIdeleClassTransition h) where
  map_self {i} c :=
    rationalRelativeIdeleClassEmbedding_self
      (i : IntermediateField ℚ (SeparableClosure ℚ)) c
  map_map {k} {j} {i} hIJ hJK c :=
    rationalRelativeIdeleClassEmbedding_comp
      (E := (i : IntermediateField ℚ (SeparableClosure ℚ)))
      (F := (j : IntermediateField ℚ (SeparableClosure ℚ)))
      (H := (k : IntermediateField ℚ (SeparableClosure ℚ)))
      hIJ hJK c

/-- The direct limit of the actual idele class groups of the finite
Galois subextensions of `SeparableClosure ℚ / ℚ`. -/
noncomputable abbrev rationalIdeleClassDirectLimit :=
  DirectLimit
    (fun E : FiniteGaloisIntermediateField ℚ (SeparableClosure ℚ) =>
      RelativeIdeleGroup.ClassGroup ℚ E)
    (fun _ _ h => rationalRelativeIdeleClassTransition h)

/-- The multiplicative structure on the rational absolute idele-class
direct limit supplied by Mathlib's directed-limit construction. -/
noncomputable instance rationalIdeleClassDirectLimitMonoid :
    Monoid rationalIdeleClassDirectLimit :=
  DirectLimit.instMonoid

theorem rationalIdeleClassDirectLimit_mk_apply
    {E F : FiniteGaloisIntermediateField ℚ (SeparableClosure ℚ)}
    (c : RelativeIdeleGroup.ClassGroup ℚ E)
    (h : E ≤ F) :
    (⟦⟨F, RelativeIdeleGroup.classEmbedding (IntermediateField.inclusion h) c⟩⟧ :
        rationalIdeleClassDirectLimit) =
      ⟦⟨E, c⟩⟧ := by
  exact
    DirectLimit.mk_apply
      (F := fun E :
        FiniteGaloisIntermediateField ℚ (SeparableClosure ℚ) =>
          RelativeIdeleGroup.ClassGroup ℚ E)
      (f := fun _ _ h =>
        rationalRelativeIdeleClassTransition h)
      E F c h

/-- The canonical map from one finite-level relative idele class group
to the directed limit. -/
def rationalRelativeIdeleClassToDirectLimit
    (E : FiniteGaloisIntermediateField ℚ (SeparableClosure ℚ)) :
    RelativeIdeleGroup.ClassGroup ℚ E →*
      rationalIdeleClassDirectLimit where
  toFun c := ⟦⟨E, c⟩⟧
  map_one' := by
    exact
      (DirectLimit.one_def
        (G := fun E :
          FiniteGaloisIntermediateField ℚ (SeparableClosure ℚ) =>
            RelativeIdeleGroup.ClassGroup ℚ E)
        (f := fun _ _ h =>
          rationalRelativeIdeleClassTransition h)
        E).symm
  map_mul' c d := by
    exact
      (DirectLimit.mul_def
        (G := fun E :
          FiniteGaloisIntermediateField ℚ (SeparableClosure ℚ) =>
            RelativeIdeleGroup.ClassGroup ℚ E)
        (f := fun _ _ h =>
          rationalRelativeIdeleClassTransition h)
        E c d).symm

/-- The rational absolute Galois action on the idele-class direct limit,
supplied by Mathlib from the equivariant transition maps. -/
noncomputable instance
    rationalIdeleClassDirectLimitMulDistribMulAction :
    MulDistribMulAction
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ)
      rationalIdeleClassDirectLimit :=
  DirectLimit.instMulDistribMulActionOfMulActionHomClass

/-- The scalar action underlying the canonical absolute Galois action on
the rational idele-class direct limit. -/
noncomputable instance rationalIdeleClassDirectLimitSMul :
    SMul
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ)
      rationalIdeleClassDirectLimit :=
  rationalIdeleClassDirectLimitMulDistribMulAction.toSMul

/-- The coefficient representation of the global class formation:
the rational absolute Galois group acts on the direct limit of the
actual finite-level idele class groups. -/
noncomputable def rationalIdeleClassRepresentation :
    Rep ℤ (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ) :=
  Rep.ofMulDistribMulAction
    (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ)
    rationalIdeleClassDirectLimit

end Reciprocity
end GlobalClassFieldTheory
end
end

section
-- module Solutions.OAIQ244_DUKE.GlobalClassFieldTheory_Reciprocity_IdeleClassDirectLimitFiniteLevelCore
private local instance q359TowerIdeleIsMulCommutative2.{w} (A B C : Type w) [Field A] [NumberField A]
    [Field B] [Field C] [Algebra A B] [Algebra B C] :
    IsMulCommutative (TowerRelativeIdeleGroup A B C) :=
  ⟨⟨fun a b => mul_comm a b⟩⟩
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 400000
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.GlobalClassFields.ConductorialSubgroup.finiteIndex _root_.GlobalClassFieldTheory.GlobalClassFields.bigHilbertClassFieldNormSubgroup_normal _root_.GlobalClassFieldTheory.GlobalClassFields.smallHilbertClassFieldNormSubgroupFiniteIndex _root_.GlobalClassFieldTheory.Reciprocity.complexFourthRootField_numberField _root_.GlobalClassFieldTheory.Reciprocity.infinitePlaceComplexificationOverfield_algebra _root_.GlobalClassFieldTheory.Reciprocity.infinitePlaceComplexificationOverfield_baseAlgebra _root_.GlobalClassFieldTheory.Reciprocity.infinitePlaceComplexificationOverfield_numberField _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.KummerTheory.primeCyclotomicBaseFiniteDimensional _root_.KummerTheory.primeCyclotomicBaseIsGalois _root_.KummerTheory.primeCyclotomicBaseNumberField _root_.KummerTheory.rationalCyclotomicLevel_numberField _root_.LocalClassFieldTheory.finiteGaloisLocalField_integerRing_moduleFinite _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.residueFieldZModAlgebra _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedIntegralAlgebraContextValuationSubringAlgebra _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedIntegralAlgebraContextValuationSubringTower _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedQPadicContextValuationSubringTower _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.boundedRealFields_numberField _root_.OAI.PrimeDegreePackets.diagonalLogAction _root_.OAI.PrimeDegreePackets.instNonemptyLeafTestSpace _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.CyclicCohomology.binaryCoefficientFamilyCommGroup _root_.CyclicCohomology.instMulDistribMulActionBinaryCoefficientFamily _root_.LocalClassFieldTheory.comparisonIntegerRingIsIntegralClosure _root_.LocalClassFieldTheory.normalizationIntegerRingIsIntegralClosure _root_.chosenFinitePlaceCompletionAlgebra _root_.chosenFinitePlaceCompletionFiniteDimensional _root_.chosenFinitePlaceLocalizedFiniteDimensional _root_.chosenFinitePlaceLocalizedIsGalois _root_.cyclicPrimeDegreeIntermediate_isGalois _root_.cyclicPrimeSubextension_isGalois _root_.relativeUnrestrictedSPlaceFactorCommGroup
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

/-!
# Finite levels of the rational idele-class direct limit

Normal closures, finite-level scalar extension, tower base change, and the
canonical embeddings into the rational idele-class direct limit.
-/

open scoped NumberField TensorProduct
open NumberField

noncomputable section

namespace GlobalClassFieldTheory
namespace Reciprocity

open CyclicCohomology

attribute [local instance]
  relativeAdeleRingIntermediateAlgebra

local instance rationalIntermediateNumberField
    (K : IntermediateField ℚ (SeparableClosure ℚ))
    [FiniteDimensional ℚ K] : NumberField K :=
  NumberField.of_module_finite ℚ K

/-- The canonical finite Galois closure, inside `SeparableClosure ℚ`,
of a finite rational intermediate field. -/
noncomputable def rationalNormalClosure
    (K : IntermediateField ℚ (SeparableClosure ℚ))
    [FiniteDimensional ℚ K] :
    FiniteGaloisIntermediateField ℚ (SeparableClosure ℚ) :=
  { IntermediateField.normalClosure
      ℚ K (SeparableClosure ℚ) with
    finiteDimensional :=
      normalClosure.is_finiteDimensional
        ℚ K (SeparableClosure ℚ)
    isGalois :=
      IsGalois.normalClosure ℚ K (SeparableClosure ℚ) }

/-- Embed the actual idele class group of a finite rational
intermediate field into the relative presentation at its canonical
finite Galois closure. -/
noncomputable def rationalIntermediateIdeleClassToNormalClosure
    (K : IntermediateField ℚ (SeparableClosure ℚ))
    [FiniteDimensional ℚ K] :
    IdeleClassGroup K →*
      RelativeIdeleGroup.ClassGroup ℚ (rationalNormalClosure K) :=
  (RelativeIdeleGroup.classEmbedding (IntermediateField.inclusion (IntermediateField.le_normalClosure K))).comp
    (_root_.relativeIdeleClassBaseChangeMulEquiv
      (K := ℚ) (L := K)).symm.toMonoidHom

/-- The canonical map from the actual idele class group of a finite
rational intermediate field to the absolute idele-class direct limit. -/
noncomputable def rationalIntermediateIdeleClassToDirectLimit
    (K : IntermediateField ℚ (SeparableClosure ℚ))
    [FiniteDimensional ℚ K] :
    IdeleClassGroup K →* rationalIdeleClassDirectLimit :=
  (rationalRelativeIdeleClassToDirectLimit
      (rationalNormalClosure K)).comp
    (rationalIntermediateIdeleClassToNormalClosure K)

/-- Passing from the relative presentation of a finite rational
intermediate field to its ordinary idele class group commutes with the
canonical map to the absolute direct limit. -/
theorem
    rationalIntermediateIdeleClassToDirectLimit_baseChange
    (K : IntermediateField ℚ (SeparableClosure ℚ))
    [FiniteDimensional ℚ K]
    (c : RelativeIdeleGroup.ClassGroup ℚ K) :
    rationalIntermediateIdeleClassToDirectLimit K
        (_root_.relativeIdeleClassBaseChangeMulEquiv
          (K := ℚ) (L := K) c) =
      rationalRelativeIdeleClassToDirectLimit
        (rationalNormalClosure K)
        (RelativeIdeleGroup.classEmbedding (IntermediateField.inclusion (IntermediateField.le_normalClosure K)) c) := by
  simp only [rationalIntermediateIdeleClassToDirectLimit,
    rationalIntermediateIdeleClassToNormalClosure]
  change
    rationalRelativeIdeleClassToDirectLimit
        (rationalNormalClosure K)
        (RelativeIdeleGroup.classEmbedding (IntermediateField.inclusion (IntermediateField.le_normalClosure K))
          ((_root_.relativeIdeleClassBaseChangeMulEquiv
            (K := ℚ) (L := K)).symm
            (_root_.relativeIdeleClassBaseChangeMulEquiv
              (K := ℚ) (L := K) c))) =
      rationalRelativeIdeleClassToDirectLimit
        (rationalNormalClosure K)
        (RelativeIdeleGroup.classEmbedding (IntermediateField.inclusion (IntermediateField.le_normalClosure K)) c)
  rw [(_root_.relativeIdeleClassBaseChangeMulEquiv
    (K := ℚ) (L := K)).symm_apply_apply]

/-- At a finite Galois rational intermediate field, the ordinary
idele-class comparison followed by the absolute direct-limit map is the
canonical finite-level map itself. -/
theorem
    rationalFiniteGaloisIdeleClassToDirectLimit_baseChange
    (E : FiniteGaloisIntermediateField ℚ (SeparableClosure ℚ))
    (c : RelativeIdeleGroup.ClassGroup ℚ E) :
    rationalIntermediateIdeleClassToDirectLimit
        (E : IntermediateField ℚ (SeparableClosure ℚ))
        (_root_.relativeIdeleClassBaseChangeMulEquiv
          (K := ℚ) (L := E) c) =
      rationalRelativeIdeleClassToDirectLimit E c := by
  rw [rationalIntermediateIdeleClassToDirectLimit_baseChange]
  exact rationalIdeleClassDirectLimit_mk_apply c
    (IntermediateField.le_normalClosure
      (E : IntermediateField ℚ (SeparableClosure ℚ)))


end Reciprocity
end GlobalClassFieldTheory
end
end

section
-- module Solutions.OAIQ244_DUKE.GlobalClassFieldTheory_Reciprocity_IdeleClassDirectLimitFiniteLevel
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 400000
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.GlobalClassFields.ConductorialSubgroup.finiteIndex _root_.GlobalClassFieldTheory.GlobalClassFields.bigHilbertClassFieldNormSubgroup_normal _root_.GlobalClassFieldTheory.GlobalClassFields.smallHilbertClassFieldNormSubgroupFiniteIndex _root_.GlobalClassFieldTheory.Reciprocity.complexFourthRootField_numberField _root_.GlobalClassFieldTheory.Reciprocity.infinitePlaceComplexificationOverfield_algebra _root_.GlobalClassFieldTheory.Reciprocity.infinitePlaceComplexificationOverfield_baseAlgebra _root_.GlobalClassFieldTheory.Reciprocity.infinitePlaceComplexificationOverfield_baseSmul _root_.GlobalClassFieldTheory.Reciprocity.infinitePlaceComplexificationOverfield_numberField _root_.GlobalClassFieldTheory.Reciprocity.infinitePlaceComplexificationOverfield_smul _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.KummerTheory.primeCyclotomicBaseFiniteDimensional _root_.KummerTheory.primeCyclotomicBaseNumberField _root_.KummerTheory.rationalCyclotomicLevel_numberField _root_.LocalClassFieldTheory.finiteGaloisLocalField_integerRing_moduleFinite _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.residueFieldZModAlgebra _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedIntegralAlgebraContextValuationSubringAlgebra _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedIntegralAlgebraContextValuationSubringTower _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedQPadicContextValuationSubringTower _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.boundedRealFields_numberField _root_.OAI.PrimeDegreePackets.diagonalLogAction _root_.OAI.PrimeDegreePackets.instNonemptyLeafTestSpace _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.CyclicCohomology.binaryCoefficientFamilyCommGroup _root_.CyclicCohomology.instMulDistribMulActionBinaryCoefficientFamily _root_.LocalClassFieldTheory.comparisonIntegerRingIsIntegralClosure _root_.LocalClassFieldTheory.normalizationIntegerRingIsIntegralClosure _root_.chosenFinitePlaceCompletionAlgebra _root_.chosenFinitePlaceCompletionFiniteDimensional _root_.chosenFinitePlaceLocalizedFiniteDimensional _root_.relativeUnrestrictedSPlaceFactorCommGroup
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

/-!
# Tensor comparison and injectivity at finite rational levels

This endpoint leaf contains the tensor-unflattening comparisons and the
resulting injectivity theorems.  The finite-level normal-closure maps and
their tower compatibility live in the reusable core leaf.
-/

open scoped NumberField TensorProduct
open NumberField

noncomputable section

namespace GlobalClassFieldTheory
namespace Reciprocity

open CyclicCohomology

attribute [local instance]
  relativeAdeleRingIntermediateAlgebra

private local instance rationalFiniteLevelTowerIdeleIsMulCommutative.{w} (A B C : Type w) [Field A] [NumberField A]
    [Field B] [Field C] [Algebra A B] [Algebra B C] :
    IsMulCommutative (TowerRelativeIdeleGroup A B C) :=
  ⟨⟨fun a b => mul_comm a b⟩⟩

local instance rationalFiniteLevelEndpointNumberField
    (K : IntermediateField ℚ (SeparableClosure ℚ))
    [FiniteDimensional ℚ K] : NumberField K :=
  NumberField.of_module_finite ℚ K
/-- Rational relative-adele scalar extension agrees with unflattening
the corresponding fixed-bottom tensor tower. -/
theorem rationalRelativeAdeleEmbedding_unflatten
    {K N : IntermediateField ℚ (SeparableClosure ℚ)}
    [FiniteDimensional ℚ K] [FiniteDimensional ℚ N]
    (hKN : K ≤ N)
    (a : RelativeAdeleRing ℚ K) :
    letI : Algebra K N :=
      (IntermediateField.inclusion hKN).toRingHom.toAlgebra
    letI : IsScalarTower ℚ K N :=
      IsScalarTower.of_algebraMap_eq' (RingHom.ext_rat _ _)
    letI : FiniteDimensional K N :=
      FiniteDimensional.right ℚ K N
    towerRelativeAdeleUnflatten ℚ K N
        (RelativeIdeleGroup.adeleEmbedding (K := ℚ) (L := K) (M := N)
          (IntermediateField.inclusion hKN) a) =
      a ⊗ₜ[K] (1 : N) := by
  let : Algebra K N :=
    (IntermediateField.inclusion hKN).toRingHom.toAlgebra
  let : IsScalarTower ℚ K N :=
    IsScalarTower.of_algebraMap_eq' (RingHom.ext_rat _ _)
  let : FiniteDimensional K N :=
    FiniteDimensional.right ℚ K N
  have hflatten :
      towerRelativeAdeleFlatten ℚ K N
          (towerRelativeAdeleUnflatten ℚ K N
            (RelativeIdeleGroup.adeleEmbedding (K := ℚ) (L := K) (M := N)
              (IntermediateField.inclusion hKN) a)) =
        RelativeIdeleGroup.adeleEmbedding (K := ℚ) (L := K) (M := N)
          (IntermediateField.inclusion hKN) a :=
    (towerRelativeAdeleRingEquiv ℚ K N).apply_symm_apply
      (RelativeIdeleGroup.adeleEmbedding (K := ℚ) (L := K) (M := N)
        (IntermediateField.inclusion hKN) a)
  apply
    (towerRelativeAdeleRingEquiv ℚ K N).injective
  change
    towerRelativeAdeleFlatten ℚ K N
        (towerRelativeAdeleUnflatten ℚ K N
          (RelativeIdeleGroup.adeleEmbedding (K := ℚ) (L := K) (M := N)
            (IntermediateField.inclusion hKN) a)) =
      towerRelativeAdeleFlatten ℚ K N
        (a ⊗ₜ[K] (1 : N))
  rw [hflatten]
  rw [towerRelativeAdeleFlatten_tmul]
  simp only [map_one, mul_one]
  rfl

/-- Rational relative-idele scalar extension agrees with unflattening
the corresponding fixed-bottom tensor tower. -/
theorem rationalRelativeIdeleEmbedding_unflatten
    {K N : IntermediateField ℚ (SeparableClosure ℚ)}
    [FiniteDimensional ℚ K] [FiniteDimensional ℚ N]
    (hKN : K ≤ N)
    (a : RelativeIdeleGroup ℚ K) :
    letI : Algebra K N :=
      (IntermediateField.inclusion hKN).toRingHom.toAlgebra
    letI : IsScalarTower ℚ K N :=
      IsScalarTower.of_algebraMap_eq' (RingHom.ext_rat _ _)
    letI : FiniteDimensional K N :=
      FiniteDimensional.right ℚ K N
    letI : Algebra K (RelativeAdeleRing ℚ K) :=
      relativeAdeleRingIntermediateAlgebra ℚ K
    (towerRelativeIdeleEquiv ℚ K N).symm
        (RelativeIdeleGroup.ideleEmbedding (K := ℚ) (L := K) (M := N)
          (IntermediateField.inclusion hKN) a) =
      (Units.map
        (@Algebra.TensorProduct.includeLeft
          K K (RelativeAdeleRing ℚ K) N
          inferInstance inferInstance
          (relativeAdeleRingIntermediateAlgebra ℚ K)
          inferInstance
          ((IntermediateField.inclusion hKN).toRingHom.toAlgebra)
          inferInstance
          (relativeAdeleRingIntermediateAlgebra ℚ K)
          (smulCommClass_self K (RelativeAdeleRing ℚ K))).toRingHom a :
        TowerRelativeIdeleGroup ℚ K N) := by
  let : Algebra K N :=
    (IntermediateField.inclusion hKN).toRingHom.toAlgebra
  let : IsScalarTower ℚ K N :=
    IsScalarTower.of_algebraMap_eq' (RingHom.ext_rat _ _)
  let : FiniteDimensional K N :=
    FiniteDimensional.right ℚ K N
  let : Algebra K (RelativeAdeleRing ℚ K) :=
    relativeAdeleRingIntermediateAlgebra ℚ K
  apply Units.ext
  exact
    rationalRelativeAdeleEmbedding_unflatten
      hKN (a : RelativeAdeleRing ℚ K)

/-- Rational relative idele-class scalar extension agrees with the
fixed-bottom tower base-change equivalence. -/
theorem
    rationalRelativeIdeleClassEmbedding_towerBaseChange
    {K N : IntermediateField ℚ (SeparableClosure ℚ)}
    [FiniteDimensional ℚ K] [FiniteDimensional ℚ N]
    (hKN : K ≤ N)
    (c : RelativeIdeleGroup.ClassGroup ℚ K) :
    letI : Algebra K N :=
      (IntermediateField.inclusion hKN).toRingHom.toAlgebra
    letI : IsScalarTower ℚ K N :=
      IsScalarTower.of_algebraMap_eq' (RingHom.ext_rat _ _)
    letI : FiniteDimensional K N :=
      FiniteDimensional.right ℚ K N
    towerRelativeIdeleClassBaseChangeMulEquiv ℚ K N
        ((TowerRelativeIdeleGroup.classGroupEquiv ℚ K N).symm
          (RelativeIdeleGroup.classEmbedding (K := ℚ) (L := K) (M := N)
            (IntermediateField.inclusion hKN) c)) =
      RelativeIdeleGroup.classInclusion K N
        (_root_.relativeIdeleClassBaseChangeMulEquiv
          (K := ℚ) (L := K) c) := by
  let : Algebra K N :=
    (IntermediateField.inclusion hKN).toRingHom.toAlgebra
  let : IsScalarTower ℚ K N :=
    IsScalarTower.of_algebraMap_eq' (RingHom.ext_rat _ _)
  let : FiniteDimensional K N :=
    FiniteDimensional.right ℚ K N
  refine QuotientGroup.induction_on c ?_
  intro a
  change
    QuotientGroup.mk'
        (RelativeIdeleGroup.principalSubgroup K N)
        (towerRelativeIdeleBaseChangeMulEquiv ℚ K N
          ((towerRelativeIdeleEquiv ℚ K N).symm
            (RelativeIdeleGroup.ideleEmbedding (K := ℚ) (L := K) (M := N)
              (IntermediateField.inclusion hKN) a))) =
      QuotientGroup.mk'
        (RelativeIdeleGroup.principalSubgroup K N)
        (RelativeIdeleGroup.inclusion K N
          (relativeIdeleBaseChangeMulEquiv
            (K := ℚ) (L := K) a))
  apply congrArg
    (QuotientGroup.mk'
      (RelativeIdeleGroup.principalSubgroup K N))
  rw [rationalRelativeIdeleEmbedding_unflatten hKN a]
  exact
    towerRelativeIdeleBaseChangeMulEquiv_includeLeft
      ℚ K N a

/-- Scalar extension between finite rational relative idele class groups
is injective. -/
theorem rationalRelativeIdeleClassEmbedding_injective
    {K N : IntermediateField ℚ (SeparableClosure ℚ)}
    [FiniteDimensional ℚ K] [FiniteDimensional ℚ N]
    (hKN : K ≤ N) :
    Function.Injective
      (RelativeIdeleGroup.classEmbedding (K := ℚ) (L := K) (M := N)
        (IntermediateField.inclusion hKN)) := by
  let : Algebra K N :=
    (IntermediateField.inclusion hKN).toRingHom.toAlgebra
  let : IsScalarTower ℚ K N :=
    IsScalarTower.of_algebraMap_eq' (RingHom.ext_rat _ _)
  let : FiniteDimensional K N :=
    FiniteDimensional.right ℚ K N
  intro a b hab
  have htransport :=
    congrArg
      (fun c : RelativeIdeleGroup.ClassGroup ℚ N =>
        towerRelativeIdeleClassBaseChangeMulEquiv ℚ K N
          ((TowerRelativeIdeleGroup.classGroupEquiv ℚ K N).symm c))
      hab
  rw [rationalRelativeIdeleClassEmbedding_towerBaseChange hKN a,
    rationalRelativeIdeleClassEmbedding_towerBaseChange hKN b]
      at htransport
  apply
    (_root_.relativeIdeleClassBaseChangeMulEquiv
      (K := ℚ) (L := K)).injective
  exact
    RelativeIdeleGroup.classInclusion_injective K N htransport

/-- Each finite-level relative idele class group embeds into the rational
idele-class direct limit. -/
theorem rationalRelativeIdeleClassToDirectLimit_injective
    (E : FiniteGaloisIntermediateField ℚ (SeparableClosure ℚ)) :
    Function.Injective
      (rationalRelativeIdeleClassToDirectLimit E) := by
  exact
    DirectLimit.mk_injective
      (F := fun E :
        FiniteGaloisIntermediateField ℚ (SeparableClosure ℚ) =>
          RelativeIdeleGroup.ClassGroup ℚ E)
      (f := fun _ _ h =>
        rationalRelativeIdeleClassTransition h)
      (fun _ _ h =>
        rationalRelativeIdeleClassEmbedding_injective h)
      E

end Reciprocity
end GlobalClassFieldTheory
end
end

section
-- module Solutions.OAIQ244_DUKE.GlobalClassFieldTheory_Reciprocity_IdeleClassDirectLimitFixedPointDescentCore
private local instance q359TowerIdeleIsMulCommutative0.{w} (A B C : Type w) [Field A] [NumberField A]
    [Field B] [Field C] [Algebra A B] [Algebra B C] :
    IsMulCommutative (TowerRelativeIdeleGroup A B C) :=
  ⟨⟨fun a b => mul_comm a b⟩⟩
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 400000
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.GlobalClassFields.ConductorialSubgroup.finiteIndex _root_.GlobalClassFieldTheory.GlobalClassFields.bigHilbertClassFieldNormSubgroup_normal _root_.GlobalClassFieldTheory.GlobalClassFields.smallHilbertClassFieldNormSubgroupFiniteIndex _root_.GlobalClassFieldTheory.Reciprocity.complexFourthRootField_numberField _root_.GlobalClassFieldTheory.Reciprocity.infinitePlaceComplexificationOverfield_algebra _root_.GlobalClassFieldTheory.Reciprocity.infinitePlaceComplexificationOverfield_baseAlgebra _root_.GlobalClassFieldTheory.Reciprocity.infinitePlaceComplexificationOverfield_baseSmul _root_.GlobalClassFieldTheory.Reciprocity.infinitePlaceComplexificationOverfield_numberField _root_.GlobalClassFieldTheory.Reciprocity.infinitePlaceComplexificationOverfield_smul _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.KummerTheory.primeCyclotomicBaseNumberField _root_.KummerTheory.rationalCyclotomicLevel_numberField _root_.LocalClassFieldTheory.finiteGaloisLocalField_integerRing_moduleFinite _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.residueFieldZModAlgebra _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedIntegralAlgebraContextValuationSubringAlgebra _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedIntegralAlgebraContextValuationSubringTower _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedQPadicContextValuationSubringTower _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.boundedRealFields_numberField _root_.OAI.PrimeDegreePackets.diagonalLogAction _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.CyclicCohomology.binaryCoefficientFamilyCommGroup _root_.LocalClassFieldTheory.comparisonIntegerRingIsIntegralClosure _root_.LocalClassFieldTheory.normalizationIntegerRingIsIntegralClosure _root_.chosenFinitePlaceCompletionAlgebra _root_.relativeUnrestrictedSPlaceFactorCommGroup
attribute [-simp] _root_.GlobalClassFieldTheory.ClassFieldAxiom.actualPushoutNormQuotientMap_mk _root_.GlobalClassFieldTheory.ClassFieldAxiom.sUnitEquivSupportedPrincipalIdeleSubgroup_coe _root_.GlobalClassFieldTheory.GlobalClassFields.bigHilbertClassFieldQuotientEquivNarrowClassGroup_mk _root_.GlobalClassFieldTheory.GlobalClassFields.bigHilbertClassFieldQuotientToSmallHilbertClassFieldQuotient_mk _root_.GlobalClassFieldTheory.GlobalClassFields.realSignToBigHilbertClassFieldQuotient_apply _root_.GlobalClassFieldTheory.GlobalClassFields.realSignToNarrowClassKernel_apply _root_.GlobalClassFieldTheory.GlobalClassFields.smallHilbertClassFieldQuotientEquivClassGroup_mk _root_.GlobalClassFieldTheory.IdealClassFieldTheory.smallHilbertClassFieldIdeleExtensionMap_mk' _root_.GlobalClassFieldTheory.Reciprocity.globalNormClassFromIdele_principalIdele _root_.GlobalClassFieldTheory.Reciprocity.infinitePlaceGlobalArtinMonoidHom_finitePlaceIdele _root_.IdeleClassGroup.normOneNorm_apply _root_.IdeleGroup.count_fractionalIdeal _root_.IdeleGroup.finitePlaceIdele_finiteComponent_of_ne _root_.IdeleGroup.finitePlaceIdele_finiteComponent_same _root_.IdeleGroup.finitePlaceIdele_infiniteComponent _root_.IdeleGroup.ideleNormContinuousMonoidHom_apply _root_.IdeleGroup.infinitePlaceIdeleContinuous_apply _root_.IdeleGroup.infinitePlaceIdele_finiteComponent _root_.IdeleGroup.infinitePlaceIdele_infiniteComponent_of_ne _root_.IdeleGroup.infinitePlaceIdele_infiniteComponent_same _root_.IsDiscreteValuationRing.addVal_ringEquiv _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.OAI.PrimeDegreePackets.ThetaConstruction.schwartzCM_apply _root_.RayClass.primesEquiv_val_eq_natGenerator _root_.RayClass.signToNarrow_mk _root_.RelativeIdeleGroup.relativeFinitePlaceIdele_finiteComponent_of_ne _root_.RelativeIdeleGroup.relativeFinitePlaceIdele_finiteComponent_same _root_.RelativeIdeleGroup.relativeFinitePlaceIdele_infiniteComponent _root_.RelativeIdeleGroup.relativeInfinitePlaceIdele_finiteComponent _root_.RelativeIdeleGroup.relativeInfinitePlaceIdele_infiniteComponent_of_ne _root_.RelativeIdeleGroup.relativeInfinitePlaceIdele_infiniteComponent_same _root_.IdeleGroup.idealClass_classRepresentative _root_.finiteIdeleOfSPlaceFactors_apply_mem _root_.finiteIdeleOfSPlaceFactors_apply_notMem _root_.ideleClassCongr_ideleClassNorm _root_.ideleClassCongr_refl _root_.ideleSupportedAtEquivSPlaceFactors_infinite _root_.ideleSupportedAtEquivSPlaceFactors_inside _root_.ideleSupportedAtEquivSPlaceFactors_outside_coe _root_.relativeIdeleClassBaseChangeMulEquiv_congrOfAlgEquiv
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

/-!
# Descent of fixed rational idele classes

An element of the rational idele-class direct limit which is fixed over a
finite intermediate field is represented at a finite Galois level.  Its
actual tower base change is Galois-fixed, hence descends to an idele class
of the intermediate field.
-/

noncomputable section

namespace GlobalClassFieldTheory
namespace Reciprocity

private local instance rationalFixedPointDescentTowerIdeleIsMulCommutative.{w} (A B C : Type w) [Field A] [NumberField A]
    [Field B] [Field C] [Algebra A B] [Algebra B C] :
    IsMulCommutative (TowerRelativeIdeleGroup A B C) :=
  ⟨⟨fun a b => mul_comm a b⟩⟩

/-- An algebra structure on nested rational intermediate fields is the
canonical one induced by intermediate-field inclusion whenever its algebra
map agrees with the ambient inclusions. -/
theorem rationalIntermediateField_algebra_eq_inclusion
    (K : IntermediateField ℚ (SeparableClosure ℚ))
    (U : FiniteGaloisIntermediateField ℚ (SeparableClosure ℚ))
    [Algebra K U]
    (hKU :
      K ≤ (U : IntermediateField ℚ (SeparableClosure ℚ)))
    (h_algebraMap : ∀ x : K,
      ((algebraMap K U x : U) : SeparableClosure ℚ) =
        (x : SeparableClosure ℚ)) :
    (inferInstance : Algebra K U) =
      (IntermediateField.inclusion hKU).toRingHom.toAlgebra := by
  apply Algebra.algebra_ext
  intro x
  apply Subtype.ext
  exact h_algebraMap x

/-- The actual tower comparison from rational relative idele classes at `U`
to relative idele classes over the intermediate field `K`. -/
noncomputable def rationalRelativeIdeleClassTowerBaseChangeEquiv
    (K : IntermediateField ℚ (SeparableClosure ℚ))
    [FiniteDimensional ℚ K]
    (U : FiniteGaloisIntermediateField ℚ (SeparableClosure ℚ))
    [Algebra K U]
    [IsScalarTower ℚ K U]
    [FiniteDimensional K U]
    [IsGalois K U] :
    RelativeIdeleGroup.ClassGroup ℚ U ≃*
      RelativeIdeleGroup.ClassGroup K U :=
  (TowerRelativeIdeleGroup.classGroupEquiv
    ℚ K U).symm.trans
      (towerRelativeIdeleClassBaseChangeMulEquiv ℚ K U)

/-- The actual idele class group of `K`, identified with the subgroup of
relative idele classes at `U` fixed by `Gal(U/K)`. This transports the
Herbrand fixed-subgroup target of `baseIdeleClassEquivFixed` to the concrete
Galois-fixed subgroup. -/
noncomputable def rationalIntermediateIdeleClassEquivGaloisFixed
    (K : IntermediateField ℚ (SeparableClosure ℚ))
    [FiniteDimensional ℚ K]
    (U : FiniteGaloisIntermediateField ℚ (SeparableClosure ℚ))
    [Algebra K U]
    [IsScalarTower ℚ K U]
    [FiniteDimensional K U]
    [IsGalois K U] :
    IdeleClassGroup K ≃*
      RelativeIdeleGroup.galoisFixedClassSubgroup K U := by
  letI :
      MulDistribMulAction (U ≃ₐ[K] U)
        (RelativeIdeleGroup.ClassGroup K U) :=
    RelativeIdeleGroup.Cohomology.ideleClassMulDistribMulAction K U
  exact
    (RelativeIdeleGroup.Cohomology.baseIdeleClassEquivFixed K U).trans
      (MulEquiv.subgroupCongr
        (RelativeIdeleGroup.Cohomology.ideleClass_fixedSubgroup_eq_galoisFixed
          K U))

/-- Under the concrete fixed-point equivalence, an idele class maps to its
actual relative class inclusion. -/
@[simp]
theorem rationalIntermediateIdeleClassEquivGaloisFixed_coe
    (K : IntermediateField ℚ (SeparableClosure ℚ))
    [FiniteDimensional ℚ K]
    (U : FiniteGaloisIntermediateField ℚ (SeparableClosure ℚ))
    [Algebra K U]
    [IsScalarTower ℚ K U]
    [FiniteDimensional K U]
    [IsGalois K U]
    (q : IdeleClassGroup K) :
    ((rationalIntermediateIdeleClassEquivGaloisFixed K U q :
        RelativeIdeleGroup.galoisFixedClassSubgroup K U) :
      RelativeIdeleGroup.ClassGroup K U) =
        RelativeIdeleGroup.classInclusion K U q := by
  let :
      MulDistribMulAction (U ≃ₐ[K] U)
        (RelativeIdeleGroup.ClassGroup K U) :=
    RelativeIdeleGroup.Cohomology.ideleClassMulDistribMulAction K U
  change
    ((RelativeIdeleGroup.Cohomology.baseIdeleClassEquivFixed K U q :
        CyclicCohomology.ProfiniteCohomology.Herbrand.fixedSubgroup
          (U ≃ₐ[K] U)
          (RelativeIdeleGroup.ClassGroup K U)) :
      RelativeIdeleGroup.ClassGroup K U) =
        RelativeIdeleGroup.classInclusion K U q
  exact
    RelativeIdeleGroup.Cohomology.baseIdeleClassEquivFixed_coe K U q


end Reciprocity
end GlobalClassFieldTheory
end
end

section
-- module Solutions.OAIQ244_DUKE.GlobalClassFieldTheory_Reciprocity_IdeleClassDirectLimitFixedPoints
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 400000
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.GlobalClassFields.ConductorialSubgroup.finiteIndex _root_.GlobalClassFieldTheory.GlobalClassFields.bigHilbertClassFieldNormSubgroup_normal _root_.GlobalClassFieldTheory.GlobalClassFields.smallHilbertClassFieldNormSubgroupFiniteIndex _root_.GlobalClassFieldTheory.Reciprocity.complexFourthRootField_numberField _root_.GlobalClassFieldTheory.Reciprocity.infinitePlaceComplexificationOverfield_algebra _root_.GlobalClassFieldTheory.Reciprocity.infinitePlaceComplexificationOverfield_baseAlgebra _root_.GlobalClassFieldTheory.Reciprocity.infinitePlaceComplexificationOverfield_numberField _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.KummerTheory.primeCyclotomicBaseIsGalois _root_.KummerTheory.primeCyclotomicBaseNumberField _root_.KummerTheory.rationalCyclotomicLevel_numberField _root_.LocalClassFieldTheory.finiteGaloisLocalField_integerRing_moduleFinite _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.residueFieldZModAlgebra _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedIntegralAlgebraContextValuationSubringAlgebra _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedIntegralAlgebraContextValuationSubringTower _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedQPadicContextValuationSubringTower _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.boundedRealFields_numberField _root_.OAI.PrimeDegreePackets.diagonalLogAction _root_.OAI.PrimeDegreePackets.instNonemptyLeafTestSpace _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.CyclicCohomology.binaryCoefficientFamilyCommGroup _root_.CyclicCohomology.instMulDistribMulActionBinaryCoefficientFamily _root_.LocalClassFieldTheory.comparisonIntegerRingIsIntegralClosure _root_.LocalClassFieldTheory.normalizationIntegerRingIsIntegralClosure _root_.chosenFinitePlaceCompletionAlgebra _root_.chosenFinitePlaceLocalizedIntegerAlgebra _root_.chosenFinitePlaceLocalizedIsGalois _root_.cyclicPrimeDegreeIntermediate_isGalois _root_.cyclicPrimeSubextension_isGalois _root_.relativeUnrestrictedSPlaceFactorCommGroup
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

/-!
# Fixed points of the rational idele-class direct limit

The actual idele class group of a finite rational intermediate field is
identified with the corresponding fixed subgroup of the direct limit.
-/

noncomputable section

namespace GlobalClassFieldTheory
namespace Reciprocity

/-- Scalar extension of a rational relative adele is fixed by every
absolute Galois element fixing the source field. -/
theorem
    rationalRelativeAdeleEmbedding_fixed_of_mem_fixingSubgroup
    {K : IntermediateField ℚ (SeparableClosure ℚ)}
    [FiniteDimensional ℚ K]
    {N : FiniteGaloisIntermediateField ℚ (SeparableClosure ℚ)}
    (hKN : K ≤ (N :
      IntermediateField ℚ (SeparableClosure ℚ)))
    (σ : SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ)
    (hσ : σ ∈ K.fixingSubgroup)
    (z : RelativeAdeleRing ℚ K) :
    RelativeIdeleGroup.conjugation ℚ N
        (AlgEquiv.restrictNormalHom N σ)
        (RelativeIdeleGroup.adeleEmbedding (K := ℚ) (L := K) (M := N)
          (IntermediateField.inclusion hKN) z) =
      RelativeIdeleGroup.adeleEmbedding (K := ℚ) (L := K) (M := N)
        (IntermediateField.inclusion hKN) z := by
  induction z using OAI.tensorInductionOn with
  | tmul a x =>
      simp only [RelativeIdeleGroup.adeleEmbedding,
        RelativeIdeleGroup.scalarEmbedding_tmul,
        RelativeIdeleGroup.conjugation_tmul]
      congr 1
      apply Subtype.ext
      calc
        (((AlgEquiv.restrictNormalHom N σ)
              (IntermediateField.inclusion hKN x) : N) :
            SeparableClosure ℚ) =
            σ ((IntermediateField.inclusion hKN x : N) :
              SeparableClosure ℚ) :=
          AlgEquiv.restrictNormal_commutes σ N
            (IntermediateField.inclusion hKN x)
        _ = σ (x : SeparableClosure ℚ) := rfl
        _ = (x : SeparableClosure ℚ) :=
          (IntermediateField.mem_fixingSubgroup_iff K σ).1
            hσ x.1 x.2
        _ = ((IntermediateField.inclusion hKN x : N) :
            SeparableClosure ℚ) := rfl
  | add x y hx hy =>
      simp only [map_add, hx, hy]

/-- Scalar extension of a rational relative idele class is fixed by every
absolute Galois element fixing the source field. -/
theorem
    rationalRelativeIdeleClassEmbedding_fixed_of_mem_fixingSubgroup
    {K : IntermediateField ℚ (SeparableClosure ℚ)}
    [FiniteDimensional ℚ K]
    {N : FiniteGaloisIntermediateField ℚ (SeparableClosure ℚ)}
    (hKN : K ≤ (N :
      IntermediateField ℚ (SeparableClosure ℚ)))
    (σ : SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ)
    (hσ : σ ∈ K.fixingSubgroup)
    (c : RelativeIdeleGroup.ClassGroup ℚ K) :
    σ • RelativeIdeleGroup.classEmbedding (K := ℚ) (L := K) (M := N)
        (IntermediateField.inclusion hKN) c =
      RelativeIdeleGroup.classEmbedding (K := ℚ) (L := K) (M := N)
        (IntermediateField.inclusion hKN) c := by
  refine QuotientGroup.induction_on c ?_
  intro a
  change
    QuotientGroup.mk'
        (RelativeIdeleGroup.principalSubgroup ℚ N)
        ((AlgEquiv.restrictNormalHom N σ) •
          RelativeIdeleGroup.ideleEmbedding (K := ℚ) (L := K) (M := N)
            (IntermediateField.inclusion hKN) a) =
      QuotientGroup.mk'
        (RelativeIdeleGroup.principalSubgroup ℚ N)
        (RelativeIdeleGroup.ideleEmbedding (K := ℚ) (L := K) (M := N)
          (IntermediateField.inclusion hKN) a)
  apply congrArg
    (QuotientGroup.mk'
      (RelativeIdeleGroup.principalSubgroup ℚ N))
  apply Units.ext
  exact
    rationalRelativeAdeleEmbedding_fixed_of_mem_fixingSubgroup
      hKN σ hσ (a : RelativeAdeleRing ℚ K)

/-- The image in the direct limit of an idele class over `K` is fixed by
the absolute Galois subgroup fixing `K`. -/
theorem rationalIntermediateIdeleClassToDirectLimit_fixed
    (K : IntermediateField ℚ (SeparableClosure ℚ))
    [FiniteDimensional ℚ K]
    (c : IdeleClassGroup K)
    (σ : SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ)
    (hσ : σ ∈ K.fixingSubgroup) :
    σ • rationalIntermediateIdeleClassToDirectLimit K c =
      rationalIntermediateIdeleClassToDirectLimit K c := by
  let N : FiniteGaloisIntermediateField ℚ (SeparableClosure ℚ) :=
    rationalNormalClosure K
  let hKN : K ≤ (N : IntermediateField ℚ (SeparableClosure ℚ)) :=
    IntermediateField.le_normalClosure K
  let : SMul
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ)
      (RelativeIdeleGroup.ClassGroup ℚ N) :=
    (rationalAbsoluteGaloisIdeleClassAction
      N).toSMul
  let d : RelativeIdeleGroup.ClassGroup ℚ K :=
    (_root_.relativeIdeleClassBaseChangeMulEquiv
      (K := ℚ) (L := K)).symm c
  have hd :
      _root_.relativeIdeleClassBaseChangeMulEquiv
          (K := ℚ) (L := K) d = c := by
    simp only [d,
      (_root_.relativeIdeleClassBaseChangeMulEquiv
        (K := ℚ) (L := K)).apply_symm_apply]
  have hfixed :
      σ • RelativeIdeleGroup.classEmbedding (K := ℚ) (L := K) (M := N)
          (IntermediateField.inclusion hKN) d =
        RelativeIdeleGroup.classEmbedding (K := ℚ) (L := K) (M := N)
          (IntermediateField.inclusion hKN) d :=
    rationalRelativeIdeleClassEmbedding_fixed_of_mem_fixingSubgroup
      hKN σ hσ d
  have hlimit_smul :
      σ • rationalRelativeIdeleClassToDirectLimit N
          (RelativeIdeleGroup.classEmbedding (K := ℚ) (L := K) (M := N)
            (IntermediateField.inclusion hKN) d) =
        rationalRelativeIdeleClassToDirectLimit N
          (σ • RelativeIdeleGroup.classEmbedding (K := ℚ) (L := K) (M := N)
            (IntermediateField.inclusion hKN) d) := by
    exact DirectLimit.smul_def _ _ _
  calc
    σ • rationalIntermediateIdeleClassToDirectLimit K c =
      σ • rationalIntermediateIdeleClassToDirectLimit K
        (_root_.relativeIdeleClassBaseChangeMulEquiv
          (K := ℚ) (L := K) d) := by
        rw [hd]
    _ = σ • rationalRelativeIdeleClassToDirectLimit N
        (RelativeIdeleGroup.classEmbedding (K := ℚ) (L := K) (M := N)
          (IntermediateField.inclusion hKN) d) := by
        convert congrArg (fun z => σ • z)
          (rationalIntermediateIdeleClassToDirectLimit_baseChange K d) using 1
        all_goals try with_reducible_and_instances rfl
        simp only [N, rationalNormalClosure]
        congr 4
    _ = rationalRelativeIdeleClassToDirectLimit N
        (σ • RelativeIdeleGroup.classEmbedding (K := ℚ) (L := K) (M := N)
          (IntermediateField.inclusion hKN) d) :=
      hlimit_smul
    _ = rationalRelativeIdeleClassToDirectLimit N
        (RelativeIdeleGroup.classEmbedding (K := ℚ) (L := K) (M := N)
          (IntermediateField.inclusion hKN) d) :=
      congrArg
        (rationalRelativeIdeleClassToDirectLimit N) hfixed
    _ = rationalIntermediateIdeleClassToDirectLimit K
        (_root_.relativeIdeleClassBaseChangeMulEquiv
          (K := ℚ) (L := K) d) :=
      by
        convert
          (rationalIntermediateIdeleClassToDirectLimit_baseChange K d).symm
            using 1
        all_goals try with_reducible_and_instances rfl
        simp only [N, rationalNormalClosure]
        congr 4
    _ = rationalIntermediateIdeleClassToDirectLimit K c := by
      rw [hd]

end Reciprocity
end GlobalClassFieldTheory
end
end

section
-- module Solutions.OAIQ244_DUKE.GlobalClassFieldTheory_Reciprocity_IdeleClassDirectLimitAbstractFixedField
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 400000
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.GlobalClassFields.finiteAbelianSubextensionAbstractRelativeFixedFieldFiniteDimensional _root_.GlobalClassFieldTheory.GlobalClassFields.finiteAbelianSubextensionAbstractRelativeFixedFieldIsAbelianGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.KummerTheory.primeCyclotomicBaseIsGalois _root_.KummerTheory.primeCyclotomicBaseNumberField _root_.LocalClassFieldTheory.finiteGaloisLocalField_integerRing_moduleFinite _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.residueFieldZModAlgebra _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedIntegralAlgebraContextValuationSubringAlgebra _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedIntegralAlgebraContextValuationSubringTower _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedQPadicContextValuationSubringTower _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.LubinTate.compatibleGroupFamiliesGroup _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.instTopologicalSpaceLocalAlgebra _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.LocalClassFieldTheory.comparisonIntegerRingIsIntegralClosure _root_.LocalClassFieldTheory.normalizationIntegerRingIsIntegralClosure _root_.chosenFinitePlaceCompletionAlgebra _root_.chosenFinitePlaceLocalizedIsGalois _root_.cyclicPrimeDegreeIntermediate_isGalois _root_.cyclicPrimeSubextension_isGalois
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

/-!
# Abstract fixed fields in the rational idele-class representation

Fixed-point comparisons for finite-index closed subgroups and their actual
abstract fixed fields.
-/

noncomputable section

namespace GlobalClassFieldTheory
namespace Reciprocity

open ClassFormation
open CyclicCohomology

noncomputable instance instNumberFieldSubtypeSeparableClosureRatMemIntermediateFieldAbstractFixedFieldOfFiniteQuotientAlgEquivSubgroupBaseFieldExtensionSubgroup
    (K : ClosedSubgroup
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
    [hfinite : Finite
      ((baseField
        (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ)).toSubgroup ⧸
        extensionSubgroup
          (baseField
            (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
          K (le_baseField K))] :
    NumberField
      (LocalClassFieldTheory.abstractFixedField
        ℚ (SeparableClosure ℚ) K) := by
  let : FiniteDimensional ℚ
      (LocalClassFieldTheory.abstractFixedField
        ℚ (SeparableClosure ℚ) K) :=
    LocalClassFieldTheory.abstractFixedField_finiteDimensional
      ℚ (SeparableClosure ℚ) K hfinite
  exact
    NumberField.of_module_finite ℚ
      (LocalClassFieldTheory.abstractFixedField
        ℚ (SeparableClosure ℚ) K)

end Reciprocity
end GlobalClassFieldTheory
end
end

section
-- module Solutions.OAIQ244_DUKE.GlobalClassFieldTheory_Reciprocity_IdeleClassDirectLimitExtension
private local instance q359TowerIdeleIsMulCommutative3.{w} (A B C : Type w) [Field A] [NumberField A]
    [Field B] [Field C] [Algebra A B] [Algebra B C] :
    IsMulCommutative (TowerRelativeIdeleGroup A B C) :=
  ⟨⟨fun a b => mul_comm a b⟩⟩
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 400000
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalClassFieldTheory.finiteGaloisLocalField_integerRing_moduleFinite _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.residueFieldZModAlgebra _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedIntegralAlgebraContextValuationSubringAlgebra _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.CyclicCohomology.binaryCoefficientFamilyCommGroup _root_.LocalClassFieldTheory.comparisonIntegerRingIsIntegralClosure _root_.LocalClassFieldTheory.normalizationIntegerRingIsIntegralClosure _root_.chosenFinitePlaceCompletionAlgebra _root_.relativeUnrestrictedSPlaceFactorCommGroup
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

/-!
# Finite extensions in the rational idele-class representation

The fixed representation of a finite abstract extension is compared with
the relative idele class group of its two actual fixed fields.
-/

noncomputable section

namespace GlobalClassFieldTheory
namespace Reciprocity

open ClassFormation
open LocalClassFieldTheory
open CyclicCohomology

noncomputable instance
    rationalAbstractRelativeClassGroupCommGroup
    (F E : Type)
    [Field F] [NumberField F]
    [Field E] [NumberField E]
    [Algebra F E] [FiniteDimensional F E] :
    CommGroup (RelativeIdeleGroup.ClassGroup F E) := by
  letI : CommGroup (RelativeIdeleGroup F E) :=
    inferInstance
  exact
    QuotientGroup.Quotient.commGroup
      (RelativeIdeleGroup.principalSubgroup F E)

noncomputable instance
    rationalAbstractRelativeClassGroupMul
    (F E : Type)
    [Field F] [NumberField F]
    [Field E] [NumberField E]
    [Algebra F E] [FiniteDimensional F E] :
    Mul (RelativeIdeleGroup.ClassGroup F E) :=
  (rationalAbstractRelativeClassGroupCommGroup F E).toMul

noncomputable instance
    rationalAbstractRelativeClassGroupMulOneClass
    (F E : Type)
    [Field F] [NumberField F]
    [Field E] [NumberField E]
    [Algebra F E] [FiniteDimensional F E] :
    MulOneClass (RelativeIdeleGroup.ClassGroup F E) :=
  (rationalAbstractRelativeClassGroupCommGroup F E).toMulOneClass

end Reciprocity
end GlobalClassFieldTheory
end
end

section
-- module Solutions.OAIQ244_DUKE.GlobalClassFieldTheory_Reciprocity_OnePlaceNormKernel
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.GlobalClassFields.ConductorialSubgroup.finiteIndex _root_.GlobalClassFieldTheory.GlobalClassFields.bigHilbertClassFieldNormSubgroup_normal _root_.GlobalClassFieldTheory.GlobalClassFields.smallHilbertClassFieldNormSubgroupFiniteIndex _root_.GlobalClassFieldTheory.Reciprocity.rationalIdeleClassDirectLimitMonoid _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalClassFieldTheory.finiteGaloisLocalField_integerRing_moduleFinite _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.residueFieldZModAlgebra _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedIntegralAlgebraContextValuationSubringAlgebra _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.GlobalClassFieldTheory.Reciprocity.instMonoidClassGroupRatSubtypeSeparableClosureMemIntermediateField _root_.GlobalClassFieldTheory.Reciprocity.rationalAbstractRelativeClassGroupMulOneClass _root_.LocalClassFieldTheory.comparisonIntegerRingIsIntegralClosure _root_.LocalClassFieldTheory.normalizationIntegerRingIsIntegralClosure _root_.chosenFinitePlaceCompletionAlgebra
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

/-!
# The one-place norm kernel

At the source level, the key calculation is that an idele supported at one
finite place is a global relative-idele norm exactly when its local component
is a norm from the corresponding local tensor algebra.  The determinant-norm
comparison then identifies this image with the norm group of any chosen
completion above the place.
-/

open scoped NumberField TensorProduct
open NumberField IsDedekindDomain
open IdeleGroup RelativeIdeleGroup

noncomputable section

namespace GlobalClassFieldTheory
namespace Reciprocity

variable
    {K L : Type}
    [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]

omit [NumberField L] [IsGalois K L] in
/-- Exact one-place intersection before quotienting by principal ideles:

`N(I_L) ∩ K_vˣ = N((K_v ⊗_K L)ˣ)`.
-/
theorem finitePlaceIdele_mem_ideleNormSubgroup_iff
    (v : HeightOneSpectrum (𝓞 K))
    (x : (v.adicCompletion K)ˣ) :
    finitePlaceIdele v x ∈
        ideleNormSubgroup (K := K) (L := L) ↔
      x ∈ (localTensorNorm (K := K) (L := L) v).range := by
  constructor
  · rintro ⟨a, ha⟩
    refine
      ⟨RelativeIdeleGroup.finiteComponent
          (K := K) (L := L) v a, ?_⟩
    have hcomponent :=
      congrArg (IdeleGroup.finiteComponent v) ha
    rw [RelativeIdeleGroup.finiteComponent_norm,
      finitePlaceIdele_finiteComponent_same] at hcomponent
    exact hcomponent
  · rintro ⟨z, rfl⟩
    exact
      ⟨relativeFinitePlaceIdele
          (K := K) (L := L) v z,
        norm_relativeFinitePlaceIdele
          (K := K) (L := L) v z⟩

end Reciprocity
end GlobalClassFieldTheory
end
end

section
-- module Solutions.OAIQ244_DUKE.LocalClassFieldTheory_Finite_LocalReciprocity_UnramifiedComparison
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.infinitePlaceComplexificationOverfield_algebra _root_.GlobalClassFieldTheory.Reciprocity.infinitePlaceComplexificationOverfield_baseAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalIdeleClassDirectLimitSMul _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.residueFieldZModAlgebra _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedIntegralAlgebraContextValuationSubringAlgebra _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedIntegralAlgebraContextValuationSubringTower _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedQPadicContextValuationSubringTower _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.instTopologicalSpaceLocalAlgebra _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.RayClass.approximationCompletionTopologicalSpace _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.GlobalClassFieldTheory.Reciprocity.instSMulAlgEquivRatSeparableClosureClassGroupSubtypeMemIntermediateField _root_.GlobalClassFieldTheory.Reciprocity.rationalAbstractRelativeClassGroupMul _root_.LocalClassFieldTheory.normalizationIntegerRingIsIntegralClosure _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.adicCompletionProperSpace _root_.chosenFinitePlaceCompletionAlgebra _root_.finiteLocalUnitsOpen _root_.infiniteAdeleRingT2Space _root_.relativeAdeleRingIntermediateAlgebra _root_.relativeAdeleRingTopIntermediateAlgebra
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

/-!
# Abstract and concrete unramified Frobenius

This module compares the residue-degree construction on a fixed separable
closure with the ordinary unramified valuation extension and its arithmetic
Frobenius.
-/

noncomputable section

namespace LocalClassFieldTheory

open scoped ValuativeRel
open LocalFieldTheory RamificationTheory CyclicCohomology KummerTheory
open ClassFormation
open RamificationTheory.HilbertRamification.ValuationSubring


section BaseResidueDegree

variable (K : Type) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]

theorem finiteResidueAbstractBase_residueDegree_eq_one :
    ((finiteResidueAbstractBase K).residueDegree : ℕ) = 1 := by
  change ((intrinsicFiniteAbstractBase K).residueDegree (localResidueDatum K) : ℕ) = 1
  exact intrinsicFiniteAbstractBase_residueDegree_eq_one K

end BaseResidueDegree

end LocalClassFieldTheory
end
end

section
-- module Solutions.OAIQ244_DUKE.GlobalClassFieldTheory_Reciprocity_RationalCyclotomicFinitePlace
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.complexFourthRootField_numberField _root_.GlobalClassFieldTheory.Reciprocity.infinitePlaceComplexificationOverfield_numberField _root_.GlobalClassFieldTheory.Reciprocity.rationalCyclotomicCompletionAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalCyclotomicLocalizedCompletionFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalCyclotomicLocalizedCompletionIsAlgebraic _root_.GlobalClassFieldTheory.Reciprocity.rationalIntermediateFieldAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalIntermediateFieldNumberField _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.KummerTheory.primeCyclotomicBaseFiniteDimensional _root_.KummerTheory.primeCyclotomicBaseIsGalois _root_.KummerTheory.primeCyclotomicBaseNumberField _root_.KummerTheory.rationalCyclotomicField_hasEnoughRootsOfUnity _root_.KummerTheory.rationalCyclotomicTorsionFixedField_isAbelianGalois _root_.KummerTheory.rationalCyclotomicTorsionFixedField_isGalois _root_.KummerTheory.rationalCyclotomicTorsionFixedField_isIntegral _root_.KummerTheory.rationalCyclotomicTorsionFixedField_normal _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.residueFieldZModAlgebra _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedIntegralAlgebraContextValuationSubringAlgebra _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.boundedRealFields_numberField _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.GlobalClassFieldTheory.Reciprocity.instNumberFieldSubtypeSeparableClosureRatMemIntermediateFieldAbstractFixedFieldOfFiniteQuotientAlgEquivSubgroupBaseFieldExtensionSubgroup _root_.LocalClassFieldTheory.normalizationIntegerRingIsIntegralClosure
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

/-!
# Unramified finite places of rational cyclotomic levels

This file connects the cyclotomic ramification-index formula over `ℤ`
to the finite-place completions used by the global Artin map.  A rational
prime outside the conductor is unramified at the actual chosen extension
of its normalized finite-place absolute value.
-/

open scoped NumberField
open NumberField IsDedekindDomain

noncomputable section

namespace GlobalClassFieldTheory
namespace Reciprocity

attribute [local instance] GlobalClassFieldTheory.Reciprocity.instFactPrimeValNat_solutions
/-- A rational cyclotomic level is unramified at every chosen finite
place whose underlying rational prime does not divide the level. -/
theorem rationalCyclotomicLevel_chosenFinitePlaceIsUnramified
    (m : ℕ+) (q : Nat.Primes)
    (hq : ¬ q.1 ∣ (m : ℕ)) :
    ChosenFinitePlaceIsUnramified
      (K := ℚ)
      (L := KummerTheory.rationalCyclotomicLevel m)
      (RayClass.rationalPrime q) := by
  apply chosenFinitePlaceIsUnramified_of_isUnramifiedAt
  exact
    rationalCyclotomicLevel_isUnramifiedAt_chosenFinitePlaceCentre
      m q hq

end Reciprocity
end GlobalClassFieldTheory
end
end

section
-- module Solutions.OAIQ244_DUKE.LocalClassFieldTheory_Finite_LocalReciprocity_UnramifiedNormComparison
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 400000
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.GlobalClassFields.bigHilbertClassFieldNormSubgroup_normal _root_.GlobalClassFieldTheory.Reciprocity.rationalIdeleClassDirectLimitMonoid _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalClassFieldTheory.finiteGaloisLocalField_integerRing_moduleFinite _root_.LocalClassFieldTheory.realComplexNormQuotientFinite _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitQuotientCarrier_finite _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.LubinTate.standardLubinTateLevelField_galFinite _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.boundedRealFields_finite _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.RayClass.Modulus.congruenceSubgroup_normal _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.CyclicCohomology.binaryCoefficientFamilyCommGroup _root_.GlobalClassFieldTheory.Reciprocity.instMonoidClassGroupRatSubtypeSeparableClosureMemIntermediateField _root_.GlobalClassFieldTheory.Reciprocity.rationalAbstractRelativeClassGroupCommGroup _root_.GlobalClassFieldTheory.Reciprocity.rationalAbstractRelativeClassGroupMul _root_.GlobalClassFieldTheory.Reciprocity.rationalAbstractRelativeClassGroupMulOneClass _root_.LocalClassFieldTheory.comparisonIntegerRingIsIntegralClosure _root_.LocalClassFieldTheory.normalizationIntegerRingIsIntegralClosure _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen _root_.infiniteAdeleRingT2Space _root_.relativeUnrestrictedSPlaceFactorCommGroup
attribute [-simp] _root_.IsDiscreteValuationRing.addVal_ringEquiv _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.LocalClassFieldTheory.integerUnitsModPrincipalUnitsNormOfGaloisOfIsIntegralClosure_mk _root_.LocalClassFieldTheory.normQuotientMapOfRingEquiv_normClass _root_.LocalClassFieldTheory.principalUnitsNormOfUnramifiedValuationOfIsIntegralClosure_apply _root_.LocalClassFieldTheory.principalUnitsSuccQuotNormOfUnramifiedValuationOfIsIntegralClosure_mk _root_.LocalClassFieldTheory.principalUnitsSuccQuotTraceOfUnramifiedValuation_apply _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.OAI.PrimeDegreePackets.ThetaConstruction.schwartzCM_apply _root_.RayClass.primesEquiv_val_eq_natGenerator _root_.infinitePlace_mult_smul
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

/-!
# Norm quotients for unramified local extensions

For a finite unramified Galois extension, the field-norm subgroup is exactly
the subgroup of elements whose normalized valuation is divisible by the
extension degree. The inclusion is the normalized norm formula; the reverse
inclusion follows from finite local reciprocity because the norm quotient and
the valuation quotient have the same finite cardinality.
-/

noncomputable section


namespace LocalClassFieldTheory

open scoped ValuativeRel
open LocalFieldTheory
open LocalFieldTheory.IsNonarchimedeanLocalField

variable (K L : Type)
  [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]
  [Field L] [ValuativeRel L] [TopologicalSpace L]
  [IsNonarchimedeanLocalField L]
  [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
  [Valuation.HasExtension (ValuativeRel.valuation K)
    (ValuativeRel.valuation L)]
  [IsIntegralClosure 𝒪[L] 𝒪[K] L]
  [Module.Finite 𝒪[K] 𝒪[L]]
  [IsUnramifiedValuedExtension K L]

/-- The canonical map from the norm quotient to the valuation quotient. -/
noncomputable def normQuotientToUnramifiedNormQuotient :
    NormQuotient K L →*
      Kˣ ⧸ unramifiedNormSubgroup K (Module.finrank K L) :=
  normQuotientLift
    (unramifiedNormClass K (Module.finrank K L))
    (by
      intro x hx
      rw [MonoidHom.mem_ker]
      exact (unramifiedNormClass_eq_one_iff_mem K (Module.finrank K L) x).2
        (localNormSubgroup_le_unramifiedNormSubgroup K L hx))

/-- The comparison map sends a norm class to the corresponding unramified valuation class. -/
@[simp]
theorem normQuotientToUnramifiedNormQuotient_mk (x : Kˣ) :
    normQuotientToUnramifiedNormQuotient K L
        (normClass K L x) =
      unramifiedNormClass K (Module.finrank K L) x :=
  rfl

/-- Every unramified valuation class is represented by an actual norm quotient class. -/
theorem normQuotientToUnramifiedNormQuotient_surjective :
    Function.Surjective
      (normQuotientToUnramifiedNormQuotient K L) :=
  normQuotientLift_surjective
    (unramifiedNormClass K (Module.finrank K L))
    (by
      intro x hx
      rw [MonoidHom.mem_ker]
      exact (unramifiedNormClass_eq_one_iff_mem K (Module.finrank K L) x).2
        (localNormSubgroup_le_unramifiedNormSubgroup K L hx))
    (unramifiedNormClass_surjective K (Module.finrank K L))

/-- Cyclicity identifies the unramified Galois group with its abelianization. -/
noncomputable def galoisGroupEquivAbelianizationOfUnramifiedValuation :
    Gal(L / K) ≃* Abelianization (Gal(L / K)) := by
  letI : IsCyclic (Gal(L / K)) :=
    isCyclic_galoisGroup_of_unramifiedValuation K L
  letI : CommGroup (Gal(L / K)) :=
    IsCyclic.commGroup (α := Gal(L / K))
  exact Abelianization.equivOfComm (H := Gal(L / K))

/-- The cyclic Galois-group equivalence is the canonical map to the abelianization. -/
@[simp]
theorem galoisGroupEquivAbelianizationOfUnramifiedValuation_apply
    (σ : Gal(L / K)) :
    galoisGroupEquivAbelianizationOfUnramifiedValuation K L σ =
      Abelianization.of σ :=
  rfl

noncomputable local instance unramifiedNormComparisonNormQuotientFinite_r49d403_1 :
    Finite (NormQuotient K L) :=
  Finite.of_equiv (Gal(L / K))
    ((galoisGroupEquivAbelianizationOfUnramifiedValuation K L).toEquiv.trans
      (abelianizationEquivNormQuotient K L).toEquiv)
theorem normQuotient_card_eq_finrank :
    Nat.card (NormQuotient K L) = Module.finrank K L := by
  let : Finite (Abelianization (Gal(L / K))) :=
    Finite.of_surjective Abelianization.of QuotientGroup.mk_surjective
  calc
    Nat.card (NormQuotient K L) =
        Nat.card (Abelianization (Gal(L / K))) :=
      Nat.card_congr (abelianizationEquivNormQuotient K L).symm.toEquiv
    _ = Nat.card (Gal(L / K)) :=
      (Nat.card_congr
        (galoisGroupEquivAbelianizationOfUnramifiedValuation K L).toEquiv).symm
    _ = Module.finrank K L :=
      galoisGroup_card_eq_finrank_of_unramifiedValuation K L

/-- The comparison from the actual norm quotient to the valuation quotient is injective. -/
theorem normQuotientToUnramifiedNormQuotient_injective :
    Function.Injective
      (normQuotientToUnramifiedNormQuotient K L) := by
  let : NeZero (Module.finrank K L) := ⟨Module.finrank_pos.ne'⟩
  let : Finite (NormQuotient K L) :=
    Finite.of_equiv (Gal(L / K))
      ((galoisGroupEquivAbelianizationOfUnramifiedValuation K L).trans
        (abelianizationEquivNormQuotient K L)).toEquiv
  have hcard :
      Nat.card (NormQuotient K L) =
        Nat.card
          (Kˣ ⧸ unramifiedNormSubgroup K (Module.finrank K L)) := by
    rw [normQuotient_card_eq_finrank K L]
    exact
      (unramifiedNormQuotient_card_eq_degree
        K (Module.finrank K L)).symm
  have hbij : Function.Bijective
      (normQuotientToUnramifiedNormQuotient K L) :=
    (Nat.bijective_iff_surjective_and_card
      (normQuotientToUnramifiedNormQuotient K L)).2
        ⟨normQuotientToUnramifiedNormQuotient_surjective K L,
          hcard⟩
  exact hbij.1

/-- The actual norm subgroup is the valuation-divisibility subgroup. -/
theorem normSubgroup_eq_unramifiedNormSubgroup_of_isIntegralClosure :
    localNormSubgroup K L =
      unramifiedNormSubgroup K (Module.finrank K L) := by
  apply le_antisymm
  · exact localNormSubgroup_le_unramifiedNormSubgroup K L
  · intro x hx
    apply (normClass_eq_one_iff_mem K L x).1
    apply normQuotientToUnramifiedNormQuotient_injective K L
    rw [map_one]
    rw [normQuotientToUnramifiedNormQuotient_mk]
    exact (unramifiedNormClass_eq_one_iff_mem K (Module.finrank K L) x).2 hx

/-- The actual unramified norm quotient is the normalized valuation quotient. -/
noncomputable def normQuotientUnramifiedValuationEquivZModOfIsIntegralClosure :
    NormQuotient K L ≃*
      Multiplicative (ZMod (Module.finrank K L)) :=
  (normQuotientEquivOfSubgroupEq K L
    (unramifiedNormSubgroup K (Module.finrank K L))
    (normSubgroup_eq_unramifiedNormSubgroup_of_isIntegralClosure K L)).trans
    (unramifiedNormQuotientEquivZMod K (Module.finrank K L))

/-- The unramified norm-quotient equivalence sends a unit class to its reduced valuation. -/
@[simp]
theorem normQuotientUnramifiedValuationEquivZModOfIsIntegralClosure_mk
    (x : Kˣ) :
    normQuotientUnramifiedValuationEquivZModOfIsIntegralClosure K L
        (normClass K L x) =
      valuationModDegreeMulHom K (Module.finrank K L) x := by
  rw [normQuotientUnramifiedValuationEquivZModOfIsIntegralClosure,
    MulEquiv.trans_apply, normQuotientEquivOfSubgroupEq_normClass,
    unramifiedNormQuotientEquivZMod_mk]

end LocalClassFieldTheory
end
end

section
-- module Solutions.OAIQ244_DUKE.LocalClassFieldTheory_Finite_LocalReciprocity_UnramifiedReciprocity
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 400000
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalIdeleClassDirectLimitMonoid _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalClassFieldTheory.finiteGaloisLocalField_integerRing_moduleFinite _root_.LocalClassFieldTheory.realComplexNormQuotientFinite _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.residueFieldZModAlgebra _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedIntegralAlgebraContextValuationSubringAlgebra _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.instTopologicalSpaceLocalAlgebra _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.RayClass.approximationCompletionTopologicalSpace _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.CyclicCohomology.binaryCoefficientFamilyCommGroup _root_.GlobalClassFieldTheory.Reciprocity.instMonoidClassGroupRatSubtypeSeparableClosureMemIntermediateField _root_.GlobalClassFieldTheory.Reciprocity.rationalAbstractRelativeClassGroupCommGroup _root_.GlobalClassFieldTheory.Reciprocity.rationalAbstractRelativeClassGroupMul _root_.GlobalClassFieldTheory.Reciprocity.rationalAbstractRelativeClassGroupMulOneClass _root_.LocalClassFieldTheory.comparisonIntegerRingIsIntegralClosure _root_.LocalClassFieldTheory.normalizationIntegerRingIsIntegralClosure _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.adicCompletionProperSpace _root_.chosenFinitePlaceCompletionAlgebra _root_.finiteLocalUnitsOpen _root_.infiniteAdeleRingT2Space _root_.relativeAdeleRingIntermediateAlgebra _root_.relativeAdeleRingTopIntermediateAlgebra _root_.relativeUnrestrictedSPlaceFactorCommGroup
attribute [-simp] _root_.IsDiscreteValuationRing.addVal_ringEquiv _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.LocalClassFieldTheory.integerUnitsModPrincipalUnitsNormOfGaloisOfIsIntegralClosure_mk _root_.LocalClassFieldTheory.normQuotientMapOfRingEquiv_normClass _root_.LocalClassFieldTheory.principalUnitsNormOfUnramifiedValuationOfIsIntegralClosure_apply _root_.LocalClassFieldTheory.principalUnitsSuccQuotNormOfUnramifiedValuationOfIsIntegralClosure_mk _root_.LocalClassFieldTheory.principalUnitsSuccQuotTraceOfUnramifiedValuation_apply _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.OAI.PrimeDegreePackets.ThetaConstruction.schwartzCM_apply _root_.RayClass.primesEquiv_val_eq_natGenerator _root_.infinitePlace_mult_smul
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

/-!
# Unramified reciprocity

For a finite unramified Galois extension, this module composes the actual norm
quotient with its normalized valuation model, the generator-normalized
Frobenius model of the Galois group, and the canonical equivalence with the
abelianization of that cyclic group.
-/
noncomputable section

namespace LocalClassFieldTheory

open scoped ValuativeRel
open LocalFieldTheory
open LocalFieldTheory.IsNonarchimedeanLocalField

/-- The actual unramified local reciprocity equivalence with target `GaloisGroup`.
The norm-subgroup equality and the Frobenius/ZMod normalization are generated
internally from the preceding source lemmas, not passed as hypotheses. -/
noncomputable def unramifiedLocalReciprocityIsoToGaloisGroup
    (K L : Type) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] [Field L] [ValuativeRel L]
    [UniformSpace L] [IsUniformAddGroup L] [IsNonarchimedeanLocalField L]
    [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]
    [IsIntegralClosure 𝒪[L] 𝒪[K] L]
    [Module.Finite 𝒪[K] 𝒪[L]]
    [IsUnramifiedValuedExtension K L] :
    NormQuotient K L ≃* Gal(L / K) :=
  (normQuotientUnramifiedValuationEquivZModOfIsIntegralClosure K L).trans
    (galoisGroupEquivZModOfUnramifiedValuationNormalized K L).symm

/-- The chosen inverse prime element
maps to the arithmetic Frobenius under the actual reciprocity equivalence. -/
@[simp]
theorem unramifiedLocalReciprocityIsoToGaloisGroup_inverseIntegerRingUniformizerFieldUnit
    (K L : Type) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] [Field L] [ValuativeRel L]
    [UniformSpace L] [IsUniformAddGroup L] [IsNonarchimedeanLocalField L]
    [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]
    [IsIntegralClosure 𝒪[L] 𝒪[K] L]
    [Module.Finite 𝒪[K] 𝒪[L]]
    [IsUnramifiedValuedExtension K L] :
    unramifiedLocalReciprocityIsoToGaloisGroup K L
        (normClass K L (inverseIntegerRingUniformizerFieldUnit K)) =
      arithmeticFrobeniusOfUnramifiedValuation K L := by
  unfold unramifiedLocalReciprocityIsoToGaloisGroup
  change (galoisGroupEquivZModOfUnramifiedValuationNormalized K L).symm
      (normQuotientUnramifiedValuationEquivZModOfIsIntegralClosure K L
        (normClass K L (inverseIntegerRingUniformizerFieldUnit K))) =
    arithmeticFrobeniusOfUnramifiedValuation K L
  rw [normQuotientUnramifiedValuationEquivZModOfIsIntegralClosure_mk]
  rw [LocalClassFieldTheory.valuationModDegreeMulHom_apply,
    LocalFieldTheory.IsNonarchimedeanLocalField.valuationMap_apply,
    v_inverseIntegerRingUniformizerFieldUnit]
  simp
  rw [← galoisGroupEquivZModOfUnramifiedValuationNormalized_arithmeticFrobenius K L]
  exact (galoisGroupEquivZModOfUnramifiedValuationNormalized K L).symm_apply_apply _

/-- The actual reciprocity equivalence to
`GaloisGroup` sends any field unit class to the corresponding power of arithmetic
Frobenius, with exponent its normalized valuation. -/
theorem unramifiedLocalReciprocityIsoToGaloisGroup_normClass
    (K L : Type) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] [Field L] [ValuativeRel L]
    [UniformSpace L] [IsUniformAddGroup L] [IsNonarchimedeanLocalField L]
    [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]
    [IsIntegralClosure 𝒪[L] 𝒪[K] L]
    [Module.Finite 𝒪[K] 𝒪[L]]
    [IsUnramifiedValuedExtension K L] (x : Kˣ) :
    unramifiedLocalReciprocityIsoToGaloisGroup K L (normClass K L x) =
      (arithmeticFrobeniusOfUnramifiedValuation K L) ^
        LocalFieldTheory.IsNonarchimedeanLocalField.valuationMap K (Additive.ofMul x) := by
  unfold unramifiedLocalReciprocityIsoToGaloisGroup
  change (galoisGroupEquivZModOfUnramifiedValuationNormalized K L).symm
      (normQuotientUnramifiedValuationEquivZModOfIsIntegralClosure K L
        (normClass K L x)) =
    (arithmeticFrobeniusOfUnramifiedValuation K L) ^
      LocalFieldTheory.IsNonarchimedeanLocalField.valuationMap K (Additive.ofMul x)
  rw [normQuotientUnramifiedValuationEquivZModOfIsIntegralClosure_mk]
  rw [LocalClassFieldTheory.valuationModDegreeMulHom_apply]
  rw [← galoisGroupEquivZModOfUnramifiedValuationNormalized_arithmeticFrobenius_zpow K L
    (LocalFieldTheory.IsNonarchimedeanLocalField.valuationMap K (Additive.ofMul x))]
  exact (galoisGroupEquivZModOfUnramifiedValuationNormalized K L).symm_apply_apply _

/-- The actual unramified local reciprocity equivalence with abelianized target.
It composes the valuation quotient and normalized Frobenius model, then
passes to the abelianization of the
cyclic Galois group. -/
noncomputable def unramifiedLocalReciprocityIso
    (K L : Type) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] [Field L] [ValuativeRel L]
    [UniformSpace L] [IsUniformAddGroup L] [IsNonarchimedeanLocalField L]
    [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]
    [IsIntegralClosure 𝒪[L] 𝒪[K] L]
    [Module.Finite 𝒪[K] 𝒪[L]]
    [IsUnramifiedValuedExtension K L] :
    NormQuotient K L ≃* Abelianization (Gal(L / K)) :=
  (unramifiedLocalReciprocityIsoToGaloisGroup K L).trans
    (galoisGroupEquivAbelianizationOfUnramifiedValuation K L)

/-- With abelianized target, the chosen
inverse prime element maps to the class of the arithmetic Frobenius. -/
@[simp]
theorem unramifiedLocalReciprocityIso_inverseIntegerRingUniformizerFieldUnit
    (K L : Type) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] [Field L] [ValuativeRel L]
    [UniformSpace L] [IsUniformAddGroup L] [IsNonarchimedeanLocalField L]
    [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]
    [IsIntegralClosure 𝒪[L] 𝒪[K] L]
    [Module.Finite 𝒪[K] 𝒪[L]]
    [IsUnramifiedValuedExtension K L] :
    unramifiedLocalReciprocityIso K L
        (normClass K L (inverseIntegerRingUniformizerFieldUnit K)) =
      Abelianization.of (arithmeticFrobeniusOfUnramifiedValuation K L) := by
  unfold unramifiedLocalReciprocityIso
  change galoisGroupEquivAbelianizationOfUnramifiedValuation K L
      (unramifiedLocalReciprocityIsoToGaloisGroup K L
        (normClass K L (inverseIntegerRingUniformizerFieldUnit K))) =
    Abelianization.of (arithmeticFrobeniusOfUnramifiedValuation K L)
  rw [unramifiedLocalReciprocityIsoToGaloisGroup_inverseIntegerRingUniformizerFieldUnit]
  rfl

/-- The unramified reciprocity map
on a general field unit is the arithmetic Frobenius class raised to the
normalized valuation. -/
theorem unramifiedLocalReciprocityIso_normClass
    (K L : Type) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] [Field L] [ValuativeRel L]
    [UniformSpace L] [IsUniformAddGroup L] [IsNonarchimedeanLocalField L]
    [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]
    [IsIntegralClosure 𝒪[L] 𝒪[K] L]
    [Module.Finite 𝒪[K] 𝒪[L]]
    [IsUnramifiedValuedExtension K L] (x : Kˣ) :
    unramifiedLocalReciprocityIso K L (normClass K L x) =
      (Abelianization.of (arithmeticFrobeniusOfUnramifiedValuation K L)) ^
        LocalFieldTheory.IsNonarchimedeanLocalField.valuationMap K (Additive.ofMul x) := by
  unfold unramifiedLocalReciprocityIso
  change galoisGroupEquivAbelianizationOfUnramifiedValuation K L
      (unramifiedLocalReciprocityIsoToGaloisGroup K L (normClass K L x)) =
    (Abelianization.of (arithmeticFrobeniusOfUnramifiedValuation K L)) ^
      LocalFieldTheory.IsNonarchimedeanLocalField.valuationMap K (Additive.ofMul x)
  rw [unramifiedLocalReciprocityIsoToGaloisGroup_normClass]
  rw [galoisGroupEquivAbelianizationOfUnramifiedValuation_apply]
  rw [map_zpow]

/-- The actual unramified Artin map induced by the certificate-free
reciprocity equivalence.  This avoids introducing `LocalReciprocityDataReal`
as an assumption package. -/
noncomputable def unramifiedLocalArtinMap
    (K L : Type) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] [Field L] [ValuativeRel L]
    [UniformSpace L] [IsUniformAddGroup L] [IsNonarchimedeanLocalField L]
    [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]
    [IsIntegralClosure 𝒪[L] 𝒪[K] L]
    [Module.Finite 𝒪[K] 𝒪[L]]
    [IsUnramifiedValuedExtension K L] :
    Kˣ →* Abelianization (Gal(L / K)) :=
  (unramifiedLocalReciprocityIso K L).toMonoidHom.comp (normClass K L)

/-- States the theorem `unramifiedLocalArtinMap_apply`. -/
@[simp]
theorem unramifiedLocalArtinMap_apply
    (K L : Type) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] [Field L] [ValuativeRel L]
    [UniformSpace L] [IsUniformAddGroup L] [IsNonarchimedeanLocalField L]
    [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]
    [IsIntegralClosure 𝒪[L] 𝒪[K] L]
    [Module.Finite 𝒪[K] 𝒪[L]]
    [IsUnramifiedValuedExtension K L] (x : Kˣ) :
    unramifiedLocalArtinMap K L x =
      unramifiedLocalReciprocityIso K L (normClass K L x) :=
  rfl

/-- In the arithmetic-Frobenius convention,
the actual local Artin map sends `x` to the arithmetic Frobenius class raised
to `v_K(x)`. -/
theorem unramifiedLocalArtinMap_eq_frobenius_zpow
    (K L : Type) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] [Field L] [ValuativeRel L]
    [UniformSpace L] [IsUniformAddGroup L] [IsNonarchimedeanLocalField L]
    [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]
    [IsIntegralClosure 𝒪[L] 𝒪[K] L]
    [Module.Finite 𝒪[K] 𝒪[L]]
    [IsUnramifiedValuedExtension K L] (x : Kˣ) :
    unramifiedLocalArtinMap K L x =
      (Abelianization.of (arithmeticFrobeniusOfUnramifiedValuation K L)) ^
        LocalFieldTheory.IsNonarchimedeanLocalField.valuationMap K (Additive.ofMul x) := by
  rw [unramifiedLocalArtinMap_apply,
    unramifiedLocalReciprocityIso_normClass]

end LocalClassFieldTheory
end
end


