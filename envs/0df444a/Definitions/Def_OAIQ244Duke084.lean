-- Prove2me | Definitions.Def_OAIQ244Duke084
-- name    : OAIQ244Duke084
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-14T00:29:15.277457+00:00
-- url     : https://prove2.me/theorems/43916eae-ecd2-43ae-bda7-51ff1b515edb
-- title:
--   Definitions bundle OAIQ244Duke084 of the split of OpenAI, Equidistribution of Prime-Degree Torus Packets with Arbitrary Local Type
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.DukePrimeDegree.prime_degree_packet_measure_equidistribution_unconditional` and `OAI.DukePrimeDegree.prime_degree_packet_measures_tendsto_haar_unconditional`, carved from OpenAI's openai/math development (OpenAI, *Equidistribution of Prime-Degree Torus Packets with Arbitrary Local Type*, OpenAI Math Release, September 24, 2026, result family 15, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 23 declarations of OpenAI's Lean: 10 definitions, 1 inductive type or structure and 12 theorems. The definitions and types are `LocalClassFieldTheory.AmbientEmbeddedFixedFieldPresentation`, `LocalClassFieldTheory.AmbientEmbeddedFixedFieldPresentation.abelianizedTransport`, `LocalClassFieldTheory.AmbientEmbeddedFixedFieldPresentation.fixedFieldQuotientEquiv`, `LocalClassFieldTheory.AmbientEmbeddedFixedFieldPresentation.normResidueAbelianElement`, `LocalClassFieldTheory.ambientEmbeddedFixedFieldPresentation`, `LocalClassFieldTheory.ambientEmbeddedNormResidueAbelianElement`, `LocalClassFieldTheory.ambientEmbeddedNormResidueElement`, `LocalClassFieldTheory.ambientEmbeddedPrimeSymbolProperty`, `LocalClassFieldTheory.ambientEmbeddedPrimeTarget`, `LocalClassFieldTheory.ambientEmbeddedPrimeTransportValue`, `LocalClassFieldTheory.ambientEmbeddedPrimeWitness`.
--
--   **Sources.** They come from these modules of lean/OAI/NumberTheory, in whole or in part: `GlobalClassFieldTheory_Reciprocity_FiniteIdeleArtin`, `LocalClassFieldTheory_Finite_LocalReciprocity_FixedFieldIntrinsicReciprocity_AmbientNormResidue`, `LocalClassFieldTheory_Finite_LocalReciprocity_FixedFieldIntrinsicReciprocity_AmbientPrimeComparison`, `LocalClassFieldTheory_Finite_LocalReciprocity_FixedFieldIntrinsicReciprocity_AmbientPrimeNormTransport`, `LocalClassFieldTheory_Finite_LocalReciprocity_FixedFieldIntrinsicReciprocity_AmbientPrimeSymbolSetup`, `LocalClassFieldTheory_Finite_LocalReciprocity_FixedFieldIntrinsicReciprocity_AmbientPrimeWitness`, `LocalClassFieldTheory_Finite_LocalReciprocity_FixedFieldIntrinsicReciprocity_AmbientPrimeWitnessComparison`, `LocalClassFieldTheory_Finite_LocalReciprocity_FixedFieldIntrinsicReciprocity_EmbeddedFrobeniusTransport`, `LocalClassFieldTheory_Finite_LocalReciprocity_FixedFieldIntrinsicReciprocity_NormRestriction`, `LubinTate_Padic_ChangedUniformizerIntertwiner_IntertwinerConstruction`.
--
--   **Imports.** It imports the bundles `OAIQ244Duke080` and `OAIQ244Duke081` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ244Duke088` and `OAIQ244Duke089`.
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
import Mathlib.Algebra.Polynomial.Monic
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
import Mathlib.FieldTheory.Galois.Notation
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
import Mathlib.RingTheory.Complex
import Mathlib.RingTheory.DedekindDomain.Different
import Mathlib.RingTheory.DedekindDomain.Factorization
import Mathlib.RingTheory.DedekindDomain.IntegralClosure
import Mathlib.RingTheory.DedekindDomain.SInteger
import Mathlib.RingTheory.DiscreteValuationRing.Basic
import Mathlib.RingTheory.DiscreteValuationRing.TFAE
import Mathlib.RingTheory.Discriminant
import Mathlib.RingTheory.Filtration
import Mathlib.RingTheory.Finiteness.Cardinality
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
import Mathlib.RingTheory.Polynomial.Eisenstein.Basic
import Mathlib.RingTheory.Polynomial.Eisenstein.IsIntegral
import Mathlib.RingTheory.Polynomial.GaussLemma
import Mathlib.RingTheory.Polynomial.Vieta
import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.RingTheory.PowerSeries.Binomial
import Mathlib.RingTheory.PowerSeries.Expand
import Mathlib.RingTheory.PowerSeries.Log
import Mathlib.RingTheory.PowerSeries.Order
import Mathlib.RingTheory.PowerSeries.Trunc
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
import Mathlib.RingTheory.WittVector.Compare
import Mathlib.RingTheory.WittVector.Complete
import Mathlib.RingTheory.WittVector.FrobeniusFractionField
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
import Definitions.Def_OAIQ244Duke080
import Definitions.Def_OAIQ244Duke081

section
-- module Solutions.OAIQ244_DUKE.LocalClassFieldTheory_Finite_LocalReciprocity_FixedFieldIntrinsicReciprocity_EmbeddedFrobeniusTransport
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 400000
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.GlobalClassFields.bigHilbertClassFieldNormSubgroup_normal _root_.GlobalClassFieldTheory.GlobalClassFields.finiteAbelianSubextensionAbstractRelativeFixedFieldFiniteDimensional _root_.GlobalClassFieldTheory.GlobalClassFields.finiteAbelianSubextensionAbstractRelativeFixedFieldIsAbelianGalois _root_.GlobalClassFieldTheory.Reciprocity.infinitePlaceComplexificationOverfield_algebra _root_.GlobalClassFieldTheory.Reciprocity.infinitePlaceComplexificationOverfield_baseAlgebra _root_.GlobalClassFieldTheory.Reciprocity.infinitePlaceComplexificationOverfield_baseSmul _root_.GlobalClassFieldTheory.Reciprocity.infinitePlaceComplexificationOverfield_smul _root_.GlobalClassFieldTheory.Reciprocity.rationalIdeleClassDirectLimitSMul _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.KummerTheory.primeCyclotomicBaseIsGalois _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.residueFieldZModAlgebra _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedIntegralAlgebraContextValuationSubringAlgebra _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedIntegralAlgebraContextValuationSubringTower _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedQPadicContextValuationSubringTower _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.LubinTate.compatibleGroupFamiliesGroup _root_.LubinTate.padicCompletedLevelField_algebra _root_.LubinTate.padicCompletedLevelField_isGalois _root_.LubinTate.padicCompletedLevelField_padicScalarTower _root_.LubinTate.padicCompletedUnramifiedFieldAlgebra _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.instTopologicalSpaceLocalAlgebra _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.RayClass.Modulus.congruenceSubgroup_normal _root_.RayClass.approximationCompletionTopologicalSpace _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.GlobalClassFieldTheory.Reciprocity.instNumberFieldSubtypeSeparableClosureRatMemIntermediateFieldAbstractFixedFieldOfFiniteQuotientAlgEquivSubgroupBaseFieldExtensionSubgroup _root_.GlobalClassFieldTheory.Reciprocity.instSMulAlgEquivRatSeparableClosureClassGroupSubtypeMemIntermediateField _root_.GlobalClassFieldTheory.Reciprocity.rationalAbstractRelativeClassGroupMul _root_.GlobalClassFieldTheory.Reciprocity.rationalAbstractRelativeClassGroupMulOneClass _root_.LocalClassFieldTheory.normalizationIntegerRingIsIntegralClosure _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.adicCompletionProperSpace _root_.chosenFinitePlaceCompletionAlgebra _root_.chosenFinitePlaceLocalizedIntegerAlgebra _root_.chosenFinitePlaceLocalizedIsGalois _root_.cyclicPrimeDegreeIntermediate_isGalois _root_.cyclicPrimeSubextension_isGalois _root_.finiteIdeleGroupIsTopologicalGroup _root_.finiteLocalUnitsOpen _root_.finiteNormalClosure_isGalois _root_.ideleGroupIsTopologicalGroup _root_.infiniteAdeleRingT2Space _root_.relativeAdeleRingIntermediateAlgebra _root_.relativeAdeleRingTopIntermediateAlgebra
attribute [-simp] _root_.ClassFormation.DegreeData.finiteUnramifiedDegreeEquiv_unramifiedFrobenius _root_.ClassFormation.DegreeData.finiteUnramifiedDegreeHom_mk _root_.ClassFormation.DegreeData.finiteUnramifiedRestriction_frobenius _root_.ClassFormation.DegreeData.finiteUnramifiedRestriction_mk _root_.ClassFormation.DegreeData.maximalUnramifiedExtensionRestriction_mk _root_.ClassFormation.DegreeData.maximalUnramifiedFrobeniusPower_one _root_.ClassFormation.DegreeData.maximalUnramifiedRestriction_frobenius _root_.ClassFormation.FiniteAbelianSubextension.extensionQuotientMk_apply _root_.ClassFormation.FiniteGaloisSubextension.classFieldCandidate_field _root_.ClassFormation.FiniteGaloisSubextension.intermediateFiniteAbelianOfCommutatorLe_field _root_.ClassFormation.ValuationData.maximalUnramifiedNormResidue_degree _root_.ClassFormation.mem_normFilterBasis_iff _root_.IsDiscreteValuationRing.addVal_ringEquiv _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.OAI.PrimeDegreePackets.ThetaConstruction.schwartzCM_apply _root_.RayClass.primesEquiv_val_eq_natGenerator _root_.infinitePlace_mult_smul
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

/-!
# Embedded Frobenius transport

This module transports inertia, Frobenius elements, and fixed fields across an explicit equivalence of separable closures.
-/

noncomputable section

namespace LocalClassFieldTheory

open LocalFieldTheory RamificationTheory CyclicCohomology KummerTheory
open ClassFormation
open scoped ValuativeRel

section EmbeddedFrobeniusTransport

variable (K F E : Type)
    [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    [Field E] [Algebra K F] [Algebra F E] [Algebra K E]
    [IsScalarTower K F E]
    [FiniteDimensional K F] [Algebra.IsSeparable K F]
    [Valuation.HasExtension
      (ValuativeRel.valuation K) (ValuativeRel.valuation F)]
    [FiniteDimensional F E] [IsGalois F E]

/-- After coercion to `SeparableClosure K`, the Frobenius fixed-field
equivalence acts as the original separable-closure equivalence. -/
@[simp]
theorem
    intrinsicFrobeniusFixedFieldEquivAmbientEmbeddedField_apply_val
    (j : E →ₐ[K] SeparableClosure K) :
    let i :=
      j.comp (IsScalarTower.toAlgHom K F E)
    letI : Algebra F (SeparableClosure F) :=
      (separableClosure F (AlgebraicClosure F)).algebra
    letI : Algebra F (SeparableClosure K) :=
      i.toRingHom.toAlgebra
    ∀ (e : SeparableClosure F ≃ₐ[F] SeparableClosure K)
      (sigma :
        let jF : E →ₐ[F] SeparableClosure K :=
          { j with commutes' := fun x => rfl }
        let jI : E →ₐ[F] SeparableClosure F :=
          e.symm.toAlgHom.comp jF
        let EI :=
          finiteGaloisAbstractExtensionOfEmbedding F E jI
        let RF :=
          (intrinsicFiniteAbstractBase F).toFiniteResidueAbstractField
            (localResidueDatum F)
        (localResidueDatum F).FrobeniusElements
          RF EI.field EI.below)
      (x :
        let jF : E →ₐ[F] SeparableClosure K :=
          { j with commutes' := fun x => rfl }
        let jI : E →ₐ[F] SeparableClosure F :=
          e.symm.toAlgHom.comp jF
        let EI :=
          finiteGaloisAbstractExtensionOfEmbedding F E jI
        let RF :=
          (intrinsicFiniteAbstractBase F).toFiniteResidueAbstractField
            (localResidueDatum F)
        let SF :=
          (localResidueDatum F).frobeniusFixedField
            RF EI.field EI.below sigma
        abstractFixedField F (SeparableClosure F) SF),
      let jF : E →ₐ[F] SeparableClosure K :=
        { j with commutes' := fun x => rfl }
      let jI : E →ₐ[F] SeparableClosure F :=
        e.symm.toAlgHom.comp jF
      let EI :=
        finiteGaloisAbstractExtensionOfEmbedding F E jI
      let H₀ :=
        closedFixingSubgroup K (SeparableClosure K)
          (AlgHom.fieldRange i)
      let J₀ :=
        closedFixingSubgroup K (SeparableClosure K)
          (AlgHom.fieldRange j)
      let hJH : J₀.toSubgroup ≤ H₀.toSubgroup := by
        change
          (AlgHom.fieldRange j).fixingSubgroup ≤
            (AlgHom.fieldRange i).fixingSubgroup
        apply (AlgHom.fieldRange i).fixingSubgroup_le
        intro y hy
        rcases hy with ⟨z, rfl⟩
        exact ⟨algebraMap F E z, rfl⟩
      letI _hSourceNormal :
          (extensionSubgroup
            (intrinsicAbstractBase F) EI.field EI.below).Normal :=
        EI.normal
      letI _hSourceFinite : Finite
          ((intrinsicAbstractBase F).toSubgroup ⧸
            extensionSubgroup
              (intrinsicAbstractBase F) EI.field EI.below) :=
        EI.finite
      letI _hTargetNormal :
          (extensionSubgroup H₀ J₀ hJH).Normal :=
        ambientEmbeddedExtensionSubgroup_normal K F E j e
      letI _hTargetFinite : Finite
          (H₀.toSubgroup ⧸ extensionSubgroup H₀ J₀ hJH) :=
        ambientEmbeddedExtensionQuotient_finite K F E j e
      let _RF :=
        (intrinsicFiniteAbstractBase F).toFiniteResidueAbstractField
          (localResidueDatum F)
      let hHabsolute : Finite
          ((baseField
            Gal(SeparableClosure K / K)).toSubgroup ⧸
            extensionSubgroup
              (baseField Gal(SeparableClosure K / K))
              H₀ (le_baseField H₀)) := by
        exact ambientEmbeddedAbsoluteQuotientFinite K F i
      let H : FiniteAbstractField
          Gal(SeparableClosure K / K) :=
        ⟨H₀, hHabsolute⟩
      let RH :=
        H.toFiniteResidueAbstractField (localResidueDatum K)
      let sigmaH :=
        intrinsicFrobeniusElementToAmbientEmbeddedField
          K F E j e sigma
      let SH :=
        (localResidueDatum K).frobeniusFixedField
          RH J₀ hJH sigmaH
      let hSHH :=
        (localResidueDatum K).frobeniusFixedField_le
          RH J₀ hJH sigmaH
      let LH :=
        abstractRelativeFixedField K (SeparableClosure K) hSHH
      let iLH : F →ₐ[K] LH :=
        i.codRestrict (LH.restrictScalars K).toSubalgebra (fun y => by
          change
            i y ∈ IntermediateField.fixedField SH.toSubgroup
          rw [IntermediateField.mem_fixedField_iff]
          intro rho hrho
          have hrhoH : rho ∈ H₀.toSubgroup :=
            hSHH hrho
          change rho (i y) = i y
          change
            rho ∈ (AlgHom.fieldRange i).fixingSubgroup at hrhoH
          rw [IntermediateField.mem_fixingSubgroup_iff] at hrhoH
          exact hrhoH (i y) ⟨y, rfl⟩)
      letI : Algebra F LH :=
        iLH.toRingHom.toAlgebra
      ((intrinsicFrobeniusFixedFieldEquivAmbientEmbeddedField
        K F E j e sigma x : LH) : SeparableClosure K) =
        e (x : SeparableClosure F) := by
  dsimp only
  intro e sigma x
  rfl

end EmbeddedFrobeniusTransport

end LocalClassFieldTheory
end
end

section
-- module Solutions.OAIQ244_DUKE.LocalClassFieldTheory_Finite_LocalReciprocity_FixedFieldIntrinsicReciprocity_AmbientNormResidue
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.GlobalClassFields.bigHilbertClassFieldNormSubgroup_normal _root_.GlobalClassFieldTheory.GlobalClassFields.finiteAbelianSubextensionAbstractRelativeFixedFieldFiniteDimensional _root_.GlobalClassFieldTheory.GlobalClassFields.finiteAbelianSubextensionAbstractRelativeFixedFieldIsAbelianGalois _root_.GlobalClassFieldTheory.Reciprocity.infinitePlaceComplexificationOverfield_algebra _root_.GlobalClassFieldTheory.Reciprocity.infinitePlaceComplexificationOverfield_baseAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalIdeleClassDirectLimitMonoid _root_.GlobalClassFieldTheory.Reciprocity.rationalIdeleClassDirectLimitSMul _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.KummerTheory.primeCyclotomicBaseIsGalois _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.residueFieldZModAlgebra _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedIntegralAlgebraContextValuationSubringAlgebra _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedIntegralAlgebraContextValuationSubringTower _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedQPadicContextValuationSubringTower _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.LubinTate.compatibleGroupFamiliesGroup _root_.LubinTate.padicCompletedLevelField_algebra _root_.LubinTate.padicCompletedLevelField_isGalois _root_.LubinTate.padicCompletedLevelField_padicScalarTower _root_.LubinTate.padicCompletedUnramifiedFieldAlgebra _root_.LubinTate.standardLubinTateLevelField_isMulCommutative _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.diagonalLogAction _root_.OAI.PrimeDegreePackets.instTopologicalSpaceLocalAlgebra _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.RayClass.Modulus.congruenceSubgroup_normal _root_.RayClass.approximationCompletionTopologicalSpace _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.RelativeIdeleGroup.relativeIdeleMulAction _root_.CyclicCohomology.binaryCoefficientFamilyCommGroup _root_.GlobalClassFieldTheory.Reciprocity.instNumberFieldSubtypeSeparableClosureRatMemIntermediateFieldAbstractFixedFieldOfFiniteQuotientAlgEquivSubgroupBaseFieldExtensionSubgroup _root_.GlobalClassFieldTheory.Reciprocity.instMonoidClassGroupRatSubtypeSeparableClosureMemIntermediateField _root_.GlobalClassFieldTheory.Reciprocity.instSMulAlgEquivRatSeparableClosureClassGroupSubtypeMemIntermediateField _root_.GlobalClassFieldTheory.Reciprocity.rationalAbstractRelativeClassGroupCommGroup _root_.GlobalClassFieldTheory.Reciprocity.rationalAbstractRelativeClassGroupMul _root_.GlobalClassFieldTheory.Reciprocity.rationalAbstractRelativeClassGroupMulOneClass _root_.LocalClassFieldTheory.normalizationIntegerRingIsIntegralClosure _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.adicCompletionProperSpace _root_.chosenFinitePlaceCompletionAlgebra _root_.chosenFinitePlaceLocalizedIntegerAlgebra _root_.chosenFinitePlaceLocalizedIsGalois _root_.cyclicPrimeDegreeIntermediate_isGalois _root_.cyclicPrimeSubextension_isGalois _root_.finiteLocalUnitsOpen _root_.finiteNormalClosure_isGalois _root_.infiniteAdeleRingT2Space _root_.relativeAdeleRingIntermediateAlgebra _root_.relativeAdeleRingTopIntermediateAlgebra _root_.relativeUnrestrictedSPlaceFactorCommGroup
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI
attribute [local instance] OAI.starSubalgebraCommCStarAlgebra

set_option autoImplicit false

/-!
# Ambient embedded norm-residue values

This module defines the ambient fixed-field norm-residue value attached
to a unit of the intrinsically presented base field, both before and
after identifying the abelianization of an abelian Galois group with
the group itself.
-/

noncomputable section

namespace LocalClassFieldTheory

open LocalFieldTheory RamificationTheory CyclicCohomology KummerTheory
open ClassFormation
open scoped ValuativeRel
open scoped IsMulCommutative

/-- A finite fixed-field presentation of an embedded finite Galois extension.

The object records the actual ambient fixed-field quotient, its realization of
the embedded base field, and the quotient map to the original Galois group.
It is the common interface for calculations that use the ambient
norm-residue value without unfolding the construction of that presentation. -/
structure AmbientEmbeddedFixedFieldPresentation
    (K F E : Type)
    [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    [Field E] [Algebra K F] [Algebra F E] [Algebra K E]
    [IsScalarTower K F E]
    [FiniteDimensional K F] [Algebra.IsSeparable K F]
    [Valuation.HasExtension
      (ValuativeRel.valuation K) (ValuativeRel.valuation F)]
    [FiniteDimensional F E] [IsGalois F E]
    (j : E →ₐ[K] SeparableClosure K) where
  /-- The given base field embedded in the ambient separable closure. -/
  baseEmbedding : F →ₐ[K] SeparableClosure K
  /-- The finite ambient fixed field representing the embedded base field. -/
  base : FiniteAbstractField Gal(SeparableClosure K / K)
  /-- The finite Galois ambient fixed-field extension representing `E / F`. -/
  extension : FiniteGaloisSubextension base.field
  /-- The base embedding is induced by the embedding of the top field. -/
  baseEmbedding_eq :
    baseEmbedding = j.comp (IsScalarTower.toAlgHom K F E)
  /-- The ambient base subgroup fixes precisely the range of the base embedding. -/
  base_field_eq :
    base.field =
      closedFixingSubgroup K (SeparableClosure K)
        (AlgHom.fieldRange baseEmbedding)
  /-- The ambient top subgroup fixes precisely the range of the top embedding. -/
  extension_field_eq :
    extension.field =
      closedFixingSubgroup K (SeparableClosure K)
        (AlgHom.fieldRange j)
  /-- The actual equivalence from the given base field to its ambient fixed field. -/
  baseEquiv :
    F ≃ₐ[K] abstractFixedField K (SeparableClosure K) base.field
  /-- The base-field equivalence realizes the chosen ambient embedding. -/
  baseEquiv_apply (x : F) :
    ((baseEquiv x :
      abstractFixedField K (SeparableClosure K) base.field) :
        SeparableClosure K) =
      baseEmbedding x
  /-- The actual quotient equivalence to the original Galois group. -/
  quotientEquiv : extension.extensionQuotient ≃* Gal(E / F)
  /-- The quotient equivalence acts through the supplied ambient embedding. -/
  quotientEquiv_mk_apply
      (sigma : base.field.toSubgroup) (x : E) :
    j (quotientEquiv (extension.extensionQuotientMk sigma) x) =
      sigma.1 (j x)

namespace AmbientEmbeddedFixedFieldPresentation

/-- The canonical quotient equivalence from an ambient finite fixed-field
extension to the Galois group of its relative fixed field. -/
noncomputable def fixedFieldQuotientEquiv
    {K F E : Type}
    [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    [Field E] [Algebra K F] [Algebra F E] [Algebra K E]
    [IsScalarTower K F E]
    [FiniteDimensional K F] [Algebra.IsSeparable K F]
    [Valuation.HasExtension
      (ValuativeRel.valuation K) (ValuativeRel.valuation F)]
    [FiniteDimensional F E] [IsGalois F E]
    {j : E →ₐ[K] SeparableClosure K}
    (P : AmbientEmbeddedFixedFieldPresentation K F E j) :
    P.extension.extensionQuotient ≃*
      Gal(abstractRelativeFixedField K (SeparableClosure K)
        P.extension.below /
        abstractFixedField K (SeparableClosure K) P.base.field) :=
  P.extension.extensionQuotientMulEquiv.trans
    (abstractExtensionQuotientEquivGaloisGroup
      K (SeparableClosure K) P.base.field P.extension.field
      P.extension.below P.extension.normal)

/-- The actual additive equivalence obtained by transporting abelianized
relative fixed-field Galois elements through an ambient fixed-field
presentation. -/
noncomputable def abelianizedTransport
    {K F E : Type}
    [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    [Field E] [Algebra K F] [Algebra F E] [Algebra K E]
    [IsScalarTower K F E]
    [FiniteDimensional K F] [Algebra.IsSeparable K F]
    [Valuation.HasExtension
      (ValuativeRel.valuation K) (ValuativeRel.valuation F)]
    [FiniteDimensional F E] [IsGalois F E]
    {j : E →ₐ[K] SeparableClosure K}
    (P : AmbientEmbeddedFixedFieldPresentation K F E j) :
    Additive
      (Abelianization
        Gal(abstractRelativeFixedField K (SeparableClosure K)
          P.extension.below /
          abstractFixedField K (SeparableClosure K) P.base.field)) ≃+
      Additive (Abelianization Gal(E / F)) :=
  (P.fixedFieldQuotientEquiv.abelianizationCongr.toAdditive.symm).trans
    P.quotientEquiv.abelianizationCongr.toAdditive

/-- Evaluate the ambient fixed-field norm-residue construction using this
presentation's actual finite quotient and base-field realization. -/
noncomputable def normResidueAbelianElement
    {K F E : Type}
    [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    [Field E] [Algebra K F] [Algebra F E] [Algebra K E]
    [IsScalarTower K F E]
    [FiniteDimensional K F] [Algebra.IsSeparable K F]
    [Valuation.HasExtension
      (ValuativeRel.valuation K) (ValuativeRel.valuation F)]
    [FiniteDimensional F E] [IsGalois F E]
    {j : E →ₐ[K] SeparableClosure K}
    (P : AmbientEmbeddedFixedFieldPresentation K F E j)
    (a : Fˣ) : Abelianization Gal(E / F) := by
  letI : (extensionSubgroup
      P.base.field P.extension.field P.extension.below).Normal :=
    P.extension.normal
  letI : Finite
      (P.base.field.toSubgroup ⧸
        extensionSubgroup P.base.field P.extension.field
          P.extension.below) :=
    P.extension.finite
  letI : Finite
      ((baseField
        Gal(SeparableClosure K / K)).toSubgroup ⧸
        extensionSubgroup
          (baseField Gal(SeparableClosure K / K))
          P.base.field (le_baseField P.base.field)) :=
    P.base.finite
  exact
    Additive.toMul
      (P.abelianizedTransport
        (abstractFixedFieldNormResidueSymbol
          K (SeparableClosure K)
          (localResidueDatum K)
          (localHenselianValuation K)
          (separableClosureUnits_isClassFormation K)
          P.base.field P.extension.field P.extension.below
          (Additive.ofMul
            (Units.mapEquiv P.baseEquiv.toMulEquiv a))))

end AmbientEmbeddedFixedFieldPresentation

/-- The canonical ambient fixed-field presentation of an embedded finite
Galois local extension. -/
noncomputable def ambientEmbeddedFixedFieldPresentation
    (K F E : Type)
    [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    [Field E] [Algebra K F] [Algebra F E] [Algebra K E]
    [IsScalarTower K F E]
    [FiniteDimensional K F] [Algebra.IsSeparable K F]
    [Valuation.HasExtension
      (ValuativeRel.valuation K) (ValuativeRel.valuation F)]
    [FiniteDimensional F E] [IsGalois F E]
    (j : E →ₐ[K] SeparableClosure K)
    (e : ambientEmbeddedSeparableClosureEquiv K F E j) :
    AmbientEmbeddedFixedFieldPresentation K F E j := by
  let i :=
    j.comp (IsScalarTower.toAlgHom K F E)
  letI : Algebra F (SeparableClosure F) :=
      (separableClosure F (AlgebraicClosure F)).algebra
  letI : Algebra F (SeparableClosure K) :=
    i.toRingHom.toAlgebra
  let H₀ :=
    closedFixingSubgroup K (SeparableClosure K)
      (AlgHom.fieldRange i)
  let J₀ :=
    closedFixingSubgroup K (SeparableClosure K)
      (AlgHom.fieldRange j)
  let hJH : J₀.toSubgroup ≤ H₀.toSubgroup := by
    change
      (AlgHom.fieldRange j).fixingSubgroup ≤
        (AlgHom.fieldRange i).fixingSubgroup
    apply (AlgHom.fieldRange i).fixingSubgroup_le
    intro x hx
    rcases hx with ⟨y, rfl⟩
    exact ⟨algebraMap F E y, rfl⟩
  letI _hTargetNormal :
      (extensionSubgroup H₀ J₀ hJH).Normal :=
    ambientEmbeddedExtensionSubgroup_normal K F E j e
  letI _hTargetFinite : Finite
      (H₀.toSubgroup ⧸ extensionSubgroup H₀ J₀ hJH) :=
    ambientEmbeddedExtensionQuotient_finite K F E j e
  letI _hHabsolute : Finite
      ((baseField
        Gal(SeparableClosure K / K)).toSubgroup ⧸
        extensionSubgroup
          (baseField Gal(SeparableClosure K / K))
        H₀ (le_baseField H₀)) := by
    exact ambientEmbeddedAbsoluteQuotientFinite K F i
  let H : FiniteAbstractField
      Gal(SeparableClosure K / K) :=
    ⟨H₀, _hHabsolute⟩
  let T : FiniteGaloisSubextension H.field :=
    ⟨J₀, hJH, _hTargetNormal, _hTargetFinite⟩
  let F₀ :=
    abstractFixedField K (SeparableClosure K) H₀
  let hfixed :
      F₀ = AlgHom.fieldRange i :=
    InfiniteGalois.fixedField_fixingSubgroup
      (AlgHom.fieldRange i)
  let phiF : F ≃ₐ[K] F₀ :=
    (i.equivFieldRange).trans
      (IntermediateField.equivOfEq hfixed.symm)
  let qE :=
    ambientEmbeddedExtensionQuotientEquivGaloisGroup
      K F E j e
  refine
    { baseEmbedding := i
      base := H
      extension := T
      baseEmbedding_eq := rfl
      base_field_eq := rfl
      extension_field_eq := rfl
      baseEquiv := phiF
      baseEquiv_apply := ?_
      quotientEquiv := T.extensionQuotientMulEquiv.trans qE
      quotientEquiv_mk_apply := ?_ }
  · intro x
    rfl
  · intro sigma x
    change
      j (qE
        (T.extensionQuotientMulEquiv
          (T.extensionQuotientMk sigma)) x) =
        sigma.1 (j x)
    rw [T.extensionQuotientMk_apply]
    exact
      ambientEmbeddedExtensionQuotientEquivGaloisGroup_mk_apply
        K F E j e sigma x

/-- The abelianized ambient fixed-field norm-residue value attached to a unit
of the intrinsically presented base field. -/
noncomputable def ambientEmbeddedNormResidueAbelianElement
    (K F E : Type)
    [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    [Field E] [Algebra K F] [Algebra F E] [Algebra K E]
    [IsScalarTower K F E]
    [FiniteDimensional K F] [Algebra.IsSeparable K F]
    [Valuation.HasExtension
      (ValuativeRel.valuation K) (ValuativeRel.valuation F)]
    [FiniteDimensional F E] [IsGalois F E]
    (j : E →ₐ[K] SeparableClosure K)
    (e : ambientEmbeddedSeparableClosureEquiv K F E j)
    (a : Fˣ) : Abelianization Gal(E / F) :=
  (ambientEmbeddedFixedFieldPresentation K F E j e).normResidueAbelianElement a

/-- The ambient fixed-field norm-residue value in `Gal(E/F)`, obtained
from its abelianized value using the canonical equivalence for an abelian extension. -/
noncomputable def ambientEmbeddedNormResidueElement
    (K F E : Type)
    [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    [Field E] [Algebra K F] [Algebra F E] [Algebra K E]
    [IsScalarTower K F E]
    [FiniteDimensional K F] [Algebra.IsSeparable K F]
    [Valuation.HasExtension
      (ValuativeRel.valuation K) (ValuativeRel.valuation F)]
    [FiniteDimensional F E] [IsAbelianGalois F E]
    (j : E →ₐ[K] SeparableClosure K)
    (e : ambientEmbeddedSeparableClosureEquiv K F E j)
    (a : Fˣ) : Gal(E / F) :=
  (Abelianization.equivOfComm (H := Gal(E / F))).symm
    (ambientEmbeddedNormResidueAbelianElement K F E j e a)

end LocalClassFieldTheory
end
end

section
-- module Solutions.OAIQ244_DUKE.LocalClassFieldTheory_Finite_LocalReciprocity_FixedFieldIntrinsicReciprocity_AmbientPrimeNormTransport
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 400000
attribute [-instance] _root_.ClassFormation.instIsAddTorsionFreeZHat _root_.ClassFormation.instIsMulTorsionFreeMultiplicativeZHat _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.GlobalClassFields.bigHilbertClassFieldNormSubgroup_normal _root_.GlobalClassFieldTheory.GlobalClassFields.finiteAbelianSubextensionAbstractRelativeFixedFieldFiniteDimensional _root_.GlobalClassFieldTheory.GlobalClassFields.finiteAbelianSubextensionAbstractRelativeFixedFieldIsAbelianGalois _root_.GlobalClassFieldTheory.Reciprocity.infinitePlaceComplexificationOverfield_algebra _root_.GlobalClassFieldTheory.Reciprocity.infinitePlaceComplexificationOverfield_baseAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalIdeleClassDirectLimitMonoid _root_.GlobalClassFieldTheory.Reciprocity.rationalIdeleClassDirectLimitSMul _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.DiscreteNthRootsSubgroup.instTopologicalSpaceSubtypeUnitsMemSubgroup _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.KummerTheory.finite_finsupp_nsmulQuotient _root_.KummerTheory.finite_sUnit_nthPowerQuotient _root_.KummerTheory.primeCyclotomicBaseIsGalois _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitQuotientCarrier_finite _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.residueFieldZModAlgebra _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedIntegralAlgebraContextValuationSubringAlgebra _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedIntegralAlgebraContextValuationSubringTower _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedQPadicContextValuationSubringTower _root_.LocalFieldTheory.DiscreteValuationField.finite_padicInt_finPi_nsmulQuotient _root_.LocalFieldTheory.DiscreteValuationField.finite_padicInt_pi_nsmulQuotient_of_coprime _root_.LocalFieldTheory.DiscreteValuationField.finite_valuationSubringUnits_nthPowerQuotient _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.Padic.padicUnitFiniteFactor_finite _root_.LocalFieldTheory.finite_multiplicative_nthPowerQuotient _root_.LocalFieldTheory.finite_nsmulAddQuotient_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.LubinTate.compatibleGroupFamiliesGroup _root_.LubinTate.padicCompletedLevelField_algebra _root_.LubinTate.padicCompletedLevelField_isGalois _root_.LubinTate.padicCompletedLevelField_padicScalarTower _root_.LubinTate.padicCompletedUnramifiedFieldAlgebra _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.boundedRealFields_finite _root_.OAI.PrimeDegreePackets.instT2SpaceLocalAlgebra _root_.OAI.PrimeDegreePackets.instTopologicalSpaceLocalAlgebra _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.OAI.PrimeDegreePackets.xT2Space _root_.RayClass.Modulus.congruenceSubgroup_normal _root_.RayClass.approximationCompletionTopologicalSpace _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.CyclicCohomology.binaryCoefficientFamilyCommGroup _root_.GlobalClassFieldTheory.Reciprocity.instNumberFieldSubtypeSeparableClosureRatMemIntermediateFieldAbstractFixedFieldOfFiniteQuotientAlgEquivSubgroupBaseFieldExtensionSubgroup _root_.GlobalClassFieldTheory.Reciprocity.instMonoidClassGroupRatSubtypeSeparableClosureMemIntermediateField _root_.GlobalClassFieldTheory.Reciprocity.instSMulAlgEquivRatSeparableClosureClassGroupSubtypeMemIntermediateField _root_.GlobalClassFieldTheory.Reciprocity.rationalAbstractRelativeClassGroupCommGroup _root_.GlobalClassFieldTheory.Reciprocity.rationalAbstractRelativeClassGroupMul _root_.GlobalClassFieldTheory.Reciprocity.rationalAbstractRelativeClassGroupMulOneClass _root_.LocalClassFieldTheory.normalizationIntegerRingIsIntegralClosure _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.adicCompletionProperSpace _root_.chosenFinitePlaceCompletionAlgebra _root_.chosenFinitePlaceLocalizedIntegerAlgebra _root_.chosenFinitePlaceLocalizedIsGalois _root_.cyclicPrimeDegreeIntermediate_isGalois _root_.cyclicPrimeSubextension_isGalois _root_.finiteIdeleGroupIsTopologicalGroup _root_.finiteIdeleGroupT2Space _root_.finiteLocalUnitsOpen _root_.finiteNormalClosure_isGalois _root_.ideleGroupIsTopologicalGroup _root_.ideleGroupT2Space _root_.infiniteAdeleRingT2Space _root_.infiniteIdeleGroupT2Space _root_.relativeAdeleRingIntermediateAlgebra _root_.relativeAdeleRingTopIntermediateAlgebra _root_.relativeUnrestrictedSPlaceFactorCommGroup
attribute [-simp] _root_.ClassFormation.DegreeData.finiteUnramifiedDegreeHom_mk _root_.ClassFormation.DegreeData.maximalUnramifiedFrobeniusPower_one _root_.ClassFormation.FiniteAbelianSubextension.normSubgroupMap_val _root_.ClassFormation.FiniteGaloisSubextension.classFieldCandidate_field _root_.ClassFormation.ValuationData.maximalUnramifiedNormResidue_degree _root_.ClassFormation.mem_normFilterBasis_iff _root_.ClassFormation.toZModPow_zHatToPadicInt _root_.ClassFormation.zHatReductionRingHom_apply _root_.ClassFormation.zHatRingEquivProfiniteIntegerPrimeProduct_apply _root_.ClassFormation.zHatToPadicInt_intCast _root_.ClassFormation.zHatToProfiniteIntegerPrimeProduct_apply _root_.ClassFormation.zHatToProfiniteIntegerPrimeProduct_intCast _root_.ClassFormation.zHatUnitsContinuousMulEquivPrimeProduct_coe_apply _root_.IsDiscreteValuationRing.addVal_ringEquiv _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.KummerTheory.torsionQuotientEquivOfZHatMulDecomposition_mk _root_.KummerTheory.zHatUnitsContinuousMulEquivPrimeProduct_rationalCyclotomicCharacter _root_.KummerTheory.zHatUnitsDecomposition_freeCoordinate _root_.LocalClassFieldTheory.valuationModDegreeMulHom_apply _root_.LocalClassFieldTheory.valuationModDegree_apply _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.OAI.PrimeDegreePackets.ThetaConstruction.schwartzCM_apply _root_.RayClass.primesEquiv_val_eq_natGenerator _root_.infinitePlace_mult_smul
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

/-!
# Valuation-one units and abstract prime norm-residue transport

This module transports valuation-one units and norm classes through
compatible field equivalences, and evaluates abstract fixed-field
norm-residue symbols on transported prime norms.
-/

noncomputable section

namespace LocalClassFieldTheory

open LocalFieldTheory RamificationTheory CyclicCohomology KummerTheory
open ClassFormation
open scoped ValuativeRel

/-- A unit of valuation one in an abstract fixed field determines a prime
element for the ambient local henselian valuation datum. -/
theorem
    localHenselianValuation_isPrimeElement_abstractFixedField
    (K : Type) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    (H : FiniteAbstractField
      Gal(SeparableClosure K / K)) :
    let L :=
      abstractFixedField K (SeparableClosure K) H.field
    letI : FiniteDimensional K L :=
      abstractFixedField_finiteDimensional
        K (SeparableClosure K) H.field H.finite
    letI : NontriviallyNormedField L :=
      finiteExtensionSpectralNormedField K L
    letI : ValuativeRel L :=
      finiteExtensionSpectralValuativeRel K L
    letI : IsNonarchimedeanLocalField L :=
      finiteExtensionSpectralIsNonarchimedeanLocalField K L
    ∀ p : Lˣ,
      IsNonarchimedeanLocalField.valuationMap L
          (Additive.ofMul p) = 1 →
        (localHenselianValuation K).IsPrimeElement H
          (abstractFixedFieldUnitsEquivGaloisFixed
            K (SeparableClosure K) H.field
              (Additive.ofMul p)) := by
  dsimp only
  intro p hp
  change (localHenselianValuation K).valuationAt H
      (abstractFixedFieldUnitsEquivGaloisFixed K (SeparableClosure K) H.field
        (Additive.ofMul p)) =
    (localHenselianValuation K).oneValue
  apply Subtype.ext
  change
    ((((localHenselianValuation K).valuationAt H
      (abstractFixedFieldUnitsEquivGaloisFixed
        K (SeparableClosure K) H.field (Additive.ofMul p)) :
      (localHenselianValuation K).valueGroup) : ZHat)) = 1
  rw [localHenselianValuation_valuationAt_abstractFixedField K H p]
  rw [hp]
  simp

/-- Under the canonical fixed-field unit identifications, the abstract
relative norm from an intrinsic fixed field is the ordinary field norm on
units. -/
theorem
    relativeNorm_intrinsicAbstractBase_abstractFixedFieldUnit
    (F : Type) [Field F]
    (S : ClosedSubgroup Gal(SeparableClosure F / F))
    (hSB : S.toSubgroup ≤ (intrinsicAbstractBase F).toSubgroup)
    [Finite
      ((intrinsicAbstractBase F).toSubgroup ⧸
        extensionSubgroup (intrinsicAbstractBase F) S hSB)]
    [FiniteDimensional F
      (abstractFixedField F (SeparableClosure F) S)]
    (p : (abstractFixedField F (SeparableClosure F) S)ˣ) :
    relativeNorm (intrinsicAbsoluteUnits F)
        (intrinsicAbstractBase F) S hSB
        (abstractFixedFieldUnitsEquivGaloisFixed
          F (SeparableClosure F) S (Additive.ofMul p)) =
      baseUnitsEquivGaloisAmbientFixed F (SeparableClosure F)
        (Additive.ofMul
          (normUnits F
            (abstractFixedField F (SeparableClosure F) S) p)) := by
  let L :=
    abstractFixedField F (SeparableClosure F) S
  let S' :=
    closedFixingSubgroup F (SeparableClosure F) L
  let hS'B : S'.toSubgroup ≤
      (intrinsicAbstractBase F).toSubgroup :=
    fixingSubgroupLeBase F (SeparableClosure F) L
  have hS'S : S' = S := by
    exact closedFixingSubgroup_abstractFixedField_eq
      F (SeparableClosure F) S
  let pi' : ambientFixedAddSubgroup
      (intrinsicAbsoluteUnits F) S' :=
    intermediateFieldUnitsEquivGaloisFixed
      F (SeparableClosure F) L (Additive.ofMul p)
  let pi : ambientFixedAddSubgroup
      (intrinsicAbsoluteUnits F) S :=
    abstractFixedFieldUnitsEquivGaloisFixed
      F (SeparableClosure F) S (Additive.ofMul p)
  let _hS'Finite : Finite
      ((intrinsicAbstractBase F).toSubgroup ⧸
        extensionSubgroup
          (intrinsicAbstractBase F) S' hS'B) :=
    inferInstance
  have hpiCoe : pi'.1 = pi.1 := by
    rfl
  have htransportCoe :=
    relativeNorm_coe_eq_of_closedSubgroup_eq
      (intrinsicAbsoluteUnits F)
      (intrinsicAbstractBase F) (intrinsicAbstractBase F)
      S' S hS'B hSB rfl hS'S pi' pi hpiCoe
  have htransport :
      relativeNorm (intrinsicAbsoluteUnits F)
          (intrinsicAbstractBase F) S' hS'B pi' =
        relativeNorm (intrinsicAbsoluteUnits F)
          (intrinsicAbstractBase F) S hSB pi := by
    apply Subtype.ext
    exact htransportCoe
  have hnorm :=
    relativeNorm_intermediateFieldUnit_of_isSeparable
      F (SeparableClosure F) L p
  change
    relativeNorm (intrinsicAbsoluteUnits F)
        (intrinsicAbstractBase F) S' hS'B pi' =
      baseUnitsEquivGaloisAmbientFixed F (SeparableClosure F)
        (Additive.ofMul (normUnits F L p)) at hnorm
  exact htransport.symm.trans hnorm

/-- Translating an abstract relative fixed-field unit through the fixed-field
unit equivalences sends its abstract relative norm to its ordinary field norm. -/
theorem
    relativeNorm_preimage_abstractRelativeFixedFieldUnit
    (K : Type) [Field K]
    (H L : ClosedSubgroup Gal(SeparableClosure K / K))
    (hLH : L.toSubgroup ≤ H.toSubgroup)
    [Finite
      (H.toSubgroup ⧸ extensionSubgroup H L hLH)]
    [Finite
      ((baseField
        Gal(SeparableClosure K / K)).toSubgroup ⧸
        extensionSubgroup
          (baseField Gal(SeparableClosure K / K))
          H (le_baseField H))]
    (p : (abstractRelativeFixedField
      K (SeparableClosure K) hLH)ˣ)
    (x : (abstractFixedField K (SeparableClosure K) H)ˣ)
    (hnorm :
      normUnits
          (abstractFixedField K (SeparableClosure K) H)
          (abstractRelativeFixedField K (SeparableClosure K) hLH)
          p =
        x) :
    Additive.toMul
        ((abstractFixedFieldUnitsEquivGaloisFixed
          K (SeparableClosure K) H).symm
          (relativeNorm
            (galoisAmbientUnitsRep K (SeparableClosure K))
            H L hLH
            (abstractRelativeFixedFieldUnitsEquivGaloisFixed
              K (SeparableClosure K) H L hLH
                (Additive.ofMul p)))) =
      x := by
  have hrelative :
      relativeNorm
          (galoisAmbientUnitsRep K (SeparableClosure K))
          H L hLH
          (abstractRelativeFixedFieldUnitsEquivGaloisFixed
            K (SeparableClosure K) H L hLH
              (Additive.ofMul p)) =
        abstractFixedFieldUnitsEquivGaloisFixed
          K (SeparableClosure K) H
            (Additive.ofMul x) := by
    rw [relativeNorm_abstractFixedFieldUnit_eq_normUnits]
    rw [hnorm]
  apply Additive.ofMul.injective
  change
    (abstractFixedFieldUnitsEquivGaloisFixed
      K (SeparableClosure K) H).symm
        (relativeNorm
          (galoisAmbientUnitsRep K (SeparableClosure K))
          H L hLH
          (abstractRelativeFixedFieldUnitsEquivGaloisFixed
            K (SeparableClosure K) H L hLH
              (Additive.ofMul p))) =
      Additive.ofMul x
  rw [hrelative,
    (abstractFixedFieldUnitsEquivGaloisFixed
      K (SeparableClosure K) H).symm_apply_apply]

/-- Evaluates the abstract fixed-field norm-residue symbol on the norm of a
prime element as the abelianized restriction of its Frobenius element. -/
theorem
    abstractFixedFieldNormResidueSymbol_eq_of_primeNorm
    (K : Type) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    (H : FiniteAbstractField
      Gal(SeparableClosure K / K))
    (J : ClosedSubgroup
      Gal(SeparableClosure K / K))
    (hJH : J.toSubgroup ≤ H.field.toSubgroup)
    [hJnormal :
      (extensionSubgroup H.field J hJH).Normal]
    [hJfinite : Finite
      (H.field.toSubgroup ⧸
        extensionSubgroup H.field J hJH)]
    (sigma :
      (localResidueDatum K).FrobeniusElements
        (H.toFiniteResidueAbstractField (localResidueDatum K))
        J hJH) :
    let S :=
      (localResidueDatum K).frobeniusFixedField
        (H.toFiniteResidueAbstractField (localResidueDatum K))
        J hJH sigma
    let hSH :=
      (localResidueDatum K).frobeniusFixedField_le
        (H.toFiniteResidueAbstractField (localResidueDatum K))
        J hJH sigma
    let hSabsolute :=
      (localResidueDatum K).frobeniusFixedField_absoluteFinite
        H J hJH sigma
    ∀ (p : (abstractRelativeFixedField
        K (SeparableClosure K) hSH)ˣ)
      (x : (abstractFixedField
        K (SeparableClosure K) H.field)ˣ),
      (localHenselianValuation K).IsPrimeElement
          ⟨S, hSabsolute⟩
          (abstractRelativeFixedFieldUnitsEquivGaloisFixed
            K (SeparableClosure K) H.field S hSH
              (Additive.ofMul p)) →
      normUnits
          (abstractFixedField K (SeparableClosure K) H.field)
          (abstractRelativeFixedField K (SeparableClosure K) hSH)
          p =
        x →
      abstractFixedFieldNormResidueSymbol
          K (SeparableClosure K)
          (localResidueDatum K)
          (localHenselianValuation K)
          (separableClosureUnits_isClassFormation K)
          H.field J hJH (Additive.ofMul x) =
        Additive.ofMul
          ((abstractExtensionQuotientEquivGaloisGroup
            K (SeparableClosure K) H.field J hJH hJnormal
            ).abelianizationCongr
            (Abelianization.of
              ((localResidueDatum K).frobeniusRestriction
                (H.toFiniteResidueAbstractField (localResidueDatum K))
                J hJH sigma))) := by
  dsimp only
  intro p x hprime hnorm
  let hHabsolute : Finite
      ((baseField
        Gal(SeparableClosure K / K)).toSubgroup ⧸
        extensionSubgroup
          (baseField Gal(SeparableClosure K / K))
          H.field (le_baseField H.field)) :=
    H.finite
  let S :=
    (localResidueDatum K).frobeniusFixedField
      (H.toFiniteResidueAbstractField (localResidueDatum K))
      J hJH sigma
  let hSH :=
    (localResidueDatum K).frobeniusFixedField_le
      (H.toFiniteResidueAbstractField (localResidueDatum K))
      J hJH sigma
  let hSabsolute :=
    (localResidueDatum K).frobeniusFixedField_absoluteFinite
      H J hJH sigma
  let hSfinite : Finite
      (H.field.toSubgroup ⧸
        extensionSubgroup H.field S hSH) :=
    (localResidueDatum K).frobeniusFixedField_finite
      (H.toFiniteResidueAbstractField (localResidueDatum K))
      J hJH sigma
  let SigmaS : FiniteAbstractField
      Gal(SeparableClosure K / K) :=
    ⟨S, hSabsolute⟩
  let pi : ambientFixedAddSubgroup
      (galoisAmbientUnitsRep K (SeparableClosure K)) S :=
    abstractRelativeFixedFieldUnitsEquivGaloisFixed
      K (SeparableClosure K) H.field S hSH
        (Additive.ofMul p)
  let qAmbient :=
    (localResidueDatum K).frobeniusRestriction
      (H.toFiniteResidueAbstractField (localResidueDatum K))
      J hJH sigma
  let qH :=
    abstractExtensionQuotientEquivGaloisGroup
      K (SeparableClosure K) H.field J hJH hJnormal
  have hx :
      Additive.toMul
          ((abstractFixedFieldUnitsEquivGaloisFixed
            K (SeparableClosure K) H.field).symm
            (relativeNorm
              (galoisAmbientUnitsRep K (SeparableClosure K))
              H.field S hSH pi)) =
        x := by
    exact
      relativeNorm_preimage_abstractRelativeFixedFieldUnit
        K H.field S hSH p x hnorm
  have hsymbol :=
    abstractFixedFieldNormResidueSymbol_apply_primeNorm
      K (SeparableClosure K)
      (localResidueDatum K)
      (localHenselianValuation K)
      (separableClosureUnits_isClassFormation K)
      H.field J hJH qAmbient sigma rfl pi hprime
  change
    abstractFixedFieldNormResidueSymbol
        K (SeparableClosure K)
        (localResidueDatum K)
        (localHenselianValuation K)
        (separableClosureUnits_isClassFormation K)
        H.field J hJH
        (Additive.ofMul
          (Additive.toMul
            ((abstractFixedFieldUnitsEquivGaloisFixed
              K (SeparableClosure K) H.field).symm
              (relativeNorm
                (galoisAmbientUnitsRep K (SeparableClosure K))
                H.field S hSH pi)))) =
      Additive.ofMul
        (qH.abelianizationCongr
          (Abelianization.of qAmbient)) at hsymbol
  rw [hx] at hsymbol
  exact hsymbol

/-- Transporting a valuation-one unit and its norm through compatible ring
equivalences evaluates the ambient fixed-field norm-residue symbol at the
associated Frobenius restriction. -/
theorem
    abstractFixedFieldNormResidueSymbol_eq_of_transportedValuationOneUnit
    (K F L : Type)
    [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    [Field F] [Field L] [Algebra F L] [FiniteDimensional F L]
    [ValuativeRel L] [TopologicalSpace L]
    [IsNonarchimedeanLocalField L]
    (H : FiniteAbstractField
      Gal(SeparableClosure K / K))
    (J : ClosedSubgroup
      Gal(SeparableClosure K / K))
    (hJH : J.toSubgroup ≤ H.field.toSubgroup)
    [hJnormal :
      (extensionSubgroup H.field J hJH).Normal]
    [hJfinite : Finite
      (H.field.toSubgroup ⧸
        extensionSubgroup H.field J hJH)]
    (sigma :
      (localResidueDatum K).FrobeniusElements
        (H.toFiniteResidueAbstractField (localResidueDatum K))
        J hJH) :
    let S :=
      (localResidueDatum K).frobeniusFixedField
        (H.toFiniteResidueAbstractField (localResidueDatum K))
        J hJH sigma
    let hSH :=
      (localResidueDatum K).frobeniusFixedField_le
        (H.toFiniteResidueAbstractField (localResidueDatum K))
        J hJH sigma
    let hSabsolute :=
      (localResidueDatum K).frobeniusFixedField_absoluteFinite
        H J hJH sigma
    let LH :=
      abstractRelativeFixedField K (SeparableClosure K) hSH
    let F₀ :=
      abstractFixedField K (SeparableClosure K) H.field
    ∀ [_hLHNorm : NontriviallyNormedField LH]
      [_hLHVal : ValuativeRel LH]
      [_hLHLocal : IsNonarchimedeanLocalField LH]
      [_hF₀LHFinite : FiniteDimensional F₀ LH]
      (phiF : F ≃+* F₀) (phi : L ≃+* LH)
      (_hcomm :
        RingHom.comp (algebraMap F₀ LH) phiF.toRingHom =
          RingHom.comp phi.toRingHom (algebraMap F L))
      (hmem : ∀ y : L,
        y ∈ (ValuativeRel.valuation L).valuationSubring ↔
          phi y ∈ (ValuativeRel.valuation LH).valuationSubring)
      (_hprime :
        (localHenselianValuation K).IsPrimeElement
          ⟨S, hSabsolute⟩
          (abstractRelativeFixedFieldUnitsEquivGaloisFixed
            K (SeparableClosure K) H.field S hSH
              (Additive.ofMul
                (Units.mapEquiv phi.toMulEquiv
                  (chosenValuationOneUnitOfRingEquiv
                    L LH phi hmem))))),
      abstractFixedFieldNormResidueSymbol
          K (SeparableClosure K)
          (localResidueDatum K)
          (localHenselianValuation K)
          (separableClosureUnits_isClassFormation K)
          H.field J hJH
          (Additive.ofMul
            (Units.mapEquiv phiF.toMulEquiv
              (normUnits F L
                (chosenValuationOneUnitOfRingEquiv
                  L LH phi hmem)))) =
        Additive.ofMul
          ((abstractExtensionQuotientEquivGaloisGroup
            K (SeparableClosure K) H.field J hJH hJnormal
            ).abelianizationCongr
            (Abelianization.of
              ((localResidueDatum K).frobeniusRestriction
                (H.toFiniteResidueAbstractField (localResidueDatum K))
                J hJH sigma))) := by
  dsimp only
  intro _hLHNorm _hLHVal _hLHLocal _hF₀LHFinite
    phiF phi hcomm hmem hprime
  let S :=
    (localResidueDatum K).frobeniusFixedField
      (H.toFiniteResidueAbstractField (localResidueDatum K))
      J hJH sigma
  let hSH :=
    (localResidueDatum K).frobeniusFixedField_le
      (H.toFiniteResidueAbstractField (localResidueDatum K))
      J hJH sigma
  let hSabsolute :=
    (localResidueDatum K).frobeniusFixedField_absoluteFinite
      H J hJH sigma
  let LH :=
    abstractRelativeFixedField K (SeparableClosure K) hSH
  let F₀ :=
    abstractFixedField K (SeparableClosure K) H.field
  let pF :=
    chosenValuationOneUnitOfRingEquiv L
      (abstractRelativeFixedField K (SeparableClosure K)
        ((localResidueDatum K).frobeniusFixedField_le
          (H.toFiniteResidueAbstractField (localResidueDatum K))
          J hJH sigma))
      phi hmem
  let pH :=
    Units.mapEquiv phi.toMulEquiv pF
  let SigmaH : FiniteAbstractField
      Gal(SeparableClosure K / K) :=
    ⟨(localResidueDatum K).frobeniusFixedField
        (H.toFiniteResidueAbstractField (localResidueDatum K))
        J hJH sigma,
      (localResidueDatum K).frobeniusFixedField_absoluteFinite
        H J hJH sigma⟩
  let piH :=
    abstractRelativeFixedFieldUnitsEquivGaloisFixed
      K (SeparableClosure K) H.field SigmaH.field
        ((localResidueDatum K).frobeniusFixedField_le
          (H.toFiniteResidueAbstractField (localResidueDatum K))
          J hJH sigma)
        (Additive.ofMul pH)
  let xPrime0 :=
    Units.mapEquiv phiF.toMulEquiv (normUnits F L pF)
  have hphiNorm :
      normUnits
          (abstractFixedField K (SeparableClosure K) H.field)
          (abstractRelativeFixedField K (SeparableClosure K)
            ((localResidueDatum K).frobeniusFixedField_le
              (H.toFiniteResidueAbstractField (localResidueDatum K))
              J hJH sigma))
          pH =
        xPrime0 := by
    exact
      normUnits_mapEquiv F L
        (abstractFixedField K (SeparableClosure K) H.field)
        (abstractRelativeFixedField K (SeparableClosure K)
          ((localResidueDatum K).frobeniusFixedField_le
            (H.toFiniteResidueAbstractField (localResidueDatum K))
            J hJH sigma))
        phiF phi hcomm pF
  exact
    abstractFixedFieldNormResidueSymbol_eq_of_primeNorm
      K H J hJH sigma pH xPrime0 hprime hphiNorm

end LocalClassFieldTheory
end
end

section
-- module Solutions.OAIQ244_DUKE.LocalClassFieldTheory_Finite_LocalReciprocity_FixedFieldIntrinsicReciprocity_AmbientPrimeWitness
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.GlobalClassFields.bigHilbertClassFieldNormSubgroup_normal _root_.GlobalClassFieldTheory.GlobalClassFields.finiteAbelianSubextensionAbstractRelativeFixedFieldFiniteDimensional _root_.GlobalClassFieldTheory.GlobalClassFields.finiteAbelianSubextensionAbstractRelativeFixedFieldIsAbelianGalois _root_.GlobalClassFieldTheory.Reciprocity.infinitePlaceComplexificationOverfield_algebra _root_.GlobalClassFieldTheory.Reciprocity.infinitePlaceComplexificationOverfield_baseAlgebra _root_.GlobalClassFieldTheory.Reciprocity.infinitePlaceComplexificationOverfield_baseSmul _root_.GlobalClassFieldTheory.Reciprocity.infinitePlaceComplexificationOverfield_smul _root_.GlobalClassFieldTheory.Reciprocity.rationalIdeleClassDirectLimitMonoid _root_.GlobalClassFieldTheory.Reciprocity.rationalIdeleClassDirectLimitSMul _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.DiscreteNthRootsSubgroup.instTopologicalSpaceSubtypeUnitsMemSubgroup _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.KummerTheory.primeCyclotomicBaseIsGalois _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.residueFieldZModAlgebra _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedIntegralAlgebraContextValuationSubringAlgebra _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedIntegralAlgebraContextValuationSubringTower _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedQPadicContextValuationSubringTower _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.LubinTate.compatibleGroupFamiliesGroup _root_.LubinTate.padicCompletedLevelField_algebra _root_.LubinTate.padicCompletedLevelField_isGalois _root_.LubinTate.padicCompletedLevelField_padicScalarTower _root_.LubinTate.padicCompletedUnramifiedFieldAlgebra _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.diagonalLogAction _root_.OAI.PrimeDegreePackets.instT2SpaceLocalAlgebra _root_.OAI.PrimeDegreePackets.instTopologicalSpaceLocalAlgebra _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.OAI.PrimeDegreePackets.xT2Space _root_.RayClass.Modulus.congruenceSubgroup_normal _root_.RayClass.approximationCompletionTopologicalSpace _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.RelativeIdeleGroup.relativeIdeleMulAction _root_.CyclicCohomology.binaryCoefficientFamilyCommGroup _root_.GlobalClassFieldTheory.Reciprocity.instNumberFieldSubtypeSeparableClosureRatMemIntermediateFieldAbstractFixedFieldOfFiniteQuotientAlgEquivSubgroupBaseFieldExtensionSubgroup _root_.GlobalClassFieldTheory.Reciprocity.instMonoidClassGroupRatSubtypeSeparableClosureMemIntermediateField _root_.GlobalClassFieldTheory.Reciprocity.instSMulAlgEquivRatSeparableClosureClassGroupSubtypeMemIntermediateField _root_.GlobalClassFieldTheory.Reciprocity.rationalAbstractRelativeClassGroupCommGroup _root_.GlobalClassFieldTheory.Reciprocity.rationalAbstractRelativeClassGroupMul _root_.GlobalClassFieldTheory.Reciprocity.rationalAbstractRelativeClassGroupMulOneClass _root_.LocalClassFieldTheory.normalizationIntegerRingIsIntegralClosure _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.adicCompletionProperSpace _root_.chosenFinitePlaceCompletionAlgebra _root_.chosenFinitePlaceLocalizedIntegerAlgebra _root_.chosenFinitePlaceLocalizedIsGalois _root_.cyclicPrimeDegreeIntermediate_isGalois _root_.cyclicPrimeSubextension_isGalois _root_.finiteIdeleGroupIsTopologicalGroup _root_.finiteIdeleGroupT2Space _root_.finiteLocalUnitsOpen _root_.finiteNormalClosure_isGalois _root_.ideleGroupIsTopologicalGroup _root_.ideleGroupT2Space _root_.infiniteAdeleRingT2Space _root_.infiniteIdeleGroupT2Space _root_.relativeAdeleRingIntermediateAlgebra _root_.relativeAdeleRingTopIntermediateAlgebra _root_.relativeUnrestrictedSPlaceFactorCommGroup
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

/-!
# Ambient prime witnesses

This module constructs the ambient norm-residue value, a valuation-one
prime witness for each abelianized Galois element, and the corresponding
ambient Frobenius target.
-/

noncomputable section

namespace LocalClassFieldTheory

open LocalFieldTheory RamificationTheory CyclicCohomology KummerTheory
open ClassFormation
open scoped ValuativeRel

/-- A prime-norm unit in the intrinsic base field chosen from a Frobenius
lift of an abelianized Galois element. -/
noncomputable def ambientEmbeddedPrimeWitness
    (K F E : Type)
    [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    [Field E] [Algebra K F] [Algebra F E] [Algebra K E]
    [IsScalarTower K F E]
    [FiniteDimensional K F] [Algebra.IsSeparable K F]
    [Valuation.HasExtension
      (ValuativeRel.valuation K) (ValuativeRel.valuation F)]
    [FiniteDimensional F E] [IsAbelianGalois F E]
    (j : E →ₐ[K] SeparableClosure K)
    (e : ambientEmbeddedSeparableClosureEquiv K F E j)
    (z : Abelianization Gal(E / F)) : Fˣ := by
  let i :=
    j.comp (IsScalarTower.toAlgHom K F E)
  letI : Algebra F (SeparableClosure K) :=
    i.toRingHom.toAlgebra
  let jF : E →ₐ[F] SeparableClosure K :=
    { j with commutes' := fun x => rfl }
  let jI : E →ₐ[F] SeparableClosure F :=
    e.symm.toAlgHom.comp jF
  let EI :=
    finiteGaloisAbstractExtensionOfEmbedding F E jI
  let H₀ :=
    closedFixingSubgroup K (SeparableClosure K)
      (AlgHom.fieldRange i)
  let J₀ :=
    closedFixingSubgroup K (SeparableClosure K)
      (AlgHom.fieldRange j)
  let hJH : J₀.toSubgroup ≤ H₀.toSubgroup := by
    change
      (AlgHom.fieldRange j).fixingSubgroup ≤
        (AlgHom.fieldRange i).fixingSubgroup
    apply (AlgHom.fieldRange i).fixingSubgroup_le
    intro x hx
    rcases hx with ⟨y, rfl⟩
    exact ⟨algebraMap F E y, rfl⟩
  letI hSourceNormal :
      (extensionSubgroup
        (intrinsicAbstractBase F) EI.field EI.below).Normal :=
    EI.normal
  letI hSourceFinite : Finite
      ((intrinsicAbstractBase F).toSubgroup ⧸
        extensionSubgroup
          (intrinsicAbstractBase F) EI.field EI.below) :=
    EI.finite
  letI hTargetNormal :
      (extensionSubgroup H₀ J₀ hJH).Normal :=
    ambientEmbeddedExtensionSubgroup_normal K F E j e
  letI hTargetFinite : Finite
      (H₀.toSubgroup ⧸ extensionSubgroup H₀ J₀ hJH) :=
    ambientEmbeddedExtensionQuotient_finite K F E j e
  letI hHabsolute : Finite
      ((baseField
        Gal(SeparableClosure K / K)).toSubgroup ⧸
        extensionSubgroup
          (baseField Gal(SeparableClosure K / K))
          H₀ (le_baseField H₀)) := by
    exact ambientEmbeddedAbsoluteQuotientFinite K F i
  let H : FiniteAbstractField
      Gal(SeparableClosure K / K) :=
    ⟨H₀, ambientEmbeddedAbsoluteQuotientFinite K F i⟩
  let qF :=
    finiteGaloisAbstractQuotientEquivGaloisGroupOfEmbedding
      F E jI
  let RF :=
    (intrinsicFiniteAbstractBase F).toFiniteResidueAbstractField
      (localResidueDatum F)
  letI _hRFFinite : Finite
      (RF.field.toSubgroup ⧸
        extensionSubgroup RF.field EI.field EI.below) := by
    change Finite
      ((intrinsicAbstractBase F).toSubgroup ⧸
        extensionSubgroup
          (intrinsicAbstractBase F) EI.field EI.below)
    exact hSourceFinite
  let RH :=
    H.toFiniteResidueAbstractField (localResidueDatum K)
  let zF : Abelianization EI.extensionQuotient :=
    qF.abelianizationCongr.symm z
  let q :=
    Classical.choose (QuotientGroup.mk_surjective zF)
  have hq :=
    Classical.choose_spec (QuotientGroup.mk_surjective zF)
  let sigma :=
    Classical.choose
      ((localResidueDatum F).frobeniusRestriction_surjective
        RF EI.field EI.below q)
  have hsigma :=
    Classical.choose_spec
      ((localResidueDatum F).frobeniusRestriction_surjective
        RF EI.field EI.below q)
  let sigmaH :=
    intrinsicFrobeniusElementToAmbientEmbeddedField
      K F E j e sigma
  let SF :=
    (localResidueDatum F).frobeniusFixedField
      RF EI.field EI.below sigma
  let hSFabsolute :=
    (localResidueDatum F).frobeniusFixedField_absoluteFinite
      (intrinsicFiniteAbstractBase F) EI.field EI.below sigma
  let LF :=
    abstractFixedField F (SeparableClosure F) SF
  let SH :=
    (localResidueDatum K).frobeniusFixedField
      RH J₀ hJH sigmaH
  let hSHH :=
    (localResidueDatum K).frobeniusFixedField_le
      RH J₀ hJH sigmaH
  let hSHabsolute :=
    (localResidueDatum K).frobeniusFixedField_absoluteFinite
      H J₀ hJH sigmaH
  let LH :=
    abstractRelativeFixedField K (SeparableClosure K) hSHH
  let iLH : F →ₐ[K] LH :=
    i.codRestrict (LH.restrictScalars K).toSubalgebra (fun x => by
      change i x ∈ IntermediateField.fixedField SH.toSubgroup
      rw [IntermediateField.mem_fixedField_iff]
      intro rho hrho
      have hrhoH : rho ∈ H₀.toSubgroup :=
        hSHH hrho
      change rho (i x) = i x
      change
        rho ∈ (AlgHom.fieldRange i).fixingSubgroup at hrhoH
      rw [IntermediateField.mem_fixingSubgroup_iff] at hrhoH
      exact hrhoH (i x) ⟨x, rfl⟩)
  let phi : LF ≃+* LH := by
    letI : Algebra F LH := iLH.toRingHom.toAlgebra
    exact
      (intrinsicFrobeniusFixedFieldEquivAmbientEmbeddedField
        K F E j e sigma).toRingEquiv
  have hphi (x : LF) :
      ((phi x : LH) : SeparableClosure K) =
        e (x : SeparableClosure F) := by
    exact
      intrinsicFrobeniusFixedFieldEquivAmbientEmbeddedField_apply_val
        K F E j e sigma x
  letI : FiniteDimensional F LF :=
    abstractFixedField_finiteDimensional
      F (SeparableClosure F) SF hSFabsolute
  letI : NontriviallyNormedField LF :=
    finiteExtensionSpectralNormedField F LF
  letI : ValuativeRel LF :=
    finiteExtensionSpectralValuativeRel F LF
  letI : IsNonarchimedeanLocalField LF :=
    finiteExtensionSpectralIsNonarchimedeanLocalField F LF
  letI : Valuation.HasExtension
      (ValuativeRel.valuation F) (ValuativeRel.valuation LF) :=
    finiteExtensionSpectralValuation_hasExtension F LF
  letI : FiniteDimensional K LH :=
    abstractFixedField_finiteDimensional
      K (SeparableClosure K) SH hSHabsolute
  let iH : LH →ₐ[K] SeparableClosure K :=
    LH.val.restrictScalars K
  letI : Algebra.IsSeparable K LH := by
    let : IsScalarTower K LH (SeparableClosure K) :=
      IsScalarTower.of_algebraMap_eq' (by
        apply RingHom.ext
        intro x
        exact (iH.commutes x).symm)
    exact
      Algebra.isSeparable_tower_bot_of_isSeparable
        K LH (SeparableClosure K)
  letI : NontriviallyNormedField LH :=
    finiteExtensionSpectralNormedField K LH
  letI : ValuativeRel LH :=
    finiteExtensionSpectralValuativeRel K LH
  letI : IsNonarchimedeanLocalField LH :=
    finiteExtensionSpectralIsNonarchimedeanLocalField K LH
  letI : Valuation.HasExtension
      (ValuativeRel.valuation K) (ValuativeRel.valuation LH) :=
    finiteExtensionSpectralValuation_hasExtension K LH
  have hmem (x : LF) :
      x ∈ (ValuativeRel.valuation LF).valuationSubring ↔
        phi x ∈ (ValuativeRel.valuation LH).valuationSubring := by
    exact
      valuationSubring_mem_iff_of_separableClosureRingEquiv
        F K LF LH LF.val iH e.toRingEquiv
        (localSeparableValuationSubring_eq_comap_finiteExtensionEquiv
          K F i e)
        phi hphi
        x
  let pF :=
    chosenValuationOneUnitOfRingEquiv LF LH phi hmem
  exact normUnits F LF pF


/-- The ambient abelianized Frobenius target associated with the same
chosen intrinsic Frobenius lift as the prime witness. -/
noncomputable def ambientEmbeddedPrimeTarget
    (K F E : Type)
    [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    [Field E] [Algebra K F] [Algebra F E] [Algebra K E]
    [IsScalarTower K F E]
    [FiniteDimensional K F] [Algebra.IsSeparable K F]
    [Valuation.HasExtension
      (ValuativeRel.valuation K) (ValuativeRel.valuation F)]
    [FiniteDimensional F E] [IsAbelianGalois F E]
    (j : E →ₐ[K] SeparableClosure K)
    (e : ambientEmbeddedSeparableClosureEquiv K F E j)
    (z : Abelianization Gal(E / F)) :
    Abelianization Gal(E / F) := by
  let i :=
    j.comp (IsScalarTower.toAlgHom K F E)
  letI : Algebra F (SeparableClosure K) :=
    i.toRingHom.toAlgebra
  let jF : E →ₐ[F] SeparableClosure K :=
    { j with commutes' := fun x => rfl }
  let jI : E →ₐ[F] SeparableClosure F :=
    e.symm.toAlgHom.comp jF
  let EI :=
    finiteGaloisAbstractExtensionOfEmbedding F E jI
  let H₀ :=
    closedFixingSubgroup K (SeparableClosure K)
      (AlgHom.fieldRange i)
  let J₀ :=
    closedFixingSubgroup K (SeparableClosure K)
      (AlgHom.fieldRange j)
  let hJH : J₀.toSubgroup ≤ H₀.toSubgroup := by
    change
      (AlgHom.fieldRange j).fixingSubgroup ≤
        (AlgHom.fieldRange i).fixingSubgroup
    apply (AlgHom.fieldRange i).fixingSubgroup_le
    intro x hx
    rcases hx with ⟨y, rfl⟩
    exact ⟨algebraMap F E y, rfl⟩
  letI hSourceNormal :
      (extensionSubgroup
        (intrinsicAbstractBase F) EI.field EI.below).Normal :=
    EI.normal
  letI hSourceFinite : Finite
      ((intrinsicAbstractBase F).toSubgroup ⧸
        extensionSubgroup
          (intrinsicAbstractBase F) EI.field EI.below) :=
    EI.finite
  letI hTargetNormal :
      (extensionSubgroup H₀ J₀ hJH).Normal :=
    ambientEmbeddedExtensionSubgroup_normal K F E j e
  letI hTargetFinite : Finite
      (H₀.toSubgroup ⧸ extensionSubgroup H₀ J₀ hJH) :=
    ambientEmbeddedExtensionQuotient_finite K F E j e
  letI hHabsolute : Finite
      ((baseField
        Gal(SeparableClosure K / K)).toSubgroup ⧸
        extensionSubgroup
          (baseField Gal(SeparableClosure K / K))
          H₀ (le_baseField H₀)) := by
    exact ambientEmbeddedAbsoluteQuotientFinite K F i
  let H : FiniteAbstractField
      Gal(SeparableClosure K / K) :=
    ⟨H₀, ambientEmbeddedAbsoluteQuotientFinite K F i⟩
  let qF :=
    finiteGaloisAbstractQuotientEquivGaloisGroupOfEmbedding
      F E jI
  let qE :=
    ambientEmbeddedExtensionQuotientEquivGaloisGroup
      K F E j e
  let RF :=
    (intrinsicFiniteAbstractBase F).toFiniteResidueAbstractField
      (localResidueDatum F)
  letI _hRFFinite : Finite
      (RF.field.toSubgroup ⧸
        extensionSubgroup RF.field EI.field EI.below) := by
    change Finite
      ((intrinsicAbstractBase F).toSubgroup ⧸
        extensionSubgroup
          (intrinsicAbstractBase F) EI.field EI.below)
    exact hSourceFinite
  let RH :=
    H.toFiniteResidueAbstractField (localResidueDatum K)
  let zF : Abelianization EI.extensionQuotient :=
    qF.abelianizationCongr.symm z
  let q :=
    Classical.choose (QuotientGroup.mk_surjective zF)
  let sigma :=
    Classical.choose
      ((localResidueDatum F).frobeniusRestriction_surjective
        RF EI.field EI.below q)
  let sigmaH :=
    intrinsicFrobeniusElementToAmbientEmbeddedField
      K F E j e sigma
  let qAmbient :=
    (localResidueDatum K).frobeniusRestriction
      RH J₀ hJH sigmaH
  exact
    qE.abelianizationCongr
      (Abelianization.of qAmbient)

end LocalClassFieldTheory
end
end

section
-- module Solutions.OAIQ244_DUKE.LocalClassFieldTheory_Finite_LocalReciprocity_FixedFieldIntrinsicReciprocity_AmbientPrimeSymbolSetup
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 400000
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.GlobalClassFields.bigHilbertClassFieldNormSubgroup_normal _root_.GlobalClassFieldTheory.GlobalClassFields.finiteAbelianSubextensionAbstractRelativeFixedFieldFiniteDimensional _root_.GlobalClassFieldTheory.GlobalClassFields.finiteAbelianSubextensionAbstractRelativeFixedFieldIsAbelianGalois _root_.GlobalClassFieldTheory.Reciprocity.infinitePlaceComplexificationOverfield_algebra _root_.GlobalClassFieldTheory.Reciprocity.infinitePlaceComplexificationOverfield_baseAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalIdeleClassDirectLimitMonoid _root_.GlobalClassFieldTheory.Reciprocity.rationalIdeleClassDirectLimitSMul _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.KummerTheory.primeCyclotomicBaseIsGalois _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.residueFieldZModAlgebra _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedIntegralAlgebraContextValuationSubringAlgebra _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedIntegralAlgebraContextValuationSubringTower _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedQPadicContextValuationSubringTower _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.LubinTate.compatibleGroupFamiliesGroup _root_.LubinTate.padicCompletedLevelField_algebra _root_.LubinTate.padicCompletedLevelField_isGalois _root_.LubinTate.padicCompletedLevelField_padicScalarTower _root_.LubinTate.padicCompletedUnramifiedFieldAlgebra _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.diagonalLogAction _root_.OAI.PrimeDegreePackets.instTopologicalSpaceLocalAlgebra _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.RayClass.Modulus.congruenceSubgroup_normal _root_.RayClass.approximationCompletionTopologicalSpace _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.RelativeIdeleGroup.relativeIdeleMulAction _root_.CyclicCohomology.binaryCoefficientFamilyCommGroup _root_.GlobalClassFieldTheory.Reciprocity.instNumberFieldSubtypeSeparableClosureRatMemIntermediateFieldAbstractFixedFieldOfFiniteQuotientAlgEquivSubgroupBaseFieldExtensionSubgroup _root_.GlobalClassFieldTheory.Reciprocity.instMonoidClassGroupRatSubtypeSeparableClosureMemIntermediateField _root_.GlobalClassFieldTheory.Reciprocity.instSMulAlgEquivRatSeparableClosureClassGroupSubtypeMemIntermediateField _root_.GlobalClassFieldTheory.Reciprocity.rationalAbstractRelativeClassGroupCommGroup _root_.GlobalClassFieldTheory.Reciprocity.rationalAbstractRelativeClassGroupMul _root_.GlobalClassFieldTheory.Reciprocity.rationalAbstractRelativeClassGroupMulOneClass _root_.LocalClassFieldTheory.normalizationIntegerRingIsIntegralClosure _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.adicCompletionProperSpace _root_.chosenFinitePlaceCompletionAlgebra _root_.chosenFinitePlaceLocalizedIntegerAlgebra _root_.chosenFinitePlaceLocalizedIsGalois _root_.cyclicPrimeDegreeIntermediate_isGalois _root_.cyclicPrimeSubextension_isGalois _root_.finiteLocalUnitsOpen _root_.finiteNormalClosure_isGalois _root_.infiniteAdeleRingT2Space _root_.relativeAdeleRingIntermediateAlgebra _root_.relativeAdeleRingTopIntermediateAlgebra _root_.relativeUnrestrictedSPlaceFactorCommGroup
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

/-!
# Ambient prime symbol setup

This module identifies the ambient norm-residue symbol of the chosen
prime witness with the Frobenius target transported back to the
original embedded Galois group.
-/

noncomputable section

namespace LocalClassFieldTheory

open LocalFieldTheory RamificationTheory CyclicCohomology KummerTheory
open ClassFormation
open scoped ValuativeRel

/-- The ambient fixed-field norm-residue value of the chosen prime
witness, transported to the original embedded Galois group. -/
noncomputable def ambientEmbeddedPrimeTransportValue
    (K F E : Type)
    [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    [Field E] [Algebra K F] [Algebra F E] [Algebra K E]
    [IsScalarTower K F E]
    [FiniteDimensional K F] [Algebra.IsSeparable K F]
    [Valuation.HasExtension
      (ValuativeRel.valuation K) (ValuativeRel.valuation F)]
    [FiniteDimensional F E] [IsAbelianGalois F E]
    (j : E →ₐ[K] SeparableClosure K)
    (e : ambientEmbeddedSeparableClosureEquiv K F E j)
    (z : Abelianization Gal(E / F)) :
    Abelianization Gal(E / F) := by
  let i :=
    j.comp (IsScalarTower.toAlgHom K F E)
  letI : Algebra F (SeparableClosure K) :=
    i.toRingHom.toAlgebra
  let H₀ :=
    closedFixingSubgroup K (SeparableClosure K)
      (AlgHom.fieldRange i)
  let J₀ :=
    closedFixingSubgroup K (SeparableClosure K)
      (AlgHom.fieldRange j)
  let hJH : J₀.toSubgroup ≤ H₀.toSubgroup := by
    change
      (AlgHom.fieldRange j).fixingSubgroup ≤
        (AlgHom.fieldRange i).fixingSubgroup
    apply (AlgHom.fieldRange i).fixingSubgroup_le
    intro x hx
    rcases hx with ⟨y, rfl⟩
    exact ⟨algebraMap F E y, rfl⟩
  letI hTargetNormal :
      (extensionSubgroup H₀ J₀ hJH).Normal :=
    ambientEmbeddedExtensionSubgroup_normal K F E j e
  letI hTargetFinite : Finite
      (H₀.toSubgroup ⧸ extensionSubgroup H₀ J₀ hJH) :=
    ambientEmbeddedExtensionQuotient_finite K F E j e
  letI hHabsolute : Finite
      ((baseField
        Gal(SeparableClosure K / K)).toSubgroup ⧸
        extensionSubgroup
          (baseField Gal(SeparableClosure K / K))
          H₀ (le_baseField H₀)) := by
    exact ambientEmbeddedAbsoluteQuotientFinite K F i
  let F₀ :=
    abstractFixedField K (SeparableClosure K) H₀
  let hfixed :
      F₀ = AlgHom.fieldRange i :=
    InfiniteGalois.fixedField_fixingSubgroup
      (AlgHom.fieldRange i)
  let phiF : F ≃ₐ[K] F₀ :=
    (i.equivFieldRange).trans
      (IntermediateField.equivOfEq hfixed.symm)
  let q₀ :=
    abstractExtensionQuotientEquivGaloisGroup
      K (SeparableClosure K) H₀ J₀ hJH hTargetNormal
  let qE :=
    ambientEmbeddedExtensionQuotientEquivGaloisGroup
      K F E j e
  exact
    qE.abelianizationCongr
      (q₀.abelianizationCongr.symm
        (Additive.toMul
          (abstractFixedFieldNormResidueSymbol
            K (SeparableClosure K)
            (localResidueDatum K)
            (localHenselianValuation K)
            (separableClosureUnits_isClassFormation K)
            H₀ J₀ hJH
            (Additive.ofMul
              (Units.mapEquiv phiF.toMulEquiv
                (ambientEmbeddedPrimeWitness K F E j e z))))))

/-- The fixed-field norm-residue symbol of the chosen prime witness is
the abelianized restriction of its ambient Frobenius lift. -/
noncomputable def ambientEmbeddedPrimeSymbolProperty
    (K F E : Type)
    [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    [Field E] [Algebra K F] [Algebra F E] [Algebra K E]
    [IsScalarTower K F E]
    [FiniteDimensional K F] [Algebra.IsSeparable K F]
    [Valuation.HasExtension
      (ValuativeRel.valuation K) (ValuativeRel.valuation F)]
    [FiniteDimensional F E] [IsAbelianGalois F E]
    (j : E →ₐ[K] SeparableClosure K)
    (e : ambientEmbeddedSeparableClosureEquiv K F E j)
    (z : Abelianization Gal(E / F)) : Prop := by
  let i :=
    j.comp (IsScalarTower.toAlgHom K F E)
  letI : Algebra F (SeparableClosure K) :=
    i.toRingHom.toAlgebra
  let jF : E →ₐ[F] SeparableClosure K :=
    { j with commutes' := fun x => rfl }
  let jI : E →ₐ[F] SeparableClosure F :=
    e.symm.toAlgHom.comp jF
  let EI :=
    finiteGaloisAbstractExtensionOfEmbedding F E jI
  let H₀ :=
    closedFixingSubgroup K (SeparableClosure K)
      (AlgHom.fieldRange i)
  let J₀ :=
    closedFixingSubgroup K (SeparableClosure K)
      (AlgHom.fieldRange j)
  let hJH : J₀.toSubgroup ≤ H₀.toSubgroup := by
    change
      (AlgHom.fieldRange j).fixingSubgroup ≤
        (AlgHom.fieldRange i).fixingSubgroup
    apply (AlgHom.fieldRange i).fixingSubgroup_le
    intro x hx
    rcases hx with ⟨y, rfl⟩
    exact ⟨algebraMap F E y, rfl⟩
  letI _hSourceNormal :
      (extensionSubgroup
        (intrinsicAbstractBase F) EI.field EI.below).Normal :=
    EI.normal
  letI hSourceFinite : Finite
      ((intrinsicAbstractBase F).toSubgroup ⧸
        extensionSubgroup
          (intrinsicAbstractBase F) EI.field EI.below) :=
    EI.finite
  letI hTargetNormal :
      (extensionSubgroup H₀ J₀ hJH).Normal :=
    ambientEmbeddedExtensionSubgroup_normal K F E j e
  letI hTargetFinite : Finite
      (H₀.toSubgroup ⧸ extensionSubgroup H₀ J₀ hJH) :=
    ambientEmbeddedExtensionQuotient_finite K F E j e
  letI hHabsolute : Finite
      ((baseField
        Gal(SeparableClosure K / K)).toSubgroup ⧸
        extensionSubgroup
          (baseField Gal(SeparableClosure K / K))
          H₀ (le_baseField H₀)) := by
    exact ambientEmbeddedAbsoluteQuotientFinite K F i
  let H : FiniteAbstractField
      Gal(SeparableClosure K / K) :=
    ⟨H₀, ambientEmbeddedAbsoluteQuotientFinite K F i⟩
  let F₀ :=
    abstractFixedField K (SeparableClosure K) H₀
  let hfixed :
      F₀ = AlgHom.fieldRange i :=
    InfiniteGalois.fixedField_fixingSubgroup
      (AlgHom.fieldRange i)
  let phiF : F ≃ₐ[K] F₀ :=
    (i.equivFieldRange).trans
      (IntermediateField.equivOfEq hfixed.symm)
  let qF :=
    finiteGaloisAbstractQuotientEquivGaloisGroupOfEmbedding
      F E jI
  let q₀ :=
    abstractExtensionQuotientEquivGaloisGroup
      K (SeparableClosure K) H₀ J₀ hJH hTargetNormal
  let RF :=
    (intrinsicFiniteAbstractBase F).toFiniteResidueAbstractField
      (localResidueDatum F)
  letI _hRFFinite : Finite
      (RF.field.toSubgroup ⧸
        extensionSubgroup RF.field EI.field EI.below) := by
    change Finite
      ((intrinsicAbstractBase F).toSubgroup ⧸
        extensionSubgroup
          (intrinsicAbstractBase F) EI.field EI.below)
    exact hSourceFinite
  let RH :=
    H.toFiniteResidueAbstractField (localResidueDatum K)
  let zF : Abelianization EI.extensionQuotient :=
    qF.abelianizationCongr.symm z
  let q :=
    Classical.choose (QuotientGroup.mk_surjective zF)
  let sigma :=
    Classical.choose
      ((localResidueDatum F).frobeniusRestriction_surjective
        RF EI.field EI.below q)
  let sigmaH :=
    intrinsicFrobeniusElementToAmbientEmbeddedField
      K F E j e sigma
  let qAmbient :=
    (localResidueDatum K).frobeniusRestriction
      RH J₀ hJH sigmaH
  exact
    abstractFixedFieldNormResidueSymbol
        K (SeparableClosure K)
        (localResidueDatum K)
        (localHenselianValuation K)
        (separableClosureUnits_isClassFormation K)
        H₀ J₀ hJH
        (Additive.ofMul
          (Units.mapEquiv phiF.toMulEquiv
            (ambientEmbeddedPrimeWitness K F E j e z))) =
      Additive.ofMul
        (q₀.abelianizationCongr
          (Abelianization.of qAmbient))

/-- The explicit fixed-field symbol formula identifies the transported
prime value with its ambient Frobenius target. -/
theorem
    ambientEmbeddedPrimeTransportValue_eq_target_of_symbol
    (K F E : Type)
    [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    [Field E] [Algebra K F] [Algebra F E] [Algebra K E]
    [IsScalarTower K F E]
    [FiniteDimensional K F] [Algebra.IsSeparable K F]
    [Valuation.HasExtension
      (ValuativeRel.valuation K) (ValuativeRel.valuation F)]
    [FiniteDimensional F E] [IsAbelianGalois F E]
    (j : E →ₐ[K] SeparableClosure K)
    (e : ambientEmbeddedSeparableClosureEquiv K F E j)
    (z : Abelianization Gal(E / F)) :
    let i :=
      j.comp (IsScalarTower.toAlgHom K F E)
    letI : Algebra F (SeparableClosure F) :=
      (separableClosure F (AlgebraicClosure F)).algebra
    letI : Algebra F (SeparableClosure K) :=
      i.toRingHom.toAlgebra
    let jF : E →ₐ[F] SeparableClosure K :=
      { j with commutes' := fun x => rfl }
    let jI : E →ₐ[F] SeparableClosure F :=
      e.symm.toAlgHom.comp jF
    let EI :=
      finiteGaloisAbstractExtensionOfEmbedding F E jI
    let H₀ :=
      closedFixingSubgroup K (SeparableClosure K)
        (AlgHom.fieldRange i)
    let J₀ :=
      closedFixingSubgroup K (SeparableClosure K)
        (AlgHom.fieldRange j)
    let hJH : J₀.toSubgroup ≤ H₀.toSubgroup := by
      change
        (AlgHom.fieldRange j).fixingSubgroup ≤
          (AlgHom.fieldRange i).fixingSubgroup
      apply (AlgHom.fieldRange i).fixingSubgroup_le
      intro x hx
      rcases hx with ⟨y, rfl⟩
      exact ⟨algebraMap F E y, rfl⟩
    letI _hSourceNormal :
        (extensionSubgroup
          (intrinsicAbstractBase F) EI.field EI.below).Normal :=
      EI.normal
    letI hSourceFinite : Finite
        ((intrinsicAbstractBase F).toSubgroup ⧸
          extensionSubgroup
            (intrinsicAbstractBase F) EI.field EI.below) :=
      EI.finite
    letI hTargetNormal :
        (extensionSubgroup H₀ J₀ hJH).Normal :=
      ambientEmbeddedExtensionSubgroup_normal K F E j e
    letI hTargetFinite : Finite
        (H₀.toSubgroup ⧸ extensionSubgroup H₀ J₀ hJH) :=
      ambientEmbeddedExtensionQuotient_finite K F E j e
    letI hHabsolute : Finite
        ((baseField
          Gal(SeparableClosure K / K)).toSubgroup ⧸
          extensionSubgroup
            (baseField Gal(SeparableClosure K / K))
            H₀ (le_baseField H₀)) := by
      exact ambientEmbeddedAbsoluteQuotientFinite K F i
    let H : FiniteAbstractField
        Gal(SeparableClosure K / K) :=
      ⟨H₀, ambientEmbeddedAbsoluteQuotientFinite K F i⟩
    let F₀ :=
      abstractFixedField K (SeparableClosure K) H₀
    let hfixed :
        F₀ = AlgHom.fieldRange i :=
      InfiniteGalois.fixedField_fixingSubgroup
        (AlgHom.fieldRange i)
    let phiF : F ≃ₐ[K] F₀ :=
      (i.equivFieldRange).trans
        (IntermediateField.equivOfEq hfixed.symm)
    let qF :=
      finiteGaloisAbstractQuotientEquivGaloisGroupOfEmbedding
        F E jI
    let q₀ :=
      abstractExtensionQuotientEquivGaloisGroup
        K (SeparableClosure K) H₀ J₀ hJH hTargetNormal
    let RF :=
      (intrinsicFiniteAbstractBase F).toFiniteResidueAbstractField
        (localResidueDatum F)
    letI _hRFFinite : Finite
        (RF.field.toSubgroup ⧸
          extensionSubgroup RF.field EI.field EI.below) := by
      change Finite
        ((intrinsicAbstractBase F).toSubgroup ⧸
          extensionSubgroup
            (intrinsicAbstractBase F) EI.field EI.below)
      exact hSourceFinite
    let RH :=
      H.toFiniteResidueAbstractField (localResidueDatum K)
    let zF : Abelianization EI.extensionQuotient :=
      qF.abelianizationCongr.symm z
    let q :=
      Classical.choose (QuotientGroup.mk_surjective zF)
    let sigma :=
      Classical.choose
        ((localResidueDatum F).frobeniusRestriction_surjective
          RF EI.field EI.below q)
    let sigmaH :=
      intrinsicFrobeniusElementToAmbientEmbeddedField
        K F E j e sigma
    let qAmbient :=
      (localResidueDatum K).frobeniusRestriction
        RH J₀ hJH sigmaH
    ∀ (_hsymbol :
        abstractFixedFieldNormResidueSymbol
            K (SeparableClosure K)
            (localResidueDatum K)
            (localHenselianValuation K)
            (separableClosureUnits_isClassFormation K)
            H₀ J₀ hJH
            (Additive.ofMul
              (Units.mapEquiv phiF.toMulEquiv
                (ambientEmbeddedPrimeWitness K F E j e z))) =
          Additive.ofMul
            (q₀.abelianizationCongr
              (Abelianization.of qAmbient))),
      ambientEmbeddedPrimeTransportValue K F E j e z =
        ambientEmbeddedPrimeTarget K F E j e z := by
  dsimp only
  intro hsymbol
  let i :=
    j.comp (IsScalarTower.toAlgHom K F E)
  let : Algebra F (SeparableClosure F) :=
    (separableClosure F (AlgebraicClosure F)).algebra
  let : Algebra F (SeparableClosure K) :=
    i.toRingHom.toAlgebra
  let H₀ :=
    closedFixingSubgroup K (SeparableClosure K)
      (AlgHom.fieldRange i)
  let J₀ :=
    closedFixingSubgroup K (SeparableClosure K)
      (AlgHom.fieldRange j)
  let hJH : J₀.toSubgroup ≤ H₀.toSubgroup := by
    change
      (AlgHom.fieldRange j).fixingSubgroup ≤
        (AlgHom.fieldRange i).fixingSubgroup
    apply (AlgHom.fieldRange i).fixingSubgroup_le
    intro x hx
    rcases hx with ⟨y, rfl⟩
    exact ⟨algebraMap F E y, rfl⟩
  let hTargetNormal :
      (extensionSubgroup H₀ J₀ hJH).Normal :=
    ambientEmbeddedExtensionSubgroup_normal K F E j e
  exact
    abelianizationCongr_symm_eq_primeTarget
      _ _ _ _ hsymbol

end LocalClassFieldTheory
end
end

section
-- module Solutions.OAIQ244_DUKE.LocalClassFieldTheory_Finite_LocalReciprocity_FixedFieldIntrinsicReciprocity_AmbientPrimeWitnessComparison
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 400000
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.GlobalClassFields.bigHilbertClassFieldNormSubgroup_normal _root_.GlobalClassFieldTheory.GlobalClassFields.finiteAbelianSubextensionAbstractRelativeFixedFieldFiniteDimensional _root_.GlobalClassFieldTheory.Reciprocity.infinitePlaceComplexificationOverfield_algebra _root_.GlobalClassFieldTheory.Reciprocity.infinitePlaceComplexificationOverfield_baseAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalIdeleClassDirectLimitMonoid _root_.GlobalClassFieldTheory.Reciprocity.rationalIdeleClassDirectLimitSMul _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.KummerTheory.primeCyclotomicBaseIsGalois _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.residueFieldZModAlgebra _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedIntegralAlgebraContextValuationSubringAlgebra _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedIntegralAlgebraContextValuationSubringTower _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedQPadicContextValuationSubringTower _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.LubinTate.compatibleGroupFamiliesGroup _root_.LubinTate.padicCompletedLevelField_algebra _root_.LubinTate.padicCompletedLevelField_isGalois _root_.LubinTate.padicCompletedLevelField_padicScalarTower _root_.LubinTate.padicCompletedUnramifiedFieldAlgebra _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.instTopologicalSpaceLocalAlgebra _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.RayClass.Modulus.congruenceSubgroup_normal _root_.RayClass.approximationCompletionTopologicalSpace _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.CyclicCohomology.binaryCoefficientFamilyCommGroup _root_.GlobalClassFieldTheory.Reciprocity.instNumberFieldSubtypeSeparableClosureRatMemIntermediateFieldAbstractFixedFieldOfFiniteQuotientAlgEquivSubgroupBaseFieldExtensionSubgroup _root_.GlobalClassFieldTheory.Reciprocity.instMonoidClassGroupRatSubtypeSeparableClosureMemIntermediateField _root_.GlobalClassFieldTheory.Reciprocity.instSMulAlgEquivRatSeparableClosureClassGroupSubtypeMemIntermediateField _root_.GlobalClassFieldTheory.Reciprocity.rationalAbstractRelativeClassGroupCommGroup _root_.GlobalClassFieldTheory.Reciprocity.rationalAbstractRelativeClassGroupMul _root_.GlobalClassFieldTheory.Reciprocity.rationalAbstractRelativeClassGroupMulOneClass _root_.LocalClassFieldTheory.normalizationIntegerRingIsIntegralClosure _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.adicCompletionProperSpace _root_.chosenFinitePlaceCompletionAlgebra _root_.chosenFinitePlaceLocalizedIsGalois _root_.cyclicPrimeDegreeIntermediate_isGalois _root_.cyclicPrimeSubextension_isGalois _root_.finiteLocalUnitsOpen _root_.finiteNormalClosure_isGalois _root_.infiniteAdeleRingT2Space _root_.relativeAdeleRingIntermediateAlgebra _root_.relativeAdeleRingTopIntermediateAlgebra _root_.relativeUnrestrictedSPlaceFactorCommGroup
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

/-!
# Local and ambient comparison for prime witnesses

The chosen ambient prime witness represents the prescribed abelianized
Galois element both under the concrete local Artin map and under the
ambient fixed-field norm-residue construction.
-/

noncomputable section

namespace LocalClassFieldTheory

open LocalFieldTheory RamificationTheory CyclicCohomology KummerTheory
open ClassFormation
open scoped ValuativeRel

/-- The ambient Frobenius target recovers the original abelianized
Galois element. -/
theorem
    ambientEmbeddedPrimeTarget_eq
    (K F E : Type)
    [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    [Field E] [Algebra K F] [Algebra F E] [Algebra K E]
    [IsScalarTower K F E]
    [FiniteDimensional K F] [Algebra.IsSeparable K F]
    [Valuation.HasExtension
      (ValuativeRel.valuation K) (ValuativeRel.valuation F)]
    [FiniteDimensional F E] [IsAbelianGalois F E]
    (j : E →ₐ[K] SeparableClosure K)
    (e : ambientEmbeddedSeparableClosureEquiv K F E j)
    (z : Abelianization Gal(E / F)) :
    ambientEmbeddedPrimeTarget K F E j e z = z := by
  let i :=
    j.comp (IsScalarTower.toAlgHom K F E)
  let : Algebra F (SeparableClosure K) :=
    i.toRingHom.toAlgebra
  let jF : E →ₐ[F] SeparableClosure K :=
    { j with commutes' := fun x => rfl }
  let jI : E →ₐ[F] SeparableClosure F :=
    e.symm.toAlgHom.comp jF
  let EI :=
    finiteGaloisAbstractExtensionOfEmbedding F E jI
  let H₀ :=
    closedFixingSubgroup K (SeparableClosure K)
      (AlgHom.fieldRange i)
  let J₀ :=
    closedFixingSubgroup K (SeparableClosure K)
      (AlgHom.fieldRange j)
  let hJH : J₀.toSubgroup ≤ H₀.toSubgroup := by
    change
      (AlgHom.fieldRange j).fixingSubgroup ≤
        (AlgHom.fieldRange i).fixingSubgroup
    apply (AlgHom.fieldRange i).fixingSubgroup_le
    intro x hx
    rcases hx with ⟨y, rfl⟩
    exact ⟨algebraMap F E y, rfl⟩
  let hSourceNormal :
      (extensionSubgroup
        (intrinsicAbstractBase F) EI.field EI.below).Normal :=
    EI.normal
  let hSourceFinite : Finite
      ((intrinsicAbstractBase F).toSubgroup ⧸
        extensionSubgroup
          (intrinsicAbstractBase F) EI.field EI.below) :=
    EI.finite
  let hTargetNormal :
      (extensionSubgroup H₀ J₀ hJH).Normal :=
    ambientEmbeddedExtensionSubgroup_normal K F E j e
  let hTargetFinite : Finite
      (H₀.toSubgroup ⧸ extensionSubgroup H₀ J₀ hJH) :=
    ambientEmbeddedExtensionQuotient_finite K F E j e
  let hHabsolute : Finite
      ((baseField
        Gal(SeparableClosure K / K)).toSubgroup ⧸
        extensionSubgroup
          (baseField Gal(SeparableClosure K / K))
          H₀ (le_baseField H₀)) := by
    exact ambientEmbeddedAbsoluteQuotientFinite K F i
  let H : FiniteAbstractField
      Gal(SeparableClosure K / K) :=
    ⟨H₀, ambientEmbeddedAbsoluteQuotientFinite K F i⟩
  let qF :=
    finiteGaloisAbstractQuotientEquivGaloisGroupOfEmbedding
      F E jI
  let qE :=
    ambientEmbeddedExtensionQuotientEquivGaloisGroup
      K F E j e
  let RF :=
    (intrinsicFiniteAbstractBase F).toFiniteResidueAbstractField
      (localResidueDatum F)
  let _hRFFinite : Finite
      (RF.field.toSubgroup ⧸
        extensionSubgroup RF.field EI.field EI.below) := by
    change Finite
      ((intrinsicAbstractBase F).toSubgroup ⧸
        extensionSubgroup
          (intrinsicAbstractBase F) EI.field EI.below)
    exact hSourceFinite
  let RH :=
    H.toFiniteResidueAbstractField (localResidueDatum K)
  let zF : Abelianization EI.extensionQuotient :=
    qF.abelianizationCongr.symm z
  let q :=
    Classical.choose (QuotientGroup.mk_surjective zF)
  have hq :=
    Classical.choose_spec (QuotientGroup.mk_surjective zF)
  let sigma :=
    Classical.choose
      ((localResidueDatum F).frobeniusRestriction_surjective
        RF EI.field EI.below q)
  have hsigma :=
    Classical.choose_spec
      ((localResidueDatum F).frobeniusRestriction_surjective
        RF EI.field EI.below q)
  let sigmaH :=
    intrinsicFrobeniusElementToAmbientEmbeddedField
      K F E j e sigma
  let qAmbient :=
    (localResidueDatum K).frobeniusRestriction
      RH J₀ hJH sigmaH
  have hrestriction :
      qE qAmbient = qF q := by
    calc
      qE qAmbient =
          qF ((localResidueDatum F).frobeniusRestriction
            RF EI.field EI.below sigma) :=
        intrinsicFrobeniusRestriction_compatibility_ambientEmbeddedField
          K F E j e sigma
      _ = qF q := congrArg qF hsigma
  have hqz :
      qF.abelianizationCongr (Abelianization.of q) = z := by
    calc
      qF.abelianizationCongr (Abelianization.of q) =
          qF.abelianizationCongr zF :=
        congrArg qF.abelianizationCongr hq
      _ = z :=
        qF.abelianizationCongr.apply_symm_apply z
  have htarget :
      ambientEmbeddedPrimeTarget K F E j e z =
        qE.abelianizationCongr
          (Abelianization.of qAmbient) := by
    rfl
  rw [htarget]
  calc
    qE.abelianizationCongr
        (Abelianization.of qAmbient) =
        Abelianization.of (qE qAmbient) :=
      abelianizationCongr_of qE qAmbient
    _ = Abelianization.of (qF q) :=
      congrArg Abelianization.of hrestriction
    _ = qF.abelianizationCongr
          (Abelianization.of q) :=
      (abelianizationCongr_of qF q).symm
    _ = z := hqz

end LocalClassFieldTheory
end
end

section
-- module Solutions.OAIQ244_DUKE.LocalClassFieldTheory_Finite_LocalReciprocity_FixedFieldIntrinsicReciprocity_AmbientPrimeComparison
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 400000
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.GlobalClassFields.finiteAbelianSubextensionAbstractRelativeFixedFieldFiniteDimensional _root_.GlobalClassFieldTheory.GlobalClassFields.finiteAbelianSubextensionAbstractRelativeFixedFieldIsAbelianGalois _root_.GlobalClassFieldTheory.Reciprocity.infinitePlaceComplexificationOverfield_algebra _root_.GlobalClassFieldTheory.Reciprocity.infinitePlaceComplexificationOverfield_baseAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalIdeleClassDirectLimitMonoid _root_.GlobalClassFieldTheory.Reciprocity.rationalIdeleClassDirectLimitSMul _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.KummerTheory.primeCyclotomicBaseIsGalois _root_.LocalClassFieldTheory.realComplexNormQuotientFinite _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.residueFieldZModAlgebra _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedIntegralAlgebraContextValuationSubringAlgebra _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedIntegralAlgebraContextValuationSubringTower _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedQPadicContextValuationSubringTower _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.LubinTate.compatibleGroupFamiliesGroup _root_.LubinTate.padicCompletedLevelField_algebra _root_.LubinTate.padicCompletedLevelField_isGalois _root_.LubinTate.padicCompletedLevelField_padicScalarTower _root_.LubinTate.padicCompletedUnramifiedFieldAlgebra _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.diagonalLogAction _root_.OAI.PrimeDegreePackets.instTopologicalSpaceLocalAlgebra _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.RayClass.approximationCompletionTopologicalSpace _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.RelativeIdeleGroup.relativeIdeleMulAction _root_.CyclicCohomology.binaryCoefficientFamilyCommGroup _root_.GlobalClassFieldTheory.Reciprocity.instNumberFieldSubtypeSeparableClosureRatMemIntermediateFieldAbstractFixedFieldOfFiniteQuotientAlgEquivSubgroupBaseFieldExtensionSubgroup _root_.GlobalClassFieldTheory.Reciprocity.instMonoidClassGroupRatSubtypeSeparableClosureMemIntermediateField _root_.GlobalClassFieldTheory.Reciprocity.instSMulAlgEquivRatSeparableClosureClassGroupSubtypeMemIntermediateField _root_.GlobalClassFieldTheory.Reciprocity.rationalAbstractRelativeClassGroupCommGroup _root_.GlobalClassFieldTheory.Reciprocity.rationalAbstractRelativeClassGroupMul _root_.GlobalClassFieldTheory.Reciprocity.rationalAbstractRelativeClassGroupMulOneClass _root_.LocalClassFieldTheory.normalizationIntegerRingIsIntegralClosure _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.adicCompletionProperSpace _root_.chosenFinitePlaceCompletionAlgebra _root_.chosenFinitePlaceLocalizedIntegerAlgebra _root_.chosenFinitePlaceLocalizedIsGalois _root_.cyclicPrimeDegreeIntermediate_isGalois _root_.cyclicPrimeSubextension_isGalois _root_.finiteLocalUnitsOpen _root_.finiteNormalClosure_isGalois _root_.infiniteAdeleRingT2Space _root_.relativeAdeleRingIntermediateAlgebra _root_.relativeAdeleRingTopIntermediateAlgebra _root_.relativeUnrestrictedSPlaceFactorCommGroup
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI
attribute [local instance] OAI.starSubalgebraCommCStarAlgebra

set_option autoImplicit false

/-!
# Ambient prime comparison

The local Artin map and the ambient embedded norm-residue construction
agree on norm classes and therefore agree pointwise.
-/

noncomputable section

namespace LocalClassFieldTheory

open LocalFieldTheory RamificationTheory CyclicCohomology KummerTheory
open ClassFormation
open scoped ValuativeRel
open scoped IsMulCommutative

/-- The ambient embedded norm-residue element depends only on the unit's norm
class modulo norms from `E`. -/
theorem
    ambientEmbeddedNormResidueAbelianElement_eq_of_normClass_eq
    (K F E : Type)
    [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    [Field E] [Algebra K F] [Algebra F E] [Algebra K E]
    [IsScalarTower K F E]
    [FiniteDimensional K F] [Algebra.IsSeparable K F]
    [Valuation.HasExtension
      (ValuativeRel.valuation K) (ValuativeRel.valuation F)]
    [FiniteDimensional F E] [IsAbelianGalois F E]
    (j : E →ₐ[K] SeparableClosure K)
    (e : ambientEmbeddedSeparableClosureEquiv K F E j)
    (a x : Fˣ)
    (h : normClass F E a = normClass F E x) :
    ambientEmbeddedNormResidueAbelianElement K F E j e a =
      ambientEmbeddedNormResidueAbelianElement K F E j e x := by
  let i :=
    j.comp (IsScalarTower.toAlgHom K F E)
  let : Algebra F (SeparableClosure K) :=
    i.toRingHom.toAlgebra
  let H₀ :=
    closedFixingSubgroup K (SeparableClosure K)
      (AlgHom.fieldRange i)
  let J₀ :=
    closedFixingSubgroup K (SeparableClosure K)
      (AlgHom.fieldRange j)
  let hJH : J₀.toSubgroup ≤ H₀.toSubgroup := by
    change
      (AlgHom.fieldRange j).fixingSubgroup ≤
        (AlgHom.fieldRange i).fixingSubgroup
    apply (AlgHom.fieldRange i).fixingSubgroup_le
    intro y hy
    rcases hy with ⟨z, rfl⟩
    exact ⟨algebraMap F E z, rfl⟩
  let hTargetNormal :
      (extensionSubgroup H₀ J₀ hJH).Normal :=
    ambientEmbeddedExtensionSubgroup_normal K F E j e
  let hTargetFinite : Finite
      (H₀.toSubgroup ⧸ extensionSubgroup H₀ J₀ hJH) :=
    ambientEmbeddedExtensionQuotient_finite K F E j e
  let hHabsolute : Finite
      ((baseField
        Gal(SeparableClosure K / K)).toSubgroup ⧸
        extensionSubgroup
          (baseField Gal(SeparableClosure K / K))
          H₀ (le_baseField H₀)) := by
    exact ambientEmbeddedAbsoluteQuotientFinite K F i
  let F₀ :=
    abstractFixedField K (SeparableClosure K) H₀
  have hfixed :
      F₀ = AlgHom.fieldRange i :=
    InfiniteGalois.fixedField_fixingSubgroup
      (AlgHom.fieldRange i)
  let phiF : F ≃ₐ[K] F₀ :=
    (i.equivFieldRange).trans
      (IntermediateField.equivOfEq hfixed.symm)
  let E₀ :=
    abstractRelativeFixedField K (SeparableClosure K) hJH
  have hfixedE :
      abstractFixedField K (SeparableClosure K) J₀ =
        AlgHom.fieldRange j :=
    InfiniteGalois.fixedField_fixingSubgroup
      (AlgHom.fieldRange j)
  let phiE : E ≃+* E₀ := by
    change
      E ≃+*
        abstractFixedField K (SeparableClosure K) J₀
    exact
      ((j.equivFieldRange).trans
        (IntermediateField.equivOfEq hfixedE.symm)).toRingEquiv
  let q₀ :=
    abstractExtensionQuotientEquivGaloisGroup
      K (SeparableClosure K) H₀ J₀ hJH hTargetNormal
  let qE :=
    ambientEmbeddedExtensionQuotientEquivGaloisGroup
      K F E j e
  let aF0 : F₀ˣ :=
    Units.mapEquiv phiF.toMulEquiv a
  let xF0 : F₀ˣ :=
    Units.mapEquiv phiF.toMulEquiv x
  have hnormClass0 :
      normClass F₀ E₀ aF0 =
        normClass F₀ E₀ xF0 := by
    exact
      normClass_mapEquiv F E F₀ E₀
        phiF.toRingEquiv phiE
        (by
          apply RingHom.ext
          intro y
          rfl)
        a x h
  have hambientSame :
      abstractFixedFieldNormResidueSymbol
          K (SeparableClosure K)
          (localResidueDatum K)
          (localHenselianValuation K)
          (separableClosureUnits_isClassFormation K)
          H₀ J₀ hJH (Additive.ofMul aF0) =
        abstractFixedFieldNormResidueSymbol
          K (SeparableClosure K)
          (localResidueDatum K)
          (localHenselianValuation K)
          (separableClosureUnits_isClassFormation K)
          H₀ J₀ hJH (Additive.ofMul xF0) :=
    abstractFixedFieldNormResidueSymbol_eq_of_normClass_eq
      K (SeparableClosure K)
      (localResidueDatum K)
      (localHenselianValuation K)
      (separableClosureUnits_isClassFormation K)
      H₀ J₀ hJH aF0 xF0 hnormClass0
  change
    qE.abelianizationCongr
        (q₀.abelianizationCongr.symm
          (Additive.toMul
            (abstractFixedFieldNormResidueSymbol
              K (SeparableClosure K)
              (localResidueDatum K)
              (localHenselianValuation K)
              (separableClosureUnits_isClassFormation K)
              H₀ J₀ hJH (Additive.ofMul aF0)))) =
      qE.abelianizationCongr
        (q₀.abelianizationCongr.symm
          (Additive.toMul
            (abstractFixedFieldNormResidueSymbol
              K (SeparableClosure K)
              (localResidueDatum K)
              (localHenselianValuation K)
              (separableClosureUnits_isClassFormation K)
              H₀ J₀ hJH (Additive.ofMul xF0))))
  rw [hambientSame]

end LocalClassFieldTheory
end
end

section
-- module Solutions.OAIQ244_DUKE.LocalClassFieldTheory_Finite_LocalReciprocity_FixedFieldIntrinsicReciprocity_NormRestriction
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 400000
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.GlobalClassFields.bigHilbertClassFieldNormSubgroup_normal _root_.GlobalClassFieldTheory.GlobalClassFields.finiteAbelianSubextensionAbstractRelativeFixedFieldFiniteDimensional _root_.GlobalClassFieldTheory.GlobalClassFields.finiteAbelianSubextensionAbstractRelativeFixedFieldIsAbelianGalois _root_.GlobalClassFieldTheory.Reciprocity.infinitePlaceComplexificationOverfield_algebra _root_.GlobalClassFieldTheory.Reciprocity.infinitePlaceComplexificationOverfield_baseAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalIdeleClassDirectLimitMonoid _root_.GlobalClassFieldTheory.Reciprocity.rationalIdeleClassDirectLimitSMul _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.KummerTheory.primeCyclotomicBaseIsGalois _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.residueFieldZModAlgebra _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedIntegralAlgebraContextValuationSubringAlgebra _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedIntegralAlgebraContextValuationSubringTower _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedIntegralLatticeContextModuleFinite _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedQPadicContextValuationSubringTower _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.LubinTate.compatibleGroupFamiliesGroup _root_.LubinTate.padicCompletedLevelCompleteDVF_hasExtensionInstance _root_.LubinTate.padicCompletedLevelField_algebra _root_.LubinTate.padicCompletedLevelField_isGalois _root_.LubinTate.padicCompletedLevelField_padicScalarTower _root_.LubinTate.padicCompletedUnramifiedFieldAlgebra _root_.LubinTate.standardLubinTateLevelValuationSubring_moduleFinite _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.diagonalLogAction _root_.OAI.PrimeDegreePackets.instTopologicalSpaceLocalAlgebra _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.RayClass.Modulus.congruenceSubgroup_normal _root_.RayClass.approximationCompletionTopologicalSpace _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.RelativeIdeleGroup.relativeIdeleMulAction _root_.CyclicCohomology.binaryCoefficientFamilyCommGroup _root_.GlobalClassFieldTheory.Reciprocity.instNumberFieldSubtypeSeparableClosureRatMemIntermediateFieldAbstractFixedFieldOfFiniteQuotientAlgEquivSubgroupBaseFieldExtensionSubgroup _root_.GlobalClassFieldTheory.Reciprocity.instMonoidClassGroupRatSubtypeSeparableClosureMemIntermediateField _root_.GlobalClassFieldTheory.Reciprocity.instSMulAlgEquivRatSeparableClosureClassGroupSubtypeMemIntermediateField _root_.GlobalClassFieldTheory.Reciprocity.rationalAbstractRelativeClassGroupCommGroup _root_.GlobalClassFieldTheory.Reciprocity.rationalAbstractRelativeClassGroupMul _root_.GlobalClassFieldTheory.Reciprocity.rationalAbstractRelativeClassGroupMulOneClass _root_.LocalClassFieldTheory.normalizationIntegerRingIsIntegralClosure _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.adicCompletionProperSpace _root_.chosenFinitePlaceCompletionAlgebra _root_.chosenFinitePlaceLocalizedIntegerAlgebra _root_.chosenFinitePlaceLocalizedIsGalois _root_.chosenFinitePlaceLocalizedValuationHasExtension _root_.cyclicPrimeDegreeIntermediate_isGalois _root_.cyclicPrimeSubextension_isGalois _root_.finiteLocalUnitsOpen _root_.finiteNormalClosure_isGalois _root_.infiniteAdeleRingT2Space _root_.relativeAdeleRingIntermediateAlgebra _root_.relativeAdeleRingTopIntermediateAlgebra _root_.relativeUnrestrictedSPlaceFactorCommGroup _root_.scaledRelativeIntegerLatticeQuotientFinite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI
attribute [local instance] OAI.starSubalgebraCommCStarAlgebra

set_option autoImplicit false

/-!
# Norm--restriction for local Artin maps

This module proves norm--restriction naturality for actual finite abelian local Artin maps.
-/

noncomputable section

namespace LocalClassFieldTheory

open LocalFieldTheory RamificationTheory CyclicCohomology KummerTheory
open ClassFormation
open scoped IsMulCommutative ValuativeRel

/-- The actual abstract fixed-field norm-residue symbols commute with norm and
restriction through the canonical quotient equivalences of the presentations. -/
theorem AmbientEmbeddedFixedFieldPresentation.fixedFieldNormResidueTransport
    (K K' L L' : Type)
    [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    [Field K'] [ValuativeRel K'] [TopologicalSpace K']
    [IsNonarchimedeanLocalField K']
    [Field L] [Field L']
    [Algebra K K'] [Algebra K L] [Algebra K L']
    [Algebra K' L'] [Algebra L L']
    [IsScalarTower K K' L'] [IsScalarTower K L L']
    [FiniteDimensional K K'] [Algebra.IsSeparable K K']
    [Valuation.HasExtension
      (ValuativeRel.valuation K) (ValuativeRel.valuation K')]
    [FiniteDimensional K L] [IsAbelianGalois K L]
    [FiniteDimensional K' L'] [IsAbelianGalois K' L']
    {jLower : L →ₐ[K] SeparableClosure K}
    {jUpper : L' →ₐ[K] SeparableClosure K}
    (lower : AmbientEmbeddedFixedFieldPresentation K K L jLower)
    (upper : AmbientEmbeddedFixedFieldPresentation K K' L' jUpper)
    (hH'H : upper.base.field.toSubgroup ≤ lower.base.field.toSubgroup)
    (hJ'J : upper.extension.field.toSubgroup ≤
      lower.extension.field.toSubgroup)
    [hJnormal :
      (extensionSubgroup lower.base.field lower.extension.field
        lower.extension.below).Normal]
    [_hJfinite : Finite
      (lower.base.field.toSubgroup ⧸
        extensionSubgroup lower.base.field lower.extension.field
          lower.extension.below)]
    [hJ'normal :
      (extensionSubgroup upper.base.field upper.extension.field
        upper.extension.below).Normal]
    [_hJ'finite : Finite
      (upper.base.field.toSubgroup ⧸
        extensionSubgroup upper.base.field upper.extension.field
          upper.extension.below)]
    [_hHabsolute : Finite
      ((baseField Gal(SeparableClosure K / K)).toSubgroup ⧸
        extensionSubgroup
          (baseField Gal(SeparableClosure K / K))
          lower.base.field (le_baseField lower.base.field))]
    [_hH'absolute : Finite
      ((baseField Gal(SeparableClosure K / K)).toSubgroup ⧸
        extensionSubgroup
          (baseField Gal(SeparableClosure K / K))
          upper.base.field (le_baseField upper.base.field))]
    [_hH'finite : Finite
      (lower.base.field.toSubgroup ⧸
        extensionSubgroup lower.base.field upper.base.field hH'H)]
    (hbase : ∀ x : L,
      jUpper (algebraMap L L' x) = jLower x)
    (a : K'ˣ) :
    normResidueNaturalityAbelianizedRestriction
        lower.base.field upper.base.field
        lower.extension.field upper.extension.field
        lower.extension.below upper.extension.below
        hH'H hJ'J
        ((upper.extension.extensionQuotientMulEquiv.symm.trans
          upper.fixedFieldQuotientEquiv).abelianizationCongr.symm
          (Additive.toMul
            (abstractFixedFieldNormResidueSymbol
              K (SeparableClosure K)
              (localResidueDatum K)
              (localHenselianValuation K)
              (separableClosureUnits_isClassFormation K)
              upper.base.field upper.extension.field
              upper.extension.below
              (Additive.ofMul
                (Units.mapEquiv upper.baseEquiv.toMulEquiv a))))) =
      (lower.extension.extensionQuotientMulEquiv.symm.trans
        lower.fixedFieldQuotientEquiv).abelianizationCongr.symm
        (Additive.toMul
          (abstractFixedFieldNormResidueSymbol
            K (SeparableClosure K)
            (localResidueDatum K)
            (localHenselianValuation K)
            (separableClosureUnits_isClassFormation K)
            lower.base.field lower.extension.field
            lower.extension.below
            (Additive.ofMul
              (Units.mapEquiv lower.baseEquiv.toMulEquiv
                (normUnits K K' a))))) := by
  let H := lower.base.field
  let H' := upper.base.field
  let J := lower.extension.field
  let J' := upper.extension.field
  let hJH : J.toSubgroup ≤ H.toSubgroup := lower.extension.below
  let hJ'H' : J'.toSubgroup ≤ H'.toSubgroup := upper.extension.below
  let qActualLower :=
    lower.extension.extensionQuotientMulEquiv.symm.trans
      lower.fixedFieldQuotientEquiv
  let qActualUpper :=
    upper.extension.extensionQuotientMulEquiv.symm.trans
      upper.fixedFieldQuotientEquiv
  let FLower :=
    abstractFixedField K (SeparableClosure K) H
  let phiLower : K ≃ₐ[K] FLower :=
    lower.baseEquiv
  let FUpper :=
    abstractFixedField K (SeparableClosure K) H'
  let : Algebra FLower FUpper :=
    RingHom.toAlgebra
      (IntermediateField.inclusion
        (abstractFixedField_le K (SeparableClosure K) hH'H))
  let phiUpper : K' ≃ₐ[K] FUpper :=
    upper.baseEquiv
  have hphiComm :
      RingHom.comp (algebraMap FLower FUpper)
          phiLower.toRingEquiv.toRingHom =
        RingHom.comp phiUpper.toRingEquiv.toRingHom
          (algebraMap K K') := by
    apply RingHom.ext
    intro x
    apply FUpper.val.injective
    change
      ((phiLower x : FLower) : SeparableClosure K) =
        ((phiUpper (algebraMap K K' x) : FUpper) : SeparableClosure K)
    rw [lower.baseEquiv_apply, upper.baseEquiv_apply,
      lower.baseEmbedding_eq, upper.baseEmbedding_eq]
    change
      jLower (algebraMap K L x) =
        jUpper (algebraMap K' L' (algebraMap K K' x))
    calc
      jLower (algebraMap K L x) =
          jUpper (algebraMap L L' (algebraMap K L x)) :=
        (hbase (algebraMap K L x)).symm
      _ = jUpper (algebraMap K' L' (algebraMap K K' x)) := by
        rw [← IsScalarTower.algebraMap_apply K L L',
          ← IsScalarTower.algebraMap_apply K K' L']
  let aUpper : FUpperˣ :=
    Units.mapEquiv phiUpper.toMulEquiv a
  let aLower : FLowerˣ :=
    Units.mapEquiv phiLower.toMulEquiv (normUnits K K' a)
  have hbaseNorm :
      abstractFixedFieldNormUnits
          K (SeparableClosure K) H H' hH'H
          (Additive.ofMul aUpper) =
        Additive.ofMul aLower := by
    exact
      congrArg Additive.toMul
        (normUnits_mapEquiv
          K K' FLower FUpper
          phiLower.toRingEquiv phiUpper.toRingEquiv
          hphiComm a)
  let symbolUpper :=
    abstractFixedFieldNormResidueSymbol
      K (SeparableClosure K)
      (localResidueDatum K)
      (localHenselianValuation K)
      (separableClosureUnits_isClassFormation K)
      H' J' hJ'H'
  let symbolLower :=
    abstractFixedFieldNormResidueSymbol
      K (SeparableClosure K)
      (localResidueDatum K)
      (localHenselianValuation K)
      (separableClosureUnits_isClassFormation K)
      H J hJH
  have hnaturality :=
    DFunLike.congr_fun
      (abstractFixedFieldNormResidueSymbol_norm_restriction
        K (SeparableClosure K)
        (localResidueDatum K)
        (localHenselianValuation K)
        (separableClosureUnits_isClassFormation K)
        H H' J J' hJH hJ'H' hH'H hJ'J)
      (Additive.ofMul aUpper)
  have hrawActual :
      normResidueNaturalityAbelianizedRestriction
          H H' J J' hJH hJ'H' hH'H hJ'J
          (qActualUpper.abelianizationCongr.symm
            (Additive.toMul
              (symbolUpper (Additive.ofMul aUpper)))) =
        qActualLower.abelianizationCongr.symm
          (Additive.toMul
            (symbolLower (Additive.ofMul aLower))) := by
    change
      (abstractFixedFieldAbelianizedRestriction
          K (SeparableClosure K) H H' J J'
          hJH hJ'H' hH'H hJ'J)
          (symbolUpper (Additive.ofMul aUpper)) =
        symbolLower
          (abstractFixedFieldNormUnits
            K (SeparableClosure K) H H' hH'H
            (Additive.ofMul aUpper)) at hnaturality
    rw [hbaseNorm] at hnaturality
    have hmul := congrArg Additive.toMul hnaturality
    change
      qActualLower.abelianizationCongr
          (normResidueNaturalityAbelianizedRestriction
            H H' J J' hJH hJ'H' hH'H hJ'J
            (qActualUpper.abelianizationCongr.symm
              (Additive.toMul
                (symbolUpper (Additive.ofMul aUpper))))) =
        Additive.toMul
          (symbolLower (Additive.ofMul aLower)) at hmul
    exact qActualLower.abelianizationCongr.eq_symm_apply.mpr hmul
  simpa only [H, H', J, J', hJH, hJ'H', qActualLower, qActualUpper,
    aUpper, aLower, symbolUpper, symbolLower] using
    hrawActual

end LocalClassFieldTheory
end
end

section
-- module Solutions.OAIQ244_DUKE.GlobalClassFieldTheory_Reciprocity_FiniteIdeleArtin
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.GlobalClassFields.ConductorialSubgroup.finiteIndex _root_.GlobalClassFieldTheory.GlobalClassFields.bigHilbertClassFieldNormSubgroup_normal _root_.GlobalClassFieldTheory.GlobalClassFields.smallHilbertClassFieldNormSubgroupFiniteIndex _root_.GlobalClassFieldTheory.Reciprocity.rationalIdeleClassDirectLimitMonoid _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.KummerTheory.primeCyclotomicBaseFiniteDimensional _root_.KummerTheory.primeCyclotomicBaseIsGalois _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.residueFieldZModAlgebra _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedIntegralAlgebraContextValuationSubringAlgebra _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedIntegralLatticeContextModuleFinite _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.LubinTate.padicCompletedLevelField_algebra _root_.LubinTate.padicCompletedLevelField_finiteDimensional _root_.LubinTate.padicCompletedLevelField_isGalois _root_.LubinTate.padicCompletedUnramifiedFieldAlgebra _root_.LubinTate.standardLubinTateLevelField_isMulCommutative _root_.LubinTate.standardLubinTateLevelValuationSubring_moduleFinite _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.CyclicCohomology.binaryCoefficientFamilyCommGroup _root_.GlobalClassFieldTheory.Reciprocity.instMonoidClassGroupRatSubtypeSeparableClosureMemIntermediateField _root_.GlobalClassFieldTheory.Reciprocity.rationalAbstractRelativeClassGroupCommGroup _root_.GlobalClassFieldTheory.Reciprocity.rationalAbstractRelativeClassGroupMulOneClass _root_.LocalClassFieldTheory.normalizationIntegerRingIsIntegralClosure _root_.relativeUnrestrictedSPlaceFactorCommGroup
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI
attribute [local instance] OAI.starSubalgebraCommCStarAlgebra

set_option autoImplicit false

/-!
# The finite-place product of local Artin homomorphisms

For a finite abelian extension of number fields `L / K`, the local
Artin factors of an idele are trivial at all but finitely many finite
places.  This file forms their `finprod` directly in the actual global
Galois group.
-/

open scoped Classical IsMulCommutative NumberField NNReal ValuativeRel
open NumberField IsDedekindDomain
open IdeleGroup RelativeIdeleGroup

noncomputable section

namespace GlobalClassFieldTheory
namespace Reciprocity

open AlgebraicNumberTheory.Valuations
open Function

variable {K L : Type}
    [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    [IsAbelianGalois K L]

/-- The local Artin factors obtained after an idele norm have finite
multiplicative support. -/
theorem finitePlaceNormArtinFactors_hasFiniteMulSupport
    {M : Type}
    [Field M] [NumberField M] [Algebra K M]
    (a : IdeleGroup M) :
    HasFiniteMulSupport
      (fun W : HeightOneSpectrum (𝓞 M) =>
        let v :=
          finitePlaceBelow (K := K) W
        letI : Algebra (v.adicCompletion K)
            (W.adicCompletion M) :=
          (finitePlaceAdicCompletionMap
            K M v ⟨W, rfl⟩).toAlgebra
        chosenFinitePlaceArtinMonoidHom
          (K := K) (L := L) v
          (LocalFieldTheory.normUnits
            (v.adicCompletion K)
            (W.adicCompletion M)
            (IdeleGroup.finiteComponent W a))) := by
  let S : Set (HeightOneSpectrum (𝓞 M)) :=
    {W | a.2 W ∉ (W.adicCompletionIntegers M).units}
  let T : Set (HeightOneSpectrum (𝓞 K)) :=
    {v | ∃ V : HeightOneSpectrum (𝓞 L),
      V.asIdeal.LiesOver v.asIdeal ∧
        ¬ Algebra.IsUnramifiedAt (𝓞 K) V.asIdeal}
  let U : Set (HeightOneSpectrum (𝓞 M)) :=
    {W | finitePlaceBelow (K := K) W ∈ T}
  have hS : S.Finite :=
    Filter.eventually_cofinite.mp
      (FiniteIdeleGroup.eventually_mem_localUnits a.2)
  have hT : T.Finite :=
    AlgebraicNumberTheory.Ramification.finite_ramified_base_heightOne_primes
      (𝓞 K) (𝓞 L)
  have hU : U.Finite := by
    exact
      Set.Finite.preimage_finitePlaceBelow
        (K := K) (L := M) hT
  rw [HasFiniteMulSupport]
  apply (hS.union hU).subset
  rw [mulSupport_subset_iff']
  intro W hW
  have hWS : W ∉ S := by
    intro hWS
    exact hW (Set.mem_union_left U hWS)
  have hWU : W ∉ U := by
    intro hWU
    exact hW (Set.mem_union_right S hWU)
  let v :=
    finitePlaceBelow (K := K) W
  have hComponentUnit :
      IdeleGroup.finiteComponent W a ∈
        (W.adicCompletionIntegers M).units := by
    simpa only [S, Set.mem_ofPred_eq, not_not,
      IdeleGroup.finiteComponent_apply] using hWS
  have hvT : v ∉ T := by
    intro hvT
    apply hWU
    exact hvT
  apply
    finitePlaceNormArtinFactor_eq_one_of_component_unit_of_unramified
      (K := K) (L := L) a W hComponentUnit
  apply chosenFinitePlaceIsUnramified_of_isUnramifiedAt
    (K := K) (L := L) v
  by_contra hram
  apply hvT
  exact
    ⟨finitePlaceExtensionCentre
        (K := K) (L := L) v
        (chosenFinitePlaceExtension (L := L) v),
      finitePlaceExtensionCentre_liesOver
        (K := K) (L := L) v
        (chosenFinitePlaceExtension (L := L) v),
      hram⟩

end Reciprocity
end GlobalClassFieldTheory
end
end

section
-- module Solutions.OAIQ244_DUKE.LubinTate_Padic_ChangedUniformizerIntertwiner_IntertwinerConstruction
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 400000
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalIdeleClassDirectLimitMonoid _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalClassFieldTheory.finiteGaloisLocalField_integerRing_moduleFinite _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitInverseLimitCarrierPadicModule _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitInverseLimitCarrierPadicSMul _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitQuotientCarrierPadicModule _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitQuotientCarrier_finite _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.adicPrincipalUnitsContinuousAdd _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.adicPrincipalUnitsContinuousSMul _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.adicPrincipalUnitsPadicModule _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.discretePrincipalUnitQuotientFinite _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.discretePrincipalUnitQuotientPadicModule _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitPadicModule _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitPadicSMul _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitProdiscreteLimitContinuousAdd _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitProdiscreteLimitContinuousSMul _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitProdiscreteLimitPadicModule _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.residueFieldZModAlgebra _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedIntegralAlgebraContextFieldAlgebra _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedIntegralAlgebraContextQPadic _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedIntegralAlgebraContextQPadicTower _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedIntegralAlgebraContextValuationSubringAlgebra _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedIntegralAlgebraContextValuationSubringTower _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedIntegralLatticeContextAlgebra _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedIntegralLatticeContextModuleFinite _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedIntegralLatticeContextModuleFree _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedMaximalIdealPowContextModuleFinite _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedMaximalIdealPowContextModuleFree _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedQPadicContextAlgebra _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedQPadicContextFact _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedQPadicContextFiniteDimensional _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedQPadicContextValuationExtension _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedQPadicContextValuationSubringTower _root_.LocalFieldTheory.DiscreteValuationField.finite_principalUnits_nthPowerKernel _root_.LocalFieldTheory.DiscreteValuationField.finite_residueRootsOfUnityGroup _root_.LocalFieldTheory.DiscreteValuationField.finite_valuationSubringUnits_nthPowerKernel _root_.LocalFieldTheory.DiscreteValuationField.finite_valuationSubringUnits_nthPowerQuotient _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.LubinTate.padicCompletedLevelCompleteDVF_hasExtensionInstance _root_.LubinTate.padicCompletedLevelField_algebra _root_.LubinTate.padicCompletedLevelField_finiteDimensional _root_.LubinTate.padicCompletedLevelField_isGalois _root_.LubinTate.padicCompletedLevelField_padicScalarTower _root_.LubinTate.standardLubinTateLevelField_galFinite _root_.LubinTate.standardLubinTateLevelField_isAbelianGalois _root_.LubinTate.standardLubinTateLevelField_isMulCommutative _root_.LubinTate.standardLubinTateUnitParameter_commGroup _root_.LubinTate.standardLubinTateUnitParameter_finite _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RamificationTheory.HilbertRamification.Higher.lowerRamificationGroup.instNormal _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionResidueField.instField _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.GlobalClassFieldTheory.Reciprocity.instMonoidClassGroupRatSubtypeSeparableClosureMemIntermediateField _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.LocalClassFieldTheory.comparisonIntegerRingIsIntegralClosure _root_.LocalClassFieldTheory.normalizationIntegerRingIsIntegralClosure _root_.RamificationTheory.HilbertRamification.CompleteDVF.decompositionGroupMulSemiringAction _root_.RamificationTheory.HilbertRamification.CompleteDVF.decompositionGroupResidueFieldMulSemiringAction _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen _root_.infiniteAdeleRingT2Space
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

/-!
# Changed-uniformizer intertwiner construction

This module builds compatible finite-degree approximations, assembles the changed-uniformizer intertwiner, proves its functional equation, and establishes uniqueness.
-/

noncomputable section

namespace LubinTate

open LocalFieldTheory.DiscreteValuationField
open LocalFieldTheory.DiscreteValuationField.Examples.Qp
open SameUniformizer

theorem padicChangedUniformizerDefect_coeff_succ_succ
    (p : ℕ) [Fact p.Prime]
    (u : (padicLocalField p).valuationSubringˣ)
    (n : ℕ) :
    PowerSeries.coeff (n + 2)
        (padicChangedUniformizerDefect p u
          (padicChangedUniformizerIntertwiner p u)) = 0 := by
  let H := padicChangedUniformizerIntertwiner p u
  let A := padicChangedUniformizerApproximation p u (n + 1)
  calc
    PowerSeries.coeff (n + 2)
        (padicChangedUniformizerDefect p u H) =
        PowerSeries.coeff (n + 2)
          (padicChangedUniformizerDefect p u A.series) := by
      apply padicChangedUniformizerDefect_coeff_eq_of_coeff_eq_le
        p u
        (padicChangedUniformizerIntertwiner_constantCoeff p u)
        A.constantCoeff_eq_zero
      intro q hq
      exact
        padicChangedUniformizerIntertwiner_coeff_eq_approximation
          p u q (n + 1) (by omega)
    _ = 0 :=
      padicChangedUniformizerApproximation_succ_defect_coeff p u n

end LubinTate

end
end


