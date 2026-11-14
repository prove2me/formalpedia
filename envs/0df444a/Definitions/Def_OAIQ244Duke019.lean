-- Prove2me | Definitions.Def_OAIQ244Duke019
-- name    : OAIQ244Duke019
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-13T06:18:16.158076+00:00
-- url     : https://prove2.me/theorems/0b46d501-c7d0-4d3d-bd65-5dad3cbf25c7
-- title:
--   Definitions bundle OAIQ244Duke019 of the split of OpenAI, Equidistribution of Prime-Degree Torus Packets with Arbitrary Local Type
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.DukePrimeDegree.prime_degree_packet_measure_equidistribution_unconditional` and `OAI.DukePrimeDegree.prime_degree_packet_measures_tendsto_haar_unconditional`, carved from OpenAI's openai/math development (OpenAI, *Equidistribution of Prime-Degree Torus Packets with Arbitrary Local Type*, OpenAI Math Release, September 24, 2026, result family 15, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 199 declarations of OpenAI's Lean: 57 definitions, 7 instances and 135 theorems. The definitions and types are `GlobalClassFieldTheory.ClassFieldAxiom.sUnitNthPowersInField`, `KummerTheory.chosenFiniteKummerRadicalRepresentative`, `KummerTheory.chosenSimpleKummerRootCharacter`, `KummerTheory.chosenSimpleKummerRootUnit`, `KummerTheory.finiteKummerCharacterEquiv`, `KummerTheory.finsuppNsmulQuotientEquivPiZMod`, `KummerTheory.fullSUnitKummerExtension`, `KummerTheory.fullSUnitKummerSubgroup`, `KummerTheory.infiniteKummerRootCharacter`, `KummerTheory.kummerRadicalExtension`, `KummerTheory.nthRootsSubgroupEquivRootsOfUnity`, `KummerTheory.sUnitKummerSubgroup`, `LocalClassFieldTheory.A`, `LocalClassFieldTheory.AG`, `LocalClassFieldTheory.B`, `LocalClassFieldTheory.B`, `LocalClassFieldTheory.G`, `LocalClassFieldTheory.G`, `LocalClassFieldTheory.abstractExtensionQuotientEquivAmbient`, `LocalClassFieldTheory.abstractRelativeToAmbientQuotient`, `LocalClassFieldTheory.baseFixingExtensionQuotientEquivAmbient`, `LocalClassFieldTheory.baseFixingExtensionQuotientEquivGaloisGroup`, `LocalClassFieldTheory.baseFixingToAmbientQuotient`, `LocalClassFieldTheory.baseUnitsEquivGaloisAmbientFixed`, `LocalClassFieldTheory.chosenNormalBasisIntegerUnitsQuotMulDistribMulAction`, `LocalClassFieldTheory.embeddedFieldUnitsEquivGaloisFixed`, `LocalClassFieldTheory.finiteGaloisAbstractQuotientEquivGaloisGroupOfEmbedding`, `LocalClassFieldTheory.finiteGaloisClosedFixingSubgroup`, `LocalClassFieldTheory.finiteGaloisClosedFixingSubgroupOfEmbedding`, `LocalClassFieldTheory.finiteGaloisConjugateBaseElement`, `LocalClassFieldTheory.finiteGaloisEmbeddingConjugator`, `LocalClassFieldTheory.finiteGaloisUnitsEquivAbstractFixed`, `LocalClassFieldTheory.finiteGaloisUnitsEquivAbstractFixedOfEmbedding`, `LocalClassFieldTheory.finiteResidueFrobeniusFromZHat`, `LocalClassFieldTheory.finiteResidueFrobeniusIntermediate`, `LocalClassFieldTheory.galoisGroupValueGroupFixedToZModHom`, `LocalClassFieldTheory.galoisGroupValueGroupHerbrandH0MulEquivZMod`, `LocalClassFieldTheory.intermediateFieldUnitsEquivGaloisFixed`, `LocalClassFieldTheory.intrinsicAbsoluteUnits`, `LocalClassFieldTheory.intrinsicAbstractBase` and 17 more.
--
--   **Sources.** They come from these modules of lean/OAI/NumberTheory, in whole or in part: `AlgebraicNumberTheory_SUnit_LogLattice`, `AlgebraicNumberTheory_SUnit_Rank`, `GlobalClassFieldTheory_ClassFieldAxiom_IdeleClassPowerLocalUnitQuotient_SupportedIdeleIndex`, `GlobalClassFieldTheory_ClassFieldAxiom_IdelePowerLocalUnitSubgroup`, `KummerTheory_Concrete_SUnitPreparation_FiniteRadicalSupport`, `KummerTheory_Concrete_SUnitPreparation_FullSUnitKummerExtension`, `KummerTheory_Concrete_SUnitPreparation_SUnitPowerQuotient`, `Kummer_Concrete_ExtensionRoundTrip`, `Kummer_Concrete_FiniteCharacterEquiv`, `Kummer_Concrete_FiniteDualSeparation`, `Kummer_Concrete_FiniteGeneration`, `Kummer_Concrete_FiniteSupport`, `Kummer_Concrete_InfiniteContinuity`, `Kummer_Concrete_InfiniteGeneration`, `Kummer_Concrete_InfiniteInverse`, `Kummer_Concrete_RadicalExtension`, `Kummer_Concrete_RadicalQuotient`, `Kummer_Concrete_RootCharacters`, `Kummer_Concrete_SimpleExtension`, `LocalClassFieldTheory_ClassFormation_CohomologyBridge`, `LocalClassFieldTheory_ClassFormation_IntegerUnitsHerbrand`, `LocalClassFieldTheory_ClassFormation_NormalBasisGaloisAction`, `LocalClassFieldTheory_ClassFormation_NormalBasisInfiniteProduct`, `LocalClassFieldTheory_ClassFormation_Valuation`, `LocalClassFieldTheory_ClassFormation_ValueGroupCohomology`, `LocalClassFieldTheory_Finite_LocalReciprocity_AbsoluteUnitsFixedField`, `LocalClassFieldTheory_Finite_LocalReciprocity_ConcreteReciprocityCanonical`, `LocalClassFieldTheory_Finite_LocalReciprocity_ConcreteReciprocityTransport`, `LocalClassFieldTheory_Finite_LocalReciprocity_FiniteAbstractFixedField`, `LocalClassFieldTheory_Finite_LocalReciprocity_FiniteGaloisRealization`, `LocalClassFieldTheory_Finite_LocalReciprocity_FiniteResidueFrobenius`, `LocalClassFieldTheory_Finite_LocalReciprocity_GaloisExtensionQuotient`, `LocalClassFieldTheory_Finite_LocalReciprocity_IntrinsicAbsoluteData`, `LocalClassFieldTheory_Finite_LocalReciprocity_ResidueAbsoluteFrobenius`, `LocalClassFieldTheory_Finite_LocalReciprocity_ResidueActionIndex`, `LocalClassFieldTheory_Finite_LocalReciprocity_ResidueAlgebraicClosureDegree`, `LocalClassFieldTheory_Finite_LocalReciprocity_ResidueDatum`, `LocalClassFieldTheory_Finite_LocalReciprocity_SeparableUnitsNorm`, `LocalField_NonarchimedeanLocalField_Basic`, `LocalField_NonarchimedeanLocalField_PrincipalUnitQuotients`, `Valuation_DiscreteValuationField_Basic`, `Valuation_DiscreteValuationField_ChevalleyExtension`, `Valuation_DiscreteValuationField_Extensions`, `Valuation_DiscreteValuationField_FiniteIntegralClosure`.
--
--   **Imports.** It imports the bundles `OAIQ244Duke001`, `OAIQ244Duke002`, `OAIQ244Duke003`, `OAIQ244Duke004`, `OAIQ244Duke005`, `OAIQ244Duke006`, `OAIQ244Duke007` and `OAIQ244Duke008` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ244Duke030`, `OAIQ244Duke031`, `OAIQ244Duke033` and `OAIQ244Duke034`.
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
import Mathlib.Algebra.Group.Equiv.Basic
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
import Mathlib.Algebra.Module.MinimalAxioms
import Mathlib.Algebra.Module.PID
import Mathlib.Algebra.Module.Shrink
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
import Mathlib.LinearAlgebra.FreeModule.IdealQuotient
import Mathlib.LinearAlgebra.Isomorphisms
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
import Mathlib.NumberTheory.NumberField.Cyclotomic.Basic
import Mathlib.NumberTheory.NumberField.ProductFormula
import Mathlib.NumberTheory.NumberField.Units.DirichletTheorem
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
import Definitions.Def_OAIQ244Duke001
import Definitions.Def_OAIQ244Duke002
import Definitions.Def_OAIQ244Duke003
import Definitions.Def_OAIQ244Duke004
import Definitions.Def_OAIQ244Duke005
import Definitions.Def_OAIQ244Duke006
import Definitions.Def_OAIQ244Duke007
import Definitions.Def_OAIQ244Duke008

section
-- module Solutions.OAIQ244_DUKE.AlgebraicNumberTheory_SUnit_Rank
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.LocalFieldTheory.DiscreteValuationField.finite_nsmulAddKernel_padicInt_pi _root_.LocalFieldTheory.finite_multiplicative_nthPowerKernel _root_.LocalFieldTheory.finite_nsmulAddKernel_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.LubinTate.compatibleGroupFamiliesCommGroup _root_.LubinTate.compatibleGroupFamiliesGroup _root_.RamificationTheory.HilbertRamification.ValuationSubring.selectedResidueField.instAlgebra _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.maximalIdealPowSuccQuotModule _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.CyclicCohomology.binaryCoefficientFamilyCommGroup _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.adicCompletionProperSpace _root_.relativeAdeleRingIntermediateAlgebra _root_.relativeAdeleRingTopIntermediateAlgebra
attribute [-simp] _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.KummerTheory.mem_sUnitFiniteKummerRadical_iff _root_.LocalFieldTheory.residueField_algebraMap_residue _root_.SUnitGroup.fullLogAmbient_finite _root_.SUnitGroup.fullLogAmbient_infinite _root_.SUnitGroup.reducedLog_fst_fromNumberFieldUnits _root_.SUnitGroup.reducedLog_snd_fromNumberFieldUnits
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

theorem fromNumberFieldUnits_injective
    (S : Finset (HeightOneSpectrum (𝓞 K))) :
    Function.Injective (fromNumberFieldUnits (K := K) S) := by
  intro u v huv
  apply (emptyEquivNumberFieldUnits (K := K)).symm.injective
  ext
  exact congrArg (fun x : SUnitGroup (K := K) S => ((x : Kˣ) : K)) huv

section DivisorMap

variable (S : Finset (HeightOneSpectrum (𝓞 K)))

theorem fromNumberFieldUnitsLinearMap_injective :
    Function.Injective (fromNumberFieldUnitsLinearMap (K := K) S) := by
  intro x y hxy
  apply Additive.toMul.injective
  exact fromNumberFieldUnits_injective (K := K) S
    (congrArg Additive.toMul hxy)

end DivisorMap

section PrimePowerSources

variable (S : Finset (HeightOneSpectrum (𝓞 K)))

/-- An `S`-unit whose divisor is `classNumber K` times the basis divisor at
`v`. -/
noncomputable def primePowerSUnit (v : S) :
    SUnitGroup (K := K) S :=
  ⟨Units.mk0
      (algebraMap (𝓞 K) K (primePowerGenerator (K := K) S v))
      ((map_ne_zero_iff (algebraMap (𝓞 K) K)
        (IsFractionRing.injective (𝓞 K) K)).mpr
          (primePowerGenerator_ne_zero (K := K) S v)),
    fun w hw => by
      apply (valuation_eq_one_iff_count_eq_zero (K := K)
        (Units.mk0
          (algebraMap (𝓞 K) K (primePowerGenerator (K := K) S v))
          ((map_ne_zero_iff (algebraMap (𝓞 K) K)
            (IsFractionRing.injective (𝓞 K) K)).mpr
              (primePowerGenerator_ne_zero (K := K) S v))) w).2
      change
        FractionalIdeal.count K w
          (FractionalIdeal.spanSingleton (𝓞 K)⁰
            (algebraMap (𝓞 K) K
              (primePowerGenerator (K := K) S v))) = 0
      rw [spanSingleton_primePowerGenerator (K := K) S v,
        FractionalIdeal.count_pow]
      have hwv :
          (v : HeightOneSpectrum (𝓞 K)) ≠ w := by
        intro hvw
        exact hw (hvw ▸ v.property)
      rw [FractionalIdeal.count_maximal_coprime K w hwv]
      simp⟩

theorem divisorCoordinate_primePowerSUnit
    (v w : S) :
    divisorCoordinate (K := K) S (primePowerSUnit (K := K) S v) w =
      classNumberBasisVector (K := K) S v w := by
  classical
  change
    FractionalIdeal.count K (w : HeightOneSpectrum (𝓞 K))
        (FractionalIdeal.spanSingleton (𝓞 K)⁰
          (algebraMap (𝓞 K) K
            (primePowerGenerator (K := K) S v))) =
      classNumberBasisVector (K := K) S v w
  simp only [classNumberBasisVector]
  rw [spanSingleton_primePowerGenerator (K := K) S v]
  split_ifs with hwv
  · subst w
    simpa using
      FractionalIdeal.count_pow_self K
        (v : HeightOneSpectrum (𝓞 K))
        (NumberField.classNumber K)
  · rw [FractionalIdeal.count_pow]
    have hvw :
        (v : HeightOneSpectrum (𝓞 K)) ≠
          (w : HeightOneSpectrum (𝓞 K)) := by
      intro h
      exact hwv (Subtype.ext h.symm)
    rw [FractionalIdeal.count_maximal_coprime K
      (w : HeightOneSpectrum (𝓞 K)) hvw]
    simp

end PrimePowerSources

section Rank

variable (S : Finset (HeightOneSpectrum (𝓞 K)))

noncomputable def divisorRangeVector (v : S) :
    LinearMap.range (divisorLinearMap (K := K) S) :=
  ⟨classNumberBasisVector (K := K) S v,
    ⟨Additive.ofMul (primePowerSUnit (K := K) S v), by
      ext w
      exact divisorCoordinate_primePowerSUnit (K := K) S v w⟩⟩

theorem divisorRangeVector_linearIndependent :
    LinearIndependent ℤ (divisorRangeVector (K := K) S) := by
  classical
  rw [Fintype.linearIndependent_iff]
  intro g hg v
  have hv := congrArg
    (fun z : LinearMap.range (divisorLinearMap (K := K) S) =>
      ((z : S → ℤ) v)) hg
  simp [divisorRangeVector, classNumberBasisVector] at hv
  exact hv.resolve_right (NumberField.classNumber_ne_zero K)

/-- The divisor-map range on `S`-units has rank equal to the number of
places in `S`. -/
theorem finrank_divisor_range :
    Module.finrank ℤ
        (LinearMap.range (divisorLinearMap (K := K) S)) =
      S.card := by
  let : Module.Finite ℤ (S → ℤ) := inferInstance
  let : Module.Finite ℤ
      (LinearMap.range (divisorLinearMap (K := K) S)) :=
    Module.Finite.of_fg
      (IsNoetherian.noetherian
        (LinearMap.range (divisorLinearMap (K := K) S)))
  apply le_antisymm
  · calc
      Module.finrank ℤ
          (LinearMap.range (divisorLinearMap (K := K) S)) ≤
          Module.finrank ℤ (S → ℤ) :=
        Submodule.finrank_le
          (LinearMap.range (divisorLinearMap (K := K) S))
      _ = S.card := by simp
  · simpa using
      (divisorRangeVector_linearIndependent (K := K) S).fintype_card_le_finrank

/-- The kernel of the `S`-unit divisor map has the ordinary unit rank. -/
theorem finrank_divisor_ker :
    Module.finrank ℤ
        (LinearMap.ker (divisorLinearMap (K := K) S)) =
      NumberField.Units.rank K := by
  calc
    Module.finrank ℤ
        (LinearMap.ker (divisorLinearMap (K := K) S)) =
        Module.finrank ℤ
          (LinearMap.range
            (fromNumberFieldUnitsLinearMap (K := K) S)) :=
      (LinearEquiv.ofEq _ _
        (range_fromNumberFieldUnitsLinearMap_eq_ker_divisorLinearMap
          (K := K) S).symm).finrank_eq
    _ = Module.finrank ℤ (Additive (𝓞 K)ˣ) :=
      (LinearEquiv.ofInjective
        (fromNumberFieldUnitsLinearMap (K := K) S)
        (fromNumberFieldUnitsLinearMap_injective (K := K) S)).symm.finrank_eq
    _ = NumberField.Units.rank K :=
      NumberField.Units.finrank_eq K

end Rank

end SUnitGroup
end
end

section
-- module Solutions.OAIQ244_DUKE.AlgebraicNumberTheory_SUnit_LogLattice
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.LubinTate.compatibleGroupFamiliesCommGroup _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.maximalIdealPowSuccQuotModule _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.CyclicCohomology.binaryCoefficientFamilyCommGroup _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.adicCompletionProperSpace
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

section Decomposition

/-- The additive torsion submodule of the `S`-unit group. -/
abbrev TorsionAdditive :=
  Submodule.torsion ℤ
    (Additive (SUnitGroup (K := K) S))

/-- The torsion-free quotient of the additive `S`-unit group. -/
abbrev FreeQuotient :=
  Additive (SUnitGroup (K := K) S) ⧸
    TorsionAdditive (K := K) S

local instance instModule_freeQuotient :
    Module ℤ (FreeQuotient (K := K) S) :=
  Submodule.Quotient.module
    (TorsionAdditive (K := K) S)

end Decomposition

end SUnitGroup
end
end

section
-- module Solutions.OAIQ244_DUKE.LocalField_NonarchimedeanLocalField_Basic
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.adicCompletionProperSpace
attribute [-simp] _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.LocalFieldTheory.residueField_algebraMap_residue
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI
/-!
# Basic structure of nonarchimedean local fields

Compactness facts and the normalized integer-valued valuation attached to a
nonarchimedean local field.
-/

set_option autoImplicit false

namespace LocalFieldTheory

noncomputable section

universe u

namespace IsNonarchimedeanLocalField

open scoped ValuativeRel WithZero

/-- Every integer occurs as the normalized valuation of a nonzero field element. -/
theorem v_surjective (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] :
    Function.Surjective (v K) := by
  intro n
  let γ : ValuativeRel.ValueGroupWithZero K :=
    (_root_.IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt K).symm
      ((Multiplicative.ofAdd n : Multiplicative Int) : WithZero (Multiplicative Int))
  obtain ⟨a, ha⟩ := ValuativeRel.valuation_surjective γ
  have hγ_ne : γ ≠ 0 := by
    dsimp [γ]
    simp
  have ha0 : a ≠ 0 := by
    intro h
    apply hγ_ne
    simpa [h] using ha.symm
  refine ⟨Additive.ofMul (Units.mk0 a ha0), ?_⟩
  simp [v, γ, ha]

/-- The canonical inclusion of valuation-integer units into field units is
injective. -/
theorem integerUnitsToFieldUnits_injective
    (K : Type u) [Field K] [ValuativeRel K] :
    Function.Injective (integerUnitsToFieldUnits K) := by
  intro x y hxy
  apply Units.ext
  apply Subtype.ext
  simpa [integerUnitsToFieldUnits] using congrArg Units.val hxy

end IsNonarchimedeanLocalField

end
end LocalFieldTheory
end

section
-- module Solutions.OAIQ244_DUKE.LocalField_NonarchimedeanLocalField_PrincipalUnitQuotients
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.adicCompletionProperSpace
attribute [-simp] _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.LocalFieldTheory.residueField_algebraMap_residue
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

/-- Rewrites a difference of units as the earlier unit times a quotient error.
This is the algebraic bridge from multiplicative tail control to additive
uniformity control. -/
lemma unit_sub_eq_mul_div_sub_one
    (K : Type u) [Field K] [ValuativeRel K] (a b : 𝒪[K]ˣ) :
    (a : 𝒪[K]) - (b : 𝒪[K]) =
      (b : 𝒪[K]) * (((a / b : 𝒪[K]ˣ) : 𝒪[K]) - 1) := by
  have hmul : (b : 𝒪[K]) * ((a / b : 𝒪[K]ˣ) : 𝒪[K]) = (a : 𝒪[K]) := by
    simp [div_eq_mul_inv, mul_left_comm]
  calc
    (a : 𝒪[K]) - (b : 𝒪[K]) =
        (b : 𝒪[K]) * ((a / b : 𝒪[K]ˣ) : 𝒪[K]) - (b : 𝒪[K]) := by
      rw [hmul]
    _ = (b : 𝒪[K]) * (((a / b : 𝒪[K]ˣ) : 𝒪[K]) - 1) := by
      ring

end
end LocalFieldTheory
end

section
-- module Solutions.OAIQ244_DUKE.LocalClassFieldTheory_ClassFormation_Valuation
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.RelativeIdeleGroup.relativeIdeleMulAction _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.adicCompletionProperSpace
attribute [-simp] _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false
/-! Provides the public declarations in the `LocalClassFieldTheory.ClassFormation.Valuation` Lean module. -/

namespace LocalClassFieldTheory

open LocalFieldTheory

noncomputable section

universe u

open scoped ValuativeRel
open IsNonarchimedeanLocalField

/-- States the theorem `galoisGroupValueGroupMulDistribMulAction_smul`. -/
@[simp]
theorem galoisGroupValueGroupMulDistribMulAction_smul
    (K L : Type u) [Field K] [Field L] [Algebra K L]
    (σ : Gal(L / K)) (n : Multiplicative Int) :
    letI := galoisGroupValueGroupMulDistribMulAction K L
    σ • n = n :=
  rfl

end
end LocalClassFieldTheory
end

section
-- module Solutions.OAIQ244_DUKE.Valuation_DiscreteValuationField_Basic
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.LocalFieldTheory.DiscreteValuationField.Examples.Qp.padicDVRValuation_isRankOneDiscrete _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.RamificationTheory.HilbertRamification.ValuationSubring.selectedResidueField.instAlgebra _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.adicCompletionProperSpace _root_.relativeAdeleRingIntermediateAlgebra _root_.relativeAdeleRingTopIntermediateAlgebra
attribute [-simp] _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.LocalFieldTheory.residueField_algebraMap_residue _root_.ValuationTheory.DiscreteValuationField.ValuedExtension.Henselian.integralClosureValuationSubringIntegerMapOfMemOrInv_apply _root_.ValuationTheory.DiscreteValuationField.ValuedExtension.degree_eq_finrank _root_.ValuationTheory.DiscreteValuationField.ValuedExtension.integerMap_apply _root_.ValuationTheory.DiscreteValuationField.ValuedExtension.integralClosureRingEquivTargetValuationSubringOfModuleFinite_apply _root_.ValuationTheory.DiscreteValuationField.ValuedExtension.integralClosureToTargetValuationSubringOfHasExtension_apply _root_.ValuationTheory.DiscreteValuationField.ValuedExtension.integralClosureValuationSubringIntegerMapOfMemOrInv_apply _root_.ValuationTheory.DiscreteValuationField.ValuedExtension.residueFieldEquivOfSurjective_apply _root_.ValuationTheory.DiscreteValuationField.ValuedExtension.residueFieldEquivOfSurjective_apply_residue _root_.ValuationTheory.DiscreteValuationField.ValuedExtension.residueFieldEquivOfSurjective_symm_apply_residueMap _root_.ValuationTheory.DiscreteValuationField.ValuedExtension.residueFieldEquivOfSurjective_symm_apply_target_residue _root_.ValuationTheory.DiscreteValuationField.ValuedExtension.residueMap_residue _root_.ValuationTheory.DiscreteValuationField.ValuedExtension.residueMap_residueFieldEquivOfSurjective_symm_apply _root_.ValuationTheory.DiscreteValuationField.ValuedExtension.residueUnitsEquivOfResidueMapSurjective_apply _root_.ValuationTheory.DiscreteValuationField.ValuedExtension.targetValuationSubringToIntegralClosureOfModuleFinite_apply _root_.ValuationTheory.DiscreteValuationField.ValuedExtension.unitMap_apply
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

/-- Membership in a power of the maximal ideal is divisibility by the
corresponding power of a uniformizer. -/
theorem mem_maximalIdeal_pow_iff_uniformizer_pow_dvd (F : DVF.{u, v} K)
    {pi x : F.valuationSubring}
    (hpi : F.valuation.IsUniformizer (pi : K)) (n : ℕ) :
    x ∈ F.maximalIdeal ^ n ↔ pi ^ n ∣ x := by
  rw [F.maximalIdeal_pow_eq_span_uniformizer_pow hpi n,
    Ideal.mem_span_singleton]

/-- No power of a uniformizer lies one step deeper in the maximal-ideal
filtration. -/
theorem uniformizer_pow_not_mem_maximalIdeal_pow_succ
    (F : DVF.{u, v} K)
    {pi : F.valuationSubring} (hpi : F.valuation.IsUniformizer (pi : K))
    (n : ℕ) :
    pi ^ n ∉ F.maximalIdeal ^ (n + 1) := by
  rw [F.mem_maximalIdeal_pow_iff_uniformizer_pow_dvd hpi (n + 1)]
  rintro ⟨a, ha⟩
  have hpi_ne : pi ≠ 0 := by
    intro hzero
    exact hpi.ne_zero (by simpa using congrArg (fun x : F.valuationSubring => (x : K)) hzero)
  have hpow_ne : pi ^ n ≠ 0 := pow_ne_zero n hpi_ne
  have hcancel : (1 : F.valuationSubring) = pi * a := by
    apply mul_left_cancel₀ hpow_ne
    calc
      pi ^ n * (1 : F.valuationSubring) = pi ^ n := by rw [mul_one]
      _ = pi ^ (n + 1) * a := ha
      _ = (pi ^ n * pi) * a := by rw [pow_succ]
      _ = pi ^ n * (pi * a) := by rw [mul_assoc]
  have hunit : IsUnit pi :=
    isUnit_iff_dvd_one.2 ⟨a, hcancel⟩
  exact hpi.not_isUnit hunit

/-! ### Successive quotients of powers of the maximal ideal -/

end DVF
end DiscreteValuationField

end

end ValuationTheory
end

section
-- module Solutions.OAIQ244_DUKE.Valuation_DiscreteValuationField_Extensions
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.RamificationTheory.HilbertRamification.ValuationSubring.selectedResidueField.instAlgebra _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.adicCompletionProperSpace _root_.relativeAdeleRingIntermediateAlgebra _root_.relativeAdeleRingTopIntermediateAlgebra
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
/-- The induced map between valuation subrings is injective. -/
theorem integerMap_injective :
    Function.Injective (integerMap base target) := by
  change Function.Injective
    (algebraMap base.valuation.valuationSubring
      target.valuation.valuationSubring)
  exact _root_.Valuation.HasExtension.algebraMap_injective
    (vK := base.valuation) (vA := target.valuation)

end ValuedExtension
end DiscreteValuationField
end
end ValuationTheory
end

section
-- module Solutions.OAIQ244_DUKE.Valuation_DiscreteValuationField_ChevalleyExtension
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.RamificationTheory.HilbertRamification.ValuationSubring.selectedResidueField.instAlgebra _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.RelativeIdeleGroup.relativeIdeleMulAction _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.adicCompletionProperSpace _root_.relativeAdeleRingIntermediateAlgebra _root_.relativeAdeleRingTopIntermediateAlgebra
attribute [-simp] _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.LocalFieldTheory.residueField_algebraMap_residue
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

namespace ValuationTheory

/-!
# Chevalley's valuation extension theorem

Mathlib has the predicate `Valuation.HasExtension` and the induced valuation
subring/residue-field API.  This file proves the field-extension form of
Chevalley's valuation extension theorem from mathlib's maximal local subring
construction: a local subring of a field is dominated by a valuation subring.
-/

noncomputable section

universe u v w x y z

namespace DiscreteValuationField
namespace Valuation

open ValuationTheory.DiscreteValuationField.ResidueField

variable {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L]
variable {ΓK : Type w} [LinearOrderedCommGroupWithZero ΓK]

/-- The canonical map from the actual integral closure of the base valuation
ring to any valuation ring extending the base valuation. -/
def integralClosureToValuationSubringOfHasExtension
    {ΓL : Type x} [LinearOrderedCommGroupWithZero ΓL]
    (vK : _root_.Valuation K ΓK) (vL : _root_.Valuation L ΓL)
    [vK.HasExtension vL] :
    integralClosure vK.valuationSubring L →+* vL.valuationSubring where
  toFun z :=
    ⟨(z : L),
      integralClosure_mem_valuationSubring_of_hasExtension
        (L := L) vK vL z⟩
  map_zero' := by ext; simp
  map_one' := by ext; simp
  map_add' z₁ z₂ := by ext; simp
  map_mul' z₁ z₂ := by ext; simp

/-- The canonical map from the integral closure to an extending valuation ring is inclusion. -/
@[simp] theorem integralClosureToValuationSubringOfHasExtension_apply
    {ΓL : Type x} [LinearOrderedCommGroupWithZero ΓL]
    (vK : _root_.Valuation K ΓK) (vL : _root_.Valuation L ΓL)
    [vK.HasExtension vL]
    (z : integralClosure vK.valuationSubring L) :
    ((integralClosureToValuationSubringOfHasExtension
      (L := L) vK vL z : vL.valuationSubring) : L) = z :=
  rfl

/-- If an extension valuation ring is integral over the base valuation ring,
then every target valuation-ring element lies in the actual integral closure.
This is the construction-level condition needed in the Henselian
finite-extension frontier. -/
theorem valuationSubring_mem_integralClosure_of_isIntegral
    {ΓL : Type x} [LinearOrderedCommGroupWithZero ΓL]
    (vK : _root_.Valuation K ΓK) (vL : _root_.Valuation L ΓL)
    [vK.HasExtension vL]
    [Algebra.IsIntegral vK.valuationSubring vL.valuationSubring]
    (z : vL.valuationSubring) :
    (z : L) ∈ integralClosure vK.valuationSubring L := by
  have hz_ring : IsIntegral vK.valuationSubring z :=
    Algebra.IsIntegral.isIntegral (R := vK.valuationSubring) z
  have hz_field : IsIntegral vK.valuationSubring
      (algebraMap vL.valuationSubring L z) :=
    hz_ring.map
      (IsScalarTower.toAlgHom vK.valuationSubring vL.valuationSubring L)
  rw [mem_integralClosure_iff]
  simpa using hz_field

/-- An extension valuation ring that is integral over the base valuation ring is
the actual integral closure of the base valuation ring in the field extension.
No finite-module certificate is introduced here; the proof is the defining
integral-closure equivalence. -/
theorem valuationSubring_isIntegralClosure_of_isIntegral
    {ΓL : Type x} [LinearOrderedCommGroupWithZero ΓL]
    (vK : _root_.Valuation K ΓK) (vL : _root_.Valuation L ΓL)
    [vK.HasExtension vL]
    [Algebra.IsIntegral vK.valuationSubring vL.valuationSubring] :
    IsIntegralClosure vL.valuationSubring vK.valuationSubring L := by
  refine
    { algebraMap_injective := Subtype.coe_injective
      isIntegral_iff := ?_ }
  intro z
  constructor
  · intro hz
    refine ⟨integralClosureToValuationSubringOfHasExtension
      (L := L) vK vL ⟨z, hz⟩, ?_⟩
    rfl
  · rintro ⟨y, rfl⟩
    exact valuationSubring_mem_integralClosure_of_isIntegral
      (L := L) vK vL y

end Valuation
end DiscreteValuationField

end

end ValuationTheory
end

section
-- module Solutions.OAIQ244_DUKE.LocalClassFieldTheory_ClassFormation_CohomologyBridge
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.maximalIdealPowSuccQuotModule _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.CyclicCohomology.binaryCoefficientFamilyCommGroup _root_.CyclicCohomology.instMulDistribMulActionBinaryCoefficientFamily _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.adicCompletionProperSpace
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

/-- The norm in the actual unit representation is the multiplicative Herbrand
norm after passing from `Additive Lˣ` back to `Lˣ`. -/
theorem unitsNormLinearMap_toMul_eq_tateNorm
    [Fintype (Gal(L / K))] (x : Lˣ) :
    Additive.toMul (unitsNormLinearMap K L (Additive.ofMul x)) =
      tateNorm (Gal(L / K)) Lˣ x := by
  have hnorm :
      unitsNormLinearMap K L (Additive.ofMul x) =
        ∑ σ : Gal(L / K), (Rep.ofAlgebraAutOnUnits K L).ρ σ (Additive.ofMul x) := by
    exact LinearMap.sum_apply Finset.univ
      (fun σ : Gal(L / K) => (Rep.ofAlgebraAutOnUnits K L).ρ σ)
      (Additive.ofMul x : Additive Lˣ)
  rw [hnorm]
  calc
    (Additive.toMul
        ((∑ σ : Gal(L / K), (Rep.ofAlgebraAutOnUnits K L).ρ σ (Additive.ofMul x)) :
          Additive Lˣ) : Lˣ) =
        ∏ σ : Gal(L / K),
          (Additive.toMul
            ((Rep.ofAlgebraAutOnUnits K L).ρ σ (Additive.ofMul x) : Additive Lˣ) : Lˣ) := by
      simpa only using additive_toMul_finset_sum_units L Finset.univ
        (fun σ : Gal(L / K) => (Rep.ofAlgebraAutOnUnits K L).ρ σ (Additive.ofMul x))
    _ = tateNorm (Gal(L / K)) Lˣ x := by
      rfl

/-- Subtraction by the identity in the actual unit representation is the
multiplicative coboundary `x ↦ g•x/x`. -/
theorem unitsRhoSub_toMul_eq_sigmaMinusOne
    (g : Gal(L / K)) (x : Lˣ) :
    (Additive.toMul ((Rep.ofAlgebraAutOnUnits K L).ρ g (Additive.ofMul x)) : Lˣ) * x⁻¹ =
      sigmaMinusOne (Gal(L / K)) Lˣ g x := by
  rfl

/-- The actual additive differential `ρ(g)-1`, with codomain restricted to
the kernel of the norm. -/
def unitsRhoSubToNormKerLinearMap [Fintype (Gal(L / K))]
    (g : Gal(L / K)) :
    Additive Lˣ →ₗ[ℤ] LinearMap.ker (unitsNormLinearMap K L) :=
  ((Rep.ofAlgebraAutOnUnits K L).ρ g - LinearMap.id).codRestrict
    (LinearMap.ker (unitsNormLinearMap K L)) (by
      intro x
      change unitsNormLinearMap K L
        ((Rep.ofAlgebraAutOnUnits K L).ρ g x - x) = 0
      change (Rep.ofAlgebraAutOnUnits K L).norm.hom
        ((Rep.ofAlgebraAutOnUnits K L).ρ g x - x) = 0
      rw [map_sub]
      apply sub_eq_zero.mpr
      change Representation.norm (Rep.ofAlgebraAutOnUnits K L).ρ
        ((Rep.ofAlgebraAutOnUnits K L).ρ g x) =
          Representation.norm (Rep.ofAlgebraAutOnUnits K L).ρ x
      exact Representation.norm_self_apply (Rep.ofAlgebraAutOnUnits K L).ρ g x)

/-- Mathlib's degree-minus-one Tate object is its standard finite-cyclic
boundary quotient `ker N / im(ρ(g)-1)`. -/
noncomputable def unitsTateHminusOneIsoBoundaryQuotient
    [FiniteDimensional K L] (g : Gal(L / K))
    (hg : ∀ x : Gal(L / K), x ∈ Subgroup.zpowers g) :
    tateCohomology (Rep.ofAlgebraAutOnUnits K L) (-1) ≅
      ModuleCat.of ℤ
        (LinearMap.ker (unitsNormLinearMap K L) ⧸
          LinearMap.range (unitsRhoSubToNormKerLinearMap K L g)) := by
  letI : IsCyclic (Gal(L / K)) :=
    CyclicCohomology.isCyclic_of_generator g hg
  letI : CommGroup (Gal(L / K)) := IsCyclic.commGroup
  let T :=
    Rep.FiniteCyclicGroup.subCompNormHom (Rep.ofAlgebraAutOnUnits K L) g
  have hmap :
      T.moduleCatToCycles =
          unitsRhoSubToNormKerLinearMap K L g := by
    ext x
    rfl
  have e := T.moduleCatHomologyIso
  change
    T.homology ≅
      ModuleCat.of ℤ
        (LinearMap.ker (unitsNormLinearMap K L) ⧸
          LinearMap.range
            T.moduleCatToCycles) at e
  rw [hmap] at e
  exact TateCohomology.isoFiniteCyclicNegOne (Rep.ofAlgebraAutOnUnits K L) g hg ≪≫
    e

end
end LocalClassFieldTheory
end

section
-- module Solutions.OAIQ244_DUKE.LocalClassFieldTheory_ClassFormation_ValueGroupCohomology
attribute [-instance] _root_.ClassFormation.DegreeData.GaloisSubextension.extensionSubgroup_normalInstance _root_.ClassFormation.FiniteCyclicSubextension.instNormalSubtypeMemSubgroupFieldExtensionSubgroupField _root_.ClassFormation.FiniteGaloisSubextension.extensionSubgroup_normalInstance _root_.ClassFormation.FiniteGaloisSubextension.extensionSubgroup_over_intermediate_normalInstance _root_.ClassFormation.FiniteGaloisSubextension.intermediateField_normalInstance _root_.ClassFormation.FiniteUnramifiedCyclicExtension.instNormalSubtypeMemSubgroupFieldExtensionSubgroupField _root_.ClassFormation.conjugateExtension_normal _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.LubinTate.compatibleGroupFamiliesGroup _root_.RamificationTheory.HilbertRamification.ValuationSubring.inertiaGroup_normal _root_.RamificationTheory.HilbertRamification.ValuationSubring.ramificationGroupInInertiaAut_normal _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.RelativeIdeleGroup.relativeIdeleMulAction _root_.ValuationTheory.DiscreteValuationField.DVF.maximalIdealPowSuccQuotModule _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.CyclicCohomology.binaryCoefficientFamilyCommGroup _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.adicCompletionProperSpace
attribute [-simp] _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.CyclicCohomology.inducedFixedEquiv_apply_coe _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit
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

/-- On the trivially acted-on value group, the finite-group norm is
multiplication by the order of the Galois group. -/
theorem galoisGroupValueGroup_tateNorm_toAdd (a : Multiplicative Int) :
    letI := galoisGroupValueGroupMulDistribMulAction K L
    Multiplicative.toAdd
        (tateNorm (Gal(L / K)) (Multiplicative Int) a) =
      (Fintype.card (Gal(L / K)) : Int) * Multiplicative.toAdd a := by
  let := galoisGroupValueGroupMulDistribMulAction K L
  have hnorm : tateNorm (Gal(L / K)) (Multiplicative Int) a =
      a ^ Fintype.card (Gal(L / K)) := by
    simp only [tateNorm, galoisGroupValueGroupMulDistribMulAction_smul,
      Finset.prod_const, Finset.card_univ]
  simpa only [toAdd_pow, nsmul_eq_mul] using
    congrArg Multiplicative.toAdd hnorm

/-- Reduction modulo `|G|` on the fixed subgroup of the trivial value-group
module. -/
def galoisGroupValueGroupFixedToZModHom :
    letI := galoisGroupValueGroupMulDistribMulAction K L
    fixedSubgroup (Gal(L / K)) (Multiplicative Int) →*
      Multiplicative (ZMod (Fintype.card (Gal(L / K)))) := by
  letI := galoisGroupValueGroupMulDistribMulAction K L
  exact
    { toFun := fun x => Multiplicative.ofAdd
        ((Multiplicative.toAdd (x : Multiplicative Int) : Int) :
          ZMod (Fintype.card (Gal(L / K))))
      map_one' := by simp
      map_mul' := by
        intro x y
        simp }

/-- States the theorem `galoisGroupValueGroupFixedToZModHom_surjective`. -/
theorem galoisGroupValueGroupFixedToZModHom_surjective :
    letI := galoisGroupValueGroupMulDistribMulAction K L
    Function.Surjective (galoisGroupValueGroupFixedToZModHom K L) := by
  let := galoisGroupValueGroupMulDistribMulAction K L
  intro y
  rcases ZMod.intCast_surjective (Multiplicative.toAdd y) with ⟨z, hz⟩
  let x : fixedSubgroup (Gal(L / K)) (Multiplicative Int) :=
    ⟨Multiplicative.ofAdd z, by intro σ; rfl⟩
  refine ⟨x, ?_⟩
  rw [show galoisGroupValueGroupFixedToZModHom K L x =
      Multiplicative.ofAdd
        ((z : Int) : ZMod (Fintype.card (Gal(L / K)))) by rfl]
  exact congrArg Multiplicative.ofAdd hz

/-- The kernel of reduction modulo `|G|` is exactly the norm subgroup inside
the fixed subgroup. -/
theorem galoisGroupValueGroupFixedToZModHom_ker :
    letI := galoisGroupValueGroupMulDistribMulAction K L
    MonoidHom.ker (galoisGroupValueGroupFixedToZModHom K L) =
      (tateNormSubgroup (Gal(L / K)) (Multiplicative Int)).subgroupOf
        (fixedSubgroup (Gal(L / K)) (Multiplicative Int)) := by
  let := galoisGroupValueGroupMulDistribMulAction K L
  ext x
  rw [MonoidHom.mem_ker]
  constructor
  · intro hx
    have hx0 :
        ((Multiplicative.toAdd (x : Multiplicative Int) : Int) :
          ZMod (Fintype.card (Gal(L / K)))) = 0 := by
      exact congrArg Multiplicative.toAdd hx
    rcases (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).1 hx0 with ⟨z, hz⟩
    change (x : Multiplicative Int) ∈
      tateNormSubgroup (Gal(L / K)) (Multiplicative Int)
    refine ⟨Multiplicative.ofAdd z, ?_⟩
    have htoAdd :
        Multiplicative.toAdd
            (tateNorm (Gal(L / K)) (Multiplicative Int)
              (Multiplicative.ofAdd z)) =
          Multiplicative.toAdd (x : Multiplicative Int) := by
      rw [galoisGroupValueGroup_tateNorm_toAdd]
      exact hz.symm
    exact congrArg Multiplicative.ofAdd htoAdd
  · intro hx
    change (x : Multiplicative Int) ∈
      tateNormSubgroup (Gal(L / K)) (Multiplicative Int) at hx
    rcases hx with ⟨z, hz⟩
    rw [tateNormHom_apply] at hz
    exact congrArg Multiplicative.ofAdd (by
      change
        ((Multiplicative.toAdd (x : Multiplicative Int) : Int) :
            ZMod (Fintype.card (Gal(L / K)))) = 0
      rw [← hz, galoisGroupValueGroup_tateNorm_toAdd]
      apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).2
      exact ⟨Multiplicative.toAdd z, rfl⟩)

/-- The actual custom Tate `H⁰` of the trivial value group is `Z/|G|Z`. -/
noncomputable def galoisGroupValueGroupHerbrandH0MulEquivZMod :
    letI := galoisGroupValueGroupMulDistribMulAction K L
    HerbrandH0 (Gal(L / K)) (Multiplicative Int) ≃*
      Multiplicative (ZMod (Fintype.card (Gal(L / K)))) := by
  letI := galoisGroupValueGroupMulDistribMulAction K L
  exact
    (HerbrandH0.equiv
      (G := Gal(L / K)) (A := Multiplicative Int)).trans
      ((QuotientGroup.quotientMulEquivOfEq
        (galoisGroupValueGroupFixedToZModHom_ker K L).symm).trans
        (QuotientGroup.quotientKerEquivOfSurjective
          (galoisGroupValueGroupFixedToZModHom K L)
          (galoisGroupValueGroupFixedToZModHom_surjective K L)))

/-- Finiteness of value-group `H⁰`, derived from its explicit cyclic
description rather than assumed as an extra hypothesis. -/
theorem galoisGroupValueGroupHerbrandH0Finite :
    letI := galoisGroupValueGroupMulDistribMulAction K L
    Finite (HerbrandH0 (Gal(L / K)) (Multiplicative Int)) := by
  let := galoisGroupValueGroupMulDistribMulAction K L
  exact Finite.of_equiv
    (Multiplicative (ZMod (Fintype.card (Gal(L / K)))))
    (galoisGroupValueGroupHerbrandH0MulEquivZMod K L).symm.toEquiv

/-- Value-group factor for the local class-field axiom: `#H⁰(G,ℤ)=|G|`. -/
theorem galoisGroupValueGroup_herbrandH0_card :
    letI := galoisGroupValueGroupMulDistribMulAction K L
    letI := galoisGroupValueGroupHerbrandH0Finite K L
    Nat.card (HerbrandH0 (Gal(L / K)) (Multiplicative Int)) =
      Fintype.card (Gal(L / K)) := by
  let := galoisGroupValueGroupMulDistribMulAction K L
  rw [Nat.card_congr (galoisGroupValueGroupHerbrandH0MulEquivZMod K L).toEquiv]
  simp

/-- For a finite Galois extension, the value-group factor is the extension
degree appearing in the local class-field-axiom theorem. -/
theorem galoisGroupValueGroup_herbrandH0_card_eq_finrank [IsGalois K L] :
    letI := galoisGroupValueGroupMulDistribMulAction K L
    letI := galoisGroupValueGroupHerbrandH0Finite K L
    Nat.card (HerbrandH0 (Gal(L / K)) (Multiplicative Int)) =
      Module.finrank K L := by
  let := galoisGroupValueGroupMulDistribMulAction K L
  rw [galoisGroupValueGroup_herbrandH0_card K L]
  exact Fintype.card_eq_nat_card.trans (IsGalois.card_aut_eq_finrank K L)

end
end LocalClassFieldTheory
end

section
-- module Solutions.OAIQ244_DUKE.LocalClassFieldTheory_ClassFormation_NormalBasisGaloisAction
attribute [-instance] _root_.ClassFormation.DegreeData.GaloisSubextension.extensionSubgroup_normalInstance _root_.ClassFormation.FiniteCyclicSubextension.instNormalSubtypeMemSubgroupFieldExtensionSubgroupField _root_.ClassFormation.FiniteGaloisSubextension.extensionSubgroup_normalInstance _root_.ClassFormation.FiniteGaloisSubextension.extensionSubgroup_over_intermediate_normalInstance _root_.ClassFormation.FiniteGaloisSubextension.intermediateField_normalInstance _root_.ClassFormation.FiniteUnramifiedCyclicExtension.instNormalSubtypeMemSubgroupFieldExtensionSubgroupField _root_.ClassFormation.conjugateExtension_normal _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.LubinTate.compatibleGroupFamiliesGroup _root_.RamificationTheory.HilbertRamification.ValuationSubring.inertiaGroup_normal _root_.RamificationTheory.HilbertRamification.ValuationSubring.ramificationGroupInInertiaAut_normal _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.RelativeIdeleGroup.relativeIdeleMulAction _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.CyclicCohomology.binaryCoefficientFamilyCommGroup _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.adicCompletionProperSpace
attribute [-simp] _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false
/-! Provides the public declarations in the `LocalClassFieldTheory.ClassFormation.NormalBasisGaloisAction` Lean module. -/

namespace LocalClassFieldTheory

open LocalFieldTheory

open CyclicCohomology

noncomputable section

universe uG uA u

open scoped ValuativeRel
open IsNonarchimedeanLocalField
open CyclicCohomology.ProfiniteCohomology.Herbrand

variable (K L : Type u) [Field K] [Field L] [Algebra K L]
  [FiniteDimensional K L] [IsGalois K L]
  [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]

variable [ValuativeRel L]
  [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]
  [IsIntegralClosure 𝒪[L] 𝒪[K] L]

/-- The quotient action on `𝒪_Lˣ / V^n`, descended from the actual integer-unit
Galois action. -/
@[implicit_reducible]
def chosenNormalBasisIntegerUnitsQuotMulDistribMulAction
    (n : Nat) (V : Subgroup 𝒪[L]ˣ)
    (hV : (V : Set 𝒪[L]ˣ) = chosenNormalBasisPrincipalUnitSet K L n) :
    MulDistribMulAction (Gal(L / K)) (𝒪[L]ˣ ⧸ V) := by
  letI := galoisGroupIntegerUnitsMulDistribMulActionOfIsIntegralClosure K L
  exact quotientMulDistribMulActionOfSubgroupStable
    (Gal(L / K)) 𝒪[L]ˣ V (by
      intro sigma a ha
      change a ∈ (V : Set 𝒪[L]ˣ) at ha
      change sigma • a ∈ (V : Set 𝒪[L]ˣ)
      rw [hV] at ha ⊢
      exact galoisGroup_smul_mem_chosenNormalBasisPrincipalUnitSet
        (K := K) (L := L) n sigma ha)

/-- The principal-unit subgroup inclusion returns the underlying integer unit. -/
@[simp]
theorem chosenNormalBasisPrincipalUnitSubgroupInclusion_apply
    (V : Subgroup 𝒪[L]ˣ) (a : V) :
    chosenNormalBasisPrincipalUnitSubgroupInclusion (L := L) V a = a :=
  rfl

/-- The integer-unit quotient map sends a unit to its quotient class. -/
@[simp]
theorem chosenNormalBasisIntegerUnitsQuotientMap_apply
    (V : Subgroup 𝒪[L]ˣ) (a : 𝒪[L]ˣ) :
    chosenNormalBasisIntegerUnitsQuotientMap (L := L) V a =
      QuotientGroup.mk a :=
  rfl

/-- Inclusion of the principal-unit subgroup is Galois equivariant. -/
theorem chosenNormalBasisPrincipalUnitSubgroupInclusion_equivariant
    (n : Nat) (V : Subgroup 𝒪[L]ˣ)
    (hV : (V : Set 𝒪[L]ˣ) = chosenNormalBasisPrincipalUnitSet K L n)
    (sigma : Gal(L / K)) (a : V) :
    letI := chosenNormalBasisPrincipalUnitSubgroupMulDistribMulAction K L n V hV
    letI := galoisGroupIntegerUnitsMulDistribMulActionOfIsIntegralClosure K L
    chosenNormalBasisPrincipalUnitSubgroupInclusion (L := L) V (sigma • a) =
      sigma • chosenNormalBasisPrincipalUnitSubgroupInclusion (L := L) V a :=
  rfl

/-- The quotient map on integer units is Galois equivariant. -/
theorem chosenNormalBasisIntegerUnitsQuotientMap_equivariant
    (n : Nat) (V : Subgroup 𝒪[L]ˣ)
    (hV : (V : Set 𝒪[L]ˣ) = chosenNormalBasisPrincipalUnitSet K L n)
    (sigma : Gal(L / K)) (a : 𝒪[L]ˣ) :
    letI := galoisGroupIntegerUnitsMulDistribMulActionOfIsIntegralClosure K L
    letI := chosenNormalBasisIntegerUnitsQuotMulDistribMulAction K L n V hV
    chosenNormalBasisIntegerUnitsQuotientMap (L := L) V (sigma • a) =
      sigma • chosenNormalBasisIntegerUnitsQuotientMap (L := L) V a := by
  rfl

/-- Inclusion of the principal-unit subgroup is injective. -/
theorem chosenNormalBasisPrincipalUnitSubgroupInclusion_injective
    (V : Subgroup 𝒪[L]ˣ) :
    Function.Injective (chosenNormalBasisPrincipalUnitSubgroupInclusion (L := L) V) :=
  Subtype.val_injective

/-- Every integer-unit quotient class has a representative. -/
theorem chosenNormalBasisIntegerUnitsQuotientMap_surjective
    (V : Subgroup 𝒪[L]ˣ) :
    Function.Surjective (chosenNormalBasisIntegerUnitsQuotientMap (L := L) V) :=
  QuotientGroup.mk'_surjective V

/-- Exactness at the integer-unit term of `1 → V^n → 𝒪_Lˣ → 𝒪_Lˣ/V^n
→ 1`. -/
theorem chosenNormalBasisPrincipalUnitSubgroupInclusion_range_eq_ker_quotient
    (V : Subgroup 𝒪[L]ˣ) :
    MonoidHom.range (chosenNormalBasisPrincipalUnitSubgroupInclusion (L := L) V) =
      MonoidHom.ker (chosenNormalBasisIntegerUnitsQuotientMap (L := L) V) := by
  ext a
  change (∃ v : V, (v : 𝒪[L]ˣ) = a) ↔ QuotientGroup.mk' V a = 1
  rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
  constructor
  · rintro ⟨v, rfl⟩
    exact v.2
  · intro ha
    exact ⟨⟨a, ha⟩, rfl⟩

end
end LocalClassFieldTheory
end

section
-- module Solutions.OAIQ244_DUKE.LocalClassFieldTheory_ClassFormation_IntegerUnitsHerbrand
attribute [-instance] _root_.ClassFormation.DegreeData.GaloisSubextension.extensionSubgroup_normalInstance _root_.ClassFormation.FiniteCyclicSubextension.instNormalSubtypeMemSubgroupFieldExtensionSubgroupField _root_.ClassFormation.FiniteGaloisSubextension.extensionSubgroup_normalInstance _root_.ClassFormation.FiniteGaloisSubextension.extensionSubgroup_over_intermediate_normalInstance _root_.ClassFormation.FiniteGaloisSubextension.intermediateField_normalInstance _root_.ClassFormation.FiniteUnramifiedCyclicExtension.instNormalSubtypeMemSubgroupFieldExtensionSubgroupField _root_.ClassFormation.conjugateExtension_normal _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.LubinTate.compatibleGroupFamiliesGroup _root_.RamificationTheory.HilbertRamification.ValuationSubring.inertiaGroup_normal _root_.RamificationTheory.HilbertRamification.ValuationSubring.ramificationGroupInInertiaAut_normal _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.RelativeIdeleGroup.relativeIdeleMulAction _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.CyclicCohomology.binaryCoefficientFamilyCommGroup _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.adicCompletionProperSpace
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

/-- The normal-basis subgroup sequence is short exact and equivariant for
the actual actions used in the local class-field-axiom argument. -/
theorem chosenNormalBasisIntegerUnitsHerbrand_shortExact
    (n : Nat) (V : Subgroup 𝒪[L]ˣ)
    (hV : (V : Set 𝒪[L]ˣ) = chosenNormalBasisPrincipalUnitSet K L n) :
    letI := chosenNormalBasisPrincipalUnitSubgroupMulDistribMulAction K L n V hV
    letI := galoisGroupIntegerUnitsMulDistribMulActionOfIsIntegralClosure K L
    letI := chosenNormalBasisIntegerUnitsQuotMulDistribMulAction K L n V hV
    (∀ (sigma : Gal(L / K)) (a : V),
        chosenNormalBasisPrincipalUnitSubgroupInclusion (L := L) V (sigma • a) =
          sigma • chosenNormalBasisPrincipalUnitSubgroupInclusion (L := L) V a) ∧
      (∀ (sigma : Gal(L / K)) (a : 𝒪[L]ˣ),
        chosenNormalBasisIntegerUnitsQuotientMap (L := L) V (sigma • a) =
          sigma • chosenNormalBasisIntegerUnitsQuotientMap (L := L) V a) ∧
      (∀ a : 𝒪[L]ˣ,
        chosenNormalBasisIntegerUnitsQuotientMap (L := L) V a = 1 ↔
          ∃ v : V,
            chosenNormalBasisPrincipalUnitSubgroupInclusion (L := L) V v = a) ∧
      Function.Injective
        (chosenNormalBasisPrincipalUnitSubgroupInclusion (L := L) V) ∧
      Function.Surjective
        (chosenNormalBasisIntegerUnitsQuotientMap (L := L) V) := by
  let := chosenNormalBasisPrincipalUnitSubgroupMulDistribMulAction K L n V hV
  let := galoisGroupIntegerUnitsMulDistribMulActionOfIsIntegralClosure K L
  let := chosenNormalBasisIntegerUnitsQuotMulDistribMulAction K L n V hV
  refine ⟨chosenNormalBasisPrincipalUnitSubgroupInclusion_equivariant K L n V hV,
    chosenNormalBasisIntegerUnitsQuotientMap_equivariant K L n V hV, ?_,
    chosenNormalBasisPrincipalUnitSubgroupInclusion_injective (L := L) V,
    chosenNormalBasisIntegerUnitsQuotientMap_surjective (L := L) V⟩
  intro a
  have hrange :=
    chosenNormalBasisPrincipalUnitSubgroupInclusion_range_eq_ker_quotient
      (L := L) V
  constructor
  · intro ha
    have ha' : a ∈ MonoidHom.ker
        (chosenNormalBasisIntegerUnitsQuotientMap (L := L) V) := ha
    rw [← hrange] at ha'
    exact ha'
  · rintro ⟨v, rfl⟩
    have hv :
        chosenNormalBasisPrincipalUnitSubgroupInclusion (L := L) V v ∈
          MonoidHom.range
            (chosenNormalBasisPrincipalUnitSubgroupInclusion (L := L) V) :=
      ⟨v, rfl⟩
    rw [hrange] at hv
    exact hv

end
end LocalClassFieldTheory
end

section
-- module Solutions.OAIQ244_DUKE.LocalClassFieldTheory_ClassFormation_NormalBasisInfiniteProduct
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.LubinTate.Valuations.exponentialValuationSubringIsLocalRing _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionFixedSubring.instIsLocalRing _root_.RamificationTheory.HilbertRamification.ValuationSubring.selectedResidueField.instAlgebra _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.RelativeIdeleGroup.relativeIdeleMulAction _root_.ValuationTheory.DiscreteValuationField.DVF.maximalIdealPowSuccQuotModule _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.isLocalRing _root_.CyclicCohomology.binaryCoefficientFamilyCommGroup _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.adicCompletionProperSpace _root_.relativeAdeleRingIntermediateAlgebra _root_.relativeAdeleRingTopIntermediateAlgebra
attribute [-simp] _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.LocalClassFieldTheory.chosenNormalBasisPrincipalUnitSubgroupMulDistribMulAction_smul _root_.LocalClassFieldTheory.chosenNormalBasisPrincipalUnitSubgroup_sigmaMinusOne_coe _root_.LocalClassFieldTheory.chosenNormalBasisPrincipalUnitSubgroup_tateNorm_coe _root_.LocalFieldTheory.galoisGroupResidueFieldEquivOfIsIntegralClosure_residue
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

/-- Every ring equivalence of the valuation integer ring is continuous.  The
proof uses the maximal-ideal powers as a neighborhood basis and the fact that
a ring equivalence preserves each such power. -/
theorem continuous_integerRingEquiv_of_isNonarchimedeanLocalField
    [UniformSpace L] [IsUniformAddGroup L] [IsNonarchimedeanLocalField L]
    (e : 𝒪[L] ≃+* 𝒪[L]) : Continuous e := by
  apply continuous_of_continuousAt_zero e.toAddMonoidHom
  rw [ContinuousAt, map_zero, tendsto_def]
  intro s hs
  rcases exists_maximalIdeal_pow_subset_nhds_zero L s hs with ⟨N, hN⟩
  exact Filter.mem_of_superset (maximalIdeal_pow_mem_nhds_zero L N)
    (fun x hx => hN
      ((integerRingEquiv_mem_maximalIdeal_pow L e N x).2 hx))

omit [IsGalois K L] [TopologicalSpace K] [IsNonarchimedeanLocalField K] in
/-- Finite Tate norms for the actual `Gal(L / K)` action commute with limits
of valuation-ring units.  This is just continuity of each Galois conjugate
followed by continuity of a finite product. -/
theorem tendsto_galoisGroupIntegerUnits_tateNorm_of_tendsto
    [UniformSpace L] [IsUniformAddGroup L] [IsNonarchimedeanLocalField L]
    [IsIntegralClosure 𝒪[L] 𝒪[K] L]
    (f : Nat → 𝒪[L]ˣ) (x : 𝒪[L]ˣ)
    (hf : Tendsto (fun d : Nat => ((f d : 𝒪[L]ˣ) : 𝒪[L])) atTop
      (nhds ((x : 𝒪[L]ˣ) : 𝒪[L]))) :
    letI := galoisGroupIntegerUnitsMulDistribMulActionOfIsIntegralClosure K L
    Tendsto
      (fun d : Nat =>
        ((tateNorm (Gal(L / K)) 𝒪[L]ˣ (f d) : 𝒪[L]ˣ) : 𝒪[L]))
      atTop
      (nhds ((tateNorm (Gal(L / K)) 𝒪[L]ˣ x : 𝒪[L]ˣ) : 𝒪[L])) := by
  let := galoisGroupIntegerUnitsMulDistribMulActionOfIsIntegralClosure K L
  have hσ (sigma : Gal(L / K)) : Tendsto
      (fun d : Nat => ((sigma • f d : 𝒪[L]ˣ) : 𝒪[L])) atTop
      (nhds ((sigma • x : 𝒪[L]ˣ) : 𝒪[L])) := by
    have he :=
      (continuous_integerRingEquiv_of_isNonarchimedeanLocalField L
        (galoisGroupIntegerRingEquivOfIsIntegralClosure K L sigma)).tendsto
          ((x : 𝒪[L]ˣ) : 𝒪[L]) |>.comp hf
    rw [show
      (⇑(galoisGroupIntegerRingEquivOfIsIntegralClosure K L sigma) ∘
          fun d : Nat => ((f d : 𝒪[L]ˣ) : 𝒪[L])) =
        (fun d : Nat =>
          (galoisGroupIntegerRingEquivOfIsIntegralClosure K L sigma)
            ((f d : 𝒪[L]ˣ) : 𝒪[L])) by
      funext d
      rfl] at he
    simpa [
      galoisGroupIntegerUnitsMulDistribMulActionOfIsIntegralClosure_smul] using he
  have hprod := tendsto_finsetProd
    (Finset.univ : Finset (Gal(L / K))) (fun sigma _ => hσ sigma)
  convert hprod using 1 <;> first | (with_reducible_and_instances rfl) | (simp [tateNorm])

omit [FiniteDimensional K L] [IsGalois K L]
    [TopologicalSpace K] [IsNonarchimedeanLocalField K] in
/-- The actual multiplicative coboundary `x ↦ g(x)x⁻¹` on valuation-ring
units commutes with limits taken in `𝒪_L`.  We use continuity of the
restricted Galois automorphism, and continuity of inversion away from zero in
the ambient local field. -/
theorem tendsto_galoisGroupIntegerUnits_sigmaMinusOne_of_tendsto
    [UniformSpace L] [IsUniformAddGroup L] [IsNonarchimedeanLocalField L]
    [IsIntegralClosure 𝒪[L] 𝒪[K] L]
    (g : Gal(L / K)) (f : Nat → 𝒪[L]ˣ) (x : 𝒪[L]ˣ)
    (hf : Tendsto (fun d : Nat => ((f d : 𝒪[L]ˣ) : 𝒪[L])) atTop
      (nhds ((x : 𝒪[L]ˣ) : 𝒪[L]))) :
    letI := galoisGroupIntegerUnitsMulDistribMulActionOfIsIntegralClosure K L
    Tendsto
      (fun d : Nat =>
        ((sigmaMinusOne (Gal(L / K)) 𝒪[L]ˣ g (f d) : 𝒪[L]ˣ) : 𝒪[L]))
      atTop
      (nhds ((sigmaMinusOne (Gal(L / K)) 𝒪[L]ˣ g x : 𝒪[L]ˣ) : 𝒪[L])) := by
  let := galoisGroupIntegerUnitsMulDistribMulActionOfIsIntegralClosure K L
  have hgO : Tendsto
      (fun d : Nat => ((g • f d : 𝒪[L]ˣ) : 𝒪[L])) atTop
      (nhds ((g • x : 𝒪[L]ˣ) : 𝒪[L])) := by
    have he :=
      (continuous_integerRingEquiv_of_isNonarchimedeanLocalField L
        (galoisGroupIntegerRingEquivOfIsIntegralClosure K L g)).tendsto
          ((x : 𝒪[L]ˣ) : 𝒪[L]) |>.comp hf
    rw [show
      (⇑(galoisGroupIntegerRingEquivOfIsIntegralClosure K L g) ∘
          fun d : Nat => ((f d : 𝒪[L]ˣ) : 𝒪[L])) =
        (fun d : Nat =>
          (galoisGroupIntegerRingEquivOfIsIntegralClosure K L g)
            ((f d : 𝒪[L]ˣ) : 𝒪[L])) by
      funext d
      rfl] at he
    simpa [
      galoisGroupIntegerUnitsMulDistribMulActionOfIsIntegralClosure_smul] using he
  have hfL : Tendsto
      (fun d : Nat => (((f d : 𝒪[L]ˣ) : 𝒪[L]) : L)) atTop
      (nhds (((x : 𝒪[L]ˣ) : 𝒪[L]) : L)) :=
    continuous_subtype_val.tendsto ((x : 𝒪[L]ˣ) : 𝒪[L]) |>.comp hf
  have hgL : Tendsto
      (fun d : Nat => (((g • f d : 𝒪[L]ˣ) : 𝒪[L]) : L)) atTop
      (nhds (((g • x : 𝒪[L]ˣ) : 𝒪[L]) : L)) :=
    continuous_subtype_val.tendsto ((g • x : 𝒪[L]ˣ) : 𝒪[L]) |>.comp hgO
  have hinv_coe (u : 𝒪[L]ˣ) :
      ((((u⁻¹ : 𝒪[L]ˣ) : 𝒪[L])) : L) =
        ((((u : 𝒪[L]ˣ) : 𝒪[L])) : L)⁻¹ := by
    apply eq_inv_of_mul_eq_one_right
    exact congrArg (fun y : 𝒪[L] => (y : L)) u.val_inv
  apply tendsto_subtype_rng.2
  have h := hgL.mul (hfL.inv₀ (by
    intro hx0
    apply Units.ne_zero x
    apply Subtype.ext
    exact hx0))
  convert h using 1 <;> first | (with_reducible_and_instances rfl) | (simp [sigmaMinusOne, hinv_coe])

end
end LocalClassFieldTheory
end

section
-- module Solutions.OAIQ244_DUKE.LocalClassFieldTheory_Finite_LocalReciprocity_AbsoluteUnitsFixedField
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionResidueField.instField _root_.RamificationTheory.HilbertRamification.ValuationSubring.selectedResidueField.instAlgebra _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.RelativeIdeleGroup.relativeIdeleMulAction _root_.ValuationTheory.DiscreteValuationField.DVF.maximalIdealPowSuccQuotModule _root_.ValuationTheory.DiscreteValuationField.DVF.residueField.field _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.isLocalRing _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.adicCompletionProperSpace _root_.relativeAdeleRingIntermediateAlgebra _root_.relativeAdeleRingTopIntermediateAlgebra
attribute [-simp] _root_.ClassFormation.DegreeData.maximalUnramifiedNormClass_eq_zero_iff _root_.ClassFormation.DegreeData.maximalUnramifiedNormQuotientInfiniteEquiv_maximalUnramifiedNormClass _root_.ClassFormation.DegreeData.maximalUnramifiedNormQuotientLift_maximalUnramifiedNormClass _root_.ClassFormation.DegreeData.maximalUnramifiedToFiniteNormQuotient_maximalUnramifiedNormClass _root_.ClassFormation.DegreeData.mem_maximalUnramifiedNormSubgroup_iff _root_.ClassFormation.ValuationData.mem_unitAddSubgroup_iff _root_.ClassFormation.ValuationData.unitRepresentation_quotient_mk_apply _root_.ClassFormation.ValuationData.valuationAt_chosenPrimeElement _root_.ClassFormation.ValuationData.valuationAt_coe _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.ClassFormation.conjugateFixedElement_coe _root_.ClassFormation.extensionFixedRepresentationEquiv_apply_coe _root_.ClassFormation.extensionFixedRepresentationEquiv_symm_apply_coe _root_.ClassFormation.finiteNormClass_add _root_.ClassFormation.finiteNormClass_eq_zero_iff _root_.ClassFormation.finiteNormClass_nsmul _root_.ClassFormation.finiteNormClass_sub _root_.ClassFormation.finiteNormClass_zero _root_.ClassFormation.finiteNormQuotientConcreteEquiv_finiteNormClass _root_.ClassFormation.finiteNormQuotientLift_finiteNormClass _root_.ClassFormation.fixedFieldInclusion_coe _root_.ClassFormation.infiniteNormClass_eq_zero_iff _root_.ClassFormation.infiniteNormQuotientConcreteEquiv_infiniteNormClass _root_.ClassFormation.infiniteNormQuotientLift_infiniteNormClass _root_.ClassFormation.mem_infiniteNormSubgroup_iff _root_.ClassFormation.normalExtensionAction_coe _root_.ClassFormation.relativeCosetAction_mk _root_.ClassFormation.relativeCosetAction_zero _root_.ClassFormation.relativeNorm_apply_coe _root_.ClassFormation.relativeNorm_self _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.LocalFieldTheory.residueField_algebraMap_residue
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

namespace LocalClassFieldTheory

open RamificationTheory KummerTheory CyclicCohomology

/-!
# Finite local reciprocity: Galois units and fixed fields

For local reciprocity the coefficient module in the abstract class formation is
`A = (K^sep)ˣ`.  This file identifies its subgroup fixed by the actual closed
fixing subgroup of an intermediate field `E` with the image of `Eˣ`.

The result is stated for an arbitrary Galois ambient extension.  In particular
it applies to `SeparableClosure K / K` for every field `K`; no perfectness,
local-field, or finite-dimensional hypothesis is needed.  Using the separable
closure is essential in positive characteristic: the fixed field of
`Aut(K^alg/K)` inside `K^alg` need not be `K` when `K` is imperfect.
-/

noncomputable section

variable (K Ω : Type) [Field K] [Field Ω] [Algebra K Ω]

variable [IsGalois K Ω]

/-- An ambient unit is fixed by `Gal(Ω/E)` exactly when its underlying
field element belongs to `E`. -/
theorem mem_galoisAmbientUnits_fixed_iff
    (E : IntermediateField K Ω)
    (x : Additive Ωˣ) :
    x ∈ ambientFixedAddSubgroup (galoisAmbientUnitsRep K Ω)
        (closedFixingSubgroup K Ω E) ↔
      ((Additive.toMul x : Ωˣ) : Ω) ∈ E := by
  change
    (show galoisAmbientUnitsRep K Ω from x) ∈
        ambientFixedAddSubgroup (galoisAmbientUnitsRep K Ω)
          (closedFixingSubgroup K Ω E) ↔
      ((Additive.toMul x : Ωˣ) : Ω) ∈ E
  rw [mem_ambientFixedAddSubgroup_iff]
  constructor
  · intro hx
    rw [← InfiniteGalois.fixedField_fixingSubgroup E,
      IntermediateField.mem_fixedField_iff]
    intro σ hσ
    have hσclosed :
        σ ∈ (closedFixingSubgroup K Ω E).toSubgroup := by
      simpa only [closedFixingSubgroup] using hσ
    have hfixed := hx ⟨σ, hσclosed⟩
    have hρ :
        (Rep.ofAlgebraAutOnUnits K Ω).ρ σ x =
          Additive.ofMul
            (Units.mapEquiv σ.toMulEquiv (Additive.toMul x)) :=
      rfl
    rw [hρ] at hfixed
    have hval := congrArg
      (fun z : Additive Ωˣ ↦ ((Additive.toMul z : Ωˣ) : Ω)) hfixed
    convert hval using 1
    all_goals try with_reducible_and_instances rfl
    rfl
  · intro hx σ
    have hσE : σ.1 ∈ E.fixingSubgroup := by
      simpa only [closedFixingSubgroup] using σ.2
    have hρ :
        (Rep.ofAlgebraAutOnUnits K Ω).ρ
            (σ : Gal(Ω / K)) x =
          Additive.ofMul
            (Units.mapEquiv
              (σ : Gal(Ω / K)).toMulEquiv (Additive.toMul x)) :=
      rfl
    rw [hρ]
    apply Additive.ext
    rw [toMul_ofMul]
    apply Units.ext
    convert (IntermediateField.mem_fixingSubgroup_iff E σ.1).1 hσE _ hx using 1
    all_goals try with_reducible_and_instances rfl
    rfl

/-- The image of `Eˣ` in `Ωˣ` is precisely the abstract fixed
subgroup `A_E` used in the abstract class-formation framework. -/
theorem intermediateFieldUnitsToGaloisAmbient_range
    (E : IntermediateField K Ω) :
    (intermediateFieldUnitsToGaloisAmbient K Ω E).range =
      ambientFixedAddSubgroup (galoisAmbientUnitsRep K Ω)
        (closedFixingSubgroup K Ω E) := by
  apply AddSubgroup.ext
  intro x
  constructor
  · rintro ⟨y, rfl⟩
    change
      (show galoisAmbientUnitsRep K Ω from
        intermediateFieldUnitsToGaloisAmbient K Ω E y) ∈
        ambientFixedAddSubgroup (galoisAmbientUnitsRep K Ω)
          (closedFixingSubgroup K Ω E)
    apply (mem_galoisAmbientUnits_fixed_iff K Ω E _).2
    rw [← ofMul_toMul y, intermediateFieldUnitsToGaloisAmbient_apply,
      toMul_ofMul, Units.coe_map]
    exact (Additive.toMul y : Eˣ).1.property
  · intro hx
    have hxE :
        ((Additive.toMul x : Ωˣ) : Ω) ∈ E :=
      (mem_galoisAmbientUnits_fixed_iff K Ω E x).1 hx
    let y₀ : E :=
      ⟨((Additive.toMul x : Ωˣ) : Ω), hxE⟩
    have hy₀ : y₀ ≠ 0 := by
      intro h
      have h' :
          ((Additive.toMul x : Ωˣ) : Ω) = 0 :=
        congrArg E.val h
      exact (Additive.toMul x : Ωˣ).ne_zero h'
    let y : Eˣ := Units.mk0 y₀ hy₀
    refine ⟨Additive.ofMul y, ?_⟩
    rw [intermediateFieldUnitsToGaloisAmbient_apply]
    apply Additive.ext
    rw [toMul_ofMul]
    apply Units.ext
    rw [Units.coe_map]
    rfl

/-- Canonical additive equivalence `Eˣ ≃ A_E` for the actual ambient-unit
representation. -/
def intermediateFieldUnitsEquivGaloisFixed
    (E : IntermediateField K Ω) :
    Additive Eˣ ≃+ ambientFixedAddSubgroup (galoisAmbientUnitsRep K Ω)
      (closedFixingSubgroup K Ω E) := by
  let eRange : Additive Eˣ ≃+
      (intermediateFieldUnitsToGaloisAmbient K Ω E).range :=
    AddMonoidHom.ofInjective (by
      intro x y hxy
      apply Additive.toMul.injective
      exact (Units.map_injective E.val.injective) (congrArg Additive.toMul hxy))
  exact eRange.trans
    (AddEquiv.addSubgroupCongr
      (intermediateFieldUnitsToGaloisAmbient_range K Ω E))

/-- States the theorem `intermediateFieldUnitsEquivGaloisFixed_coe`. -/
@[simp]
theorem intermediateFieldUnitsEquivGaloisFixed_coe
    (E : IntermediateField K Ω) (x : Additive Eˣ) :
    (intermediateFieldUnitsEquivGaloisFixed K Ω E x).1 =
        intermediateFieldUnitsToGaloisAmbient K Ω E x :=
  rfl

/-- For an embedded extension `i : L → Ω`, the coefficient group fixed by
`Gal(Ω/i(L))` is canonically the actual unit group `Lˣ`.  This is the form
needed when an abstract finite extension is realized inside a separable
closure. -/
def embeddedFieldUnitsEquivGaloisFixed
    (L : Type) [Field L] [Algebra K L]
    (i : L →ₐ[K] Ω) :
    Additive Lˣ ≃+ ambientFixedAddSubgroup (galoisAmbientUnitsRep K Ω)
      (closedFixingSubgroup K Ω (AlgHom.fieldRange i)) :=
  (MulEquiv.toAdditive
    (Units.mapEquiv (AlgEquiv.ofInjectiveField i).toMulEquiv)).trans
      (intermediateFieldUnitsEquivGaloisFixed K Ω (AlgHom.fieldRange i))

/-- States the theorem `embeddedFieldUnitsEquivGaloisFixed_coe`. -/
@[simp]
theorem embeddedFieldUnitsEquivGaloisFixed_coe
    (L : Type) [Field L] [Algebra K L]
    (i : L →ₐ[K] Ω) (x : Lˣ) :
    (embeddedFieldUnitsEquivGaloisFixed K Ω L i (Additive.ofMul x)).1 =
      Additive.ofMul (Units.map i.toRingHom.toMonoidHom x) :=
  rfl

end
end LocalClassFieldTheory
end

section
-- module Solutions.OAIQ244_DUKE.LocalClassFieldTheory_Finite_LocalReciprocity_GaloisExtensionQuotient
attribute [-instance] _root_.ClassFormation.DegreeData.FiniteTower.totalQuotientFinite _root_.ClassFormation.DegreeData.frobeniusClosure_isTopologicalGroup _root_.ClassFormation.FiniteCyclicSubextension.instFiniteQuotientSubtypeMemSubgroupFieldExtensionSubgroupField _root_.ClassFormation.FiniteCyclicSubextension.instFintypeQuotientSubtypeMemSubgroupFieldExtensionSubgroupField _root_.ClassFormation.FiniteCyclicSubextension.instNormalSubtypeMemSubgroupFieldExtensionSubgroupField _root_.ClassFormation.FiniteGaloisSubextension.extensionSubgroup_normalInstance _root_.ClassFormation.FiniteGaloisSubextension.extensionSubgroup_over_intermediate_normalInstance _root_.ClassFormation.FiniteGaloisSubextension.intermediateField_normalInstance _root_.ClassFormation.FiniteUnramifiedCyclicExtension.instFiniteQuotientSubtypeMemSubgroupFieldExtensionSubgroupField _root_.ClassFormation.FiniteUnramifiedCyclicExtension.instFintypeQuotientSubtypeMemSubgroupFieldExtensionSubgroupField _root_.ClassFormation.FiniteUnramifiedCyclicExtension.instNormalSubtypeMemSubgroupFieldExtensionSubgroupField _root_.ClassFormation.conjugateExtension_normal _root_.ClassFormation.finiteNormQuotientAddCommGroup _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.LubinTate.compatibleGroupFamiliesGroup _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionResidueField.instField _root_.RamificationTheory.HilbertRamification.ValuationSubring.inertiaGroup_normal _root_.RamificationTheory.HilbertRamification.ValuationSubring.ramificationGroupInInertiaAut_normal _root_.RamificationTheory.HilbertRamification.ValuationSubring.selectedResidueField.instAlgebra _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.RelativeIdeleGroup.relativeIdeleMulAction _root_.ValuationTheory.DiscreteValuationField.DVF.maximalIdealPowSuccQuotModule _root_.ValuationTheory.DiscreteValuationField.DVF.residueField.field _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.adicCompletionProperSpace _root_.relativeAdeleRingIntermediateAlgebra _root_.relativeAdeleRingTopIntermediateAlgebra
attribute [-simp] _root_.ClassFormation.DegreeData.extensionNormalizedDegreeContinuous_apply _root_.ClassFormation.DegreeData.extensionNormalizedDegreeContinuous_toMonoidHom _root_.ClassFormation.DegreeData.maximalUnramifiedToFiniteNormQuotient_maximalUnramifiedNormClass _root_.ClassFormation.FiniteGaloisSubextension.extensionQuotientMk_apply _root_.ClassFormation.FiniteGaloisSubextension.extensionQuotientMk_eq_one_iff _root_.ClassFormation.ValuationData.unitRepresentation_quotient_mk_apply _root_.ClassFormation.absoluteConjugateCosetEquiv_mk _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.ClassFormation.extensionFixedRepresentationEquiv_apply_coe _root_.ClassFormation.extensionFixedRepresentationEquiv_symm_apply_coe _root_.ClassFormation.finiteNormClass_add _root_.ClassFormation.finiteNormClass_eq_zero_iff _root_.ClassFormation.finiteNormClass_nsmul _root_.ClassFormation.finiteNormClass_sub _root_.ClassFormation.finiteNormClass_zero _root_.ClassFormation.finiteNormQuotientConcreteEquiv_finiteNormClass _root_.ClassFormation.finiteNormQuotientLift_finiteNormClass _root_.ClassFormation.finiteReciprocityNaturalityConjugation_mk _root_.ClassFormation.normalExtensionAction_coe _root_.ClassFormation.relativeConjugateCosetEquiv_mk _root_.ClassFormation.relativeNorm_self _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.LocalFieldTheory.residueField_algebraMap_residue
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

namespace LocalClassFieldTheory
open RamificationTheory CyclicCohomology

open ClassFormation

/-!
# Finite local reciprocity: abstract extension quotients and actual Galois groups

For a Galois ambient extension `Ω/K`, the abstract class-formation model represents `K` by the
closed fixing subgroup of the bottom intermediate field and an intermediate
normal extension `E/K` by the closed subgroup fixing `E`.  This file proves
that the resulting abstract class-formation quotient is canonically the actual group
`Gal(E/K)`.
-/

noncomputable section

variable (K Ω : Type) [Field K] [Field Ω] [Algebra K Ω] [IsGalois K Ω]

/-- The subgroup fixing the bottom intermediate field is the distinguished
base field of the class formation. -/
theorem closedFixingSubgroup_bot_eq_baseField :
    closedFixingSubgroup K Ω (⊥ : IntermediateField K Ω) =
      baseField (Gal(Ω / K)) := by
  ext σ
  change σ ∈ (⊥ : IntermediateField K Ω).fixingSubgroup ↔
    σ ∈ (⊤ : Subgroup (Gal(Ω / K)))
  rw [IntermediateField.fixingSubgroup_bot]

/-- The fixing subgroup of an intermediate field lies in the fixing subgroup
of the base field. -/
theorem fixingSubgroupLeBase
    (E : IntermediateField K Ω) :
    (closedFixingSubgroup K Ω E).toSubgroup ≤
      (closedFixingSubgroup K Ω (⊥ : IntermediateField K Ω)).toSubgroup :=
  IntermediateField.fixingSubgroup_le bot_le

/-- In the base fixing group, the abstract class-formation extension subgroup is exactly
the subgroup obtained from the ambient fixing subgroup by `subgroupOf`. -/
theorem extensionSubgroup_base_eq_subgroupOf
    (E : IntermediateField K Ω) :
    extensionSubgroup
        (closedFixingSubgroup K Ω (⊥ : IntermediateField K Ω))
        (closedFixingSubgroup K Ω E) (fixingSubgroupLeBase K Ω E) =
      (closedFixingSubgroup K Ω E).toSubgroup.subgroupOf
        (closedFixingSubgroup K Ω (⊥ : IntermediateField K Ω)).toSubgroup := by
  rfl

/-- The fixing subgroup of a Galois intermediate extension is normal in the
ambient Galois group. -/
instance closedFixingSubgroup_normal
    (E : IntermediateField K Ω) [IsGalois K E] :
    (closedFixingSubgroup K Ω E).toSubgroup.Normal :=
  (InfiniteGalois.normal_iff_isGalois E).2 inferInstance

/-- Normality of a Galois intermediate extension, in the exact subgroup
presentation used by the abstract class-formation framework. -/
instance extensionSubgroupBase_normal
    (E : IntermediateField K Ω) [IsGalois K E] :
    (extensionSubgroup
      (closedFixingSubgroup K Ω (⊥ : IntermediateField K Ω))
      (closedFixingSubgroup K Ω E) (fixingSubgroupLeBase K Ω E)).Normal := by
  rw [extensionSubgroup_base_eq_subgroupOf]
  infer_instance

/-- The quotient map from the abstract class-formation base fixing group to the ordinary
ambient quotient by `Gal(Ω/E)`. -/
def baseFixingToAmbientQuotient
    (E : IntermediateField K Ω) [IsGalois K E] :
    (closedFixingSubgroup K Ω (⊥ : IntermediateField K Ω)).toSubgroup →*
      Gal(Ω / K) ⧸ (closedFixingSubgroup K Ω E).toSubgroup :=
  (QuotientGroup.mk' (closedFixingSubgroup K Ω E).toSubgroup).comp
    (closedFixingSubgroup K Ω (⊥ : IntermediateField K Ω)).toSubgroup.subtype

/-- The kernel of the preceding map is the exact `extensionSubgroup` used in
the abstract theory. -/
theorem baseFixingToAmbientQuotient_ker
    (E : IntermediateField K Ω) [IsGalois K E] :
    (baseFixingToAmbientQuotient K Ω E).ker =
      extensionSubgroup
        (closedFixingSubgroup K Ω (⊥ : IntermediateField K Ω))
        (closedFixingSubgroup K Ω E) (fixingSubgroupLeBase K Ω E) := by
  rw [extensionSubgroup_base_eq_subgroupOf]
  ext x
  change
    (QuotientGroup.mk' (closedFixingSubgroup K Ω E).toSubgroup x.1 = 1) ↔
      x.1 ∈ (closedFixingSubgroup K Ω E).toSubgroup
  exact QuotientGroup.eq_one_iff x.1

/-- The base fixing group is the whole ambient Galois group, hence its map to
the ambient quotient is onto. -/
theorem baseFixingToAmbientQuotient_surjective
    (E : IntermediateField K Ω) [IsGalois K E] :
    Function.Surjective (baseFixingToAmbientQuotient K Ω E) := by
  intro q
  refine Quotient.inductionOn' q ?_
  intro σ
  have hσ :
      σ ∈ (closedFixingSubgroup K Ω
        (⊥ : IntermediateField K Ω)).toSubgroup := by
    change σ ∈ (⊥ : IntermediateField K Ω).fixingSubgroup
    rw [IntermediateField.fixingSubgroup_bot]
    exact Subgroup.mem_top σ
  exact ⟨⟨σ, hσ⟩, rfl⟩

/-- The abstract class-formation quotient for `E/K` is the ordinary quotient of the
ambient Galois group by the subgroup fixing `E`. -/
def baseFixingExtensionQuotientEquivAmbient
    (E : IntermediateField K Ω) [IsGalois K E] :
    ((closedFixingSubgroup K Ω (⊥ : IntermediateField K Ω)).toSubgroup ⧸
      extensionSubgroup
        (closedFixingSubgroup K Ω (⊥ : IntermediateField K Ω))
        (closedFixingSubgroup K Ω E) (fixingSubgroupLeBase K Ω E)) ≃*
      Gal(Ω / K) ⧸ (closedFixingSubgroup K Ω E).toSubgroup :=
  (QuotientGroup.quotientMulEquivOfEq
      (baseFixingToAmbientQuotient_ker K Ω E).symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective
      (baseFixingToAmbientQuotient K Ω E)
      (baseFixingToAmbientQuotient_surjective K Ω E))

/-- States the theorem `baseFixingExtensionQuotientEquivAmbient_mk`. -/
@[simp]
theorem baseFixingExtensionQuotientEquivAmbient_mk
    (E : IntermediateField K Ω) [IsGalois K E]
    (σ : (closedFixingSubgroup K Ω
      (⊥ : IntermediateField K Ω)).toSubgroup) :
    baseFixingExtensionQuotientEquivAmbient K Ω E (QuotientGroup.mk σ) =
      QuotientGroup.mk σ.1 :=
  rfl

/-- The exact quotient group appearing in the abstract class-formation framework for the normal
intermediate extension `E/K` is canonically the actual `Gal(E/K)`. -/
def baseFixingExtensionQuotientEquivGaloisGroup
    (E : IntermediateField K Ω) [IsGalois K E] :
    ((closedFixingSubgroup K Ω (⊥ : IntermediateField K Ω)).toSubgroup ⧸
      extensionSubgroup
        (closedFixingSubgroup K Ω (⊥ : IntermediateField K Ω))
        (closedFixingSubgroup K Ω E) (fixingSubgroupLeBase K Ω E)) ≃*
      Gal(E / K) := by
  let H : ClosedSubgroup (Gal(Ω / K)) := closedFixingSubgroup K Ω E
  letI : H.toSubgroup.Normal := closedFixingSubgroup_normal K Ω E
  exact (baseFixingExtensionQuotientEquivAmbient K Ω E).trans
    ((InfiniteGalois.normalAutEquivQuotient H).trans
      (AlgEquiv.autCongr
        (IntermediateField.equivOfEq
          (InfiniteGalois.fixedField_fixingSubgroup E))))

end
end LocalClassFieldTheory
end

section
-- module Solutions.OAIQ244_DUKE.LocalClassFieldTheory_Finite_LocalReciprocity_FiniteGaloisRealization
attribute [-instance] _root_.ClassFormation.DegreeData.FiniteTower.totalQuotientFinite _root_.ClassFormation.DegreeData.frobeniusClosure_isTopologicalGroup _root_.ClassFormation.FiniteCyclicSubextension.instFiniteQuotientSubtypeMemSubgroupFieldExtensionSubgroupField _root_.ClassFormation.FiniteCyclicSubextension.instFintypeQuotientSubtypeMemSubgroupFieldExtensionSubgroupField _root_.ClassFormation.FiniteCyclicSubextension.instNormalSubtypeMemSubgroupFieldExtensionSubgroupField _root_.ClassFormation.FiniteGaloisSubextension.extensionSubgroup_normalInstance _root_.ClassFormation.FiniteGaloisSubextension.extensionSubgroup_over_intermediate_normalInstance _root_.ClassFormation.FiniteGaloisSubextension.intermediateField_normalInstance _root_.ClassFormation.FiniteUnramifiedCyclicExtension.instFiniteQuotientSubtypeMemSubgroupFieldExtensionSubgroupField _root_.ClassFormation.FiniteUnramifiedCyclicExtension.instFintypeQuotientSubtypeMemSubgroupFieldExtensionSubgroupField _root_.ClassFormation.FiniteUnramifiedCyclicExtension.instNormalSubtypeMemSubgroupFieldExtensionSubgroupField _root_.ClassFormation.conjugateExtension_normal _root_.ClassFormation.finiteNormQuotientAddCommGroup _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.LubinTate.compatibleGroupFamiliesGroup _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionResidueExtension_normal _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionResidueField.instField _root_.RamificationTheory.HilbertRamification.ValuationSubring.inertiaGroup_normal _root_.RamificationTheory.HilbertRamification.ValuationSubring.ramificationGroupInInertiaAut_normal _root_.RamificationTheory.HilbertRamification.ValuationSubring.selectedResidueField.instAlgebra _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.RelativeIdeleGroup.relativeIdeleMulAction _root_.ValuationTheory.DiscreteValuationField.DVF.maximalIdealPowSuccQuotModule _root_.ValuationTheory.DiscreteValuationField.DVF.residueField.field _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.isLocalRing _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.adicCompletionProperSpace _root_.cyclicPrimeSubextension_isGalois _root_.finiteNormalClosure_isGalois _root_.relativeAdeleRingIntermediateAlgebra _root_.relativeAdeleRingTopIntermediateAlgebra
attribute [-simp] _root_.ClassFormation.DegreeData.maximalUnramifiedNormClass_eq_zero_iff _root_.ClassFormation.DegreeData.maximalUnramifiedNormQuotientInfiniteEquiv_maximalUnramifiedNormClass _root_.ClassFormation.DegreeData.maximalUnramifiedNormQuotientLift_maximalUnramifiedNormClass _root_.ClassFormation.DegreeData.maximalUnramifiedToFiniteNormQuotient_maximalUnramifiedNormClass _root_.ClassFormation.DegreeData.mem_maximalUnramifiedNormSubgroup_iff _root_.ClassFormation.ValuationData.mem_unitAddSubgroup_iff _root_.ClassFormation.ValuationData.unitRepresentation_quotient_mk_apply _root_.ClassFormation.ValuationData.valuationAt_chosenPrimeElement _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.ClassFormation.conjugateFixedElement_coe _root_.ClassFormation.extensionFixedRepresentationEquiv_apply_coe _root_.ClassFormation.extensionFixedRepresentationEquiv_symm_apply_coe _root_.ClassFormation.finiteNormClass_add _root_.ClassFormation.finiteNormClass_eq_zero_iff _root_.ClassFormation.finiteNormClass_nsmul _root_.ClassFormation.finiteNormClass_sub _root_.ClassFormation.finiteNormClass_zero _root_.ClassFormation.finiteNormQuotientConcreteEquiv_finiteNormClass _root_.ClassFormation.finiteNormQuotientLift_finiteNormClass _root_.ClassFormation.fixedFieldInclusion_coe _root_.ClassFormation.infiniteNormClass_eq_zero_iff _root_.ClassFormation.infiniteNormQuotientConcreteEquiv_infiniteNormClass _root_.ClassFormation.infiniteNormQuotientLift_infiniteNormClass _root_.ClassFormation.mem_infiniteNormSubgroup_iff _root_.ClassFormation.normalExtensionAction_coe _root_.ClassFormation.relativeNorm_self _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.LocalFieldTheory.residueField_algebraMap_residue
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

namespace LocalClassFieldTheory
open RamificationTheory CyclicCohomology KummerTheory

/-!
# Finite local reciprocity: realizing finite Galois extensions in a separable closure

Every finite Galois extension `L/K` is embedded into the chosen separable
closure of `K`.  Its image supplies the concrete closed subgroup used by the
abstract class-field theory.  The resulting abstract fixed coefficient group
is `Lˣ`, and the resulting abstract extension quotient is the actual
`Gal(L/K)`.

No perfectness hypothesis is imposed; this includes equal-characteristic
local fields such as finite extensions of `𝔽_q((t))`.
-/

noncomputable section

variable (K L : Type) [Field K] [Field L] [Algebra K L]
  [FiniteDimensional K L] [IsGalois K L]

/-! ## Realization relative to an explicit embedding -/

/-- The closed fixing subgroup attached to an explicit realization of
`L/K` in the separable closure. -/
def finiteGaloisClosedFixingSubgroupOfEmbedding
    (i : L →ₐ[K] SeparableClosure K) :
    ClosedSubgroup (Gal(SeparableClosure K / K)) :=
  closedFixingSubgroup K (SeparableClosure K)
    (finiteGaloisFieldRangeOfEmbedding K L i)

/-- The fixing subgroup of an embedded finite Galois extension is normal in the absolute subgroup. -/
noncomputable instance finiteGaloisExtensionSubgroupOfEmbedding_normal
    (i : L →ₐ[K] SeparableClosure K) :
    (extensionSubgroup
      (closedFixingSubgroup K (SeparableClosure K)
        (⊥ : IntermediateField K (SeparableClosure K)))
      (finiteGaloisClosedFixingSubgroupOfEmbedding K L i)
      (fixingSubgroupLeBase K (SeparableClosure K)
        (finiteGaloisFieldRangeOfEmbedding K L i))).Normal := by
  change
    (extensionSubgroup
      (closedFixingSubgroup K (SeparableClosure K)
        (⊥ : IntermediateField K (SeparableClosure K)))
      (closedFixingSubgroup K (SeparableClosure K)
        (finiteGaloisFieldRangeOfEmbedding K L i))
      (fixingSubgroupLeBase K (SeparableClosure K)
        (finiteGaloisFieldRangeOfEmbedding K L i))).Normal
  infer_instance

/-- The fixed coefficient group attached to an explicit realization is
canonically the actual unit group `Lˣ`. -/
def finiteGaloisUnitsEquivAbstractFixedOfEmbedding
    (i : L →ₐ[K] SeparableClosure K) :
    Additive Lˣ ≃+
      ambientFixedAddSubgroup
        (galoisAmbientUnitsRep K (SeparableClosure K))
        (finiteGaloisClosedFixingSubgroupOfEmbedding K L i) :=
  embeddedFieldUnitsEquivGaloisFixed K (SeparableClosure K) L i

omit [FiniteDimensional K L] [IsGalois K L] in
/-- The fixed-module equivalence sends a field unit to the unit induced by the chosen embedding. -/
@[simp]
theorem finiteGaloisUnitsEquivAbstractFixedOfEmbedding_coe
    (i : L →ₐ[K] SeparableClosure K) (x : Lˣ) :
    (finiteGaloisUnitsEquivAbstractFixedOfEmbedding K L i
      (Additive.ofMul x)).1 =
      Additive.ofMul (Units.map i.toRingHom.toMonoidHom x) :=
  rfl

/-- The abstract class-formation extension quotient attached to an explicit realization
of `L/K` is the actual relative Galois group. -/
def finiteGaloisAbstractQuotientEquivGaloisGroupOfEmbedding
    (i : L →ₐ[K] SeparableClosure K) :
    ((closedFixingSubgroup K (SeparableClosure K)
        (⊥ : IntermediateField K (SeparableClosure K))).toSubgroup ⧸
      extensionSubgroup
        (closedFixingSubgroup K (SeparableClosure K)
          (⊥ : IntermediateField K (SeparableClosure K)))
        (finiteGaloisClosedFixingSubgroupOfEmbedding K L i)
        (fixingSubgroupLeBase K (SeparableClosure K)
          (finiteGaloisFieldRangeOfEmbedding K L i))) ≃*
      Gal(L / K) :=
  (baseFixingExtensionQuotientEquivGaloisGroup K (SeparableClosure K)
    (finiteGaloisFieldRangeOfEmbedding K L i)).trans
      (AlgEquiv.autCongr
        (finiteGaloisFieldRangeEquivOfEmbedding K L i)).symm

/-! ## The chosen realization -/

/-- The concrete closed subgroup of the absolute separable Galois group
attached to `L/K`. -/
def finiteGaloisClosedFixingSubgroup :
    ClosedSubgroup (Gal(SeparableClosure K / K)) :=
  finiteGaloisClosedFixingSubgroupOfEmbedding K L
    (AlgebraicNumberTheory.separableEmbeddingIntoSeparableClosure K L)

/-- The actual coefficient group fixed by the concrete subgroup attached to
`L/K` is canonically `Lˣ`. -/
def finiteGaloisUnitsEquivAbstractFixed :
    Additive Lˣ ≃+
      ambientFixedAddSubgroup
        (galoisAmbientUnitsRep K (SeparableClosure K))
        (finiteGaloisClosedFixingSubgroup K L) :=
  finiteGaloisUnitsEquivAbstractFixedOfEmbedding K L
    (AlgebraicNumberTheory.separableEmbeddingIntoSeparableClosure K L)

omit [FiniteDimensional K L] in
/-- The canonical fixed-module equivalence sends a unit through the chosen embedding. -/
@[simp]
theorem finiteGaloisUnitsEquivAbstractFixed_coe (x : Lˣ) :
    (finiteGaloisUnitsEquivAbstractFixed K L (Additive.ofMul x)).1 =
      Additive.ofMul
        (Units.map
          (AlgebraicNumberTheory.separableEmbeddingIntoSeparableClosure K L).toRingHom.toMonoidHom
            x) :=
  rfl

end
end LocalClassFieldTheory
end

section
-- module Solutions.OAIQ244_DUKE.LocalClassFieldTheory_Finite_LocalReciprocity_IntrinsicAbsoluteData
attribute [-instance] _root_.ClassFormation.DegreeData.FiniteTower.totalQuotientFinite _root_.ClassFormation.DegreeData.frobeniusClosure_isTopologicalGroup _root_.ClassFormation.FiniteCyclicSubextension.instFiniteQuotientSubtypeMemSubgroupFieldExtensionSubgroupField _root_.ClassFormation.FiniteCyclicSubextension.instFintypeQuotientSubtypeMemSubgroupFieldExtensionSubgroupField _root_.ClassFormation.FiniteCyclicSubextension.instNormalSubtypeMemSubgroupFieldExtensionSubgroupField _root_.ClassFormation.FiniteGaloisSubextension.extensionSubgroup_normalInstance _root_.ClassFormation.FiniteGaloisSubextension.extensionSubgroup_over_intermediate_normalInstance _root_.ClassFormation.FiniteGaloisSubextension.intermediateField_normalInstance _root_.ClassFormation.FiniteUnramifiedCyclicExtension.instFiniteQuotientSubtypeMemSubgroupFieldExtensionSubgroupField _root_.ClassFormation.FiniteUnramifiedCyclicExtension.instFintypeQuotientSubtypeMemSubgroupFieldExtensionSubgroupField _root_.ClassFormation.FiniteUnramifiedCyclicExtension.instNormalSubtypeMemSubgroupFieldExtensionSubgroupField _root_.ClassFormation.conjugateExtension_normal _root_.ClassFormation.finiteNormQuotientAddCommGroup _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.LocalClassFieldTheory.finiteGaloisExtensionSubgroupOfEmbedding_normal _root_.LocalClassFieldTheory.finiteGaloisFieldRangeOfEmbedding_isGalois _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionResidueExtension_normal _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionResidueField.instField _root_.RamificationTheory.HilbertRamification.ValuationSubring.selectedResidueField.instAlgebra _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.residueField.field _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.isLocalRing _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.adicCompletionProperSpace _root_.cyclicPrimeSubextension_isGalois _root_.finiteNormalClosure_isGalois _root_.relativeAdeleRingIntermediateAlgebra _root_.relativeAdeleRingTopIntermediateAlgebra
attribute [-simp] _root_.ClassFormation.ValuationData.mem_unitAddSubgroup_iff _root_.ClassFormation.ValuationData.unitRepresentation_quotient_mk_apply _root_.ClassFormation.ValuationData.valuationAt_chosenPrimeElement _root_.ClassFormation.absoluteConjugateCosetEquiv_mk _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.LocalFieldTheory.residueField_algebraMap_residue
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

/-!
# Intrinsic absolute Galois data

This module packages the absolute Galois group of a field, its integral unit
representation, and its distinguished abstract base field using the chosen
separable closure.
-/

noncomputable section

namespace LocalClassFieldTheory

open RamificationTheory CyclicCohomology KummerTheory
open ClassFormation

/-- The integral representation of the intrinsic absolute Galois group on the
units of the chosen separable closure. -/
abbrev intrinsicAbsoluteUnits
    (F : Type) [Field F] :
    Rep ℤ (intrinsicAbsoluteGalois F) :=
  galoisAmbientUnitsRep F (SeparableClosure F)

/-- The closed base subgroup of the intrinsic absolute Galois group, expressed
as the fixing subgroup of the bottom intermediate field. -/
abbrev intrinsicAbstractBase
    (F : Type) [Field F] :
    ClosedSubgroup (intrinsicAbsoluteGalois F) :=
  closedFixingSubgroup F (SeparableClosure F)
    (⊥ : IntermediateField F (SeparableClosure F))

/-- The canonical equivalence from the intrinsic abstract base subgroup to the
full absolute Galois group. -/
noncomputable def intrinsicAbstractBaseEquivAbsolute
    (F : Type) [Field F] :
    (intrinsicAbstractBase F).toSubgroup ≃*
      intrinsicAbsoluteGalois F :=
  (MulEquiv.subgroupCongr (by
    rw [intrinsicAbstractBase,
      closedFixingSubgroup_bot_eq_baseField,
      baseField_toSubgroup])).trans Subgroup.topEquiv

/-- The inverse intrinsic-base equivalence has underlying automorphism equal to
the supplied absolute Galois automorphism. -/
@[simp]
theorem intrinsicAbstractBaseEquivAbsolute_symm_apply_val
    (F : Type) [Field F] (σ : intrinsicAbsoluteGalois F) :
    ((intrinsicAbstractBaseEquivAbsolute F).symm σ).1 = σ := by
  simp [intrinsicAbstractBaseEquivAbsolute]

/-- The intrinsic abstract base packaged as a finite abstract field; its
defining quotient is the trivial finite quotient. -/
@[reducible]
noncomputable def intrinsicFiniteAbstractBase
    (F : Type) [Field F] :
    FiniteAbstractField (intrinsicAbsoluteGalois F) where
  field := intrinsicAbstractBase F
  finite := by
    rw [intrinsicAbstractBase, closedFixingSubgroup_bot_eq_baseField]
    exact (FiniteAbstractField.base (intrinsicAbsoluteGalois F)).finite

/-- The finite intrinsic base is the distinguished finite base of the
abstract class formation. -/
@[simp]
theorem intrinsicFiniteAbstractBase_eq_base
    (F : Type) [Field F] :
    intrinsicFiniteAbstractBase F =
      FiniteAbstractField.base (intrinsicAbsoluteGalois F) := by
  have h := closedFixingSubgroup_bot_eq_baseField F (SeparableClosure F)
  change intrinsicAbstractBase F =
    baseField (intrinsicAbsoluteGalois F) at h
  exact FiniteAbstractField.eq_of_field_eq _ _ h
end LocalClassFieldTheory
end
end

section
-- module Solutions.OAIQ244_DUKE.LocalClassFieldTheory_Finite_LocalReciprocity_SeparableUnitsNorm
attribute [-instance] _root_.ClassFormation.DegreeData.frobeniusClosure_isTopologicalGroup _root_.ClassFormation.FiniteCyclicSubextension.instFiniteQuotientSubtypeMemSubgroupFieldExtensionSubgroupField _root_.ClassFormation.FiniteCyclicSubextension.instFintypeQuotientSubtypeMemSubgroupFieldExtensionSubgroupField _root_.ClassFormation.FiniteCyclicSubextension.instNormalSubtypeMemSubgroupFieldExtensionSubgroupField _root_.ClassFormation.FiniteGaloisSubextension.extensionSubgroup_normalInstance _root_.ClassFormation.FiniteGaloisSubextension.extensionSubgroup_over_intermediate_normalInstance _root_.ClassFormation.FiniteGaloisSubextension.intermediateField_normalInstance _root_.ClassFormation.FiniteUnramifiedCyclicExtension.instFiniteQuotientSubtypeMemSubgroupFieldExtensionSubgroupField _root_.ClassFormation.FiniteUnramifiedCyclicExtension.instFintypeQuotientSubtypeMemSubgroupFieldExtensionSubgroupField _root_.ClassFormation.FiniteUnramifiedCyclicExtension.instNormalSubtypeMemSubgroupFieldExtensionSubgroupField _root_.ClassFormation.conjugateExtension_normal _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.LocalClassFieldTheory.finiteGaloisExtensionSubgroupOfEmbedding_normal _root_.LocalClassFieldTheory.finiteGaloisFieldRangeOfEmbedding_isGalois _root_.LocalFieldTheory.DiscreteValuationField.finite_padicInt_finPi_nsmulQuotient _root_.LocalFieldTheory.finite_multiplicative_nthPowerQuotient _root_.LocalFieldTheory.finite_nsmulAddQuotient_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.LubinTate.compatibleGroupFamiliesGroup _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionResidueExtension_normal _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionResidueField.instField _root_.RamificationTheory.HilbertRamification.ValuationSubring.inertiaGroup_normal _root_.RamificationTheory.HilbertRamification.ValuationSubring.ramificationGroupInInertiaAut_normal _root_.RamificationTheory.HilbertRamification.ValuationSubring.selectedResidueField.instAlgebra _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.RelativeIdeleGroup.relativeIdeleMulAction _root_.ValuationTheory.DiscreteValuationField.DVF.maximalIdealPowSuccQuotModule _root_.ValuationTheory.DiscreteValuationField.DVF.residueField.field _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.isLocalRing _root_.CyclicCohomology.binaryCoefficientFamilyCommGroup _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.adicCompletionProperSpace _root_.cyclicPrimeSubextension_isGalois _root_.finiteNormalClosure_isGalois _root_.relativeAdeleRingIntermediateAlgebra _root_.relativeAdeleRingTopIntermediateAlgebra
attribute [-simp] _root_.ClassFormation.ValuationData.unitRepresentation_quotient_mk_apply _root_.ClassFormation.ValuationData.valuationAt_chosenPrimeElement _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.ClassFormation.extensionFixedRepresentationEquiv_apply_coe _root_.ClassFormation.extensionFixedRepresentationEquiv_symm_apply_coe _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.LocalClassFieldTheory.finiteGaloisUnitsEquivAbstractFixedOfEmbedding_coe _root_.LocalClassFieldTheory.finiteGaloisUnitsEquivAbstractFixed_coe _root_.LocalFieldTheory.residueField_algebraMap_residue
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

/-- Canonical identification of `Kˣ` with the coefficient group fixed by the
full absolute Galois group. -/
def baseUnitsEquivGaloisAmbientFixed :
    Additive Kˣ ≃+ ambientFixedAddSubgroup
      (galoisAmbientUnitsRep K Ω)
      (closedFixingSubgroup K Ω (⊥ : IntermediateField K Ω)) := by
  let eBot : Additive Kˣ ≃+
      Additive (⊥ : IntermediateField K Ω)ˣ :=
    MulEquiv.toAdditive
      (Units.mapEquiv (IntermediateField.botEquiv K Ω).symm.toMulEquiv)
  exact eBot.trans
    (intermediateFieldUnitsEquivGaloisFixed K Ω ⊥)

/-- States the theorem `baseUnitsEquivGaloisAmbientFixed_val`. -/
@[simp]
theorem baseUnitsEquivGaloisAmbientFixed_val (x : Kˣ) :
    ((Additive.toMul
      ((baseUnitsEquivGaloisAmbientFixed K Ω (Additive.ofMul x)).1 :
        Additive Ωˣ) : Ωˣ) : Ω) = algebraMap K Ω (x : K) := by
  rfl

section FiniteGaloisIntermediate

variable (E : IntermediateField K Ω) [FiniteDimensional K E] [IsGalois K E]

/-- Provides the instance `baseFixingExtensionQuotient_finite`. -/
noncomputable instance baseFixingExtensionQuotient_finite :
    Finite ((closedFixingSubgroup K Ω
        (⊥ : IntermediateField K Ω)).toSubgroup ⧸
      extensionSubgroup
        (closedFixingSubgroup K Ω (⊥ : IntermediateField K Ω))
        (closedFixingSubgroup K Ω E)
        (fixingSubgroupLeBase K Ω E)) :=
  (baseFixingExtensionQuotientEquivGaloisGroup K Ω E).toEquiv.finite_iff.mpr
    inferInstance

omit [FiniteDimensional K E] in
/-- States the theorem `relativeCosetAction_intermediateFieldUnit_val`. -/
theorem relativeCosetAction_intermediateFieldUnit_val
    (x : Eˣ)
    (q : (closedFixingSubgroup K Ω
        (⊥ : IntermediateField K Ω)).toSubgroup ⧸
      extensionSubgroup
        (closedFixingSubgroup K Ω (⊥ : IntermediateField K Ω))
        (closedFixingSubgroup K Ω E)
        (fixingSubgroupLeBase K Ω E)) :
    ((Additive.toMul
      (relativeCosetAction (galoisAmbientUnitsRep K Ω)
        (closedFixingSubgroup K Ω (⊥ : IntermediateField K Ω))
        (closedFixingSubgroup K Ω E) (fixingSubgroupLeBase K Ω E)
        (intermediateFieldUnitsEquivGaloisFixed K Ω E
          (Additive.ofMul x)) q) : Ωˣ) : Ω) =
      E.val ((baseFixingExtensionQuotientEquivGaloisGroup K Ω E q) (x : E)) := by
  refine Quotient.inductionOn' q ?_
  intro σ
  rw [relativeCosetAction_mk]
  change σ.1 (E.val (x : E)) =
    E.val ((baseFixingExtensionQuotientEquivGaloisGroup K Ω E
      (QuotientGroup.mk' _ σ)) (x : E))
  have hq :
      baseFixingExtensionQuotientEquivAmbient K Ω E
          (QuotientGroup.mk' _ σ) =
        QuotientGroup.mk' (closedFixingSubgroup K Ω E).toSubgroup σ.1 := by
    rfl
  have hn := InfiniteGalois.normalAutEquivQuotient_apply
    (closedFixingSubgroup K Ω E) σ.1
  change InfiniteGalois.normalAutEquivQuotient (closedFixingSubgroup K Ω E)
      (QuotientGroup.mk' _ σ.1) = _ at hn
  rw [baseFixingExtensionQuotientEquivGaloisGroup, MulEquiv.trans_apply, hq,
    MulEquiv.trans_apply, hn, AlgEquiv.autCongr_apply]
  simp only [AlgEquiv.trans_apply, IntermediateField.equivOfEq_symm,
    IntermediateField.equivOfEq_apply]
  change σ.1 (E.val (x : E)) =
    (((AlgEquiv.restrictNormalHom
      (IntermediateField.fixedField
        (closedFixingSubgroup K Ω E).toSubgroup) σ.1)
      ⟨E.val (x : E), _⟩ : IntermediateField.fixedField
        (closedFixingSubgroup K Ω E).toSubgroup) : Ω)
  rw [AlgEquiv.restrictNormalHom_apply]

/-- On units coming from a finite Galois intermediate field, the abstract
relative norm is the ordinary field norm. -/
theorem relativeNorm_intermediateFieldUnit_val (x : Eˣ) :
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
      (closedFixingSubgroup K Ω E)
      (fixingSubgroupLeBase K Ω E)
  let := Fintype.ofFinite Q
  change
    ((Additive.toMul
      (relativeNormValue (galoisAmbientUnitsRep K Ω)
        (closedFixingSubgroup K Ω (⊥ : IntermediateField K Ω))
        (closedFixingSubgroup K Ω E) (fixingSubgroupLeBase K Ω E)
        (intermediateFieldUnitsEquivGaloisFixed K Ω E
          (Additive.ofMul x))) : Ωˣ) : Ω) = _
  rw [relativeNormValue]
  let action : Q → Additive Ωˣ := fun q =>
    relativeCosetAction (galoisAmbientUnitsRep K Ω)
      (closedFixingSubgroup K Ω (⊥ : IntermediateField K Ω))
      (closedFixingSubgroup K Ω E) (fixingSubgroupLeBase K Ω E)
      (intermediateFieldUnitsEquivGaloisFixed K Ω E
        (Additive.ofMul x)) q
  change (↑(Additive.toMul (∑ q : Q, action q)) : Ω) = _
  rw [toMul_sum]
  change (Units.coeHom Ω) (∏ q : Q, Additive.toMul (action q)) = _
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
    _ = ∏ σ : Gal(E / K), E.val (σ (x : E)) := by
      exact Fintype.prod_equiv
        (baseFixingExtensionQuotientEquivGaloisGroup K Ω E).toEquiv
        (fun q : Q => ((Additive.toMul (action q) : Ωˣ) : Ω))
        (fun σ : Gal(E / K) => E.val (σ (x : E)))
        (relativeCosetAction_intermediateFieldUnit_val K Ω E x)
    _ = E.val (algebraMap K E (Algebra.norm K (x : E))) := by
      rw [Algebra.norm_eq_prod_automorphisms, map_prod]
    _ = algebraMap K Ω (Algebra.norm K (x : E)) := rfl

/-- Equivariant form of the norm comparison, with both fixed coefficient
groups identified with the corresponding field unit groups. -/
theorem relativeNorm_intermediateFieldUnit (x : Eˣ) :
    relativeNorm (galoisAmbientUnitsRep K Ω)
        (closedFixingSubgroup K Ω (⊥ : IntermediateField K Ω))
        (closedFixingSubgroup K Ω E) (fixingSubgroupLeBase K Ω E)
        (intermediateFieldUnitsEquivGaloisFixed K Ω E
          (Additive.ofMul x)) =
      baseUnitsEquivGaloisAmbientFixed K Ω
        (Additive.ofMul (normUnits K E x)) := by
  apply Subtype.ext
  apply Additive.ext
  apply Units.ext
  exact relativeNorm_intermediateFieldUnit_val K Ω E x

end FiniteGaloisIntermediate

section EmbeddedFiniteGaloisExtension

variable (L : Type) [Field L] [Algebra K L]
  [FiniteDimensional K L] [IsGalois K L]
  (i : L →ₐ[K] Ω)

attribute [local instance] LocalClassFieldTheory.embeddedFieldRangeFiniteDimensional
attribute [local instance] LocalClassFieldTheory.embeddedFieldRangeIsGalois
omit [IsGalois K Ω] [FiniteDimensional K L] [IsGalois K L] in

/-- The field norm is invariant under an algebra equivalence, at unit level. -/
theorem normUnits_embeddedExtensionAlgEquiv (x : Lˣ) :
    normUnits K (AlgHom.fieldRange i)
        (Units.mapEquiv (AlgEquiv.ofInjectiveField i).toMulEquiv x) =
      normUnits K L x := by
  apply Units.ext
  exact Algebra.norm_eq_of_algEquiv
    (AlgEquiv.ofInjectiveField i) (x : L)

end EmbeddedFiniteGaloisExtension

end
end LocalClassFieldTheory
end

section
-- module Solutions.OAIQ244_DUKE.LocalClassFieldTheory_Finite_LocalReciprocity_ConcreteReciprocityTransport
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionResidueField.instField _root_.RamificationTheory.HilbertRamification.ValuationSubring.selectedResidueField.instAlgebra _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.residueField.field _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.adicCompletionProperSpace _root_.relativeAdeleRingIntermediateAlgebra _root_.relativeAdeleRingTopIntermediateAlgebra
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

namespace LocalClassFieldTheory
open RamificationTheory KummerTheory CyclicCohomology

open LocalFieldTheory

open ClassFormation

/-!
# Finite local reciprocity: transport of abstract reciprocity to a field extension

This file contains the final comparison step in the proof of the local
reciprocity law.  Once the actual absolute-Galois datum, henselian valuation,
and class-field axiom have been constructed, the abstract reciprocity theorem is transported
through the concrete finite Galois realization in a separable closure and
through the actual field norm.

The coefficient module remains `(SeparableClosure K)ˣ`; this is essential in
imperfect positive characteristic.
-/

noncomputable section

variable (K L : Type) [Field K] [Field L] [Algebra K L]
  [FiniteDimensional K L] [IsGalois K L]

abbrev G_p1 (K : Type) [Field K] :=
  intrinsicAbsoluteGalois K

abbrev A_p0 (K : Type) [Field K] : Rep ℤ (G_p1 K) :=
  intrinsicAbsoluteUnits K

abbrev B_p1 (K : Type) [Field K] : ClosedSubgroup (G_p1 K) :=
  intrinsicAbstractBase K

noncomputable instance intrinsicAbsoluteGaloisT2 : T2Space (G_p1 K) :=
  krullTopology_t2

/-! ## Transport relative to an explicit embedding -/

end
end LocalClassFieldTheory
end

section
-- module Solutions.OAIQ244_DUKE.LocalClassFieldTheory_Finite_LocalReciprocity_ConcreteReciprocityCanonical
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionResidueExtension_normal _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionResidueField.instField _root_.RamificationTheory.HilbertRamification.ValuationSubring.selectedResidueField.instAlgebra _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.maximalIdealPowSuccQuotModule _root_.ValuationTheory.DiscreteValuationField.DVF.residueField.field _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.adicCompletionProperSpace _root_.cyclicPrimeSubextension_isGalois _root_.finiteNormalClosure_isGalois _root_.relativeAdeleRingIntermediateAlgebra _root_.relativeAdeleRingTopIntermediateAlgebra
attribute [-simp] _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.LocalFieldTheory.residueField_algebraMap_residue
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
# Finite local reciprocity: canonicity of local reciprocity

The construction of local reciprocity realizes a finite Galois extension in
a fixed separable closure.  This file proves that the transported reciprocity
isomorphism is independent of that realization.  Two embeddings are extended
to an automorphism of the separable closure, and
the abstract reciprocity naturality theorem supplies the required naturality.
-/

noncomputable section

variable (K L : Type) [Field K] [Field L] [Algebra K L]
  [FiniteDimensional K L] [IsGalois K L]

abbrev G_p0 (K : Type) [Field K] :=
  intrinsicAbsoluteGalois K

abbrev AG (K : Type) [Field K] : Rep ℤ (G_p0 K) :=
  intrinsicAbsoluteUnits K

abbrev B_p0 (K : Type) [Field K] : ClosedSubgroup (G_p0 K) :=
  intrinsicAbstractBase K

/-! ## Conjugating two realizations -/

/-- An automorphism of the separable closure carrying the image of `i` to
the image of `j`. -/
def finiteGaloisEmbeddingConjugator
    (i j : L →ₐ[K] SeparableClosure K) : G_p0 K :=
  ((finiteGaloisFieldRangeEquivOfEmbedding K L i).symm.trans
    (finiteGaloisFieldRangeEquivOfEmbedding K L j)).liftNormal
      (SeparableClosure K)

omit [FiniteDimensional K L] [IsGalois K L] in
/-- The chosen absolute Galois conjugator carries one embedding to the other on every element. -/
@[simp]
theorem finiteGaloisEmbeddingConjugator_apply
    (i j : L →ₐ[K] SeparableClosure K) (x : L) :
    finiteGaloisEmbeddingConjugator K L i j (i x) = j x := by
  let ei := finiteGaloisFieldRangeEquivOfEmbedding K L i
  let ej := finiteGaloisFieldRangeEquivOfEmbedding K L j
  let e := ei.symm.trans ej
  have hi :
      algebraMap (finiteGaloisFieldRangeOfEmbedding K L i) (SeparableClosure K)
          (ei x) = i x := by
    rfl
  have hj :
      algebraMap (finiteGaloisFieldRangeOfEmbedding K L j) (SeparableClosure K)
          (e (ei x)) = j x := by
    dsimp only [e]
    rw [AlgEquiv.trans_apply, AlgEquiv.symm_apply_apply]
    rfl
  change e.liftNormal (SeparableClosure K) (i x) = j x
  rw [← hi, e.liftNormal_commutes, hj]

omit [FiniteDimensional K L] [IsGalois K L] in
/-- Composing the first embedding with its conjugator gives the second embedding. -/
theorem finiteGaloisEmbeddingConjugator_comp
    (i j : L →ₐ[K] SeparableClosure K) :
    (finiteGaloisEmbeddingConjugator K L i j).toAlgHom.comp i = j := by
  ext x
  exact congrArg Subtype.val
    (finiteGaloisEmbeddingConjugator_apply K L i j x)

omit [FiniteDimensional K L] [IsGalois K L] in
/-- The two embedded field ranges are related by the chosen Galois conjugator. -/
theorem finiteGaloisFieldRange_conjugator
    (i j : L →ₐ[K] SeparableClosure K) :
    finiteGaloisFieldRangeOfEmbedding K L j =
      (finiteGaloisFieldRangeOfEmbedding K L i).map
        (finiteGaloisEmbeddingConjugator K L i j).toAlgHom := by
  let σ := finiteGaloisEmbeddingConjugator K L i j
  calc
    finiteGaloisFieldRangeOfEmbedding K L j =
        AlgHom.fieldRange (σ.toAlgHom.comp i) := by
      exact congrArg AlgHom.fieldRange
        (finiteGaloisEmbeddingConjugator_comp K L i j).symm
    _ = (finiteGaloisFieldRangeOfEmbedding K L i).map σ.toAlgHom :=
      (AlgHom.map_fieldRange i σ.toAlgHom).symm

/-- The representative in the base subgroup obtained by conjugating with
the automorphism carrying `i` to `j`. -/
def finiteGaloisConjugateBaseElement
    (i j : L →ₐ[K] SeparableClosure K) (τ : (B_p0 K).toSubgroup) :
    (B_p0 K).toSubgroup :=
  ⟨finiteGaloisEmbeddingConjugator K L i j * τ.1 *
      (finiteGaloisEmbeddingConjugator K L i j)⁻¹, by
    change _ ∈ (⊥ : IntermediateField K (SeparableClosure K)).fixingSubgroup
    rw [IntermediateField.fixingSubgroup_bot]
    exact Subgroup.mem_top _⟩

/-! ## The two vertical maps of the abstract reciprocity naturality theorem -/

end
end LocalClassFieldTheory
end

section
-- module Solutions.OAIQ244_DUKE.LocalClassFieldTheory_Finite_LocalReciprocity_FiniteAbstractFixedField
attribute [-instance] _root_.ClassFormation.DegreeData.frobeniusClosure_isTopologicalGroup _root_.ClassFormation.FiniteGaloisSubextension.extensionSubgroup_over_intermediate_normalInstance _root_.ClassFormation.FiniteGaloisSubextension.intermediateField_normalInstance _root_.ClassFormation.conjugateExtension_normal _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.LocalClassFieldTheory.finiteGaloisExtensionSubgroupOfEmbedding_normal _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.LubinTate.compatibleGroupFamiliesGroup _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionResidueField.instField _root_.RamificationTheory.HilbertRamification.ValuationSubring.inertiaGroup_normal _root_.RamificationTheory.HilbertRamification.ValuationSubring.ramificationGroupInInertiaAut_normal _root_.RamificationTheory.HilbertRamification.ValuationSubring.selectedResidueField.instAlgebra _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.RelativeIdeleGroup.relativeIdeleMulAction _root_.ValuationTheory.DiscreteValuationField.DVF.maximalIdealPowSuccQuotModule _root_.ValuationTheory.DiscreteValuationField.DVF.residueField.field _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.adicCompletionProperSpace _root_.relativeAdeleRingIntermediateAlgebra _root_.relativeAdeleRingTopIntermediateAlgebra
attribute [-simp] _root_.ClassFormation.DegreeData.extensionNormalizedDegreeContinuous_apply _root_.ClassFormation.DegreeData.extensionNormalizedDegreeContinuous_toMonoidHom _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.ClassFormation.extensionFixedRepresentationEquiv_apply_coe _root_.ClassFormation.extensionFixedRepresentationEquiv_symm_apply_coe _root_.ClassFormation.finiteReciprocityNaturalityConjugation_mk _root_.ClassFormation.relativeConjugateCosetEquiv_mk _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.LocalFieldTheory.residueField_algebraMap_residue
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

omit [IsGalois k Ω] in
/-- Absolute finiteness in the abstract class-formation quotient presentation gives a
finite quotient of the ambient absolute Galois group by the same subgroup. -/
theorem ambientQuotientFiniteOfAbstractFinite
    (H : ClosedSubgroup (Gal(Ω / k)))
    (hfinite : Finite ((baseField (Gal(Ω / k))).toSubgroup ⧸
      extensionSubgroup (baseField (Gal(Ω / k))) H (le_baseField H))) :
    Finite (Gal(Ω / k) ⧸ H.toSubgroup) := by
  apply Nat.finite_of_card_ne_zero
  change H.toSubgroup.index ≠ 0
  rw [← Subgroup.relIndex_top_right]
  change (extensionSubgroup (baseField (Gal(Ω / k))) H
    (le_baseField H)).index ≠ 0
  exact @Subgroup.index_ne_zero_of_finite
    (baseField (Gal(Ω / k))).toSubgroup _
    (extensionSubgroup (baseField (Gal(Ω / k))) H (le_baseField H))
    hfinite

omit [IsGalois k Ω] in
/-- An abstract field finite over the distinguished base is represented by
an open subgroup of the absolute Galois group. -/
theorem abstractFiniteClosedSubgroup_isOpen
    (H : ClosedSubgroup (Gal(Ω / k)))
    (hfinite : Finite ((baseField (Gal(Ω / k))).toSubgroup ⧸
      extensionSubgroup (baseField (Gal(Ω / k))) H (le_baseField H))) :
    IsOpen H.carrier := by
  let : Finite (Gal(Ω / k) ⧸ H.toSubgroup) :=
    ambientQuotientFiniteOfAbstractFinite k Ω H hfinite
  let : Subgroup.FiniteIndex H.toSubgroup :=
    H.toSubgroup.finiteIndex_of_finite_quotient
  exact Subgroup.isOpen_of_isClosed_of_finiteIndex H.toSubgroup H.isClosed'

/-- The fixed field of an abstract field finite over the distinguished base
is an actual finite field extension. -/
theorem abstractFixedField_finiteDimensional
    (H : ClosedSubgroup (Gal(Ω / k)))
    (hfinite : Finite ((baseField (Gal(Ω / k))).toSubgroup ⧸
      extensionSubgroup (baseField (Gal(Ω / k))) H (le_baseField H))) :
    FiniteDimensional k (abstractFixedField k Ω H) := by
  apply (InfiniteGalois.isOpen_iff_finite
    (K := Ω) (abstractFixedField k Ω H)).1
  rw [InfiniteGalois.fixingSubgroup_fixedField H]
  exact abstractFiniteClosedSubgroup_isOpen k Ω H hfinite

/-- Under the preceding Galois-group equivalence, the relative class-formation
subgroup is exactly the subgroup fixing the upper concrete field. -/
theorem map_extensionSubgroup_abstractSubgroupEquiv
    (K L : ClosedSubgroup (Gal(Ω / k)))
    (hLK : L.toSubgroup ≤ K.toSubgroup) :
    (extensionSubgroup K L hLK).map
        (abstractSubgroupEquivGaloisGroup k Ω K).toMonoidHom =
      (abstractRelativeFixedField k Ω hLK).fixingSubgroup := by
  ext τ
  constructor
  · rintro ⟨σ, hσ, rfl⟩
    rw [IntermediateField.mem_fixingSubgroup_iff]
    intro x hx
    have hσL : (σ.1 : Gal(Ω / k)) ∈ L :=
      (mem_extensionSubgroup_iff K L hLK σ).1 hσ
    have hfix : ∀ y ∈ abstractFixedField k Ω L, σ.1 y = y := by
      have hσfix : σ.1 ∈ (abstractFixedField k Ω L).fixingSubgroup := by
        rw [InfiniteGalois.fixingSubgroup_fixedField L]
        exact hσL
      exact (IntermediateField.mem_fixingSubgroup_iff
        (abstractFixedField k Ω L) σ.1).1 hσfix
    exact hfix x hx
  · intro hτ
    let σ : K.toSubgroup :=
      (abstractSubgroupEquivGaloisGroup k Ω K).symm τ
    refine ⟨σ, ?_, (abstractSubgroupEquivGaloisGroup k Ω K).apply_symm_apply τ⟩
    apply (mem_extensionSubgroup_iff K L hLK σ).2
    have hσfix : (σ.1 : Gal(Ω / k)) ∈
        (abstractFixedField k Ω L).fixingSubgroup := by
      rw [IntermediateField.mem_fixingSubgroup_iff]
      intro x hx
      have hτfix := (IntermediateField.mem_fixingSubgroup_iff
        (abstractRelativeFixedField k Ω hLK) τ).1 hτ x hx
      calc
        σ.1 x = abstractSubgroupEquivGaloisGroup k Ω K σ x :=
          (abstractSubgroupEquivGaloisGroup_apply k Ω K σ x).symm
        _ = τ x := by
          rw [show abstractSubgroupEquivGaloisGroup k Ω K σ = τ by
            exact (abstractSubgroupEquivGaloisGroup k Ω K).apply_symm_apply τ]
        _ = x := hτfix
    rw [InfiniteGalois.fixingSubgroup_fixedField L] at hσfix
    exact hσfix

/-- Relative normality in the abstract class-formation framework is the actual normality of the subgroup
fixing the upper field inside the lower field's absolute Galois group. -/
theorem abstractRelativeFixingSubgroup_normal
    (K L : ClosedSubgroup (Gal(Ω / k)))
    (hLK : L.toSubgroup ≤ K.toSubgroup)
    (hnormal : (extensionSubgroup K L hLK).Normal) :
    (abstractRelativeFixedField k Ω hLK).fixingSubgroup.Normal := by
  have hmap : ((extensionSubgroup K L hLK).map
      (abstractSubgroupEquivGaloisGroup k Ω K).toMonoidHom).Normal :=
    hnormal.map (abstractSubgroupEquivGaloisGroup k Ω K).toMonoidHom
      (abstractSubgroupEquivGaloisGroup k Ω K).surjective
  rw [map_extensionSubgroup_abstractSubgroupEquiv k Ω K L hLK] at hmap
  exact hmap

/-- The concrete relative fixed field is Galois precisely from the normality
witness occurring in the abstract cyclic extension. -/
theorem abstractRelativeFixedField_isGalois
    (K L : ClosedSubgroup (Gal(Ω / k)))
    (hLK : L.toSubgroup ≤ K.toSubgroup)
    (hnormal : (extensionSubgroup K L hLK).Normal) :
    IsGalois (abstractFixedField k Ω K)
      (abstractRelativeFixedField k Ω hLK) := by
  apply (InfiniteGalois.normal_iff_isGalois
    (abstractRelativeFixedField k Ω hLK)).1
  exact abstractRelativeFixingSubgroup_normal k Ω K L hLK hnormal

/-- Restriction through the lower fixed field, followed by quotienting by
the upper fixing subgroup. -/
def abstractRelativeToAmbientQuotient
    (K L : ClosedSubgroup (Gal(Ω / k)))
    (hLK : L.toSubgroup ≤ K.toSubgroup)
    (hnormal : (extensionSubgroup K L hLK).Normal) :
    letI := abstractRelativeFixingSubgroup_normal k Ω K L hLK hnormal
    K.toSubgroup →*
      Gal(Ω / abstractFixedField k Ω K) ⧸
        (abstractRelativeFixedField k Ω hLK).fixingSubgroup := by
  letI : (abstractRelativeFixedField k Ω hLK).fixingSubgroup.Normal :=
    abstractRelativeFixingSubgroup_normal k Ω K L hLK hnormal
  exact (QuotientGroup.mk'
    (abstractRelativeFixedField k Ω hLK).fixingSubgroup).comp
      (abstractSubgroupEquivGaloisGroup k Ω K).toMonoidHom

/-- The kernel of the preceding quotient map is the exact abstract class-formation
relative subgroup. -/
theorem abstractRelativeToAmbientQuotient_ker
    (K L : ClosedSubgroup (Gal(Ω / k)))
    (hLK : L.toSubgroup ≤ K.toSubgroup)
    (hnormal : (extensionSubgroup K L hLK).Normal) :
    letI := abstractRelativeFixingSubgroup_normal k Ω K L hLK hnormal
    (abstractRelativeToAmbientQuotient k Ω K L hLK hnormal).ker =
      extensionSubgroup K L hLK := by
  let : (abstractRelativeFixedField k Ω hLK).fixingSubgroup.Normal :=
    abstractRelativeFixingSubgroup_normal k Ω K L hLK hnormal
  ext σ
  change
    QuotientGroup.mk' (abstractRelativeFixedField k Ω hLK).fixingSubgroup
        (abstractSubgroupEquivGaloisGroup k Ω K σ) = 1 ↔
      σ ∈ extensionSubgroup K L hLK
  rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
  rw [← map_extensionSubgroup_abstractSubgroupEquiv k Ω K L hLK]
  constructor
  · rintro ⟨τ, hτ, hτσ⟩
    have : τ = σ :=
      (abstractSubgroupEquivGaloisGroup k Ω K).injective hτσ
    simpa [this] using hτ
  · intro hσ
    exact ⟨σ, hσ, rfl⟩

/-- The quotient map from the abstract lower subgroup is surjective. -/
theorem abstractRelativeToAmbientQuotient_surjective
    (K L : ClosedSubgroup (Gal(Ω / k)))
    (hLK : L.toSubgroup ≤ K.toSubgroup)
    (hnormal : (extensionSubgroup K L hLK).Normal) :
    letI := abstractRelativeFixingSubgroup_normal k Ω K L hLK hnormal
    Function.Surjective
      (abstractRelativeToAmbientQuotient k Ω K L hLK hnormal) := by
  let : (abstractRelativeFixedField k Ω hLK).fixingSubgroup.Normal :=
    abstractRelativeFixingSubgroup_normal k Ω K L hLK hnormal
  intro q
  refine Quotient.inductionOn' q ?_
  intro τ
  refine ⟨(abstractSubgroupEquivGaloisGroup k Ω K).symm τ, ?_⟩
  change QuotientGroup.mk
    (abstractSubgroupEquivGaloisGroup k Ω K
      ((abstractSubgroupEquivGaloisGroup k Ω K).symm τ)) =
      QuotientGroup.mk τ
  rw [(abstractSubgroupEquivGaloisGroup k Ω K).apply_symm_apply]

/-- The exact abstract class-formation quotient of a relative normal extension is the
ordinary quotient of the lower absolute Galois group by the upper fixing
subgroup. -/
def abstractExtensionQuotientEquivAmbient
    (K L : ClosedSubgroup (Gal(Ω / k)))
    (hLK : L.toSubgroup ≤ K.toSubgroup)
    (hnormal : (extensionSubgroup K L hLK).Normal) :
    letI := hnormal
    letI := abstractRelativeFixingSubgroup_normal k Ω K L hLK hnormal
    K.toSubgroup ⧸ extensionSubgroup K L hLK ≃*
      Gal(Ω / abstractFixedField k Ω K) ⧸
        (abstractRelativeFixedField k Ω hLK).fixingSubgroup := by
  letI := hnormal
  letI : (abstractRelativeFixedField k Ω hLK).fixingSubgroup.Normal :=
    abstractRelativeFixingSubgroup_normal k Ω K L hLK hnormal
  exact (QuotientGroup.quotientMulEquivOfEq
      (abstractRelativeToAmbientQuotient_ker
        k Ω K L hLK hnormal).symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective
      (abstractRelativeToAmbientQuotient k Ω K L hLK hnormal)
      (abstractRelativeToAmbientQuotient_surjective
        k Ω K L hLK hnormal))

/-- In a finite abstract tower `L / K / k`, the concrete upper fixed field is
finite over the concrete lower fixed field. -/
theorem abstractFixedField_relativeFiniteDimensional
    (K L : ClosedSubgroup (Gal(Ω / k)))
    (hLK : L.toSubgroup ≤ K.toSubgroup)
    (hKfinite : Finite ((baseField (Gal(Ω / k))).toSubgroup ⧸
      extensionSubgroup (baseField (Gal(Ω / k))) K (le_baseField K)))
    (hLKfinite : Finite
      (K.toSubgroup ⧸ extensionSubgroup K L hLK)) :
    letI : Algebra (abstractFixedField k Ω K) (abstractFixedField k Ω L) :=
      RingHom.toAlgebra
        (IntermediateField.inclusion (abstractFixedField_le k Ω hLK))
    FiniteDimensional (abstractFixedField k Ω K)
      (abstractFixedField k Ω L) := by
  let : Algebra (abstractFixedField k Ω K) (abstractFixedField k Ω L) :=
    RingHom.toAlgebra
      (IntermediateField.inclusion (abstractFixedField_le k Ω hLK))
  let : IsScalarTower k (abstractFixedField k Ω K)
      (abstractFixedField k Ω L) :=
    IsScalarTower.of_algebraMap_eq' rfl
  let : Finite ((baseField (Gal(Ω / k))).toSubgroup ⧸
      extensionSubgroup (baseField (Gal(Ω / k))) K (le_baseField K)) :=
    hKfinite
  let : Finite
      (K.toSubgroup ⧸ extensionSubgroup K L hLK) := hLKfinite
  let : Finite ((baseField (Gal(Ω / k))).toSubgroup ⧸
      extensionSubgroup (baseField (Gal(Ω / k))) L (le_baseField L)) :=
    FiniteGaloisSubextension.finite_extension_trans hLK (le_baseField K)
  let : FiniteDimensional k (abstractFixedField k Ω L) :=
    abstractFixedField_finiteDimensional k Ω L inferInstance
  exact FiniteDimensional.right k
    (abstractFixedField k Ω K) (abstractFixedField k Ω L)

/-- The same relative finiteness statement in the scalar-extended
intermediate-field presentation used by infinite Galois theory. -/
theorem abstractRelativeFixedField_finiteDimensional
    (K L : ClosedSubgroup (Gal(Ω / k)))
    (hLK : L.toSubgroup ≤ K.toSubgroup)
    (hKfinite : Finite ((baseField (Gal(Ω / k))).toSubgroup ⧸
      extensionSubgroup (baseField (Gal(Ω / k))) K (le_baseField K)))
    (hLKfinite : Finite
      (K.toSubgroup ⧸ extensionSubgroup K L hLK)) :
    FiniteDimensional (abstractFixedField k Ω K)
      (abstractRelativeFixedField k Ω hLK) := by
  let : Algebra (abstractFixedField k Ω K) (abstractFixedField k Ω L) :=
    RingHom.toAlgebra
      (IntermediateField.inclusion (abstractFixedField_le k Ω hLK))
  let : FiniteDimensional (abstractFixedField k Ω K)
      (abstractFixedField k Ω L) :=
    abstractFixedField_relativeFiniteDimensional
      k Ω K L hLK hKfinite hLKfinite
  let e : abstractFixedField k Ω L ≃ₗ[abstractFixedField k Ω K]
      abstractRelativeFixedField k Ω hLK :=
    { toFun := fun x => ⟨x.1, x.2⟩
      invFun := fun x => ⟨x.1, x.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  exact e.finiteDimensional

end
end LocalClassFieldTheory
end

section
-- module Solutions.OAIQ244_DUKE.Valuation_DiscreteValuationField_FiniteIntegralClosure
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.LocalFieldTheory.DiscreteValuationField.Examples.Qp.padicDVRValuation_isRankOneDiscrete _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.RamificationTheory.HilbertRamification.ValuationSubring.selectedResidueField.instAlgebra _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.adicCompletionProperSpace _root_.relativeAdeleRingIntermediateAlgebra _root_.relativeAdeleRingTopIntermediateAlgebra
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
omit [FiniteDimensional K L] in
/-- The algebra map into a finite integral closure is injective. -/
theorem CanonicalIntegralClosure.algebraMap_injective
    (base : CompleteDVF.{u, v} K) :
    Function.Injective
      (algebraMap base.valuationSubring
        (integralClosure base.valuationSubring L)) := by
  intro x y hxy
  apply Subtype.ext
  apply FaithfulSMul.algebraMap_injective K L
  exact
    congrArg
      (fun z : integralClosure base.valuationSubring L => (z : L)) hxy

/- The integral closure is faithful as a module over the base valuation
ring. -/
omit [FiniteDimensional K L] in
/-- Scalar multiplication on a finite integral closure is faithful. -/
theorem CanonicalIntegralClosure.faithfulSMul
    (base : CompleteDVF.{u, v} K) :
    FaithfulSMul base.valuationSubring
      (integralClosure base.valuationSubring L) :=
  (faithfulSMul_iff_algebraMap_injective base.valuationSubring
    (integralClosure base.valuationSubring L)).mpr
    (CanonicalIntegralClosure.algebraMap_injective (K := K) (L := L) base)

omit [FiniteDimensional K L] in
/-- The integral closure in a nontrivial finite separable extension is not a field. -/
theorem integralClosure_not_isField_of_finite_separable
    (base : CompleteDVF.{u, v} K)
    [Algebra.IsSeparable K L] :
    ¬ IsField (integralClosure base.valuationSubring L) := by
  let B := integralClosure base.valuationSubring L
  let : Algebra.IsIntegral base.valuationSubring B := by
    change Algebra.IsIntegral base.valuationSubring
      (integralClosure base.valuationSubring L)
    infer_instance
  let : FaithfulSMul base.valuationSubring B :=
    CanonicalIntegralClosure.faithfulSMul (K := K) (L := L) base
  intro hB
  have hbase : IsField base.valuationSubring :=
    isField_of_isIntegral_of_isField
      (R := base.valuationSubring) (S := B)
      (FaithfulSMul.algebraMap_injective base.valuationSubring B) hB
  exact IsDiscreteValuationRing.not_isField base.valuationSubring hbase

end ValuedExtension
end DiscreteValuationField

end

end ValuationTheory
end

section
-- module Solutions.OAIQ244_DUKE.LocalClassFieldTheory_Finite_LocalReciprocity_FiniteResidueFrobenius
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionResidueExtension_normal _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.maximalIdealPowSuccQuotModule _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.isLocalRing _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.adicCompletionProperSpace
attribute [-simp] _root_.ClassFormation.DegreeData.extensionNormalizedDegreeContinuous_apply _root_.ClassFormation.DegreeData.extensionNormalizedDegreeContinuous_toMonoidHom _root_.ClassFormation.DegreeData.extensionNormalizedDegree_mk _root_.ClassFormation.DegreeData.fieldImageAdd_index _root_.ClassFormation.DegreeData.maximalUnramifiedDegreeEquiv_frobenius _root_.ClassFormation.DegreeData.maximalUnramifiedDegreeEquiv_mk _root_.ClassFormation.DegreeData.mem_maximalUnramifiedField_iff _root_.ClassFormation.DegreeData.normalizedDegree_apply_toAdd _root_.ClassFormation.DegreeData.restrictedDegreeInMulNatRange_coe _root_.ClassFormation.ValuationData.mem_unitAddSubgroup_iff _root_.ClassFormation.ValuationData.oneValue_coe _root_.ClassFormation.ValuationData.valuationAt_chosenPrimeElement _root_.ClassFormation.ValuationData.valuationAt_coe _root_.ClassFormation.ValuationData.valueModulo_apply _root_.ClassFormation.canonicalValueQuotientMap_mk _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.ClassFormation.mem_nsmulImage_iff _root_.ClassFormation.nsmulImage_top _root_.ClassFormation.zHatPowNat_apply_toAdd _root_.ClassFormation.zHatPowNat_one _root_.ClassFormation.zHatReductionMul_apply_toAdd _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.LocalFieldTheory.residueField_algebraMap_residue
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

namespace LocalClassFieldTheory

open ClassFormation

/-!
# Finite local reciprocity: finite residue Frobenius coordinates

The degree map used in local reciprocity comes from the arithmetic Frobenius
on the algebraic closure of the finite residue field.  This file constructs
the finite-level source of that map: for every finite extension of a finite
field, exponentiation of Frobenius identifies its Galois group with the
appropriate cyclic quotient of `ℤ̂`.

No cyclic generator is chosen.  The generator is the actual arithmetic
Frobenius `x ↦ x ^ #k`, and the exponent map is obtained by factoring its
integer powers through `ZMod [L : k]`.
-/

noncomputable section

universe u v w

variable (k : Type u) (L : Type v)
  [Field k] [Fintype k] [Field L] [Finite L] [Algebra k L]

/-- A profinite exponent acts on a finite residue extension through reduction
modulo its degree. -/
def finiteResidueFrobeniusFromZHat :
    ZHatMul →ₜ* (L ≃ₐ[k] L) where
  toFun z := finiteResidueFrobeniusExponentHom k L
    (Multiplicative.ofAdd
      (zHatReduction (Module.finrank k L) Module.finrank_pos z.toAdd))
  map_one' := by
    apply (finiteResidueFrobeniusExponentHom k L).map_one
  map_mul' x y := by
    apply (finiteResidueFrobeniusExponentHom k L).map_mul
  continuous_toFun := by
    apply continuous_of_discreteTopology.comp
    exact continuous_ofAdd.comp
      ((zHatReduction (Module.finrank k L) Module.finrank_pos).continuous_toFun.comp
        continuous_toAdd)

/-- The profinite Frobenius map depends on reduction modulo the residue extension degree. -/
@[simp]
theorem finiteResidueFrobeniusFromZHat_apply (z : ZHatMul) :
    finiteResidueFrobeniusFromZHat k L z =
      finiteResidueFrobeniusExponentHom k L
        (Multiplicative.ofAdd
          (zHatReduction (Module.finrank k L) Module.finrank_pos z.toAdd)) :=
  rfl

/-- The distinguished profinite integer `1` acts as arithmetic Frobenius. -/
@[simp]
theorem finiteResidueFrobeniusFromZHat_one :
    finiteResidueFrobeniusFromZHat k L
        (Multiplicative.ofAdd (1 : ZHat)) =
      FiniteField.frobeniusAlgEquivOfAlgebraic k L := by
  rw [finiteResidueFrobeniusFromZHat_apply]
  exact finiteResidueFrobeniusExponentHom_one k L

section Tower

variable {E : Type v} {F : Type w}
  [Field E] [Finite E] [Field F] [Finite F]
  [Algebra k E] [Algebra k F] [Algebra E F]
  [IsScalarTower k E F] [Normal k E]

/-- The finite Frobenius exponent coordinates commute with restriction.  The
exponent on the smaller field is obtained by the canonical reduction
`Z/[F:k]Z → Z/[E:k]Z`. -/
theorem restrictNormalHom_finiteResidueFrobeniusExponentHom
    (z : Multiplicative (ZMod (Module.finrank k F))) :
    AlgEquiv.restrictNormalHom E
        (finiteResidueFrobeniusExponentHom k F z) =
      finiteResidueFrobeniusExponentHom k E
        (Multiplicative.ofAdd
          (ZMod.castHom
            (show Module.finrank k E ∣ Module.finrank k F from
              ⟨Module.finrank E F,
                (Module.finrank_mul_finrank k E F).symm⟩)
            (ZMod (Module.finrank k E)) z.toAdd)) := by
  rcases ZMod.intCast_surjective z.toAdd with ⟨m, hm⟩
  have hz : z = Multiplicative.ofAdd
      (m : ZMod (Module.finrank k F)) := by
    apply Multiplicative.ext
    exact hm.symm
  subst z
  apply AlgEquiv.ext
  intro x
  rw [finiteResidueFrobeniusExponentHom_intCast]
  simp only [toAdd_ofAdd]
  have hred :
      ZMod.castHom
          (show Module.finrank k E ∣ Module.finrank k F from
            ⟨Module.finrank E F,
              (Module.finrank_mul_finrank k E F).symm⟩)
          (ZMod (Module.finrank k E))
          (m : ZMod (Module.finrank k F)) =
        (m : ZMod (Module.finrank k E)) := by
    exact map_intCast _ m
  rw [hred, finiteResidueFrobeniusExponentHom_intCast]
  have hfrob := restrictNormalHom_finiteResidueFrobenius
    (k := k) (E := E) (F := F)
  have hpow := congrArg (fun sigma : E ≃ₐ[k] E => sigma ^ m) hfrob
  rw [map_zpow]
  exact DFunLike.congr_fun hpow x

/-- The actions of `ℤ̂` on finite residue extensions commute with restriction
in finite towers. -/
theorem restrictNormalHom_finiteResidueFrobeniusFromZHat (z : ZHatMul) :
    AlgEquiv.restrictNormalHom E
        (finiteResidueFrobeniusFromZHat k F z) =
      finiteResidueFrobeniusFromZHat k E z := by
  rw [finiteResidueFrobeniusFromZHat_apply,
    restrictNormalHom_finiteResidueFrobeniusExponentHom,
    finiteResidueFrobeniusFromZHat_apply]
  congr 2
  apply Multiplicative.ext
  exact zHatReduction_transition
    (m := Module.finrank k E) (n := Module.finrank k F)
    Module.finrank_pos Module.finrank_pos
    (show Module.finrank k E ∣ Module.finrank k F from
      ⟨Module.finrank E F,
        (Module.finrank_mul_finrank k E F).symm⟩)
    z.toAdd

end Tower

end
end LocalClassFieldTheory
end

section
-- module Solutions.OAIQ244_DUKE.LocalClassFieldTheory_Finite_LocalReciprocity_ResidueAbsoluteFrobenius
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.LocalClassFieldTheory.finiteGaloisFieldRangeOfEmbedding_finiteDimensional _root_.LocalClassFieldTheory.finiteGaloisFieldRangeOfEmbedding_isGalois _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.LubinTate.compatibleGroupFamiliesGroup _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionResidueExtension_normal _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionResidueField.instField _root_.RamificationTheory.HilbertRamification.ValuationSubring.selectedResidueField.instAlgebra _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.RelativeIdeleGroup.relativeIdeleMulAction _root_.ValuationTheory.DiscreteValuationField.DVF.maximalIdealPowSuccQuotModule _root_.ValuationTheory.DiscreteValuationField.DVF.residueField.field _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.adicCompletionProperSpace _root_.cyclicPrimeSubextension_isGalois _root_.finiteNormalClosure_isGalois _root_.relativeAdeleRingIntermediateAlgebra _root_.relativeAdeleRingTopIntermediateAlgebra
attribute [-simp] _root_.ClassFormation.DegreeData.extensionNormalizedDegreeContinuous_apply _root_.ClassFormation.DegreeData.extensionNormalizedDegreeContinuous_toMonoidHom _root_.ClassFormation.DegreeData.extensionNormalizedDegree_mk _root_.ClassFormation.DegreeData.fieldImageAdd_index _root_.ClassFormation.DegreeData.maximalUnramifiedDegreeEquiv_frobenius _root_.ClassFormation.DegreeData.maximalUnramifiedDegreeEquiv_mk _root_.ClassFormation.DegreeData.mem_maximalUnramifiedField_iff _root_.ClassFormation.DegreeData.normalizedDegree_apply_toAdd _root_.ClassFormation.DegreeData.restrictedDegreeInMulNatRange_coe _root_.ClassFormation.ValuationData.mem_unitAddSubgroup_iff _root_.ClassFormation.ValuationData.oneValue_coe _root_.ClassFormation.ValuationData.valuationAt_chosenPrimeElement _root_.ClassFormation.ValuationData.valuationAt_coe _root_.ClassFormation.ValuationData.valueModulo_apply _root_.ClassFormation.canonicalValueQuotientMap_mk _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.ClassFormation.mem_nsmulImage_iff _root_.ClassFormation.nsmulImage_top _root_.ClassFormation.zHatPowNat_apply_toAdd _root_.ClassFormation.zHatPowNat_one _root_.ClassFormation.zHatReductionMul_apply_toAdd _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.LocalFieldTheory.residueField_algebraMap_residue
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

namespace LocalClassFieldTheory

open ClassFormation

/-!
# Finite local reciprocity: Frobenius on an infinite residue extension

The finite Frobenius exponent maps are compatible with restriction.  This
file therefore assembles them in the actual inverse-limit presentation of an
infinite Galois group.  It produces the canonical continuous homomorphism
from the profinite integers to the Galois group of an algebraic Galois
extension of a finite field.

For an algebraic closure this is the Frobenius map compared with the degree
map in finite local reciprocity. The construction itself does not require a
bijectivity hypothesis.
-/

noncomputable section

universe u v

open CategoryTheory Opposite
open FiniteGaloisIntermediateField ProfiniteGrp
variable (k : Type u) (Omega : Type v)
  [Field k] [Fintype k] [Field Omega] [Algebra k Omega]
  [IsGalois k Omega]

/-- The finite Frobenius action on an intermediate field, with finiteness
derived from finite-dimensionality over the finite base. -/
def finiteResidueFrobeniusIntermediate
    (E : FiniteGaloisIntermediateField k Omega) :
    ZHatMul →ₜ* (E ≃ₐ[k] E) := by
  letI : Finite E := Module.finite_of_finite k
  exact finiteResidueFrobeniusFromZHat k E

/-- The compatible finite Frobenius coordinates attached to one profinite
integer. -/
def residueFrobeniusLimitPoint (z : ZHatMul) :
    limit (InfiniteGalois.asProfiniteGaloisGroupFunctor k Omega) where
  val := fun E => finiteResidueFrobeniusIntermediate k Omega E.unop z
  property := by
    intro E F f
    algebraize [Subsemiring.inclusion <| leOfHom f.1]
    have : IsScalarTower k F.unop E.unop :=
      IsScalarTower.of_algebraMap_eq (congrFun rfl)
    let : Finite F.unop := Module.finite_of_finite k
    let : Finite E.unop := Module.finite_of_finite k
    change AlgEquiv.restrictNormalHom F.unop
        (finiteResidueFrobeniusFromZHat k E.unop z) =
      finiteResidueFrobeniusFromZHat k F.unop z
    exact restrictNormalHom_finiteResidueFrobeniusFromZHat
      (k := k) (E := F.unop) (F := E.unop) z

/-- The compatible Frobenius coordinates as a continuous homomorphism into
the finite-Galois inverse limit. -/
def residueFrobeniusToLimit :
    ZHatMul →ₜ* limit (InfiniteGalois.asProfiniteGaloisGroupFunctor k Omega) where
  toFun := residueFrobeniusLimitPoint k Omega
  map_one' := by
    apply Subtype.ext
    funext E
    exact (finiteResidueFrobeniusIntermediate k Omega E.unop).map_one
  map_mul' x y := by
    apply Subtype.ext
    funext E
    exact (finiteResidueFrobeniusIntermediate k Omega E.unop).map_mul x y
  continuous_toFun := by
    have hcontinuous (E : (FiniteGaloisIntermediateField k Omega)ᵒᵖ) :
        @Continuous ZHatMul (E.unop ≃ₐ[k] E.unop)
          inferInstance (krullTopology k E.unop)
          (finiteResidueFrobeniusIntermediate k Omega E.unop) :=
      (finiteResidueFrobeniusIntermediate k Omega E.unop).continuous_toFun
    let (E : (FiniteGaloisIntermediateField k Omega)ᵒᵖ) :
        TopologicalSpace (E.unop ≃ₐ[k] E.unop) :=
      ((InfiniteGalois.asProfiniteGaloisGroupFunctor k Omega).obj E).toProfinite.toTop.str
    apply Continuous.subtype_mk
    exact continuous_pi fun E => by
      change @Continuous ZHatMul (E.unop ≃ₐ[k] E.unop)
        inferInstance inferInstance
        (finiteResidueFrobeniusIntermediate k Omega E.unop)
      rw [show
        (inferInstance : TopologicalSpace (E.unop ≃ₐ[k] E.unop)) =
          krullTopology k E.unop by
        change (⊥ : TopologicalSpace (E.unop ≃ₐ[k] E.unop)) = krullTopology k E.unop
        exact (@DiscreteTopology.eq_bot _ (krullTopology k E.unop) inferInstance).symm]
      exact hcontinuous E

omit [IsGalois k Omega] in
/-- States the theorem `residueFrobeniusToLimit_apply_component`. -/
@[simp]
theorem residueFrobeniusToLimit_apply_component (z : ZHatMul)
    (E : (FiniteGaloisIntermediateField k Omega)ᵒᵖ) :
    (residueFrobeniusToLimit k Omega z).val E =
      finiteResidueFrobeniusIntermediate k Omega E.unop z :=
  rfl

/-- The canonical continuous Frobenius-parameter homomorphism
`ℤ̂ → Gal(Omega/k)` for a Galois algebraic extension of a finite field. -/
def residueAbsoluteFrobenius : ZHatMul →ₜ* (Omega ≃ₐ[k] Omega) :=
  (ContinuousMonoidHom.toContinuousMonoidHom
    (InfiniteGalois.continuousMulEquivToLimit k Omega).symm).comp
    (residueFrobeniusToLimit k Omega)

/-- Restricting the assembled Frobenius to a finite Galois intermediate
field gives exactly the finite Frobenius coordinate. -/
theorem restrictNormalHom_residueAbsoluteFrobenius
    (z : ZHatMul) (E : FiniteGaloisIntermediateField k Omega) :
    AlgEquiv.restrictNormalHom E (residueAbsoluteFrobenius k Omega z) =
      finiteResidueFrobeniusIntermediate k Omega E z := by
  have hcomponent := congrArg (fun q => q.val (op E))
    ((InfiniteGalois.continuousMulEquivToLimit k Omega).apply_symm_apply
      (residueFrobeniusToLimit k Omega z))
  exact hcomponent

/-- The element `1 ∈ ℤ̂` gives the actual arithmetic Frobenius on every
finite Galois residue subextension. -/
theorem restrictNormalHom_residueAbsoluteFrobenius_one
    (E : FiniteGaloisIntermediateField k Omega) :
    AlgEquiv.restrictNormalHom E
        (residueAbsoluteFrobenius k Omega
          (Multiplicative.ofAdd (1 : ZHat))) =
      FiniteField.frobeniusAlgEquivOfAlgebraic k E := by
  rw [restrictNormalHom_residueAbsoluteFrobenius]
  let : Finite E := Module.finite_of_finite k
  exact finiteResidueFrobeniusFromZHat_one k E

/-- The distinguished element `1 ∈ ℤ̂` acts on the whole algebraic Galois
extension by the actual arithmetic Frobenius. -/
@[simp]
theorem residueAbsoluteFrobenius_one :
    residueAbsoluteFrobenius k Omega
        (Multiplicative.ofAdd (1 : ZHat)) =
      FiniteField.frobeniusAlgEquivOfAlgebraic k Omega := by
  apply (InfiniteGalois.continuousMulEquivToLimit k Omega).injective
  apply Subtype.ext
  funext E
  change AlgEquiv.restrictNormalHom E.unop
      (residueAbsoluteFrobenius k Omega
        (Multiplicative.ofAdd (1 : ZHat))) =
    AlgEquiv.restrictNormalHom E.unop
      (FiniteField.frobeniusAlgEquivOfAlgebraic k Omega)
  rw [restrictNormalHom_residueAbsoluteFrobenius_one,
    restrictNormalHom_frobeniusAlgEquivOfAlgebraic]

end
end LocalClassFieldTheory
end

section
-- module Solutions.OAIQ244_DUKE.LocalClassFieldTheory_Finite_LocalReciprocity_ResidueAlgebraicClosureDegree
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.LocalClassFieldTheory.finiteGaloisFieldRangeOfEmbedding_finiteDimensional _root_.LocalClassFieldTheory.finiteGaloisFieldRangeOfEmbedding_isGalois _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionFixedSubring.instIsLocalRing _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionResidueExtension_normal _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionResidueField.instField _root_.RamificationTheory.HilbertRamification.ValuationSubring.selectedResidueField.instAlgebra _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.RelativeIdeleGroup.relativeIdeleMulAction _root_.LocalClassFieldTheory.intrinsicAbsoluteGaloisT2 _root_.adicCompletionProperSpace _root_.cyclicPrimeSubextension_isGalois _root_.finiteNormalClosure_isGalois _root_.relativeAdeleRingIntermediateAlgebra _root_.relativeAdeleRingTopIntermediateAlgebra
attribute [-simp] _root_.ClassFormation.DegreeData.extensionNormalizedDegreeContinuous_apply _root_.ClassFormation.DegreeData.extensionNormalizedDegreeContinuous_toMonoidHom _root_.ClassFormation.DegreeData.extensionNormalizedDegree_mk _root_.ClassFormation.DegreeData.fieldImageAdd_index _root_.ClassFormation.DegreeData.maximalUnramifiedDegreeEquiv_frobenius _root_.ClassFormation.DegreeData.maximalUnramifiedDegreeEquiv_mk _root_.ClassFormation.DegreeData.mem_maximalUnramifiedField_iff _root_.ClassFormation.DegreeData.normalizedDegree_apply_toAdd _root_.ClassFormation.DegreeData.restrictedDegreeInMulNatRange_coe _root_.ClassFormation.ValuationData.mem_unitAddSubgroup_iff _root_.ClassFormation.ValuationData.oneValue_coe _root_.ClassFormation.ValuationData.valuationAt_chosenPrimeElement _root_.ClassFormation.ValuationData.valuationAt_coe _root_.ClassFormation.ValuationData.valueModulo_apply _root_.ClassFormation.canonicalValueQuotientMap_mk _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.ClassFormation.mem_nsmulImage_iff _root_.ClassFormation.nsmulImage_top _root_.ClassFormation.zHatPowNat_apply_toAdd _root_.ClassFormation.zHatPowNat_one _root_.ClassFormation.zHatReductionMul_apply_toAdd _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.LocalFieldTheory.residueField_algebraMap_residue
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

namespace LocalClassFieldTheory

open ClassFormation

/-!
# Finite local reciprocity: degree coordinates on any residue algebraic closure

The residue field obtained from a valuation ring in a separable closure is
not definitionally Mathlib's chosen `AlgebraicClosure`.  The construction of
the degree map must therefore work on any algebraically closed algebraic
extension of the finite residue field.

This file repeats the inverse-limit detection argument in that intrinsic
setting.  The resulting map is the inverse of the canonical arithmetic
Frobenius homomorphism itself; no equivalence with a chosen algebraic closure
and no generator of a finite cyclic group enters its definition.
-/

noncomputable section

universe u v

open CategoryTheory Opposite
open FiniteGaloisIntermediateField ProfiniteGrp
open RamificationTheory.Field.absoluteGaloisGroup
open Polynomial

variable (k : Type u) [Field k] [Fintype k]
variable (Omega : Type v) [Field Omega] [Algebra k Omega]
  [Algebra.IsAlgebraic k Omega] [IsAlgClosed Omega]

/-- Finite subextensions of every positive degree detect every coordinate of
the canonical Frobenius homomorphism on an arbitrary residue algebraic
closure. -/
theorem residueAbsoluteFrobenius_isAlgClosure_injective :
    Function.Injective (residueAbsoluteFrobenius k Omega) := by
  intro z w hzw
  apply Multiplicative.ext
  apply ZHat.ext
  intro n hn
  let : NeZero n := ⟨Nat.ne_of_gt hn⟩
  let E := finiteResidueGaloisIntermediateFieldIn k Omega n
  have hrestriction := congrArg (AlgEquiv.restrictNormalHom E) hzw
  rw [restrictNormalHom_residueAbsoluteFrobenius (z := z) (E := E),
    restrictNormalHom_residueAbsoluteFrobenius (z := w) (E := E)] at hrestriction
  let : Finite E := Module.finite_of_finite k
  change finiteResidueFrobeniusFromZHat k E z =
    finiteResidueFrobeniusFromZHat k E w at hrestriction
  rw [finiteResidueFrobeniusFromZHat_apply,
    finiteResidueFrobeniusFromZHat_apply] at hrestriction
  have hcoordinate := congrArg Multiplicative.toAdd
    (finiteResidueFrobeniusExponentHom_injective k E hrestriction)
  have hdegree : Module.finrank k E = n := by
    exact finrank_finiteResidueGaloisIntermediateFieldIn
      k Omega n
  simp only [toAdd_ofAdd] at hcoordinate
  change zHatReduction (Module.finrank k E) Module.finrank_pos z.toAdd =
    zHatReduction (Module.finrank k E) Module.finrank_pos w.toAdd at hcoordinate
  have hdiv : n ∣ Module.finrank k E := by simp [hdegree]
  have hcast := congrArg (ZMod.castHom hdiv (ZMod n)) hcoordinate
  rw [zHatReduction_transition hn Module.finrank_pos hdiv z.toAdd,
    zHatReduction_transition hn Module.finrank_pos hdiv w.toAdd] at hcast
  exact hcast

/-- The compact image of the intrinsic Frobenius homomorphism. -/
noncomputable def residueAbsoluteFrobeniusRangeIn :
    ClosedSubgroup (Omega ≃ₐ[k] Omega) where
  toSubgroup := (residueAbsoluteFrobenius k Omega).toMonoidHom.range
  isClosed' := by
    change IsClosed (Set.range (residueAbsoluteFrobenius k Omega))
    exact (isCompact_range
      (residueAbsoluteFrobenius k Omega).continuous_toFun).isClosed

/-- The compact Frobenius image fixes precisely the finite base field. -/
theorem fixedField_residueAbsoluteFrobeniusRangeIn :
    IntermediateField.fixedField
        (residueAbsoluteFrobeniusRangeIn k Omega).toSubgroup = ⊥ := by
  apply le_antisymm
  · intro x hx
    have hfrobenius_mem :
        FiniteField.frobeniusAlgEquivOfAlgebraic k Omega ∈
          residueAbsoluteFrobeniusRangeIn k Omega := by
      change FiniteField.frobeniusAlgEquivOfAlgebraic k Omega ∈
        (residueAbsoluteFrobenius k Omega).toMonoidHom.range
      exact ⟨Multiplicative.ofAdd (1 : ZHat),
        residueAbsoluteFrobenius_one k Omega⟩
    rw [IntermediateField.mem_fixedField_iff] at hx
    have hxFrobenius := hx
      (FiniteField.frobeniusAlgEquivOfAlgebraic k Omega)
      hfrobenius_mem
    rw [IntermediateField.mem_bot]
    exact (mem_range_algebraMap_iff_frobenius_fixed_in k Omega x).mpr
      hxFrobenius
  · exact bot_le

/-- The intrinsic Frobenius image is the whole residue absolute Galois group. -/
theorem residueAbsoluteFrobeniusRangeIn_eq_top :
    (residueAbsoluteFrobeniusRangeIn k Omega).toSubgroup = ⊤ := by
  have hfixed := InfiniteGalois.fixingSubgroup_fixedField
    (residueAbsoluteFrobeniusRangeIn k Omega)
  rw [fixedField_residueAbsoluteFrobeniusRangeIn,
    IntermediateField.fixingSubgroup_bot] at hfixed
  exact hfixed.symm

/-- The intrinsic Frobenius homomorphism is surjective. -/
theorem residueAbsoluteFrobenius_isAlgClosure_surjective :
    Function.Surjective (residueAbsoluteFrobenius k Omega) := by
  intro sigma
  have hsigma : sigma ∈
      (residueAbsoluteFrobeniusRangeIn k Omega).toSubgroup := by
    rw [residueAbsoluteFrobeniusRangeIn_eq_top]
    exact Subgroup.mem_top sigma
  exact hsigma

/-- Arithmetic Frobenius gives the canonical topological equivalence between
`ZHatMul` and the Galois group of any algebraic closure of a finite field. -/
noncomputable def residueAbsoluteFrobeniusEquivIn :
    ZHatMul ≃ₜ* (Omega ≃ₐ[k] Omega) where
  toMulEquiv := MulEquiv.ofBijective
    (residueAbsoluteFrobenius k Omega).toMonoidHom
    ⟨residueAbsoluteFrobenius_isAlgClosure_injective k Omega,
      residueAbsoluteFrobenius_isAlgClosure_surjective k Omega⟩
  continuous_toFun := (residueAbsoluteFrobenius k Omega).continuous_toFun
  continuous_invFun :=
    Continuous.continuous_symm_of_equiv_compact_to_t2
      (f := (MulEquiv.ofBijective
        (residueAbsoluteFrobenius k Omega).toMonoidHom
        ⟨residueAbsoluteFrobenius_isAlgClosure_injective k Omega,
          residueAbsoluteFrobenius_isAlgClosure_surjective k Omega⟩).toEquiv)
      (residueAbsoluteFrobenius k Omega).continuous_toFun

/-- **Finite local reciprocity, intrinsic residue degree.**  This is the inverse of
arithmetic Frobenius coordinates on the actual residue algebraic closure. -/
noncomputable def residueAbsoluteDegreeIn :
    (Omega ≃ₐ[k] Omega) →ₜ* ZHatMul :=
  ContinuousMonoidHom.toContinuousMonoidHom
    (residueAbsoluteFrobeniusEquivIn k Omega).symm

/-- The intrinsic degree map sends arithmetic Frobenius to `1`. -/
@[simp]
theorem residueAbsoluteDegreeIn_frobenius :
    residueAbsoluteDegreeIn k Omega
        (FiniteField.frobeniusAlgEquivOfAlgebraic k Omega) =
      Multiplicative.ofAdd (1 : ZHat) := by
  apply (residueAbsoluteFrobeniusEquivIn k Omega).injective
  change (residueAbsoluteFrobeniusEquivIn k Omega)
      ((residueAbsoluteFrobeniusEquivIn k Omega).symm
        (FiniteField.frobeniusAlgEquivOfAlgebraic k Omega)) =
    (residueAbsoluteFrobeniusEquivIn k Omega)
      (Multiplicative.ofAdd (1 : ZHat))
  rw [(residueAbsoluteFrobeniusEquivIn k Omega).apply_symm_apply]
  exact (residueAbsoluteFrobenius_one k Omega).symm

/-- Finite-coordinate compatibility for the intrinsic residue degree. -/
theorem finiteResidueFrobeniusExponentEquiv_symm_restrict_in
    (sigma : Omega ≃ₐ[k] Omega)
    (E : FiniteGaloisIntermediateField k Omega) :
    letI : Finite E := Module.finite_of_finite k
    (finiteResidueFrobeniusExponentEquiv k E).symm
        (AlgEquiv.restrictNormalHom E sigma) =
      Multiplicative.ofAdd
        (zHatReduction (Module.finrank k E) Module.finrank_pos
          (residueAbsoluteDegreeIn k Omega sigma).toAdd) := by
  let : Finite E := Module.finite_of_finite k
  apply (finiteResidueFrobeniusExponentEquiv k E).injective
  rw [(finiteResidueFrobeniusExponentEquiv k E).apply_symm_apply]
  change AlgEquiv.restrictNormalHom E sigma =
    finiteResidueFrobeniusIntermediate k Omega E
      (residueAbsoluteDegreeIn k Omega sigma)
  rw [← restrictNormalHom_residueAbsoluteFrobenius]
  congr 1
  exact ((residueAbsoluteFrobeniusEquivIn k Omega).apply_symm_apply sigma).symm

end
end LocalClassFieldTheory
end

section
-- module Solutions.OAIQ244_DUKE.LocalClassFieldTheory_Finite_LocalReciprocity_ResidueDatum
attribute [-instance] _root_.ClassFormation.DegreeData.extensionInertiaWithin_normal _root_.ClassFormation.DegreeData.frobeniusClosure_isTopologicalGroup _root_.ClassFormation.DegreeData.maximalUnramifiedNormQuotientAddCommGroup _root_.ClassFormation.FiniteUnramifiedCyclicExtension.instFiniteQuotientSubtypeMemSubgroupFieldExtensionSubgroupField _root_.ClassFormation.FiniteUnramifiedCyclicExtension.instFintypeQuotientSubtypeMemSubgroupFieldExtensionSubgroupField _root_.ClassFormation.FiniteUnramifiedCyclicExtension.instNormalSubtypeMemSubgroupFieldExtensionSubgroupField _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.LocalClassFieldTheory.baseFixingExtensionQuotient_finite _root_.LocalClassFieldTheory.closedFixingSubgroup_normal _root_.LocalClassFieldTheory.extensionSubgroupBase_normal _root_.LocalClassFieldTheory.finiteGaloisExtensionSubgroupOfEmbedding_normal _root_.LocalClassFieldTheory.finiteGaloisFieldRangeOfEmbedding_finiteDimensional _root_.LocalClassFieldTheory.finiteGaloisFieldRangeOfEmbedding_isGalois _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.LubinTate.compatibleGroupFamiliesGroup _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionFixedSubring.instIsLocalRing _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionResidueExtension_normal _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionResidueField.instField _root_.RamificationTheory.HilbertRamification.ValuationSubring.selectedResidueField.instAlgebra _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.RelativeIdeleGroup.relativeIdeleMulAction _root_.adicCompletionProperSpace _root_.cyclicPrimeSubextension_isGalois _root_.finiteNormalClosure_isGalois _root_.relativeAdeleRingIntermediateAlgebra _root_.relativeAdeleRingTopIntermediateAlgebra
attribute [-simp] _root_.ClassFormation.DegreeData.extensionNormalizedDegreeContinuous_apply _root_.ClassFormation.DegreeData.extensionNormalizedDegreeContinuous_toMonoidHom _root_.ClassFormation.DegreeData.extensionNormalizedDegree_mk _root_.ClassFormation.DegreeData.fieldImageAdd_index _root_.ClassFormation.DegreeData.maximalUnramifiedDegreeEquiv_frobenius _root_.ClassFormation.DegreeData.maximalUnramifiedDegreeEquiv_mk _root_.ClassFormation.DegreeData.mem_maximalUnramifiedField_iff _root_.ClassFormation.DegreeData.normalizedDegree_apply_toAdd _root_.ClassFormation.DegreeData.restrictedDegreeInMulNatRange_coe _root_.ClassFormation.ValuationData.mem_unitAddSubgroup_iff _root_.ClassFormation.ValuationData.oneValue_coe _root_.ClassFormation.ValuationData.valuationAt_chosenPrimeElement _root_.ClassFormation.ValuationData.valuationAt_coe _root_.ClassFormation.ValuationData.valueModulo_apply _root_.ClassFormation.canonicalValueQuotientMap_mk _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.ClassFormation.mem_nsmulImage_iff _root_.ClassFormation.nsmulImage_top _root_.ClassFormation.zHatPowNat_apply_toAdd _root_.ClassFormation.zHatPowNat_one _root_.ClassFormation.zHatReductionMul_apply_toAdd _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.LocalClassFieldTheory.baseFixingExtensionQuotientEquivAmbient_mk _root_.LocalClassFieldTheory.baseUnitsEquivGaloisAmbientFixed_val _root_.LocalClassFieldTheory.embeddedFieldUnitsEquivGaloisFixed_coe _root_.LocalClassFieldTheory.intermediateFieldUnitsEquivGaloisFixed_coe _root_.LocalFieldTheory.residueField_algebraMap_residue
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

namespace LocalClassFieldTheory
open RamificationTheory

open ClassFormation

/-!
# Finite local reciprocity: the residue datum and its finite indices

The arithmetic-Frobenius degree on an algebraic closure of a finite field is
packaged as the initial datum of the abstract class-formation framework.  For every finite residue
subextension, the image of its fixing subgroup is proved to be exactly
`n ℤ̂`; consequently the abstract residue degree is the ordinary field
degree.  This is the finite-coordinate comparison needed in the local-field
specialization.
-/

noncomputable section

variable (k Omega : Type)
  [Field k] [Fintype k] [Field Omega] [Algebra k Omega]
  [Algebra.IsAlgebraic k Omega] [IsAlgClosed Omega]

/-- The abstract class-formation datum supplied by arithmetic Frobenius on the actual
residue algebraic closure. -/
noncomputable def residueDatumIn : DegreeData (Omega ≃ₐ[k] Omega) where
  degree := residueAbsoluteDegreeIn k Omega
  degree_surjective := (residueAbsoluteFrobeniusEquivIn k Omega).symm.surjective

/-- The degree image of the subgroup fixing a finite residue extension of
degree `n` is exactly `n ℤ̂`. -/
theorem residueDatumIn_fieldImage_closedFixingSubgroup
    (E : FiniteGaloisIntermediateField k Omega) :
    (residueDatumIn k Omega).fieldImage
        (closedFixingSubgroup k Omega E) =
      (zHatMulNat (Module.finrank k E)).toAddMonoidHom.range.toSubgroup := by
  ext z
  let : Finite E := Module.finite_of_finite k
  constructor
  · rintro ⟨sigma, rfl⟩
    change (residueAbsoluteDegreeIn k Omega sigma.1).toAdd ∈
      (zHatMulNat (Module.finrank k E)).toAddMonoidHom.range
    rw [zHatMulNat_range_eq_ker_reduction
      (Module.finrank k E) Module.finrank_pos]
    change zHatReduction (Module.finrank k E) Module.finrank_pos
      (residueAbsoluteDegreeIn k Omega sigma.1).toAdd = 0
    have hrestrict : AlgEquiv.restrictNormalHom E sigma.1 = 1 :=
      (mem_fixingSubgroup_iff_restrictNormalHom_eq_one
        k Omega E sigma.1).1 sigma.2
    have hcoordinate :=
      finiteResidueFrobeniusExponentEquiv_symm_restrict_in
        k Omega sigma.1 E
    rw [hrestrict, map_one] at hcoordinate
    exact congrArg Multiplicative.toAdd hcoordinate |>.symm
  · intro hz
    change z.toAdd ∈
      (zHatMulNat (Module.finrank k E)).toAddMonoidHom.range at hz
    rw [zHatMulNat_range_eq_ker_reduction
      (Module.finrank k E) Module.finrank_pos] at hz
    refine ⟨⟨residueAbsoluteFrobenius k Omega z, ?_⟩, ?_⟩
    · apply (mem_fixingSubgroup_iff_restrictNormalHom_eq_one
        k Omega E (residueAbsoluteFrobenius k Omega z)).2
      rw [restrictNormalHom_residueAbsoluteFrobenius]
      change finiteResidueFrobeniusFromZHat k E z = 1
      rw [finiteResidueFrobeniusFromZHat_apply]
      change finiteResidueFrobeniusExponentHom k E
        (Multiplicative.ofAdd
          (zHatReduction (Module.finrank k E) Module.finrank_pos z.toAdd)) = 1
      rw [show zHatReduction (Module.finrank k E) Module.finrank_pos z.toAdd = 0
        from hz]
      simp
    · exact (residueAbsoluteFrobeniusEquivIn k Omega).symm_apply_apply z

/-- Internal finite-coordinate calculation: the degree image of the fixing
subgroup has natural index equal to the ordinary residue-field degree.  Public
residue-degree APIs use `Cardinal` or a finite residue-field bundle. -/
theorem Internal.residueDatumIn_fieldImage_index_closedFixingSubgroup
    (E : FiniteGaloisIntermediateField k Omega) :
    ((residueDatumIn k Omega).fieldImage
        (closedFixingSubgroup k Omega E)).index = Module.finrank k E := by
  rw [residueDatumIn_fieldImage_closedFixingSubgroup k Omega E,
    AddSubgroup.index_toSubgroup]
  exact zHatMulNat_range_index (Module.finrank k E) Module.finrank_pos

end
end LocalClassFieldTheory
end

section
-- module Solutions.OAIQ244_DUKE.LocalClassFieldTheory_Finite_LocalReciprocity_ResidueActionIndex
attribute [-instance] _root_.ClassFormation.DegreeData.extensionInertiaWithin_normal _root_.ClassFormation.DegreeData.frobeniusClosure_isTopologicalGroup _root_.ClassFormation.DegreeData.maximalUnramifiedNormQuotientAddCommGroup _root_.ClassFormation.FiniteUnramifiedCyclicExtension.instFiniteQuotientSubtypeMemSubgroupFieldExtensionSubgroupField _root_.ClassFormation.FiniteUnramifiedCyclicExtension.instFintypeQuotientSubtypeMemSubgroupFieldExtensionSubgroupField _root_.ClassFormation.FiniteUnramifiedCyclicExtension.instNormalSubtypeMemSubgroupFieldExtensionSubgroupField _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.LocalClassFieldTheory.baseFixingExtensionQuotient_finite _root_.LocalClassFieldTheory.closedFixingSubgroup_normal _root_.LocalClassFieldTheory.extensionSubgroupBase_normal _root_.LocalClassFieldTheory.finiteGaloisExtensionSubgroupOfEmbedding_normal _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.RelativeIdeleGroup.relativeIdeleMulAction _root_.adicCompletionProperSpace
attribute [-simp] _root_.ClassFormation.DegreeData.extensionNormalizedDegreeContinuous_apply _root_.ClassFormation.DegreeData.extensionNormalizedDegreeContinuous_toMonoidHom _root_.ClassFormation.DegreeData.extensionNormalizedDegree_mk _root_.ClassFormation.DegreeData.extensionRestriction_mk _root_.ClassFormation.DegreeData.fieldImageAdd_index _root_.ClassFormation.DegreeData.maximalUnramifiedDegreeEquiv_frobenius _root_.ClassFormation.DegreeData.maximalUnramifiedDegreeEquiv_mk _root_.ClassFormation.DegreeData.maximalUnramifiedNormClass_eq_zero_iff _root_.ClassFormation.DegreeData.maximalUnramifiedNormQuotientInfiniteEquiv_maximalUnramifiedNormClass _root_.ClassFormation.DegreeData.maximalUnramifiedNormQuotientLift_maximalUnramifiedNormClass _root_.ClassFormation.DegreeData.maximalUnramifiedRestriction_mk _root_.ClassFormation.DegreeData.maximalUnramifiedToFiniteNormQuotient_maximalUnramifiedNormClass _root_.ClassFormation.DegreeData.mem_maximalUnramifiedField_iff _root_.ClassFormation.DegreeData.mem_maximalUnramifiedNormSubgroup_iff _root_.ClassFormation.DegreeData.normalizedDegree_apply_toAdd _root_.ClassFormation.DegreeData.restrictedDegreeInMulNatRange_coe _root_.ClassFormation.FiniteGaloisSubextension.toGaloisSubextension_isTotallyRamified_iff _root_.ClassFormation.FiniteGaloisSubextension.toGaloisSubextension_isUnramified_iff _root_.ClassFormation.ValuationData.mem_unitAddSubgroup_iff _root_.ClassFormation.ValuationData.oneValue_coe _root_.ClassFormation.ValuationData.unitRepresentation_quotient_mk_apply _root_.ClassFormation.ValuationData.valuationAt_chosenPrimeElement _root_.ClassFormation.ValuationData.valuationAt_coe _root_.ClassFormation.ValuationData.valueModulo_apply _root_.ClassFormation.canonicalValueQuotientMap_mk _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.ClassFormation.mem_nsmulImage_iff _root_.ClassFormation.nsmulImage_top _root_.ClassFormation.zHatPowNat_apply_toAdd _root_.ClassFormation.zHatPowNat_one _root_.ClassFormation.zHatReductionMul_apply_toAdd _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.LocalClassFieldTheory.baseFixingExtensionQuotientEquivAmbient_mk _root_.LocalClassFieldTheory.baseUnitsEquivGaloisAmbientFixed_val _root_.LocalClassFieldTheory.embeddedFieldUnitsEquivGaloisFixed_coe _root_.LocalClassFieldTheory.intermediateFieldUnitsEquivGaloisFixed_coe _root_.LocalFieldTheory.residueField_algebraMap_residue
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

namespace LocalClassFieldTheory

open RamificationTheory

open ClassFormation

/-!
# Finite local reciprocity: residue-action image indices

This file separates the two group-theoretic comparisons used by the local
degree map.  The residue-action exact-sequence theorem supplies the actual action of an absolute
decomposition group on the selected residue algebraic closure.  Once the
decomposition group is all of the absolute Galois group, that action is
surjective.  If a finite-index subgroup has residue-action image equal to the
fixing group of a finite residue subextension, its degree image has the
ordinary residue-field index.
-/

noncomputable section

universe u v

open _root_.RamificationTheory.HilbertRamification.ValuationSubring

variable (K : Type u) {L : Type v} [Field K] [Field L] [Algebra K L]
  [IsGalois K L]

section FiniteImageIndex

variable (k Omega : Type)
  [Field k] [Fintype k] [Field Omega] [Algebra k Omega]
  [Algebra.IsAlgebraic k Omega] [IsAlgClosed Omega]

/-- Finite-subgroup coordinate/index comparison.  If the residue action of a
subgroup is precisely the subgroup fixing a finite residue field `E`, then
the image of the composite degree map has index `[E:k]`. -/
theorem residueDegreeImage_index_eq_finrank_of_map_eq_fixingSubgroup
    {G : Type*} [Group G]
    (rho : G →* (Omega ≃ₐ[k] Omega))
    (H : Subgroup G)
    (E : FiniteGaloisIntermediateField k Omega)
    (himage : H.map rho = E.toIntermediateField.fixingSubgroup) :
    (H.map ((residueAbsoluteDegreeIn k Omega).toMonoidHom.comp rho)).index =
      Module.finrank k E := by
  rw [← Subgroup.map_map, himage]
  have h :=
    Internal.residueDatumIn_fieldImage_index_closedFixingSubgroup k Omega E
  rw [(residueDatumIn k Omega).fieldImage_eq_map] at h
  simpa [residueDatumIn, closedFixingSubgroup] using h

end FiniteImageIndex

end
end LocalClassFieldTheory
end

section
-- module Solutions.OAIQ244_DUKE.Kummer_Concrete_RootCharacters
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.KummerTheory.RadicalDatum.radicalQuotient_commGroupInstance _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.RelativeIdeleGroup.relativeIdeleMulAction _root_.CyclicCohomology.instMulDistribMulActionBinaryCoefficientFamily _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.adicCompletionProperSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

/-!
# Root characters for Kummer theory

Support API for root-quotient constructions in concrete Kummer extensions.
-/

namespace KummerTheory

open groupCohomology

section RootQuotients

variable {K L : Type*} [Field K] [Field L] [Algebra K L]

/-- If `β ^ n` is fixed by Galois, then the root-quotient lands in `μₙ(L)`. -/
theorem rootQuotient_mem_nthRootsSubgroup_of_pow_fixed
    {n : ℕ} {β : Lˣ} (hβ : ∀ σ : Gal(L/K), σ • (β ^ n) = β ^ n)
    (σ : Gal(L/K)) :
    rootQuotient (K := K) (L := L) β σ ∈ nthRootsSubgroup L n := by
  rw [mem_nthRootsSubgroup_iff]
  exact rootQuotient_pow_eq_one_of_pow_fixed (K := K) (L := L) hβ σ

end RootQuotients

section RadicalData

variable {K L : Type*} [Field K] [Field L] [Algebra K L]

namespace RadicalDatum

variable {n : ℕ+} (D : RadicalDatum (K := K) (L := L) n)

/-- The canonical character agrees with any root quotient having the same `n`-th power. -/
theorem rootCharacter_eq_of_same_pow
    (hfixed : ∀ σ : Gal(L/K), ∀ u : Lˣ, u ^ (n : ℕ) = 1 → σ • u = u)
    {u : Lˣ} (a : D.carrier)
    (hu : u ^ (n : ℕ) = Units.map (algebraMap K L).toMonoidHom a.1)
    (σ : Gal(L/K)) :
    rootQuotient (K := K) (L := L) u σ = D.rootCharacter a hfixed σ := by
  rw [D.rootCharacter_apply]
  exact D.rootQuotient_eq_rootCocycle_of_same_pow hfixed a hu σ

end RadicalDatum
end RadicalData

end KummerTheory
end

section
-- module Solutions.OAIQ244_DUKE.Kummer_Concrete_RadicalQuotient
attribute [-instance] _root_.ClassFormation.DegreeData.GaloisSubextension.extensionSubgroup_normalInstance _root_.ClassFormation.FiniteCyclicSubextension.instNormalSubtypeMemSubgroupFieldExtensionSubgroupField _root_.ClassFormation.FiniteGaloisSubextension.extensionSubgroup_normalInstance _root_.ClassFormation.FiniteGaloisSubextension.extensionSubgroup_over_intermediate_normalInstance _root_.ClassFormation.FiniteGaloisSubextension.intermediateField_normalInstance _root_.ClassFormation.FiniteUnramifiedCyclicExtension.instNormalSubtypeMemSubgroupFieldExtensionSubgroupField _root_.ClassFormation.conjugateExtension_normal _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.LocalClassFieldTheory.extensionSubgroupBase_normal _root_.LocalClassFieldTheory.finiteGaloisExtensionSubgroupOfEmbedding_normal _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.LubinTate.compatibleGroupFamiliesCommGroup _root_.LubinTate.compatibleGroupFamiliesGroup _root_.RamificationTheory.HilbertRamification.ValuationSubring.inertiaGroup_normal _root_.RamificationTheory.HilbertRamification.ValuationSubring.ramificationGroupInInertiaAut_normal _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.RelativeIdeleGroup.relativeIdeleMulAction _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.CyclicCohomology.binaryCoefficientFamilyCommGroup _root_.CyclicCohomology.instMulDistribMulActionBinaryCoefficientFamily _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.adicCompletionProperSpace
attribute [-simp] _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.KummerTheory.characterToNthRoots_apply _root_.KummerTheory.restrictedKummerTranspose_apply _root_.KummerTheory.restrictedQuotientKummerCharacter_mk _root_.LocalFieldTheory.residueField_algebraMap_residue
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

/-!
# Ambient radical quotients

Source lemmas for the quotient on the radical side of the Kummer pairing in
Concrete Kummer radical quotients.  Unlike `MultiplicativeRadicalDatum`, this construction starts
with an arbitrary choice of roots.  The hypothesis that `μₙ(L)` is fixed by
Galois makes the resulting root characters independent of that choice.

The denominator is the subgroup of elements of `D.carrier` which are `n`-th
powers in the ambient group `Kˣ`, in the ambient group, rather than the generally
smaller subgroup of `n`-th powers of elements of `D.carrier`.
-/

namespace KummerTheory

section RadicalQuotient

variable {K L : Type*} [Field K] [Field L] [Algebra K L]

namespace RadicalDatum

variable {n : ℕ+} (D : RadicalDatum (K := K) (L := L) n)

/-- Every ambient radical class has a representative in `D.carrier`. -/
theorem radicalQuotientMk_surjective :
    Function.Surjective D.radicalQuotientMk := by
  change Function.Surjective
    (QuotientGroup.mk' D.ambientNthPowersSubgroup)
  exact QuotientGroup.mk'_surjective D.ambientNthPowersSubgroup

/-- Eliminate a named ambient radical quotient through its canonical
representatives. -/
protected theorem radicalQuotient_inductionOn
    {motive : D.RadicalQuotient → Prop} (q : D.RadicalQuotient)
    (mk : ∀ a : D.carrier, motive (D.radicalQuotientMk a)) :
    motive q := by
  exact QuotientGroup.induction_on' q mk

/-- The character map on the ambient radical quotient is injective.  This is
the kernel half of the canonical isomorphism in the finite Kummer character equivalence. -/
theorem quotientKummerCharacterWithoutSection_injective
    [IsGalois K L]
    (hfixed : ∀ σ : Gal(L/K), ∀ u : Lˣ, u ^ (n : ℕ) = 1 → σ • u = u) :
    Function.Injective (D.quotientKummerCharacterWithoutSection hfixed) := by
  intro q
  refine D.radicalQuotient_inductionOn
    (motive := fun q => ∀ r,
      D.quotientKummerCharacterWithoutSection hfixed q =
          D.quotientKummerCharacterWithoutSection hfixed r →
        q = r)
    q ?_
  intro a r
  refine D.radicalQuotient_inductionOn
    (motive := fun r =>
      D.quotientKummerCharacterWithoutSection hfixed
          (D.radicalQuotientMk a) =
          D.quotientKummerCharacterWithoutSection hfixed r →
        D.radicalQuotientMk a = r)
    r ?_
  intro b hab
  apply (D.radicalQuotientMk_eq_iff a b).2
  rw [← D.ker_kummerCharacterWithoutSection_eq_ambientNthPowers hfixed]
  have hab' : D.kummerCharacterWithoutSection hfixed a =
      D.kummerCharacterWithoutSection hfixed b := by
    simpa using hab
  rw [MonoidHom.mem_ker, map_div, hab']
  exact div_self' (D.kummerCharacterWithoutSection hfixed b)

end RadicalDatum
end RadicalQuotient

end KummerTheory
end

section
-- module Solutions.OAIQ244_DUKE.Kummer_Concrete_FiniteCharacterEquiv
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.LubinTate.compatibleGroupFamiliesCommGroup _root_.LubinTate.compatibleGroupFamiliesGroup _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.RelativeIdeleGroup.relativeIdeleMulAction _root_.ValuationTheory.DiscreteValuationField.DVF.maximalIdealPowSuccQuotModule _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.isLocalRing _root_.CyclicCohomology.binaryCoefficientFamilyCommGroup _root_.CyclicCohomology.instMulDistribMulActionBinaryCoefficientFamily _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.adicCompletionProperSpace
attribute [-simp] _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.KummerTheory.characterToNthRoots_apply _root_.KummerTheory.restrictedKummerTranspose_apply _root_.KummerTheory.restrictedQuotientKummerCharacter_mk _root_.LocalFieldTheory.residueField_algebraMap_residue
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

/-!
# finite Kummer character isomorphism

For an actual finite Galois extension `L/K`, this file constructs

`Delta = {a : Kˣ | there is beta : Lˣ with beta ^ n = a}`

as a subgroup, chooses one root for each element only after the subgroup has
been constructed, and proves the character isomorphism

`Delta / (Delta intersect Kˣ^n) ~= Hom(Gal(L/K), mu_n)`.

There is no multiplicative choice of roots.  Surjectivity is produced by
Noether's Hilbert theorem 90.  This is the finite actual-field character-
isomorphism half of The finite Kummer character equivalence; it does not assert the full
lattice correspondence between radical subgroups and abelian extensions.
-/

noncomputable section

namespace KummerTheory

section FiniteKummerCharacterIso

variable {K L : Type*} [Field K] [Field L] [Algebra K L]

/-- The root-choice-free Kummer character on the ambient-power quotient is
surjective.  The preimage of a character is produced by Noether Hilbert 90,
not supplied as a hypothesis. -/
theorem finiteKummerQuotientCharacter_surjective
    [FiniteDimensional K L] [IsGalois K L]
    (n : ℕ+) (hmu : NthRootsOfUnityInBase (K := K) (L := L) n) :
    Function.Surjective
      ((chosenFiniteKummerRadicalDatum (K := K) (L := L) n).quotientKummerCharacterWithoutSection
          (nthRootsOfUnity_fixed (K := K) (L := L) n hmu)) := by
  let D := chosenFiniteKummerRadicalDatum (K := K) (L := L) n
  let hfixed : ∀ sigma : Gal(L/K), ∀ u : Lˣ,
      u ^ (n : ℕ) = 1 → sigma • u = u :=
    nthRootsOfUnity_fixed (K := K) (L := L) n hmu
  intro chi
  let f : Gal(L/K) → Lˣ := fun sigma => (chi sigma).1
  have hf : groupCohomology.IsMulCocycle₁ f := by
    intro sigma tau
    change (chi (sigma * tau)).1 = sigma • (chi tau).1 * (chi sigma).1
    rw [map_mul, hfixed sigma (chi tau).1 (chi tau).2, mul_comm]
    rfl
  obtain ⟨beta, hbeta_div⟩ :=
    groupCohomology.isMulCoboundary₁_of_isMulCocycle₁_of_aut_to_units f hf
  have hbeta : ∀ sigma : Gal(L/K), sigma • beta = f sigma * beta := by
    intro sigma
    rw [← hbeta_div sigma]
    exact (div_mul_cancel (sigma • beta) beta).symm
  have hbeta_pow_fixed : ∀ sigma : Gal(L/K),
      sigma • (beta ^ (n : ℕ)) = beta ^ (n : ℕ) := by
    intro sigma
    calc
      sigma • (beta ^ (n : ℕ)) = (sigma • beta) ^ (n : ℕ) := by
        exact map_pow (MulDistribMulAction.toMonoidHom Lˣ sigma) beta (n : ℕ)
      _ = (f sigma * beta) ^ (n : ℕ) := by rw [hbeta sigma]
      _ = (f sigma) ^ (n : ℕ) * beta ^ (n : ℕ) := mul_pow _ _ _
      _ = beta ^ (n : ℕ) := by
        rw [show (f sigma) ^ (n : ℕ) = 1 from (chi sigma).2, one_mul]
  have hbeta_pow_range : ((beta ^ (n : ℕ) : Lˣ) : L) ∈
      Set.range (algebraMap K L) := by
    apply (IsGalois.mem_range_algebraMap_iff_fixed
      (((beta ^ (n : ℕ) : Lˣ) : L))).2
    intro sigma
    exact congrArg Units.val (hbeta_pow_fixed sigma)
  obtain ⟨a, ha⟩ := hbeta_pow_range
  have ha_ne : a ≠ 0 := by
    intro ha_zero
    have : (((beta ^ (n : ℕ) : Lˣ) : L)) = 0 := by
      simpa [ha_zero] using ha.symm
    exact (beta ^ (n : ℕ)).ne_zero this
  let aunit : Kˣ := Units.mk0 a ha_ne
  have hbeta_pow : beta ^ (n : ℕ) =
      Units.map (algebraMap K L).toMonoidHom aunit := by
    apply Units.ext
    exact ha.symm
  let delta : D.carrier := ⟨aunit, beta, hbeta_pow⟩
  refine ⟨D.radicalQuotientMk delta, ?_⟩
  rw [D.quotientKummerCharacterWithoutSection_mk]
  apply MonoidHom.ext
  intro sigma
  apply Subtype.ext
  change D.rootCharacter delta hfixed sigma = (chi sigma).1
  rw [← D.rootCharacter_eq_of_same_pow hfixed delta hbeta_pow sigma]
  simp [rootQuotient, hbeta sigma, f]

/-- The finite actual-field Kummer character isomorphism on
`Delta / (Delta intersect Kˣ^n)`.  This is the character-isomorphism half of
the finite Kummer character equivalence, not the full subgroup/extension correspondence. -/
def finiteKummerCharacterEquiv
    [FiniteDimensional K L] [IsGalois K L]
    (n : ℕ+) (hmu : NthRootsOfUnityInBase (K := K) (L := L) n) :
    (chosenFiniteKummerRadicalDatum (K := K) (L := L) n).RadicalQuotient ≃*
      (Gal(L/K) →* nthRootsSubgroup L (n : ℕ)) :=
  MulEquiv.ofBijective
    ((chosenFiniteKummerRadicalDatum (K := K) (L := L) n).quotientKummerCharacterWithoutSection
        (nthRootsOfUnity_fixed (K := K) (L := L) n hmu))
    ⟨(chosenFiniteKummerRadicalDatum (K := K) (L := L) n).quotientKummerCharacterWithoutSection_injective
          (nthRootsOfUnity_fixed (K := K) (L := L) n hmu),
      finiteKummerQuotientCharacter_surjective (K := K) (L := L) n hmu⟩

end FiniteKummerCharacterIso

end KummerTheory
end
end

section
-- module Solutions.OAIQ244_DUKE.Kummer_Concrete_FiniteGeneration
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.LubinTate.compatibleGroupFamiliesCommGroup _root_.LubinTate.compatibleGroupFamiliesGroup _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.RelativeIdeleGroup.relativeIdeleMulAction _root_.ValuationTheory.DiscreteValuationField.DVF.maximalIdealPowSuccQuotModule _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.isLocalRing _root_.CyclicCohomology.binaryCoefficientFamilyCommGroup _root_.CyclicCohomology.instMulDistribMulActionBinaryCoefficientFamily _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.adicCompletionProperSpace
attribute [-simp] _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.KummerTheory.characterToNthRoots_apply _root_.KummerTheory.restrictedKummerTranspose_apply _root_.KummerTheory.restrictedQuotientKummerCharacter_mk _root_.LocalFieldTheory.residueField_algebraMap_residue
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

/-!
# finite actual-field form

Let `L/K` be a finite abelian Galois extension whose Galois group is killed by
`n`, and suppose that `K` contains a primitive `n`-th root of unity.  This file
proves that `L` is generated over `K` by all nonzero `beta : L` such that
`beta ^ n` belongs to `K`.

The proof uses finite-abelian character separation and the finite Kummer
character isomorphism.  It is the finite `n`-th-power, actual-field form of
the Kummer generation theorem; it is not the general abstract-module or infinite statement.
-/

noncomputable section

namespace KummerTheory

open scoped IsMulCommutative

section FiniteKummerGeneration

variable {K L : Type*} [Field K] [Field L] [Algebra K L]

/-- Finite actual-field version of The Kummer generation theorem.

An abelian Galois extension of exponent dividing `n`, over a field containing
the `n`-th roots of unity, is generated by the elements whose `n`-th powers
belong to the base field. -/
theorem finiteKummerRootSet_adjoin_eq_top
    [FiniteDimensional K L] [IsGalois K L] [IsMulCommutative Gal(L/K)]
    (n : ℕ+) (hmu : (primitiveRoots (n : ℕ) K).Nonempty)
    (hexponent : ∀ sigma : Gal(L/K), sigma ^ (n : ℕ) = 1) :
    IntermediateField.adjoin K (finiteKummerRootSet (K := K) (L := L) n) = ⊤ := by
  let D := chosenFiniteKummerRadicalDatum (K := K) (L := L) n
  let hbase : NthRootsOfUnityInBase (K := K) (L := L) n :=
    nthRootsOfUnityInBase_of_primitiveRoots (K := K) (L := L) n hmu
  let hfixed : ∀ sigma : Gal(L/K), ∀ u : Lˣ,
      u ^ (n : ℕ) = 1 → sigma • u = u :=
    nthRootsOfUnity_fixed (K := K) (L := L) n hbase
  let E : IntermediateField K L :=
    IntermediateField.adjoin K (finiteKummerRootSet (K := K) (L := L) n)
  apply IsGalois.intermediateFieldEquivSubgroup.injective
  rw [map_top, eq_top_iff]
  intro sigma hsigma
  have hsigma_eq_one : sigma = 1 := by
    by_contra hsigma_ne
    let : NeZero (n : ℕ) := ⟨n.ne_zero⟩
    obtain ⟨zeta, hzeta⟩ := hmu
    have hzeta_primitive : IsPrimitiveRoot zeta (n : ℕ) :=
      (mem_primitiveRoots n.pos).1 hzeta
    let : HasEnoughRootsOfUnity K (n : ℕ) :=
      { prim := ⟨zeta, hzeta_primitive⟩
        cyc := rootsOfUnity.isCyclic K (n : ℕ) }
    have hexponent_dvd : Monoid.exponent Gal(L/K) ∣ (n : ℕ) :=
      Monoid.exponent_dvd_of_forall_pow_eq_one (fun tau => by
        simpa only using hexponent tau)
    let : HasEnoughRootsOfUnity K (Monoid.exponent Gal(L/K)) :=
      HasEnoughRootsOfUnity.of_dvd K hexponent_dvd
    obtain ⟨phi, hphi⟩ :=
      CommGroup.exists_apply_ne_one_of_hasEnoughRootsOfUnity Gal(L/K) K hsigma_ne
    let chi : Gal(L/K) →* nthRootsSubgroup L (n : ℕ) :=
      { toFun := fun tau =>
          ⟨Units.map (algebraMap K L).toMonoidHom (phi tau), by
            calc
              (Units.map (algebraMap K L).toMonoidHom (phi tau)) ^ (n : ℕ) =
                  Units.map (algebraMap K L).toMonoidHom ((phi tau) ^ (n : ℕ)) :=
                (map_pow (Units.map (algebraMap K L).toMonoidHom)
                  (phi tau) (n : ℕ)).symm
              _ = Units.map (algebraMap K L).toMonoidHom (phi (tau ^ (n : ℕ))) := by
                exact congrArg (Units.map (algebraMap K L).toMonoidHom)
                  (map_pow phi tau (n : ℕ)).symm
              _ = 1 := by rw [hexponent tau, map_one, map_one]⟩
        map_one' := by
          apply Subtype.ext
          simp
        map_mul' := by
          intro sigma tau
          apply Subtype.ext
          simp }
    have hchi_sigma : chi sigma ≠ 1 := by
      intro hchi
      have hmap : Units.map (algebraMap K L).toMonoidHom (phi sigma) = 1 := by
        simpa [chi] using congrArg Subtype.val hchi
      apply hphi
      apply (Units.map_injective (f := (algebraMap K L).toMonoidHom)
        (algebraMap K L).injective)
      simpa using hmap
    obtain ⟨q, hq⟩ :=
      finiteKummerQuotientCharacter_surjective (K := K) (L := L) n hbase chi
    obtain ⟨delta, rfl⟩ := D.radicalQuotientMk_surjective q
    have hroot_mem : (D.root delta : L) ∈
        finiteKummerRootSet (K := K) (L := L) n := by
      refine ⟨(D.root delta).ne_zero, delta.1, ?_⟩
      exact congrArg Units.val (D.root_pow_eq_map delta)
    have hroot_fixed_val : sigma (D.root delta : L) = D.root delta :=
      hsigma ⟨D.root delta,
        IntermediateField.subset_adjoin K
          (finiteKummerRootSet (K := K) (L := L) n) hroot_mem⟩
    have hroot_fixed : sigma • D.root delta = D.root delta := by
      apply Units.ext
      exact hroot_fixed_val
    have hkummer_sigma : D.kummerCharacterWithoutSection hfixed delta sigma = 1 := by
      apply Subtype.ext
      change D.rootCharacter delta hfixed sigma = 1
      rw [D.rootCharacter_apply]
      change rootQuotient (K := K) (L := L) (D.root delta) sigma = 1
      exact (rootQuotient_eq_one_iff (K := K) (L := L) (D.root delta) sigma).2
        hroot_fixed
    have hchi_eq : D.kummerCharacterWithoutSection hfixed delta = chi := by
      rw [← D.quotientKummerCharacterWithoutSection_mk delta hfixed]
      exact hq
    apply hchi_sigma
    rw [← hchi_eq]
    exact hkummer_sigma
  rw [hsigma_eq_one]
  exact one_mem _

end FiniteKummerGeneration

end KummerTheory
end
end

section
-- module Solutions.OAIQ244_DUKE.Kummer_Concrete_InfiniteGeneration
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.LocalClassFieldTheory.finiteGaloisFieldRangeOfEmbedding_finiteDimensional _root_.LocalClassFieldTheory.finiteGaloisFieldRangeOfEmbedding_isGalois _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionResidueExtension_normal _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionResidueField.instField _root_.RamificationTheory.HilbertRamification.ValuationSubring.selectedResidueField.instAlgebra _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.RelativeIdeleGroup.relativeIdeleMulAction _root_.ValuationTheory.DiscreteValuationField.DVF.maximalIdealPowSuccQuotModule _root_.ValuationTheory.DiscreteValuationField.DVF.residueField.field _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.isLocalRing _root_.CyclicCohomology.binaryCoefficientFamilyCommGroup _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.adicCompletionProperSpace _root_.cyclicPrimeSubextension_isGalois _root_.finiteNormalClosure_isGalois _root_.relativeAdeleRingIntermediateAlgebra _root_.relativeAdeleRingTopIntermediateAlgebra
attribute [-simp] _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.LocalFieldTheory.residueField_algebraMap_residue
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

/-!
# infinite actual-field form

For an arbitrary Galois extension `Ω/K`, each element of `Ω` lies in a
finite Galois intermediate field.  If the full Galois group is abelian and
killed by `n`, restriction gives the same two properties at that finite
stage.  The finite actual-field case of the Kummer generation theorem then shows that the
element belongs to the field generated by the global `n`-th radicals.

This is the actual-field `n`-th-power case.  It does not claim the general
abstract-operator statement of the Kummer generation theorem.
-/

noncomputable section

namespace KummerTheory

open scoped IsMulCommutative

variable {K Ω : Type*} [Field K] [Field Ω] [Algebra K Ω]

/-- The Kummer generation theorem for a possibly infinite actual-field
Galois extension and the `n`-th-power operator.

The finite-stage abelian and exponent hypotheses are derived through the
surjective restriction map; they are not supplied as extra assumptions. -/
theorem kummerRootSet_adjoin_eq_top
    [IsGalois K Ω] [IsMulCommutative Gal(Ω/K)]
    (n : ℕ+) (hmu : (primitiveRoots (n : ℕ) K).Nonempty)
    (hexponent : ∀ σ : Gal(Ω/K), σ ^ (n : ℕ) = 1) :
    IntermediateField.adjoin K (finiteKummerRootSet (K := K) (L := Ω) n) = ⊤ := by
  let U : IntermediateField K Ω :=
    IntermediateField.adjoin K (finiteKummerRootSet (K := K) (L := Ω) n)
  apply top_unique
  intro x _
  let E : FiniteGaloisIntermediateField K Ω :=
    FiniteGaloisIntermediateField.adjoin K {x}
  let res : Gal(Ω/K) →* Gal(E/K) := AlgEquiv.restrictNormalHom E
  have hres_surjective : Function.Surjective res :=
    AlgEquiv.restrictNormalHom_surjective Ω
  let : IsMulCommutative Gal(E/K) :=
    { is_comm := ⟨fun σ τ => by
        obtain ⟨σ', rfl⟩ := hres_surjective σ
        obtain ⟨τ', rfl⟩ := hres_surjective τ
        rw [← map_mul, mul_comm σ' τ', map_mul]⟩ }
  have hE_exponent : ∀ σ : Gal(E/K), σ ^ (n : ℕ) = 1 := by
    intro σ
    obtain ⟨σ', rfl⟩ := hres_surjective σ
    rw [← map_pow, hexponent σ', map_one]
  have hE_generation :
      IntermediateField.adjoin K (finiteKummerRootSet (K := K) (L := E) n) = ⊤ :=
    finiteKummerRootSet_adjoin_eq_top
      (K := K) (L := E) n hmu hE_exponent
  have hroot_subset : finiteKummerRootSet (K := K) (L := E) n ⊆ U.comap E.val := by
    intro β hβ
    change (β : Ω) ∈ U
    apply IntermediateField.subset_adjoin K
      (finiteKummerRootSet (K := K) (L := Ω) n)
    refine ⟨?_, ?_⟩
    · exact (map_ne_zero E.val).2 hβ.1
    · obtain ⟨a, ha⟩ := hβ.2
      refine ⟨a, ?_⟩
      simpa using congrArg E.val ha
  have htop_le : (⊤ : IntermediateField K E) ≤ U.comap E.val := by
    rw [← hE_generation]
    exact IntermediateField.adjoin_le_iff.mpr hroot_subset
  let xE : E :=
    ⟨x, FiniteGaloisIntermediateField.subset_adjoin K {x} (Set.mem_singleton x)⟩
  have hxE : xE ∈ U.comap E.val := htop_le (Set.mem_univ xE)
  exact hxE

end KummerTheory
end
end

section
-- module Solutions.OAIQ244_DUKE.Kummer_Concrete_RadicalExtension
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.KummerTheory.finiteSupportKummerQuotient_commGroupInstance _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionResidueExtension_normal _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionResidueField.instField _root_.RamificationTheory.HilbertRamification.ValuationSubring.selectedResidueField.instAlgebra _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.RelativeIdeleGroup.relativeIdeleMulAction _root_.ValuationTheory.DiscreteValuationField.DVF.maximalIdealPowSuccQuotModule _root_.ValuationTheory.DiscreteValuationField.DVF.residueField.field _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.CyclicCohomology.binaryCoefficientFamilyCommGroup _root_.CyclicCohomology.instMulDistribMulActionBinaryCoefficientFamily _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.adicCompletionProperSpace _root_.relativeAdeleRingIntermediateAlgebra _root_.relativeAdeleRingTopIntermediateAlgebra
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

/-- The field `K(√[n]{Delta})` inside the chosen separable closure. -/
def kummerRadicalExtension (n : ℕ+) (Delta : Subgroup Kˣ) :
    IntermediateField K Omega :=
  IntermediateField.adjoin K (kummerRootSet (K := K) (Omega := Omega) n Delta)

/-- Every `K`-automorphism of the separable closure preserves the full root
set. -/
theorem kummerRootSet_mapsTo
    (n : ℕ+) (Delta : Subgroup Kˣ) (sigma : Gal(Omega/K)) :
    Set.MapsTo sigma
      (kummerRootSet (K := K) (Omega := Omega) n Delta)
      (kummerRootSet (K := K) (Omega := Omega) n Delta) := by
  rintro beta ⟨a, hbeta⟩
  refine ⟨a, ?_⟩
  calc
    sigma beta ^ (n : ℕ) = sigma (beta ^ (n : ℕ)) :=
      (map_pow sigma beta (n : ℕ)).symm
    _ = sigma (algebraMap K Omega (a.1 : K)) := congrArg sigma hbeta
    _ = algebraMap K Omega (a.1 : K) := sigma.commutes (a.1 : K)

/-- Because inverse automorphisms preserve the same equations, the root set
is carried onto itself, not merely into itself. -/
theorem kummerRootSet_image
    (n : ℕ+) (Delta : Subgroup Kˣ) (sigma : Gal(Omega/K)) :
    sigma '' kummerRootSet (K := K) (Omega := Omega) n Delta =
      kummerRootSet (K := K) (Omega := Omega) n Delta := by
  apply Set.Subset.antisymm
  · rintro _ ⟨beta, hbeta, rfl⟩
    exact kummerRootSet_mapsTo n Delta sigma hbeta
  · intro beta hbeta
    refine ⟨sigma.symm beta, kummerRootSet_mapsTo n Delta sigma.symm hbeta, ?_⟩
    exact sigma.apply_symm_apply beta

/-- The actual radical field is stable under every automorphism of the
separable closure. -/
theorem kummerRadicalExtension_map
    (n : ℕ+) (Delta : Subgroup Kˣ) (sigma : Gal(Omega/K)) :
    (kummerRadicalExtension (K := K) (Omega := Omega) n Delta).map sigma =
      kummerRadicalExtension (K := K) (Omega := Omega) n Delta := by
  rw [kummerRadicalExtension, IntermediateField.adjoin_map]
  congr 1
  exact kummerRootSet_image n Delta sigma

/-- The stability just proved is precisely normality over `K`. -/
theorem kummerRadicalExtension_normal
    [IsSepClosure K Omega]
    (n : ℕ+) (Delta : Subgroup Kˣ) :
    Normal K (kummerRadicalExtension (K := K) (Omega := Omega) n Delta) := by
  rw [IntermediateField.normal_iff_forall_map_eq']
  exact kummerRadicalExtension_map n Delta

/-- The extension `K(√[n]{Delta})/K` is Galois.  Separability comes from the
ambient separable closure and normality from invariance of the full root
set. -/
theorem kummerRadicalExtension_isGalois
    [IsSepClosure K Omega]
    (n : ℕ+) (Delta : Subgroup Kˣ) :
    IsGalois K (kummerRadicalExtension (K := K) (Omega := Omega) n Delta) := by
  rw [isGalois_iff]
  exact ⟨inferInstance, kummerRadicalExtension_normal n Delta⟩

/-- On every radical generator, two automorphisms commute.  The quotient
`sigma(beta) / beta` is an `n`-th root of unity, hence lies in and is fixed
by the base field under the primitive-root hypothesis. -/
theorem kummerRadicalExtension_generator_commute
    [IsSepClosure K Omega]
    (n : ℕ+) (hmu : (primitiveRoots (n : ℕ) K).Nonempty)
    (Delta : Subgroup Kˣ)
    (sigma tau : Gal(kummerRadicalExtension (K := K) (Omega := Omega) n Delta/K))
    {beta : Omega}
    (hbeta : beta ∈ kummerRootSet (K := K) (Omega := Omega) n Delta) :
    (sigma * tau)
        ⟨beta, IntermediateField.subset_adjoin K
          (kummerRootSet (K := K) (Omega := Omega) n Delta) hbeta⟩ =
      (tau * sigma)
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
  have hquot_pow (rho : Gal(E/K)) :
      rootQuotient (K := K) (L := E) betaUnit rho ^ (n : ℕ) = 1 :=
    rootQuotient_pow_eq_one_of_pow_fixed (K := K) (L := E) hpow_fixed rho
  have hquot_fixed (rho eta : Gal(E/K)) :
      eta • rootQuotient (K := K) (L := E) betaUnit rho =
        rootQuotient (K := K) (L := E) betaUnit rho :=
    nthRootsOfUnity_fixed (K := K) (L := E) n hbase eta _ (hquot_pow rho)
  have hquot_commute :
      rootQuotient (K := K) (L := E) betaUnit (sigma * tau) =
        rootQuotient (K := K) (L := E) betaUnit (tau * sigma) := by
    rw [rootQuotient_mul, rootQuotient_mul,
      hquot_fixed tau sigma, hquot_fixed sigma tau, mul_comm]
  have hunit_commute : (sigma * tau) • betaUnit = (tau * sigma) • betaUnit := by
    rw [← rootQuotient_mul_right (K := K) (L := E) betaUnit (sigma * tau),
      ← rootQuotient_mul_right (K := K) (L := E) betaUnit (tau * sigma),
      hquot_commute]
  exact congrArg Units.val hunit_commute

/-- Hence `Gal(K(√[n]{Delta})/K)` is commutative.  Equality is checked on
the radical generators of the adjoin. -/
theorem kummerRadicalExtension_isMulCommutative
    [IsSepClosure K Omega]
    (n : ℕ+) (hmu : (primitiveRoots (n : ℕ) K).Nonempty)
    (Delta : Subgroup Kˣ) :
    IsMulCommutative Gal(kummerRadicalExtension (K := K) (Omega := Omega) n Delta/K) := by
  refine ⟨⟨fun sigma tau => ?_⟩⟩
  apply AlgEquiv.coe_toAlgHom_injective
  apply IntermediateField.adjoin_algHom_ext K
  intro beta hbeta
  exact kummerRadicalExtension_generator_commute n hmu Delta sigma tau hbeta

/-- the Kummer correspondence, forward construction: adjoining the radicals attached to
`Delta` produces an abelian Galois extension. -/
theorem kummerRadicalExtension_isAbelianGalois
    [IsSepClosure K Omega]
    (n : ℕ+) (hmu : (primitiveRoots (n : ℕ) K).Nonempty)
    (Delta : Subgroup Kˣ) :
    IsAbelianGalois K
      (kummerRadicalExtension (K := K) (Omega := Omega) n Delta) where
  toIsGalois := kummerRadicalExtension_isGalois n Delta
  toIsMulCommutative := kummerRadicalExtension_isMulCommutative n hmu Delta

end RadicalExtension

end KummerTheory
end
end

section
-- module Solutions.OAIQ244_DUKE.Kummer_Concrete_ExtensionRoundTrip
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.KummerTheory.finiteSupportKummerQuotient_commGroupInstance _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionResidueField.instField _root_.RamificationTheory.HilbertRamification.ValuationSubring.selectedResidueField.instAlgebra _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.RelativeIdeleGroup.relativeIdeleMulAction _root_.ValuationTheory.DiscreteValuationField.DVF.maximalIdealPowSuccQuotModule _root_.ValuationTheory.DiscreteValuationField.DVF.residueField.field _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.CyclicCohomology.binaryCoefficientFamilyCommGroup _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.adicCompletionProperSpace _root_.relativeAdeleRingIntermediateAlgebra _root_.relativeAdeleRingTopIntermediateAlgebra
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

/-!
# extension-side round trip

For an abelian Galois intermediate extension `E/K` of exponent dividing
`n`, adjoining in the ambient algebraic closure all `n`-th roots belonging
to the actual radical subgroup of `E` recovers `E` itself.
-/

noncomputable section

namespace KummerTheory

variable {K Omega : Type*} [Field K] [Field Omega] [Algebra K Omega]

/-- Every ambient root belonging to the actual radical subgroup of `E`
already lies in `E`.  Its ratio with a root chosen in `E` is an `n`-th root
of unity, hence belongs to `K`. -/
theorem kummerRootSet_finiteKummerRadicalSubgroup_le
    (E : IntermediateField K Omega) (n : ℕ+)
    (hmu : (primitiveRoots (n : ℕ) K).Nonempty) :
    kummerRootSet (K := K) (Omega := Omega) n
        (finiteKummerRadicalSubgroup (K := K) (L := E) n) ⊆ E := by
  intro beta hbeta
  have hbeta_ne : beta ≠ 0 :=
    kummerRootSet_ne_zero n
      (finiteKummerRadicalSubgroup (K := K) (L := E) n) hbeta
  obtain ⟨a, hbeta_pow⟩ := hbeta
  obtain ⟨gamma, hgamma_pow⟩ := a.property
  let gammaOmega : Omegaˣ := Units.map E.val.toMonoidHom gamma
  let betaUnit : Omegaˣ := Units.mk0 beta hbeta_ne
  have hbetaUnit_pow : betaUnit ^ (n : ℕ) =
      Units.map (algebraMap K Omega).toMonoidHom a.1 := by
    apply Units.ext
    exact hbeta_pow
  have hgammaOmega_pow : gammaOmega ^ (n : ℕ) =
      Units.map (algebraMap K Omega).toMonoidHom a.1 := by
    apply Units.ext
    exact congrArg E.val (congrArg Units.val hgamma_pow)
  have hratio_pow : (betaUnit / gammaOmega) ^ (n : ℕ) = 1 := by
    rw [div_pow, hbetaUnit_pow, hgammaOmega_pow]
    exact div_self' _
  let hbase : NthRootsOfUnityInBase (K := K) (L := Omega) n :=
    nthRootsOfUnityInBase_of_primitiveRoots
      (K := K) (L := Omega) n hmu
  obtain ⟨zeta, hzeta⟩ := hbase (betaUnit / gammaOmega) hratio_pow
  have hbeta_eq : betaUnit =
      Units.map (algebraMap K Omega).toMonoidHom zeta * gammaOmega := by
    rw [hzeta]
    exact (div_mul_cancel betaUnit gammaOmega).symm
  have hbeta_val := congrArg Units.val hbeta_eq
  change (betaUnit : Omega) ∈ E
  rw [hbeta_val]
  exact E.mul_mem (E.algebraMap_mem (zeta : K)) gamma.1.property

/-- The radical extension constructed from the actual radical subgroup of
`E` is contained in `E`. -/
theorem kummerRadicalExtension_finiteKummerRadicalSubgroup_le
    (E : IntermediateField K Omega) (n : ℕ+)
    (hmu : (primitiveRoots (n : ℕ) K).Nonempty) :
    kummerRadicalExtension (K := K) (Omega := Omega) n
        (finiteKummerRadicalSubgroup (K := K) (L := E) n) ≤ E := by
  exact IntermediateField.adjoin_le_iff.mpr
    (kummerRootSet_finiteKummerRadicalSubgroup_le E n hmu)

/-- The internal generation theorem for `E/K`, transported through
`E.val`, gives the reverse inclusion into the ambient radical extension. -/
theorem le_kummerRadicalExtension_finiteKummerRadicalSubgroup
    (E : IntermediateField K Omega)
    [IsGalois K E] [IsMulCommutative Gal(E/K)]
    (n : ℕ+) (hmu : (primitiveRoots (n : ℕ) K).Nonempty)
    (hexponent : ∀ sigma : Gal(E/K), sigma ^ (n : ℕ) = 1) :
    E ≤ kummerRadicalExtension (K := K) (Omega := Omega) n
      (finiteKummerRadicalSubgroup (K := K) (L := E) n) := by
  let R : IntermediateField K Omega :=
    kummerRadicalExtension (K := K) (Omega := Omega) n
      (finiteKummerRadicalSubgroup (K := K) (L := E) n)
  have hgeneration :
      IntermediateField.adjoin K
        (finiteKummerRootSet (K := K) (L := E) n) = ⊤ :=
    kummerRootSet_adjoin_eq_top
      (K := K) (Ω := E) n hmu hexponent
  have hroot_subset :
      finiteKummerRootSet (K := K) (L := E) n ⊆ R.comap E.val := by
    intro beta hbeta
    change (beta : Omega) ∈ R
    apply IntermediateField.subset_adjoin K
      (kummerRootSet (K := K) (Omega := Omega) n
        (finiteKummerRadicalSubgroup (K := K) (L := E) n))
    obtain ⟨hbeta_ne, a, hbeta_pow⟩ := hbeta
    let betaUnit : Eˣ := Units.mk0 beta hbeta_ne
    have ha : a ∈ finiteKummerRadicalSubgroup (K := K) (L := E) n := by
      refine ⟨betaUnit, ?_⟩
      apply Units.ext
      exact hbeta_pow
    refine ⟨⟨a, ha⟩, ?_⟩
    exact congrArg E.val hbeta_pow
  have htop_le : (⊤ : IntermediateField K E) ≤ R.comap E.val := by
    rw [← hgeneration]
    exact IntermediateField.adjoin_le_iff.mpr hroot_subset
  intro x hx
  let xE : E := ⟨x, hx⟩
  exact htop_le (Set.mem_univ xE)

/-- **the Kummer correspondence, extension-side round trip.**  For an abelian Galois
intermediate extension of exponent dividing `n`, taking its actual radical
subgroup and adjoining all corresponding roots in the ambient closure
recovers the original intermediate field. -/
theorem kummerRadicalExtension_finiteKummerRadicalSubgroup_eq
    (E : IntermediateField K Omega)
    [IsGalois K E] [IsMulCommutative Gal(E/K)]
    (n : ℕ+) (hmu : (primitiveRoots (n : ℕ) K).Nonempty)
    (hexponent : ∀ sigma : Gal(E/K), sigma ^ (n : ℕ) = 1) :
    kummerRadicalExtension (K := K) (Omega := Omega) n
        (finiteKummerRadicalSubgroup (K := K) (L := E) n) = E := by
  apply le_antisymm
  · exact kummerRadicalExtension_finiteKummerRadicalSubgroup_le E n hmu
  · exact le_kummerRadicalExtension_finiteKummerRadicalSubgroup
      E n hmu hexponent

end KummerTheory
end
end

section
-- module Solutions.OAIQ244_DUKE.Kummer_Concrete_InfiniteContinuity
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.LubinTate.compatibleGroupFamiliesGroup _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.adicCompletionProperSpace
attribute [-simp] _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.KummerTheory.characterToNthRoots_apply _root_.KummerTheory.restrictedKummerTranspose_apply _root_.KummerTheory.restrictedQuotientKummerCharacter_mk _root_.LocalFieldTheory.residueField_algebraMap_residue
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

/-- The Kummer root character with codomain given its intended discrete
topology. -/
def infiniteKummerRootCharacter
    (n : ℕ+) (hmu : NthRootsOfUnityInBase (K := K) (L := Ω) n)
    (a : (chosenFiniteKummerRadicalDatum (K := K) (L := Ω) n).carrier) :
    Gal(Ω/K) →* DiscreteNthRootsSubgroup Ω (n : ℕ) :=
  (chosenFiniteKummerRadicalDatum (K := K) (L := Ω) n).rootCharacterToMuWithoutSection
    a (nthRootsOfUnity_fixed (K := K) (L := Ω) n hmu)

/-- The infinite Kummer root character evaluates by the usual Galois ratio. -/
@[simp] theorem infiniteKummerRootCharacter_apply
    (n : ℕ+) (hmu : NthRootsOfUnityInBase (K := K) (L := Ω) n)
    (a : (chosenFiniteKummerRadicalDatum (K := K) (L := Ω) n).carrier)
    (σ : Gal(Ω/K)) :
    infiniteKummerRootCharacter n hmu a σ =
      (chosenFiniteKummerRadicalDatum (K := K) (L := Ω) n).rootCharacterToMuWithoutSection
        a (nthRootsOfUnity_fixed (K := K) (L := Ω) n hmu) σ :=
  rfl

end InfiniteKummerContinuity

end KummerTheory
end
end

section
-- module Solutions.OAIQ244_DUKE.Kummer_Concrete_FiniteSupport
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.KummerTheory.restrictedRadicalQuotient_commGroupInstance _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.adicCompletionProperSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

/-!
# finite radical support

Membership in `K(√[n]{Δ})` uses only finitely many of the adjoined roots.
For such a finite root set this file chooses the corresponding coefficients
in `Δ`, records them in a finite subset of `Kˣ`, and forms the subgroup they
generate.  The resulting subgroup lies in `Δ`, and every selected root has
its `n`-th power in that finitely generated subgroup.

These are the concrete finite-support data needed for the later reduction to
finite Kummer theory; no finite Kummer endpoint is assumed here.
-/

noncomputable section

namespace KummerTheory

variable {K Omega : Type*} [Field K] [Field Omega] [Algebra K Omega]

/-- The chosen coefficient really is the `n`-th power of its root. -/
theorem chosenFiniteSupportCoefficient_pow
    (n : ℕ+) (Delta : Subgroup Kˣ) (T : Finset Omega)
    (hT : (T : Set Omega) ⊆ kummerRootSet (K := K) (Omega := Omega) n Delta)
    (beta : T) :
    (beta.1 : Omega) ^ (n : ℕ) =
      algebraMap K Omega ((chosenFiniteSupportCoefficient n Delta T hT beta).1 : K) :=
  Classical.choose_spec (hT beta.property)

/-- The selected nonzero coefficient belongs to the finite support set. -/
theorem chosenFiniteSupportCoefficient_mem_set
    (n : ℕ+) (Delta : Subgroup Kˣ) (T : Finset Omega)
    (hT : (T : Set Omega) ⊆ kummerRootSet (K := K) (Omega := Omega) n Delta)
    (beta : T) :
    (chosenFiniteSupportCoefficient n Delta T hT beta).1 ∈
      chosenFiniteSupportCoefficientSet (K := K) (Omega := Omega) n Delta T hT := by
  classical
  rw [chosenFiniteSupportCoefficientSet]
  apply Finset.mem_image.2
  exact ⟨beta, Finset.mem_univ beta, rfl⟩

/-- Each chosen coefficient belongs to the generated subgroup `Delta₀`. -/
theorem chosenFiniteSupportCoefficient_mem_subgroup
    (n : ℕ+) (Delta : Subgroup Kˣ) (T : Finset Omega)
    (hT : (T : Set Omega) ⊆ kummerRootSet (K := K) (Omega := Omega) n Delta)
    (beta : T) :
    (chosenFiniteSupportCoefficient n Delta T hT beta).1 ∈
      chosenFiniteSupportCoefficientSubgroup (K := K) (Omega := Omega) n Delta T hT := by
  apply Subgroup.subset_closure
  exact chosenFiniteSupportCoefficient_mem_set n Delta T hT beta

/-- A selected root still has its `n`-th power in the enlarged admissible
subgroup `Delta₀`. -/
theorem finiteSupportRoot_pow_from_admissibleSubgroup
    (n : ℕ+) (Delta : KummerSubgroup K n) (T : Finset Omega)
    (hT : (T : Set Omega) ⊆
      kummerRootSet (K := K) (Omega := Omega) n Delta.1)
    (root : T) :
    ∃ a : (admissibleFiniteSupportSubgroup
        (K := K) (Omega := Omega) n Delta T hT).1,
      (root.1 : Omega) ^ (n : ℕ) = algebraMap K Omega (a.1 : K) := by
  let coefficient := chosenFiniteSupportCoefficient n Delta.1 T hT root
  let a : (admissibleFiniteSupportSubgroup
      (K := K) (Omega := Omega) n Delta T hT).1 :=
    ⟨coefficient.1, Subgroup.mem_sup_right
      (chosenFiniteSupportCoefficient_mem_subgroup n Delta.1 T hT root)⟩
  exact ⟨a, chosenFiniteSupportCoefficient_pow n Delta.1 T hT root⟩


end KummerTheory
end
end

section
-- module Solutions.OAIQ244_DUKE.Kummer_Concrete_FiniteDualSeparation
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.LocalFieldTheory.DiscreteValuationField.finite_nsmulAddKernel_padicInt_pi _root_.LocalFieldTheory.finite_multiplicative_nthPowerKernel _root_.LocalFieldTheory.finite_nsmulAddKernel_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.adicCompletionProperSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

/-!
# finite Kummer dual separation

This file supplies the first missing finite-duality source for the full
subgroup/extension correspondence in the Kummer correspondence.  Characters of a finite
abelian group killed by `n` can be chosen with values in `μₙ`, and these
characters separate points.  Consequently, the transpose of a character
equivalence `R ≃ Hom(G, μₙ)` is injective.

No lattice correspondence or infinite Kummer endpoint is asserted here.
-/

noncomputable section

namespace KummerTheory

/-- The locally defined `nthRootsSubgroup` is canonically the same group as
mathlib's `rootsOfUnity`. -/
def nthRootsSubgroupEquivRootsOfUnity
    (K : Type*) [Field K] (n : ℕ) :
    nthRootsSubgroup K n ≃* rootsOfUnity n K where
  toFun z := ⟨z.1, z.2⟩
  invFun z := ⟨z.1, z.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl

/-- The subgroup of `n`th roots of unity has a canonical finite type structure. -/
noncomputable instance nthRootsSubgroupFintype
    (K : Type*) [Field K] (n : ℕ) [NeZero n] : Fintype (nthRootsSubgroup K n) :=
  letI : Fintype (rootsOfUnity n K) := Fintype.ofFinite _
  Fintype.ofEquiv (rootsOfUnity n K)
    (nthRootsSubgroupEquivRootsOfUnity K n).symm.toEquiv

end KummerTheory
end
end

section
-- module Solutions.OAIQ244_DUKE.Kummer_Concrete_InfiniteInverse
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionResidueField.instField _root_.RamificationTheory.HilbertRamification.ValuationSubring.selectedResidueField.instAlgebra _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.RelativeIdeleGroup.relativeIdeleMulAction _root_.ValuationTheory.DiscreteValuationField.DVF.maximalIdealPowSuccQuotModule _root_.ValuationTheory.DiscreteValuationField.DVF.residueField.field _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.CyclicCohomology.binaryCoefficientFamilyCommGroup _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.adicCompletionProperSpace _root_.relativeAdeleRingIntermediateAlgebra _root_.relativeAdeleRingTopIntermediateAlgebra
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

/-!
# infinite inverse inclusion

Any radical appearing in `K(√[n]{Δ})` uses only finitely many of the
adjoined roots.  The corresponding admissible finite-support subgroup
`Δ₀ ≤ Δ` gives a finite Galois Kummer stage.  Applying the finite inverse
theorem at that stage shows that the original radical already belongs to
`Δ₀`, hence to `Δ`.
-/

noncomputable section

namespace KummerTheory

variable {K Omega : Type*} [Field K] [Field Omega] [Algebra K Omega]

section FiniteSupportField

variable (n : ℕ+) (Delta : KummerSubgroup K n) (T : Finset Omega)
  (hT : (T : Set Omega) ⊆
    kummerRootSet (K := K) (Omega := Omega) n Delta.1)

/-- The admissible finite-support subgroup has all of its prescribed roots
in the field generated by `T`. -/
theorem admissibleFiniteSupportSubgroup_le_finiteKummerRadicalSubgroup :
    (admissibleFiniteSupportSubgroup
      (K := K) (Omega := Omega) n Delta T hT).1 ≤
      finiteKummerRadicalSubgroup
        (K := K) (L := finiteSupportField (K := K) T) n := by
  apply sup_le
  · intro a ha
    obtain ⟨b, hb⟩ := (mem_unitNthPowersSubgroup_iff n).1 ha
    refine ⟨Units.map
      (algebraMap K (finiteSupportField (K := K) T)).toMonoidHom b, ?_⟩
    rw [← map_pow, hb]
  · rw [chosenFiniteSupportCoefficientSubgroup, Subgroup.closure_le]
    intro a ha
    change a ∈ chosenFiniteSupportCoefficientSet
      (K := K) (Omega := Omega) n Delta.1 T hT at ha
    classical
    rw [chosenFiniteSupportCoefficientSet] at ha
    obtain ⟨root, _, rfl⟩ := Finset.mem_image.1 ha
    let rootL : finiteSupportField (K := K) T :=
      ⟨root.1, IntermediateField.subset_adjoin K (T : Set Omega) root.property⟩
    have hroot_ne : rootL ≠ 0 := by
      intro hzero
      apply kummerRootSet_ne_zero n Delta.1 (hT root.property)
      exact congrArg Subtype.val hzero
    refine ⟨Units.mk0 rootL hroot_ne, ?_⟩
    apply Units.ext
    apply Subtype.ext
    exact chosenFiniteSupportCoefficient_pow n Delta.1 T hT root

/-- Every global root belonging to the finite-support subgroup already lies
in the field generated by `T`.  The ratio with a root in that field is an
`n`-th root of unity and hence lies in `K`. -/
theorem kummerRootSet_admissibleFiniteSupport_subset
    (hmu : (primitiveRoots (n : ℕ) K).Nonempty) :
    kummerRootSet (K := K) (Omega := Omega) n
        (admissibleFiniteSupportSubgroup
          (K := K) (Omega := Omega) n Delta T hT).1 ≤
      finiteSupportField (K := K) T := by
  intro beta hbeta
  let Delta0 := admissibleFiniteSupportSubgroup
    (K := K) (Omega := Omega) n Delta T hT
  let L0 := finiteSupportField (K := K) T
  have hbeta_ne : beta ≠ 0 :=
    kummerRootSet_ne_zero n Delta0.1 hbeta
  obtain ⟨a, hbeta_pow⟩ := hbeta
  have ha_radical : a.1 ∈ finiteKummerRadicalSubgroup (K := K) (L := L0) n :=
    admissibleFiniteSupportSubgroup_le_finiteKummerRadicalSubgroup n Delta T hT a.property
  obtain ⟨gamma, hgamma_pow⟩ := ha_radical
  let gammaOmega : Omegaˣ := Units.map L0.val.toMonoidHom gamma
  let betaUnit : Omegaˣ := Units.mk0 beta hbeta_ne
  have hbetaUnit_pow : betaUnit ^ (n : ℕ) =
      Units.map (algebraMap K Omega).toMonoidHom a.1 := by
    apply Units.ext
    exact hbeta_pow
  have hgammaOmega_pow : gammaOmega ^ (n : ℕ) =
      Units.map (algebraMap K Omega).toMonoidHom a.1 := by
    apply Units.ext
    exact congrArg L0.val (congrArg Units.val hgamma_pow)
  have hratio_pow : (betaUnit / gammaOmega) ^ (n : ℕ) = 1 := by
    rw [div_pow, hbetaUnit_pow, hgammaOmega_pow]
    exact div_self' _
  let hbase : NthRootsOfUnityInBase (K := K) (L := Omega) n :=
    nthRootsOfUnityInBase_of_primitiveRoots
      (K := K) (L := Omega) n hmu
  obtain ⟨zeta, hzeta⟩ := hbase (betaUnit / gammaOmega) hratio_pow
  have hbeta_eq : betaUnit =
      Units.map (algebraMap K Omega).toMonoidHom zeta * gammaOmega := by
    rw [hzeta]
    exact (div_mul_cancel betaUnit gammaOmega).symm
  have hbeta_val := congrArg Units.val hbeta_eq
  change (betaUnit : Omega) ∈ L0
  rw [hbeta_val]
  exact L0.mul_mem (L0.algebraMap_mem (zeta : K)) gamma.1.property

/-- The full radical extension attached to the finite-support subgroup is
exactly the field generated by the selected roots. -/
theorem kummerRadicalExtension_admissibleFiniteSupport_eq
    (hmu : (primitiveRoots (n : ℕ) K).Nonempty) :
    kummerRadicalExtension (K := K) (Omega := Omega) n
        (admissibleFiniteSupportSubgroup
          (K := K) (Omega := Omega) n Delta T hT).1 =
      finiteSupportField (K := K) T := by
  apply le_antisymm
  · exact IntermediateField.adjoin_le_iff.mpr
      (kummerRootSet_admissibleFiniteSupport_subset n Delta T hT hmu)
  · apply IntermediateField.adjoin_le_iff.mpr
    intro root hroot
    apply IntermediateField.subset_adjoin K
    exact finiteSupportRoot_pow_from_admissibleSubgroup n Delta T hT ⟨root, hroot⟩

end FiniteSupportField

end KummerTheory
end
end

section
-- module Solutions.OAIQ244_DUKE.KummerTheory_Concrete_SUnitPreparation_SUnitPowerQuotient
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.LocalFieldTheory.DiscreteValuationField.finite_padicInt_finPi_nsmulQuotient _root_.RamificationTheory.HilbertRamification.ValuationSubring.selectedResidueField.instAlgebra _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.adicCompletionProperSpace _root_.relativeAdeleRingIntermediateAlgebra _root_.relativeAdeleRingTopIntermediateAlgebra
attribute [-simp] _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.LocalFieldTheory.residueField_algebraMap_residue
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

/-- The kernel of coordinatewise reduction is exactly the subgroup of
`n`-fold multiples. -/
theorem finsuppModHom_ker (d n : ℕ) :
    (finsuppModHom d n).ker =
      LocalFieldTheory.nsmulAddSubgroup (Fin d →₀ ℤ) n := by
  ext x
  constructor
  · intro hx
    rw [AddMonoidHom.mem_ker] at hx
    rw [LocalFieldTheory.mem_nsmulAddSubgroup_iff]
    let y : Fin d → ℤ := fun i => (x i) / n
    let y' : Fin d →₀ ℤ :=
      (Finsupp.equivFunOnFinite).symm y
    refine ⟨y', ?_⟩
    ext i
    have hdiv : (n : ℤ) ∣ x i := by
      rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
      exact congrFun hx i
    change (n : ℤ) * (x i / n) = x i
    rw [mul_comm]
    exact Int.ediv_mul_cancel hdiv
  · intro hx
    rw [LocalFieldTheory.mem_nsmulAddSubgroup_iff] at hx
    obtain ⟨y, rfl⟩ := hx
    rw [AddMonoidHom.mem_ker]
    ext i
    simp [finsuppModHom]

/-- The finite-free quotient `(ℤ^d) / n(ℤ^d)` is `(ZMod n)^d`. -/
noncomputable def finsuppNsmulQuotientEquivPiZMod
    (d n : ℕ) :
    (Fin d →₀ ℤ) ⧸
        LocalFieldTheory.nsmulAddSubgroup (Fin d →₀ ℤ) n ≃+
      (Fin d → ZMod n) := by
  rw [← finsuppModHom_ker d n]
  exact QuotientAddGroup.quotientKerEquivOfSurjective
    (finsuppModHom d n)
    (finsuppModHom_surjective d n)

/-- The quotient of a finite free integral module by a positive multiple
is finite. -/
noncomputable instance finite_finsupp_nsmulQuotient
    (d : ℕ) (n : ℕ+) :
    Finite
      ((Fin d →₀ ℤ) ⧸
        LocalFieldTheory.nsmulAddSubgroup
          (Fin d →₀ ℤ) (n : ℕ)) := by
  let _ : NeZero (n : ℕ) := ⟨n.ne_zero⟩
  exact Finite.of_equiv
    (Fin d → ZMod (n : ℕ))
    (finsuppNsmulQuotientEquivPiZMod d n).symm

/-- If a positive power of a global unit is an `S`-unit, then the unit
itself is an `S`-unit.  This is the valuation-theoretic saturation needed
to compare the abstract Kummer quotient with `Kˢ / Kˢⁿ`. -/
theorem mem_sUnitGroup_of_pow_mem
    (S : Finset (HeightOneSpectrum (𝓞 K)))
    (n : ℕ+) (x : Kˣ)
    (hx : x ^ (n : ℕ) ∈ SUnitGroup (K := K) S) :
    x ∈ SUnitGroup (K := K) S := by
  rw [mem_SUnitGroup_iff] at hx ⊢
  intro v hv
  have hpow := hx v hv
  change
    v.valuation K (((x : Kˣ) : K) ^ (n : ℕ)) = 1
      at hpow
  rw [map_pow] at hpow
  exact
    (pow_eq_one_iff_left
      (a := v.valuation K ((x : Kˣ) : K)) n.ne_zero).mp hpow

/-- The admissible subgroup

`Kˢ · Kˣⁿ ≤ Kˣ`

whose radical extension is the field `N = K(√[n]{Kˢ})` in the finite S-unit preparation argument. -/
def fullSUnitKummerSubgroup
    (n : ℕ+)
    (S : Finset (HeightOneSpectrum (𝓞 K))) :
    KummerTheory.KummerSubgroup K n :=
  ⟨SUnitGroup (K := K) S ⊔
      KummerTheory.unitNthPowersSubgroup K n,
    le_sup_right⟩

end KummerTheory
end
end

section
-- module Solutions.OAIQ244_DUKE.GlobalClassFieldTheory_ClassFieldAxiom_IdelePowerLocalUnitSubgroup
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.LubinTate.compatibleGroupFamiliesCommGroup _root_.LubinTate.compatibleGroupFamiliesGroup _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.CyclicCohomology.binaryCoefficientFamilyCommGroup _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.adicCompletionProperSpace
attribute [-simp] _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.KummerTheory.mem_sUnitFiniteKummerRadical_iff
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

/-!
# Power-local-unit subgroups of the idele group

This module defines the subgroup of ideles that are local powers at selected
places and integral units elsewhere, together with its intersection with
principal ideles and the corresponding subgroup of S-unit powers.
-/

open scoped NumberField Classical NNReal IsMulCommutative
open NumberField IsDedekindDomain
open KummerTheory

noncomputable section

namespace GlobalClassFieldTheory.ClassFieldAxiom

variable {K : Type*} [Field K] [NumberField K]

/-- The subgroup of field units obtained as `n`-th powers of `U`-units. -/
def sUnitNthPowersInField
    (n : ℕ+)
    (U : Finset (HeightOneSpectrum (𝓞 K))) :
    Subgroup Kˣ :=
  ((powMonoidHom (n : ℕ) :
      SUnitGroup (K := K) U →*
        SUnitGroup (K := K) U).range).map
    (SUnitGroup (K := K) U).subtype

/-- A field unit is an `n`-th power of an `U`-unit exactly when it is
simultaneously an `U`-unit and an `n`-th power in the field.  The reverse
direction uses the valuation-theoretic saturation of `SUnitGroup`. -/
theorem mem_sUnitNthPowersInField_iff
    (n : ℕ+)
    (U : Finset (HeightOneSpectrum (𝓞 K)))
    (x : Kˣ) :
    x ∈ sUnitNthPowersInField (K := K) n U ↔
      x ∈ SUnitGroup (K := K) U ∧
        x ∈ (powMonoidHom (n : ℕ) : Kˣ →* Kˣ).range := by
  constructor
  · rintro ⟨y, hy, rfl⟩
    refine ⟨y.property, ?_⟩
    obtain ⟨z, hz⟩ :=
      (MonoidHom.mem_range
        (G := SUnitGroup (K := K) U)).mp hy
    rw [powMonoidHom_apply] at hz
    subst y
    exact
      (MonoidHom.mem_range
        (G := Kˣ)).mpr ⟨(z : Kˣ), by
          rw [powMonoidHom_apply]
          rfl⟩
  · rintro ⟨hxU, hxPow⟩
    obtain ⟨z, hz⟩ :=
      (MonoidHom.mem_range
        (G := Kˣ)).mp hxPow
    rw [powMonoidHom_apply] at hz
    subst x
    have hzU : z ∈ SUnitGroup (K := K) U :=
      mem_sUnitGroup_of_pow_mem (K := K) U n z hxU
    let zU : SUnitGroup (K := K) U := ⟨z, hzU⟩
    refine ⟨zU ^ (n : ℕ), ?_, ?_⟩
    · exact
        (MonoidHom.mem_range
          (G := SUnitGroup (K := K) U)).mpr
          ⟨zU, by rw [powMonoidHom_apply]⟩
    · simp [zU]

end GlobalClassFieldTheory.ClassFieldAxiom
end
end

section
-- module Solutions.OAIQ244_DUKE.GlobalClassFieldTheory_ClassFieldAxiom_IdeleClassPowerLocalUnitQuotient_SupportedIdeleIndex
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

/-- The product of the archimedean local power indices.  Only real
places and an even exponent contribute a factor `2`. -/
theorem prod_infinitePlace_nthPowerIndex
    (n : ℕ+) :
    (∏ w : InfinitePlace K,
        if w.IsReal ∧ Even (n : ℕ) then 2 else 1) =
      if Even (n : ℕ) then
        2 ^ InfinitePlace.nrRealPlaces K
      else 1 := by
  classical
  by_cases hn : Even (n : ℕ)
  · rw [ite_eq_left hn]
    rw [InfinitePlace.prod_eq_prod_mul_prod]
    simp only [hn, and_true]
    have hr :
        (∏ w : {w : InfinitePlace K // w.IsReal},
            if w.1.IsReal then 2 else 1) =
          ∏ _w : {w : InfinitePlace K // w.IsReal}, 2 := by
      apply Finset.prod_congr rfl
      intro w _
      rw [ite_eq_left w.2]
    have hc :
        (∏ w : {w : InfinitePlace K // w.IsComplex},
            if w.1.IsReal then 2 else 1) =
          ∏ _w : {w : InfinitePlace K // w.IsComplex}, 1 := by
      apply Finset.prod_congr rfl
      intro w _
      rw [ite_eq_right
        (InfinitePlace.not_isReal_iff_isComplex.mpr w.2)]
    rw [hr, hc]
    simp [InfinitePlace.nrRealPlaces]
  · simp [hn]

/-- The archimedean signature calculation used together with the finite
product formula.  If `K` contains a primitive `n`-th root with `n > 2`,
it has no real places; the remaining cases are `n = 1, 2`. -/
theorem prod_infinitePlace_nthPowerIndex_mul_natDegree
    (n : ℕ+)
    (hmu : (primitiveRoots (n : ℕ) K).Nonempty) :
    (∏ w : InfinitePlace K,
        if w.IsReal ∧ Even (n : ℕ) then 2 else 1) *
        (n : ℕ) ^ Module.finrank ℚ K =
      (n : ℕ) ^
        (2 * Fintype.card (InfinitePlace K)) := by
  classical
  have harch :=
    prod_infinitePlace_nthPowerIndex (K := K) n
  obtain ⟨ζ, hζ⟩ := hmu
  have hζprim : IsPrimitiveRoot ζ (n : ℕ) :=
    (mem_primitiveRoots n.pos).mp hζ
  have hsignature :=
    InfinitePlace.card_add_two_mul_card_eq_rank K
  have hplaces :=
    InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces K
  by_cases hlarge : 2 < (n : ℕ)
  · have hreal :
        InfinitePlace.nrRealPlaces K = 0 :=
      InfinitePlace.IsPrimitiveRoot.nrRealPlaces_eq_zero_of_two_lt
        hlarge hζprim
    rw [hreal, zero_add] at hsignature hplaces
    have hdegree :
        Module.finrank ℚ K =
          2 * Fintype.card (InfinitePlace K) := by
      omega
    rw [harch, hreal, hdegree]
    simp
  · have hnle : (n : ℕ) ≤ 2 :=
      Nat.le_of_not_gt hlarge
    have hnpos : 0 < (n : ℕ) := n.pos
    have hone_or_two :
        (n : ℕ) = 1 ∨ (n : ℕ) = 2 := by
      omega
    rcases hone_or_two with hone | htwo
    · have hn : n = (1 : ℕ+) := Subtype.ext hone
      subst n
      rw [harch]
      simp
    · have hn : n = (2 : ℕ+) := Subtype.ext htwo
      subst n
      rw [harch]
      rw [ite_eq_left (by decide :
        Even (((2 : ℕ+) : ℕ)))]
      change
        2 ^ InfinitePlace.nrRealPlaces K *
            2 ^ Module.finrank ℚ K =
          2 ^ (2 * Fintype.card (InfinitePlace K))
      rw [← pow_add]
      congr 1
      omega


end GlobalClassFieldTheory.ClassFieldAxiom
end
end

section
-- module Solutions.OAIQ244_DUKE.KummerTheory_Concrete_SUnitPreparation_FiniteRadicalSupport
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.LocalFieldTheory.DiscreteValuationField.finite_nsmulAddKernel_padicInt_pi _root_.LubinTate.compatibleGroupFamiliesCommGroup _root_.LubinTate.compatibleGroupFamiliesGroup _root_.ValuationTheory.DiscreteValuationField.DVF.maximalIdealPowSuccQuotModule _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.CyclicCohomology.binaryCoefficientFamilyCommGroup _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois
attribute [-simp] _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.CyclicCohomology.additive_toMul_finset_sum_units
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

/-- Adjoin the ambient `n`-th powers to `D ∩ Kˢ`, producing an admissible
object on the subgroup side of Kummer theory. -/
def sUnitKummerSubgroup
    {L : Type*} [Field L] [Algebra K L]
    (n : ℕ+)
    (S : Finset (HeightOneSpectrum (𝓞 K))) :
    KummerTheory.KummerSubgroup K n :=
  ⟨sUnitFiniteKummerRadical (K := K) (L := L) n S ⊔
      KummerTheory.unitNthPowersSubgroup K n,
    le_sup_right⟩

/-- The `S`-unit Kummer subgroup lies in the actual radical of `L / K`. -/
theorem sUnitKummerSubgroup_le_finiteKummerRadicalSubgroup
    {L : Type*} [Field L] [Algebra K L]
    (n : ℕ+)
    (S : Finset (HeightOneSpectrum (𝓞 K))) :
    (sUnitKummerSubgroup (K := K) (L := L) n S).1 ≤
      KummerTheory.finiteKummerRadicalSubgroup
        (K := K) (L := L) n := by
  apply sup_le
  · exact inf_le_right
  · intro x hx
    obtain ⟨y, rfl⟩ :=
      (KummerTheory.mem_unitNthPowersSubgroup_iff n).mp hx
    exact
      (KummerTheory.mem_finiteKummerRadicalSubgroup_iff n).mpr
        ⟨Units.map (algebraMap K L).toMonoidHom y, by simp⟩

/-- Enlarging the finite set of places enlarges the `S`-unit group. -/
theorem sUnitGroup_mono
    {S T : Finset (HeightOneSpectrum (𝓞 K))}
    (hST : S ⊆ T) :
    SUnitGroup (K := K) S ≤ SUnitGroup (K := K) T := by
  intro x hx
  rw [mem_SUnitGroup_iff] at hx ⊢
  intro v hvT
  exact hx v (fun hvS => hvT (hST hvS))

omit numberFieldK in
/-- The actual radical quotient of a finite Galois extension is finite.
This is obtained from the concrete finite Kummer character equivalence,
not supplied as a finiteness hypothesis. -/
theorem finite_chosenFiniteKummerRadicalQuotient
    {L : Type*} [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    (n : ℕ+)
    (hmu : (primitiveRoots (n : ℕ) K).Nonempty) :
    Finite
      ((KummerTheory.chosenFiniteKummerRadicalDatum
        (K := K) (L := L) n).RadicalQuotient) := by
  let : NeZero (n : ℕ) := ⟨n.ne_zero⟩
  let D :=
    KummerTheory.chosenFiniteKummerRadicalDatum
      (K := K) (L := L) n
  let H :=
    Gal(L/K) →* KummerTheory.nthRootsSubgroup L (n : ℕ)
  let : Finite H :=
    Finite.of_injective
      (fun chi : H =>
        (chi : Gal(L/K) →
          KummerTheory.nthRootsSubgroup L (n : ℕ)))
      DFunLike.coe_injective
  let hbase :
      KummerTheory.NthRootsOfUnityInBase
        (K := K) (L := L) n :=
    KummerTheory.nthRootsOfUnityInBase_of_primitiveRoots
      (K := K) (L := L) n hmu
  let e : D.RadicalQuotient ≃* H :=
    KummerTheory.finiteKummerCharacterEquiv n hbase
  exact Finite.of_equiv H e.symm.toEquiv

/-- A chosen representative of a class in the actual finite Kummer
radical quotient. -/
noncomputable def chosenFiniteKummerRadicalRepresentative
    {L : Type*} [Field L] [Algebra K L]
    (n : ℕ+)
    (q :
      (KummerTheory.chosenFiniteKummerRadicalDatum
        (K := K) (L := L) n).RadicalQuotient) :
    (KummerTheory.chosenFiniteKummerRadicalDatum
      (K := K) (L := L) n).carrier :=
  Classical.choose
    ((KummerTheory.chosenFiniteKummerRadicalDatum
      (K := K) (L := L) n).radicalQuotientMk_surjective q)

omit numberFieldK in
/-- The chosen representative maps back to the prescribed radical class. -/
@[simp]
theorem chosenFiniteKummerRadicalRepresentative_spec
    {L : Type*} [Field L] [Algebra K L]
    (n : ℕ+)
    (q :
      (KummerTheory.chosenFiniteKummerRadicalDatum
        (K := K) (L := L) n).RadicalQuotient) :
    (KummerTheory.chosenFiniteKummerRadicalDatum
        (K := K) (L := L) n).radicalQuotientMk
      (chosenFiniteKummerRadicalRepresentative
        (K := K) (L := L) n q) = q :=
  Classical.choose_spec
    ((KummerTheory.chosenFiniteKummerRadicalDatum
      (K := K) (L := L) n).radicalQuotientMk_surjective q)

/-- The `S`-unit radical subgroup belonging to an extension is contained
in the full `S`-unit Kummer subgroup. -/
theorem sUnitKummerSubgroup_le_fullSUnitKummerSubgroup
    {L : Type*} [Field L] [Algebra K L]
    (n : ℕ+)
    (S : Finset (HeightOneSpectrum (𝓞 K))) :
    (sUnitKummerSubgroup (K := K) (L := L) n S).1 ≤
      (fullSUnitKummerSubgroup (K := K) n S).1 := by
  apply sup_le
  · exact inf_le_left.trans le_sup_left
  · exact le_sup_right

omit numberFieldK in
/-- Monotonicity of the concrete radical-extension construction. -/
theorem kummerRadicalExtension_mono
    {Omega : Type*} [Field Omega] [Algebra K Omega]
    (n : ℕ+)
    {Delta Gamma : Subgroup Kˣ}
    (h : Delta ≤ Gamma) :
    KummerTheory.kummerRadicalExtension
        (K := K) (Omega := Omega) n Delta ≤
      KummerTheory.kummerRadicalExtension
        (K := K) (Omega := Omega) n Gamma := by
  apply IntermediateField.adjoin_le_iff.mpr
  rintro beta ⟨a, ha⟩
  apply IntermediateField.subset_adjoin K
    (KummerTheory.kummerRootSet
      (K := K) (Omega := Omega) n Gamma)
  exact ⟨⟨a.1, h a.2⟩, ha⟩

end KummerTheory
end
end

section
-- module Solutions.OAIQ244_DUKE.KummerTheory_Concrete_SUnitPreparation_FullSUnitKummerExtension
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.adicCompletionProperSpace
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

/-- The actual field `N = K(√[n]{Kˢ})` in a fixed separable closure. -/
def fullSUnitKummerExtension
    {Omega : Type*} [Field Omega] [Algebra K Omega]
    (n : ℕ+)
    (S : Finset (HeightOneSpectrum (𝓞 K))) :
    IntermediateField K Omega :=
  KummerTheory.kummerRadicalExtension
    (K := K) (Omega := Omega) n
    (fullSUnitKummerSubgroup (K := K) n S).1

end KummerTheory
end
end

section
-- module Solutions.OAIQ244_DUKE.Kummer_Concrete_SimpleExtension
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionResidueField.instField _root_.RamificationTheory.HilbertRamification.ValuationSubring.selectedResidueField.instAlgebra _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.RelativeIdeleGroup.relativeIdeleMulAction _root_.CyclicCohomology.binaryCoefficientFamilyCommGroup _root_.CyclicCohomology.instMulDistribMulActionBinaryCoefficientFamily _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.adicCompletionProperSpace _root_.relativeAdeleRingIntermediateAlgebra _root_.relativeAdeleRingTopIntermediateAlgebra
attribute [-simp] _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.KummerTheory.chosenFiniteKummerRadicalRepresentative_spec _root_.LocalFieldTheory.residueField_algebraMap_residue
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

/-!
# Simple Kummer extensions

This file exposes the chosen singleton-radical construction used in
Kummer theory.  For `b : Kˣ`, it chooses an embedded field
`K(ⁿ√b)` inside the separable closure and proves that, when `K` contains
the `n`-th roots of unity, this is a finite cyclic Galois extension.
-/

noncomputable section

namespace KummerTheory

variable (K : Type) [Field K]

/-- The chosen element is an actual `n`-th root of `b`. -/
theorem chosenSimpleKummerRoot_pow
    (n : ℕ+) (hnK : ((n : ℕ) : K) ≠ 0) (b : Kˣ) :
    chosenSimpleKummerRoot K n hnK b ^ (n : ℕ) =
      algebraMap K (SeparableClosure K) (b : K) :=
  (Classical.choose_spec
    (exists_kummerRootSet
      (K := K) (Omega := SeparableClosure K) n hnK
      (maximalKummerSubgroup K n).1
      (⟨b, by simp [maximalKummerSubgroup]⟩ :
        (maximalKummerSubgroup K n).1))).2

/-- The chosen radical as a unit of `K(ⁿ√b)`. -/
noncomputable def chosenSimpleKummerRootUnit
    (n : ℕ+) (hnK : ((n : ℕ) : K) ≠ 0) (b : Kˣ) :
    (chosenSimpleKummerExtension K n hnK b)ˣ :=
  Units.mk0
    ⟨chosenSimpleKummerRoot K n hnK b,
      IntermediateField.subset_adjoin K
        {chosenSimpleKummerRoot K n hnK b}
        (Set.mem_singleton (chosenSimpleKummerRoot K n hnK b))⟩
    (by
      intro hzero
      apply kummerRootSet_ne_zero
        (K := K) (Omega := SeparableClosure K) n
        (maximalKummerSubgroup K n).1
        (chosenSimpleKummerRoot_mem K n hnK b)
      exact congrArg Subtype.val hzero)

/-- The radical still has `n`-th power `b` in the simple extension. -/
@[simp]
theorem chosenSimpleKummerRootUnit_pow
    (n : ℕ+) (hnK : ((n : ℕ) : K) ≠ 0) (b : Kˣ) :
    chosenSimpleKummerRootUnit K n hnK b ^ (n : ℕ) =
      Units.map
        (algebraMap K (chosenSimpleKummerExtension K n hnK b)).toMonoidHom b := by
  apply Units.ext
  apply Subtype.ext
  exact chosenSimpleKummerRoot_pow K n hnK b

/-- The extension generated by the chosen simple Kummer root is finite-dimensional. -/
theorem chosenSimpleKummerExtension_finiteDimensional
    (n : ℕ+) (hnK : ((n : ℕ) : K) ≠ 0) (b : Kˣ) :
    FiniteDimensional K (chosenSimpleKummerExtension K n hnK b) := by
  apply IntermediateField.finiteDimensional_adjoin
  intro x hx
  have hx' : x = chosenSimpleKummerRoot K n hnK b :=
    Set.mem_singleton_iff.mp hx
  subst x
  apply IsIntegral.of_pow n.pos
  rw [chosenSimpleKummerRoot_pow K n hnK b]
  exact isIntegral_algebraMap

/-- If `K` contains `μₙ`, then `K(ⁿ√b) / K` is abelian Galois. -/
theorem chosenSimpleKummerExtension_isAbelianGalois
    (n : ℕ+) (hnK : ((n : ℕ) : K) ≠ 0)
    (hmu : (primitiveRoots (n : ℕ) K).Nonempty) (b : Kˣ) :
    IsAbelianGalois K (chosenSimpleKummerExtension K n hnK b) := by
  classical
  let Delta := maximalKummerSubgroup K n
  let beta := chosenSimpleKummerRoot K n hnK b
  let T : Finset (SeparableClosure K) := {beta}
  have hT : (T : Set (SeparableClosure K)) ⊆
      kummerRootSet (K := K) (Omega := SeparableClosure K) n Delta.1 := by
    intro x hx
    have hx' : x = beta := by simpa [T] using hx
    subst x
    simpa [Delta, beta] using chosenSimpleKummerRoot_mem K n hnK b
  let Delta0 := admissibleFiniteSupportSubgroup
    (K := K) (Omega := SeparableClosure K) n Delta T hT
  have hAbelian : IsAbelianGalois K
      (kummerRadicalExtension
        (K := K) (Omega := SeparableClosure K) n Delta0.1) :=
    kummerRadicalExtension_isAbelianGalois
      (K := K) (Omega := SeparableClosure K) n hmu Delta0.1
  have hfield := kummerRadicalExtension_admissibleFiniteSupport_eq
    (K := K) (Omega := SeparableClosure K) n Delta T hT hmu
  rw [hfield] at hAbelian
  change IsAbelianGalois K
    (IntermediateField.adjoin K (T : Set (SeparableClosure K))) at hAbelian
  have hTset : (T : Set (SeparableClosure K)) =
      {chosenSimpleKummerRoot K n hnK b} := by
    ext x
    simp [T, beta]
  rw [hTset] at hAbelian
  exact hAbelian

/-- Every Galois root quotient of the chosen radical is an `n`-th root
of unity. -/
theorem chosenSimpleKummer_rootQuotient_mem
    (n : ℕ+) (hnK : ((n : ℕ) : K) ≠ 0) (b : Kˣ)
    (sigma : Gal((chosenSimpleKummerExtension K n hnK b)/K)) :
    rootQuotient
        (K := K) (L := chosenSimpleKummerExtension K n hnK b)
        (chosenSimpleKummerRootUnit K n hnK b) sigma ∈
      nthRootsSubgroup (chosenSimpleKummerExtension K n hnK b) (n : ℕ) := by
  apply rootQuotient_mem_nthRootsSubgroup_of_pow_fixed
  intro tau
  rw [chosenSimpleKummerRootUnit_pow K n hnK b]
  exact RadicalDatum.smul_algebraMap_unit
    (K := K) (L := chosenSimpleKummerExtension K n hnK b) tau b

/-- The root quotient of the chosen radical is a character of the
Galois group. -/
noncomputable def chosenSimpleKummerRootCharacter
    (n : ℕ+) (hnK : ((n : ℕ) : K) ≠ 0)
    (hmu : (primitiveRoots (n : ℕ) K).Nonempty) (b : Kˣ) :
    Gal((chosenSimpleKummerExtension K n hnK b)/K) →*
      nthRootsSubgroup (chosenSimpleKummerExtension K n hnK b) (n : ℕ) :=
  let E := chosenSimpleKummerExtension K n hnK b
  let : MulDistribMulAction Gal(E/K) Eˣ :=
    AlgEquiv.instMulDistribMulActionUnits
  let D :=
    chosenFiniteKummerRadicalDatum (K := K) (L := E) n
  let delta : D.carrier :=
    ⟨b, chosenSimpleKummerRootUnit K n hnK b,
      chosenSimpleKummerRootUnit_pow K n hnK b⟩
  let hfixed :
      ∀ sigma : Gal(E/K), ∀ u : Eˣ,
        u ^ (n : ℕ) = 1 →
          Units.map sigma.toMonoidHom u = u :=
    nthRootsOfUnity_fixed (K := K) (L := E) n
      (nthRootsOfUnityInBase_of_primitiveRoots
        (K := K) (L := E) n hmu)
  D.rootCharacterToMuWithoutSection delta hfixed

/-- The character attached to the chosen Kummer root agrees with the root
quotient of the chosen generator. -/
@[simp]
theorem chosenSimpleKummerRootCharacter_apply
    (n : ℕ+) (hnK : ((n : ℕ) : K) ≠ 0)
    (hmu : (primitiveRoots (n : ℕ) K).Nonempty) (b : Kˣ)
    (sigma : Gal((chosenSimpleKummerExtension K n hnK b)/K)) :
    chosenSimpleKummerRootCharacter K n hnK hmu b sigma =
      ⟨rootQuotient
          (K := K) (L := chosenSimpleKummerExtension K n hnK b)
          (chosenSimpleKummerRootUnit K n hnK b) sigma,
        chosenSimpleKummer_rootQuotient_mem K n hnK b sigma⟩ := by
  let E := chosenSimpleKummerExtension K n hnK b
  let _ : MulDistribMulAction Gal(E/K) Eˣ :=
    AlgEquiv.instMulDistribMulActionUnits
  let D :=
    chosenFiniteKummerRadicalDatum (K := K) (L := E) n
  let delta : D.carrier :=
    ⟨b, chosenSimpleKummerRootUnit K n hnK b,
      chosenSimpleKummerRootUnit_pow K n hnK b⟩
  let hfixed :
      ∀ tau : Gal(E/K), ∀ u : Eˣ,
        u ^ (n : ℕ) = 1 →
          Units.map tau.toMonoidHom u = u :=
    nthRootsOfUnity_fixed (K := K) (L := E) n
      (nthRootsOfUnityInBase_of_primitiveRoots
        (K := K) (L := E) n hmu)
  apply Subtype.ext
  change
    D.rootCharacter delta hfixed sigma =
      rootQuotient
        (K := K) (L := E)
        (chosenSimpleKummerRootUnit K n hnK b) sigma
  exact
    (D.rootCharacter_eq_of_same_pow hfixed delta
      (chosenSimpleKummerRootUnit_pow K n hnK b) sigma).symm

/-- A Galois automorphism fixes the chosen radical exactly when it is the
identity. -/
theorem chosenSimpleKummerRootQuotient_eq_one_iff
    (n : ℕ+) (hnK : ((n : ℕ) : K) ≠ 0) (b : Kˣ)
    (sigma : Gal((chosenSimpleKummerExtension K n hnK b)/K)) :
    rootQuotient
        (K := K) (L := chosenSimpleKummerExtension K n hnK b)
        (chosenSimpleKummerRootUnit K n hnK b) sigma = 1 ↔
      sigma = 1 := by
  constructor
  · intro hquot
    have hfix := (rootQuotient_eq_one_iff
      (K := K) (L := chosenSimpleKummerExtension K n hnK b)
      (chosenSimpleKummerRootUnit K n hnK b) sigma).1 hquot
    apply AlgEquiv.coe_toAlgHom_injective
    apply IntermediateField.adjoin_algHom_ext K
    intro beta hbeta
    have hbeta' : beta = chosenSimpleKummerRoot K n hnK b :=
      Set.mem_singleton_iff.mp hbeta
    subst beta
    have hval := congrArg Units.val hfix
    change
      sigma
          (chosenSimpleKummerRootUnit K n hnK b :
            chosenSimpleKummerExtension K n hnK b) =
        (1 : Gal((chosenSimpleKummerExtension K n hnK b)/K))
          (chosenSimpleKummerRootUnit K n hnK b :
            chosenSimpleKummerExtension K n hnK b)
    exact hval
  · rintro rfl
    exact rootQuotient_one
      (K := K) (L := chosenSimpleKummerExtension K n hnK b)
      (chosenSimpleKummerRootUnit K n hnK b)

/-- Evaluation on the generating radical separates all automorphisms. -/
theorem chosenSimpleKummerRootCharacter_injective
    (n : ℕ+) (hnK : ((n : ℕ) : K) ≠ 0)
    (hmu : (primitiveRoots (n : ℕ) K).Nonempty) (b : Kˣ) :
    Function.Injective
      (chosenSimpleKummerRootCharacter K n hnK hmu b) := by
  intro sigma tau hst
  apply div_eq_one.mp
  apply
    (chosenSimpleKummerRootQuotient_eq_one_iff
      K n hnK b (sigma / tau)).1
  have hchar :
      chosenSimpleKummerRootCharacter K n hnK hmu b (sigma / tau) = 1 := by
    rw [map_div, hst]
    exact div_self' _
  rw [chosenSimpleKummerRootCharacter_apply K n hnK hmu b] at hchar
  exact congrArg Subtype.val hchar

/-- Every automorphism of a simple Kummer extension has exponent
dividing `n`. -/
theorem chosenSimpleKummerExtension_galois_pow_eq_one
    (n : ℕ+) (hnK : ((n : ℕ) : K) ≠ 0)
    (hmu : (primitiveRoots (n : ℕ) K).Nonempty) (b : Kˣ)
    (sigma : Gal((chosenSimpleKummerExtension K n hnK b)/K)) :
    sigma ^ (n : ℕ) = 1 := by
  apply chosenSimpleKummerRootCharacter_injective K n hnK hmu b
  rw [map_pow, map_one]
  apply Subtype.ext
  exact (chosenSimpleKummerRootCharacter K n hnK hmu b sigma).property

end KummerTheory
end
end


